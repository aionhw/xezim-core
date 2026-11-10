//! Thread-safe, nonsemantic AST caches. IEEE 1800-2023 §13.3/§13.4 bodies
//! may be shared, but widths and resolved names remain scope-dependent.

use std::sync::OnceLock;
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};

#[derive(Clone, Copy, PartialEq, Eq)]
enum ScopeCacheMode {
    Preserve,
    Disabled,
    Fresh,
}

thread_local! {
    static SCOPE_CACHE_MODE: std::cell::Cell<ScopeCacheMode> =
        const { std::cell::Cell::new(ScopeCacheMode::Preserve) };
}

fn with_scope_cache_mode<R>(mode: ScopeCacheMode, f: impl FnOnce() -> R) -> R {
    struct Restore(ScopeCacheMode);
    impl Drop for Restore {
        fn drop(&mut self) {
            SCOPE_CACHE_MODE.with(|flag| flag.set(self.0));
        }
    }
    let _restore = Restore(SCOPE_CACHE_MODE.with(|flag| flag.replace(mode)));
    f()
}

/// Construct or clone a body for use in more than one lexical scope.
/// Every cache constructor participates, including expressions in dimensions,
/// assertion actions and constraints that a procedural-only visitor misses.
pub fn without_scope_caches<R>(f: impl FnOnce() -> R) -> R {
    with_scope_cache_mode(ScopeCacheMode::Disabled, f)
}

/// Deep-clone a private runtime body with empty, enabled contextual caches.
/// The caller must give this body one lexical binding; sharing the original
/// source remains safe because only the newly cloned caches are enabled.
pub fn with_fresh_scope_caches<R>(f: impl FnOnce() -> R) -> R {
    with_scope_cache_mode(ScopeCacheMode::Fresh, f)
}

fn scope_cache_mode() -> ScopeCacheMode {
    SCOPE_CACHE_MODE.with(|flag| flag.get())
}

fn scope_caches_disabled() -> bool {
    scope_cache_mode() == ScopeCacheMode::Disabled
}

macro_rules! option_cache {
    ($name:ident, $atomic:ident, $storage:ty, $value:ty) => {
        #[derive(Debug)]
        pub struct $name($atomic);

        impl $name {
            const EMPTY: $storage = <$storage>::MAX;
            const DISABLED: $storage = <$storage>::MAX - 1;

            pub fn new(value: Option<$value>) -> Self {
                let value = if scope_caches_disabled() {
                    Self::DISABLED
                } else {
                    value.map_or(Self::EMPTY, |v| v as $storage)
                };
                Self($atomic::new(value))
            }

            pub fn get(&self) -> Option<$value> {
                let value = self.0.load(Ordering::Relaxed);
                (value < Self::DISABLED).then_some(value as $value)
            }

            pub fn set(&self, value: Option<$value>) {
                let value = value.map_or(Self::EMPTY, |v| v as $storage);
                debug_assert!(value != Self::DISABLED);
                let mut old = self.0.load(Ordering::Relaxed);
                while old != Self::DISABLED {
                    match self.0.compare_exchange_weak(
                        old,
                        value,
                        Ordering::Relaxed,
                        Ordering::Relaxed,
                    ) {
                        Ok(_) => return,
                        Err(current) => old = current,
                    }
                }
            }

            /// Shared bodies cannot retain results from one call's scope.
            pub fn disable(&self) {
                self.0.store(Self::DISABLED, Ordering::Relaxed);
            }
        }

        impl Default for $name {
            fn default() -> Self {
                Self::new(None)
            }
        }

        impl Clone for $name {
            fn clone(&self) -> Self {
                let value = match scope_cache_mode() {
                    ScopeCacheMode::Disabled => Self::DISABLED,
                    ScopeCacheMode::Fresh => Self::EMPTY,
                    ScopeCacheMode::Preserve => self.0.load(Ordering::Relaxed),
                };
                Self($atomic::new(value))
            }
        }
    };
}

option_cache!(WidthCache, AtomicU64, u64, u32);
option_cache!(SignalCache, AtomicUsize, usize, usize);

#[derive(Debug, Default, Clone)]
pub struct LiteralCache(OnceLock<(u64, u64, u32)>);

impl LiteralCache {
    pub fn new(value: Option<(u64, u64, u32)>) -> Self {
        let cache = Self::default();
        cache.set(value);
        cache
    }

    pub fn get(&self) -> Option<(u64, u64, u32)> {
        self.0.get().copied()
    }

    pub fn set(&self, value: Option<(u64, u64, u32)>) {
        if let Some(value) = value {
            if let Err(value) = self.0.set(value) {
                debug_assert_eq!(self.0.get(), Some(&value));
            }
        }
    }
}

#[derive(Debug)]
pub struct NameCache {
    value: OnceLock<String>,
    disabled: AtomicBool,
}

impl NameCache {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn get(&self) -> Option<&String> {
        if self.disabled.load(Ordering::Relaxed) {
            None
        } else {
            self.value.get()
        }
    }

    pub fn set(&self, value: String) -> Result<(), String> {
        if self.disabled.load(Ordering::Relaxed) {
            Err(value)
        } else {
            self.value.set(value)
        }
    }

    pub fn disable(&self) {
        self.disabled.store(true, Ordering::Relaxed);
    }
}

impl Default for NameCache {
    fn default() -> Self {
        Self {
            value: OnceLock::new(),
            disabled: AtomicBool::new(scope_caches_disabled()),
        }
    }
}

impl Clone for NameCache {
    fn clone(&self) -> Self {
        let mode = scope_cache_mode();
        let disabled = mode == ScopeCacheMode::Disabled
            || (mode == ScopeCacheMode::Preserve && self.disabled.load(Ordering::Relaxed));
        Self {
            value: if disabled || mode == ScopeCacheMode::Fresh {
                OnceLock::new()
            } else {
                self.value.clone()
            },
            disabled: AtomicBool::new(disabled),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn disabled_scope_caches_stay_empty_after_writes_and_clones() {
        let width = WidthCache::new(Some(32));
        width.disable();
        width.set(Some(64));
        assert_eq!(width.clone().get(), None);
        let signal = SignalCache::new(Some(17));
        signal.disable();
        signal.set(None);
        assert_eq!(signal.clone().get(), None);
        let name = NameCache::new();
        name.set("a.word".into()).unwrap();
        name.disable();
        assert!(name.set("b.word".into()).is_err());
        assert!(name.clone().get().is_none());
    }

    #[test]
    fn construction_guard_disables_clones_and_restores_on_unwind() {
        let original = WidthCache::new(Some(16));
        let name = NameCache::new();
        name.set("first.word".into()).unwrap();
        let _ = std::panic::catch_unwind(|| {
            without_scope_caches(|| {
                let cloned = original.clone();
                cloned.set(Some(32));
                assert_eq!(cloned.get(), None);
                assert!(name.clone().get().is_none());
                assert!(NameCache::new().set("second.word".into()).is_err());
                assert_eq!(WidthCache::new(Some(8)).get(), None);
                assert_eq!(LiteralCache::new(Some((7, 0, 32))).get(), Some((7, 0, 32)));
                panic!("exercise restoration");
            })
        });
        assert_eq!(original.get(), Some(16));
        assert_eq!(WidthCache::new(Some(8)).get(), Some(8));
        assert_eq!(name.get().map(String::as_str), Some("first.word"));
    }

    #[test]
    fn parsed_callable_bodies_disable_contextual_caches_before_any_clone() {
        let parsed = crate::parse(
            "module top; function int f(input int x); return x+1; endfunction task t; int y; y=1; endtask endmodule",
        );
        assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
        let crate::ast::Description::Module(module) = &parsed.source.descriptions[0] else {
            panic!("module expected");
        };
        let crate::ast::decl::ModuleItem::FunctionDeclaration(function) = &module.items[0] else {
            panic!("function expected");
        };
        let crate::ast::stmt::StatementKind::Return(Some(expr)) = &function.items[0].kind else {
            panic!("return expected");
        };
        expr.cached_width.set(Some(8));
        assert_eq!(expr.cached_width.get(), None);
        let crate::ast::decl::ModuleItem::TaskDeclaration(task) = &module.items[1] else {
            panic!("task expected");
        };
        let crate::ast::stmt::StatementKind::BlockingAssign { rvalue, .. } = &task.items[1].kind
        else {
            panic!("assignment expected");
        };
        rvalue.cached_width.set(Some(8));
        assert_eq!(rvalue.cached_width.get(), None);
    }

    #[test]
    fn root_package_and_local_class_bodies_share_without_scope_caches() {
        use crate::ast::decl::{ClassItem, ClassMethodKind, ModuleItem, PackageItem};
        use crate::ast::types::{DataType, PackedDimension};
        let function = "function logic [7:0] f(input logic [7:0] x); return x+1; endfunction";
        for source in [
            format!("module top; {function} endmodule"),
            format!("package p; {function} endpackage"),
            format!("module top; class C; {function} endclass endmodule"),
        ] {
            let parsed = crate::parse(&source);
            assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
            let function = match &parsed.source.descriptions[0] {
                crate::ast::Description::Module(module) => match &module.items[0] {
                    ModuleItem::FunctionDeclaration(function) => function,
                    ModuleItem::ClassDeclaration(class) => match &class.items[0] {
                        ClassItem::Method(method) => match &method.kind {
                            ClassMethodKind::Function(function) => function,
                            _ => panic!("function method expected"),
                        },
                        _ => panic!("class method expected"),
                    },
                    _ => panic!("callable expected"),
                },
                crate::ast::Description::Package(package) => match &package.items[0] {
                    PackageItem::Function(function) => function,
                    _ => panic!("package function expected"),
                },
                _ => panic!("module or package expected"),
            };
            let cloned = function.clone();
            assert!(std::sync::Arc::ptr_eq(
                function.items.as_arc(),
                cloned.items.as_arc()
            ));
            let crate::ast::stmt::StatementKind::Return(Some(expr)) = &function.items[0].kind
            else {
                panic!("return expected");
            };
            expr.cached_width.set(Some(8));
            assert_eq!(expr.cached_width.get(), None);
            let DataType::IntegerVector { dimensions, .. } = &function.ports[0].data_type else {
                panic!("packed formal expected");
            };
            let PackedDimension::Range { left, .. } = &dimensions[0] else {
                panic!("range expected");
            };
            left.cached_width.set(Some(32));
            assert_eq!(left.cached_width.get(), Some(32));
        }
    }

    #[test]
    fn fresh_private_clones_enable_empty_caches_without_changing_source() {
        let disabled = without_scope_caches(|| WidthCache::new(Some(8)));
        let private = with_fresh_scope_caches(|| disabled.clone());
        assert_eq!(private.get(), None);
        private.set(Some(16));
        assert_eq!(private.get(), Some(16));
        assert_eq!(disabled.get(), None);
        let existing = NameCache::new();
        existing.set("old.scope".into()).unwrap();
        let private = with_fresh_scope_caches(|| existing.clone());
        assert!(private.get().is_none());
        private.set("new.scope".into()).unwrap();
        assert_eq!(existing.get().map(String::as_str), Some("old.scope"));
        assert_eq!(private.get().map(String::as_str), Some("new.scope"));
    }

    #[test]
    fn parser_ast_remains_send_and_sync() {
        fn assert_traits<T: Send + Sync>() {}
        assert_traits::<super::super::stmt::Statement>();
        assert_traits::<super::super::decl::FunctionDeclaration>();
    }

    #[test]
    fn concurrent_literal_cache_writers_agree() {
        let cache = LiteralCache::default();
        std::thread::scope(|scope| {
            for _ in 0..4 {
                scope.spawn(|| cache.set(Some((7, 0, 32))));
            }
        });
        assert_eq!(cache.get(), Some((7, 0, 32)));
    }
}
