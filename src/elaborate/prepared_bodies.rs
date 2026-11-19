//! IEEE 1800-2023 §23.10, §27: the prepared bodies of one inlining pass, by
//! parameter environment (aionhw/xezim#721).
//!
//! A body is prepared once for each environment a definition is instantiated
//! in and reused by every later instance in the same one. An environment no
//! other instance repeats (a definition generated under a distinct value for
//! each instance) leaves a body nothing reads again once its instance is
//! inlined; holding all of them made the cache grow with the instance count.
//!
//! A body is therefore held while it can still be told to be useful:
//!
//! - a key a second instance asked for is kept for the whole pass, as before
//!   (an instance asks twice itself: where it is instantiated, and when its
//!   own body is inlined);
//! - of the keys only one instance asked for so far, each definition keeps
//!   its `UNSHARED_WINDOW` most recent ones, and releases the body of an
//!   older one;
//! - a released key that comes back is prepared again and then kept, so no
//!   body is prepared more than twice.
//!
//! Definitions instantiated under few environments, and environments that
//! recur, behave exactly as with an unbounded cache.

use super::PreparedModuleItems;
use super::param_scope::PreparedKey;
use crate::hasher::{DeterministicState, HashMap, HashSet};
use std::cell::Cell;
use std::collections::VecDeque;
use std::hash::BuildHasher;
use std::rc::Rc;

/// How many keys of a single instance each one definition holds.
pub(super) const UNSHARED_WINDOW: usize = 16;

struct Held {
    body: Rc<PreparedModuleItems>,
    /// The instance the body was prepared for.
    instance: u64,
    /// Whether another instance asked for it too.
    reused: Cell<bool>,
}

#[derive(Default)]
pub(super) struct PreparedBodies {
    bodies: HashMap<Rc<PreparedKey>, Held>,
    /// The instance whose body is being prepared, as a hash of its path: it
    /// only tells an instance from the next one, and two paths that hash
    /// alike are taken for one instance, whose bodies may then be released.
    instance: u64,
    /// Per definition, the keys not known to be reused, oldest first.
    unshared: HashMap<(String, usize), VecDeque<Rc<PreparedKey>>>,
    /// The hashes of the keys released without a reuse. A key that hashes
    /// like one is kept when it is prepared again; the hash decides nothing
    /// else.
    released: HashSet<u64>,
    #[cfg(test)]
    pub(super) releases: usize,
}

impl PreparedBodies {
    /// How many bodies are held.
    pub(super) fn len(&self) -> usize {
        self.bodies.len()
    }

    /// The lookups and insertions that follow are for the instance at
    /// `path`.
    pub(super) fn enter_instance(&mut self, path: &str) {
        self.instance = DeterministicState::default().hash_one(path);
    }

    /// The body prepared under `key`. Asked for by another instance than the
    /// one it was prepared for, it is known to be reused.
    pub(super) fn get(&self, key: &PreparedKey) -> Option<&Rc<PreparedModuleItems>> {
        let held = self.bodies.get(key)?;
        if held.instance != self.instance {
            held.reused.set(true);
        }
        Some(&held.body)
    }

    pub(super) fn insert(&mut self, key: PreparedKey, body: Rc<PreparedModuleItems>) {
        let came_back = !self.released.is_empty() && self.released.remove(&Self::hash_of(&key));
        let key = Rc::new(key);
        if !came_back {
            let definition = key.definition();
            let recent = match self.unshared.get_mut(definition) {
                Some(recent) => recent,
                None => self.unshared.entry(definition.clone()).or_default(),
            };
            recent.push_back(Rc::clone(&key));
            while recent.len() > UNSHARED_WINDOW {
                let Some(oldest) = recent.pop_front() else {
                    break;
                };
                if self
                    .bodies
                    .get(&*oldest)
                    .is_some_and(|held| !held.reused.get())
                {
                    self.bodies.remove(&*oldest);
                    self.released.insert(Self::hash_of(&oldest));
                    #[cfg(test)]
                    {
                        self.releases += 1;
                    }
                }
            }
        }
        self.bodies.insert(
            key,
            Held {
                body,
                instance: self.instance,
                reused: Cell::new(came_back),
            },
        );
    }

    fn hash_of(key: &PreparedKey) -> u64 {
        DeterministicState::default().hash_one(key)
    }
}
