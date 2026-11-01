//! `encode_name_key` / `decode_name_key` (§7.8.2 string keys in flat names).
use xezim_core::value::{decode_name_key, encode_name_key};

#[test]
fn encoded_keys_hold_no_brackets_and_round_trip() {
    for key in [
        "", "plain", "x[1]", "]", "[[", "a\\", "\\(", "a\\)b[c]", "é\n",
    ] {
        let enc = encode_name_key(key);
        assert!(
            !enc.contains('[') && !enc.contains(']'),
            "{key:?} -> {enc:?}"
        );
        assert_eq!(decode_name_key(&enc), key);
    }
    assert!(matches!(
        encode_name_key("plain"),
        std::borrow::Cow::Borrowed(_)
    ));
}
