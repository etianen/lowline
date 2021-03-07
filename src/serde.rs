use std::fmt;
use serde::{Serialize, Serializer, de::{self, Visitor}, Deserialize, Deserializer};
use crate::str::Str;

impl<'a> Serialize for Str<'a> {
    #[inline]
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.as_str().serialize(serializer)
    }
}

struct StrVisitor;

impl<'de> Visitor<'de> for StrVisitor {
    type Value = Str<'de>;

    #[inline]
    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("string")
    }

    #[inline]
    fn visit_borrowed_str<E: de::Error>(self, value: &'de str) -> Result<Self::Value, E> {
        Ok(Str::from(value))
    }

    #[inline]
    fn visit_str<E: de::Error>(self, value: &str) -> Result<Self::Value, E> {
        Ok(Str::from(value.to_owned()))
    }

    #[inline]
    fn visit_string<E: de::Error>(self, value: String) -> Result<Self::Value, E> {
        Ok(Str::from(value))
    }
}

impl<'de> Deserialize<'de> for Str<'de> {
    #[inline]
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_str(StrVisitor)
    }
}

#[cfg(test)]
mod test {
    use std::borrow::Cow;
    use serde_json::json;
    use super::*;

    #[test]
    fn test_serialize() {
        assert_eq!(json!(Str::from("moo")), json!("moo"));
    }

    #[test]
    fn test_deserialize() {
        // Test borrowed.
        let s = serde_json::from_slice::<Str>(b"\"moo\"").unwrap();
        assert!(matches!(Cow::from(s), Cow::Borrowed("moo")));
        // Test owned by putting an escape sequence in the string.
        let s = serde_json::from_slice::<Str>(b"\"moo\\n\"").unwrap();
        assert!(matches!(Cow::from(s), Cow::Owned(ref s) if s == "moo\n"));
    }
}
