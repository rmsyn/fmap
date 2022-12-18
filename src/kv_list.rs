use crate::Error;
use alloc::{string::String, vec, vec::Vec};

pub const KV_MAX_VALUE_LEN: usize = 1024;

#[repr(C)]
#[derive(Debug, PartialEq)]
pub struct KvPair {
    key: String,
    value: String,
}

impl KvPair {
    pub const fn new() -> Self {
        Self {
            key: String::new(),
            value: String::new(),
        }
    }

    pub fn create(key: &str, val: &str) -> Result<Self, Error> {
        if key.len() == 0 || val.len() == 0 || val.len() > KV_MAX_VALUE_LEN {
            Err(Error::Generic)
        } else {
            Ok(Self {
                key: String::from(key),
                value: String::from(val),
            })
        }
    }
}

#[repr(C)]
#[derive(Debug, PartialEq)]
pub struct KvList {
    list: Vec<KvPair>,
}

impl KvList {
    pub const fn new() -> Self {
        Self { list: Vec::new() }
    }

    pub fn create(key: &str, value: &str) -> Result<Self, Error> {
        Ok(Self {
            list: vec![KvPair::create(key, value)?],
        })
    }

    pub fn add(&mut self, key: &str, value: &str) -> Result<(), Error> {
        self.list.push(KvPair::create(key, value)?);

        Ok(())
    }

    pub fn add_bool(&mut self, key: &str, val: bool) -> Result<(), Error> {
        let value = if val { "yes" } else { "no" };

        self.add(key, value)
    }

    pub fn find_value(&self, key: &str) -> Option<&str> {
        for kv in self.list.iter() {
            if &kv.key == key {
                return Some(&kv.value);
            }
        }

        None
    }

    pub fn len(&self) -> usize {
        self.list.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_kv() -> Result<(), Error> {
        let mut kv = KvList::new();

        let exp_key = "some_key";
        let exp_value = "some_value";

        assert!(kv.add(exp_key, exp_value).is_ok());

        let nkv = KvList::create(exp_key, exp_value)?;

        assert_eq!(kv, nkv);

        Ok(())
    }

    #[test]
    fn test_add_kv() {
        let mut kv = KvList::new();

        let exp_key = "some_key";
        let exp_value = "some_value";

        assert!(kv.add(exp_key, exp_value).is_ok());

        assert_eq!(kv.find_value(exp_key), Some(exp_value));
        assert_eq!(kv.find_value("bad_key"), None);
    }

    #[test]
    fn test_add_bool() {
        let mut kv = KvList::new();
        let (true_key, false_key, maybe_key) = ("true_key", "false_key", "maybe_key");

        assert!(kv.add_bool(true_key, true).is_ok());
        assert!(kv.add_bool(false_key, false).is_ok());

        assert_eq!(kv.find_value(true_key), Some("yes"));
        assert_eq!(kv.find_value(false_key), Some("no"));
        assert_eq!(kv.find_value(maybe_key), None);
    }

    #[test]
    fn test_update_value() {
        let mut kv = KvList::new();

        let key = "some_key";
        let value = "some_value";
        let update = "some_update";

        assert!(kv.add(key, value).is_ok());

        // adding the same key with a new value appends to the end of the list
        assert!(kv.add(key, update).is_ok());
        // will only ever find the first value with the same key
        assert_eq!(kv.find_value(key), Some(value));
    }

    #[test]
    fn test_over_max_value() {
        let mut kv = KvList::new();
        let key = "some_key";
        let over_max_val = core::str::from_utf8(&[0x00u8; KV_MAX_VALUE_LEN + 1]).unwrap();

        assert!(kv.add(key, over_max_val).is_err());
        assert_eq!(kv.find_value(key), None);
    }
}
