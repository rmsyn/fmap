/// Value + string structure for common conversions
#[repr(C)]
pub struct ValStr<'a> {
    /// Field value
    val: u32,
    /// Field description
    string: &'a str,
}

impl<'a> ValStr<'a> {
    pub const fn new() -> Self {
        Self { val: 0, string: "" }
    }

    pub const fn create(val: u32, string: &'a str) -> Self {
        Self { val, string }
    }

    pub fn match_val(&self, val: u32) -> Option<&str> {
        if self.value() == val {
            return Some(self.string);
        }

        None
    }

    pub fn value(&self) -> u32 {
        self.val
    }

    pub fn set_value(&mut self, val: u32) {
        self.val = val;
    }

    pub fn string(&self) -> &str {
        self.string
    }

    pub fn set_string(&mut self, string: &'a str) {
        self.string = string;
    }
}

/// val2str_default  -  convert value to string
///
/// @val:        value to convert
/// @vs:         value-string data
/// @def_str:    default string to return if no matching value found
///
/// returns string of matching value
/// returns def_str if no matching value found
pub fn val2str_default<'a>(val: u32, vs: &'a [ValStr], def_str: &'a str) -> &'a str {
    for v in vs.iter() {
        if let Some(s) = v.match_val(val) {
            return s;
        }
    }

    def_str
}

/// val2str  -  convert value to string
///
/// @val:        value to convert
/// @vs:         value-string data
///
/// returns string of matching value
/// returns pointer to "unknown" static string if not found
pub fn val2str<'a>(val: u32, vs: &'a [ValStr]) -> &'a str {
    val2str_default(val, vs, "Unknown")
}

/// str2val  -  convert string to value
///
/// @str:        string to convert
/// @vs:         value-string data
///
/// returns value for string
/// returns value for last entry in value-string data if not found
pub fn str2val(string: &str, vs: &[ValStr]) -> u32 {
    for v in vs.iter() {
        if v.string == string {
            return v.val;
        }
    }

    vs[vs.len() - 1].value()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_match_val() {
        let vs = [
            ValStr::create(0, "foo"),
            ValStr::create(1, "bar"),
            ValStr::create(2, "baz"),
        ];

        assert_eq!(val2str_default(0, &vs, "empty"), "foo");
        assert_eq!(val2str_default(1, &vs, "empty"), "bar");
        assert_eq!(val2str_default(2, &vs, "empty"), "baz");

        assert_eq!(val2str_default(3, &vs, "empty"), "empty");
        assert_eq!(val2str_default(42, &vs, "empty"), "empty");

        assert_eq!(val2str(42, &vs), "Unknown");
    }

    #[test]
    fn test_valstr() {
        let mut vs = ValStr::new();
        let exp_val = 32;
        let exp_str = "foo";

        vs.set_value(exp_val);
        assert_eq!(vs.value(), exp_val);

        vs.set_string(exp_str);
        assert_eq!(vs.string(), exp_str);
    }

    #[test]
    fn test_match_str() {
        let vs = [
            ValStr::create(3, "foo"),
            ValStr::create(2, "bar"),
            ValStr::create(1, "baz"),
        ];

        assert_eq!(str2val("baz", &vs), 1);
        assert_eq!(str2val("bar", &vs), 2);
        assert_eq!(str2val("foo", &vs), 3);

        // return the last value in the list when no matching string found
        assert_eq!(str2val("what", &vs), 1);
    }
}
