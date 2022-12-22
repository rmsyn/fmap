use crate::{
    Error, Fmap, FmapArea, FLAG_LUT, FMAP_SIGNATURE, FMAP_SIGNATURE_LEN, FMAP_STRLEN, MAX_LEN,
};
use alloc::vec;
use core::mem::size_of;

pub type KvHandler = fn(&mut [u8], &[u8]) -> Result<(), Error>;

#[repr(C)]
pub struct KvAttr<'a, 'b> {
    pub key: &'a str,
    pub dest: &'b mut [u8],
    pub handler: KvHandler,
}

impl<'a, 'b> KvAttr<'a, 'b> {
    pub fn create(key: &'a str, dest: &'b mut [u8], handler: KvHandler) -> Self {
        Self { key, dest, handler }
    }
}

/// extract_value - Extract value from key="value" string
///
/// line: string to extract value from
///
/// returns allocated, NULL-terminated copy of value
/// returns NULL to indicate failure
pub fn extract_value(line: &str) -> Result<&str, Error> {
    if line == "" {
        return Err(Error::Generic);
    }

    if let Some(i) = line.find("\"") {
        if let Some(j) = line[i + 1..].find("\"") {
            return Ok(&line[i + 1..=i + j]);
        }
    }

    Err(Error::Generic)
}

pub fn do_strcpy(dest: &mut [u8], src: &[u8]) -> Result<(), Error> {
    if dest.len() == 0 || src.len() == 0 || src.len() > MAX_LEN {
        return Err(Error::Generic);
    }

    let len = core::cmp::min(dest.len(), src.len());

    dest[..len].copy_from_slice(&src[..len]);

    Ok(())
}

pub fn do_memcpy(dest: &mut [u8], src: &[u8]) -> Result<(), Error> {
    if dest.len() == 0 || src.len() == 0 {
        return Err(Error::Generic);
    }

    let len = core::cmp::min(dest.len(), src.len());

    dest[..len].copy_from_slice(&src[..len]);

    Ok(())
}

pub fn do_signature(dest: &mut [u8], src: &[u8]) -> Result<(), Error> {
    if dest.len() == 0 || dest.len() < FMAP_SIGNATURE_LEN || src.len() == 0 {
        return Err(Error::Generic);
    }

    dest[..FMAP_SIGNATURE_LEN].copy_from_slice(FMAP_SIGNATURE.as_ref());

    Ok(())
}

/// do_flags - translate strings into flag bitmap
///
/// @dest:	destination memory address
/// @src:	null-terminated string containing ASCII representation of flags
/// @len:	size of destination storage location
///
/// returns () to indicate success
/// returns Error to indicate failure
pub fn do_flags(dest: &mut [u8], src: &[u8]) -> Result<(), Error> {
    if dest.len() == 0 || src.len() == 0 {
        return Err(Error::Generic);
    }

    let mut flags = 0u32;

    if is_zeros(src) {
        for i in dest.iter_mut() {
            *i = 0;
        }
    }

    let srcstr = core::str::from_utf8(src).map_err(|_| Error::Generic)?;
    for lut in FLAG_LUT.iter() {
        if srcstr.find(lut.string()).is_some() {
            flags |= lut.value();
        }
    }

    dest[..size_of::<u32>()].copy_from_slice(&flags.to_le_bytes());
    Ok(())
}

fn is_zeros(b: &[u8]) -> bool {
    for &i in b.iter() {
        if i != 0 {
            return false;
        }
    }
    true
}

/// do_strtoul - do ASCII to (unsigned) integer conversion
///
/// @dest:	destination memory address
/// @src:	null-terminated string containing ASCII representation of number
/// @len:	size of destination storage location
///
/// returns () to indicate success
/// returns Error to indicate failure
pub fn do_strtoul(dest: &mut [u8], src: &[u8]) -> Result<(), Error> {
    if dest.len() == 0 || src.len() == 0 {
        return Err(Error::Generic);
    }

    let is_hex = if src.len() > 1 {
        &src[..2] == b"0x" || &src[..2] == b"0X"
    } else {
        false
    };

    let (psrc, base) = if is_hex {
        (
            core::str::from_utf8(&src[2..]).map_err(|_| Error::Generic)?,
            16,
        )
    } else {
        (core::str::from_utf8(src).map_err(|_| Error::Generic)?, 10)
    };

    let len = dest.len();

    match len {
        1 => {
            let n = u8::from_str_radix(psrc, base).map_err(|_| Error::Generic)?;
            dest[..len].copy_from_slice(n.to_le_bytes().as_ref());
        }
        2 => {
            let n = u16::from_str_radix(psrc, base).map_err(|_| Error::Generic)?;
            dest[..len].copy_from_slice(n.to_le_bytes().as_ref());
        }
        4 => {
            let n = u32::from_str_radix(psrc, base).map_err(|_| Error::Generic)?;
            dest[..len].copy_from_slice(n.to_le_bytes().as_ref());
        }
        8 => {
            let n = u64::from_str_radix(psrc, base).map_err(|_| Error::Generic)?;
            dest[..len].copy_from_slice(n.to_le_bytes().as_ref());
        }
        _ => return Err(Error::Generic),
    }

    Ok(())
}

pub fn doit(line: &str, kv_attrs: &mut [KvAttr]) -> Result<(), Error> {
    let mut offset = 0;
    for kv in kv_attrs.iter_mut() {
        // failed to find the key, abort
        if line[offset..].find(kv.key).is_none() {
            return Err(Error::Generic);
        }

        let mut p = &line[offset..];
        while let Some(i) = p.find(kv.key) {
            if &p[i + kv.key.len()..i + kv.key.len() + 1] == "=" {
                offset += i + kv.key.len() + 1;
                break;
            }
            p = &p[1..];
        }

        if p.len() == 0 {
            return Err(Error::Generic);
        }

        // found key, extract value from remainder of input string
        let value = extract_value(p)?;
        offset += value.len() + 3;

        (kv.handler)(kv.dest, value.as_bytes())?;
    }

    Ok(())
}

impl Fmap {
    pub fn parse(&mut self, line: &str) -> Result<(), Error> {
        let mut signature = [0u8; FMAP_SIGNATURE_LEN];
        let mut ver_major = [0u8; 1];
        let mut ver_minor = [0u8; 1];
        let mut base = [0u8; 8];
        let mut size = [0u8; 4];
        let mut name = [0u8; FMAP_STRLEN];
        let mut nareas = [0u8; 2];

        let mut kv_attrs = [
            KvAttr::create("fmap_signature", signature.as_mut(), do_signature),
            KvAttr::create("fmap_ver_major", ver_major.as_mut(), do_strtoul),
            KvAttr::create("fmap_ver_minor", ver_minor.as_mut(), do_strtoul),
            KvAttr::create("fmap_base", base.as_mut(), do_strtoul),
            KvAttr::create("fmap_size", size.as_mut(), do_strtoul),
            KvAttr::create("fmap_name", name.as_mut(), do_strcpy),
            KvAttr::create("fmap_nareas", nareas.as_mut(), do_strtoul),
        ];

        doit(line, kv_attrs.as_mut())?;

        self.signature = signature;
        self.ver_major = ver_major[0];
        self.ver_minor = ver_minor[0];
        self.base = u64::from_le_bytes(base);
        self.size = u32::from_le_bytes(size);
        self.name = name;

        self.areas = vec![FmapArea::new(); u16::from_le_bytes(nareas) as usize];

        Ok(())
    }
}

impl FmapArea {
    pub fn parse(&mut self, line: &str) -> Result<(), Error> {
        let mut offset = [0u8; 4];
        let mut size = [0u8; 4];
        let mut name = [0u8; FMAP_STRLEN];
        let mut flags = [0u8; 4];

        let mut kv_attrs = [
            KvAttr::create("area_offset", offset.as_mut(), do_strtoul),
            KvAttr::create("area_size", size.as_mut(), do_strtoul),
            KvAttr::create("area_name", name.as_mut(), do_strcpy),
            KvAttr::create("area_flags", flags.as_mut(), do_flags),
        ];

        doit(line, kv_attrs.as_mut())?;

        self.offset = u32::from_le_bytes(offset);
        self.size = u32::from_le_bytes(size);
        self.name = name;
        // FIXME: C flashmap defines FmapArea::flags as u16, but FLAG_LUT flags as u32
        // all flags values (even bitwise-ORed) still fit in u16
        self.flags = u32::from_le_bytes(flags) as u16;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::valstr::str2val;
    use alloc::string::String;

    #[test]
    fn test_extract_value() -> Result<(), Error> {
        // empty kv pair
        assert!(extract_value("").is_err());

        // normal case
        assert_eq!(extract_value("foo=\"bar\"")?, "bar");

        // missing quote
        assert!(extract_value("foo=\"bar").is_err());
        assert!(extract_value("foo=bar\"").is_err());

        Ok(())
    }

    #[test]
    fn test_trivial_helper_function_tests() -> Result<(), Error> {
        let mut dest = [0u8; 512];
        let mut src = [0u8; 512];

        let hello = b"hello world";
        let hello_len = hello.len();

        // do_strcpy
        src[..hello_len].copy_from_slice(hello.as_ref());
        do_strcpy(dest[..hello_len].as_mut(), &src[..hello_len])?;

        assert_eq!(dest[..hello_len], src[..hello_len]);

        assert!(do_strcpy(&mut [], &src[..hello_len]).is_err());
        assert!(do_strcpy(dest.as_mut(), &[]).is_err());

        // length of src exceeds max length
        assert!(do_strcpy(dest.as_mut(), src.as_ref()).is_err());

        // do_memcpy
        assert!(do_memcpy(&mut [], src.as_ref()).is_err());
        assert!(do_memcpy(dest.as_mut(), &[]).is_err());

        do_memcpy(&mut dest[..hello_len], &src[..hello_len])?;

        assert_eq!(dest[..hello_len], src[..hello_len]);

        // do_signature
        assert!(do_signature(&mut [], src.as_ref()).is_err());
        assert!(do_signature(dest.as_mut(), &[]).is_err());

        do_signature(&mut dest[..FMAP_SIGNATURE_LEN], &src[..hello_len])?;

        assert_eq!(&dest[..FMAP_SIGNATURE_LEN], FMAP_SIGNATURE.as_ref());

        Ok(())
    }

    #[test]
    fn test_do_strtoul() -> Result<(), Error> {
        let mut src = [0u8; 32];
        let mut dest8 = [0u8];
        let mut dest16 = [0u8; 2];
        let mut dest32 = [0u8; 4];
        let mut dest64 = [0u8; 8];

        src[..4].copy_from_slice(b"0xff");
        assert!(do_strtoul(dest8.as_mut(), &src[..4]).is_ok());
        assert_eq!(u8::from_le_bytes(dest8), 0xff);

        src[..6].copy_from_slice(b"0xffff");
        assert!(do_strtoul(dest16.as_mut(), &src[..6]).is_ok());
        assert_eq!(u16::from_le_bytes(dest16), 0xffff);

        src[..10].copy_from_slice(b"0xffffffff");
        assert!(do_strtoul(dest32.as_mut(), &src[..10]).is_ok());
        assert_eq!(u32::from_le_bytes(dest32), 0xffff_ffff);

        src[..18].copy_from_slice(b"0xffffffffffffffff");
        assert!(do_strtoul(dest64.as_mut(), &src[..18]).is_ok());
        assert_eq!(u64::from_le_bytes(dest64), 0xffff_ffff_ffff_ffff);

        // invalid length
        assert!(do_strtoul(&mut dest32[..3], src.as_ref()).is_err());

        // null cases
        assert!(do_strtoul(&mut [], &src[..1]).is_err());
        assert!(do_strtoul(dest8.as_mut(), &[]).is_err());

        // leading zeroes
        src[..10].copy_from_slice(b"0x00ffffff");
        assert!(do_strtoul(dest32.as_mut(), &src[..10]).is_ok());
        assert_eq!(u32::from_le_bytes(dest32), 0x00ff_ffff);

        // decimal value
        src[..4].copy_from_slice(b"1000");
        assert!(do_strtoul(dest32.as_mut(), &src[..4]).is_ok());
        assert_eq!(u32::from_le_bytes(dest32), 1000);

        Ok(())
    }

    #[test]
    fn test_do_flags() -> Result<(), Error> {
        let mut src = String::new();
        let mut dest = [0u8; 4];

        assert!(do_flags(&mut [], src.as_ref()).is_err());
        assert!(do_flags(dest.as_mut(), src.as_ref()).is_err());

        // convert each flag individually
        for lut in FLAG_LUT.iter() {
            do_flags(dest.as_mut(), lut.string().as_bytes())?;
            assert_eq!(u32::from_le_bytes(dest), str2val(lut.string(), &FLAG_LUT));
        }

        let mut tmp = 0;
        for (i, lut) in FLAG_LUT.iter().enumerate() {
            // prepend a comma before adding this entry
            if i != 0 {
                src.push(',');
            }

            src.push_str(lut.string());
            tmp |= lut.value();
        }

        do_flags(dest.as_mut(), src.as_bytes())?;
        assert_eq!(u32::from_le_bytes(dest), tmp);

        // zero length
        assert!(do_flags(dest.as_mut(), b"").is_err());

        Ok(())
    }

    fn dummy_handler(_dest: &mut [u8], _src: &[u8]) -> Result<(), Error> {
        Err(Error::Generic)
    }

    #[test]
    fn test_doit() -> Result<(), Error> {
        let mut dest = [0u8; 2048];
        let mut line = String::with_capacity(2048);
        let mut fmap = Fmap::new();
        let mut fmap_area = FmapArea::new();
        let mut attr = [KvAttr::create("foo", dest.as_mut(), do_strcpy)];

        // parse a valid header line
        line.push_str("fmap_signature=\"0x5f5f50414d465f5f\" ");
        line.push_str("fmap_ver_major=\"1\" fmap_ver_minor=\"0\" ");
        line.push_str("fmap_base=\"0x00000000ffe00000\" fmap_size=\"0x200000\" ");
        line.push_str("fmap_name=\"System BIOS\" fmap_nareas=\"4\"");

        assert!(fmap.parse(&line).is_ok());

        // parse a valid fmap area line
        line.clear();
        line.push_str("area_offset=\"0x00040000\" area_size=\"0x00180000\" ");
        line.push_str("area_name=\"FV_MAIN\" area_flags=\"static,compressed\"");
        assert!(fmap_area.parse(&line).is_ok());

        // partially matched key should be ignored
        line.clear();
        line.push_str("foo_bar=\"foobar\" foo=\"bar\"");
        assert!(doit(&line, attr.as_mut()).is_ok());
        assert_ne!(&attr[0].dest[..3], b"bar");

        // nonexistent key
        line.clear();
        line.push_str("nonexistent=\"value\"");
        assert!(doit(&line, attr.as_mut()).is_err());

        // bad value (missing end quote)
        line.clear();
        line.push_str("foo=\"bar");
        assert!(doit(&line, attr.as_mut()).is_err());

        // handler failure
        line.clear();
        line.push_str("foo=\"bar\"");
        attr[0].handler = dummy_handler;
        assert!(doit(&line, attr.as_mut()).is_err());

        Ok(())
    }
}
