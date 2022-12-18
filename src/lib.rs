#![no_std]

extern crate alloc;

pub mod kv_list;
pub mod valstr;

mod error;

pub use error::Error;

use alloc::{string::String, vec::Vec};
use core::mem::size_of;
use sha2::{Digest, Sha256};
use valstr::{val2str, ValStr};

pub const FMAP_SIGNATURE_LEN: usize = 8;
pub const FMAP_SIGNATURE: &[u8; FMAP_SIGNATURE_LEN] = b"__FMAP__";
pub const FMAP_VER_MAJOR: u8 = 1;
pub const FMAP_VER_MINOR: u8 = 1;
pub const FMAP_STRLEN: usize = 32;
pub const FMAP_AREA_LEN: usize = 42;

#[repr(C)]
#[derive(PartialEq)]
pub enum FmapFlags {
    Static = 1 << 0,
    Compressed = 1 << 1,
    Ro = 1 << 2,
    Preserve = 1 << 3,
}

pub const FLAG_LUT: [ValStr; 4] = [
    ValStr::create(FmapFlags::Static as u32, "static"),
    ValStr::create(FmapFlags::Compressed as u32, "compressed"),
    ValStr::create(FmapFlags::Ro as u32, "ro"),
    ValStr::create(FmapFlags::Preserve as u32, "preserve"),
];

/// Mapping of volatile and static regions in firmware binary
#[repr(C)]
#[derive(Debug, PartialEq)]
pub struct FmapArea {
    /// Offset relative to base
    offset: u32,
    /// Size in bytes
    size: u32,
    /// Descriptive name
    name: [u8; FMAP_STRLEN],
    /// Flags for this area
    flags: u16,
}

impl FmapArea {
    pub const fn new() -> Self {
        Self {
            offset: 0,
            size: 0,
            name: [0u8; FMAP_STRLEN],
            flags: 0,
        }
    }

    pub fn create(offset: u32, size: u32, name: &[u8], flags: u16) -> Result<Self, Error> {
        if name.len() == 0 {
            return Err(Error::Generic);
        }

        let mut n = [0u8; FMAP_STRLEN];
        n[..core::cmp::min(FMAP_STRLEN, name.len())].copy_from_slice(name);

        Ok(Self {
            offset,
            size,
            name: n,
            flags,
        })
    }

    pub fn to_bytes(&self) -> [u8; FMAP_AREA_LEN] {
        let mut ret = [0u8; FMAP_AREA_LEN];
        let mut idx = 4;

        ret[..idx].copy_from_slice(&self.offset.to_le_bytes());

        ret[idx..idx + size_of::<u32>()].copy_from_slice(&self.size.to_le_bytes());
        idx += size_of::<u32>();

        ret[idx..idx + FMAP_STRLEN].copy_from_slice(&self.name);
        idx += FMAP_STRLEN;

        ret[idx..idx + size_of::<u16>()].copy_from_slice(&self.flags.to_le_bytes());

        ret
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        if bytes.len() < FMAP_AREA_LEN {
            return Err(Error::Generic);
        }

        let mut ret = Self::new();
        let mut idx = 0;

        ret.offset = u32::from_le_bytes(bytes[idx..idx + size_of::<u32>()].try_into().unwrap());
        idx += size_of::<u32>();

        ret.size = u32::from_le_bytes(bytes[idx..idx + size_of::<u32>()].try_into().unwrap());
        idx += size_of::<u32>();

        ret.name.copy_from_slice(&bytes[idx..idx + FMAP_STRLEN]);
        idx += FMAP_STRLEN;

        ret.flags = u16::from_le_bytes(bytes[idx..idx + size_of::<u16>()].try_into().unwrap());

        Ok(ret)
    }

    pub fn flags_to_string(&self) -> String {
        let mut string = String::new();
        let mut flags = self.flags;

        for i in 0..size_of::<u16>() * size_of::<char>() {
            if flags == 0 {
                break;
            }

            if flags & (1 << i) != 0 {
                let tmp = val2str(1 << i, &FLAG_LUT);
                string.push_str(tmp);

                flags &= !(1 << i);
                if flags != 0 {
                    string.push(',');
                }
            }
        }

        string
    }

    pub fn offset(&self) -> u32 {
        self.offset
    }

    pub fn size(&self) -> u32 {
        self.size
    }

    pub fn name(&self) -> &[u8] {
        self.name.as_ref()
    }

    pub fn flags(&self) -> u16 {
        self.flags
    }
}

#[repr(C)]
#[derive(Debug, PartialEq)]
pub struct Fmap {
    /// "__FMAP__" (0x5F5F464D41505F5F)
    signature: [u8; FMAP_SIGNATURE_LEN],
    /// Major version
    ver_major: u8,
    /// Minor version
    ver_minor: u8,
    /// Address of the firmare binary
    base: u64,
    /// Size of the firmware binary in bytes
    size: u32,
    /// Name of this firmware binary
    name: [u8; FMAP_STRLEN],
    /// Fmap areas
    areas: Vec<FmapArea>,
}

impl Fmap {
    pub const fn new() -> Self {
        Self {
            signature: *FMAP_SIGNATURE,
            ver_major: FMAP_VER_MAJOR,
            ver_minor: FMAP_VER_MINOR,
            base: 0,
            size: 0,
            name: [0u8; FMAP_STRLEN],
            areas: Vec::new(),
        }
    }

    pub fn create(base: u64, size: u32, name: &[u8]) -> Self {
        let mut n = [0u8; FMAP_STRLEN];
        let name_len = core::cmp::min(name.len(), FMAP_STRLEN);
        n[..name_len].copy_from_slice(&name[..name_len]);

        Self {
            signature: *FMAP_SIGNATURE,
            ver_major: FMAP_VER_MAJOR,
            ver_minor: FMAP_VER_MINOR,
            base,
            size,
            name: n,
            areas: Vec::new(),
        }
    }

    pub fn signature(&self) -> &[u8] {
        &self.signature
    }

    pub fn version_major(&self) -> u8 {
        self.ver_major
    }

    pub fn version_minor(&self) -> u8 {
        self.ver_minor
    }

    pub fn base(&self) -> u64 {
        self.base
    }

    pub fn size(&self) -> u32 {
        self.size
    }

    pub fn name(&self) -> &[u8] {
        &self.name
    }

    pub fn areas(&self) -> &[FmapArea] {
        &self.areas
    }

    pub fn len(&self) -> usize {
        size_of::<Self>() + (self.areas.len() * size_of::<FmapArea>())
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut ret = Vec::with_capacity(self.len());

        ret.extend_from_slice(&self.signature);
        ret.push(self.ver_major);
        ret.push(self.ver_minor);
        ret.extend_from_slice(&self.base.to_le_bytes());
        ret.extend_from_slice(&self.size.to_le_bytes());
        ret.extend_from_slice(&self.name);
        ret.extend_from_slice(&(self.areas.len() as u16).to_le_bytes());

        for area in self.areas.iter() {
            ret.extend_from_slice(&area.to_bytes());
        }

        ret
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        if bytes.len() < size_of::<Self>() {
            return Err(Error::Generic);
        }

        if &bytes[..FMAP_SIGNATURE_LEN] != FMAP_SIGNATURE {
            return Err(Error::Generic);
        }

        let mut ret = Self::new();
        let mut idx = FMAP_SIGNATURE_LEN;

        ret.ver_major = u8::from_le_bytes(bytes[idx..idx + size_of::<u8>()].try_into().unwrap());
        idx += size_of::<u8>();

        ret.ver_minor = u8::from_le_bytes(bytes[idx..idx + size_of::<u8>()].try_into().unwrap());
        idx += size_of::<u8>();

        if ret.ver_major != FMAP_VER_MAJOR || ret.ver_minor != FMAP_VER_MINOR {
            return Err(Error::Generic);
        }

        ret.base = u64::from_le_bytes(bytes[idx..idx + size_of::<u64>()].try_into().unwrap());
        idx += size_of::<usize>();

        ret.size = u32::from_le_bytes(bytes[idx..idx + size_of::<u32>()].try_into().unwrap());
        idx += size_of::<u32>();

        ret.name.copy_from_slice(&bytes[idx..idx + FMAP_STRLEN]);
        idx += FMAP_STRLEN;

        let nareas = u16::from_le_bytes(bytes[idx..idx + size_of::<u16>()].try_into().unwrap());
        idx += size_of::<u16>();

        ret.areas = Vec::with_capacity(nareas as usize);

        for _i in 0..(nareas as usize) {
            ret.areas
                .push(FmapArea::from_bytes(&bytes[idx..idx + FMAP_AREA_LEN])?);
            idx += FMAP_AREA_LEN;
        }

        Ok(ret)
    }

    /// fmap_find - find FMAP signature in a binary image
    ///
    /// @image:	binary image
    ///
    /// This function does no error checking. The caller is responsible for
    /// verifying that the contents are sane.
    ///
    /// returns deserialized FMAP struct to indicate success
    /// returns <0 to indicate failure
    pub fn find(image: &[u8]) -> Result<Self, Error> {
        let image_len = image.len();
        if image_len == 0 {
            return Err(Error::Generic);
        }

        let ret = if popcnt(image_len) == 1 {
            Self::bsearch(image)?
        } else {
            Self::lsearch(image)?
        };

        Ok(ret)
    }

    /// If image length is a power of 2, use binary search
    fn bsearch(image: &[u8]) -> Result<Fmap, Error> {
        let image_len = image.len();
        let mut fmap_found = false;
        let mut stride = image_len / 2;
        let mut offset = 0;

        // For efficient operation, we start with the largest stride possible
        // and then decrease the stride on each iteration. Also, check for a
        // remainder when modding the offset with the previous stride. This
        // makes it so that each offset is only checked once.
        while stride >= 1 {
            if fmap_found {
                break;
            }

            let mut o = 0;
            while o < (image_len - FMAP_SIGNATURE.len()) {
                if o % (stride * 2) == 0 && offset != 0 {
                    continue;
                }

                if &image[o..o + FMAP_SIGNATURE_LEN] == FMAP_SIGNATURE.as_ref() {
                    fmap_found = true;
                    offset = o;
                    break;
                }

                o += stride;
            }

            stride /= 2;
        }

        if !fmap_found {
            return Err(Error::Generic);
        }

        let fmap = Fmap::from_bytes(&image[offset..])?;
        if offset + fmap.len() > image_len {
            Err(Error::Generic)
        } else {
            Ok(fmap)
        }
    }

    /// Brute force linear search
    fn lsearch(image: &[u8]) -> Result<Fmap, Error> {
        let image_len = image.len();

        if image_len < FMAP_SIGNATURE_LEN || image_len < size_of::<Fmap>() {
            return Err(Error::Generic);
        }

        let mut fmap_found = false;
        let mut offset = 0;

        for o in 0..(image_len - FMAP_SIGNATURE_LEN) {
            if &image[o..o + FMAP_SIGNATURE_LEN] == FMAP_SIGNATURE {
                fmap_found = true;
                offset = o;
                break;
            }
        }

        if !fmap_found {
            return Err(Error::Generic);
        }

        let fmap = Fmap::from_bytes(&image[offset..])?;

        if offset + fmap.len() > image_len {
            return Err(Error::Generic);
        }

        Ok(fmap)
    }

    pub fn append_area(
        &mut self,
        offset: u32,
        size: u32,
        name: &[u8],
        flags: u16,
    ) -> Result<usize, Error> {
        self.areas
            .push(FmapArea::create(offset, size, name, flags)?);
        Ok(self.len())
    }

    pub fn find_area(&self, name: &str) -> Option<&FmapArea> {
        if self.areas.len() == 0 || name.len() == 0 {
            return None;
        }

        for area in self.areas.iter() {
            if &area.name == name.as_bytes() {
                return Some(area);
            }
        }

        None
    }

    /// fmap_get_csum - get the checksum of static regions of an image
    ///
    /// @image:	image to checksum
    ///
    /// fmap_get_csum() will reset, write, and finalize the digest.
    ///
    /// returns digest length if successful
    /// returns <0 to indicate error
    ///
    /// Switch out SHA1 with SHA256 because SHA1 is cryptographically broken, and has been for a
    /// while
    pub fn get_csum(image: &[u8]) -> Result<[u8; 32], Error> {
        let image_len = image.len();

        if image_len == 0 {
            return Err(Error::Generic);
        }

        let fmap = Fmap::find(image)?;

        let mut hasher = Sha256::new();

        // Iterate through flash map and calculate the checksum piece-wise.
        for area in fmap.areas().iter() {
            // skip non-static areas
            if (area.flags & FmapFlags::Static as u16) == 0 {
                continue;
            }

            // sanity check the offset
            if area.size + area.offset > image_len as u32 {
                return Err(Error::Generic);
            }

            let offset = area.offset as usize;
            let size = area.size as usize;
            hasher.update(&image[offset..offset + size]);
        }

        Ok(hasher.finalize()[..].try_into().unwrap())
    }
}

fn popcnt(mut u: usize) -> usize {
    let mut count = 0;

    // K&R method
    while u != 0 {
        u &= u - 1;
        count += 1;
    }

    count
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fmap_create() {
        let base = 0;
        let size = 0x100000;
        let name = b"test_fmap";

        let fmap = Fmap::create(base, size, name.as_ref());
        assert_eq!(fmap.signature(), FMAP_SIGNATURE);

        assert_eq!(fmap.version_major(), FMAP_VER_MAJOR);
        assert_eq!(fmap.version_minor(), FMAP_VER_MINOR);

        assert_eq!(fmap.base(), base);
        assert_eq!(fmap.size(), size);

        assert_eq!(&fmap.name()[..name.len()], name.as_ref());

        assert_eq!(fmap.areas().len(), 0);
    }

    #[test]
    fn test_get_csum() -> Result<(), Error> {
        let base = 0;
        let size = 0x100000;
        let name = b"test_fmap";

        let fmap = Fmap::create(base, size, name.as_ref());
        let csum = [
            227, 176, 196, 66, 152, 252, 28, 20, 154, 251, 244, 200, 153, 111, 185, 36, 39, 174,
            65, 228, 100, 155, 147, 76, 164, 149, 153, 27, 120, 82, 184, 85,
        ];

        assert!(Fmap::get_csum(&[]).is_err());

        let mut image = [0u8; 0x20000];
        let fmap_bytes = fmap.to_bytes();
        image[..fmap_bytes.len()].copy_from_slice(fmap_bytes.as_ref());

        let digest = Fmap::get_csum(&image)?;

        assert_eq!(digest, csum);

        Ok(())
    }

    #[test]
    fn test_fmap_size() -> Result<(), Error> {
        let base = 0;
        let size = 0x100000;
        let name = b"test_fmap";

        let mut fmap = Fmap::create(base, size, name.as_ref());

        // FIXME: still unclear where this extra 32 bytes comes from...
        assert_eq!(fmap.len(), 88);
        assert_eq!(size_of::<Fmap>(), 88);
        assert_eq!(fmap.to_bytes().len(), 56);

        let update_len = fmap.append_area(0, 0, b"some area", 0)?;
        assert_eq!(update_len, 132);
        assert_eq!(fmap.to_bytes().len(), 98);

        Ok(())
    }

    #[test]
    fn test_fmap_serialization() -> Result<(), Error> {
        let base = 0;
        let size = 0x100000;
        let name = b"test_fmap";

        let mut fmap = Fmap::create(base, size, name.as_ref());
        let _update_len = fmap.append_area(0, 0, b"some area", 0);

        let new_fmap = Fmap::from_bytes(&fmap.to_bytes())?;

        assert_eq!(fmap, new_fmap);

        Ok(())
    }

    #[test]
    fn test_append_area() -> Result<(), Error> {
        let base = 0;
        let size = 0x100000;
        let name = b"test_fmap";

        let test_area = FmapArea::create(0x400, 0x10000, b"test_area_1", FmapFlags::Static as u16)?;
        let mut fmap = Fmap::create(base, size, name.as_ref());
        // reject unnamed FmapArea
        assert!(fmap.append_area(0, 0, &[], 0).is_err());

        assert_eq!(fmap.areas().len(), 0);

        let total_size = size_of::<Fmap>() + size_of::<FmapArea>();
        let update_size = fmap.append_area(
            test_area.offset(),
            test_area.size(),
            test_area.name(),
            test_area.flags,
        )?;

        assert_eq!(total_size, update_size);

        assert_eq!(fmap.areas().len(), 1);

        Ok(())
    }

    #[test]
    fn test_find() -> Result<(), Error> {
        // Note: In these tests, we'll use fmap_find() and control usage of
        // lsearch and bsearch by using a power-of-2 total_size. For lsearch,
        // use total_size - 1. For bsearch, use total_size.

        let base = 0;
        let size = 0x100000;
        let name = b"test_fmap";

        let fmap = Fmap::create(base, size, name.as_ref());
        let mut buf = [0u8; 0x100000];

        // test if image length is zero
        assert!(Fmap::find(&[]).is_err());

        // test if no fmap exists
        assert!(Fmap::find(&buf[..buf.len() - 2]).is_err());

        // test if no fmap exists
        assert!(Fmap::find(&buf).is_err());

        // test finding at offset
        let offset = (buf.len() / 2) + 1;
        let fmap_bytes = fmap.to_bytes();

        buf[offset..offset + fmap_bytes.len()].copy_from_slice(&fmap_bytes);

        assert!(Fmap::find(&buf[..buf.len() - 2]).is_ok());
        assert!(Fmap::find(&buf).is_ok());

        // test at offset 0
        buf[..fmap_bytes.len()].copy_from_slice(&fmap_bytes);

        assert!(Fmap::find(&buf[..buf.len() - 2]).is_ok());
        assert!(Fmap::find(&buf).is_ok());

        Ok(())
    }
}
