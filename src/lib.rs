//! A module, providing way to parse Bencoded files (e.g. torrent files).
//!
//! Contains all types of elements (`BNumber`, `BList`, `BDictionary`, `BString`), which
//! have trait `BElement` with decoding functionality.

use std::fmt::Formatter;
use std::fmt::Debug;
use std::fmt::Error;

/// Trait for all bencode elements.
///
/// Provides way to decode some type of element `T`, which must have trait `BElement`, from
/// array of bytes
///
/// # Examples
///
/// Simple implementation.
///
/// ```rust
/// use bencode::BElement;
///
/// struct BExample {
///     e: i8,
/// }
///
/// impl BElement<BExample> for BExample {
///     fn decode(encoded: &[u8]) -> Result<(usize, BExample), &'static str> {
///         Err("No implementation, sorry")
///     }
/// }
/// ```
pub trait BElement<T> where T: BElement<T> {
    /// Decodes element from array of bytes.
    /// 
    /// Returns `Ok((position of last used byte in array of bytes, parsed element))` or
    /// `Err` if parse has failed.
    fn decode(encoded: &[u8]) -> Result<(usize, T), &'static str>;
}

/// Struct for representing numbers in Bencode format.
pub struct BNumber {
    /// Real number, represented by `BNumber`.
    number: i64,
}

impl BNumber {
    /// Simple constructor from one `i64`.
    pub fn new(number: i64) -> BNumber {
        BNumber { number: number }
    }
}

/// Basic equivalence relation.
///
/// Checks for equality simply using `BNumber`'s `number` field. Works exactly
/// like equivalence in i64.
impl PartialEq for BNumber {
    fn eq(&self, other: &Self) -> bool {
        self.number == other.number
    }

    fn ne(&self, other: &Self) -> bool {
        self.number != other.number
    }
}

/// Guarantees to be reflexive.
impl Eq for BNumber {
    
}

/// Simple `Debug` implementation.
///
/// Works just like `i64::fmt`.
impl Debug for BNumber {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        self.number.fmt(f)
    }
}

impl BElement<BNumber> for BNumber {

    /// Decodes `BNumber` from array of bytes. 
    /// 
    /// Returnes `Ok((position of last used byte in passed array, parsed BNumber))` 
    /// or `Err` if couldn't parse BNumber correctly.
    /// # Examples
    ///
    /// BNumber must begin with 'i' char and end with 'e' char.
    ///
    /// ```rust
    /// use bencode::BElement;
    /// use bencode::BNumber;
    /// assert_eq!((4, BNumber::new(300)),
    ///                BNumber::decode("i300e".as_bytes()).ok().expect("invalid"));
    /// assert_eq!((5, BNumber::new(-204)),
    ///                BNumber::decode("i-204e".as_bytes()).ok().expect("invalid"));
    /// ```
    ///
    /// If it's not, then error is generated.
    ///
    /// ```rust
    /// use bencode::BElement;
    /// use bencode::BNumber;
    /// assert!(BNumber::decode("l300e".as_bytes()).is_err());
    /// ```
    /// 
    /// Also error is generated, when number isn't valid or is too big for `i64`.
    /// 
    /// ```rust
    /// use bencode::BElement;
    /// use bencode::BNumber;
    /// assert!(BNumber::decode("i400000000000000000000000000000000000000000000e".as_bytes()).is_err());
    /// ```
    fn decode(encoded: &[u8]) -> Result<(usize, BNumber), &'static str> {
        if encoded.len() < 1 {
            Err("empty string isn't valid BNumber")
        } else {
            match encoded[0] as char {
                'i' => {
                    let mut i : usize = 1;
                    while i < encoded.len() && encoded[i] as char != 'e' {
                        i += 1;
                    }
                    if i == encoded.len() {
                        return Err("expected 'e' after number");
                    }
                    let number: &[u8] = &encoded[1..i];
                    let str_number: String = String::from_utf8_lossy(number).into_owned();
                    if let Ok(x) = str_number.parse::<i64>() {
                        Ok((i, BNumber::new(x)))
                    } else {
                        Err("expected correct i64 number")
                    }
                },
                _ => Err("expected 'i' before number")
            }
        }
    }
}

/// Struct for representing string (byte sequence) in Bencode format.
pub struct BString {
    /// Sequence of bytes, contained in this `BString`.
    data: String,
}

/// Basic equivalence relation.
///
/// Checks for equality simply using `BString`'s `data` field. Works exactly
/// like equivalence in &[u8].
impl PartialEq for BString {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }

    fn ne(&self, other: &Self) -> bool {
        self.data != other.data
    }
}

/// Guarantees to be reflexive.
impl Eq for BString {
    
}

/// Simple `Debug` implementation.
///
/// Works just like `[u8]::fmt`.
impl Debug for BString{
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        self.data.fmt(f)
    }
}

impl BString {
    /// Simple constructor from array of bytes.
    pub fn new(data: &[u8]) -> BString {
        BString { data: String::from_utf8_lossy(data).into_owned() }
    }
}

impl BElement<BString> for BString {
    /// Decodes `BString` from array of bytes.
    /// 
    /// Returns `Ok((position of last used byte in passed array, parsed BString))`
    /// or `Err` if couldn't parse `BString` correctly.
    /// # Examples
    /// 
    /// `BString` must have following structure: <length>:<data>, where data - sequence
    /// of bytes with corresponding length.
    ///
    /// ```
    /// use bencode::BElement;
    /// use bencode::BString;
    ///
    /// assert_eq!((4, BString::new("abc".as_bytes())), 
    ///            BString::decode("3:abc".as_bytes()).ok().expect("invalid"));
    /// ```
    fn decode(encoded: &[u8]) -> Result<(usize, BString), &'static str> {
        let mut i: usize = 0;
        while i < encoded.len() && encoded[i] as char != ':' {
            i += 1;
        }
        if i == encoded.len() {
            Err("expected :, but end was found")
        } else {
            let length: &[u8] = &encoded[0..i];
            if let Ok(x) = String::from_utf8_lossy(length).into_owned().parse::<usize>() {
                if i + x + 1 <= encoded.len() {
                    let value: &[u8] = &encoded[i + 1..i + x + 1];
                    Ok((i + x, BString::new(value)))
                } else {
                    Err("expected more bytes, but end was found")
                }
            } else {
                Err("expected correct usize number, representing length")
            }
        }
    }
}

/// Simple test module.
#[cfg(test)]
mod bnumber_tests {
    extern crate rand;

    use super::*;

    fn test_bnumber(string: &[u8], index: usize, result: i64) {
        let (ind, num) = BNumber::decode(string).ok().expect("invalid test");
        assert_eq!(result, num.number);
        assert_eq!(index, ind);
    }

    fn test_bnumber_invalid(string: &[u8], expected: &str) {
        let error = BNumber::decode(string).err().expect("invalid test");
        assert_eq!(expected, error);
    }

    #[test]
    fn test1_bnumber_simple() {
        test_bnumber("i300e".as_bytes(), 4, 300);
    }

    #[test]
    fn test2_bnumber_negative() {
        test_bnumber("i-23487e".as_bytes(), 7, -23487);
    }

    #[test]
    fn test3_bnumber_invalid_format() {
        test_bnumber_invalid("l487e".as_bytes(), "expected 'i' before number");
    }

    #[test]
    fn test4_bnumber_invalid_format() {
        test_bnumber_invalid("i487k".as_bytes(), "expected 'e' after number");
    }

    #[test]
    fn test5_bnumber_invalid_number() {
        test_bnumber_invalid("i-650-4e".as_bytes(), "expected correct i64 number");
    }

    #[test]
    fn test6_bnumber_too_big_number() {
        test_bnumber_invalid("i2398475629384765298346529384756293487562923452983e".as_bytes()
                             , "expected correct i64 number");
    }

    #[test]
    fn test7_bnumber_zero() {
        test_bnumber("i0e".as_bytes(), 2, 0);
    }

    #[test]
    fn test8_bnumer_empty_number() {
        test_bnumber_invalid("ie".as_bytes(), "expected correct i64 number");
    }

    #[test]
    fn test9_bnumer_too_short() {
        test_bnumber_invalid("i".as_bytes(), "expected 'e' after number");
    }

    #[test]
    fn test10_bnumer_even_shorter() {
        test_bnumber_invalid("".as_bytes(), "empty string isn't valid BNumber");
    }

    #[test]
    fn test11_bnumer_stress() {
        for _ in 0..100000 {
            let number: i64 = rand::random::<i64>();
            let string: String = format!("i{}e", number);
            test_bnumber(string.as_bytes(), string.len() - 1, number);
        }
    }
}

#[cfg(test)]
mod bstring_tests {
    use super::*;
    fn test_bstring(string: &[u8], index: usize, result: String) {
        let (ind, bstr) = BString::decode(string).ok().expect("invalid test");
        assert_eq!(index, ind);
        assert_eq!(result, bstr.data);
    }

    fn test_bstring_invalid(string: &[u8], expected: &str) {
        let error = BString::decode(string).err().expect("invalid test");
        assert_eq!(expected, error);
    }

    #[test]
    fn test1_bstring_simple() {
        test_bstring("3:abc".as_bytes(), 4, "abc".to_string());
    }

    #[test]
    fn test2_bstring_short() {
        test_bstring("1:a".as_bytes(), 2, "a".to_string());
    }

    #[test]
    fn test3_bstring_even_shorter() {
        test_bstring("0:".as_bytes(), 1, "".to_string());
    }

    #[test]
    fn test4_bstring_digits() {
        test_bstring("5:12345".as_bytes(), 6, "12345".to_string());
    }

    #[test]
    fn test5_bstring_bad_symbols() {
        test_bstring("14:!@#$%^&*()_+-=".as_bytes(), 16, "!@#$%^&*()_+-=".to_string());
    }

    #[test]
    fn test6_bstring_empty() {
        test_bstring_invalid("".as_bytes(), "expected :, but end was found");
    }

    #[test]
    fn test7_bstring_bad_len() {
        test_bstring_invalid("1:".as_bytes(), "expected more bytes, but end was found");
    }

    #[test]
    fn test8_bstring_no_colon() {
        test_bstring_invalid("128911".as_bytes(), "expected :, but end was found");
    }

    #[test]
    fn test9_bstring_invalid_len() {
        test_bstring_invalid("2a:a".as_bytes(), "expected correct usize number, representing length");
    }

    #[test]
    fn test10_bstring_colon_first() {
        test_bstring_invalid(":123".as_bytes(), "expected correct usize number, representing length");
    }
}
