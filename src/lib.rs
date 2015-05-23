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
/// ```ignore
/// struct BExample {
///     e: i8,
/// }
///
/// impl BElement<BExample> for BExample {
///     //Implementation
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

    /// Decodes BNumber from array of bytes. 
    /// 
    /// Returnes `Ok((position of next token in bencode, parsed BNumber))` 
    /// or `Error` if couldn't parse BNumber.
    /// # Examples
    ///
    /// BNumber must begin with 'i' char and end with 'e' char.
    ///
    /// ```
    /// use bencode::BElement;
    /// use bencode::BNumber;
    /// assert_eq!((4, BNumber::new(300)),
    ///                BNumber::decode("i300e".as_bytes()).ok().expect("invalid"));
    /// ```
    ///
    /// If it's not, then error is generated.
    ///
    /// ```
    /// use bencode::BElement;
    /// use bencode::BNumber;
    /// assert!(BNumber::decode("l300e".as_bytes()).is_err());
    /// ```
    fn decode(encoded: &[u8]) -> Result<(usize, BNumber), &'static str> {
        match encoded[0] as char {
            'i' => {
                let mut i : usize = 1;
                while i < encoded.len() && (encoded[i] as char).is_digit(10) {
                    i += 1;
                }
                if i == encoded.len() {
                    return Err("expected 'e' after number");
                }
                let number: &[u8] = &encoded[1..i];
                match encoded[i] as char {
                    'e' => {
                        let str_number: String = String::from_utf8_lossy(number).into_owned();
                        if let Ok(x) = str_number.parse::<i64>() {
                            Ok((i, BNumber::new(x)))
                        } else {
                            Err("expected correct i64 number")
                        }
                    },
                    _ => Err("expected 'e' after number")
                }
            },
            _ => Err("expected 'i' before number")
        }
    }
}

#[test]
fn test1_bnumber_parse() {
    let (index, number) = BNumber::decode("i300e".as_bytes()).ok().expect("invalid"); 
    assert_eq!(300, number.number);
    assert_eq!(4, index);
}
