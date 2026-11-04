//! The bounded CompactSize reader of Dogecoin Core v1.14.9.
//! Source: SOURCES.md, D1, src/serialize.h, ReadCompactSize.

/// The complete reader result, with a consumed byte count on success.
pub enum ReadResult {
    Truncated,
    NonCanonical,
    TooLarge,
    Success { value: u64, consumed: usize },
}

/// Append a low byte to a little-endian payload's higher bytes.
/// Each call below has at most seven higher bytes, so neither operation wraps.
pub fn join(low: u8, high: u64) -> u64 {
    high.wrapping_mul(256).wrapping_add(low as u64)
}

/// Read a prefix, preserving Core's truncation, canonicality and size-check order.
/// Success leaves bytes after the consumed prefix unread.
pub fn decode(bytes: &[u8]) -> ReadResult {
    if bytes.len() < 1 {
        return ReadResult::Truncated;
    }
    let marker = bytes[0];
    let value;
    let consumed;
    if marker < 253 {
        value = marker as u64;
        consumed = 1;
    } else if marker == 253 {
        if bytes.len() < 3 {
            return ReadResult::Truncated;
        }
        value = join(bytes[1], bytes[2] as u64);
        consumed = 3;
        if value < 253 {
            return ReadResult::NonCanonical;
        }
    } else if marker == 254 {
        if bytes.len() < 5 {
            return ReadResult::Truncated;
        }
        value = join(bytes[1], join(bytes[2], join(bytes[3], bytes[4] as u64)));
        consumed = 5;
        if value < 0x10000 {
            return ReadResult::NonCanonical;
        }
    } else {
        if bytes.len() < 9 {
            return ReadResult::Truncated;
        }
        value = join(
            bytes[1],
            join(
                bytes[2],
                join(
                    bytes[3],
                    join(
                        bytes[4],
                        join(bytes[5], join(bytes[6], join(bytes[7], bytes[8] as u64))),
                    ),
                ),
            ),
        );
        consumed = 9;
        if value < 0x100000000 {
            return ReadResult::NonCanonical;
        }
    }
    if value > 0x02000000 {
        ReadResult::TooLarge
    } else {
        ReadResult::Success { value, consumed }
    }
}
