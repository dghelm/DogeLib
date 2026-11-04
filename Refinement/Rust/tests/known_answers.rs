// Expected values and error categories are the boundedCases fixtures in
// tests/KnownAnswers.lean at DogeLib commit 4678cb76c68811ea78c7a8fa81662e3f647d8014.
// Their provenance is Core's serialize_tests.cpp and the pinned reader source.
use dogelib_compactsize::{decode, ReadResult};

fn observable(bytes: &[u8]) -> Result<(u64, usize), u8> {
    match decode(bytes) {
        ReadResult::Truncated => Err(0),
        ReadResult::NonCanonical => Err(1),
        ReadResult::TooLarge => Err(2),
        ReadResult::Success { value, consumed } => Ok((value, consumed)),
    }
}

#[test]
fn bounded_known_answers() {
    let cases: &[(&str, &[u8], Result<(u64, usize), u8>)] = &[
        ("line 265: zero in three bytes", &[0xfd, 0x00, 0x00], Err(1)),
        ("line 269: 0xfc in three bytes", &[0xfd, 0xfc, 0x00], Err(1)),
        (
            "line 273: 0xfd in three bytes is OK",
            &[0xfd, 0xfd, 0x00],
            Ok((0xfd, 3)),
        ),
        (
            "line 278: zero in five bytes",
            &[0xfe, 0x00, 0x00, 0x00, 0x00],
            Err(1),
        ),
        (
            "line 282: 0xffff in five bytes",
            &[0xfe, 0xff, 0xff, 0x00, 0x00],
            Err(1),
        ),
        (
            "line 286: zero in nine bytes",
            &[0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
            Err(1),
        ),
        (
            "line 290: 0x01ffffff in nine bytes",
            &[0xff, 0xff, 0xff, 0xff, 0x01, 0x00, 0x00, 0x00, 0x00],
            Err(1),
        ),
        (
            "0xfd in three bytes, then one more byte",
            &[0xfd, 0xfd, 0x00, 0xab],
            Ok((0xfd, 3)),
        ),
        (
            "252 in one byte, then one more byte",
            &[0xfc, 0xfd],
            Ok((252, 1)),
        ),
        ("no bytes", &[], Err(0)),
        ("marker fd with no payload", &[0xfd], Err(0)),
        ("marker fd with 1 of 2 payload bytes", &[0xfd, 0xfd], Err(0)),
        (
            "marker fe with 3 of 4 payload bytes",
            &[0xfe, 0x00, 0x00, 0x01],
            Err(0),
        ),
        (
            "marker ff with 7 of 8 payload bytes",
            &[0xff, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00],
            Err(0),
        ),
        (
            "MAX_SIZE = 0x02000000 is accepted",
            &[0xfe, 0x00, 0x00, 0x00, 0x02],
            Ok((0x02000000, 5)),
        ),
        (
            "0x02000001 is too large",
            &[0xfe, 0x01, 0x00, 0x00, 0x02],
            Err(2),
        ),
        (
            "0xffffffff is too large",
            &[0xfe, 0xff, 0xff, 0xff, 0xff],
            Err(2),
        ),
        (
            "0x100000000 is too large",
            &[0xff, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00],
            Err(2),
        ),
        (
            "0xffffffffffffffff is too large",
            &[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff],
            Err(2),
        ),
        (
            "0xffffffff in nine bytes is non-canonical, not too large",
            &[0xff, 0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00],
            Err(1),
        ),
    ];
    for (name, input, expected) in cases {
        assert_eq!(observable(input), *expected, "{name}");
    }
}

#[test]
fn core_boundary_sweep() {
    // Core serializes and reads i - 1 and i, for powers of two through MAX_SIZE.
    let values: Vec<u64> = (0..26).flat_map(|k| [(1u64 << k) - 1, 1u64 << k]).collect();
    let mut bytes = Vec::new();
    for value in &values {
        if *value < 253 {
            bytes.push(*value as u8);
        } else if *value <= 0xffff {
            bytes.push(253);
            bytes.extend_from_slice(&(*value as u16).to_le_bytes());
        } else {
            bytes.push(254);
            bytes.extend_from_slice(&(*value as u32).to_le_bytes());
        }
    }
    let mut offset = 0;
    for expected in values {
        let (value, consumed) = observable(&bytes[offset..]).unwrap();
        assert_eq!(value, expected);
        assert!(consumed <= bytes.len() - offset);
        offset += consumed;
    }
    assert_eq!(offset, bytes.len());
}
