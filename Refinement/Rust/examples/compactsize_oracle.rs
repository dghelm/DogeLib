//! JSON Lines adapter for the compiled public CompactSize reader.
use dogelib_compactsize::{decode, ReadResult};
use serde_json::{json, Value};
use std::io::{self, BufRead, Write};

fn hex_bytes(text: &str) -> Result<Vec<u8>, &'static str> {
    if text.len() % 2 != 0 || !text.bytes().all(|c| c.is_ascii_hexdigit()) {
        return Err("bytes_hex must contain two hexadecimal digits per byte");
    }
    (0..text.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&text[i..i + 2], 16).map_err(|_| "invalid hex"))
        .collect()
}

fn respond(request: &Value, format: &str) -> Result<Value, &'static str> {
    let object = request.as_object().ok_or("request must be an object")?;
    let op = object
        .get("op")
        .and_then(Value::as_str)
        .ok_or("op must be a string")?;
    let allowed: &[&str] = match op {
        "oracle.version" => &["id", "op"],
        "compactsize.read" => &["id", "op", "bytes_hex"],
        _ => return Err("unsupported operation"),
    };
    if object.keys().any(|key| !allowed.contains(&key.as_str())) {
        return Err("unknown argument");
    }
    if op == "oracle.version" {
        return Ok(json!({"format": format}));
    }
    let text = object
        .get("bytes_hex")
        .and_then(Value::as_str)
        .ok_or("bytes_hex must be a string")?;
    let bytes = hex_bytes(text)?;
    match decode(&bytes) {
        ReadResult::Success { value, consumed } => {
            let rest: String = bytes[consumed..]
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect();
            Ok(json!({"value": value.to_string(), "consumed": consumed, "rest_hex": rest}))
        }
        ReadResult::Truncated => Err("truncated"),
        ReadResult::NonCanonical => Err("non_canonical"),
        ReadResult::TooLarge => Err("too_large"),
    }
}

fn response(line: &str, format: &str) -> Value {
    let request = match serde_json::from_str::<Value>(line) {
        Ok(request) => request,
        Err(_) => {
            return json!({"id": null, "error": {"kind": "request", "message": "invalid JSON"}})
        }
    };
    let id = request.get("id").cloned().unwrap_or(Value::Null);
    match respond(&request, format) {
        Ok(ok) => json!({"id": id, "ok": ok}),
        Err(reason @ ("truncated" | "non_canonical" | "too_large")) => {
            json!({"id": id, "error": {"kind": "read", "reason": reason}})
        }
        Err(message) => json!({"id": id, "error": {"kind": "request", "message": message}}),
    }
}

fn main() -> io::Result<()> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if !(args.len() == 2 || (args.len() == 3 && args[2] == "--version"))
        || args[0] != "--oracle-format"
        || !args[1].starts_with("dogelib-oracle/")
        || !args[1]["dogelib-oracle/".len()..]
            .bytes()
            .all(|c| c.is_ascii_digit())
        || args[1] == "dogelib-oracle/"
    {
        eprintln!("usage: compactsize_oracle --oracle-format dogelib-oracle/N [--version]");
        std::process::exit(2);
    }
    let format = format!("{}-rust-compactsize", args[1]);
    let mut stdout = io::BufWriter::new(io::stdout().lock());
    if args.len() == 3 {
        writeln!(stdout, "{}", json!({"format": format}))?;
        return stdout.flush();
    }
    for line in io::stdin().lock().lines() {
        let line = line?;
        if line.trim().is_empty() {
            continue;
        }
        writeln!(stdout, "{}", response(&line, &format))?;
        stdout.flush()?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    const FORMAT: &str = "dogelib-oracle/999-rust-compactsize";

    #[test]
    fn protocol_errors_keep_the_request_id() {
        for request in [
            json!({"id": [1, "two"], "op": "compactsize.encode", "value": "0"}),
            json!({"id": [1, "two"], "op": "tx.read_base", "bytes_hex": "00"}),
            json!({"id": [1, "two"], "op": "compactsize.read", "bytes_hex": "0"}),
            json!({"id": [1, "two"], "op": "compactsize.read", "bytes_hex": "é"}),
            json!({"id": [1, "two"], "op": "compactsize.read", "bytes_hex": "zz"}),
            json!({"id": [1, "two"], "op": "compactsize.read", "bytes_hex": 0}),
            json!({"id": [1, "two"], "op": "compactsize.read"}),
            json!({"id": [1, "two"], "op": "compactsize.read", "bytes_hex": "00", "extra": 1}),
            json!({"id": [1, "two"], "op": "oracle.version", "extra": 1}),
        ] {
            let result = response(&request.to_string(), FORMAT);
            assert_eq!(result["id"], request["id"]);
            assert_eq!(result["error"]["kind"], "request");
        }
        for line in ["{", "null", "[]", "0", "true"] {
            let result = response(line, FORMAT);
            assert_eq!(result["id"], Value::Null);
            assert_eq!(result["error"]["kind"], "request");
        }
    }

    #[test]
    fn projection_version_and_success() {
        assert_eq!(
            response(r#"{"op":"oracle.version"}"#, FORMAT),
            json!({"id": null, "ok": {"format": FORMAT}})
        );
        // Core D1, ReadCompactSize: fd fd 00 is 253 and leaves the suffix unread.
        assert_eq!(
            response(
                r#"{"id":false,"op":"compactsize.read","bytes_hex":"FDFD00AB"}"#,
                FORMAT
            ),
            json!({"id": false, "ok": {"value": "253", "consumed": 3, "rest_hex": "ab"}})
        );
    }

    #[test]
    fn large_numeric_ids_remain_exact() {
        let line = r#"{"id":18446744073709551616,"op":"oracle.version"}"#;
        assert_eq!(
            response(line, FORMAT)["id"].to_string(),
            "18446744073709551616"
        );
    }

    #[test]
    fn reader_errors_keep_their_categories() {
        // D1 and D21 define truncation, canonicality and MAX_SIZE precedence.
        for (bytes, reason) in [
            ("fd", "truncated"),
            ("fdfc00", "non_canonical"),
            ("fe01000002", "too_large"),
            ("ffffffffff00000000", "non_canonical"),
        ] {
            let request = json!({"op": "compactsize.read", "bytes_hex": bytes});
            assert_eq!(
                response(&request.to_string(), FORMAT),
                json!({"id": null, "error": {"kind": "read", "reason": reason}})
            );
        }
    }
}
