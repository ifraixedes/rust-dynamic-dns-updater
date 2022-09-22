//! Command-line interface.

use clap::{ArgEnum, Args, Parser, Subcommand};
use std::vec::Vec;

/// Command-line tool for updating the registered IP of dynamic DNS providers
/// with the public IP of the machine that executes it.
#[derive(Parser)]
#[clap(author, name = "dynamic-dns-updater", version)]
pub struct App {
    #[clap(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
pub enum Command {
    /// Update the DNS of the indicated providers.
    ///
    /// It uses the passed IP otherwise the public IP of this machine revealed
    /// by the first indicated finder with a successful response.
    Update {
        /// Providers to update.
        ///
        /// Format: <provider_id>:[<config_field_name>[=[<config_field_value]]]
        ///
        /// Supported providers (<Name> (<identifier>)):
        /// Duck DNS (duckdns)
        providers: Providers,

        /// Finders to use. When several, they will be requested concurrently for using the first
        /// one that replies.
        ///
        /// Supported finders: ipify.
        #[clap(short = 'f')]
        #[clap(default_value = "ipify")]
        finder: Vec<Finder>,
    },
}

/// Supported providers.
#[derive(Args)]
pub struct Providers {
    /// Duck DNS provider.
    pub duck_dns: Option<DuckDns>,
}

impl std::str::FromStr for Providers {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        const PROVIDERS: [&str; 1] = ["duckdns"];
        match s.split_once(":") {
            Some(("duckdns", settings)) => {
                let p = DuckDns::from_str(settings)?;
                Ok(Self{duck_dns: Some(p)})
            },
            Some((p, _)) => Err(format!("unsupported provider: '{}'.\nThe supported providers identifiers are: {}", p, PROVIDERS.join(", "))),
            None => Err(String::from("invalid provider specifier, the format is: '<provider_id:[<config_field_name>[=[<config_field_value]]]'")),
        }
    }
}

/// Duck DNS provider configuration parameters.
#[derive(Debug)]
pub struct DuckDns {
    /// The API key to use.
    pub key: String,
}

impl std::str::FromStr for DuckDns {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let field = parse_field(s).map_err(|_| "'key' field is required")?;
        match field {
            ("key", Some("")) => Err(String::from("'key' field must have a non-empty value")),
            ("key", Some(val)) => Ok(Self {
                key: val.to_owned(),
            }),
            ("key", _) => Err(String::from("'key' field must have a value")),
            (name, _) => Err(format!(
                "unrecognized field: '{}'. Only 'key' field is accepted and required",
                name
            )),
        }
    }
}

#[derive(ArgEnum, Clone)]
pub enum Finder {
    Ipify,
}

impl std::str::FromStr for Finder {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "ipify" => Ok(Finder::Ipify),
            unmatch => Err(format!("unrecognized finder: '{unmatch}'")),
        }
    }
}

/// Parses a field and returns its name-value pair.
///
/// A field has this syntax: `name[=[value]]`. `name` is the field's name and
/// `value` its associated value, which is optional. A field without value
/// returns `None` for it, when `=` is present but value isn't, it returns
/// `Some(String::from(""))` because the field has value but it's an empty string.
///
/// Values can have any character and fields too, except `'='`.
fn parse_field<'a>(nv: &'a str) -> Result<(&'a str, Option<&'a str>), &'a str> {
    if nv.is_empty() {
        return Err("field's name is missing");
    }

    match nv.split_once('=') {
        Some((n, v)) => {
            if n.is_empty() {
                Err("field's name is missing")
            } else {
                Ok((n, Some(v)))
            }
        }
        None => Ok((nv, None)),
    }
}

/// Parse a string of a comma separated fields and it returns a vector of field name-value pairs.
///
/// The syntax of a single field is documented by the function [`parse_field`], which is used for
/// parsing each field which is split from from the list.
///
/// However, fields in this list has a few more restrictions for supporting fields with commans in
/// their names or values.
///
/// * names and values can contain `','` if they are quoted.
/// * names and value can contain `'"'` if they are escaped with `'\'`, otherwise it interprets them
///   for quoting fields' names and values. They have to be quoted separately, e.g. `"foo"="bar"` is
///   valid, `"foo=var"` is invalid. `'\'` used for escaping are stripped out and they won't be
///   present in names or values.
/// * names and values can contain `'\'` and they don't need to be escaped;
///
/// An error is only returned for invalid inputs which has a field without name, which happens
/// when:
///
/// * field without name. E.g. `=value`, `field1=value1,=value2`
/// * empty field. E.g. `field1=value1,` `,field1=value1`, `field1=value1,,field3=value3`
///
/// Other invalid inputs as, impaired quoted names or values, unquoted names or values which have
/// commas, etc., won't return an error, but it's likely that the list won't have the expected
/// fields or values.
///
/// Note, when `l` is empty, it retusn an empty vector.
// TODO: implement this function with indexes for avoiding allocations, is that possible without
// using `unsafe`?
fn parse_fields_list<'a>(l: &'a str) -> Result<std::vec::Vec<(String, Option<String>)>, String> {
    let mut fields = std::vec::Vec::new();

    let mut name = String::new();
    let mut value = String::new();

    if l.is_empty() {
        return Ok(fields);
    }

    fn unescape(i: &str) -> String {
        i.replace("\\\"", "\"")
    }

    fn is_quoted_ended(i: &str) -> bool {
        i.ends_with('"') && !i.ends_with("\\\"")
    }

    for chunk in l.split(',') {
        if !value.is_empty() {
            // Previous chunk has part of the current value.

            if is_quoted_ended(chunk) {
                // Chunk contains the last part of the quoted value and perhaps the name is also
                // quoted.
                value.push_str(chunk);

                // The name may or may not be quoted, trimmed to ensure adding it unquoted to the
                // list.
                fields.push((
                    unescape(name.trim_matches('"')),
                    Some(unescape(value.trim_matches('"'))),
                ));
                name = String::new();
                value = String::new();
            } else {
                // Chunk contains an intermediate part of the quoted value; we have to add the
                // stripped comma by split because it's part of the value.
                value.push_str(chunk);
                value.push(',');
            }

            continue;
        }

        // Previous chunk doesn't contain part of a value, then this chunk is a beginning or
        // intermediate part of a field.
        let (n, ov) = parse_field(chunk).map_err(|err| format!("invalid field: {}", err))?;

        if n.starts_with('"') {
            // Chunk contains a completed or partial quoted name.

            if !is_quoted_ended(n) {
                // Chunk contains the beginning part of the quoted name.

                if ov.is_some() {
                    // Invalid because an `'='` was found before closing the quotes.
                    return Err("at least one field's name has an impaired quote".to_string());
                }

                // Chunk contains an intermediate part of the quoted name; we have to add the
                // stripped comma by split because it's part of the name.
                name.push_str(n);
                name.push(',');
            } else {
                // Chunk contains the whole quoted name.
                if let Some(v) = ov {
                    if v.starts_with('"') {
                        // Chunk contains completed or partial quoted value.

                        if is_quoted_ended(v) {
                            // Chunk contains a completed field, with a quoted name and value.
                            // Unquote them and add it to the fields list.
                            fields.push((
                                unescape(n.trim_matches('"')),
                                Some(unescape(v.trim_matches('"'))),
                            ));
                        } else {
                            // Chunk contains the beginning of a quoted value; we have to add the
                            // stripped comma by split because it's part of the value.
                            value.push_str(v);
                            value.push(',');
                        }
                    } else {
                        // Chunk contains a completed field, with a quoted name.
                        // name. Unquote the name and add it to the fields list.
                        fields.push((unescape(n.trim_matches('"')), Some(unescape(v))));
                    }
                }
            }

            continue;
        }

        if is_quoted_ended(n) {
            // Chunk contains the ending of quoted name, therefore concatenate with the previous
            // chunks that contains the previous parts of the completed name.
            name.push_str(n);

            if let Some(v) = ov {
                if v.starts_with('"') {
                    if is_quoted_ended(v) {
                        // Chunk contains a completed quoted value.
                        fields.push((
                            unescape(name.trim_matches('"')),
                            Some(unescape(v.trim_matches('"'))),
                        ));
                        name = String::new();
                    } else {
                        // Chunk contains the beginning of a quoted value; we have to add the
                        // stripped comma by split because it's part of the value.
                        value.push_str(v);
                        value.push(',');
                    }
                    continue;
                }

                // Chunk contains the last part of the name and the completed value.
                fields.push((unescape(name.trim_matches('"')), Some(unescape(v))));
            } else {
                // Chunk contains the last part of the name and no value.
                fields.push((unescape(name.trim_matches('"')), None));
            }

            name = String::new();
            continue;
        }

        // Check if previous chunks contained part of a field.
        if name.is_empty() {
            // Chunk contains a completed unquoted name.

            if let Some(v) = ov {
                if v.starts_with('"') {
                    if is_quoted_ended(v) {
                        // Chunk contains a completed quoted value.
                        fields.push((unescape(n), Some(unescape(v.trim_matches('"')))));
                    } else {
                        // Keep the field's name until the field definition ends.
                        name = String::from(n);

                        // Chunk contains the beginning of a quoted value; we have to add the
                        // stripped comma by split because it's part of the value.
                        value.push_str(v);
                        value.push(',');
                    }
                    continue;
                }

                // Chunk contains a completed field with value.
                fields.push((unescape(n), Some(unescape(v))));
            } else {
                // Chunk contains a completed field without value.
                fields.push((unescape(n), None));
            }

            continue;
        }

        // Chunk contains an intermediate part of a quoted name.
        name.push_str(n);
    }

    Ok(fields)
}

#[cfg(test)]
mod test {
    use super::*;

    use std::str::FromStr;

    #[test]
    fn test_duck_dns() {
        {
            // OK.
            let i = "key=test-key";
            let p = DuckDns::from_str(i).unwrap_or_else(|_| panic!("'{}' is a valid input", i));
            assert_eq!(p.key, "test-key", "not properly parsed API key");
        }
        {
            // Error: No key field.
            let i = "api-key=test-key";
            let err = DuckDns::from_str(i).expect_err("no key field");
            assert_eq!(
                &err.to_string(),
                "unrecognized field: 'api-key'. Only 'key' field is accepted and required"
            );
        }
        {
            // Error: Key field without value.
            let i = "key";
            let err = DuckDns::from_str(i).expect_err("key field without value");
            assert_eq!(&err.to_string(), "'key' field must have a value");
        }
        {
            // Error: Key field with empty value.
            let i = "key=";
            let err = DuckDns::from_str(i).expect_err("key field with empty value");
            assert_eq!(&err.to_string(), "'key' field must have a non-empty value");
        }
    }

    #[test]
    fn test_parse_field() {
        {
            // OK: value with no spaces.
            let i = "field=a-value";
            let (f, v) = parse_field(i).unwrap_or_else(|_| panic!("'{}' is a valid input", i));
            assert_eq!(f, "field", "not properly parsed field's name");
            assert_eq!(v, Some("a-value"), "not properly parsed field's value");
        }
        {
            // OK: value with no spaces but optionally quoting.
            let i = r#"field="a-value""#;
            let (f, v) = parse_field(i).unwrap_or_else(|_| panic!("'{}' is a valid input", i));
            assert_eq!(f, "field", "not properly parsed field's name");
            assert_eq!(v, Some("\"a-value\""), "not properly parsed field's value");
        }
        {
            // OK: value with spaces.
            let i = "field=a value ";
            let (f, v) = parse_field(i).unwrap_or_else(|_| panic!("'{}' is a valid input", i));
            assert_eq!(f, "field", "not properly parsed field's name");
            assert_eq!(v, Some("a value "), "not properly parsed field's value");
        }
        {
            // OK: value with new line.
            let i = "field=a va\nlue";
            let (f, v) = parse_field(i).unwrap_or_else(|_| panic!("'{}' is a valid input", i));
            assert_eq!(f, "field", "not properly parsed field's name");
            assert_eq!(v, Some("a va\nlue"), "not properly parsed field's value");
        }
        {
            // OK: empty value.
            let i = "field=";
            let (f, v) = parse_field(i).unwrap_or_else(|_| panic!("'{}' is a valid input", i));
            assert_eq!(f, "field", "not properly parsed field's name");
            assert_eq!(v, Some(""), "not properly parsed field's value");
        }
        {
            // OK: value with equals (i.e. =) symbols.
            let i = "field=a=18 b=10 ";
            let (f, v) = parse_field(i).unwrap_or_else(|_| panic!("'{}' is a valid input", i));
            assert_eq!(f, "field", "not properly parsed field's name");
            assert_eq!(v, Some("a=18 b=10 "), "not properly parsed value");
        }
        {
            // OK: field with spaces.
            let i = "field 1   = wow";
            let (f, v) = parse_field(i).unwrap_or_else(|_| panic!("'{}' is a valid input", i));
            assert_eq!(f, "field 1   ", "not properly parsed field's name");
            assert_eq!(v, Some(" wow"), "not properly parsed value");
        }
        {
            // OK: field with spaces and quoted value
            let i = r#"field 1   =" wow""#;
            let (f, v) = parse_field(i).unwrap_or_else(|_| panic!("'{}' is a valid input", i));
            assert_eq!(f, "field 1   ", "not properly parsed field's name");
            assert_eq!(v, Some("\" wow\""), "not properly parsed value");
        }
        {
            // OK: quoted field's name.
            let i = r#""field "=wow"#;
            let (f, v) = parse_field(i).unwrap_or_else(|_| panic!("'{}' is a valid input", i));
            assert_eq!(f, "\"field \"", "not properly parsed field's name");
            assert_eq!(v, Some("wow"), "not properly parsed value");
        }
        {
            // OK: quoted field's value.
            let i = r#"field="wow""#;
            let (f, v) = parse_field(i).unwrap_or_else(|_| panic!("'{}' is a valid input", i));
            assert_eq!(f, "field", "not properly parsed field's name");
            assert_eq!(v, Some("\"wow\""), "not properly parsed value");
        }
        {
            // OK: quoted field's name and value.
            let i = r#""field"="wow""#;
            let (f, v) = parse_field(i).unwrap_or_else(|_| panic!("'{}' is a valid input", i));
            assert_eq!(f, "\"field\"", "not properly parsed field's name");
            assert_eq!(v, Some("\"wow\""), "not properly parsed value");
        }
        {
            // OK: field's value with quotes.
            let i = r#"field=w"o"w"#;
            let (f, v) = parse_field(i).unwrap_or_else(|_| panic!("'{}' is a valid input", i));
            assert_eq!(f, "field", "not properly parsed field's name");
            assert_eq!(v, Some("w\"o\"w"), "not properly parsed value");
        }
        {
            // OK: field's name with quotes.
            let i = r#"f"ield=wow"#;
            let (f, v) = parse_field(i).unwrap_or_else(|_| panic!("'{}' is a valid input", i));
            assert_eq!(f, "f\"ield", "not properly parsed field's name");
            assert_eq!(v, Some("wow"), "not properly parsed value");
        }
        {
            // OK: field's name and value with quotes.
            let i = r#""field=wow""#;
            let (f, v) = parse_field(i).unwrap_or_else(|_| panic!("'{}' is a valid input", i));
            assert_eq!(f, "\"field", "not properly parsed field's name");
            assert_eq!(v, Some("wow\""), "not properly parsed value");
        }
        {
            // OK: field's name and values with slashes.
            let i = r#"f\iel/d=w\ow"#;
            let (f, v) = parse_field(i).unwrap_or_else(|_| panic!("'{}' is a valid input", i));
            assert_eq!(f, "f\\iel/d", "not properly parsed field's name");
            assert_eq!(v, Some("w\\ow"), "not properly parsed value");
        }
        {
            // OK: field with no value.
            let i = "field";
            let (f, v) = parse_field(i).unwrap_or_else(|_| panic!("'{}' is a valid input", i));
            assert_eq!(f, "field", "not properly parsed field's name");
            assert_eq!(v, None, "not properly parsed value");
        }
        {
            // Error: no field name.
            let i = "=a-value";
            let err = parse_field(i).expect_err("no field's name");
            assert_eq!(&err.to_string(), "field's name is missing");
        }
        {
            // Error: empty.
            let i = "";
            let err = parse_field(i).expect_err("no field's name");
            assert_eq!(&err.to_string(), "field's name is missing");
        }
    }

    #[test]
    fn test_parse_fields_list() {
        {
            // OK: zero fields.
            let l =
                parse_fields_list("").unwrap_or_else(|_| panic!("empty string is a valid input"));

            assert!(l.is_empty(), "zero field-value");
        }
        {
            // OK: one field-value.
            let i = "field=a-value";
            let l = parse_fields_list(i).unwrap_or_else(|_| panic!("'{}' is a valid input", i));

            assert_eq!(l.len(), 1, "one field-value");
            assert_eq!(l[0].0, "field", "not properly parsed field's name");
            assert_eq!(
                l[0].1,
                Some(String::from("a-value")),
                "not properly parsed field's value"
            );
        }
        {
            // OK: more than one field-value.
            let i = "field 1= value 1,field2=value2,field   3  = v a l u e ,field 4,field5=,field6=value=6";
            let l = parse_fields_list(i).unwrap_or_else(|_| panic!("'{}' is a valid input", i));

            assert_eq!(l.len(), 6, "more than one field-value");
            assert_eq!(l[0].0, "field 1", "not properly parsed field's name");
            assert_eq!(
                l[0].1,
                Some(String::from(" value 1")),
                "not properly parsed field's value"
            );
            assert_eq!(l[1].0, "field2", "not properly parsed field's name");
            assert_eq!(
                l[1].1,
                Some(String::from("value2")),
                "not properly parsed field's value"
            );
            assert_eq!(l[2].0, "field   3  ", "not properly parsed field's name");
            assert_eq!(
                l[2].1,
                Some(String::from(" v a l u e ")),
                "not properly parsed field's value"
            );
            assert_eq!(l[3].0, "field 4", "not properly parsed field's name");
            assert_eq!(l[3].1, None, "not properly parsed field's value");
            assert_eq!(l[4].0, "field5", "not properly parsed field's name");
            assert_eq!(
                l[4].1,
                Some(String::from("")),
                "not properly parsed field's value"
            );
            assert_eq!(l[5].0, "field6", "not properly parsed field's name");
            assert_eq!(
                l[5].1,
                Some(String::from("value=6")),
                "not properly parsed field's value"
            );
        }
        {
            // OK: fields values with commas.
            let i = r#"field=value,"field,1"=value1,field 2 =" v,a,l,u,e, ""#;
            let l = parse_fields_list(i).unwrap_or_else(|_| panic!("'{}' is a valid input", i));

            assert_eq!(l.len(), 3, "fields values with commas");
            assert_eq!(l[0].0, "field", "not properly parsed field's name");
            assert_eq!(
                l[0].1,
                Some(String::from("value")),
                "not properly parsed field's value"
            );
            assert_eq!(l[1].0, "field,1", "not properly parsed field's name");
            assert_eq!(
                l[1].1,
                Some(String::from("value1")),
                "not properly parsed field's value"
            );
            assert_eq!(l[2].0, "field 2 ", "not properly parsed field's name");
            assert_eq!(
                l[2].1,
                Some(String::from(" v,a,l,u,e, ")),
                "not properly parsed field's value"
            );
        }
        {
            // OK: fields values with quotes.
            let i = r#"field=value,\"field 1\"=value1,field 2 =\"val\"ue\",\"field_3"#;
            let l = parse_fields_list(i).unwrap_or_else(|_| panic!("'{}' is a valid input", i));

            assert_eq!(l.len(), 4, "fields values with commas");
            assert_eq!(l[0].0, "field", "not properly parsed field's name");
            assert_eq!(
                l[0].1,
                Some(String::from("value")),
                "not properly parsed field's value"
            );
            assert_eq!(l[1].0, "\"field 1\"", "not properly parsed field's name");
            assert_eq!(
                l[1].1,
                Some(String::from("value1")),
                "not properly parsed field's value"
            );
            assert_eq!(l[2].0, "field 2 ", "not properly parsed field's name");
            assert_eq!(
                l[2].1,
                Some(String::from("\"val\"ue\"")),
                "not properly parsed field's value"
            );
            assert_eq!(l[3].0, "\"field_3", "not properly parsed field's name");
            assert_eq!(l[3].1, None, "not properly parsed field's value");
        }
        {
            // OK: fields values with quotes and commas.
            let i = r#"field=\"value\","field ,  1"=value1,field 2 ="val\"u,e""#;
            let l = parse_fields_list(i).unwrap_or_else(|_| panic!("'{}' is a valid input", i));

            assert_eq!(l.len(), 3, "fields values with commas");
            assert_eq!(l[0].0, "field", "not properly parsed field's name");
            assert_eq!(
                l[0].1,
                Some(String::from("\"value\"")),
                "not properly parsed field's value"
            );
            assert_eq!(l[1].0, "field ,  1", "not properly parsed field's name");
            assert_eq!(
                l[1].1,
                Some(String::from("value1")),
                "not properly parsed field's value"
            );
            assert_eq!(l[2].0, "field 2 ", "not properly parsed field's name");
            assert_eq!(
                l[2].1,
                Some(String::from("val\"u,e")),
                "not properly parsed field's value"
            );
        }
        {
            // OK: fields values with quotes, commas, and backslashes.
            let i = r#"\fi\\eld=\"value\","field , 1"=val\ue1,field 2 ="val\\"u,e""#;
            let l = parse_fields_list(i).unwrap_or_else(|_| panic!("'{}' is a valid input", i));

            assert_eq!(l.len(), 3, "fields values with commas");
            assert_eq!(l[0].0, "\\fi\\\\eld", "not properly parsed field's name");
            assert_eq!(
                l[0].1,
                Some(String::from("\"value\"")),
                "not properly parsed field's value"
            );
            assert_eq!(l[1].0, "field , 1", "not properly parsed field's name");
            assert_eq!(
                l[1].1,
                Some(String::from("val\\ue1")),
                "not properly parsed field's value"
            );
            assert_eq!(l[2].0, "field 2 ", "not properly parsed field's name");
            assert_eq!(
                l[2].1,
                Some(String::from("val\\\"u,e")),
                "not properly parsed field's value"
            );
        }
        {
            // Invalid (no error): fields' names and values with unquoted commas.
            let i = "field=value,field,1=value1,field 2 =v,a,l,u,e";
            let l = parse_fields_list(i).unwrap_or_else(|_| panic!("'{}' is a valid input", i));
            assert_eq!(l.len(), 8, "fields values with commas");
            assert_eq!(l[0].0, "field", "not properly parsed field's name");
            assert_eq!(
                l[0].1,
                Some(String::from("value")),
                "not properly parsed field's value"
            );
            assert_eq!(l[1].0, "field", "not properly parsed field's name");
            assert_eq!(l[1].1, None, "not properly parsed field's value");
            assert_eq!(l[2].0, "1", "not properly parsed field's name");
            assert_eq!(
                l[2].1,
                Some(String::from("value1")),
                "not properly parsed field's value"
            );
            assert_eq!(l[3].0, "field 2 ", "not properly parsed field's name");
            assert_eq!(
                l[3].1,
                Some(String::from("v")),
                "not properly parsed field's value"
            );
            assert_eq!(l[4].0, "a", "not properly parsed field's name");
            assert_eq!(l[4].1, None, "not properly parsed field's value");
            assert_eq!(l[5].0, "l", "not properly parsed field's name");
            assert_eq!(l[5].1, None, "not properly parsed field's value");
            assert_eq!(l[6].0, "u", "not properly parsed field's name");
            assert_eq!(l[6].1, None, "not properly parsed field's value");
            assert_eq!(l[7].0, "e", "not properly parsed field's name");
            assert_eq!(l[7].1, None, "not properly parsed field's value");
        }
        {
            // Invalid (no error): field's name with impaired quotes (starts, not ends).
            let i = r#"field=value,\"field1=value1,field 2 =value"#;
            let l = parse_fields_list(i).unwrap_or_else(|_| panic!("'{}' is a valid input", i));
            assert_eq!(l.len(), 3, "fields values with commas");
            assert_eq!(l[0].0, "field", "not properly parsed field's name");
            assert_eq!(
                l[0].1,
                Some(String::from("value")),
                "not properly parsed field's value"
            );
            assert_eq!(l[1].0, "\"field1", "not properly parsed field's name");
            assert_eq!(
                l[1].1,
                Some(String::from("value1")),
                "not properly parsed field's value"
            );
            assert_eq!(l[2].0, "field 2 ", "not properly parsed field's name");
            assert_eq!(
                l[2].1,
                Some(String::from("value")),
                "not properly parsed field's value"
            );
        }
        {
            // Invalid (no error): field's name with impaired quotes (ends, not starts).
            let i = r#"field=value,field1\"=value1,field 2 =value"#;
            let l = parse_fields_list(i).unwrap_or_else(|_| panic!("'{}' is a valid input", i));
            assert_eq!(l.len(), 3, "fields values with commas");
            assert_eq!(l[0].0, "field", "not properly parsed field's name");
            assert_eq!(
                l[0].1,
                Some(String::from("value")),
                "not properly parsed field's value"
            );
            assert_eq!(l[1].0, "field1\"", "not properly parsed field's name");
            assert_eq!(
                l[1].1,
                Some(String::from("value1")),
                "not properly parsed field's value"
            );
            assert_eq!(l[2].0, "field 2 ", "not properly parsed field's name");
            assert_eq!(
                l[2].1,
                Some(String::from("value")),
                "not properly parsed field's value"
            );
        }
        {
            // Invalid (no error): field's value with impaired quotes (starts, not ends).
            let i = r#"field=value,field1=\"value1,field 2 =value"#;
            let l = parse_fields_list(i).unwrap_or_else(|_| panic!("'{}' is a valid input", i));
            assert_eq!(l.len(), 3, "fields values with commas");
            assert_eq!(l[0].0, "field", "not properly parsed field's name");
            assert_eq!(
                l[0].1,
                Some(String::from("value")),
                "not properly parsed field's value"
            );
            assert_eq!(l[1].0, "field1", "not properly parsed field's name");
            assert_eq!(
                l[1].1,
                Some(String::from("\"value1")),
                "not properly parsed field's value"
            );
            assert_eq!(l[2].0, "field 2 ", "not properly parsed field's name");
            assert_eq!(
                l[2].1,
                Some(String::from("value")),
                "not properly parsed field's value"
            );
        }
        {
            // Invalid (no error): field's value with impaired quotes (ends, not starts).
            let i = r#"field=value,field1=value1\",field 2 =value"#;
            let l = parse_fields_list(i).unwrap_or_else(|_| panic!("'{}' is a valid input", i));
            assert_eq!(l.len(), 3, "fields values with commas");
            assert_eq!(l[0].0, "field", "not properly parsed field's name");
            assert_eq!(
                l[0].1,
                Some(String::from("value")),
                "not properly parsed field's value"
            );
            assert_eq!(l[1].0, "field1", "not properly parsed field's name");
            assert_eq!(
                l[1].1,
                Some(String::from("value1\"")),
                "not properly parsed field's value"
            );
            assert_eq!(l[2].0, "field 2 ", "not properly parsed field's name");
            assert_eq!(
                l[2].1,
                Some(String::from("value")),
                "not properly parsed field's value"
            );
        }
        {
            // Invalid (no error): fields' names and values with impaired quotes and commas.
            let i = r#"field=value,\"field,1=value1\",field 2 =value"#;
            let l = parse_fields_list(i).unwrap_or_else(|_| panic!("'{}' is a valid input", i));
            assert_eq!(l.len(), 4, "fields values with commas");
            assert_eq!(l[0].0, "field", "not properly parsed field's name");
            assert_eq!(
                l[0].1,
                Some(String::from("value")),
                "not properly parsed field's value"
            );
            assert_eq!(l[1].0, "\"field", "not properly parsed field's name");
            assert_eq!(l[1].1, None, "not properly parsed field's value");
            assert_eq!(l[2].0, "1", "not properly parsed field's name");
            assert_eq!(
                l[2].1,
                Some(String::from("value1\"")),
                "not properly parsed field's value"
            );
            assert_eq!(l[3].0, "field 2 ", "not properly parsed field's name");
            assert_eq!(
                l[3].1,
                Some(String::from("value")),
                "not properly parsed field's value"
            );
        }
        {
            // Error: Invalid field-value, no field's name.
            let i = "field=value,=value";
            let err = parse_fields_list(i).expect_err("field's name is missing");
            assert_eq!(&err.to_string(), "invalid field: field's name is missing",);
        }
        {
            // Error: Invalid field-value, empty field-value at the beginning.
            let i = ",field=value";
            let err = parse_fields_list(i).expect_err("empty field-value");
            assert_eq!(&err.to_string(), "invalid field: field's name is missing",);
        }
        {
            // Error: Invalid field-value, empty field-value at the end.
            let i = "field=value,";
            let err = parse_fields_list(i).expect_err("empty field-value");
            assert_eq!(&err.to_string(), "invalid field: field's name is missing",);
        }
        {
            // Error: Invalid field-value, empty field-value in the middle.
            let i = "field=value,,field3=value3";
            let err = parse_fields_list(i).expect_err("empty field-value");
            assert_eq!(&err.to_string(), "invalid field: field's name is missing",);
        }
    }
}
