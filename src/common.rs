use regex::Regex;

/// Check the given string against the identifier regex `[a-zA-Z_][a-zA-Z0-9_]*`
/// and return whether or not it matches.
pub fn is_valid_name(name: &str) -> bool {
    lazy_static! {
        static ref NAME_RE: Regex = Regex::new(r"^[a-zA-Z_][a-zA-Z0-9_]*$").unwrap();
    }
    NAME_RE.is_match(name)
}
