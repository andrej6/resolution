use regex::Regex;

// TODO: this module should propbably not be public. Need to rework module structure a bit to
// make that happen.

lazy_static! {
    static ref NAME_RE: Regex = Regex::new(r"^[a-zA-Z_][a-zA-Z0-9_]*$").unwrap();
}

pub fn is_valid_name(name: &str) -> bool {
    NAME_RE.is_match(name)
}
