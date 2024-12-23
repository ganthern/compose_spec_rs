//! Implementation of the environment variable interpolation as defined in the
//! [compose spec](https://github.com/compose-spec/compose-spec/blob/main/12-interpolation.md)
//!
//! `YamlValues` are interpolated in-place.

use std::{collections::HashMap, iter::Peekable, str::Chars};

use serde::de::Error;
use serde_yaml::{Mapping, Sequence};

use crate::YamlValue;

#[derive(Debug, Default, Clone, PartialEq, Eq)]
/// Resolves values for a given key from the relevant sources (.env files, process environment, ...)
pub(crate) struct EnvironmentResolver {
    /// map of all resolvable variable names
    vars: HashMap<String, String>,
}

impl EnvironmentResolver {
    /// construct a new instance that contains not values
    pub(crate) fn new() -> Self {
        Self {
            vars: HashMap::default(),
        }
    }

    /// read the processes' environment and add them as interpolatable variables
    pub(crate) fn read_env(&mut self) -> &mut Self {
        self.add_vars(get_envs())
    }

    pub(crate) fn add_vars(&mut self, new_vars: HashMap<String, String>) -> &mut Self {
        for (key, value) in new_vars {
            self.vars.insert(key, value);
        }
        self
    }

    /// get the value associated with the given key. If the sources don't contain a valid
    /// UTF-8 String for the key, None is returned.
    pub(crate) fn get(&self, key: impl AsRef<str>) -> Option<&str> {
        self.vars.get(key.as_ref()).map(String::as_str)
    }
}

/// get a map of the processes environment variables
fn get_envs() -> HashMap<String, String> {
    std::env::vars().collect()
}

/// recursively interpolate all nested YAML strings containing variables.
/// will return the first failure to replace a variable.
pub(crate) fn interpolate_value(
    vars: &EnvironmentResolver,
    value: &mut YamlValue,
) -> serde_yaml::Result<()> {
    match value {
        YamlValue::String(s) => {
            let new_s = interpolate_string(vars, s)?;
            let _ = std::mem::replace(value, YamlValue::String(new_s));
        }
        YamlValue::Sequence(sequence) => interpolate_sequence(vars, sequence)?,
        YamlValue::Mapping(mapping) => interpolate_mapping(vars, mapping)?,
        _ => {}
    };
    Ok(())
}

/// try to interpolate variables in each of the elements of the given sequence.
fn interpolate_sequence(
    vars: &EnvironmentResolver,
    sequence: &mut Sequence,
) -> serde_yaml::Result<()> {
    for element in sequence.iter_mut() {
        interpolate_value(vars, element)?;
    }
    Ok(())
}

/// try to interpolate variables in each of the values of the mapping. keys are never interpolated.
fn interpolate_mapping(
    vars: &EnvironmentResolver,
    mapping: &mut Mapping,
) -> serde_yaml::Result<()> {
    for (_key, value) in mapping.iter_mut() {
        interpolate_value(vars, value)?;
    }
    Ok(())
}

/// parse the given `String` and return a new `String`, replacing  any encountered
/// variables with the value returned by `vars`
fn interpolate_string(vars: &EnvironmentResolver, value: &str) -> serde_yaml::Result<String> {
    let mut output = String::with_capacity(value.len());
    let mut iter = value.chars().peekable();
    loop {
        iter = match iter.peek() {
            Some('$') => parse_variable_start(iter, vars, &mut output)?,
            Some(_) => parse_literal(iter, vars, &mut output)?,
            None => break,
        }
    }

    Ok(output)
}

/// format a readable error message using `serde_yaml::Error::custom`
/// the three arguments are
/// * the message (which cannot contain placeholders)
/// * the current output string
/// * the iterator containing the rest of the string we tried to parse
macro_rules! interpolate_err {
    ($lit:expr, $out:expr, $rest:expr) => {{
        let lit: &str = $lit;
        let out: String = $out.clone();
        let rest: String = $rest.clone().collect();
        let msg = format!(r#"{} | output: "{}" | rest: "{}" "#, lit, out, rest);
        Err(serde_yaml::Error::custom(msg))
    }};
}

/// the iterator type used to iterate the source
type SourceIter<'a> = Peekable<Chars<'a>>;

///
fn parse_variable_start<'i>(
    mut iter: SourceIter<'i>,
    vars: &EnvironmentResolver,
    output: &mut String,
) -> serde_yaml::Result<SourceIter<'i>> {
    // check that the iterator points to a $
    match iter.next() {
        Some('$') => {}
        _ => interpolate_err!("expected $", output, iter)?,
    }

    // check if it's escaped. if so, consume & push $ to output and return iter.
    // if not, continue with a braced or non-braced variable.
    match iter.peek() {
        Some('$') => {
            let _ = iter.next();
            output.push('$');
            Ok(iter)
        }
        Some('{') => parse_braced_variable_start(iter, vars, output),
        _ => parse_variable_name(iter, vars, output),
    }
}

/// parse a braced variable: `{NAME}`
fn parse_braced_variable_start<'a>(
    mut iter: SourceIter<'a>,
    vars: &EnvironmentResolver,
    output: &mut String,
) -> serde_yaml::Result<SourceIter<'a>> {
    // check that the iterator points to a $
    match iter.next() {
        Some('{') => {}
        _ => interpolate_err!("expected {", output, iter)?,
    }
    parse_braced_variable_name(iter, vars, output)
}

/// parse the name of an unbraced variable and replace it with its value
fn parse_variable_name<'a>(
    mut iter: SourceIter<'a>,
    vars: &EnvironmentResolver,
    output: &mut String,
) -> serde_yaml::Result<SourceIter<'a>> {
    match iter.peek() {
        Some('_' | 'a'..='z' | 'A'..='Z') => {}
        _ => interpolate_err!("expected $|{|_|a-z|A-Z", output, iter)?,
    }

    // consume & push until we know the variable name ended.
    let mut name = String::new();
    while let Some(character @ ('a'..='z' | 'A'..='Z' | '0'..='9' | '_')) = iter.peek() {
        name.push(*character);
        let _ = iter.next();
    }

    if let Some(value) = vars.get(&name) {
        output.push_str(value);
        Ok(iter)
    } else {
        interpolate_err!("unbound variable", name, iter)
    }
}

/// parse a variable name and push the associated value into `output`
fn parse_braced_variable_name<'a>(
    mut iter: SourceIter<'a>,
    vars: &EnvironmentResolver,
    output: &mut String,
) -> serde_yaml::Result<SourceIter<'a>> {
    // the next character should be the start of a variable name.
    match iter.peek() {
        Some('_' | 'a'..='z' | 'A'..='Z') => {}
        _ => interpolate_err!("expected $|{|_|a-z|A-Z", output, iter)?,
    }

    // consume & push until we know the variable name ended.
    let mut name = String::new();
    loop {
        match iter.next() {
            Some(':' | '?' | '-' | '$') => todo!("default values, error messagesi, nested"),
            Some(' ') => todo!("unbraced variable name with spaces?"),
            Some('}') => break,
            Some(character) => {
                name.push(character);
            }
            _ => interpolate_err!("expected variable name", output, iter)?,
        }
    }

    if let Some(value) = vars.get(&name) {
        output.push_str(value);
        Ok(iter)
    } else {
        interpolate_err!("unbound variable", name, iter)
    }
}

/// parse a character that's not part of a variable name and not a `$`
fn parse_literal<'i>(
    mut iter: SourceIter<'i>,
    _vars: &EnvironmentResolver,
    output: &mut String,
) -> serde_yaml::Result<SourceIter<'i>> {
    match iter.next() {
        Some('$') => interpolate_err!("unexpected '$'", output, iter),
        None => interpolate_err!("input ended unexpectedly", output, iter),
        Some(character) => {
            output.push(character);
            Ok(iter)
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::environment_interpolation::{interpolate_string, EnvironmentResolver};

    #[test]
    fn interpolate_blank_strings() {
        let res = EnvironmentResolver::new();
        assert_eq!(interpolate_string(&res, "").expect("failed"), "");
        assert_eq!(interpolate_string(&res, " ").expect("failed"), " ");
    }

    #[test]
    fn interpolate_without_variables() {
        let res = EnvironmentResolver::new();
        assert_eq!(interpolate_string(&res, "abc").expect("failed"), "abc");
        assert_eq!(interpolate_string(&res, "a{c").expect("failed"), "a{c");
        assert_eq!(
            interpolate_string(&res, "/this/is/a/path").expect("failed"),
            "/this/is/a/path"
        );
    }

    #[test]
    fn interpolate_with_escaped_dollar() {
        let res = EnvironmentResolver::new();
        assert_eq!(interpolate_string(&res, "$$").expect("failed"), "$");
        assert_eq!(interpolate_string(&res, "$$$$").expect("failed"), "$$");
        assert_eq!(interpolate_string(&res, "$$ $$").expect("failed"), "$ $");
        assert_eq!(
            interpolate_string(&res, "$$ab$$cd$$ef").expect("failed"),
            "$ab$cd$ef"
        );
    }

    #[test]
    fn interpolate_with_unterminated_brace() {
        let res = EnvironmentResolver::new();
        let result = interpolate_string(&res, "${").expect_err("did not fail");
        assert_eq!(result.to_string(), "");
    }

    #[test]
    fn interpolate_with_unbound_variable_unbraced() {
        let res = EnvironmentResolver::new();
        let result = interpolate_string(&res, "$MOO").expect_err("did not fail");
        assert!(result.to_string().contains("unbound variable"));
        assert!(result.to_string().contains("MOO"));
    }

    #[test]
    fn interpolate_unbraced_variable() {
        let mut res = EnvironmentResolver::new();
        res.add_vars(HashMap::from([
            ("_".into(), "UNDERSCORE".into()),
            ("__".into(), "DOUBLESCORE".into()),
            ("a_".into(), "ALPHASCORE".into()),
        ]));
        assert_eq!(
            interpolate_string(&res, "_ is $_").expect("failed"),
            "_ is UNDERSCORE"
        );
        assert_eq!(
            interpolate_string(&res, "__ is $__").expect("failed"),
            "__ is DOUBLESCORE"
        );
        assert_eq!(
            interpolate_string(&res, "__ is $__ and $a_").expect("failed"),
            "__ is DOUBLESCORE and ALPHASCORE"
        );
    }
}
