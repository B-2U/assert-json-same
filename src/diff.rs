use crate::core_ext::{Indent, Indexes};
use crate::{CompareMode, Config, NumericMode};
use float_cmp::{ApproxEq, FloatMargin};
use serde_json::Value;
use std::{collections::HashSet, fmt};

pub(crate) fn diff<'a>(lhs: &'a Value, rhs: &'a Value, config: Config) -> Vec<Difference<'a>> {
    let mut acc = vec![];
    diff_with(lhs, rhs, config, Path::Root, &mut acc);
    acc
}

fn diff_with<'a>(
    lhs: &'a Value,
    rhs: &'a Value,
    config: Config,
    path: Path<'a>,
    acc: &mut Vec<Difference<'a>>,
) {
    let mut folder = DiffFolder {
        rhs,
        path,
        acc,
        config,
    };

    fold_json(lhs, &mut folder);
}

#[derive(Debug)]
struct DiffFolder<'a, 'b> {
    rhs: &'a Value,
    path: Path<'a>,
    acc: &'b mut Vec<Difference<'a>>,
    config: Config,
}

macro_rules! direct_compare {
    ($name:ident) => {
        fn $name(&mut self, lhs: &'a Value) {
            if self.rhs != lhs {
                self.acc.push(Difference {
                    lhs: Some(lhs),
                    rhs: Some(&self.rhs),
                    path: self.path.clone(),
                    config: self.config.clone(),
                });
            }
        }
    };
}

impl<'a, 'b> DiffFolder<'a, 'b> {
    direct_compare!(on_null);
    direct_compare!(on_bool);
    direct_compare!(on_string);

    fn on_number(&mut self, lhs: &'a Value) {
        let is_equal = match self.config.numeric_mode {
            NumericMode::Strict => self.rhs == lhs,
            NumericMode::AssumeFloat => self.rhs.as_f64() == lhs.as_f64(),
            NumericMode::AssumeFloatEpsilon(epsilon) => match (lhs.as_f64(), self.rhs.as_f64()) {
                (Some(lhs_f64), Some(rhs_f64)) => {
                    lhs_f64.approx_eq(rhs_f64, float_cmp::F64Margin::default().epsilon(epsilon))
                }
                _ => false,
            },
        };
        if !is_equal {
            self.acc.push(Difference {
                lhs: Some(lhs),
                rhs: Some(self.rhs),
                path: self.path.clone(),
                config: self.config.clone(),
            });
        }
    }

    fn on_array(&mut self, lhs: &'a Value) {
        if let Some(rhs) = self.rhs.as_array() {
            let lhs = lhs.as_array().unwrap();

            match self.config.compare_mode {
                CompareMode::Inclusive => {
                    for (idx, rhs) in rhs.iter().enumerate() {
                        let path = self.path.append(Key::Idx(idx));

                        if let Some(lhs) = lhs.get(idx) {
                            diff_with(lhs, rhs, self.config.clone(), path, self.acc)
                        } else {
                            self.acc.push(Difference {
                                lhs: None,
                                rhs: Some(self.rhs),
                                path,
                                config: self.config.clone(),
                            });
                        }
                    }
                }
                CompareMode::Strict => {
                    let all_keys = rhs
                        .indexes()
                        .into_iter()
                        .chain(lhs.indexes())
                        .collect::<HashSet<_>>();
                    for key in all_keys {
                        let path = self.path.append(Key::Idx(key));

                        match (lhs.get(key), rhs.get(key)) {
                            (Some(lhs), Some(rhs)) => {
                                diff_with(lhs, rhs, self.config.clone(), path, self.acc);
                            }
                            (None, Some(rhs)) => {
                                self.acc.push(Difference {
                                    lhs: None,
                                    rhs: Some(rhs),
                                    path,
                                    config: self.config.clone(),
                                });
                            }
                            (Some(lhs), None) => {
                                self.acc.push(Difference {
                                    lhs: Some(lhs),
                                    rhs: None,
                                    path,
                                    config: self.config.clone(),
                                });
                            }
                            (None, None) => {
                                unreachable!("at least one of the maps should have the key")
                            }
                        }
                    }
                }
            }
        } else {
            self.acc.push(Difference {
                lhs: Some(lhs),
                rhs: Some(self.rhs),
                path: self.path.clone(),
                config: self.config.clone(),
            });
        }
    }

    fn on_object(&mut self, lhs: &'a Value) {
        if let Some(rhs) = self.rhs.as_object() {
            let lhs = lhs.as_object().unwrap();

            match self.config.compare_mode {
                CompareMode::Inclusive => {
                    for (key, rhs) in rhs.iter() {
                        let path = self.path.append(Key::Field(key));

                        if let Some(lhs) = lhs.get(key) {
                            diff_with(lhs, rhs, self.config.clone(), path, self.acc)
                        } else {
                            self.acc.push(Difference {
                                lhs: None,
                                rhs: Some(self.rhs),
                                path,
                                config: self.config.clone(),
                            });
                        }
                    }
                }
                CompareMode::Strict => {
                    let all_keys = rhs.keys().chain(lhs.keys()).collect::<HashSet<_>>();
                    for key in all_keys {
                        let path = self.path.append(Key::Field(key));

                        match (lhs.get(key), rhs.get(key)) {
                            (Some(lhs), Some(rhs)) => {
                                diff_with(lhs, rhs, self.config.clone(), path, self.acc);
                            }
                            (None, Some(rhs)) => {
                                self.acc.push(Difference {
                                    lhs: None,
                                    rhs: Some(rhs),
                                    path,
                                    config: self.config.clone(),
                                });
                            }
                            (Some(lhs), None) => {
                                self.acc.push(Difference {
                                    lhs: Some(lhs),
                                    rhs: None,
                                    path,
                                    config: self.config.clone(),
                                });
                            }
                            (None, None) => {
                                unreachable!("at least one of the maps should have the key")
                            }
                        }
                    }
                }
            }
        } else {
            self.acc.push(Difference {
                lhs: Some(lhs),
                rhs: Some(self.rhs),
                path: self.path.clone(),
                config: self.config.clone(),
            });
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Difference<'a> {
    path: Path<'a>,
    lhs: Option<&'a Value>,
    rhs: Option<&'a Value>,
    config: Config,
}

impl<'a> fmt::Display for Difference<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let json_to_string = |json: &Value| serde_json::to_string_pretty(json).unwrap();

        match (&self.config.compare_mode, &self.lhs, &self.rhs) {
            (CompareMode::Inclusive, Some(actual), Some(expected)) => {
                writeln!(f, "json atoms at path \"{}\" are not equal:", self.path)?;
                writeln!(f, "    expected:")?;
                writeln!(f, "{}", json_to_string(expected).indent(8))?;
                writeln!(f, "    actual:")?;
                write!(f, "{}", json_to_string(actual).indent(8))?;
            }
            (CompareMode::Inclusive, None, Some(_expected)) => {
                write!(
                    f,
                    "json atom at path \"{}\" is missing from actual",
                    self.path
                )?;
            }
            (CompareMode::Inclusive, Some(_actual), None) => {
                unreachable!("stuff missing actual wont produce an error")
            }
            (CompareMode::Inclusive, None, None) => unreachable!("can't both be missing"),

            (CompareMode::Strict, Some(lhs), Some(rhs)) => {
                writeln!(f, "json atoms at path \"{}\" are not equal:", self.path)?;
                writeln!(f, "    lhs:")?;
                writeln!(f, "{}", json_to_string(lhs).indent(8))?;
                writeln!(f, "    rhs:")?;
                write!(f, "{}", json_to_string(rhs).indent(8))?;
            }
            (CompareMode::Strict, None, Some(_)) => {
                write!(f, "json atom at path \"{}\" is missing from lhs", self.path)?;
            }
            (CompareMode::Strict, Some(_), None) => {
                write!(f, "json atom at path \"{}\" is missing from rhs", self.path)?;
            }
            (CompareMode::Strict, None, None) => unreachable!("can't both be missing"),
        }

        Ok(())
    }
}

impl Difference<'_> {
    /// Returns a string representation of the difference, suitable for display.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

#[derive(Debug, PartialEq)]
pub struct DifferenceBuf {
    path: PathBuf,
    lhs: Option<Value>,
    rhs: Option<Value>,
    config: Config,
}

impl<'a> From<Difference<'a>> for DifferenceBuf {
    fn from(diff: Difference<'a>) -> Self {
        DifferenceBuf {
            path: PathBuf::from(diff.path),
            lhs: diff.lhs.cloned(),
            rhs: diff.rhs.cloned(),
            config: diff.config.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
enum Path<'a> {
    Root,
    Keys(Vec<Key<'a>>),
}

impl<'a> Path<'a> {
    fn append(&self, next: Key<'a>) -> Path<'a> {
        match self {
            Path::Root => Path::Keys(vec![next]),
            Path::Keys(list) => {
                let mut copy = list.clone();
                copy.push(next);
                Path::Keys(copy)
            }
        }
    }
}

impl<'a> fmt::Display for Path<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Path::Root => write!(f, "(root)"),
            Path::Keys(keys) => {
                for key in keys {
                    write!(f, "{}", key)?;
                }
                Ok(())
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
enum PathBuf {
    Root,
    Keys(Vec<KeyBuf>),
}

impl<'a> From<Path<'a>> for PathBuf {
    fn from(path: Path<'a>) -> Self {
        match path {
            Path::Root => PathBuf::Root,
            Path::Keys(keys) => PathBuf::Keys(keys.into_iter().map(KeyBuf::from).collect()),
        }
    }
}
#[derive(Debug, Copy, Clone, PartialEq)]
enum Key<'a> {
    Idx(usize),
    Field(&'a str),
}

#[derive(Debug, Clone, PartialEq)]
enum KeyBuf {
    Idx(usize),
    Field(String),
}

impl<'a> From<Key<'a>> for KeyBuf {
    fn from(key: Key<'a>) -> Self {
        match key {
            Key::Idx(idx) => KeyBuf::Idx(idx),
            Key::Field(field) => KeyBuf::Field(field.to_owned()),
        }
    }
}

impl<'a> fmt::Display for Key<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Key::Idx(idx) => write!(f, "[{}]", idx),
            Key::Field(key) => write!(f, ".{}", key),
        }
    }
}

fn fold_json<'a>(json: &'a Value, folder: &mut DiffFolder<'a, '_>) {
    match json {
        Value::Null => folder.on_null(json),
        Value::Bool(_) => folder.on_bool(json),
        Value::Number(_) => folder.on_number(json),
        Value::String(_) => folder.on_string(json),
        Value::Array(_) => folder.on_array(json),
        Value::Object(_) => folder.on_object(json),
    }
}

#[cfg(test)]
mod test {
    #[allow(unused_imports)]
    use super::*;
    use serde_json::json;

    #[test]
    fn test_diffing_leaf_json() {
        let diffs = diff(
            &json!(null),
            &json!(null),
            Config::new(CompareMode::Inclusive),
        );
        assert_eq!(diffs, vec![]);

        let diffs = diff(
            &json!(false),
            &json!(false),
            Config::new(CompareMode::Inclusive),
        );
        assert_eq!(diffs, vec![]);

        let diffs = diff(
            &json!(true),
            &json!(true),
            Config::new(CompareMode::Inclusive),
        );
        assert_eq!(diffs, vec![]);

        let diffs = diff(
            &json!(false),
            &json!(true),
            Config::new(CompareMode::Inclusive),
        );
        assert_eq!(diffs.len(), 1);

        let diffs = diff(
            &json!(true),
            &json!(false),
            Config::new(CompareMode::Inclusive),
        );
        assert_eq!(diffs.len(), 1);

        let actual = json!(1);
        let expected = json!(1);
        let diffs = diff(&actual, &expected, Config::new(CompareMode::Inclusive));
        assert_eq!(diffs, vec![]);

        let actual = json!(2);
        let expected = json!(1);
        let diffs = diff(&actual, &expected, Config::new(CompareMode::Inclusive));
        assert_eq!(diffs.len(), 1);

        let actual = json!(1);
        let expected = json!(2);
        let diffs = diff(&actual, &expected, Config::new(CompareMode::Inclusive));
        assert_eq!(diffs.len(), 1);

        let actual = json!(1.0);
        let expected = json!(1.0);
        let diffs = diff(&actual, &expected, Config::new(CompareMode::Inclusive));
        assert_eq!(diffs, vec![]);

        let actual = json!(1);
        let expected = json!(1.0);
        let diffs = diff(&actual, &expected, Config::new(CompareMode::Inclusive));
        assert_eq!(diffs.len(), 1);

        let actual = json!(1.0);
        let expected = json!(1);
        let diffs = diff(&actual, &expected, Config::new(CompareMode::Inclusive));
        assert_eq!(diffs.len(), 1);

        let actual = json!(1);
        let expected = json!(1.0);
        let diffs = diff(
            &actual,
            &expected,
            Config::new(CompareMode::Inclusive).numeric_mode(NumericMode::AssumeFloat),
        );
        assert_eq!(diffs, vec![]);

        let actual = json!(1.0);
        let expected = json!(1);
        let diffs = diff(
            &actual,
            &expected,
            Config::new(CompareMode::Inclusive).numeric_mode(NumericMode::AssumeFloat),
        );
        assert_eq!(diffs, vec![]);
    }

    #[test]
    fn test_diffing_array() {
        // empty
        let actual = json!([]);
        let expected = json!([]);
        let diffs = diff(&actual, &expected, Config::new(CompareMode::Inclusive));
        assert_eq!(diffs, vec![]);

        let actual = json!([1]);
        let expected = json!([]);
        let diffs = diff(&actual, &expected, Config::new(CompareMode::Inclusive));
        assert_eq!(diffs.len(), 0);

        let actual = json!([]);
        let expected = json!([1]);
        let diffs = diff(&actual, &expected, Config::new(CompareMode::Inclusive));
        assert_eq!(diffs.len(), 1);

        // eq
        let actual = json!([1]);
        let expected = json!([1]);
        let diffs = diff(&actual, &expected, Config::new(CompareMode::Inclusive));
        assert_eq!(diffs, vec![]);

        // actual longer
        let actual = json!([1, 2]);
        let expected = json!([1]);
        let diffs = diff(&actual, &expected, Config::new(CompareMode::Inclusive));
        assert_eq!(diffs, vec![]);

        // expected longer
        let actual = json!([1]);
        let expected = json!([1, 2]);
        let diffs = diff(&actual, &expected, Config::new(CompareMode::Inclusive));
        assert_eq!(diffs.len(), 1);

        // eq length but different
        let actual = json!([1, 3]);
        let expected = json!([1, 2]);
        let diffs = diff(&actual, &expected, Config::new(CompareMode::Inclusive));
        assert_eq!(diffs.len(), 1);

        // different types
        let actual = json!(1);
        let expected = json!([1]);
        let diffs = diff(&actual, &expected, Config::new(CompareMode::Inclusive));
        assert_eq!(diffs.len(), 1);

        let actual = json!([1]);
        let expected = json!(1);
        let diffs = diff(&actual, &expected, Config::new(CompareMode::Inclusive));
        assert_eq!(diffs.len(), 1);
    }

    #[test]
    fn test_array_strict() {
        let actual = json!([]);
        let expected = json!([]);
        let diffs = diff(&actual, &expected, Config::new(CompareMode::Strict));
        assert_eq!(diffs.len(), 0);

        let actual = json!([1, 2]);
        let expected = json!([1, 2]);
        let diffs = diff(&actual, &expected, Config::new(CompareMode::Strict));
        assert_eq!(diffs.len(), 0);

        let actual = json!([1]);
        let expected = json!([1, 2]);
        let diffs = diff(&actual, &expected, Config::new(CompareMode::Strict));
        assert_eq!(diffs.len(), 1);

        let actual = json!([1, 2]);
        let expected = json!([1]);
        let diffs = diff(&actual, &expected, Config::new(CompareMode::Strict));
        assert_eq!(diffs.len(), 1);
    }

    #[test]
    fn test_object() {
        let actual = json!({});
        let expected = json!({});
        let diffs = diff(&actual, &expected, Config::new(CompareMode::Inclusive));
        assert_eq!(diffs, vec![]);

        let actual = json!({ "a": 1 });
        let expected = json!({ "a": 1 });
        let diffs = diff(&actual, &expected, Config::new(CompareMode::Inclusive));
        assert_eq!(diffs, vec![]);

        let actual = json!({ "a": 1, "b": 123 });
        let expected = json!({ "a": 1 });
        let diffs = diff(&actual, &expected, Config::new(CompareMode::Inclusive));
        assert_eq!(diffs, vec![]);

        let actual = json!({ "a": 1 });
        let expected = json!({ "b": 1 });
        let diffs = diff(&actual, &expected, Config::new(CompareMode::Inclusive));
        assert_eq!(diffs.len(), 1);

        let actual = json!({ "a": 1 });
        let expected = json!({ "a": 2 });
        let diffs = diff(&actual, &expected, Config::new(CompareMode::Inclusive));
        assert_eq!(diffs.len(), 1);

        let actual = json!({ "a": { "b": true } });
        let expected = json!({ "a": {} });
        let diffs = diff(&actual, &expected, Config::new(CompareMode::Inclusive));
        assert_eq!(diffs, vec![]);
    }

    #[test]
    fn test_object_strict() {
        let lhs = json!({});
        let rhs = json!({ "a": 1 });
        let diffs = diff(&lhs, &rhs, Config::new(CompareMode::Strict));
        assert_eq!(diffs.len(), 1);

        let lhs = json!({ "a": 1 });
        let rhs = json!({});
        let diffs = diff(&lhs, &rhs, Config::new(CompareMode::Strict));
        assert_eq!(diffs.len(), 1);

        let json = json!({ "a": 1 });
        let diffs = diff(&json, &json, Config::new(CompareMode::Strict));
        assert_eq!(diffs.len(), 0);
    }

    #[test]
    fn test_floats_epsilon() {
        let actual = json!(1.15);
        let expected = json!(1);
        let diffs = diff(
            &actual,
            &expected,
            Config::new(CompareMode::Inclusive).numeric_mode(NumericMode::AssumeFloatEpsilon(0.2)),
        );
        assert_eq!(diffs.len(), 0);

        let actual = json!(1.25);
        let expected = json!(1);
        let diffs = diff(
            &actual,
            &expected,
            Config::new(CompareMode::Inclusive).numeric_mode(NumericMode::AssumeFloatEpsilon(0.2)),
        );
        assert_eq!(diffs.len(), 1);
    }
}
