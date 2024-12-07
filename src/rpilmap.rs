use rustc_data_structures::fx::FxHashMap;

use crate::serialmap::UnaryRecursive;

use super::rpil::LowRpilOp;
use super::serialmap::{SerialMap, SerialMapForUnaryRecursive};

#[derive(Clone)]
pub struct LowRpilMap(FxHashMap<LowRpilOp, (LowRpilOp, usize)>);

impl LowRpilMap {
    pub fn new() -> Self {
        LowRpilMap(FxHashMap::default())
    }
}

fn assert_no_self_reference(key: &LowRpilOp, val: &LowRpilOp) {
    assert_ne!(key, val, "self-reference is unsupported");
    if let Some(key_inner) = key.get_inner() {
        assert_no_self_reference(key_inner, val);
    }
}

impl SerialMap<LowRpilOp> for LowRpilMap {
    fn iter<'a>(&'a self) -> impl Iterator<Item = (&'a LowRpilOp, &'a LowRpilOp, usize)>
    where
        LowRpilOp: 'a,
    {
        self.0
            .iter()
            .map(move |(key, (val, serial))| (key, val, *serial))
    }

    fn into_iter(self) -> impl Iterator<Item = (LowRpilOp, LowRpilOp, usize)> {
        self.0
            .into_iter()
            .map(|(key, (val, serial))| (key, val, serial))
    }

    fn insert(&mut self, key: LowRpilOp, val: LowRpilOp, serial: usize) {
        assert_ne!(key, val, "circular assignment is currently unsupported");
        assert_no_self_reference(&key, &val);
        self.0.insert(key, (val, serial));
    }

    fn remove(&mut self, key: &LowRpilOp) {
        self.0.remove(key);
    }

    fn get(&self, key: &LowRpilOp) -> Option<&LowRpilOp> {
        self.0.get(key).map(|(val, _serial)| val)
    }
}

impl SerialMapForUnaryRecursive<LowRpilOp> for LowRpilMap {}

impl LowRpilMap {
    pub fn remove_over_depth_mapping(&mut self, max_depth: usize) {
        let mut to_remove = vec![];
        for (key, val, _serial) in self.iter() {
            if key.depth() >= max_depth || val.depth() >= max_depth {
                to_remove.push(key.clone());
            }
        }
        for key in to_remove {
            self.remove(&key);
        }
    }
}
