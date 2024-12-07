use rustc_data_structures::fx::FxHashMap;

use std::hash::Hash;

pub trait UnaryRecursive {
    fn get_inner(&self) -> Option<&Self>;

    fn replace_inner(&self, op: Self) -> Self;
}

pub trait SerialMap<T>
where
    T: PartialEq + Eq + Hash,
{
    fn iter<'a>(&'a self) -> impl Iterator<Item = (&'a T, &'a T, usize)>
    where
        T: 'a;

    fn into_iter(self) -> impl Iterator<Item = (T, T, usize)>;

    fn insert(&mut self, key: T, val: T, serial: usize);

    fn remove(&mut self, key: &T);

    fn get(&self, key: &T) -> Option<&T>;
}

fn structural_aliases<T: UnaryRecursive + Clone + PartialEq + Eq + Hash>(
    reverse_mapping: &FxHashMap<T, Vec<(T, usize)>>,
    op: &T,
) -> Vec<(T, usize)> {
    let mut results = vec![];
    if let Some(reverse_mapped_ops) = reverse_mapping.get(op) {
        results.extend(reverse_mapped_ops.iter().cloned());
    }
    if let Some(inner_op) = op.get_inner() {
        results.extend(
            structural_aliases(reverse_mapping, inner_op)
                .into_iter()
                .map(|(reverse_mapped_inner_op, serial)| {
                    let reverse_mapped_op = op.replace_inner(reverse_mapped_inner_op);
                    (reverse_mapped_op, serial)
                }),
        );
    }
    results
}

pub trait SerialMapForUnaryRecursive<T>
where
    Self: SerialMap<T> + Clone,
    T: UnaryRecursive + Clone + PartialEq + Eq + Hash,
{
    fn expand_to_transitive_closure(&mut self) {
        let mut reverse_mapping = FxHashMap::<T, Vec<(T, usize)>>::default();
        for (key, val, serial) in self.iter() {
            if let Some(entries) = reverse_mapping.get_mut(val) {
                entries.push((key.clone(), serial))
            } else {
                reverse_mapping.insert(val.clone(), vec![(key.clone(), serial)]);
            }
        }
        let mut to_insert = vec![];
        for (key, val, serial) in self.iter() {
            for (alias_key, alias_serial) in structural_aliases(&reverse_mapping, key) {
                if alias_serial < serial {
                    continue;
                }
                to_insert.push((alias_key, val.clone(), alias_serial));
            }
        }
        for (key, val, serial) in to_insert {
            self.insert(key, val, serial);
        }
    }
}
