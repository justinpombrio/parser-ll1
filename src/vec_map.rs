use std::iter::IntoIterator;

/// Map from `usize` to `T`, where you know a-priori that the
/// `usize` keys will be small, densely packed numbers.
#[derive(Debug, Clone)]
pub struct VecMap<T>(Vec<Option<T>>);

impl<T> VecMap<T> {
    pub fn new() -> VecMap<T> {
        VecMap(Vec::new())
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        match self.0.get(index) {
            None | Some(None) => None,
            Some(Some(value)) => Some(value),
        }
    }

    pub fn set(&mut self, index: usize, value: T) {
        if index >= self.0.len() {
            self.0.resize_with(index + 1, || None);
        }
        self.0[index] = Some(value);
    }

    pub fn extend(&mut self, iter: impl IntoIterator<Item = (usize, T)>) {
        for (i, v) in iter {
            self.set(i, v);
        }
    }

    pub fn clear(&mut self) {
        for i in 0..self.0.len() {
            self.0[i] = None;
        }
    }

    pub fn iter(&self) -> VecMapIter<T> {
        VecMapIter {
            index: 0,
            vec: &self.0,
        }
    }

    pub fn map<U: Clone>(&self, func: impl Fn(T) -> U) -> VecMap<U>
    where
        T: Clone,
    {
        let mut result = VecMap(vec![None; self.0.len()]);
        for (i, val) in self.iter() {
            result.set(i, func(val.clone()));
        }
        result
    }
}

pub struct VecMapIter<'a, T> {
    index: usize,
    vec: &'a Vec<Option<T>>,
}

impl<'a, T> Iterator for VecMapIter<'a, T> {
    type Item = (usize, &'a T);

    fn next(&mut self) -> Option<(usize, &'a T)> {
        while self.index < self.vec.len() {
            let index = self.index;
            self.index += 1;
            match &self.vec[index] {
                None => (),
                Some(val) => return Some((index, val)),
            }
        }
        None
    }
}

impl<'a, T> IntoIterator for &'a VecMap<T> {
    type Item = (usize, &'a T);
    type IntoIter = VecMapIter<'a, T>;

    fn into_iter(self) -> VecMapIter<'a, T> {
        self.iter()
    }
}

pub struct VecMapIntoIter<T> {
    index: usize,
    vec: Vec<Option<T>>,
}

impl<T> Iterator for VecMapIntoIter<T> {
    type Item = (usize, T);

    fn next(&mut self) -> Option<(usize, T)> {
        while self.index < self.vec.len() {
            let index = self.index;
            self.index += 1;
            match self.vec[index].take() {
                None => (),
                Some(val) => return Some((index, val)),
            }
        }
        None
    }
}

impl<T> IntoIterator for VecMap<T> {
    type Item = (usize, T);
    type IntoIter = VecMapIntoIter<T>;

    fn into_iter(self) -> VecMapIntoIter<T> {
        VecMapIntoIter {
            index: 0,
            vec: self.0,
        }
    }
}

#[test]
fn test_vec_map() {
    let mut map = VecMap::<char>::new();
    assert_eq!(map.get(0), None);
    assert_eq!(map.get(1), None);
    assert_eq!(map.iter().collect::<Vec<_>>(), Vec::new());

    map.set(1, '1');
    assert_eq!(map.get(0), None);
    assert_eq!(map.get(1), Some(&'1'));
    assert_eq!(map.get(2), None);
    assert_eq!(map.iter().collect::<Vec<_>>(), vec![(1, &'1')]);

    map.set(3, '3');
    map.set(4, '3');
    assert_eq!(map.get(0), None);
    assert_eq!(map.get(1), Some(&'1'));
    assert_eq!(map.get(2), None);
    assert_eq!(map.get(3), Some(&'3'));
    assert_eq!(map.get(4), Some(&'3'));
    assert_eq!(map.get(5), None);
    assert_eq!(
        map.iter().collect::<Vec<_>>(),
        vec![(1, &'1'), (3, &'3'), (4, &'3')]
    );

    map.set(4, 'x');
    map.set(1, 'x');
    map.set(4, 'y');
    assert_eq!(map.get(0), None);
    assert_eq!(map.get(1), Some(&'x'));
    assert_eq!(map.get(2), None);
    assert_eq!(map.get(3), Some(&'3'));
    assert_eq!(map.get(4), Some(&'y'));
    assert_eq!(map.get(5), None);
    assert_eq!(
        map.iter().collect::<Vec<_>>(),
        vec![(1, &'x'), (3, &'3'), (4, &'y')]
    );
    assert_eq!(
        map.into_iter().collect::<Vec<_>>(),
        vec![(1, 'x'), (3, '3'), (4, 'y')]
    );

    let mut map1 = VecMap::<char>::new();
    map1.set(1, '1');
    map1.set(2, '2');
    let mut map2 = VecMap::<char>::new();
    map2.set(2, '*');
    map2.set(3, '3');

    map1.extend(map2);
    assert_eq!(
        map1.into_iter().collect::<Vec<_>>(),
        vec![(1, '1'), (2, '*'), (3, '3')]
    );
}
