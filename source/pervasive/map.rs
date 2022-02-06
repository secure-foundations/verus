#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use crate::pervasive::*;
#[allow(unused_imports)]
use crate::pervasive::set::*;

/// map type for specifications
#[verifier(external_body)]
pub struct Map<#[verifier(maybe_negative)] K, #[verifier(strictly_positive)] V> {
    dummy: std::marker::PhantomData<(K, V)>,
}

impl<K, V> Map<K, V> {
    #[spec]
    #[verifier(external_body)]
    pub fn empty() -> Map<K, V> {
        unimplemented!()
    }

    #[spec]
    pub fn total<F: Fn(K) -> V>(f: F) -> Map<K, V> {
        Set::full().mk_map(f)
    }

    #[spec]
    #[verifier(external_body)]
    pub fn dom(self) -> Set<K> {
        unimplemented!()
    }

    #[spec]
    #[verifier(external_body)]
    pub fn index(self, key: K) -> V {
        unimplemented!()
    }

    #[spec]
    #[verifier(external_body)]
    pub fn insert(self, key: K, value: V) -> Map<K, V> {
        unimplemented!()
    }

    #[spec]
    pub fn ext_equal(self, m2: Map<K, V>) -> bool {
        self.dom().ext_equal(m2.dom()) &&
        forall(|k: K| self.dom().contains(k) >>= equal(self.index(k), m2.index(k)))
    }
}

// Trusted axioms

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_map_empty<K, V>() {
    ensures(equal(Map::<K, V>::empty().dom(), Set::empty()));
}

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_map_insert_domain<K, V>(m: Map<K, V>, key: K, value: V) {
    ensures(equal(#[trigger] m.insert(key, value).dom(), m.dom().insert(key)));
}

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_map_insert_same<K, V>(m: Map<K, V>, key: K, value: V) {
    ensures(equal(#[trigger] m.insert(key, value).index(key), value));
}

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_map_insert_different<K, V>(m: Map<K, V>, key1: K, key2: K, value: V) {
    requires([
        m.dom().contains(key1),
        !equal(key1, key2),
    ]);
    ensures(equal(m.insert(key2, value).index(key1), m.index(key1)));
}

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_map_ext_equal<K, V>(m1: Map<K, V>, m2: Map<K, V>) {
    ensures(m1.ext_equal(m2) == equal(m1, m2));
}

// Macros

#[macro_export]
macro_rules! map_insert_rec {
    [$val:expr;] => {
        $val
    };
    [$val:expr;$key:expr => $value:expr] => {
        map_insert_rec![$val.insert($key, $value);]
    };
    [$val:expr;$key:expr => $value:expr,$($tail:tt)*] => {
        map_insert_rec![$val.insert($key, $value);$($tail)*]
    }
}

#[macro_export]
macro_rules! map {
    [$($tail:tt)*] => {
        map_insert_rec![$crate::pervasive::map::Map::empty();$($tail)*]
    }
} 
