#[allow(unused_imports)]
use builtin::*;
mod pervasive;
use pervasive::*;
use pervasive::map::*;

use state_machines_macros::tokenized_state_machine;

tokenized_state_machine!(
    X {
        fields {
            #[sharding(map)]
            pub bool_map: Map<int, bool>,

        }

        init!{
            initialize(cond: bool) {
                init bool_map = Map::empty().insert(5, true);
            }
        }

        transition!{
            add(n: int) {
                remove bool_map -= [n => true];
                add bool_map += [n => true];
            }
        }

        transition!{
            add_have(n: int) {
                remove bool_map -= [n => false];
                have bool_map >= [19 => false];
                add bool_map += [n => true];
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: X, cond: bool) { }
   
        #[inductive(add)]
        fn add_inductive(self: X, post: X, n: int) { }
   
        #[inductive(add_have)]
        fn add_have_inductive(self: X, post: X, n: int) { }
    }
);

tokenized_state_machine!(
    Fancy {
        fields {
            #[sharding(variable)]
            pub m: int,

            #[sharding(map)]
            pub map: Map<int, bool>,

            #[sharding(storage_map)]
            pub storage_map: Map<int, bool>,
        }

        #[invariant]
        fn inv1(self) -> bool {
            forall(|i: int|
              self.storage_map.dom().contains(i) >>= (0 <= i && i < self.m))
        }

        #[invariant]
        fn inv2(self) -> bool {
            forall(|i: int|
              (0 <= i && i < self.m) >>= self.storage_map.dom().contains(i))
        }

        #[invariant]
        fn inv3(self) -> bool {
            self.m >= 0 &&
            equal(self.storage_map, self.map)
        }

        #[init]
        fn initialize(cond: bool) {
            init(m, 0);
            init(storage_map, Map::empty());
            init(map, Map::empty());
        }

        #[transition]
        fn do_deposit(self, b: bool) {
            update(m, self.m + 1);
            add_kv(map, self.m, b);
            deposit_kv(storage_map, self.m, b);
        }

        #[transition]
        fn do_withdraw(self, b: bool) {
            require(self.m >= 1);
            update(m, self.m - 1);
            remove_kv(map, self.m, b);
            withdraw_kv(storage_map, self.m, b);
        }

        #[readonly]
        fn do_guard(self, i: int, b: bool) {
            have_kv(map, i, b);
            guard_kv(storage_map, i, b);
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Fancy, cond: bool) { }
   
        #[inductive(do_deposit)]
        fn do_deposit_inductive(self: Fancy, post: Fancy, b: bool) {
            /*
            assert_forall_by(|i: int| {
              requires(post.storage_map.dom().contains(i));
              ensures(0 <= i && i < post.m);
              if self.storage_map.dom().contains(i) {
                  assert(0 <= i && i < post.m);
              } else {
                  assert(i == self.m);
                  assert(0 <= i && i < post.m);
              }
            });
            */
        }

        #[inductive(do_withdraw)]
        fn do_withdraw_inductive(self: Fancy, post: Fancy, b: bool) { }
    }
);

fn main() { }
