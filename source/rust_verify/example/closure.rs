// We can use a blanket impl (e.g., in pervasive or builtin)
// To give every closure a 'requires' and 'ensures' function

trait VerifiedFn<Args, Output> {
    fn requires(args: Args) -> bool;
    fn ensures(args: Args, output: Output) -> bool;
}

impl<Args, Output, F: FnOnce(Args) -> Output> VerifiedFn<Args, Output> for F { 
    fn requires(args: Args) -> bool {
        unimplemented!();
    }

    fn ensures(args: Args, output: Output) -> bool {
        unimplemented!();
    }
}

//// Calling closure functions

// If f implements Fn (and thus implements VerifiedFn), then a call `f(x)` is
// for verification purposes equivalent to calling `call(f, x)`, where:

#[exec]
fn call<Args, Output>(f: impl VerifiedFn(Args, Output), x: Args) -> (ret: Output)
    requires f.requires(x),
    ensures f.ensures(x, ret),

// Example use:

#[exec]
fn call_closure(f: impl Fn(u64) -> u64)
requires
    f.requires(0),
    forall |x| f.ensures(0, x) ==> x == 1 || x == 2,
{
    let ret = f(0); // allowed since f.requires(0)

    assert(ret == 1 || ret == 2); // follows from post-condition of f
}

// note: 'requires' and 'ensures' might actually be a little confusing as names
// when they are used like this?

// We can also have a shorthand notation that makes it easier to talk about these conditions:
// e.g., this would be equivalent to the above

#[exec]
fn call_closure(f: impl Fn(u64) -> u64)
requires
    func_spec!(f(x) -> ret
        requires x == 0,
        ensures ret == 1 || ret == 2
    );

// One motivation for closures is to simplify the specification for thread-spawning.
// Currently it uses a trait with a lot of parts, but with closures we could reduce
// it to the following:

impl<V> JoinHandle<V> {
    spec fn predicate(v: V) -> bool;

    exec fn join() -> (v: V)
        ensures predicate(v)
}

exec fn spawn<V>(f: impl FnOnce(()) -> V) -> (handle: JoinHandle<V>)
    ensures
        forall |v| handle.predicate(v) ==> f.ensures((), v)

// Note that if any arguments need to be passed into the spawned thread, they can be done
// via the closure. Thus `f` itself can just take a unit argument.

//// Declaring closures

// closures will be declared with requires and ensures clauses:

fn main() {
    call_closure(|x|
        requires x == 0
        ensures ret == 1 || ret == 2
        {
            return 1;
        }
    );
}

// note: something to determine is where the name of returned argument should come from.
// I don't think the closure syntax allows a return type?

// Rust has 3 function types: FnOnce, FnMut, Fn
// _every_ closure type implements FnOnce. Some of those will also implement FnMut
// and some of those will implement Fn
//
// That is, the user who holds a Fn can make stronger assumptions and do more things,
// but there are the most restrictions when declaring a Fn.
//
// As usual, we can mostly rely on Rust's borrow-checking here.
// However, this has some implications for verification at the declaration site.
// In particular, what context gets inherited?

// Fn is the easiest. If a function is Fn, then that means it only takes shared-borrows
// (no &mut borrows) to anything in the surrounding context.
// That means we can just inherit all known verification facts from the context.

// (Note that this isn't _really_ about being Fn.
// Being Fn just means the function can be called while shared-borrowed, which isn't
// really the point here.
//
// It's better to say, the same conditions that let you declare a closure as Fn -
// that is, the function only takes shared borrows to captured variables - 
// also let you get this ability to capture the context.)

fn test_fn() {
    let x = 5;
    let mut y = 6;

    let t = || {
        ensures |ret| ret == 5,

        // In spec code, these variables refer to their values when the closure is declared.
        // These facts are inherited from the context.
        assert x == 5;
        assert y == 6;

        // Exec value (actual value) agrees with the spec value, guaranteed by the
        // borrow-checker.
        return x;
    };  

    y = 7; // borrow-checker says this is OK because the closure 't' never access 'y'
           // in borrow-checked code

    let ret = t();
    assert(ret == 5);
}

// If a function takes mutable borrows to surrounding values, then it can
// mutate those values.
// In this case, need some kind of invariant mechanism:

fn test_fn_mut() {
    let mut x = 4;

    let mut t = || {
        invariant x % 2 == 0,

        // CANNOT assume that x == 4 here

        x += 2;
    };  

    t();
    t();
    // If we tried to say `x = 5` here to violate the invariant, the borrow-checker
    // would complain.
    t();

    // should be able to recover this from the invariant.
    // (Q: how do know that the borrow on `x` has expired,
    // so we can talk about it in spec code? The same question has come up for normal
    // mutable borrows. For now, though, we could get around this by only letting us
    // use closures as arguments to functions.)
    assert x % 2 == 0;
}

// If a function is FnOnce (or more precisely, if we don't allow the function to be FnMut or Fn)
// Then we can actually recover the ability to import the context:

fn test_fn_once() {
    let mut x = 4;

    let mut t = || {
        // Although the closure mutates x, this function can only be called once.
        // So we can still assume that `x` looks the same way it does at the declaration
        // of the closure.
        assert(x == 4);

        x += 2;

        // note: there needs to be some way for the user to "opt in" to such behavior.
        // In doing so, verus will create an additional restriction that the function
        // cannot be marked FnMut.
    };

    t();
    // t();     // would be disallowed by borrow-checker
}

// In summary, the rules are:
//
//    1. We can always take in the ambient proof for variables that are either not accessed,
//       or which are only accessed read-only.
//
//    2. We can take in the ambient proof context for variables that the closure mutates,
//       but if we do, then we must not allow the closure to be FnMut
//       (i.e., the strongest trait we can give it is FnOnce).
//
//    3. If we don't do (2), we can still reason about mutated variables via invariants.

// Questions:
// 
//  1. How to specify the name of the return value for a closure, to be used in
//     an 'ensures' clauses?
//
//  2. We can use this to implement things like `map` on iters, although it might
//     be annoying because of having to add requires/ensures. Can this be made easier?
//
//  3. For functions that are FnMut, you might want additional restrictions, like
//     "can only be called 3 times" or something. That is, there may be some needed
//     for the caller of the function to reason about its internal state.
//     In there a need to add explicit functionality to help with this?
//     (I think the use-case is probably served with tracked ghost state, though.)
//
//  4. What knobs do we provide for the user to have control over what context they get?
//     (Similar question may apply to 'while' loops.)
