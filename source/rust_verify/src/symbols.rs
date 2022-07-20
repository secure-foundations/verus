use rustc_span::symbol::Symbol;
use lazy_static::lazy_static;

lazy_static! {

static ref BUILTIN_ADMIT: Symbol = Symbol::intern("builtin::admit");
static ref BUILTIN_NO_METHOD_BODY: Symbol = Symbol::intern("builtin::no_method_body");
static ref BUILTIN_REQUIRES: Symbol = Symbol::intern("builtin::requires");
static ref BUILTIN_RECOMMENDS: Symbol = Symbol::intern("builtin::recommends");
static ref BUILTIN_ENSURES: Symbol = Symbol::intern("builtin::ensures");
static ref BUILTIN_INVARIANT: Symbol = Symbol::intern("builtin::invariant");
static ref BUILTIN_DECREASES: Symbol = Symbol::intern("builtin::decreases");
static ref BUILTIN_DECREASES_WHEN: Symbol = Symbol::intern("builtin::decreases_when");
static ref BUILTIN_DECREASES_BY: Symbol = Symbol::intern("builtin::decreases_by");
static ref BUILTIN_RECOMMENDS_BY: Symbol = Symbol::intern("builtin::recommends_by");
static ref BUILTIN_OPENS_INVARIANTS_NONE: Symbol = Symbol::intern("builtin::opens_invariants_none");
static ref BUILTIN_OPENS_INVARIANTS_ANY: Symbol = Symbol::intern("builtin::opens_invariants_any");
static ref BUILTIN_OPENS_INVARIANTS: Symbol = Symbol::intern("builtin::opens_invariants");
static ref BUILTIN_OPENS_INVARIANTS_EXCEPT: Symbol = Symbol::intern("builtin::opens_invariants_except");
static ref BUILTIN_FORALL: Symbol = Symbol::intern("builtin::forall");
static ref BUILTIN_EXISTS: Symbol = Symbol::intern("builtin::exists");
static ref BUILTIN_FORALL_ARITH: Symbol = Symbol::intern("builtin::forall_arith");
static ref BUILTIN_CHOOSE: Symbol = Symbol::intern("builtin::choose");
static ref BUILTIN_CHOOSE_TUPLE: Symbol = Symbol::intern("builtin::choose_tuple");
static ref BUILTIN_WITH_TRIGGERS: Symbol = Symbol::intern("builtin::with_triggers");
static ref BUILTIN_EQUAL: Symbol = Symbol::intern("builtin::equal");
static ref BUILTIN_CHAINED_VALUE: Symbol = Symbol::intern("builtin::spec_chained_value");
static ref BUILTIN_CHAINED_LE: Symbol = Symbol::intern("builtin::spec_chained_le");
static ref BUILTIN_CHAINED_LT: Symbol = Symbol::intern("builtin::spec_chained_lt");
static ref BUILTIN_CHAINED_GE: Symbol = Symbol::intern("builtin::spec_chained_ge");
static ref BUILTIN_CHAINED_GT: Symbol = Symbol::intern("builtin::spec_chained_gt");
static ref BUILTIN_CHAINED_CMP: Symbol = Symbol::intern("builtin::spec_chained_cmp");
static ref BUILTIN_HIDE: Symbol = Symbol::intern("builtin::hide");
static ref BUILTIN_EXTRA_DEPENDENCY: Symbol = Symbol::intern("builtin::extra_dependency");
static ref BUILTIN_REVEAL: Symbol = Symbol::intern("builtin::reveal");
static ref BUILTIN_REVEAL_WITH_FUEL: Symbol = Symbol::intern("builtin::reveal_with_fuel");
static ref BUILTIN_IMPLY: Symbol = Symbol::intern("builtin::imply");
static ref BUILTIN_ASSERT_BY: Symbol = Symbol::intern("builtin::assert_by");
static ref BUILTIN_ASSERT_NONLINEAR_BY: Symbol = Symbol::intern("builtin::assert_nonlinear_by");
static ref BUILTIN_ASSERT_FORALL_BY: Symbol = Symbol::intern("builtin::assert_forall_by");
static ref BUILTIN_ASSERT_BIT_VECTOR: Symbol = Symbol::intern("builtin::assert_bit_vector");
static ref BUILTIN_OLD: Symbol = Symbol::intern("builtin::old");
}


