(* Author: Tobias Nipkow

Instantiation of the generic linear arithmetic package for int.
*)

signature INT_ARITH =
sig
  val fast_int_arith_simproc: simproc
  val setup: Context.generic -> Context.generic
end

structure Int_Arith : INT_ARITH =
struct

(* Update parameters of arithmetic prover *)

(* reduce contradictory =/</<= to False *)

(* Evaluation of terms of the form "m R n" where R is one of "=", "<=" or "<",
   and m and n are ground terms over rings (roughly speaking).
   That is, m and n consist only of 1s combined with "+", "-" and "*".
*)

val zeroth = (symmetric o mk_meta_eq) @{thm of_int_0};

val lhss0 = [@{cpat "0::?'a::ring"}];

fun proc0 phi ss ct =
  let val T = ctyp_of_term ct
  in if typ_of T = @{typ int} then NONE else
     SOME (instantiate' [SOME T] [] zeroth)
  end;

val zero_to_of_int_zero_simproc =
  make_simproc {lhss = lhss0, name = "zero_to_of_int_zero_simproc",
  proc = proc0, identifier = []};

val oneth = (symmetric o mk_meta_eq) @{thm of_int_1};

val lhss1 = [@{cpat "1::?'a::ring_1"}];

fun proc1 phi ss ct =
  let val T = ctyp_of_term ct
  in if typ_of T = @{typ int} then NONE else
     SOME (instantiate' [SOME T] [] oneth)
  end;

val one_to_of_int_one_simproc =
  make_simproc {lhss = lhss1, name = "one_to_of_int_one_simproc",
  proc = proc1, identifier = []};

val allowed_consts =
  [@{const_name "op ="}, @{const_name "HOL.times"}, @{const_name "HOL.uminus"},
   @{const_name "HOL.minus"}, @{const_name "HOL.plus"},
   @{const_name "HOL.zero"}, @{const_name "HOL.one"}, @{const_name "HOL.less"},
   @{const_name "HOL.less_eq"}];

fun check t = case t of
   Const(s,t) => if s = @{const_name "HOL.one"} then not (t = @{typ int})
                else s mem_string allowed_consts
 | a$b => check a andalso check b
 | _ => false;

val conv =
  Simplifier.rewrite
   (HOL_basic_ss addsimps
     ((map (fn th => th RS sym) [@{thm of_int_add}, @{thm of_int_mult},
             @{thm of_int_diff},  @{thm of_int_minus}])@
      [@{thm of_int_less_iff}, @{thm of_int_le_iff}, @{thm of_int_eq_iff}])
     addsimprocs [zero_to_of_int_zero_simproc,one_to_of_int_one_simproc]);

fun sproc phi ss ct = if check (term_of ct) then SOME (conv ct) else NONE

val lhss' =
  [@{cpat "(?x::?'a::ring_char_0) = (?y::?'a)"},
   @{cpat "(?x::?'a::ordered_idom) < (?y::?'a)"},
   @{cpat "(?x::?'a::ordered_idom) <= (?y::?'a)"}]

val zero_one_idom_simproc =
  make_simproc {lhss = lhss' , name = "zero_one_idom_simproc",
  proc = sproc, identifier = []}

val add_rules =
    simp_thms @ @{thms arith_simps} @ @{thms rel_simps} @ @{thms arith_special} @
    @{thms int_arith_rules}

val nat_inj_thms = [@{thm zle_int} RS iffD2, @{thm int_int_eq} RS iffD2]

val numeral_base_simprocs = Numeral_Simprocs.assoc_fold_simproc :: zero_one_idom_simproc
  :: Numeral_Simprocs.combine_numerals
  :: Numeral_Simprocs.cancel_numerals;

val setup =
  Lin_Arith.map_data (fn {add_mono_thms, mult_mono_thms, inj_thms, lessD, neqE, simpset} =>
   {add_mono_thms = add_mono_thms,
    mult_mono_thms = @{thm mult_strict_left_mono} :: @{thm mult_left_mono} :: mult_mono_thms,
    inj_thms = nat_inj_thms @ inj_thms,
    lessD = lessD @ [@{thm zless_imp_add1_zle}],
    neqE = neqE,
    simpset = simpset addsimps add_rules
                      addsimprocs numeral_base_simprocs
                      addcongs [if_weak_cong]}) #>
  arith_inj_const (@{const_name of_nat}, HOLogic.natT --> HOLogic.intT) #>
  arith_discrete @{type_name Int.int}

val fast_int_arith_simproc =
  Simplifier.simproc (the_context ())
  "fast_int_arith" 
     ["(m::'a::{ordered_idom,number_ring}) < n",
      "(m::'a::{ordered_idom,number_ring}) <= n",
      "(m::'a::{ordered_idom,number_ring}) = n"] (K Lin_Arith.lin_arith_simproc);

end;

Addsimprocs [Int_Arith.fast_int_arith_simproc];
