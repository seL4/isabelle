(* Author: Tobias Nipkow

Instantiation of the generic linear arithmetic package for int.
*)

signature INT_ARITH =
sig
  val setup: Context.generic -> Context.generic
  val global_setup: theory -> theory
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

fun check (Const (@{const_name HOL.one}, @{typ int})) = false
  | check (Const (@{const_name HOL.one}, _)) = true
  | check (Const (s, _)) = member (op =) [@{const_name "op ="},
      @{const_name HOL.times}, @{const_name HOL.uminus},
      @{const_name HOL.minus}, @{const_name HOL.plus},
      @{const_name HOL.zero},
      @{const_name HOL.less}, @{const_name HOL.less_eq}] s
  | check (a $ b) = check a andalso check b
  | check _ = false;

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

val fast_int_arith_simproc =
  Simplifier.simproc @{theory} "fast_int_arith"
     ["(m::'a::{ordered_idom,number_ring}) < n",
      "(m::'a::{ordered_idom,number_ring}) <= n",
      "(m::'a::{ordered_idom,number_ring}) = n"] (K Lin_Arith.simproc);

val global_setup = Simplifier.map_simpset
  (fn simpset => simpset addsimprocs [fast_int_arith_simproc]);


fun number_of thy T n =
  if not (Sign.of_sort thy (T, @{sort number}))
  then raise CTERM ("number_of", [])
  else Numeral.mk_cnumber (Thm.ctyp_of thy T) n

val setup =
  Lin_Arith.add_inj_thms [@{thm zle_int} RS iffD2, @{thm int_int_eq} RS iffD2]
  #> Lin_Arith.add_lessD @{thm zless_imp_add1_zle}
  #> Lin_Arith.add_simps (@{thms simp_thms} @ @{thms arith_simps} @ @{thms rel_simps}
      @ @{thms arith_special} @ @{thms int_arith_rules})
  #> Lin_Arith.add_simprocs (Numeral_Simprocs.assoc_fold_simproc :: zero_one_idom_simproc
      :: Numeral_Simprocs.combine_numerals
      :: Numeral_Simprocs.cancel_numerals)
  #> Lin_Arith.set_number_of number_of
  #> Lin_Arith.add_inj_const (@{const_name of_nat}, HOLogic.natT --> HOLogic.intT)
  #> Lin_Arith.add_discrete_type @{type_name Int.int}

end;
