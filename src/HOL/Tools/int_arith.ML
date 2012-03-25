(* Author: Tobias Nipkow

Instantiation of the generic linear arithmetic package for int.
*)

signature INT_ARITH =
sig
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

val zeroth = (Thm.symmetric o mk_meta_eq) @{thm of_int_0};

val lhss0 = [@{cpat "0::?'a::ring"}];

fun proc0 phi ss ct =
  let val T = ctyp_of_term ct
  in if typ_of T = @{typ int} then NONE else
     SOME (instantiate' [SOME T] [] zeroth)
  end;

val zero_to_of_int_zero_simproc =
  make_simproc {lhss = lhss0, name = "zero_to_of_int_zero_simproc",
  proc = proc0, identifier = []};

val oneth = (Thm.symmetric o mk_meta_eq) @{thm of_int_1};

val lhss1 = [@{cpat "1::?'a::ring_1"}];

fun proc1 phi ss ct =
  let val T = ctyp_of_term ct
  in if typ_of T = @{typ int} then NONE else
     SOME (instantiate' [SOME T] [] oneth)
  end;

val one_to_of_int_one_simproc =
  make_simproc {lhss = lhss1, name = "one_to_of_int_one_simproc",
  proc = proc1, identifier = []};

fun check (Const (@{const_name Groups.one}, @{typ int})) = false
  | check (Const (@{const_name Groups.one}, _)) = true
  | check (Const (s, _)) = member (op =) [@{const_name HOL.eq},
      @{const_name Groups.times}, @{const_name Groups.uminus},
      @{const_name Groups.minus}, @{const_name Groups.plus},
      @{const_name Groups.zero},
      @{const_name Orderings.less}, @{const_name Orderings.less_eq}] s
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
   @{cpat "(?x::?'a::linordered_idom) < (?y::?'a)"},
   @{cpat "(?x::?'a::linordered_idom) <= (?y::?'a)"}]

val zero_one_idom_simproc =
  make_simproc {lhss = lhss' , name = "zero_one_idom_simproc",
  proc = sproc, identifier = []}

fun number_of thy T n =
  if not (Sign.of_sort thy (T, @{sort numeral}))
  then raise CTERM ("number_of", [])
  else Numeral.mk_cnumber (Thm.ctyp_of thy T) n;

val setup =
  Lin_Arith.add_inj_thms [@{thm zle_int} RS iffD2, @{thm int_int_eq} RS iffD2]
  #> Lin_Arith.add_lessD @{thm zless_imp_add1_zle}
  #> Lin_Arith.add_simps (@{thms simp_thms} @ @{thms arith_simps} @ @{thms rel_simps}
      @ @{thms arith_special} @ @{thms int_arith_rules})
  #> Lin_Arith.add_simprocs [zero_one_idom_simproc]
  #> Lin_Arith.set_number_of number_of
  #> Lin_Arith.add_inj_const (@{const_name of_nat}, HOLogic.natT --> HOLogic.intT)
  #> Lin_Arith.add_discrete_type @{type_name Int.int}

end;
