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

val zeroth = Thm.symmetric (mk_meta_eq @{thm of_int_0});

val zero_to_of_int_zero_simproc =
  Simplifier.make_simproc @{context} "zero_to_of_int_zero_simproc"
   {lhss = [@{term "0::'a::ring"}],
    proc = fn _ => fn ctxt => fn ct =>
      let val T = Thm.ctyp_of_cterm ct in
        if Thm.typ_of T = @{typ int} then NONE
        else SOME (Thm.instantiate' [SOME T] [] zeroth)
      end};

val oneth = Thm.symmetric (mk_meta_eq @{thm of_int_1});

val one_to_of_int_one_simproc =
  Simplifier.make_simproc @{context} "one_to_of_int_one_simproc"
   {lhss = [@{term "1::'a::ring_1"}],
    proc = fn _ => fn ctxt => fn ct =>
      let val T = Thm.ctyp_of_cterm ct in
        if Thm.typ_of T = @{typ int} then NONE
        else SOME (Thm.instantiate' [SOME T] [] oneth)
      end};

fun check (Const (@{const_name Groups.one}, @{typ int})) = false
  | check (Const (@{const_name Groups.one}, _)) = true
  | check (Const (s, _)) = member (op =) [@{const_name HOL.eq},
      @{const_name Groups.times}, @{const_name Groups.uminus},
      @{const_name Groups.minus}, @{const_name Groups.plus},
      @{const_name Groups.zero},
      @{const_name Orderings.less}, @{const_name Orderings.less_eq}] s
  | check (a $ b) = check a andalso check b
  | check _ = false;

val conv_ss =
  simpset_of (put_simpset HOL_basic_ss @{context}
    addsimps
     ((map (fn th => th RS sym) [@{thm of_int_add}, @{thm of_int_mult},
             @{thm of_int_diff},  @{thm of_int_minus}])@
      [@{thm of_int_less_iff}, @{thm of_int_le_iff}, @{thm of_int_eq_iff}])
     addsimprocs [zero_to_of_int_zero_simproc,one_to_of_int_one_simproc]);

val zero_one_idom_simproc =
  Simplifier.make_simproc @{context} "zero_one_idom_simproc"
   {lhss =
      [@{term "(x::'a::ring_char_0) = y"},
       @{term "(x::'a::linordered_idom) < y"},
       @{term "(x::'a::linordered_idom) \<le> y"}],
    proc = fn _ => fn ctxt => fn ct =>
      if check (Thm.term_of ct)
      then SOME (Simplifier.rewrite (put_simpset conv_ss ctxt) ct)
      else NONE};


fun number_of ctxt T n =
  if not (Sign.of_sort (Proof_Context.theory_of ctxt) (T, @{sort numeral}))
  then raise CTERM ("number_of", [])
  else Numeral.mk_cnumber (Thm.ctyp_of ctxt T) n;

val setup =
  Lin_Arith.add_inj_thms [@{thm of_nat_le_iff} RS iffD2, @{thm of_nat_eq_iff} RS iffD2]
  #> Lin_Arith.add_lessD @{thm zless_imp_add1_zle}
  #> Lin_Arith.add_simps @{thms of_nat_simps of_int_simps}
  #> Lin_Arith.add_simps
      [@{thm of_int_numeral}, @{thm nat_0}, @{thm nat_1}, @{thm diff_nat_numeral}, @{thm nat_numeral}]
  #> Lin_Arith.add_simprocs [zero_one_idom_simproc]
  #> Lin_Arith.set_number_of number_of
  #> Lin_Arith.add_inj_const (@{const_name of_nat}, HOLogic.natT --> HOLogic.intT)
  #> Lin_Arith.add_discrete_type @{type_name Int.int}

end;
