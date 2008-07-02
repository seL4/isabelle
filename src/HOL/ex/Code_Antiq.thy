(*  Title:      HOL/ex/Code_Antiq.thy
    ID:         $Id$
    Author:     Florian Haftmann
*)

header {* A simple certificate check as toy example for the code antiquotation *}

theory Code_Antiq
imports Plain
begin

lemma div_cert1:
  fixes n m q r :: nat
  assumes "r < m"
    and "0 < m"
    and "n = m * q + r"
  shows "n div m = q"
using assms by (simp add: div_mult_self2 add_commute)

lemma div_cert2:
  fixes n :: nat
  shows "n div 0 = 0"
by simp

ML {*
local

fun code_of_val k = if k <= 0 then @{code "0::nat"}
  else @{code Suc} (code_of_val (k - 1));

fun val_of_code @{code "0::nat"} = 0
  | val_of_code (@{code Suc} n) = val_of_code n + 1;

val term_of_code = HOLogic.mk_nat o val_of_code;

infix 9 &$;
val op &$ = uncurry Thm.capply;

val simpset = HOL_ss addsimps
  @{thms plus_nat.simps add_0_right add_Suc_right times_nat.simps mult_0_right mult_Suc_right  less_nat_zero_code le_simps(2) less_eq_nat.simps(1) le_simps(3)}

fun prove prop = Goal.prove_internal [] (@{cterm Trueprop} &$ prop)
  (K (ALLGOALS (Simplifier.simp_tac simpset))); (*FIXME*)

in

fun simp_div ctxt ct_n ct_m =
  let
    val m = HOLogic.dest_nat (Thm.term_of ct_m);
  in if m = 0 then Drule.instantiate'[] [SOME ct_n] @{thm div_cert2} else
    let
      val thy = ProofContext.theory_of ctxt;
      val n = HOLogic.dest_nat (Thm.term_of ct_n);
      val c_n = code_of_val n;
      val c_m = code_of_val m;
      val (c_q, c_r) = @{code divmod} c_n c_m;
      val t_q = term_of_code c_q;
      val t_r = term_of_code c_r;
      val ct_q = Thm.cterm_of thy t_q;
      val ct_r = Thm.cterm_of thy t_r;
      val thm_r = prove (@{cterm "op < \<Colon> nat \<Rightarrow> _"} &$ ct_r &$ ct_m);
      val thm_m = prove (@{cterm "(op < \<Colon> nat \<Rightarrow> _) 0"} &$ ct_m);
      val thm_n = prove (@{cterm "(op = \<Colon> nat \<Rightarrow> _)"} &$ ct_n
        &$ (@{cterm "(op + \<Colon> nat \<Rightarrow> _)"}
          &$ (@{cterm "(op * \<Colon> nat \<Rightarrow> _)"} &$ ct_m &$ ct_q) &$ ct_r));
    in @{thm div_cert1} OF [thm_r, thm_m, thm_n] end
  end;

end;
*}

ML_val {*
  simp_div @{context}
    @{cterm "Suc (Suc (Suc (Suc (Suc 0))))"}
    @{cterm "(Suc (Suc 0))"}
*}

ML_val {*
  simp_div @{context}
    (Thm.cterm_of @{theory} (HOLogic.mk_nat 170))
    (Thm.cterm_of @{theory} (HOLogic.mk_nat 42))
*}

end