(*  Title:      HOL/BCV/Fixpoint.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1999 TUM
*)

goalw_cterm [] (cterm_of (sign_of thy) (HOLogic.mk_Trueprop (hd fix.tcs)));
by (asm_full_simp_tac (simpset() addsimps [wf_iff_no_infinite_down_chain]
                                addsplits [split_split]) 1);
by (Clarify_tac 1);
by (rtac ccontr 1);
by (Asm_full_simp_tac 1);
by (res_inst_tac[("x","0")] allE 1);
by (assume_tac 1);
by (Clarify_tac 1);
by (rename_tac "next s0" 1);
by (subgoal_tac "!i. fst(f i) = next" 1);
by (eres_inst_tac[("x","%i. snd(f i)")] allE 1);
by (Asm_full_simp_tac 1);
by (Clarify_tac 1);
by (eres_inst_tac[("x","i")] allE 1);
by (eres_inst_tac[("x","i")] allE 1);
by (Force_tac 1);
by (rtac allI 1);
by (induct_tac "i" 1);
by (Asm_simp_tac 1);
by (eres_inst_tac[("x","n")] allE 1);
by (Auto_tac);
val fix_tc = result();

Goalw [wf_iff_no_infinite_down_chain RS eq_reflection]
 "[| wf{(t,s). s:A & next s = Some t & t ~= s}; \
\    !a:A. next a : option A; s:A |] ==> \
\ fix(next,s) = (case next s of None => False \
\                | Some t => if t=s then True else fix(next,t))";
by (stac (fix_tc RS (hd fix.rules)) 1);
by (Simp_tac 1);
by (Clarify_tac 1);
by (subgoal_tac "!i. f i : A" 1);
 by (Blast_tac 1);
by (rtac allI 1);
by (induct_tac "i" 1);
 by (Asm_simp_tac 1);
by (Auto_tac);
qed "fix_unfold";

(* Thm: next has fixpoint above s iff fix(next,s) *)

Goal "[| x = Some y; x : option A |] ==> y : A";
by (Blast_tac 1);
val lemma = result();

Goal
"[| acc L; \
\   !t:L. !s:L. next t = Some t & s <= t --> (? u. next s = Some u & u <= t); \
\   !a:L. next a : option L; !a:L. !b. next a = Some b --> a <= b |] \
\ ==> s:L --> fix(next,s) = (? t:L. s <= t & next t = Some t)";
by (subgoal_tac "wf{(y,x::'a::order). x : L & next x = Some y & y ~= x}" 1);
 by (full_simp_tac (simpset() addsimps [acc_def]) 2);
 by (etac wf_subset 2);
 by (simp_tac (simpset() addsimps [order_less_le]) 2);
 by (blast_tac (claset() addDs [lemma]) 2);
by (res_inst_tac [("a","s")] wf_induct 1);
 by (assume_tac 1);
by (Clarify_tac 1);
by (Full_simp_tac 1);
by (stac fix_unfold 1);
   by (assume_tac 1);
  by (assume_tac 1);
 by (assume_tac 1);
by (split_tac [option.split] 1);
by (rtac conjI 1);
 by (thin_tac "!a:L. !b. next a = Some b --> a <= b" 1);
 by (Force_tac 1);
by (Clarify_tac 1);
by (split_tac [split_if] 1);
by (rtac conjI 1);
 by (Blast_tac 1);
by (Clarify_tac 1);
by (EVERY[etac allE 1, etac impE 1, etac impE 2, etac trans 3]);
  by (Blast_tac 1);
 by (etac lemma 1);
 by (Blast_tac 1);
by (rtac iffI 1);
 by (blast_tac (claset() addIs [order_trans]) 1);
by (Clarify_tac 1);
by (EVERY[rtac bexI 1, atac 2, rtac conjI 1, atac 2]);
by (thin_tac "!a:L. !b. next a = Some b --> a <= b" 1);
by (Force_tac 1);
qed_spec_mp "fix_iff_has_fixpoint";


(* This lemma looks more pleasing to the eye, because of the monotonicity
assumption for next, instead of the strange assumption above.
However, function next as defined in DFAimpl is NOT monotone because
None is not required to be detected as early as possible. Thus the following
does not hold: sos <= tos & next sos = None ==> next tos = None

Goal
"[| wf{(y,x::'a::order). x : L & next x = Some y & y ~= x}; \
\   !t:L. !s:L. s <= t & next s = None --> next t = None; \
\   !t:L. !s:L. !u. s <= t & next s = Some u --> \
\                   next t = None | (? v. next t = Some v & u <= v); \
\   !a:L. next a : option L; !a:L. !b. next a = Some b --> a <= b |] \
\ ==> s:L --> fix(next,s) = (? t:L. s <= t & next t = Some t)";
by (res_inst_tac [("a","s")] wf_induct 1);
 by (assume_tac 1);
by (Clarify_tac 1);
by (Full_simp_tac 1);
by (stac fix_unfold 1);
   by (assume_tac 1);
  by (assume_tac 1);
 by (assume_tac 1);
by (split_tac [option.split] 1);
by (rtac conjI 1);
 by (blast_tac (claset() addDs [sym RS trans]) 1);
by (Clarify_tac 1);
by (split_tac [split_if] 1);
by (rtac conjI 1);
 by (Blast_tac 1);
by (Clarify_tac 1);
by (EVERY[etac allE 1, etac impE 1, etac impE 2, etac trans 3]);
  by (Blast_tac 1);
 by (etac lemma 1);
 by (Blast_tac 1);
by (rtac iffI 1);
 by (subgoal_tac "next a ~= None" 1);
  by (Clarify_tac 1);
  by (EVERY[etac ballE 1, etac ballE 1, etac allE 1, etac impE 1,etac disjE 2]);
      by (rtac conjI 1);
       by (assume_tac 1);
      by (assume_tac 1);
     by (blast_tac (claset() addDs [sym RS trans]) 1);
    by (blast_tac (claset() addIs [order_trans]) 1);
   by (blast_tac (claset() addIs [order_trans]) 1);
  by (Blast_tac 1);
 by (rtac notI 1);
 by (Clarify_tac 1);
 by (blast_tac (claset() addDs [sym RS trans,lemma]) 1);
by (blast_tac (claset() addDs [sym RS trans]) 1);
qed_spec_mp "fix_iff_has_fixpoint";
*)
