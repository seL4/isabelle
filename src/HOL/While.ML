(*  Title:      HOL/While
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TU Muenchen
*)

goalw_cterm [] (cterm_of (sign_of thy)
 (HOLogic.mk_Trueprop (hd while_aux.tcs)));
br wf_same_fstI 1;
br wf_same_fstI 1;
by (asm_full_simp_tac (simpset() addsimps [wf_iff_no_infinite_down_chain]) 1);
by(Blast_tac 1);
val while_aux_tc = result();

Goal
 "while_aux(b,c,s) = (if ? f. f 0 = s & (!i. b(f i) & c(f i) = f(i+1)) \
\                     then arbitrary \
\                     else (if b s then while_aux(b,c,c s) else s))";
by(rtac (while_aux_tc RS (hd while_aux.simps) RS trans) 1);
 by(simp_tac (simpset() addsimps [same_fst_def]) 1);
br refl 1;
qed "while_aux_unfold";

(*** The recursion equation for while: directly executable! ***)

Goalw [while_def] "while b c s = (if b s then while b c (c s) else s)";
by(rtac (while_aux_unfold RS trans) 1);
by (Auto_tac);
by(stac while_aux_unfold 1);
by(Asm_full_simp_tac 1);
by(Clarify_tac 1);
by(eres_inst_tac [("x","%i. f(Suc i)")] allE 1);
by(Blast_tac 1);
qed "while_unfold";

(*** The proof rule for while; P is the invariant ***)

val [prem1,prem2,prem3] = Goal
"[| !!s. [| P s; b s |] ==> P(c s); \
\   !!s. [| P s; ~b s |] ==> Q s; \
\   wf{(t,s). P s & b s & t = c s} |] \
\ ==> P s --> Q(while b c s)";
by(res_inst_tac [("a","s")] (prem3 RS wf_induct) 1);
by(Asm_full_simp_tac 1);
by(Clarify_tac 1);
by(stac while_unfold 1);
by(asm_full_simp_tac (simpset() addsimps [prem1,prem2]) 1);
qed_spec_mp "while_rule";

(*** An application: computation of the lfp on finite sets via iteration ***)

Goal
 "[| mono f; finite U; f U = U |] \
\ ==> lfp f = fst(while (%(A,fA). A~=fA) (%(A,fA). (fA, f fA)) ({},f{}))";
by(res_inst_tac [("P","%(A,B).(A <= U & B = f A & A <= B & B <= lfp f)")]
     while_rule 1);
   by(stac lfp_Tarski 1);
    ba 1;
   by(Clarsimp_tac 1);
   by(blast_tac (claset() addDs [monoD]) 1);
  by(fast_tac (claset() addSIs [lfp_lowerbound] addss simpset()) 1);
 by(res_inst_tac [("r","((Pow U <*> UNIV) <*> (Pow U <*> UNIV)) Int \
 \                      inv_image finite_psubset (op - U o fst)")]
                 wf_subset 1);
  by(blast_tac (claset() addIs
      [wf_finite_psubset,Int_lower2 RSN (2,wf_subset)]) 1);
 by(clarsimp_tac (claset(),simpset() addsimps
      [inv_image_def,finite_psubset_def,order_less_le]) 1);
 by(blast_tac (claset() addSIs [finite_Diff] addDs [monoD]) 1);
by(stac lfp_Tarski 1);
 ba 1;
by(asm_simp_tac (simpset() addsimps [monoD]) 1);
qed "lfp_conv_while";

(*** An example; requires integers

Goal "{f n|n. A n | B n} = {f n|n. A n} Un {f n|n. B n}";
by(Blast_tac 1);
qed "lemma";

Goal "P(lfp (%N::int set. {#0} Un {(n + #2) mod #6 |n. n:N})) = P{#0,#4,#2}";
by(stac (read_instantiate [("U","{#0,#1,#2,#3,#4,#5}")] lfp_conv_while) 1);
   br monoI 1;
   by(Blast_tac 1);
  by(Simp_tac 1);
 by(simp_tac (simpset() addsimps [lemma,set_eq_subset]) 1);
(* The fixpoint computation is performed purely by rewriting: *)
by(simp_tac (simpset() addsimps [while_unfold,lemma,set_eq_subset]
     delsimps [subset_empty]) 1);
result();

***)
