(*  Title:      HOL/ex/set.ML
    ID:         $Id$
    Author:     Tobias Nipkow, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Cantor's Theorem; the Schroeder-Berstein Theorem.  
*)

(*These two are cited in Benzmueller and Kohlhase's system description of LEO,
  CADE-15, 1998 (page 139-143) as theorems LEO could not prove.*)

Goal "(X = Y Un Z) = (Y<=X & Z<=X & (ALL V. Y<=V & Z<=V --> X<=V))";
by (Blast_tac 1);
qed "";

Goal "(X = Y Int Z) = (X<=Y & X<=Z & (ALL V. V<=Y & V<=Z --> V<=X))";
by (Blast_tac 1);
qed "";

(*trivial example of term synthesis: apparently hard for some provers!*)
Goal "a ~= b ==> a:?X & b ~: ?X";
by (Blast_tac 1);
qed "";

(** Examples for the Blast_tac paper **)

(*Union-image, called Un_Union_image on equalities.ML*)
Goal "(UN x:C. f(x) Un g(x)) = Union(f``C)  Un  Union(g``C)";
by (Blast_tac 1);
qed "";

(*Inter-image, called Int_Inter_image on equalities.ML*)
Goal "(INT x:C. f(x) Int g(x)) = Inter(f``C) Int Inter(g``C)";
by (Blast_tac 1);
qed "";

(*Singleton I.  Nice demonstration of blast_tac--and its limitations*)
Goal "!!S::'a set set. ALL x:S. ALL y:S. x<=y ==> EX z. S <= {z}";
(*for some unfathomable reason, UNIV_I increases the search space greatly*)
by (blast_tac (claset() delrules [UNIV_I]) 1);
qed "";

(*Singleton II.  variant of the benchmark above*)
Goal "ALL x:S. Union(S) <= x ==> EX z. S <= {z}";
by (blast_tac (claset() delrules [UNIV_I]) 1);
(*just Blast_tac takes 5 seconds instead of 1*)
qed "";

(*** A unique fixpoint theorem --- fast/best/meson all fail ***)

Goal "?!x. f(g(x))=x ==> ?!y. g(f(y))=y";
by (EVERY1[etac ex1E, rtac ex1I, etac arg_cong,
          rtac subst, atac, etac allE, rtac arg_cong, etac mp, etac arg_cong]);
qed "";


(*** Cantor's Theorem: There is no surjection from a set to its powerset. ***)

Goal "~ (? f:: 'a=>'a set. ! S. ? x. f(x) = S)";
(*requires best-first search because it is undirectional*)
by (best_tac (claset() addSEs [equalityCE]) 1);
qed "cantor1";

(*This form displays the diagonal term*)
Goal "! f:: 'a=>'a set. ! x. f(x) ~= ?S(f)";
by (best_tac (claset() addSEs [equalityCE]) 1);
uresult();

(*This form exploits the set constructs*)
Goal "?S ~: range(f :: 'a=>'a set)";
by (rtac notI 1);
by (etac rangeE 1);
by (etac equalityCE 1);
by (dtac CollectD 1);
by (contr_tac 1);
by (swap_res_tac [CollectI] 1);
by (assume_tac 1);

choplev 0;
by (best_tac (claset() addSEs [equalityCE]) 1);
qed "";


(*** The Schroder-Berstein Theorem ***)

Goal "[| -(f``X) = g``(-X);  f(a)=g(b);  a:X |] ==> b:X";
by (blast_tac (claset() addEs [equalityE]) 1);
qed "disj_lemma";

Goal "-(f``X) = g``(-X) ==> surj(%z. if z:X then f(z) else g(z))";
by (asm_simp_tac (simpset() addsimps [surj_def]) 1);
by (blast_tac (claset() addEs [equalityE]) 1);
qed "surj_if_then_else";

Goalw [inj_on_def]
     "[| inj_on f X;  inj_on g (-X);  -(f``X) = g``(-X); \
\        h = (%z. if z:X then f(z) else g(z)) |]       \
\     ==> inj(h) & surj(h)";
by (asm_simp_tac (simpset() addsimps [surj_if_then_else]) 1);
   (*PROOF FAILED if inj_onD*)
by (blast_tac (claset() addDs [disj_lemma, sym RSN (2,disj_lemma)]) 1);
qed "bij_if_then_else";

Goal "? X. X = - (g``(- (f``X)))";
by (rtac exI 1);
by (rtac lfp_Tarski 1);
by (REPEAT (ares_tac [monoI, image_mono, Compl_anti_mono] 1));
qed "decomposition";

val [injf,injg] = goal (the_context ())
   "[| inj (f:: 'a=>'b);  inj (g:: 'b=>'a) |] ==> \
\   ? h:: 'a=>'b. inj(h) & surj(h)";
by (rtac (decomposition RS exE) 1);
by (rtac exI 1);
by (rtac bij_if_then_else 1);
by (rtac refl 4);
by (rtac inj_on_inv 2);
by (rtac ([subset_UNIV, injf] MRS subset_inj_on) 1);
  (**tricky variable instantiations!**)
by (EVERY1 [etac ssubst, stac double_complement, rtac subsetI,
            etac imageE, etac ssubst, rtac rangeI]);
by (EVERY1 [etac ssubst, stac double_complement, 
            rtac (injg RS inv_image_comp RS sym)]);
qed "schroeder_bernstein";
