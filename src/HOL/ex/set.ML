(*  Title:      HOL/ex/set.ML
    ID:         $Id$
    Author:     Tobias Nipkow, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Cantor's Theorem; the Schroeder-Berstein Theorem.  
*)


writeln"File HOL/ex/set.";

set_current_thy"Set";

(*Nice demonstration of blast_tac--and its overloading problems*)
goal Set.thy "!!S::'a set set. ALL x:S. ALL y:S. x<=y ==> EX z. S <= {z}";
let val insertCI' = read_instantiate [("'a", "?'a set")] insertCI
in    (*Type instantiation is required so that blast_tac can apply equalityI
        to the subgoal arising from insertCI*)
by(blast_tac (!claset addSIs [insertCI']) 1)
end;

(*** A unique fixpoint theorem --- fast/best/meson all fail ***)

val [prem] = goal HOL.thy "?!x.f(g(x))=x ==> ?!y.g(f(y))=y";
by (EVERY1[rtac (prem RS ex1E), rtac ex1I, etac arg_cong,
          rtac subst, atac, etac allE, rtac arg_cong, etac mp, etac arg_cong]);
result();

(*** Cantor's Theorem: There is no surjection from a set to its powerset. ***)

goal Set.thy "~ (? f:: 'a=>'a set. ! S. ? x. f(x) = S)";
(*requires best-first search because it is undirectional*)
by (best_tac (!claset addSEs [equalityCE]) 1);
qed "cantor1";

(*This form displays the diagonal term*)
goal Set.thy "! f:: 'a=>'a set. ! x. f(x) ~= ?S(f)";
by (best_tac (!claset addSEs [equalityCE]) 1);
uresult();

(*This form exploits the set constructs*)
goal Set.thy "?S ~: range(f :: 'a=>'a set)";
by (rtac notI 1);
by (etac rangeE 1);
by (etac equalityCE 1);
by (dtac CollectD 1);
by (contr_tac 1);
by (swap_res_tac [CollectI] 1);
by (assume_tac 1);

choplev 0;
by (best_tac (!claset addSEs [equalityCE]) 1);

(*** The Schroder-Berstein Theorem ***)

goalw Lfp.thy [image_def] "!!f. inj(f) ==> inv(f)``(f``X) = X";
by (rtac equalityI 1);
by (fast_tac (!claset addEs [inv_f_f RS ssubst]) 1);
by (fast_tac (!claset addEs [inv_f_f RS ssubst]) 1);
qed "inv_image_comp";

goal Set.thy "!!f. f(a) ~: (f``X) ==> a~:X";
by (Blast_tac 1);
qed "contra_imageI";

goal Lfp.thy "(a ~: Compl(X)) = (a:X)";
by (Blast_tac 1);
qed "not_Compl";

(*Lots of backtracking in this proof...*)
val [compl,fg,Xa] = goal Lfp.thy
    "[| Compl(f``X) = g``Compl(X);  f(a)=g(b);  a:X |] ==> b:X";
by (EVERY1 [rtac (not_Compl RS subst), rtac contra_imageI,
            rtac (compl RS subst), rtac (fg RS subst), stac not_Compl,
            rtac imageI, rtac Xa]);
qed "disj_lemma";

goalw Lfp.thy [image_def]
    "range(%z. if z:X then f(z) else g(z)) = f``X Un g``Compl(X)";
by (simp_tac (!simpset setloop split_tac [expand_if]) 1);
by (Blast_tac 1);
qed "range_if_then_else";

goal Lfp.thy "a : X Un Compl(X)";
by (Blast_tac 1);
qed "X_Un_Compl";

goalw Lfp.thy [surj_def] "surj(f) = (!a. a : range(f))";
by (fast_tac (!claset addEs [ssubst]) 1);
qed "surj_iff_full_range";

val [compl] = goal Lfp.thy
    "Compl(f``X) = g``Compl(X) ==> surj(%z. if z:X then f(z) else g(z))";
by (EVERY1[stac surj_iff_full_range, stac range_if_then_else,
           stac (compl RS sym)]);
by (rtac (X_Un_Compl RS allI) 1);
qed "surj_if_then_else";

val [injf,injg,compl,bij] = goal Lfp.thy
    "[| inj_onto f X;  inj_onto g (Compl X);  Compl(f``X) = g``Compl(X); \
\       bij = (%z. if z:X then f(z) else g(z)) |] ==> \
\       inj(bij) & surj(bij)";
val f_eq_gE = make_elim (compl RS disj_lemma);
by (stac bij 1);
by (rtac conjI 1);
by (rtac (compl RS surj_if_then_else) 2);
by (rewtac inj_def);
by (cut_facts_tac [injf,injg] 1);
by (EVERY1 [rtac allI, rtac allI, stac expand_if, rtac conjI, stac expand_if]);
by (fast_tac (!claset addEs  [inj_ontoD, sym RS f_eq_gE]) 1);
by (stac expand_if 1);
by (fast_tac (!claset addEs  [inj_ontoD, f_eq_gE]) 1);
qed "bij_if_then_else";

goal Lfp.thy "? X. X = Compl(g``Compl((f:: 'a=>'b)``X))";
by (rtac exI 1);
by (rtac lfp_Tarski 1);
by (REPEAT (ares_tac [monoI, image_mono, Compl_anti_mono] 1));
qed "decomposition";

val [injf,injg] = goal Lfp.thy
   "[| inj(f:: 'a=>'b);  inj(g:: 'b=>'a) |] ==> \
\   ? h:: 'a=>'b. inj(h) & surj(h)";
by (rtac (decomposition RS exE) 1);
by (rtac exI 1);
by (rtac bij_if_then_else 1);
by (EVERY [rtac refl 4, rtac (injf RS inj_imp) 1,
           rtac (injg RS inj_onto_inv) 1]);
by (EVERY1 [etac ssubst, stac double_complement, rtac subsetI,
            etac imageE, etac ssubst, rtac rangeI]);
by (EVERY1 [etac ssubst, stac double_complement, 
            rtac (injg RS inv_image_comp RS sym)]);
qed "schroeder_bernstein";

writeln"Reached end of file.";
