(*  Title:      HOL/Tools/rewrite_hol_proof.ML
    Author:     Stefan Berghofer, TU Muenchen

Rewrite rules for HOL proofs
*)

signature REWRITE_HOL_PROOF =
sig
  val rews: (Proofterm.proof * Proofterm.proof) list
  val elim_cong: typ list -> term option list -> Proofterm.proof -> (Proofterm.proof * Proofterm.proof) option
end;

structure RewriteHOLProof : REWRITE_HOL_PROOF =
struct

val rews = map (apply2 (Proof_Syntax.proof_of_term @{theory} true) o
    Logic.dest_equals o Logic.varify_global o Proof_Syntax.read_term @{theory} true propT)

  (** eliminate meta-equality rules **)

  ["(equal_elim % x1 % x2 %% \
 \    (combination % TYPE('T1) % TYPE('T2) % Trueprop % x3 % A % B %%  \
 \      (axm.reflexive % TYPE('T3) % x4) %% prf1)) ==  \
 \  (iffD1 % A % B %%  \
 \    (meta_eq_to_obj_eq % TYPE(bool) % A % B %% arity_type_bool %% prf1))",

   "(equal_elim % x1 % x2 %% (axm.symmetric % TYPE('T1) % x3 % x4 %%  \
 \    (combination % TYPE('T2) % TYPE('T3) % Trueprop % x5 % A % B %%  \
 \      (axm.reflexive % TYPE('T4) % x6) %% prf1))) ==  \
 \  (iffD2 % A % B %%  \
 \    (meta_eq_to_obj_eq % TYPE(bool) % A % B %% arity_type_bool %% prf1))",

   "(meta_eq_to_obj_eq % TYPE('U) % x1 % x2 %% prfU %%  \
 \    (combination % TYPE('T) % TYPE('U) % f % g % x % y %% prf1 %% prf2)) ==  \
 \  (cong % TYPE('T) % TYPE('U) % f % g % x % y %%  \
 \    (OfClass type_class % TYPE('T)) %% prfU %%  \
 \    (meta_eq_to_obj_eq % TYPE('T => 'U) % f % g %% (OfClass type_class % TYPE('T => 'U)) %% prf1) %%  \
 \    (meta_eq_to_obj_eq % TYPE('T) % x % y %% (OfClass type_class % TYPE('T)) %% prf2))",

   "(meta_eq_to_obj_eq % TYPE('T) % x1 % x2 %% prfT %%  \
 \    (axm.transitive % TYPE('T) % x % y % z %% prf1 %% prf2)) ==  \
 \  (HOL.trans % TYPE('T) % x % y % z %% prfT %%  \
 \    (meta_eq_to_obj_eq % TYPE('T) % x % y %% prfT %% prf1) %%  \
 \    (meta_eq_to_obj_eq % TYPE('T) % y % z %% prfT %% prf2))",

   "(meta_eq_to_obj_eq % TYPE('T) % x % x %% prfT %% (axm.reflexive % TYPE('T) % x)) ==  \
 \  (HOL.refl % TYPE('T) % x %% prfT)",

   "(meta_eq_to_obj_eq % TYPE('T) % x % y %% prfT %%  \
 \    (axm.symmetric % TYPE('T) % x % y %% prf)) ==  \
 \  (sym % TYPE('T) % x % y %% prfT %% (meta_eq_to_obj_eq % TYPE('T) % x % y %% prfT %% prf))",

   "(meta_eq_to_obj_eq % TYPE('T => 'U) % x1 % x2 %% prfTU %%  \
 \    (abstract_rule % TYPE('T) % TYPE('U) % f % g %% prf)) ==  \
 \  (ext % TYPE('T) % TYPE('U) % f % g %%  \
 \    (OfClass type_class % TYPE('T)) %% (OfClass type_class % TYPE('U)) %%  \
 \    (Lam (x::'T). meta_eq_to_obj_eq % TYPE('U) % f x % g x %%  \
 \       (OfClass type_class % TYPE('U)) %% (prf % x)))",

   "(meta_eq_to_obj_eq % TYPE('T) % x % y %% prfT %%  \
 \    (eq_reflection % TYPE('T) % x % y %% prfT %% prf)) == prf",

   "(meta_eq_to_obj_eq % TYPE('T) % x1 % x2 %% prfT %% (equal_elim % x3 % x4 %%  \
 \    (combination % TYPE('T) % TYPE(prop) % x7 % x8 % C % D %%  \
 \      (combination % TYPE('T) % TYPE('T3) % op == % op == % A % B %%  \
 \        (axm.reflexive % TYPE('T4) % op ==) %% prf1) %% prf2) %% prf3)) ==  \
 \  (iffD1 % A = C % B = D %%  \
 \    (cong % TYPE('T) % TYPE(bool) % op = A % op = B % C % D %%  \
 \      prfT %% arity_type_bool %%  \
 \      (cong % TYPE('T) % TYPE('T=>bool) %  \
 \        (op = :: 'T=>'T=>bool) % (op = :: 'T=>'T=>bool) % A % B %%  \
 \        prfT %% (OfClass type_class % TYPE('T=>bool)) %%  \
 \        (HOL.refl % TYPE('T=>'T=>bool) % (op = :: 'T=>'T=>bool) %%  \
 \           (OfClass type_class % TYPE('T=>'T=>bool))) %%  \
 \        (meta_eq_to_obj_eq % TYPE('T) % A % B %% prfT %% prf1)) %%  \
 \      (meta_eq_to_obj_eq % TYPE('T) % C % D %% prfT %% prf2)) %%  \
 \    (meta_eq_to_obj_eq % TYPE('T) % A % C %% prfT %% prf3))",

   "(meta_eq_to_obj_eq % TYPE('T) % x1 % x2 %% prfT %% (equal_elim % x3 % x4 %%  \
 \    (axm.symmetric % TYPE('T2) % x5 % x6 %%  \
 \      (combination % TYPE('T) % TYPE(prop) % x7 % x8 % C % D %%  \
 \        (combination % TYPE('T) % TYPE('T3) % op == % op == % A % B %%  \
 \          (axm.reflexive % TYPE('T4) % op ==) %% prf1) %% prf2)) %% prf3)) ==  \
 \  (iffD2 % A = C % B = D %%  \
 \    (cong % TYPE('T) % TYPE(bool) % op = A % op = B % C % D %%  \
 \      prfT %% arity_type_bool %%  \
 \      (cong % TYPE('T) % TYPE('T=>bool) %  \
 \        (op = :: 'T=>'T=>bool) % (op = :: 'T=>'T=>bool) % A % B %%  \
 \        prfT %% (OfClass type_class % TYPE('T=>bool)) %%  \
 \        (HOL.refl % TYPE('T=>'T=>bool) % (op = :: 'T=>'T=>bool) %%  \
 \           (OfClass type_class % TYPE('T=>'T=>bool))) %%  \
 \        (meta_eq_to_obj_eq % TYPE('T) % A % B %% prfT %% prf1)) %%  \
 \      (meta_eq_to_obj_eq % TYPE('T) % C % D %% prfT %% prf2)) %%  \
 \    (meta_eq_to_obj_eq % TYPE('T) % B % D %% prfT %% prf3))",

   (** rewriting on bool: insert proper congruence rules for logical connectives **)

   (* All *)

   "(iffD1 % All P % All Q %% (cong % TYPE('T1) % TYPE('T2) % All % All % P % Q %% prfT1 %% prfT2 %%  \
 \    (HOL.refl % TYPE('T3) % x1 %% prfT3) %%  \
 \    (ext % TYPE('a) % TYPE(bool) % x2 % x3 %% prfa %% prfb %% prf)) %% prf') ==  \
 \  (allI % TYPE('a) % Q %% prfa %%  \
 \    (Lam x.  \
 \        iffD1 % P x % Q x %% (prf % x) %%  \
 \         (spec % TYPE('a) % P % x %% prfa %% prf')))",

   "(iffD2 % All P % All Q %% (cong % TYPE('T1) % TYPE('T2) % All % All % P % Q %% prfT1 %% prfT2 %%  \
 \    (HOL.refl % TYPE('T3) % x1 %% prfT3) %%  \
 \    (ext % TYPE('a) % TYPE(bool) % x2 % x3 %% prfa %% prfb %% prf)) %% prf') ==  \
 \  (allI % TYPE('a) % P %% prfa %%  \
 \    (Lam x.  \
 \        iffD2 % P x % Q x %% (prf % x) %%  \
 \         (spec % TYPE('a) % Q % x %% prfa %% prf')))",

   (* Ex *)

   "(iffD1 % Ex P % Ex Q %% (cong % TYPE('T1) % TYPE('T2) % Ex % Ex % P % Q %% prfT1 %% prfT2 %%  \
 \    (HOL.refl % TYPE('T3) % x1 %% prfT3) %%  \
 \    (ext % TYPE('a) % TYPE(bool) % x2 % x3 %% prfa %% prfb %% prf)) %% prf') ==  \
 \  (exE % TYPE('a) % P % EX x. Q x %% prfa %% prf' %%  \
 \    (Lam x H : P x.  \
 \        exI % TYPE('a) % Q % x %% prfa %%  \
 \         (iffD1 % P x % Q x %% (prf % x) %% H)))",

   "(iffD2 % Ex P % Ex Q %% (cong % TYPE('T1) % TYPE('T2) % Ex % Ex % P % Q %% prfT1 %% prfT2 %%  \
 \    (HOL.refl % TYPE('T3) % x1 %% prfT3) %%  \
 \    (ext % TYPE('a) % TYPE(bool) % x2 % x3 %% prfa %% prfb %% prf)) %% prf') ==  \
 \  (exE % TYPE('a) % Q % EX x. P x %% prfa %% prf' %%  \
 \    (Lam x H : Q x.  \
 \        exI % TYPE('a) % P % x %% prfa %%  \
 \         (iffD2 % P x % Q x %% (prf % x) %% H)))",

   (* & *)

   "(iffD1 % A & C % B & D %% (cong % TYPE('T1) % TYPE('T2) % x1 % x2 % C % D %% prfT1 %% prfT2 %%  \
 \    (cong % TYPE('T3) % TYPE('T4) % op & % op & % A % B %% prfT3 %% prfT4 %%  \
 \      (HOL.refl % TYPE('T5) % op & %% prfT5) %% prf1) %% prf2) %% prf3) ==  \
 \  (conjI % B % D %%  \
 \    (iffD1 % A % B %% prf1 %% (conjunct1 % A % C %% prf3)) %%  \
 \    (iffD1 % C % D %% prf2 %% (conjunct2 % A % C %% prf3)))",

   "(iffD2 % A & C % B & D %% (cong % TYPE('T1) % TYPE('T2) % x1 % x2 % C % D %% prfT1 %% prfT2 %%  \
 \    (cong % TYPE('T3) % TYPE('T4) % op & % op & % A % B %% prfT3 %% prfT4 %%  \
 \      (HOL.refl % TYPE('T5) % op & %% prfT5) %% prf1) %% prf2) %% prf3) ==  \
 \  (conjI % A % C %%  \
 \    (iffD2 % A % B %% prf1 %% (conjunct1 % B % D %% prf3)) %%  \
 \    (iffD2 % C % D %% prf2 %% (conjunct2 % B % D %% prf3)))",

   "(cong % TYPE(bool) % TYPE(bool) % op & A % op & A % B % C %% prfb %% prfb %%  \
 \    (HOL.refl % TYPE(bool=>bool) % op & A %% prfbb)) ==  \
 \  (cong % TYPE(bool) % TYPE(bool) % op & A % op & A % B % C %% prfb %% prfb %%  \
 \    (cong % TYPE(bool) % TYPE(bool=>bool) %  \
 \      (op & :: bool=>bool=>bool) % (op & :: bool=>bool=>bool) % A % A %%  \
 \        prfb %% prfbb %%  \
 \        (HOL.refl % TYPE(bool=>bool=>bool) % (op & :: bool=>bool=>bool) %%  \
 \           (OfClass type_class % TYPE(bool=>bool=>bool))) %%  \
 \        (HOL.refl % TYPE(bool) % A %% prfb)))",

   (* | *)

   "(iffD1 % A | C % B | D %% (cong % TYPE('T1) % TYPE('T2) % x1 % x2 % C % D %% prfT1 %% prfT2 %%  \
 \    (cong % TYPE('T3) % TYPE('T4) % op | % op | % A % B %% prfT3 %% prfT4 %%  \
 \      (HOL.refl % TYPE('T5) % op | %% prfT5) %% prf1) %% prf2) %% prf3) ==  \
 \  (disjE % A % C % B | D %% prf3 %%  \
 \    (Lam H : A. disjI1 % B % D %% (iffD1 % A % B %% prf1 %% H)) %%  \
 \    (Lam H : C. disjI2 % D % B %% (iffD1 % C % D %% prf2 %% H)))",

   "(iffD2 % A | C % B | D %% (cong % TYPE('T1) % TYPE('T2) % x1 % x2 % C % D %% prfT1 %% prfT2 %%  \
 \    (cong % TYPE('T3) % TYPE('T4) % op | % op | % A % B %% prfT3 %% prfT4 %%  \
 \      (HOL.refl % TYPE('T5) % op | %% prfT5) %% prf1) %% prf2) %% prf3) ==  \
 \  (disjE % B % D % A | C %% prf3 %%  \
 \    (Lam H : B. disjI1 % A % C %% (iffD2 % A % B %% prf1 %% H)) %%  \
 \    (Lam H : D. disjI2 % C % A %% (iffD2 % C % D %% prf2 %% H)))",

   "(cong % TYPE(bool) % TYPE(bool) % op | A % op | A % B % C %% prfb %% prfb %%  \
 \    (HOL.refl % TYPE(bool=>bool) % op | A %% prfbb)) ==  \
 \  (cong % TYPE(bool) % TYPE(bool) % op | A % op | A % B % C %% prfb %% prfb %%  \
 \    (cong % TYPE(bool) % TYPE(bool=>bool) %  \
 \      (op | :: bool=>bool=>bool) % (op | :: bool=>bool=>bool) % A % A %%  \
 \        prfb %% prfbb %%  \
 \        (HOL.refl % TYPE(bool=>bool=>bool) % (op | :: bool=>bool=>bool) %%  \
 \           (OfClass type_class % TYPE(bool=>bool=>bool))) %%  \
 \        (HOL.refl % TYPE(bool) % A %% prfb)))",

   (* --> *)

   "(iffD1 % A --> C % B --> D %% (cong % TYPE('T1) % TYPE('T2) % x1 % x2 % C % D %% prfT1 %% prfT2 %%  \
 \    (cong % TYPE('T3) % TYPE('T4) % op --> % op --> % A % B %% prfT3 %% prfT4 %%  \
 \      (HOL.refl % TYPE('T5) % op --> %% prfT5) %% prf1) %% prf2) %% prf3) ==  \
 \  (impI % B % D %% (Lam H: B. iffD1 % C % D %% prf2 %%  \
 \    (mp % A % C %% prf3 %% (iffD2 % A % B %% prf1 %% H))))",

   "(iffD2 % A --> C % B --> D %% (cong % TYPE('T1) % TYPE('T2) % x1 % x2 % C % D %% prfT1 %% prfT2 %%  \
 \    (cong % TYPE('T3) % TYPE('T4) % op --> % op --> % A % B %% prfT3 %% prfT4 %%  \
 \      (HOL.refl % TYPE('T5) % op --> %% prfT5) %% prf1) %% prf2) %% prf3) ==  \
 \  (impI % A % C %% (Lam H: A. iffD2 % C % D %% prf2 %%  \
 \    (mp % B % D %% prf3 %% (iffD1 % A % B %% prf1 %% H))))",

   "(cong % TYPE(bool) % TYPE(bool) % op --> A % op --> A % B % C %% prfb %% prfb %%  \
 \    (HOL.refl % TYPE(bool=>bool) % op --> A %% prfbb)) ==  \
 \  (cong % TYPE(bool) % TYPE(bool) % op --> A % op --> A % B % C %% prfb %% prfb %%  \
 \    (cong % TYPE(bool) % TYPE(bool=>bool) %  \
 \      (op --> :: bool=>bool=>bool) % (op --> :: bool=>bool=>bool) % A % A %%  \
 \        prfb %% prfbb %%  \
 \        (HOL.refl % TYPE(bool=>bool=>bool) % (op --> :: bool=>bool=>bool) %%  \
 \           (OfClass type_class % TYPE(bool=>bool=>bool))) %%  \
 \        (HOL.refl % TYPE(bool) % A %% prfb)))",

   (* ~ *)

   "(iffD1 % ~ P % ~ Q %% (cong % TYPE('T1) % TYPE('T2) % Not % Not % P % Q %% prfT1 %% prfT2 %%  \
 \    (HOL.refl % TYPE('T3) % Not %% prfT3) %% prf1) %% prf2) ==  \
 \  (notI % Q %% (Lam H: Q.  \
 \    notE % P % False %% prf2 %% (iffD2 % P % Q %% prf1 %% H)))",

   "(iffD2 % ~ P % ~ Q %% (cong % TYPE('T1) % TYPE('T2) % Not % Not % P % Q %% prfT1 %% prfT2 %%  \
 \    (HOL.refl % TYPE('T3) % Not %% prfT3) %% prf1) %% prf2) ==  \
 \  (notI % P %% (Lam H: P.  \
 \    notE % Q % False %% prf2 %% (iffD1 % P % Q %% prf1 %% H)))",

   (* = *)

   "(iffD1 % B % D %%  \
 \    (iffD1 % A = C % B = D %% (cong % TYPE(bool) % TYPE('T1) % x1 % x2 % C % D %% prfb %% prfT1 %%  \
 \      (cong % TYPE(bool) % TYPE('T2) % op = % op = % A % B %% prfb %% prfT2 %%  \
 \        (HOL.refl % TYPE('T3) % op = %% prfT3) %% prf1) %% prf2) %% prf3) %% prf4) ==  \
 \  (iffD1 % C % D %% prf2 %%  \
 \    (iffD1 % A % C %% prf3 %% (iffD2 % A % B %% prf1 %% prf4)))",

   "(iffD2 % B % D %%  \
 \    (iffD1 % A = C % B = D %% (cong % TYPE(bool) % TYPE('T1) % x1 % x2 % C % D %% prfb %% prfT1 %%  \
 \      (cong % TYPE(bool) % TYPE('T2) % op = % op = % A % B %% prfb %% prfT2 %%  \
 \        (HOL.refl % TYPE('T3) % op = %% prfT3) %% prf1) %% prf2) %% prf3) %% prf4) ==  \
 \  (iffD1 % A % B %% prf1 %%  \
 \    (iffD2 % A % C %% prf3 %% (iffD2 % C % D %% prf2 %% prf4)))",

   "(iffD1 % A % C %%  \
 \    (iffD2 % A = C % B = D %% (cong % TYPE(bool) % TYPE('T1) % x1 % x2 % C % D %% prfb %% prfT1 %%  \
 \      (cong % TYPE(bool) % TYPE('T2) % op = % op = % A % B %% prfb %% prfT2 %%  \
 \        (HOL.refl % TYPE('T3) % op = %% prfT3) %% prf1) %% prf2) %% prf3) %% prf4)==  \
 \  (iffD2 % C % D %% prf2 %%  \
 \    (iffD1 % B % D %% prf3 %% (iffD1 % A % B %% prf1 %% prf4)))",

   "(iffD2 % A % C %%  \
 \    (iffD2 % A = C % B = D %% (cong % TYPE(bool) % TYPE('T1) % x1 % x2 % C % D %% prfb %% prfT1 %%  \
 \      (cong % TYPE(bool) % TYPE('T2) % op = % op = % A % B %% prfb %% prfT2 %%  \
 \        (HOL.refl % TYPE('T3) % op = %% prfT3) %% prf1) %% prf2) %% prf3) %% prf4) ==  \
 \  (iffD2 % A % B %% prf1 %%  \
 \    (iffD2 % B % D %% prf3 %% (iffD1 % C % D %% prf2 %% prf4)))",

   "(cong % TYPE(bool) % TYPE(bool) % op = A % op = A % B % C %% prfb %% prfb %%  \
 \    (HOL.refl % TYPE(bool=>bool) % op = A %% prfbb)) ==  \
 \  (cong % TYPE(bool) % TYPE(bool) % op = A % op = A % B % C %% prfb %% prfb %%  \
 \    (cong % TYPE(bool) % TYPE(bool=>bool) %  \
 \      (op = :: bool=>bool=>bool) % (op = :: bool=>bool=>bool) % A % A %%  \
 \        prfb %% prfbb %%  \
 \        (HOL.refl % TYPE(bool=>bool=>bool) % (op = :: bool=>bool=>bool) %%  \
 \           (OfClass type_class % TYPE(bool=>bool=>bool))) %%  \
 \        (HOL.refl % TYPE(bool) % A %% prfb)))",

   (** transitivity, reflexivity, and symmetry **)

   "(iffD1 % A % C %% (HOL.trans % TYPE(bool) % A % B % C %% prfb %% prf1 %% prf2) %% prf3) ==  \
 \  (iffD1 % B % C %% prf2 %% (iffD1 % A % B %% prf1 %% prf3))",

   "(iffD2 % A % C %% (HOL.trans % TYPE(bool) % A % B % C %% prfb %% prf1 %% prf2) %% prf3) ==  \
 \  (iffD2 % A % B %% prf1 %% (iffD2 % B % C %% prf2 %% prf3))",

   "(iffD1 % A % A %% (HOL.refl % TYPE(bool) % A %% prfb) %% prf) == prf",

   "(iffD2 % A % A %% (HOL.refl % TYPE(bool) % A %% prfb) %% prf) == prf",

   "(iffD1 % A % B %% (sym % TYPE(bool) % B % A %% prfb %% prf)) == (iffD2 % B % A %% prf)",

   "(iffD2 % A % B %% (sym % TYPE(bool) % B % A %% prfb %% prf)) == (iffD1 % B % A %% prf)",

   (** normalization of HOL proofs **)

   "(mp % A % B %% (impI % A % B %% prf)) == prf",

   "(impI % A % B %% (mp % A % B %% prf)) == prf",

   "(spec % TYPE('a) % P % x %% prfa %% (allI % TYPE('a) % P %% prfa %% prf)) == prf % x",

   "(allI % TYPE('a) % P %% prfa %% (Lam x::'a. spec % TYPE('a) % P % x %% prfa %% prf)) == prf",

   "(exE % TYPE('a) % P % Q %% prfa %% (exI % TYPE('a) % P % x %% prfa %% prf1) %% prf2) == (prf2 % x %% prf1)",

   "(exE % TYPE('a) % P % Q %% prfa %% prf %% (exI % TYPE('a) % P %% prfa)) == prf",

   "(disjE % P % Q % R %% (disjI1 % P % Q %% prf1) %% prf2 %% prf3) == (prf2 %% prf1)",

   "(disjE % P % Q % R %% (disjI2 % Q % P %% prf1) %% prf2 %% prf3) == (prf3 %% prf1)",

   "(conjunct1 % P % Q %% (conjI % P % Q %% prf1 %% prf2)) == prf1",

   "(conjunct2 % P % Q %% (conjI % P % Q %% prf1 %% prf2)) == prf2",

   "(iffD1 % A % B %% (iffI % A % B %% prf1 %% prf2)) == prf1",

   "(iffD2 % A % B %% (iffI % A % B %% prf1 %% prf2)) == prf2"];


(** Replace congruence rules by substitution rules **)

fun strip_cong ps (PThm (_, (("HOL.cong", _, _), _)) % _ % _ % SOME x % SOME y %%
      prfa %% prfT %% prf1 %% prf2) = strip_cong (((x, y), (prf2, prfa)) :: ps) prf1
  | strip_cong ps (PThm (_, (("HOL.refl", _, _), _)) % SOME f %% _) = SOME (f, ps)
  | strip_cong _ _ = NONE;

val subst_prf = fst (Proofterm.strip_combt (fst (Proofterm.strip_combP (Thm.proof_of subst))));
val sym_prf = fst (Proofterm.strip_combt (fst (Proofterm.strip_combP (Thm.proof_of sym))));

fun make_subst Ts prf xs (_, []) = prf
  | make_subst Ts prf xs (f, ((x, y), (prf', clprf)) :: ps) =
      let val T = fastype_of1 (Ts, x)
      in if x aconv y then make_subst Ts prf (xs @ [x]) (f, ps)
        else Proofterm.change_type (SOME [T]) subst_prf %> x %> y %>
          Abs ("z", T, list_comb (incr_boundvars 1 f,
            map (incr_boundvars 1) xs @ Bound 0 ::
            map (incr_boundvars 1 o snd o fst) ps)) %% clprf %% prf' %%
          make_subst Ts prf (xs @ [x]) (f, ps)
      end;

fun make_sym Ts ((x, y), (prf, clprf)) =
  ((y, x),
    (Proofterm.change_type (SOME [fastype_of1 (Ts, x)]) sym_prf %> x %> y %% clprf %% prf, clprf));

fun mk_AbsP P t = AbsP ("H", Option.map HOLogic.mk_Trueprop P, t);

fun elim_cong_aux Ts (PThm (_, (("HOL.iffD1", _, _), _)) % _ % _ %% prf1 %% prf2) =
      Option.map (make_subst Ts prf2 []) (strip_cong [] prf1)
  | elim_cong_aux Ts (PThm (_, (("HOL.iffD1", _, _), _)) % P % _ %% prf) =
      Option.map (mk_AbsP P o make_subst Ts (PBound 0) [])
        (strip_cong [] (Proofterm.incr_pboundvars 1 0 prf))
  | elim_cong_aux Ts (PThm (_, (("HOL.iffD2", _, _), _)) % _ % _ %% prf1 %% prf2) =
      Option.map (make_subst Ts prf2 [] o
        apsnd (map (make_sym Ts))) (strip_cong [] prf1)
  | elim_cong_aux Ts (PThm (_, (("HOL.iffD2", _, _), _)) % _ % P %% prf) =
      Option.map (mk_AbsP P o make_subst Ts (PBound 0) [] o
        apsnd (map (make_sym Ts))) (strip_cong [] (Proofterm.incr_pboundvars 1 0 prf))
  | elim_cong_aux _ _ = NONE;

fun elim_cong Ts hs prf = Option.map (rpair Proofterm.no_skel) (elim_cong_aux Ts prf);

end;
