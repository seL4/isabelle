(*  Title:      HOL/Tools/rewrite_hol_proof.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Rewrite rules for HOL proofs
*)

signature REWRITE_HOL_PROOF =
sig
  val rews: (Proofterm.proof * Proofterm.proof) list
  val elim_cong: typ list -> Proofterm.proof -> Proofterm.proof option
end;

structure RewriteHOLProof : REWRITE_HOL_PROOF =
struct

open Proofterm;

val rews = map (pairself (ProofSyntax.proof_of_term (the_context ()) Symtab.empty true) o
    Logic.dest_equals o Logic.varify o ProofSyntax.read_term (the_context ()) propT)

  (** eliminate meta-equality rules **)

  ["(equal_elim % x1 % x2 %% \
 \    (combination % TYPE('T1) % TYPE('T2) % Trueprop % x3 % A % B %%  \
 \      (axm.reflexive % TYPE('T3) % x4) %% prf1) %% prf2) ==  \
 \  (iffD1 % A % B %%  \
 \    (meta_eq_to_obj_eq % TYPE(bool) % A % B %% prf1) %% prf2)",

   "(equal_elim % x1 % x2 %% (axm.symmetric % TYPE('T1) % x3 % x4 %%  \
 \    (combination % TYPE('T2) % TYPE('T3) % Trueprop % x5 % A % B %%  \
 \      (axm.reflexive % TYPE('T4) % x6) %% prf1)) %% prf2) ==  \
 \  (iffD2 % A % B %%  \
 \    (meta_eq_to_obj_eq % TYPE(bool) % A % B %% prf1) %% prf2)",

   "(meta_eq_to_obj_eq % TYPE('U) % x1 % x2 %%  \
 \    (combination % TYPE('U) % TYPE('T) % f % g % x % y %% prf1 %% prf2)) ==  \
 \  (cong % TYPE('U) % TYPE('T) % f % g % x % y %%  \
 \    (meta_eq_to_obj_eq % TYPE('T => 'U) % f % g %% prf1) %%  \
 \    (meta_eq_to_obj_eq % TYPE('T) % x % y %% prf2))",

   "(meta_eq_to_obj_eq % TYPE('T) % x1 % x2 %%  \
 \    (axm.transitive % TYPE('T) % x % y % z %% prf1 %% prf2)) ==  \
 \  (trans % TYPE('T) % x % y % z %%  \
 \    (meta_eq_to_obj_eq % TYPE('T) % x % y %% prf1) %%  \
 \    (meta_eq_to_obj_eq % TYPE('T) % y % z %% prf2))",

   "(meta_eq_to_obj_eq % TYPE('T) % x % x %% (axm.reflexive % TYPE('T) % x)) ==  \
 \  (refl % TYPE('T) % x)",

   "(meta_eq_to_obj_eq % TYPE('T) % x % y %%  \
 \    (axm.symmetric % TYPE('T) % x % y %% prf)) ==  \
 \  (sym % TYPE('T) % x % y %% (meta_eq_to_obj_eq % TYPE('T) % x % y %% prf))",

   "(meta_eq_to_obj_eq % TYPE('T => 'U) % x1 % x2 %%  \
 \    (abstract_rule % TYPE('U) % TYPE('T) % f % g %% prf)) ==  \
 \  (ext % TYPE('U) % TYPE('T) % f % g %%  \
 \    (Lam (x::'T). meta_eq_to_obj_eq % TYPE('U) % f x % g x %% (prf % x)))",

   "(meta_eq_to_obj_eq % TYPE('T) % x % y %%  \
 \    (eq_reflection % TYPE('T) % x % y %% prf)) == prf",

   "(meta_eq_to_obj_eq % TYPE('T1) % x1 % x2 %% (equal_elim % x3 % x4 %%  \
 \    (combination % TYPE(prop) % TYPE('T) % x7 % x8 % C % D %%  \
 \      (combination % TYPE('T3) % TYPE('T) % op == % op == % A % B %%  \
 \        (axm.reflexive % TYPE('T4) % op ==) %% prf1) %% prf2) %% prf3)) ==  \
 \  (iffD1 % A = C % B = D %%  \
 \    (cong % TYPE(bool) % TYPE('T::type) % op = A % op = B % C % D %%  \
 \      (cong % TYPE('T=>bool) % TYPE('T) %  \
 \        (op = :: 'T=>'T=>bool) % (op = :: 'T=>'T=>bool) % A % B %%  \
 \        (refl % TYPE('T=>'T=>bool) % (op = :: 'T=>'T=>bool)) %%  \
 \        (meta_eq_to_obj_eq % TYPE('T) % A % B %% prf1)) %%  \
 \      (meta_eq_to_obj_eq % TYPE('T) % C % D %% prf2)) %%  \
 \    (meta_eq_to_obj_eq % TYPE('T) % C % D %% prf3))",

   "(meta_eq_to_obj_eq % TYPE('T1) % x1 % x2 %% (equal_elim % x3 % x4 %%  \
 \    (axm.symmetric % TYPE('T2) % x5 % x6 %%  \
 \      (combination % TYPE(prop) % TYPE('T) % x7 % x8 % C % D %%  \
 \        (combination % TYPE('T3) % TYPE('T) % op == % op == % A % B %%  \
 \          (axm.reflexive % TYPE('T4) % op ==) %% prf1) %% prf2)) %% prf3)) ==  \
 \  (iffD2 % A = C % B = D %%  \
 \    (cong % TYPE(bool) % TYPE('T::type) % op = A % op = B % C % D %%  \
 \      (cong % TYPE('T=>bool) % TYPE('T) %  \
 \        (op = :: 'T=>'T=>bool) % (op = :: 'T=>'T=>bool) % A % B %%  \
 \        (refl % TYPE('T=>'T=>bool) % (op = :: 'T=>'T=>bool)) %%  \
 \        (meta_eq_to_obj_eq % TYPE('T) % A % B %% prf1)) %%  \
 \      (meta_eq_to_obj_eq % TYPE('T) % C % D %% prf2)) %%  \
 \    (meta_eq_to_obj_eq % TYPE('T) % C % D %% prf3))",

   (** rewriting on bool: insert proper congruence rules for logical connectives **)

   (* All *)

   "(iffD1 % All P % All Q %% (cong % TYPE('T1) % TYPE('T2) % All % All % P % Q %%  \
 \    (refl % TYPE('T3) % x1) %% (ext % TYPE(bool) % TYPE('a) % x2 % x3 %% prf)) %% prf') ==  \
 \  (allI % TYPE('a) % Q %%  \
 \    (Lam x.  \
 \        iffD1 % P x % Q x %% (prf % x) %%  \
 \         (spec % TYPE('a) % P % x %% prf')))",

   "(iffD2 % All P % All Q %% (cong % TYPE('T1) % TYPE('T2) % All % All % P % Q %%  \
 \    (refl % TYPE('T3) % x1) %% (ext % TYPE(bool) % TYPE('a) % x2 % x3 %% prf)) %% prf') ==  \
 \  (allI % TYPE('a) % P %%  \
 \    (Lam x.  \
 \        iffD2 % P x % Q x %% (prf % x) %%  \
 \         (spec % TYPE('a) % ?Q % x %% prf')))",

   (* Ex *)

   "(iffD1 % Ex P % Ex Q %% (cong % TYPE('T1) % TYPE('T2) % Ex % Ex % P % Q %%  \
 \    (refl % TYPE('T3) % x1) %% (ext % TYPE(bool) % TYPE('a) % x2 % x3 %% prf)) %% prf') ==  \
 \  (exE % TYPE('a) % P % EX x. Q x %% prf' %%  \
 \    (Lam x H : P x.  \
 \        exI % TYPE('a) % Q % x %%  \
 \         (iffD1 % P x % Q x %% (prf % x) %% H)))",

   "(iffD2 % Ex P % Ex Q %% (cong % TYPE('T1) % TYPE('T2) % Ex % Ex % P % Q %%  \
 \    (refl % TYPE('T3) % x1) %% (ext % TYPE(bool) % TYPE('a) % x2 % x3 %% prf)) %% prf') ==  \
 \  (exE % TYPE('a) % Q % EX x. P x %% prf' %%  \
 \    (Lam x H : Q x.  \
 \        exI % TYPE('a) % P % x %%  \
 \         (iffD2 % P x % Q x %% (prf % x) %% H)))",

   (* & *)

   "(iffD1 % A & C % B & D %% (cong % TYPE('T1) % TYPE('T2) % x1 % x2 % C % D %%  \
 \    (cong % TYPE('T3) % TYPE('T4) % op & % op & % A % B %%  \
 \      (refl % TYPE('T5) % op &) %% prf1) %% prf2) %% prf3) ==  \
 \  (conjI % B % D %%  \
 \    (iffD1 % A % B %% prf1 %% (conjunct1 % A % C %% prf3)) %%  \
 \    (iffD1 % C % D %% prf2 %% (conjunct2 % A % C %% prf3)))",

   "(iffD2 % A & C % B & D %% (cong % TYPE('T1) % TYPE('T2) % x1 % x2 % C % D %%  \
 \    (cong % TYPE('T3) % TYPE('T4) % op & % op & % A % B %%  \
 \      (refl % TYPE('T5) % op &) %% prf1) %% prf2) %% prf3) ==  \
 \  (conjI % A % C %%  \
 \    (iffD2 % A % B %% prf1 %% (conjunct1 % B % D %% prf3)) %%  \
 \    (iffD2 % C % D %% prf2 %% (conjunct2 % B % D %% prf3)))",

   (* | *)

   "(iffD1 % A | C % B | D %% (cong % TYPE('T1) % TYPE('T2) % x1 % x2 % C % D %%  \
 \    (cong % TYPE('T3) % TYPE('T4) % op | % op | % A % B %%  \
 \      (refl % TYPE('T5) % op | ) %% prf1) %% prf2) %% prf3) ==  \
 \  (disjE % A % C % B | D %% prf3 %%  \
 \    (Lam H : A. disjI1 % B % D %% (iffD1 % A % B %% prf1 %% H)) %%  \
 \    (Lam H : C. disjI2 % D % B %% (iffD1 % C % D %% prf2 %% H)))",

   "(iffD2 % A | C % B | D %% (cong % TYPE('T1) % TYPE('T2) % x1 % x2 % C % D %%  \
 \    (cong % TYPE('T3) % TYPE('T4) % op | % op | % A % B %%  \
 \      (refl % TYPE('T5) % op | ) %% prf1) %% prf2) %% prf3) ==  \
 \  (disjE % B % D % A | C %% prf3 %%  \
 \    (Lam H : B. disjI1 % A % C %% (iffD2 % A % B %% prf1 %% H)) %%  \
 \    (Lam H : D. disjI2 % C % A %% (iffD2 % C % D %% prf2 %% H)))",

   (* --> *)

   "(iffD1 % A --> C % B --> D %% (cong % TYPE('T1) % TYPE('T2) % x1 % x2 % C % D %%  \
 \    (cong % TYPE('T3) % TYPE('T4) % op --> % op --> % A % B %%  \
 \      (refl % TYPE('T5) % op --> ) %% prf1) %% prf2) %% prf3) ==  \
 \  (impI % B % D %% (Lam H: B. iffD1 % C % D %% prf2 %%  \
 \    (mp % A % C %% prf3 %% (iffD2 % A % B %% prf1 %% H))))",

   "(iffD2 % A --> C % B --> D %% (cong % TYPE('T1) % TYPE('T2) % x1 % x2 % C % D %%  \
 \    (cong % TYPE('T3) % TYPE('T4) % op --> % op --> % A % B %%  \
 \      (refl % TYPE('T5) % op --> ) %% prf1) %% prf2) %% prf3) ==  \
 \  (impI % A % C %% (Lam H: A. iffD2 % C % D %% prf2 %%  \
 \    (mp % B % D %% prf3 %% (iffD1 % A % B %% prf1 %% H))))",

   (* ~ *)

   "(iffD1 % ~ P % ~ Q %% (cong % TYPE('T1) % TYPE('T2) % Not % Not % P % Q %%  \
 \    (refl % TYPE('T3) % Not) %% prf1) %% prf2) ==  \
 \  (notI % Q %% (Lam H: Q.  \
 \    notE % P % False %% prf2 %% (iffD2 % P % Q %% prf1 %% H)))",

   "(iffD2 % ~ P % ~ Q %% (cong % TYPE('T1) % TYPE('T2) % Not % Not % P % Q %%  \
 \    (refl % TYPE('T3) % Not) %% prf1) %% prf2) ==  \
 \  (notI % P %% (Lam H: P.  \
 \    notE % Q % False %% prf2 %% (iffD1 % P % Q %% prf1 %% H)))",

   (* = *)

   "(iffD1 % B % D %%  \
 \    (iffD1 % A = C % B = D %% (cong % TYPE('T1) % TYPE(bool) % x1 % x2 % C % D %%  \
 \      (cong % TYPE('T2) % TYPE(bool) % op = % op = % A % B %%  \
 \        (refl % TYPE('T3) % op =) %% prf1) %% prf2) %% prf3) %% prf4) ==  \
 \  (iffD1 % C % D %% prf2 %%  \
 \    (iffD1 % A % C %% prf3 %% (iffD2 % A % B %% prf1 %% prf4)))",

   "(iffD2 % B % D %%  \
 \    (iffD1 % A = C % B = D %% (cong % TYPE('T1) % TYPE(bool) % x1 % x2 % C % D %%  \
 \      (cong % TYPE('T2) % TYPE(bool) % op = % op = % A % B %%  \
 \        (refl % TYPE('T3) % op =) %% prf1) %% prf2) %% prf3) %% prf4) ==  \
 \  (iffD1 % A % B %% prf1 %%  \
 \    (iffD2 % A % C %% prf3 %% (iffD2 % C % D %% prf2 %% prf4)))",

   "(iffD1 % A % C %%  \
 \    (iffD2 % A = C % B = D %% (cong % TYPE('T1) % TYPE(bool) % x1 % x2 % C % D %%  \
 \      (cong % TYPE('T2) % TYPE(bool) % op = % op = % A % B %%  \
 \        (refl % TYPE('T3) % op =) %% prf1) %% prf2) %% prf3) %% prf4)==  \
 \  (iffD2 % C % D %% prf2 %%  \
 \    (iffD1 % B % D %% prf3 %% (iffD1 % A % B %% prf1 %% prf4)))",

   "(iffD2 % A % C %%  \
 \    (iffD2 % A = C % B = D %% (cong % TYPE('T1) % TYPE(bool) % x1 % x2 % C % D %%  \
 \      (cong % TYPE('T2) % TYPE(bool) % op = % op = % A % B %%  \
 \        (refl % TYPE('T3) % op =) %% prf1) %% prf2) %% prf3) %% prf4) ==  \
 \  (iffD2 % A % B %% prf1 %%  \
 \    (iffD2 % B % D %% prf3 %% (iffD1 % C % D %% prf2 %% prf4)))",

   "(cong % TYPE(bool) % TYPE(bool) % op = A % op = A % B % C %%  \
 \    (refl % TYPE(bool) % op = A)) ==  \
 \  (cong % TYPE(bool) % TYPE(bool) % op = A % op = A % B % C %%  \
 \    (cong % TYPE(bool=>bool) % TYPE(bool) %  \
 \      (op = :: bool=>bool=>bool) % (op = :: bool=>bool=>bool) % A % A %%  \
 \        (refl % TYPE(bool=>bool=>bool) % (op = :: bool=>bool=>bool)) %%  \
 \        (refl % TYPE(bool) % A % A)))",

   "(iffD1 % A % C %% (trans % TYPE(bool) % A % B % C %% prf1 %% prf2) %% prf3) ==  \
 \  (iffD1 % B % C %% prf2 %% (iffD1 % A % B %% prf1 %% prf3))",

   "(iffD2 % A % C %% (trans % TYPE(bool) % A % B % C %% prf1 %% prf2) %% prf3) ==  \
 \  (iffD2 % A % B %% prf1 %% (iffD2 % B % C %% prf2 %% prf3))",

   "(iffD1 % A % A %% (refl % TYPE(bool) % A) %% prf) == prf",

   "(iffD2 % A % A %% (refl % TYPE(bool) % A) %% prf) == prf",

   (** normalization of HOL proofs **)

   "(mp % A % B %% (impI % A % B %% prf)) == prf",

   "(impI % A % B %% (mp % A % B %% prf)) == prf",

   "(spec % TYPE('a) % P % x %% (allI % TYPE('a) % P %% prf)) == prf % x",

   "(allI % TYPE('a) % P %% (Lam x::'a. spec % TYPE('a) % P % x %% prf)) == prf",

   "(disjE % P % Q % R %% (disjI1 % P % Q %% prf1) %% prf2 %% prf3) == (prf2 %% prf1)",

   "(disjE % P % Q % R %% (disjI2 % Q % P %% prf1) %% prf2 %% prf3) == (prf3 %% prf1)",

   "(conjunct1 % P % Q %% (conjI % P % Q %% prf1 %% prf2)) == prf1",

   "(conjunct2 % P % Q %% (conjI % P % Q %% prf1 %% prf2)) == prf2",

   "(iffD1 % A % B %% (iffI % A % B %% prf1 %% prf2)) == prf1",

   "(iffD2 % A % B %% (iffI % A % B %% prf1 %% prf2)) == prf2"];


(** Replace congruence rules by substitution rules **)

fun strip_cong ps (PThm (("HOL.cong", _), _, _, _) % _ % _ % Some x % Some y %%
      prf1 %% prf2) = strip_cong (((x, y), prf2) :: ps) prf1
  | strip_cong ps (PThm (("HOL.refl", _), _, _, _) % Some f) = Some (f, ps)
  | strip_cong _ _ = None;

val subst_prf = fst (strip_combt (#2 (#der (rep_thm subst))));
val sym_prf = fst (strip_combt (#2 (#der (rep_thm sym))));

fun make_subst Ts prf xs (_, []) = prf
  | make_subst Ts prf xs (f, ((x, y), prf') :: ps) =
      let val T = fastype_of1 (Ts, x)
      in if x aconv y then make_subst Ts prf (xs @ [x]) (f, ps)
        else change_type (Some [T]) subst_prf %> x %> y %>
          Abs ("z", T, list_comb (incr_boundvars 1 f,
            map (incr_boundvars 1) xs @ Bound 0 ::
            map (incr_boundvars 1 o snd o fst) ps)) %% prf' %%
          make_subst Ts prf (xs @ [x]) (f, ps)
      end;

fun make_sym Ts ((x, y), prf) =
  ((y, x), change_type (Some [fastype_of1 (Ts, x)]) sym_prf %> x %> y %% prf);

fun elim_cong Ts (PThm (("HOL.iffD1", _), _, _, _) % _ % _ %% prf1 %% prf2) =
      apsome (make_subst Ts prf2 []) (strip_cong [] prf1)
  | elim_cong Ts (PThm (("HOL.iffD2", _), _, _, _) % _ % _ %% prf1 %% prf2) =
      apsome (make_subst Ts prf2 [] o
        apsnd (map (make_sym Ts))) (strip_cong [] prf1)
  | elim_cong _ _ = None;

end;
