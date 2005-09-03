
theory ex
imports Cube
begin

text {*
  Examples taken from:

  H. Barendregt. Introduction to Generalised Type Systems.
  J. Functional Programming.
*}

method_setup depth_solve = {*
  Method.thms_args (fn thms => Method.METHOD (fn facts =>
  (DEPTH_SOLVE (HEADGOAL (ares_tac (facts @ thms))))))
*} ""

method_setup depth_solve1 = {*
  Method.thms_args (fn thms => Method.METHOD (fn facts =>
  (DEPTH_SOLVE_1 (HEADGOAL (ares_tac (facts @ thms))))))
*} ""

ML {*
local val strip_b = thm "strip_b" and strip_s = thm "strip_s" in
fun strip_asms_tac thms  i =
  REPEAT (resolve_tac [strip_b, strip_s] i THEN DEPTH_SOLVE_1 (ares_tac thms i))
end
*}


subsection {* Simple types *}

lemma "A:* |- A->A : ?T"
  by (depth_solve rules)

lemma "A:* |- Lam a:A. a : ?T"
  by (depth_solve rules)

lemma "A:* B:* b:B |- Lam x:A. b : ?T"
  by (depth_solve rules)

lemma "A:* b:A |- (Lam a:A. a)^b: ?T"
  by (depth_solve rules)

lemma "A:* B:* c:A b:B |- (Lam x:A. b)^ c: ?T"
  by (depth_solve rules)

lemma "A:* B:* |- Lam a:A. Lam b:B. a : ?T"
  by (depth_solve rules)


subsection {* Second-order types *}

lemma (in L2) "|- Lam A:*. Lam a:A. a : ?T"
  by (depth_solve rules)

lemma (in L2) "A:* |- (Lam B:*.Lam b:B. b)^A : ?T"
  by (depth_solve rules)

lemma (in L2) "A:* b:A |- (Lam B:*.Lam b:B. b) ^ A ^ b: ?T"
  by (depth_solve rules)

lemma (in L2) "|- Lam B:*.Lam a:(Pi A:*.A).a ^ ((Pi A:*.A)->B) ^ a: ?T"
  by (depth_solve rules)


subsection {* Weakly higher-order propositional logic *}

lemma (in Lomega) "|- Lam A:*.A->A : ?T"
  by (depth_solve rules)

lemma (in Lomega) "B:* |- (Lam A:*.A->A) ^ B : ?T"
  by (depth_solve rules)

lemma (in Lomega) "B:* b:B |- (Lam y:B. b): ?T"
  by (depth_solve rules)

lemma (in Lomega) "A:* F:*->* |- F^(F^A): ?T"
  by (depth_solve rules)

lemma (in Lomega) "A:* |- Lam F:*->*.F^(F^A): ?T"
  by (depth_solve rules)


subsection {* LP *}

lemma (in LP) "A:* |- A -> * : ?T"
  by (depth_solve rules)

lemma (in LP) "A:* P:A->* a:A |- P^a: ?T"
  by (depth_solve rules)

lemma (in LP) "A:* P:A->A->* a:A |- Pi a:A. P^a^a: ?T"
  by (depth_solve rules)

lemma (in LP) "A:* P:A->* Q:A->* |- Pi a:A. P^a -> Q^a: ?T"
  by (depth_solve rules)

lemma (in LP) "A:* P:A->* |- Pi a:A. P^a -> P^a: ?T"
  by (depth_solve rules)

lemma (in LP) "A:* P:A->* |- Lam a:A. Lam x:P^a. x: ?T"
  by (depth_solve rules)

lemma (in LP) "A:* P:A->* Q:* |- (Pi a:A. P^a->Q) -> (Pi a:A. P^a) -> Q : ?T"
  by (depth_solve rules)

lemma (in LP) "A:* P:A->* Q:* a0:A |-
        Lam x:Pi a:A. P^a->Q. Lam y:Pi a:A. P^a. x^a0^(y^a0): ?T"
  by (depth_solve rules)


subsection {* Omega-order types *}

lemma (in L2) "A:* B:* |- Pi C:*.(A->B->C)->C : ?T"
  by (depth_solve rules)

lemma (in Lomega2) "|- Lam A:*.Lam B:*.Pi C:*.(A->B->C)->C : ?T"
  by (depth_solve rules)

lemma (in Lomega2) "|- Lam A:*.Lam B:*.Lam x:A. Lam y:B. x : ?T"
  by (depth_solve rules)

lemma (in Lomega2) "A:* B:* |- ?p : (A->B) -> ((B->Pi P:*.P)->(A->Pi P:*.P))"
  apply (tactic {* strip_asms_tac (thms "rules") 1 *})
  apply (rule lam_ss)
    apply (depth_solve1 rules)
   prefer 2
   apply (depth_solve1 rules)
  apply (rule lam_ss)
    apply (depth_solve1 rules)
   prefer 2
   apply (depth_solve1 rules)
  apply (rule lam_ss)
    apply assumption
   prefer 2
   apply (depth_solve1 rules)
  apply (erule pi_elim)
   apply assumption
  apply (erule pi_elim)
   apply assumption
  apply assumption
  done


subsection {* Second-order Predicate Logic *}

lemma (in LP2) "A:* P:A->* |- Lam a:A. P^a->(Pi A:*.A) : ?T"
  by (depth_solve rules)

lemma (in LP2) "A:* P:A->A->* |-
    (Pi a:A. Pi b:A. P^a^b->P^b^a->Pi P:*.P) -> Pi a:A. P^a^a->Pi P:*.P : ?T"
  by (depth_solve rules)

lemma (in LP2) "A:* P:A->A->* |-
    ?p: (Pi a:A. Pi b:A. P^a^b->P^b^a->Pi P:*.P) -> Pi a:A. P^a^a->Pi P:*.P"
  -- {* Antisymmetry implies irreflexivity: *}
  apply (tactic {* strip_asms_tac (thms "rules") 1 *})
  apply (rule lam_ss)
    apply (depth_solve1 rules)
   prefer 2
   apply (depth_solve1 rules)
  apply (rule lam_ss)
    apply assumption
   prefer 2
   apply (depth_solve1 rules)
  apply (rule lam_ss)
    apply (depth_solve1 rules)
   prefer 2
   apply (depth_solve1 rules)
  apply (erule pi_elim, assumption, assumption?)+
  done


subsection {* LPomega *}

lemma (in LPomega) "A:* |- Lam P:A->A->*.Lam a:A. P^a^a : ?T"
  by (depth_solve rules)

lemma (in LPomega) "|- Lam A:*.Lam P:A->A->*.Lam a:A. P^a^a : ?T"
  by (depth_solve rules)


subsection {* Constructions *}

lemma (in CC) "|- Lam A:*.Lam P:A->*.Lam a:A. P^a->Pi P:*.P: ?T"
  by (depth_solve rules)

lemma (in CC) "|- Lam A:*.Lam P:A->*.Pi a:A. P^a: ?T"
  by (depth_solve rules)

lemma (in CC) "A:* P:A->* a:A |- ?p : (Pi a:A. P^a)->P^a"
  apply (tactic {* strip_asms_tac (thms "rules") 1 *})
  apply (rule lam_ss)
    apply (depth_solve1 rules)
   prefer 2
   apply (depth_solve1 rules)
  apply (erule pi_elim, assumption, assumption)
  done


subsection {* Some random examples *}

lemma (in LP2) "A:* c:A f:A->A |-
    Lam a:A. Pi P:A->*.P^c -> (Pi x:A. P^x->P^(f^x)) -> P^a : ?T"
  by (depth_solve rules)

lemma (in CC) "Lam A:*.Lam c:A. Lam f:A->A.
    Lam a:A. Pi P:A->*.P^c -> (Pi x:A. P^x->P^(f^x)) -> P^a : ?T"
  by (depth_solve rules)

lemma (in LP2)
  "A:* a:A b:A |- ?p: (Pi P:A->*.P^a->P^b) -> (Pi P:A->*.P^b->P^a)"
  -- {* Symmetry of Leibnitz equality *}
  apply (tactic {* strip_asms_tac (thms "rules") 1 *})
  apply (rule lam_ss)
    apply (depth_solve1 rules)
   prefer 2
   apply (depth_solve1 rules)
  apply (erule_tac a = "Lam x:A. Pi Q:A->*.Q^x->Q^a" in pi_elim)
   apply (depth_solve1 rules)
  apply (unfold beta)
  apply (erule imp_elim)
   apply (rule lam_bs)
     apply (depth_solve1 rules)
    prefer 2
    apply (depth_solve1 rules)
   apply (rule lam_ss)
     apply (depth_solve1 rules)
    prefer 2
    apply (depth_solve1 rules)
   apply assumption
  apply assumption
  done

end
