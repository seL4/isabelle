header {* Lambda Cube Examples *}

theory Example
imports Cube
begin

text {*
  Examples taken from:

  H. Barendregt. Introduction to Generalised Type Systems.
  J. Functional Programming.
*}

method_setup depth_solve = {*
  Attrib.thms >> (fn thms => K (METHOD (fn facts =>
    (DEPTH_SOLVE (HEADGOAL (ares_tac (facts @ thms)))))))
*}

method_setup depth_solve1 = {*
  Attrib.thms >> (fn thms => K (METHOD (fn facts =>
    (DEPTH_SOLVE_1 (HEADGOAL (ares_tac (facts @ thms)))))))
*}

method_setup strip_asms =  {*
  Attrib.thms >> (fn thms => K (METHOD (fn facts =>
    REPEAT (resolve_tac [@{thm strip_b}, @{thm strip_s}] 1 THEN
    DEPTH_SOLVE_1 (ares_tac (facts @ thms) 1)))))
*}


subsection {* Simple types *}

schematic_lemma "A:* \<turnstile> A\<rightarrow>A : ?T"
  by (depth_solve rules)

schematic_lemma "A:* \<turnstile> \<Lambda> a:A. a : ?T"
  by (depth_solve rules)

schematic_lemma "A:* B:* b:B \<turnstile> \<Lambda> x:A. b : ?T"
  by (depth_solve rules)

schematic_lemma "A:* b:A \<turnstile> (\<Lambda> a:A. a)^b: ?T"
  by (depth_solve rules)

schematic_lemma "A:* B:* c:A b:B \<turnstile> (\<Lambda> x:A. b)^ c: ?T"
  by (depth_solve rules)

schematic_lemma "A:* B:* \<turnstile> \<Lambda> a:A. \<Lambda> b:B. a : ?T"
  by (depth_solve rules)


subsection {* Second-order types *}

schematic_lemma (in L2) "\<turnstile> \<Lambda> A:*. \<Lambda> a:A. a : ?T"
  by (depth_solve rules)

schematic_lemma (in L2) "A:* \<turnstile> (\<Lambda> B:*.\<Lambda> b:B. b)^A : ?T"
  by (depth_solve rules)

schematic_lemma (in L2) "A:* b:A \<turnstile> (\<Lambda> B:*.\<Lambda> b:B. b) ^ A ^ b: ?T"
  by (depth_solve rules)

schematic_lemma (in L2) "\<turnstile> \<Lambda> B:*.\<Lambda> a:(\<Pi> A:*.A).a ^ ((\<Pi> A:*.A)\<rightarrow>B) ^ a: ?T"
  by (depth_solve rules)


subsection {* Weakly higher-order propositional logic *}

schematic_lemma (in Lomega) "\<turnstile> \<Lambda> A:*.A\<rightarrow>A : ?T"
  by (depth_solve rules)

schematic_lemma (in Lomega) "B:* \<turnstile> (\<Lambda> A:*.A\<rightarrow>A) ^ B : ?T"
  by (depth_solve rules)

schematic_lemma (in Lomega) "B:* b:B \<turnstile> (\<Lambda> y:B. b): ?T"
  by (depth_solve rules)

schematic_lemma (in Lomega) "A:* F:*\<rightarrow>* \<turnstile> F^(F^A): ?T"
  by (depth_solve rules)

schematic_lemma (in Lomega) "A:* \<turnstile> \<Lambda> F:*\<rightarrow>*.F^(F^A): ?T"
  by (depth_solve rules)


subsection {* LP *}

schematic_lemma (in LP) "A:* \<turnstile> A \<rightarrow> * : ?T"
  by (depth_solve rules)

schematic_lemma (in LP) "A:* P:A\<rightarrow>* a:A \<turnstile> P^a: ?T"
  by (depth_solve rules)

schematic_lemma (in LP) "A:* P:A\<rightarrow>A\<rightarrow>* a:A \<turnstile> \<Pi> a:A. P^a^a: ?T"
  by (depth_solve rules)

schematic_lemma (in LP) "A:* P:A\<rightarrow>* Q:A\<rightarrow>* \<turnstile> \<Pi> a:A. P^a \<rightarrow> Q^a: ?T"
  by (depth_solve rules)

schematic_lemma (in LP) "A:* P:A\<rightarrow>* \<turnstile> \<Pi> a:A. P^a \<rightarrow> P^a: ?T"
  by (depth_solve rules)

schematic_lemma (in LP) "A:* P:A\<rightarrow>* \<turnstile> \<Lambda> a:A. \<Lambda> x:P^a. x: ?T"
  by (depth_solve rules)

schematic_lemma (in LP) "A:* P:A\<rightarrow>* Q:* \<turnstile> (\<Pi> a:A. P^a\<rightarrow>Q) \<rightarrow> (\<Pi> a:A. P^a) \<rightarrow> Q : ?T"
  by (depth_solve rules)

schematic_lemma (in LP) "A:* P:A\<rightarrow>* Q:* a0:A \<turnstile>
        \<Lambda> x:\<Pi> a:A. P^a\<rightarrow>Q. \<Lambda> y:\<Pi> a:A. P^a. x^a0^(y^a0): ?T"
  by (depth_solve rules)


subsection {* Omega-order types *}

schematic_lemma (in L2) "A:* B:* \<turnstile> \<Pi> C:*.(A\<rightarrow>B\<rightarrow>C)\<rightarrow>C : ?T"
  by (depth_solve rules)

schematic_lemma (in Lomega2) "\<turnstile> \<Lambda> A:*.\<Lambda> B:*.\<Pi> C:*.(A\<rightarrow>B\<rightarrow>C)\<rightarrow>C : ?T"
  by (depth_solve rules)

schematic_lemma (in Lomega2) "\<turnstile> \<Lambda> A:*.\<Lambda> B:*.\<Lambda> x:A. \<Lambda> y:B. x : ?T"
  by (depth_solve rules)

schematic_lemma (in Lomega2) "A:* B:* \<turnstile> ?p : (A\<rightarrow>B) \<rightarrow> ((B\<rightarrow>\<Pi> P:*.P)\<rightarrow>(A\<rightarrow>\<Pi> P:*.P))"
  apply (strip_asms rules)
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

schematic_lemma (in LP2) "A:* P:A\<rightarrow>* \<turnstile> \<Lambda> a:A. P^a\<rightarrow>(\<Pi> A:*.A) : ?T"
  by (depth_solve rules)

schematic_lemma (in LP2) "A:* P:A\<rightarrow>A\<rightarrow>* \<turnstile>
    (\<Pi> a:A. \<Pi> b:A. P^a^b\<rightarrow>P^b^a\<rightarrow>\<Pi> P:*.P) \<rightarrow> \<Pi> a:A. P^a^a\<rightarrow>\<Pi> P:*.P : ?T"
  by (depth_solve rules)

schematic_lemma (in LP2) "A:* P:A\<rightarrow>A\<rightarrow>* \<turnstile>
    ?p: (\<Pi> a:A. \<Pi> b:A. P^a^b\<rightarrow>P^b^a\<rightarrow>\<Pi> P:*.P) \<rightarrow> \<Pi> a:A. P^a^a\<rightarrow>\<Pi> P:*.P"
  -- {* Antisymmetry implies irreflexivity: *}
  apply (strip_asms rules)
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

schematic_lemma (in LPomega) "A:* \<turnstile> \<Lambda> P:A\<rightarrow>A\<rightarrow>*.\<Lambda> a:A. P^a^a : ?T"
  by (depth_solve rules)

schematic_lemma (in LPomega) "\<turnstile> \<Lambda> A:*.\<Lambda> P:A\<rightarrow>A\<rightarrow>*.\<Lambda> a:A. P^a^a : ?T"
  by (depth_solve rules)


subsection {* Constructions *}

schematic_lemma (in CC) "\<turnstile> \<Lambda> A:*.\<Lambda> P:A\<rightarrow>*.\<Lambda> a:A. P^a\<rightarrow>\<Pi> P:*.P: ?T"
  by (depth_solve rules)

schematic_lemma (in CC) "\<turnstile> \<Lambda> A:*.\<Lambda> P:A\<rightarrow>*.\<Pi> a:A. P^a: ?T"
  by (depth_solve rules)

schematic_lemma (in CC) "A:* P:A\<rightarrow>* a:A \<turnstile> ?p : (\<Pi> a:A. P^a)\<rightarrow>P^a"
  apply (strip_asms rules)
  apply (rule lam_ss)
    apply (depth_solve1 rules)
   prefer 2
   apply (depth_solve1 rules)
  apply (erule pi_elim, assumption, assumption)
  done


subsection {* Some random examples *}

schematic_lemma (in LP2) "A:* c:A f:A\<rightarrow>A \<turnstile>
    \<Lambda> a:A. \<Pi> P:A\<rightarrow>*.P^c \<rightarrow> (\<Pi> x:A. P^x\<rightarrow>P^(f^x)) \<rightarrow> P^a : ?T"
  by (depth_solve rules)

schematic_lemma (in CC) "\<Lambda> A:*.\<Lambda> c:A. \<Lambda> f:A\<rightarrow>A.
    \<Lambda> a:A. \<Pi> P:A\<rightarrow>*.P^c \<rightarrow> (\<Pi> x:A. P^x\<rightarrow>P^(f^x)) \<rightarrow> P^a : ?T"
  by (depth_solve rules)

schematic_lemma (in LP2)
  "A:* a:A b:A \<turnstile> ?p: (\<Pi> P:A\<rightarrow>*.P^a\<rightarrow>P^b) \<rightarrow> (\<Pi> P:A\<rightarrow>*.P^b\<rightarrow>P^a)"
  -- {* Symmetry of Leibnitz equality *}
  apply (strip_asms rules)
  apply (rule lam_ss)
    apply (depth_solve1 rules)
   prefer 2
   apply (depth_solve1 rules)
  apply (erule_tac a = "\<Lambda> x:A. \<Pi> Q:A\<rightarrow>*.Q^x\<rightarrow>Q^a" in pi_elim)
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
