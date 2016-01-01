section \<open>Lambda Cube Examples\<close>

theory Example
imports Cube
begin

text \<open>Examples taken from:

  H. Barendregt. Introduction to Generalised Type Systems.
  J. Functional Programming.\<close>

method_setup depth_solve =
  \<open>Attrib.thms >> (fn thms => fn ctxt => METHOD (fn facts =>
    (DEPTH_SOLVE (HEADGOAL (assume_tac ctxt ORELSE' resolve_tac ctxt (facts @ thms))))))\<close>

method_setup depth_solve1 =
  \<open>Attrib.thms >> (fn thms => fn ctxt => METHOD (fn facts =>
    (DEPTH_SOLVE_1 (HEADGOAL (assume_tac ctxt ORELSE' resolve_tac ctxt (facts @ thms))))))\<close>

method_setup strip_asms =
  \<open>Attrib.thms >> (fn thms => fn ctxt => METHOD (fn facts =>
    REPEAT (resolve_tac ctxt @{thms strip_b strip_s} 1 THEN
    DEPTH_SOLVE_1 (assume_tac ctxt 1 ORELSE resolve_tac ctxt (facts @ thms) 1))))\<close>


subsection \<open>Simple types\<close>

schematic_goal "A:* \<turnstile> A\<rightarrow>A : ?T"
  by (depth_solve rules)

schematic_goal "A:* \<turnstile> \<^bold>\<lambda>a:A. a : ?T"
  by (depth_solve rules)

schematic_goal "A:* B:* b:B \<turnstile> \<^bold>\<lambda>x:A. b : ?T"
  by (depth_solve rules)

schematic_goal "A:* b:A \<turnstile> (\<^bold>\<lambda>a:A. a)\<cdot>b: ?T"
  by (depth_solve rules)

schematic_goal "A:* B:* c:A b:B \<turnstile> (\<^bold>\<lambda>x:A. b)\<cdot> c: ?T"
  by (depth_solve rules)

schematic_goal "A:* B:* \<turnstile> \<^bold>\<lambda>a:A. \<^bold>\<lambda>b:B. a : ?T"
  by (depth_solve rules)


subsection \<open>Second-order types\<close>

schematic_goal (in L2) "\<turnstile> \<^bold>\<lambda>A:*. \<^bold>\<lambda>a:A. a : ?T"
  by (depth_solve rules)

schematic_goal (in L2) "A:* \<turnstile> (\<^bold>\<lambda>B:*. \<^bold>\<lambda>b:B. b)\<cdot>A : ?T"
  by (depth_solve rules)

schematic_goal (in L2) "A:* b:A \<turnstile> (\<^bold>\<lambda>B:*. \<^bold>\<lambda>b:B. b) \<cdot> A \<cdot> b: ?T"
  by (depth_solve rules)

schematic_goal (in L2) "\<turnstile> \<^bold>\<lambda>B:*. \<^bold>\<lambda>a:(\<Prod>A:*.A).a \<cdot> ((\<Prod>A:*.A)\<rightarrow>B) \<cdot> a: ?T"
  by (depth_solve rules)


subsection \<open>Weakly higher-order propositional logic\<close>

schematic_goal (in Lomega) "\<turnstile> \<^bold>\<lambda>A:*.A\<rightarrow>A : ?T"
  by (depth_solve rules)

schematic_goal (in Lomega) "B:* \<turnstile> (\<^bold>\<lambda>A:*.A\<rightarrow>A) \<cdot> B : ?T"
  by (depth_solve rules)

schematic_goal (in Lomega) "B:* b:B \<turnstile> (\<^bold>\<lambda>y:B. b): ?T"
  by (depth_solve rules)

schematic_goal (in Lomega) "A:* F:*\<rightarrow>* \<turnstile> F\<cdot>(F\<cdot>A): ?T"
  by (depth_solve rules)

schematic_goal (in Lomega) "A:* \<turnstile> \<^bold>\<lambda>F:*\<rightarrow>*.F\<cdot>(F\<cdot>A): ?T"
  by (depth_solve rules)


subsection \<open>LP\<close>

schematic_goal (in LP) "A:* \<turnstile> A \<rightarrow> * : ?T"
  by (depth_solve rules)

schematic_goal (in LP) "A:* P:A\<rightarrow>* a:A \<turnstile> P\<cdot>a: ?T"
  by (depth_solve rules)

schematic_goal (in LP) "A:* P:A\<rightarrow>A\<rightarrow>* a:A \<turnstile> \<Prod>a:A. P\<cdot>a\<cdot>a: ?T"
  by (depth_solve rules)

schematic_goal (in LP) "A:* P:A\<rightarrow>* Q:A\<rightarrow>* \<turnstile> \<Prod>a:A. P\<cdot>a \<rightarrow> Q\<cdot>a: ?T"
  by (depth_solve rules)

schematic_goal (in LP) "A:* P:A\<rightarrow>* \<turnstile> \<Prod>a:A. P\<cdot>a \<rightarrow> P\<cdot>a: ?T"
  by (depth_solve rules)

schematic_goal (in LP) "A:* P:A\<rightarrow>* \<turnstile> \<^bold>\<lambda>a:A. \<^bold>\<lambda>x:P\<cdot>a. x: ?T"
  by (depth_solve rules)

schematic_goal (in LP) "A:* P:A\<rightarrow>* Q:* \<turnstile> (\<Prod>a:A. P\<cdot>a\<rightarrow>Q) \<rightarrow> (\<Prod>a:A. P\<cdot>a) \<rightarrow> Q : ?T"
  by (depth_solve rules)

schematic_goal (in LP) "A:* P:A\<rightarrow>* Q:* a0:A \<turnstile>
        \<^bold>\<lambda>x:\<Prod>a:A. P\<cdot>a\<rightarrow>Q. \<^bold>\<lambda>y:\<Prod>a:A. P\<cdot>a. x\<cdot>a0\<cdot>(y\<cdot>a0): ?T"
  by (depth_solve rules)


subsection \<open>Omega-order types\<close>

schematic_goal (in L2) "A:* B:* \<turnstile> \<Prod>C:*.(A\<rightarrow>B\<rightarrow>C)\<rightarrow>C : ?T"
  by (depth_solve rules)

schematic_goal (in Lomega2) "\<turnstile> \<^bold>\<lambda>A:*. \<^bold>\<lambda>B:*.\<Prod>C:*.(A\<rightarrow>B\<rightarrow>C)\<rightarrow>C : ?T"
  by (depth_solve rules)

schematic_goal (in Lomega2) "\<turnstile> \<^bold>\<lambda>A:*. \<^bold>\<lambda>B:*. \<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B. x : ?T"
  by (depth_solve rules)

schematic_goal (in Lomega2) "A:* B:* \<turnstile> ?p : (A\<rightarrow>B) \<rightarrow> ((B\<rightarrow>\<Prod>P:*.P)\<rightarrow>(A\<rightarrow>\<Prod>P:*.P))"
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


subsection \<open>Second-order Predicate Logic\<close>

schematic_goal (in LP2) "A:* P:A\<rightarrow>* \<turnstile> \<^bold>\<lambda>a:A. P\<cdot>a\<rightarrow>(\<Prod>A:*.A) : ?T"
  by (depth_solve rules)

schematic_goal (in LP2) "A:* P:A\<rightarrow>A\<rightarrow>* \<turnstile>
    (\<Prod>a:A. \<Prod>b:A. P\<cdot>a\<cdot>b\<rightarrow>P\<cdot>b\<cdot>a\<rightarrow>\<Prod>P:*.P) \<rightarrow> \<Prod>a:A. P\<cdot>a\<cdot>a\<rightarrow>\<Prod>P:*.P : ?T"
  by (depth_solve rules)

schematic_goal (in LP2) "A:* P:A\<rightarrow>A\<rightarrow>* \<turnstile>
    ?p: (\<Prod>a:A. \<Prod>b:A. P\<cdot>a\<cdot>b\<rightarrow>P\<cdot>b\<cdot>a\<rightarrow>\<Prod>P:*.P) \<rightarrow> \<Prod>a:A. P\<cdot>a\<cdot>a\<rightarrow>\<Prod>P:*.P"
  \<comment> \<open>Antisymmetry implies irreflexivity:\<close>
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


subsection \<open>LPomega\<close>

schematic_goal (in LPomega) "A:* \<turnstile> \<^bold>\<lambda>P:A\<rightarrow>A\<rightarrow>*. \<^bold>\<lambda>a:A. P\<cdot>a\<cdot>a : ?T"
  by (depth_solve rules)

schematic_goal (in LPomega) "\<turnstile> \<^bold>\<lambda>A:*. \<^bold>\<lambda>P:A\<rightarrow>A\<rightarrow>*. \<^bold>\<lambda>a:A. P\<cdot>a\<cdot>a : ?T"
  by (depth_solve rules)


subsection \<open>Constructions\<close>

schematic_goal (in CC) "\<turnstile> \<^bold>\<lambda>A:*. \<^bold>\<lambda>P:A\<rightarrow>*. \<^bold>\<lambda>a:A. P\<cdot>a\<rightarrow>\<Prod>P:*.P: ?T"
  by (depth_solve rules)

schematic_goal (in CC) "\<turnstile> \<^bold>\<lambda>A:*. \<^bold>\<lambda>P:A\<rightarrow>*.\<Prod>a:A. P\<cdot>a: ?T"
  by (depth_solve rules)

schematic_goal (in CC) "A:* P:A\<rightarrow>* a:A \<turnstile> ?p : (\<Prod>a:A. P\<cdot>a)\<rightarrow>P\<cdot>a"
  apply (strip_asms rules)
  apply (rule lam_ss)
    apply (depth_solve1 rules)
   prefer 2
   apply (depth_solve1 rules)
  apply (erule pi_elim, assumption, assumption)
  done


subsection \<open>Some random examples\<close>

schematic_goal (in LP2) "A:* c:A f:A\<rightarrow>A \<turnstile>
    \<^bold>\<lambda>a:A. \<Prod>P:A\<rightarrow>*.P\<cdot>c \<rightarrow> (\<Prod>x:A. P\<cdot>x\<rightarrow>P\<cdot>(f\<cdot>x)) \<rightarrow> P\<cdot>a : ?T"
  by (depth_solve rules)

schematic_goal (in CC) "\<^bold>\<lambda>A:*. \<^bold>\<lambda>c:A. \<^bold>\<lambda>f:A\<rightarrow>A.
    \<^bold>\<lambda>a:A. \<Prod>P:A\<rightarrow>*.P\<cdot>c \<rightarrow> (\<Prod>x:A. P\<cdot>x\<rightarrow>P\<cdot>(f\<cdot>x)) \<rightarrow> P\<cdot>a : ?T"
  by (depth_solve rules)

schematic_goal (in LP2)
  "A:* a:A b:A \<turnstile> ?p: (\<Prod>P:A\<rightarrow>*.P\<cdot>a\<rightarrow>P\<cdot>b) \<rightarrow> (\<Prod>P:A\<rightarrow>*.P\<cdot>b\<rightarrow>P\<cdot>a)"
  \<comment> \<open>Symmetry of Leibnitz equality\<close>
  apply (strip_asms rules)
  apply (rule lam_ss)
    apply (depth_solve1 rules)
   prefer 2
   apply (depth_solve1 rules)
  apply (erule_tac a = "\<^bold>\<lambda>x:A. \<Prod>Q:A\<rightarrow>*.Q\<cdot>x\<rightarrow>Q\<cdot>a" in pi_elim)
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
