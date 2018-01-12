(* Author: Gerwin Klein, Tobias Nipkow *)

theory Big_Step imports Com begin

subsection "Big-Step Semantics of Commands"

text \<open>
The big-step semantics is a straight-forward inductive definition
with concrete syntax. Note that the first parameter is a tuple,
so the syntax becomes @{text "(c,s) \<Rightarrow> s'"}.
\<close>

text_raw\<open>\snip{BigStepdef}{0}{1}{%\<close>
inductive
  big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
Skip: "(SKIP,s) \<Rightarrow> s" |
Assign: "(x ::= a,s) \<Rightarrow> s(x := aval a s)" |
Seq: "\<lbrakk> (c\<^sub>1,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (c\<^sub>2,s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> \<Longrightarrow> (c\<^sub>1;;c\<^sub>2, s\<^sub>1) \<Rightarrow> s\<^sub>3" |
IfTrue: "\<lbrakk> bval b s;  (c\<^sub>1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
IfFalse: "\<lbrakk> \<not>bval b s;  (c\<^sub>2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
WhileFalse: "\<not>bval b s \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow> s" |
WhileTrue:
"\<lbrakk> bval b s\<^sub>1;  (c,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (WHILE b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> 
\<Longrightarrow> (WHILE b DO c, s\<^sub>1) \<Rightarrow> s\<^sub>3"
text_raw\<open>}%endsnip\<close>

text_raw\<open>\snip{BigStepEx}{1}{2}{%\<close>
schematic_goal ex: "(''x'' ::= N 5;; ''y'' ::= V ''x'', s) \<Rightarrow> ?t"
apply(rule Seq)
apply(rule Assign)
apply simp
apply(rule Assign)
done
text_raw\<open>}%endsnip\<close>

thm ex[simplified]

text\<open>We want to execute the big-step rules:\<close>

code_pred big_step .

text\<open>For inductive definitions we need command
       \texttt{values} instead of \texttt{value}.\<close>

values "{t. (SKIP, \<lambda>_. 0) \<Rightarrow> t}"

text\<open>We need to translate the result state into a list
to display it.\<close>

values "{map t [''x''] |t. (SKIP, <''x'' := 42>) \<Rightarrow> t}"

values "{map t [''x''] |t. (''x'' ::= N 2, <''x'' := 42>) \<Rightarrow> t}"

values "{map t [''x'',''y''] |t.
  (WHILE Less (V ''x'') (V ''y'') DO (''x'' ::= Plus (V ''x'') (N 5)),
   <''x'' := 0, ''y'' := 13>) \<Rightarrow> t}"


text\<open>Proof automation:\<close>

text \<open>The introduction rules are good for automatically
construction small program executions. The recursive cases
may require backtracking, so we declare the set as unsafe
intro rules.\<close>
declare big_step.intros [intro]

text\<open>The standard induction rule 
@{thm [display] big_step.induct [no_vars]}\<close>

thm big_step.induct

text\<open>
This induction schema is almost perfect for our purposes, but
our trick for reusing the tuple syntax means that the induction
schema has two parameters instead of the @{text c}, @{text s},
and @{text s'} that we are likely to encounter. Splitting
the tuple parameter fixes this:
\<close>
lemmas big_step_induct = big_step.induct[split_format(complete)]
thm big_step_induct
text \<open>
@{thm [display] big_step_induct [no_vars]}
\<close>


subsection "Rule inversion"

text\<open>What can we deduce from @{prop "(SKIP,s) \<Rightarrow> t"} ?
That @{prop "s = t"}. This is how we can automatically prove it:\<close>

inductive_cases SkipE[elim!]: "(SKIP,s) \<Rightarrow> t"
thm SkipE

text\<open>This is an \emph{elimination rule}. The [elim] attribute tells auto,
blast and friends (but not simp!) to use it automatically; [elim!] means that
it is applied eagerly.

Similarly for the other commands:\<close>

inductive_cases AssignE[elim!]: "(x ::= a,s) \<Rightarrow> t"
thm AssignE
inductive_cases SeqE[elim!]: "(c1;;c2,s1) \<Rightarrow> s3"
thm SeqE
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<Rightarrow> t"
thm IfE

inductive_cases WhileE[elim]: "(WHILE b DO c,s) \<Rightarrow> t"
thm WhileE
text\<open>Only [elim]: [elim!] would not terminate.\<close>

text\<open>An automatic example:\<close>

lemma "(IF b THEN SKIP ELSE SKIP, s) \<Rightarrow> t \<Longrightarrow> t = s"
by blast

text\<open>Rule inversion by hand via the ``cases'' method:\<close>

lemma assumes "(IF b THEN SKIP ELSE SKIP, s) \<Rightarrow> t"
shows "t = s"
proof-
  from assms show ?thesis
  proof cases  \<comment>"inverting assms"
    case IfTrue thm IfTrue
    thus ?thesis by blast
  next
    case IfFalse thus ?thesis by blast
  qed
qed

(* Using rule inversion to prove simplification rules: *)
lemma assign_simp:
  "(x ::= a,s) \<Rightarrow> s' \<longleftrightarrow> (s' = s(x := aval a s))"
  by auto

text \<open>An example combining rule inversion and derivations\<close>
lemma Seq_assoc:
  "(c1;; c2;; c3, s) \<Rightarrow> s' \<longleftrightarrow> (c1;; (c2;; c3), s) \<Rightarrow> s'"
proof
  assume "(c1;; c2;; c3, s) \<Rightarrow> s'"
  then obtain s1 s2 where
    c1: "(c1, s) \<Rightarrow> s1" and
    c2: "(c2, s1) \<Rightarrow> s2" and
    c3: "(c3, s2) \<Rightarrow> s'" by auto
  from c2 c3
  have "(c2;; c3, s1) \<Rightarrow> s'" by (rule Seq)
  with c1
  show "(c1;; (c2;; c3), s) \<Rightarrow> s'" by (rule Seq)
next
  \<comment> "The other direction is analogous"
  assume "(c1;; (c2;; c3), s) \<Rightarrow> s'"
  thus "(c1;; c2;; c3, s) \<Rightarrow> s'" by auto
qed


subsection "Command Equivalence"

text \<open>
  We call two statements @{text c} and @{text c'} equivalent wrt.\ the
  big-step semantics when \emph{@{text c} started in @{text s} terminates
  in @{text s'} iff @{text c'} started in the same @{text s} also terminates
  in the same @{text s'}}. Formally:
\<close>
text_raw\<open>\snip{BigStepEquiv}{0}{1}{%\<close>
abbreviation
  equiv_c :: "com \<Rightarrow> com \<Rightarrow> bool" (infix "\<sim>" 50) where
  "c \<sim> c' \<equiv> (\<forall>s t. (c,s) \<Rightarrow> t  =  (c',s) \<Rightarrow> t)"
text_raw\<open>}%endsnip\<close>

text \<open>
Warning: @{text"\<sim>"} is the symbol written \verb!\ < s i m >! (without spaces).

  As an example, we show that loop unfolding is an equivalence
  transformation on programs:
\<close>
lemma unfold_while:
  "(WHILE b DO c) \<sim> (IF b THEN c;; WHILE b DO c ELSE SKIP)" (is "?w \<sim> ?iw")
proof -
  \<comment> "to show the equivalence, we look at the derivation tree for"
  \<comment> "each side and from that construct a derivation tree for the other side"
  have "(?iw, s) \<Rightarrow> t" if assm: "(?w, s) \<Rightarrow> t" for s t
  proof -
    from assm show ?thesis
    proof cases \<comment>"rule inversion on \<open>(?w, s) \<Rightarrow> t\<close>"
      case WhileFalse
      thus ?thesis by blast
    next
      case WhileTrue
      from \<open>bval b s\<close> \<open>(?w, s) \<Rightarrow> t\<close> obtain s' where
        "(c, s) \<Rightarrow> s'" and "(?w, s') \<Rightarrow> t" by auto
      \<comment> "now we can build a derivation tree for the @{text IF}"
      \<comment> "first, the body of the True-branch:"
      hence "(c;; ?w, s) \<Rightarrow> t" by (rule Seq)
      \<comment> "then the whole @{text IF}"
      with \<open>bval b s\<close> show ?thesis by (rule IfTrue)
    qed
  qed
  moreover
  \<comment> "now the other direction:"
  have "(?w, s) \<Rightarrow> t" if assm: "(?iw, s) \<Rightarrow> t" for s t
  proof -
    from assm show ?thesis
    proof cases \<comment>"rule inversion on \<open>(?iw, s) \<Rightarrow> t\<close>"
      case IfFalse
      hence "s = t" using \<open>(?iw, s) \<Rightarrow> t\<close> by blast
      thus ?thesis using \<open>\<not>bval b s\<close> by blast
    next
      case IfTrue
      \<comment> "and for this, only the Seq-rule is applicable:"
      from \<open>(c;; ?w, s) \<Rightarrow> t\<close> obtain s' where
        "(c, s) \<Rightarrow> s'" and "(?w, s') \<Rightarrow> t" by auto
      \<comment> "with this information, we can build a derivation tree for @{text WHILE}"
      with \<open>bval b s\<close> show ?thesis by (rule WhileTrue)
    qed
  qed
  ultimately
  show ?thesis by blast
qed

text \<open>Luckily, such lengthy proofs are seldom necessary.  Isabelle can
prove many such facts automatically.\<close>

lemma while_unfold:
  "(WHILE b DO c) \<sim> (IF b THEN c;; WHILE b DO c ELSE SKIP)"
by blast

lemma triv_if:
  "(IF b THEN c ELSE c) \<sim> c"
by blast

lemma commute_if:
  "(IF b1 THEN (IF b2 THEN c11 ELSE c12) ELSE c2) 
   \<sim> 
   (IF b2 THEN (IF b1 THEN c11 ELSE c2) ELSE (IF b1 THEN c12 ELSE c2))"
by blast

lemma sim_while_cong_aux:
  "(WHILE b DO c,s) \<Rightarrow> t  \<Longrightarrow> c \<sim> c' \<Longrightarrow>  (WHILE b DO c',s) \<Rightarrow> t"
apply(induction "WHILE b DO c" s t arbitrary: b c rule: big_step_induct)
 apply blast
apply blast
done

lemma sim_while_cong: "c \<sim> c' \<Longrightarrow> WHILE b DO c \<sim> WHILE b DO c'"
by (metis sim_while_cong_aux)

text \<open>Command equivalence is an equivalence relation, i.e.\ it is
reflexive, symmetric, and transitive. Because we used an abbreviation
above, Isabelle derives this automatically.\<close>

lemma sim_refl:  "c \<sim> c" by simp
lemma sim_sym:   "(c \<sim> c') = (c' \<sim> c)" by auto
lemma sim_trans: "c \<sim> c' \<Longrightarrow> c' \<sim> c'' \<Longrightarrow> c \<sim> c''" by auto

subsection "Execution is deterministic"

text \<open>This proof is automatic.\<close>

theorem big_step_determ: "\<lbrakk> (c,s) \<Rightarrow> t; (c,s) \<Rightarrow> u \<rbrakk> \<Longrightarrow> u = t"
  by (induction arbitrary: u rule: big_step.induct) blast+

text \<open>
  This is the proof as you might present it in a lecture. The remaining
  cases are simple enough to be proved automatically:
\<close>
text_raw\<open>\snip{BigStepDetLong}{0}{2}{%\<close>
theorem
  "(c,s) \<Rightarrow> t  \<Longrightarrow>  (c,s) \<Rightarrow> t'  \<Longrightarrow>  t' = t"
proof (induction arbitrary: t' rule: big_step.induct)
  \<comment> "the only interesting case, @{text WhileTrue}:"
  fix b c s s\<^sub>1 t t'
  \<comment> "The assumptions of the rule:"
  assume "bval b s" and "(c,s) \<Rightarrow> s\<^sub>1" and "(WHILE b DO c,s\<^sub>1) \<Rightarrow> t"
  \<comment> \<open>Ind.Hyp; note the @{text"\<And>"} because of arbitrary:\<close>
  assume IHc: "\<And>t'. (c,s) \<Rightarrow> t' \<Longrightarrow> t' = s\<^sub>1"
  assume IHw: "\<And>t'. (WHILE b DO c,s\<^sub>1) \<Rightarrow> t' \<Longrightarrow> t' = t"
  \<comment> "Premise of implication:"
  assume "(WHILE b DO c,s) \<Rightarrow> t'"
  with \<open>bval b s\<close> obtain s\<^sub>1' where
      c: "(c,s) \<Rightarrow> s\<^sub>1'" and
      w: "(WHILE b DO c,s\<^sub>1') \<Rightarrow> t'"
    by auto
  from c IHc have "s\<^sub>1' = s\<^sub>1" by blast
  with w IHw show "t' = t" by blast
qed blast+ \<comment> "prove the rest automatically"
text_raw\<open>}%endsnip\<close>

end
