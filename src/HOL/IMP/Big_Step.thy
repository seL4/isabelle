(* Author: Gerwin Klein, Tobias Nipkow *)

theory Big_Step imports Com begin

subsection "Big-Step Semantics of Commands"

text_raw{*\begin{isaverbatimwrite}\newcommand{\BigStepdef}{% *}
inductive
  big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
Skip:    "(SKIP,s) \<Rightarrow> s" |
Assign:  "(x ::= a,s) \<Rightarrow> s(x := aval a s)" |
Semi:    "\<lbrakk> (c\<^isub>1,s\<^isub>1) \<Rightarrow> s\<^isub>2;  (c\<^isub>2,s\<^isub>2) \<Rightarrow> s\<^isub>3 \<rbrakk> \<Longrightarrow>
          (c\<^isub>1;c\<^isub>2, s\<^isub>1) \<Rightarrow> s\<^isub>3" |

IfTrue:  "\<lbrakk> bval b s;  (c\<^isub>1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow>
         (IF b THEN c\<^isub>1 ELSE c\<^isub>2, s) \<Rightarrow> t" |
IfFalse: "\<lbrakk> \<not>bval b s;  (c\<^isub>2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow>
         (IF b THEN c\<^isub>1 ELSE c\<^isub>2, s) \<Rightarrow> t" |

WhileFalse: "\<not>bval b s \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow> s" |
WhileTrue:  "\<lbrakk> bval b s\<^isub>1;  (c,s\<^isub>1) \<Rightarrow> s\<^isub>2;  (WHILE b DO c, s\<^isub>2) \<Rightarrow> s\<^isub>3 \<rbrakk> \<Longrightarrow>
             (WHILE b DO c, s\<^isub>1) \<Rightarrow> s\<^isub>3"
text_raw{*}\end{isaverbatimwrite}*}

text_raw{*\begin{isaverbatimwrite}\newcommand{\BigStepEx}{% *}
schematic_lemma ex: "(''x'' ::= N 5; ''y'' ::= V ''x'', s) \<Rightarrow> ?t"
apply(rule Semi)
apply(rule Assign)
apply simp
apply(rule Assign)
done
text_raw{*}\end{isaverbatimwrite}*}

thm ex[simplified]

text{* We want to execute the big-step rules: *}

code_pred big_step .

text{* For inductive definitions we need command
       \texttt{values} instead of \texttt{value}. *}

values "{t. (SKIP, \<lambda>_. 0) \<Rightarrow> t}"

text{* We need to translate the result state into a list
to display it. *}

values "{map t [''x''] |t. (SKIP, <''x'' := 42>) \<Rightarrow> t}"

values "{map t [''x''] |t. (''x'' ::= N 2, <''x'' := 42>) \<Rightarrow> t}"

values "{map t [''x'',''y''] |t.
  (WHILE Less (V ''x'') (V ''y'') DO (''x'' ::= Plus (V ''x'') (N 5)),
   <''x'' := 0, ''y'' := 13>) \<Rightarrow> t}"


text{* Proof automation: *}

declare big_step.intros [intro]

text{* The standard induction rule 
@{thm [display] big_step.induct [no_vars]} *}

thm big_step.induct

text{* A customized induction rule for (c,s) pairs: *}

lemmas big_step_induct = big_step.induct[split_format(complete)]
thm big_step_induct
text {*
@{thm [display] big_step_induct [no_vars]}
*}


subsection "Rule inversion"

text{* What can we deduce from @{prop "(SKIP,s) \<Rightarrow> t"} ?
That @{prop "s = t"}. This is how we can automatically prove it: *}

inductive_cases skipE[elim!]: "(SKIP,s) \<Rightarrow> t"
thm skipE

text{* This is an \emph{elimination rule}. The [elim] attribute tells auto,
blast and friends (but not simp!) to use it automatically; [elim!] means that
it is applied eagerly.

Similarly for the other commands: *}

inductive_cases AssignE[elim!]: "(x ::= a,s) \<Rightarrow> t"
thm AssignE
inductive_cases SemiE[elim!]: "(c1;c2,s1) \<Rightarrow> s3"
thm SemiE
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<Rightarrow> t"
thm IfE

inductive_cases WhileE[elim]: "(WHILE b DO c,s) \<Rightarrow> t"
thm WhileE
text{* Only [elim]: [elim!] would not terminate. *}

text{* An automatic example: *}

lemma "(IF b THEN SKIP ELSE SKIP, s) \<Rightarrow> t \<Longrightarrow> t = s"
by blast

text{* Rule inversion by hand via the ``cases'' method: *}

lemma assumes "(IF b THEN SKIP ELSE SKIP, s) \<Rightarrow> t"
shows "t = s"
proof-
  from assms show ?thesis
  proof cases  --"inverting assms"
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

subsection "Command Equivalence"

text {*
  We call two statements @{text c} and @{text c'} equivalent wrt.\ the
  big-step semantics when \emph{@{text c} started in @{text s} terminates
  in @{text s'} iff @{text c'} started in the same @{text s} also terminates
  in the same @{text s'}}. Formally:
*}
text_raw{*\begin{isaverbatimwrite}\newcommand{\BigStepEquiv}{% *}
abbreviation
  equiv_c :: "com \<Rightarrow> com \<Rightarrow> bool" (infix "\<sim>" 50) where
  "c \<sim> c' == (\<forall>s t. (c,s) \<Rightarrow> t  =  (c',s) \<Rightarrow> t)"
text_raw{*}\end{isaverbatimwrite}*}

text {*
Warning: @{text"\<sim>"} is the symbol written \verb!\ < s i m >! (without spaces).

  As an example, we show that loop unfolding is an equivalence
  transformation on programs:
*}
lemma unfold_while:
  "(WHILE b DO c) \<sim> (IF b THEN c; WHILE b DO c ELSE SKIP)" (is "?w \<sim> ?iw")
proof -
  -- "to show the equivalence, we look at the derivation tree for"
  -- "each side and from that construct a derivation tree for the other side"
  { fix s t assume "(?w, s) \<Rightarrow> t"
    -- "as a first thing we note that, if @{text b} is @{text False} in state @{text s},"
    -- "then both statements do nothing:"
    { assume "\<not>bval b s"
      hence "t = s" using `(?w,s) \<Rightarrow> t` by blast
      hence "(?iw, s) \<Rightarrow> t" using `\<not>bval b s` by blast
    }
    moreover
    -- "on the other hand, if @{text b} is @{text True} in state @{text s},"
    -- {* then only the @{text WhileTrue} rule can have been used to derive @{text "(?w, s) \<Rightarrow> t"} *}
    { assume "bval b s"
      with `(?w, s) \<Rightarrow> t` obtain s' where
        "(c, s) \<Rightarrow> s'" and "(?w, s') \<Rightarrow> t" by auto
      -- "now we can build a derivation tree for the @{text IF}"
      -- "first, the body of the True-branch:"
      hence "(c; ?w, s) \<Rightarrow> t" by (rule Semi)
      -- "then the whole @{text IF}"
      with `bval b s` have "(?iw, s) \<Rightarrow> t" by (rule IfTrue)
    }
    ultimately
    -- "both cases together give us what we want:"
    have "(?iw, s) \<Rightarrow> t" by blast
  }
  moreover
  -- "now the other direction:"
  { fix s t assume "(?iw, s) \<Rightarrow> t"
    -- "again, if @{text b} is @{text False} in state @{text s}, then the False-branch"
    -- "of the @{text IF} is executed, and both statements do nothing:"
    { assume "\<not>bval b s"
      hence "s = t" using `(?iw, s) \<Rightarrow> t` by blast
      hence "(?w, s) \<Rightarrow> t" using `\<not>bval b s` by blast
    }
    moreover
    -- "on the other hand, if @{text b} is @{text True} in state @{text s},"
    -- {* then this time only the @{text IfTrue} rule can have be used *}
    { assume "bval b s"
      with `(?iw, s) \<Rightarrow> t` have "(c; ?w, s) \<Rightarrow> t" by auto
      -- "and for this, only the Semi-rule is applicable:"
      then obtain s' where
        "(c, s) \<Rightarrow> s'" and "(?w, s') \<Rightarrow> t" by auto
      -- "with this information, we can build a derivation tree for the @{text WHILE}"
      with `bval b s`
      have "(?w, s) \<Rightarrow> t" by (rule WhileTrue)
    }
    ultimately
    -- "both cases together again give us what we want:"
    have "(?w, s) \<Rightarrow> t" by blast
  }
  ultimately
  show ?thesis by blast
qed

text {* Luckily, such lengthy proofs are seldom necessary.  Isabelle can
prove many such facts automatically.  *}

lemma while_unfold:
  "(WHILE b DO c) \<sim> (IF b THEN c; WHILE b DO c ELSE SKIP)"
by blast

lemma triv_if:
  "(IF b THEN c ELSE c) \<sim> c"
by blast

lemma commute_if:
  "(IF b1 THEN (IF b2 THEN c11 ELSE c12) ELSE c2) 
   \<sim> 
   (IF b2 THEN (IF b1 THEN c11 ELSE c2) ELSE (IF b1 THEN c12 ELSE c2))"
by blast


subsection "Execution is deterministic"

text {* This proof is automatic. *}
text_raw{*\begin{isaverbatimwrite}\newcommand{\BigStepDeterministic}{% *}
theorem big_step_determ: "\<lbrakk> (c,s) \<Rightarrow> t; (c,s) \<Rightarrow> u \<rbrakk> \<Longrightarrow> u = t"
  by (induction arbitrary: u rule: big_step.induct) blast+
text_raw{*}\end{isaverbatimwrite}*}


text {*
  This is the proof as you might present it in a lecture. The remaining
  cases are simple enough to be proved automatically:
*}
text_raw{*\begin{isaverbatimwrite}\newcommand{\BigStepDetLong}{% *}
theorem
  "(c,s) \<Rightarrow> t  \<Longrightarrow>  (c,s) \<Rightarrow> t'  \<Longrightarrow>  t' = t"
proof (induction arbitrary: t' rule: big_step.induct)
  -- "the only interesting case, @{text WhileTrue}:"
  fix b c s s1 t t'
  -- "The assumptions of the rule:"
  assume "bval b s" and "(c,s) \<Rightarrow> s1" and "(WHILE b DO c,s1) \<Rightarrow> t"
  -- {* Ind.Hyp; note the @{text"\<And>"} because of arbitrary: *}
  assume IHc: "\<And>t'. (c,s) \<Rightarrow> t' \<Longrightarrow> t' = s1"
  assume IHw: "\<And>t'. (WHILE b DO c,s1) \<Rightarrow> t' \<Longrightarrow> t' = t"
  -- "Premise of implication:"
  assume "(WHILE b DO c,s) \<Rightarrow> t'"
  with `bval b s` obtain s1' where
      c: "(c,s) \<Rightarrow> s1'" and
      w: "(WHILE b DO c,s1') \<Rightarrow> t'"
    by auto
  from c IHc have "s1' = s1" by blast
  with w IHw show "t' = t" by blast
qed blast+ -- "prove the rest automatically"
text_raw{*}\end{isaverbatimwrite}*}

end
