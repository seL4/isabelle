(*  Title:        HOL/IMP/Natural.thy
    ID:           $Id$
    Author:       Tobias Nipkow & Robert Sandner, TUM
    Isar Version: Gerwin Klein, 2001; additional proofs by Lawrence Paulson
    Copyright     1996 TUM
*)

header "Natural Semantics of Commands"

theory Natural imports Com begin

subsection "Execution of commands"

text {*
  We write @{text "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c s'"} for \emph{Statement @{text c}, started
  in state @{text s}, terminates in state @{text s'}}. Formally,
  @{text "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c s'"} is just another form of saying \emph{the tuple
  @{text "(c,s,s')"} is part of the relation @{text evalc}}:
*}

definition
  update :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b)" ("_/[_ ::= /_]" [900,0,0] 900) where
  "update = fun_upd"

notation (xsymbols)
  update  ("_/[_ \<mapsto> /_]" [900,0,0] 900)

text {*
  The big-step execution relation @{text evalc} is defined inductively:
*}
inductive
  evalc :: "[com,state,state] \<Rightarrow> bool" ("\<langle>_,_\<rangle>/ \<longrightarrow>\<^sub>c _" [0,0,60] 60)
where
  Skip:    "\<langle>\<SKIP>,s\<rangle> \<longrightarrow>\<^sub>c s"
| Assign:  "\<langle>x :== a,s\<rangle> \<longrightarrow>\<^sub>c s[x\<mapsto>a s]"

| Semi:    "\<langle>c0,s\<rangle> \<longrightarrow>\<^sub>c s'' \<Longrightarrow> \<langle>c1,s''\<rangle> \<longrightarrow>\<^sub>c s' \<Longrightarrow> \<langle>c0; c1, s\<rangle> \<longrightarrow>\<^sub>c s'"

| IfTrue:  "b s \<Longrightarrow> \<langle>c0,s\<rangle> \<longrightarrow>\<^sub>c s' \<Longrightarrow> \<langle>\<IF> b \<THEN> c0 \<ELSE> c1, s\<rangle> \<longrightarrow>\<^sub>c s'"
| IfFalse: "\<not>b s \<Longrightarrow> \<langle>c1,s\<rangle> \<longrightarrow>\<^sub>c s' \<Longrightarrow> \<langle>\<IF> b \<THEN> c0 \<ELSE> c1, s\<rangle> \<longrightarrow>\<^sub>c s'"

| WhileFalse: "\<not>b s \<Longrightarrow> \<langle>\<WHILE> b \<DO> c,s\<rangle> \<longrightarrow>\<^sub>c s"
| WhileTrue:  "b s \<Longrightarrow> \<langle>c,s\<rangle> \<longrightarrow>\<^sub>c s'' \<Longrightarrow> \<langle>\<WHILE> b \<DO> c, s''\<rangle> \<longrightarrow>\<^sub>c s'
               \<Longrightarrow> \<langle>\<WHILE> b \<DO> c, s\<rangle> \<longrightarrow>\<^sub>c s'"

lemmas evalc.intros [intro] -- "use those rules in automatic proofs"

text {*
The induction principle induced by this definition looks like this:

@{thm [display] evalc.induct [no_vars]}


(@{text "\<And>"} and @{text "\<Longrightarrow>"} are Isabelle's
  meta symbols for @{text "\<forall>"} and @{text "\<longrightarrow>"})
*}

text {*
  The rules of @{text evalc} are syntax directed, i.e.~for each
  syntactic category there is always only one rule applicable. That
  means we can use the rules in both directions.  This property is called rule inversion.
*}
inductive_cases skipE [elim!]:   "\<langle>\<SKIP>,s\<rangle> \<longrightarrow>\<^sub>c s'"
inductive_cases semiE [elim!]:   "\<langle>c0; c1, s\<rangle> \<longrightarrow>\<^sub>c s'"
inductive_cases assignE [elim!]: "\<langle>x :== a,s\<rangle> \<longrightarrow>\<^sub>c s'"
inductive_cases ifE [elim!]:     "\<langle>\<IF> b \<THEN> c0 \<ELSE> c1, s\<rangle> \<longrightarrow>\<^sub>c s'"
inductive_cases whileE [elim]:  "\<langle>\<WHILE> b \<DO> c,s\<rangle> \<longrightarrow>\<^sub>c s'"

text {* The next proofs are all trivial by rule inversion.
*}

lemma skip:
  "\<langle>\<SKIP>,s\<rangle> \<longrightarrow>\<^sub>c s' = (s' = s)"
  by auto

lemma assign:
  "\<langle>x :== a,s\<rangle> \<longrightarrow>\<^sub>c s' = (s' = s[x\<mapsto>a s])"
  by auto

lemma semi:
  "\<langle>c0; c1, s\<rangle> \<longrightarrow>\<^sub>c s' = (\<exists>s''. \<langle>c0,s\<rangle> \<longrightarrow>\<^sub>c s'' \<and> \<langle>c1,s''\<rangle> \<longrightarrow>\<^sub>c s')"
  by auto

lemma ifTrue:
  "b s \<Longrightarrow> \<langle>\<IF> b \<THEN> c0 \<ELSE> c1, s\<rangle> \<longrightarrow>\<^sub>c s' = \<langle>c0,s\<rangle> \<longrightarrow>\<^sub>c s'"
  by auto

lemma ifFalse:
  "\<not>b s \<Longrightarrow> \<langle>\<IF> b \<THEN> c0 \<ELSE> c1, s\<rangle> \<longrightarrow>\<^sub>c s' = \<langle>c1,s\<rangle> \<longrightarrow>\<^sub>c s'"
  by auto

lemma whileFalse:
  "\<not> b s \<Longrightarrow> \<langle>\<WHILE> b \<DO> c,s\<rangle> \<longrightarrow>\<^sub>c s' = (s' = s)"
  by auto

lemma whileTrue:
  "b s \<Longrightarrow>
  \<langle>\<WHILE> b \<DO> c, s\<rangle> \<longrightarrow>\<^sub>c s' =
  (\<exists>s''. \<langle>c,s\<rangle> \<longrightarrow>\<^sub>c s'' \<and> \<langle>\<WHILE> b \<DO> c, s''\<rangle> \<longrightarrow>\<^sub>c s')"
  by auto

text "Again, Isabelle may use these rules in automatic proofs:"
lemmas evalc_cases [simp] = skip assign ifTrue ifFalse whileFalse semi whileTrue

subsection "Equivalence of statements"

text {*
  We call two statements @{text c} and @{text c'} equivalent wrt.~the
  big-step semantics when \emph{@{text c} started in @{text s} terminates
  in @{text s'} iff @{text c'} started in the same @{text s} also terminates
  in the same @{text s'}}. Formally:
*}
definition
  equiv_c :: "com \<Rightarrow> com \<Rightarrow> bool" ("_ \<sim> _") where
  "c \<sim> c' = (\<forall>s s'. \<langle>c, s\<rangle> \<longrightarrow>\<^sub>c s' = \<langle>c', s\<rangle> \<longrightarrow>\<^sub>c s')"

text {*
  Proof rules telling Isabelle to unfold the definition
  if there is something to be proved about equivalent
  statements: *}
lemma equivI [intro!]:
  "(\<And>s s'. \<langle>c, s\<rangle> \<longrightarrow>\<^sub>c s' = \<langle>c', s\<rangle> \<longrightarrow>\<^sub>c s') \<Longrightarrow> c \<sim> c'"
  by (unfold equiv_c_def) blast

lemma equivD1:
  "c \<sim> c' \<Longrightarrow> \<langle>c, s\<rangle> \<longrightarrow>\<^sub>c s' \<Longrightarrow> \<langle>c', s\<rangle> \<longrightarrow>\<^sub>c s'"
  by (unfold equiv_c_def) blast

lemma equivD2:
  "c \<sim> c' \<Longrightarrow> \<langle>c', s\<rangle> \<longrightarrow>\<^sub>c s' \<Longrightarrow> \<langle>c, s\<rangle> \<longrightarrow>\<^sub>c s'"
  by (unfold equiv_c_def) blast

text {*
  As an example, we show that loop unfolding is an equivalence
  transformation on programs:
*}
lemma unfold_while:
  "(\<WHILE> b \<DO> c) \<sim> (\<IF> b \<THEN> c; \<WHILE> b \<DO> c \<ELSE> \<SKIP>)" (is "?w \<sim> ?if")
proof -
  -- "to show the equivalence, we look at the derivation tree for"
  -- "each side and from that construct a derivation tree for the other side"
  { fix s s' assume w: "\<langle>?w, s\<rangle> \<longrightarrow>\<^sub>c s'"
    -- "as a first thing we note that, if @{text b} is @{text False} in state @{text s},"
    -- "then both statements do nothing:"
    hence "\<not>b s \<Longrightarrow> s = s'" by blast
    hence "\<not>b s \<Longrightarrow> \<langle>?if, s\<rangle> \<longrightarrow>\<^sub>c s'" by blast
    moreover
    -- "on the other hand, if @{text b} is @{text True} in state @{text s},"
    -- {* then only the @{text WhileTrue} rule can have been used to derive @{text "\<langle>?w, s\<rangle> \<longrightarrow>\<^sub>c s'"} *}
    { assume b: "b s"
      with w obtain s'' where
        "\<langle>c, s\<rangle> \<longrightarrow>\<^sub>c s''" and "\<langle>?w, s''\<rangle> \<longrightarrow>\<^sub>c s'" by (cases set: evalc) auto
      -- "now we can build a derivation tree for the @{text \<IF>}"
      -- "first, the body of the True-branch:"
      hence "\<langle>c; ?w, s\<rangle> \<longrightarrow>\<^sub>c s'" by (rule Semi)
      -- "then the whole @{text \<IF>}"
      with b have "\<langle>?if, s\<rangle> \<longrightarrow>\<^sub>c s'" by (rule IfTrue)
    }
    ultimately
    -- "both cases together give us what we want:"
    have "\<langle>?if, s\<rangle> \<longrightarrow>\<^sub>c s'" by blast
  }
  moreover
  -- "now the other direction:"
  { fix s s' assume "if": "\<langle>?if, s\<rangle> \<longrightarrow>\<^sub>c s'"
    -- "again, if @{text b} is @{text False} in state @{text s}, then the False-branch"
    -- "of the @{text \<IF>} is executed, and both statements do nothing:"
    hence "\<not>b s \<Longrightarrow> s = s'" by blast
    hence "\<not>b s \<Longrightarrow> \<langle>?w, s\<rangle> \<longrightarrow>\<^sub>c s'" by blast
    moreover
    -- "on the other hand, if @{text b} is @{text True} in state @{text s},"
    -- {* then this time only the @{text IfTrue} rule can have be used *}
    { assume b: "b s"
      with "if" have "\<langle>c; ?w, s\<rangle> \<longrightarrow>\<^sub>c s'" by (cases set: evalc) auto
      -- "and for this, only the Semi-rule is applicable:"
      then obtain s'' where
        "\<langle>c, s\<rangle> \<longrightarrow>\<^sub>c s''" and "\<langle>?w, s''\<rangle> \<longrightarrow>\<^sub>c s'" by (cases set: evalc) auto
      -- "with this information, we can build a derivation tree for the @{text \<WHILE>}"
      with b
      have "\<langle>?w, s\<rangle> \<longrightarrow>\<^sub>c s'" by (rule WhileTrue)
    }
    ultimately
    -- "both cases together again give us what we want:"
    have "\<langle>?w, s\<rangle> \<longrightarrow>\<^sub>c s'" by blast
  }
  ultimately
  show ?thesis by blast
qed

text {*
   Happily, such lengthy proofs are seldom necessary.  Isabelle can prove many such facts automatically.
*}

lemma 
  "(\<WHILE> b \<DO> c) \<sim> (\<IF> b \<THEN> c; \<WHILE> b \<DO> c \<ELSE> \<SKIP>)"
by blast

lemma triv_if:
  "(\<IF> b \<THEN> c \<ELSE> c) \<sim> c"
by blast

lemma commute_if:
  "(\<IF> b1 \<THEN> (\<IF> b2 \<THEN> c11 \<ELSE> c12) \<ELSE> c2) 
   \<sim> 
   (\<IF> b2 \<THEN> (\<IF> b1 \<THEN> c11 \<ELSE> c2) \<ELSE> (\<IF> b1 \<THEN> c12 \<ELSE> c2))"
by blast

lemma while_equiv:
  "\<langle>c0, s\<rangle> \<longrightarrow>\<^sub>c u \<Longrightarrow> c \<sim> c' \<Longrightarrow> (c0 = \<WHILE> b \<DO> c) \<Longrightarrow> \<langle>\<WHILE> b \<DO> c', s\<rangle> \<longrightarrow>\<^sub>c u" 
by (induct rule: evalc.induct) (auto simp add: equiv_c_def) 

lemma equiv_while:
  "c \<sim> c' \<Longrightarrow> (\<WHILE> b \<DO> c) \<sim> (\<WHILE> b \<DO> c')"
by (simp add: equiv_c_def) (metis equiv_c_def while_equiv) 


text {*
    Program equivalence is an equivalence relation.
*}

lemma equiv_refl:
  "c \<sim> c"
by blast

lemma equiv_sym:
  "c1 \<sim> c2 \<Longrightarrow> c2 \<sim> c1"
by (auto simp add: equiv_c_def) 

lemma equiv_trans:
  "c1 \<sim> c2 \<Longrightarrow> c2 \<sim> c3 \<Longrightarrow> c1 \<sim> c3"
by (auto simp add: equiv_c_def) 

text {*
    Program constructions preserve equivalence.
*}

lemma equiv_semi:
  "c1 \<sim> c1' \<Longrightarrow> c2 \<sim> c2' \<Longrightarrow> (c1; c2) \<sim> (c1'; c2')"
by (force simp add: equiv_c_def) 

lemma equiv_if:
  "c1 \<sim> c1' \<Longrightarrow> c2 \<sim> c2' \<Longrightarrow> (\<IF> b \<THEN> c1 \<ELSE> c2) \<sim> (\<IF> b \<THEN> c1' \<ELSE> c2')"
by (force simp add: equiv_c_def) 

lemma while_never: "\<langle>c, s\<rangle> \<longrightarrow>\<^sub>c u \<Longrightarrow> c \<noteq> \<WHILE> (\<lambda>s. True) \<DO> c1"
apply (induct rule: evalc.induct)
apply auto
done

lemma equiv_while_True:
  "(\<WHILE> (\<lambda>s. True) \<DO> c1) \<sim> (\<WHILE> (\<lambda>s. True) \<DO> c2)" 
by (blast dest: while_never) 


subsection "Execution is deterministic"

text {*
This proof is automatic.
*}
theorem "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c t \<Longrightarrow> \<langle>c,s\<rangle> \<longrightarrow>\<^sub>c u \<Longrightarrow> u = t"
by (induct arbitrary: u rule: evalc.induct) blast+


text {*
The following proof presents all the details:
*}
theorem com_det:
  assumes "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c t" and "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c u"
  shows "u = t"
  using prems
proof (induct arbitrary: u set: evalc)
  fix s u assume "\<langle>\<SKIP>,s\<rangle> \<longrightarrow>\<^sub>c u"
  thus "u = s" by blast
next
  fix a s x u assume "\<langle>x :== a,s\<rangle> \<longrightarrow>\<^sub>c u"
  thus "u = s[x \<mapsto> a s]" by blast
next
  fix c0 c1 s s1 s2 u
  assume IH0: "\<And>u. \<langle>c0,s\<rangle> \<longrightarrow>\<^sub>c u \<Longrightarrow> u = s2"
  assume IH1: "\<And>u. \<langle>c1,s2\<rangle> \<longrightarrow>\<^sub>c u \<Longrightarrow> u = s1"

  assume "\<langle>c0;c1, s\<rangle> \<longrightarrow>\<^sub>c u"
  then obtain s' where
      c0: "\<langle>c0,s\<rangle> \<longrightarrow>\<^sub>c s'" and
      c1: "\<langle>c1,s'\<rangle> \<longrightarrow>\<^sub>c u"
    by auto

  from c0 IH0 have "s'=s2" by blast
  with c1 IH1 show "u=s1" by blast
next
  fix b c0 c1 s s1 u
  assume IH: "\<And>u. \<langle>c0,s\<rangle> \<longrightarrow>\<^sub>c u \<Longrightarrow> u = s1"

  assume "b s" and "\<langle>\<IF> b \<THEN> c0 \<ELSE> c1,s\<rangle> \<longrightarrow>\<^sub>c u"
  hence "\<langle>c0, s\<rangle> \<longrightarrow>\<^sub>c u" by blast
  with IH show "u = s1" by blast
next
  fix b c0 c1 s s1 u
  assume IH: "\<And>u. \<langle>c1,s\<rangle> \<longrightarrow>\<^sub>c u \<Longrightarrow> u = s1"

  assume "\<not>b s" and "\<langle>\<IF> b \<THEN> c0 \<ELSE> c1,s\<rangle> \<longrightarrow>\<^sub>c u"
  hence "\<langle>c1, s\<rangle> \<longrightarrow>\<^sub>c u" by blast
  with IH show "u = s1" by blast
next
  fix b c s u
  assume "\<not>b s" and "\<langle>\<WHILE> b \<DO> c,s\<rangle> \<longrightarrow>\<^sub>c u"
  thus "u = s" by blast
next
  fix b c s s1 s2 u
  assume "IH\<^sub>c": "\<And>u. \<langle>c,s\<rangle> \<longrightarrow>\<^sub>c u \<Longrightarrow> u = s2"
  assume "IH\<^sub>w": "\<And>u. \<langle>\<WHILE> b \<DO> c,s2\<rangle> \<longrightarrow>\<^sub>c u \<Longrightarrow> u = s1"

  assume "b s" and "\<langle>\<WHILE> b \<DO> c,s\<rangle> \<longrightarrow>\<^sub>c u"
  then obtain s' where
      c: "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c s'" and
      w: "\<langle>\<WHILE> b \<DO> c,s'\<rangle> \<longrightarrow>\<^sub>c u"
    by auto

  from c "IH\<^sub>c" have "s' = s2" by blast
  with w "IH\<^sub>w" show "u = s1" by blast
qed


text {*
  This is the proof as you might present it in a lecture. The remaining
  cases are simple enough to be proved automatically:
*}
theorem
  assumes "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c t" and "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c u"
  shows "u = t"
  using prems
proof (induct arbitrary: u)
  -- "the simple @{text \<SKIP>} case for demonstration:"
  fix s u assume "\<langle>\<SKIP>,s\<rangle> \<longrightarrow>\<^sub>c u"
  thus "u = s" by blast
next
  -- "and the only really interesting case, @{text \<WHILE>}:"
  fix b c s s1 s2 u
  assume "IH\<^sub>c": "\<And>u. \<langle>c,s\<rangle> \<longrightarrow>\<^sub>c u \<Longrightarrow> u = s2"
  assume "IH\<^sub>w": "\<And>u. \<langle>\<WHILE> b \<DO> c,s2\<rangle> \<longrightarrow>\<^sub>c u \<Longrightarrow> u = s1"

  assume "b s" and "\<langle>\<WHILE> b \<DO> c,s\<rangle> \<longrightarrow>\<^sub>c u"
  then obtain s' where
      c: "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c s'" and
      w: "\<langle>\<WHILE> b \<DO> c,s'\<rangle> \<longrightarrow>\<^sub>c u"
    by auto

  from c "IH\<^sub>c" have "s' = s2" by blast
  with w "IH\<^sub>w" show "u = s1" by blast
qed blast+ -- "prove the rest automatically"

end
