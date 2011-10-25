header "Small-Step Semantics of Commands"

theory Small_Step imports Star Big_Step begin

subsection "The transition relation"

inductive
  small_step :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
Assign:  "(x ::= a, s) \<rightarrow> (SKIP, s(x := aval a s))" |

Semi1:   "(SKIP;c\<^isub>2,s) \<rightarrow> (c\<^isub>2,s)" |
Semi2:   "(c\<^isub>1,s) \<rightarrow> (c\<^isub>1',s') \<Longrightarrow> (c\<^isub>1;c\<^isub>2,s) \<rightarrow> (c\<^isub>1';c\<^isub>2,s')" |

IfTrue:  "bval b s \<Longrightarrow> (IF b THEN c\<^isub>1 ELSE c\<^isub>2,s) \<rightarrow> (c\<^isub>1,s)" |
IfFalse: "\<not>bval b s \<Longrightarrow> (IF b THEN c\<^isub>1 ELSE c\<^isub>2,s) \<rightarrow> (c\<^isub>2,s)" |

While:   "(WHILE b DO c,s) \<rightarrow> (IF b THEN c; WHILE b DO c ELSE SKIP,s)"


abbreviation small_steps :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
where "x \<rightarrow>* y == star small_step x y"

subsection{* Executability *}

code_pred small_step .

values "{(c',map t [''x'',''y'',''z'']) |c' t.
   (''x'' ::= V ''z''; ''y'' ::= V ''x'',
    <''x'' := 3, ''y'' := 7, ''z'' := 5>) \<rightarrow>* (c',t)}"


subsection{* Proof infrastructure *}

subsubsection{* Induction rules *}

text{* The default induction rule @{thm[source] small_step.induct} only works
for lemmas of the form @{text"a \<rightarrow> b \<Longrightarrow> \<dots>"} where @{text a} and @{text b} are
not already pairs @{text"(DUMMY,DUMMY)"}. We can generate a suitable variant
of @{thm[source] small_step.induct} for pairs by ``splitting'' the arguments
@{text"\<rightarrow>"} into pairs: *}
lemmas small_step_induct = small_step.induct[split_format(complete)]


subsubsection{* Proof automation *}

declare small_step.intros[simp,intro]

text{* Rule inversion: *}

inductive_cases SkipE[elim!]: "(SKIP,s) \<rightarrow> ct"
thm SkipE
inductive_cases AssignE[elim!]: "(x::=a,s) \<rightarrow> ct"
thm AssignE
inductive_cases SemiE[elim]: "(c1;c2,s) \<rightarrow> ct"
thm SemiE
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<rightarrow> ct"
inductive_cases WhileE[elim]: "(WHILE b DO c, s) \<rightarrow> ct"


text{* A simple property: *}
lemma deterministic:
  "cs \<rightarrow> cs' \<Longrightarrow> cs \<rightarrow> cs'' \<Longrightarrow> cs'' = cs'"
apply(induction arbitrary: cs'' rule: small_step.induct)
apply blast+
done


subsection "Equivalence with big-step semantics"

lemma star_semi2: "(c1,s) \<rightarrow>* (c1',s') \<Longrightarrow> (c1;c2,s) \<rightarrow>* (c1';c2,s')"
proof(induction rule: star_induct)
  case refl thus ?case by simp
next
  case step
  thus ?case by (metis Semi2 star.step)
qed

lemma semi_comp:
  "\<lbrakk> (c1,s1) \<rightarrow>* (SKIP,s2); (c2,s2) \<rightarrow>* (SKIP,s3) \<rbrakk>
   \<Longrightarrow> (c1;c2, s1) \<rightarrow>* (SKIP,s3)"
by(blast intro: star.step star_semi2 star_trans)

text{* The following proof corresponds to one on the board where one would
show chains of @{text "\<rightarrow>"} and @{text "\<rightarrow>*"} steps. *}

lemma big_to_small:
  "cs \<Rightarrow> t \<Longrightarrow> cs \<rightarrow>* (SKIP,t)"
proof (induction rule: big_step.induct)
  fix s show "(SKIP,s) \<rightarrow>* (SKIP,s)" by simp
next
  fix x a s show "(x ::= a,s) \<rightarrow>* (SKIP, s(x := aval a s))" by auto
next
  fix c1 c2 s1 s2 s3
  assume "(c1,s1) \<rightarrow>* (SKIP,s2)" and "(c2,s2) \<rightarrow>* (SKIP,s3)"
  thus "(c1;c2, s1) \<rightarrow>* (SKIP,s3)" by (rule semi_comp)
next
  fix s::state and b c0 c1 t
  assume "bval b s"
  hence "(IF b THEN c0 ELSE c1,s) \<rightarrow> (c0,s)" by simp
  moreover assume "(c0,s) \<rightarrow>* (SKIP,t)"
  ultimately 
  show "(IF b THEN c0 ELSE c1,s) \<rightarrow>* (SKIP,t)" by (metis star.simps)
next
  fix s::state and b c0 c1 t
  assume "\<not>bval b s"
  hence "(IF b THEN c0 ELSE c1,s) \<rightarrow> (c1,s)" by simp
  moreover assume "(c1,s) \<rightarrow>* (SKIP,t)"
  ultimately 
  show "(IF b THEN c0 ELSE c1,s) \<rightarrow>* (SKIP,t)" by (metis star.simps)
next
  fix b c and s::state
  assume b: "\<not>bval b s"
  let ?if = "IF b THEN c; WHILE b DO c ELSE SKIP"
  have "(WHILE b DO c,s) \<rightarrow> (?if, s)" by blast
  moreover have "(?if,s) \<rightarrow> (SKIP, s)" by (simp add: b)
  ultimately show "(WHILE b DO c,s) \<rightarrow>* (SKIP,s)" by(metis star.refl star.step)
next
  fix b c s s' t
  let ?w  = "WHILE b DO c"
  let ?if = "IF b THEN c; ?w ELSE SKIP"
  assume w: "(?w,s') \<rightarrow>* (SKIP,t)"
  assume c: "(c,s) \<rightarrow>* (SKIP,s')"
  assume b: "bval b s"
  have "(?w,s) \<rightarrow> (?if, s)" by blast
  moreover have "(?if, s) \<rightarrow> (c; ?w, s)" by (simp add: b)
  moreover have "(c; ?w,s) \<rightarrow>* (SKIP,t)" by(rule semi_comp[OF c w])
  ultimately show "(WHILE b DO c,s) \<rightarrow>* (SKIP,t)" by (metis star.simps)
qed

text{* Each case of the induction can be proved automatically: *}
lemma  "cs \<Rightarrow> t \<Longrightarrow> cs \<rightarrow>* (SKIP,t)"
proof (induction rule: big_step.induct)
  case Skip show ?case by blast
next
  case Assign show ?case by blast
next
  case Semi thus ?case by (blast intro: semi_comp)
next
  case IfTrue thus ?case by (blast intro: star.step)
next
  case IfFalse thus ?case by (blast intro: star.step)
next
  case WhileFalse thus ?case
    by (metis star.step star_step1 small_step.IfFalse small_step.While)
next
  case WhileTrue
  thus ?case
    by(metis While semi_comp small_step.IfTrue star.step[of small_step])
qed

lemma small1_big_continue:
  "cs \<rightarrow> cs' \<Longrightarrow> cs' \<Rightarrow> t \<Longrightarrow> cs \<Rightarrow> t"
apply (induction arbitrary: t rule: small_step.induct)
apply auto
done

lemma small_big_continue:
  "cs \<rightarrow>* cs' \<Longrightarrow> cs' \<Rightarrow> t \<Longrightarrow> cs \<Rightarrow> t"
apply (induction rule: star.induct)
apply (auto intro: small1_big_continue)
done

lemma small_to_big: "cs \<rightarrow>* (SKIP,t) \<Longrightarrow> cs \<Rightarrow> t"
by (metis small_big_continue Skip)

text {*
  Finally, the equivalence theorem:
*}
theorem big_iff_small:
  "cs \<Rightarrow> t = cs \<rightarrow>* (SKIP,t)"
by(metis big_to_small small_to_big)


subsection "Final configurations and infinite reductions"

definition "final cs \<longleftrightarrow> \<not>(EX cs'. cs \<rightarrow> cs')"

lemma finalD: "final (c,s) \<Longrightarrow> c = SKIP"
apply(simp add: final_def)
apply(induction c)
apply blast+
done

lemma final_iff_SKIP: "final (c,s) = (c = SKIP)"
by (metis SkipE finalD final_def)

text{* Now we can show that @{text"\<Rightarrow>"} yields a final state iff @{text"\<rightarrow>"}
terminates: *}

lemma big_iff_small_termination:
  "(EX t. cs \<Rightarrow> t) \<longleftrightarrow> (EX cs'. cs \<rightarrow>* cs' \<and> final cs')"
by(simp add: big_iff_small final_iff_SKIP)

text{* This is the same as saying that the absence of a big step result is
equivalent with absence of a terminating small step sequence, i.e.\ with
nontermination.  Since @{text"\<rightarrow>"} is determininistic, there is no difference
between may and must terminate. *}

end
