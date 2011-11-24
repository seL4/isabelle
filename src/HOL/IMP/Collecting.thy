theory Collecting
imports Complete_Lattice_ix ACom
begin

subsection "Collecting Semantics of Commands"

subsubsection "Annotated commands as a complete lattice"

(* Orderings could also be lifted generically (thus subsuming the
instantiation for preord and order), but then less_eq_acom would need to
become a definition, eg less_eq_acom = lift2 less_eq, and then proofs would
need to unfold this defn first. *)

instantiation acom :: (order) order
begin

fun less_eq_acom :: "('a::order)acom \<Rightarrow> 'a acom \<Rightarrow> bool" where
"less_eq_acom (SKIP {S}) (SKIP {S'}) = (S \<le> S')" |
"less_eq_acom (x ::= e {S}) (x' ::= e' {S'}) = (x=x' \<and> e=e' \<and> S \<le> S')" |
"less_eq_acom (c1;c2) (c1';c2') = (less_eq_acom c1 c1' \<and> less_eq_acom c2 c2')" |
"less_eq_acom (IF b THEN c1 ELSE c2 {S}) (IF b' THEN c1' ELSE c2' {S'}) =
  (b=b' \<and> less_eq_acom c1 c1' \<and> less_eq_acom c2 c2' \<and> S \<le> S')" |
"less_eq_acom ({Inv} WHILE b DO c {P}) ({Inv'} WHILE b' DO c' {P'}) =
  (b=b' \<and> less_eq_acom c c' \<and> Inv \<le> Inv' \<and> P \<le> P')" |
"less_eq_acom _ _ = False"

lemma SKIP_le: "SKIP {S} \<le> c \<longleftrightarrow> (\<exists>S'. c = SKIP {S'} \<and> S \<le> S')"
by (cases c) auto

lemma Assign_le: "x ::= e {S} \<le> c \<longleftrightarrow> (\<exists>S'. c = x ::= e {S'} \<and> S \<le> S')"
by (cases c) auto

lemma Semi_le: "c1;c2 \<le> c \<longleftrightarrow> (\<exists>c1' c2'. c = c1';c2' \<and> c1 \<le> c1' \<and> c2 \<le> c2')"
by (cases c) auto

lemma If_le: "IF b THEN c1 ELSE c2 {S} \<le> c \<longleftrightarrow>
  (\<exists>c1' c2' S'. c= IF b THEN c1' ELSE c2' {S'} \<and> c1 \<le> c1' \<and> c2 \<le> c2' \<and> S \<le> S')"
by (cases c) auto

lemma While_le: "{Inv} WHILE b DO c {P} \<le> w \<longleftrightarrow>
  (\<exists>Inv' c' P'. w = {Inv'} WHILE b DO c' {P'} \<and> c \<le> c' \<and> Inv \<le> Inv' \<and> P \<le> P')"
by (cases w) auto

definition less_acom :: "'a acom \<Rightarrow> 'a acom \<Rightarrow> bool" where
"less_acom x y = (x \<le> y \<and> \<not> y \<le> x)"

instance
proof
  case goal1 show ?case by(simp add: less_acom_def)
next
  case goal2 thus ?case by (induct x) auto
next
  case goal3 thus ?case
  apply(induct x y arbitrary: z rule: less_eq_acom.induct)
  apply (auto intro: le_trans simp: SKIP_le Assign_le Semi_le If_le While_le)
  done
next
  case goal4 thus ?case
  apply(induct x y rule: less_eq_acom.induct)
  apply (auto intro: le_antisym)
  done
qed

end

fun lift :: "('a set set \<Rightarrow> 'a set) \<Rightarrow> com \<Rightarrow> 'a set acom set \<Rightarrow> 'a set acom"
where
"lift F com.SKIP M = (SKIP {F {P. SKIP {P} : M}})" |
"lift F (x ::= a) M = (x ::= a {F {P. x::=a {P} : M}})" |
"lift F (c1;c2) M =
  (lift F c1 {c1. \<exists>c2. c1;c2 : M}); (lift F c2 {c2. \<exists>c1. c1;c2 : M})" |
"lift F (IF b THEN c1 ELSE c2) M =
  IF b THEN lift F c1 {c1. \<exists>c2 P. IF b THEN c1 ELSE c2 {P} : M}
       ELSE lift F c2 {c2. \<exists>c1 P. IF b THEN c1 ELSE c2 {P} : M}
  {F {P. \<exists>c1 c2. IF b THEN c1 ELSE c2 {P} : M}}" |
"lift F (WHILE b DO c) M =
 {F {I. \<exists>c P. {I} WHILE b DO c {P} : M}}
 WHILE b DO lift F c {c. \<exists>I P. {I} WHILE b DO c {P} : M}
 {F {P. \<exists>I c. {I} WHILE b DO c {P} : M}}"

interpretation Complete_Lattice_ix strip "lift Inter"
proof
  case goal1
  have "a:A \<Longrightarrow> lift Inter (strip a) A \<le> a"
  proof(induction a arbitrary: A)
    case Semi from Semi.prems show ?case by(fastforce intro!: Semi.IH)
  next
    case If from If.prems show ?case by(fastforce intro!: If.IH)
  next
    case While from While.prems show ?case by(fastforce intro!: While.IH)
  qed auto
  with goal1 show ?case by auto
next
  case goal2
  thus ?case
  proof(induction b arbitrary: i A)
    case Semi from Semi.prems show ?case by (fastforce intro!: Semi.IH)
  next
    case If from If.prems show ?case by (fastforce intro!: If.IH)
  next
    case While from While.prems show ?case by(fastforce intro: While.IH)
  qed fastforce+
next
  case goal3
  thus ?case
  proof(induction i arbitrary: A)
    case Semi from Semi.prems show ?case by (fastforce intro!: Semi.IH)
  next
    case If from If.prems show ?case by (fastforce intro!: If.IH)
  next
    case While from While.prems show ?case by(fastforce intro: While.IH)
  qed auto
qed

lemma le_post: "c \<le> d \<Longrightarrow> post c \<le> post d"
by(induction c d rule: less_eq_acom.induct) auto

lemma le_strip: "c \<le> d \<Longrightarrow> strip c = strip d"
by(induction c d rule: less_eq_acom.induct) auto

lemma le_SKIP_iff: "c \<le> SKIP {P'} \<longleftrightarrow> (EX P. c = SKIP {P} \<and> P \<le> P')"
by (cases c) simp_all

lemma le_Assign_iff: "c \<le> x::=e {P'} \<longleftrightarrow> (EX P. c = x::=e {P} \<and> P \<le> P')"
by (cases c) simp_all

lemma le_Semi_iff: "c \<le> d1;d2 \<longleftrightarrow> (EX c1 c2. c = c1;c2 \<and> c1 \<le> d1 \<and> c2 \<le> d2)"
by (cases c) simp_all

lemma le_If_iff: "c \<le> IF b THEN d1 ELSE d2 {P'} \<longleftrightarrow>
  (EX c1 c2 P. c = IF b THEN c1 ELSE c2 {P} \<and> c1 \<le> d1 \<and> c2 \<le> d2 \<and> P \<le> P')"
by (cases c) simp_all

lemma le_While_iff: "c \<le> {I'} WHILE b DO d {P'} \<longleftrightarrow>
  (EX I c' P. c = {I} WHILE b DO c' {P} \<and> I \<le> I' \<and> c' \<le> d \<and> P \<le> P')"
by (cases c) auto


subsubsection "Collecting semantics"

fun step_cs :: "state set \<Rightarrow> state set acom \<Rightarrow> state set acom" where
"step_cs S (SKIP {P}) = (SKIP {S})" |
"step_cs S (x ::= e {P}) =
  (x ::= e {{s'. EX s:S. s' = s(x := aval e s)}})" |
"step_cs S (c1; c2) = step_cs S c1; step_cs (post c1) c2" |
"step_cs S (IF b THEN c1 ELSE c2 {P}) =
   IF b THEN step_cs {s:S. bval b s} c1 ELSE step_cs {s:S. \<not> bval b s} c2
   {post c1 \<union> post c2}" |
"step_cs S ({Inv} WHILE b DO c {P}) =
  {S \<union> post c} WHILE b DO (step_cs {s:Inv. bval b s} c) {{s:Inv. \<not> bval b s}}"

definition CS :: "state set \<Rightarrow> com \<Rightarrow> state set acom" where
"CS S c = lfp c (step_cs S)"

lemma mono_step_cs_aux: "x \<le> y \<Longrightarrow> S \<subseteq> T \<Longrightarrow> step_cs S x \<le> step_cs T y"
proof(induction x y arbitrary: S T rule: less_eq_acom.induct)
  case 2 thus ?case by fastforce
next
  case 3 thus ?case by(simp add: le_post)
next
  case 4 thus ?case by(simp add: subset_iff)(metis le_post set_mp)+
next
  case 5 thus ?case by(simp add: subset_iff) (metis le_post set_mp)
qed auto

lemma mono_step_cs: "mono (step_cs S)"
by(blast intro: monoI mono_step_cs_aux)

lemma strip_step_cs: "strip(step_cs S c) = strip c"
by (induction c arbitrary: S) auto

lemmas lfp_cs_unfold = lfp_unfold[OF strip_step_cs mono_step_cs]

lemma CS_unfold: "CS S c = step_cs S (CS S c)"
by (metis CS_def lfp_cs_unfold)

lemma strip_CS[simp]: "strip(CS S c) = c"
by(simp add: CS_def)

end
