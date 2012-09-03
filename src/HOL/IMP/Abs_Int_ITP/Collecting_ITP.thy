theory Collecting_ITP
imports Complete_Lattice_ix "ACom_ITP"
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
"(SKIP {S}) \<le> (SKIP {S'}) = (S \<le> S')" |
"(x ::= e {S}) \<le> (x' ::= e' {S'}) = (x=x' \<and> e=e' \<and> S \<le> S')" |
"(c1;c2) \<le> (c1';c2') = (c1 \<le> c1' \<and> c2 \<le> c2')" |
"(IF b THEN c1 ELSE c2 {S}) \<le> (IF b' THEN c1' ELSE c2' {S'}) =
  (b=b' \<and> c1 \<le> c1' \<and> c2 \<le> c2' \<and> S \<le> S')" |
"({Inv} WHILE b DO c {P}) \<le> ({Inv'} WHILE b' DO c' {P'}) =
  (b=b' \<and> c \<le> c' \<and> Inv \<le> Inv' \<and> P \<le> P')" |
"less_eq_acom _ _ = False"

lemma SKIP_le: "SKIP {S} \<le> c \<longleftrightarrow> (\<exists>S'. c = SKIP {S'} \<and> S \<le> S')"
by (cases c) auto

lemma Assign_le: "x ::= e {S} \<le> c \<longleftrightarrow> (\<exists>S'. c = x ::= e {S'} \<and> S \<le> S')"
by (cases c) auto

lemma Seq_le: "c1;c2 \<le> c \<longleftrightarrow> (\<exists>c1' c2'. c = c1';c2' \<and> c1 \<le> c1' \<and> c2 \<le> c2')"
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
  apply (auto intro: le_trans simp: SKIP_le Assign_le Seq_le If_le While_le)
  done
next
  case goal4 thus ?case
  apply(induct x y rule: less_eq_acom.induct)
  apply (auto intro: le_antisym)
  done
qed

end

fun sub\<^isub>1 :: "'a acom \<Rightarrow> 'a acom" where
"sub\<^isub>1(c1;c2) = c1" |
"sub\<^isub>1(IF b THEN c1 ELSE c2 {S}) = c1" |
"sub\<^isub>1({I} WHILE b DO c {P}) = c"

fun sub\<^isub>2 :: "'a acom \<Rightarrow> 'a acom" where
"sub\<^isub>2(c1;c2) = c2" |
"sub\<^isub>2(IF b THEN c1 ELSE c2 {S}) = c2"

fun invar :: "'a acom \<Rightarrow> 'a" where
"invar({I} WHILE b DO c {P}) = I"

fun lift :: "('a set \<Rightarrow> 'b) \<Rightarrow> com \<Rightarrow> 'a acom set \<Rightarrow> 'b acom"
where
"lift F com.SKIP M = (SKIP {F (post ` M)})" |
"lift F (x ::= a) M = (x ::= a {F (post ` M)})" |
"lift F (c1;c2) M =
  lift F c1 (sub\<^isub>1 ` M); lift F c2 (sub\<^isub>2 ` M)" |
"lift F (IF b THEN c1 ELSE c2) M =
  IF b THEN lift F c1 (sub\<^isub>1 ` M) ELSE lift F c2 (sub\<^isub>2 ` M)
  {F (post ` M)}" |
"lift F (WHILE b DO c) M =
 {F (invar ` M)}
 WHILE b DO lift F c (sub\<^isub>1 ` M)
 {F (post ` M)}"

interpretation Complete_Lattice_ix "%c. {c'. strip c' = c}" "lift Inter"
proof
  case goal1
  have "a:A \<Longrightarrow> lift Inter (strip a) A \<le> a"
  proof(induction a arbitrary: A)
    case Seq from Seq.prems show ?case by(force intro!: Seq.IH)
  next
    case If from If.prems show ?case by(force intro!: If.IH)
  next
    case While from While.prems show ?case by(force intro!: While.IH)
  qed force+
  with goal1 show ?case by auto
next
  case goal2
  thus ?case
  proof(induction b arbitrary: i A)
    case SKIP thus ?case by (force simp:SKIP_le)
  next
    case Assign thus ?case by (force simp:Assign_le)
  next
    case Seq from Seq.prems show ?case
      by (force intro!: Seq.IH simp:Seq_le)
  next
    case If from If.prems show ?case by (force simp: If_le intro!: If.IH)
  next
    case While from While.prems show ?case
      by(fastforce simp: While_le intro: While.IH)
  qed
next
  case goal3
  have "strip(lift Inter i A) = i"
  proof(induction i arbitrary: A)
    case Seq from Seq.prems show ?case
      by (fastforce simp: strip_eq_Seq subset_iff intro!: Seq.IH)
  next
    case If from If.prems show ?case
      by (fastforce intro!: If.IH simp: strip_eq_If)
  next
    case While from While.prems show ?case
      by(fastforce intro: While.IH simp: strip_eq_While)
  qed auto
  thus ?case by auto
qed

lemma le_post: "c \<le> d \<Longrightarrow> post c \<le> post d"
by(induction c d rule: less_eq_acom.induct) auto

subsubsection "Collecting semantics"

fun step :: "state set \<Rightarrow> state set acom \<Rightarrow> state set acom" where
"step S (SKIP {P}) = (SKIP {S})" |
"step S (x ::= e {P}) =
  (x ::= e {{s'. EX s:S. s' = s(x := aval e s)}})" |
"step S (c1; c2) = step S c1; step (post c1) c2" |
"step S (IF b THEN c1 ELSE c2 {P}) =
   IF b THEN step {s:S. bval b s} c1 ELSE step {s:S. \<not> bval b s} c2
   {post c1 \<union> post c2}" |
"step S ({Inv} WHILE b DO c {P}) =
  {S \<union> post c} WHILE b DO (step {s:Inv. bval b s} c) {{s:Inv. \<not> bval b s}}"

definition CS :: "com \<Rightarrow> state set acom" where
"CS c = lfp (step UNIV) c"

lemma mono2_step: "c1 \<le> c2 \<Longrightarrow> S1 \<subseteq> S2 \<Longrightarrow> step S1 c1 \<le> step S2 c2"
proof(induction c1 c2 arbitrary: S1 S2 rule: less_eq_acom.induct)
  case 2 thus ?case by fastforce
next
  case 3 thus ?case by(simp add: le_post)
next
  case 4 thus ?case by(simp add: subset_iff)(metis le_post set_mp)+
next
  case 5 thus ?case by(simp add: subset_iff) (metis le_post set_mp)
qed auto

lemma mono_step: "mono (step S)"
by(blast intro: monoI mono2_step)

lemma strip_step: "strip(step S c) = strip c"
by (induction c arbitrary: S) auto

lemma lfp_cs_unfold: "lfp (step S) c = step S (lfp (step S) c)"
apply(rule lfp_unfold[OF _  mono_step])
apply(simp add: strip_step)
done

lemma CS_unfold: "CS c = step UNIV (CS c)"
by (metis CS_def lfp_cs_unfold)

lemma strip_CS[simp]: "strip(CS c) = c"
by(simp add: CS_def index_lfp[simplified])

end
