theory Collecting
imports Complete_Lattice Big_Step ACom
        "~~/src/HOL/ex/Interpretation_with_Defs"
begin

subsection "The generic Step function"

notation
  sup (infixl "\<squnion>" 65) and
  inf (infixl "\<sqinter>" 70) and
  bot ("\<bottom>") and
  top ("\<top>")

fun Step :: "(vname \<Rightarrow> aexp \<Rightarrow> 'a \<Rightarrow> 'a::sup) \<Rightarrow> (bexp \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a acom \<Rightarrow> 'a acom" where
"Step f g S (SKIP {Q}) = (SKIP {S})" |
"Step f g S (x ::= e {Q}) =
  x ::= e {f x e S}" |
"Step f g S (C1; C2) = Step f g S C1; Step f g (post C1) C2" |
"Step f g S (IF b THEN {P1} C1 ELSE {P2} C2 {Q}) =
  IF b THEN {g b S} Step f g P1 C1 ELSE {g (Not b) S} Step f g P2 C2
  {post C1 \<squnion> post C2}" |
"Step f g S ({I} WHILE b DO {P} C {Q}) =
  {S \<squnion> post C} WHILE b DO {g b I} Step f g P C {g (Not b) I}"

(* Could hide f and g like this:
consts fa :: "vname \<Rightarrow> aexp \<Rightarrow> 'a \<Rightarrow> 'a::sup"
       fb :: "bexp \<Rightarrow> 'a \<Rightarrow> 'a::sup"
abbreviation "STEP == Step fa fb"
thm Step.simps[where f = fa and g = fb]
*)

lemma strip_Step[simp]: "strip(Step f g S C) = strip C"
by(induct C arbitrary: S) auto


subsection "Collecting Semantics of Commands"

subsubsection "Annotated commands as a complete lattice"

(* Orderings could also be lifted generically (thus subsuming the
instantiation for preord and order), but then less_eq_acom would need to
become a definition, eg less_eq_acom = lift2 less_eq, and then proofs would
need to unfold this defn first. *)

instantiation acom :: (order) order
begin

fun less_eq_acom :: "('a::order)acom \<Rightarrow> 'a acom \<Rightarrow> bool" where
"(SKIP {P}) \<le> (SKIP {P'}) = (P \<le> P')" |
"(x ::= e {P}) \<le> (x' ::= e' {P'}) = (x=x' \<and> e=e' \<and> P \<le> P')" |
"(C1;C2) \<le> (C1';C2') = (C1 \<le> C1' \<and> C2 \<le> C2')" |
"(IF b THEN {P1} C1 ELSE {P2} C2 {Q}) \<le> (IF b' THEN {P1'} C1' ELSE {P2'} C2' {Q'}) =
  (b=b' \<and> P1 \<le> P1' \<and> C1 \<le> C1' \<and> P2 \<le> P2' \<and> C2 \<le> C2' \<and> Q \<le> Q')" |
"({I} WHILE b DO {P} C {Q}) \<le> ({I'} WHILE b' DO {P'} C' {Q'}) =
  (b=b' \<and> C \<le> C' \<and> I \<le> I' \<and> P \<le> P' \<and> Q \<le> Q')" |
"less_eq_acom _ _ = False"

lemma SKIP_le: "SKIP {S} \<le> c \<longleftrightarrow> (\<exists>S'. c = SKIP {S'} \<and> S \<le> S')"
by (cases c) auto

lemma Assign_le: "x ::= e {S} \<le> c \<longleftrightarrow> (\<exists>S'. c = x ::= e {S'} \<and> S \<le> S')"
by (cases c) auto

lemma Seq_le: "C1;C2 \<le> C \<longleftrightarrow> (\<exists>C1' C2'. C = C1';C2' \<and> C1 \<le> C1' \<and> C2 \<le> C2')"
by (cases C) auto

lemma If_le: "IF b THEN {p1} C1 ELSE {p2} C2 {S} \<le> C \<longleftrightarrow>
  (\<exists>p1' p2' C1' C2' S'. C = IF b THEN {p1'} C1' ELSE {p2'} C2' {S'} \<and>
     p1 \<le> p1' \<and> p2 \<le> p2' \<and> C1 \<le> C1' \<and> C2 \<le> C2' \<and> S \<le> S')"
by (cases C) auto

lemma While_le: "{I} WHILE b DO {p} C {P} \<le> W \<longleftrightarrow>
  (\<exists>I' p' C' P'. W = {I'} WHILE b DO {p'} C' {P'} \<and> C \<le> C' \<and> p \<le> p' \<and> I \<le> I' \<and> P \<le> P')"
by (cases W) auto

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

text_raw{*\snip{subadef}{2}{1}{% *}
fun sub\<^isub>1 :: "'a acom \<Rightarrow> 'a acom" where
"sub\<^isub>1(C\<^isub>1;C\<^isub>2) = C\<^isub>1" |
"sub\<^isub>1(IF b THEN {P\<^isub>1} C\<^isub>1 ELSE {P\<^isub>2} C\<^isub>2 {Q}) = C\<^isub>1" |
"sub\<^isub>1({I} WHILE b DO {P} C {Q}) = C"
text_raw{*}%endsnip*}

text_raw{*\snip{subbdef}{1}{1}{% *}
fun sub\<^isub>2 :: "'a acom \<Rightarrow> 'a acom" where
"sub\<^isub>2(C\<^isub>1;C\<^isub>2) = C\<^isub>2" |
"sub\<^isub>2(IF b THEN {P\<^isub>1} C\<^isub>1 ELSE {P\<^isub>2} C\<^isub>2 {Q}) = C\<^isub>2"
text_raw{*}%endsnip*}

text_raw{*\snip{annoadef}{1}{1}{% *}
fun anno\<^isub>1 :: "'a acom \<Rightarrow> 'a" where
"anno\<^isub>1(IF b THEN {P\<^isub>1} C\<^isub>1 ELSE {P\<^isub>2} C\<^isub>2 {Q}) = P\<^isub>1" |
"anno\<^isub>1({I} WHILE b DO {P} C {Q}) = I"
text_raw{*}%endsnip*}

text_raw{*\snip{annobdef}{1}{2}{% *}
fun anno\<^isub>2 :: "'a acom \<Rightarrow> 'a" where
"anno\<^isub>2(IF b THEN {P\<^isub>1} C\<^isub>1 ELSE {P\<^isub>2} C\<^isub>2 {Q}) = P\<^isub>2" |
"anno\<^isub>2({I} WHILE b DO {P} C {Q}) = P"
text_raw{*}%endsnip*}

fun merge :: "com \<Rightarrow> 'a acom set \<Rightarrow> 'a set acom" where
"merge com.SKIP M = (SKIP {post ` M})" |
"merge (x ::= a) M = (x ::= a {post ` M})" |
"merge (c1;c2) M =
  merge c1 (sub\<^isub>1 ` M); merge c2 (sub\<^isub>2 ` M)" |
"merge (IF b THEN c1 ELSE c2) M =
  IF b THEN {anno\<^isub>1 ` M} merge c1 (sub\<^isub>1 ` M) ELSE {anno\<^isub>2 ` M} merge c2 (sub\<^isub>2 ` M)
  {post ` M}" |
"merge (WHILE b DO c) M =
 {anno\<^isub>1 ` M}
 WHILE b DO {anno\<^isub>2 ` M} merge c (sub\<^isub>1 ` M)
 {post ` M}"

interpretation
  Complete_Lattice "{C. strip C = c}" "map_acom Inter o (merge c)" for c
proof
  case goal1
  have "a:A \<Longrightarrow> map_acom Inter (merge (strip a) A) \<le> a"
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
  proof(simp, induction b arbitrary: c A)
    case SKIP thus ?case by (force simp:SKIP_le)
  next
    case Assign thus ?case by (force simp:Assign_le)
  next
    case Seq from Seq.prems show ?case by(force intro!: Seq.IH simp:Seq_le)
  next
    case If from If.prems show ?case by (force simp: If_le intro!: If.IH)
  next
    case While from While.prems show ?case by(fastforce simp: While_le intro: While.IH)
  qed
next
  case goal3
  have "strip(merge c A) = c"
  proof(induction c arbitrary: A)
    case Seq from Seq.prems show ?case by (fastforce simp: strip_eq_Seq subset_iff intro!: Seq.IH)
  next
    case If from If.prems show ?case by (fastforce intro!: If.IH simp: strip_eq_If)
  next
    case While from While.prems show ?case by(fastforce intro: While.IH simp: strip_eq_While)
  qed auto
  thus ?case by auto
qed

lemma le_post: "c \<le> d \<Longrightarrow> post c \<le> post d"
by(induction c d rule: less_eq_acom.induct) auto


subsubsection "Collecting semantics"

definition "step = Step (\<lambda>x e S. {s(x := aval e s) |s. s : S}) (\<lambda>b S. {s:S. bval b s})"

definition CS :: "com \<Rightarrow> state set acom" where
"CS c = lfp c (step UNIV)"

lemma mono2_Step: fixes C1 C2 :: "'a::semilattice_sup acom"
  assumes "!!x e S1 S2. S1 \<le> S2 \<Longrightarrow> f x e S1 \<le> f x e S2"
          "!!b S1 S2. S1 \<le> S2 \<Longrightarrow> g b S1 \<le> g b S2"
  shows "C1 \<le> C2 \<Longrightarrow> S1 \<le> S2 \<Longrightarrow> Step f g S1 C1 \<le> Step f g S2 C2"
proof(induction C1 C2 arbitrary: S1 S2 rule: less_eq_acom.induct)
  case 2 thus ?case by (fastforce simp: assms(1))
next
  case 3 thus ?case by(simp add: le_post)
next
  case 4 thus ?case
    by(simp add: subset_iff assms(2)) (metis le_post le_supI1 le_supI2)
next
  case 5 thus ?case
    by(simp add: subset_iff assms(2)) (metis le_post le_supI1 le_supI2)
qed auto

lemma mono2_step: "C1 \<le> C2 \<Longrightarrow> S1 \<subseteq> S2 \<Longrightarrow> step S1 C1 \<le> step S2 C2"
unfolding step_def by(rule mono2_Step) auto

lemma mono_step: "mono (step S)"
by(blast intro: monoI mono2_step)

lemma strip_step: "strip(step S C) = strip C"
by (induction C arbitrary: S) (auto simp: step_def)

lemma lfp_cs_unfold: "lfp c (step S) = step S (lfp c (step S))"
apply(rule lfp_unfold[OF _  mono_step])
apply(simp add: strip_step)
done

lemma CS_unfold: "CS c = step UNIV (CS c)"
by (metis CS_def lfp_cs_unfold)

lemma strip_CS[simp]: "strip(CS c) = c"
by(simp add: CS_def index_lfp[simplified])


subsubsection "Relation to big-step semantics"

lemma post_merge: "\<forall> c' \<in> M. strip c' = c \<Longrightarrow> post (merge c M) = post ` M"
proof(induction c arbitrary: M)
  case (Seq c1 c2)
  have "post ` M = post ` sub\<^isub>2 ` M" using Seq.prems by (force simp: strip_eq_Seq)
  moreover have "\<forall> c' \<in> sub\<^isub>2 ` M. strip c' = c2" using Seq.prems by (auto simp: strip_eq_Seq)
  ultimately show ?case using Seq.IH(2)[of "sub\<^isub>2 ` M"] by simp
qed simp_all


lemma post_lfp: "post(lfp c f) = (\<Inter>{post C|C. strip C = c \<and> f C \<le> C})"
by(auto simp add: lfp_def post_merge)

lemma big_step_post_step:
  "\<lbrakk> (c, s) \<Rightarrow> t;  strip C = c;  s \<in> S;  step S C \<le> C \<rbrakk> \<Longrightarrow> t \<in> post C"
proof(induction arbitrary: C S rule: big_step_induct)
  case Skip thus ?case by(auto simp: strip_eq_SKIP step_def)
next
  case Assign thus ?case by(fastforce simp: strip_eq_Assign step_def)
next
  case Seq thus ?case by(fastforce simp: strip_eq_Seq step_def)
next
  case IfTrue thus ?case apply(auto simp: strip_eq_If step_def)
    by (metis (lifting,full_types) mem_Collect_eq set_mp)
next
  case IfFalse thus ?case apply(auto simp: strip_eq_If step_def)
    by (metis (lifting,full_types) mem_Collect_eq set_mp)
next
  case (WhileTrue b s1 c' s2 s3)
  from WhileTrue.prems(1) obtain I P C' Q where "C = {I} WHILE b DO {P} C' {Q}" "strip C' = c'"
    by(auto simp: strip_eq_While)
  from WhileTrue.prems(3) `C = _`
  have "step P C' \<le> C'"  "{s \<in> I. bval b s} \<le> P"  "S \<le> I"  "step (post C') C \<le> C"
    by (auto simp: step_def)
  have "step {s \<in> I. bval b s} C' \<le> C'"
    by (rule order_trans[OF mono2_step[OF order_refl `{s \<in> I. bval b s} \<le> P`] `step P C' \<le> C'`])
  have "s1: {s:I. bval b s}" using `s1 \<in> S` `S \<subseteq> I` `bval b s1` by auto
  note s2_in_post_C' = WhileTrue.IH(1)[OF `strip C' = c'` this `step {s \<in> I. bval b s} C' \<le> C'`]
  from WhileTrue.IH(2)[OF WhileTrue.prems(1) s2_in_post_C' `step (post C') C \<le> C`]
  show ?case .
next
  case (WhileFalse b s1 c') thus ?case by (force simp: strip_eq_While step_def)
qed

lemma big_step_lfp: "\<lbrakk> (c,s) \<Rightarrow> t;  s \<in> S \<rbrakk> \<Longrightarrow> t \<in> post(lfp c (step S))"
by(auto simp add: post_lfp intro: big_step_post_step)

lemma big_step_CS: "(c,s) \<Rightarrow> t \<Longrightarrow> t : post(CS c)"
by(simp add: CS_def big_step_lfp)

end
