theory Collecting1
imports Collecting
begin

subsection "A small step semantics on annotated commands"

text{* The idea: the state is propagated through the annotated command as an
annotation @{term "Some s"}, all other annotations are @{const None}. *}

fun join :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
"join None x = x" |
"join x None = x"

definition bfilter :: "bexp \<Rightarrow> bool \<Rightarrow> state option \<Rightarrow> state option" where
"bfilter b r so =
  (case so of None \<Rightarrow> None | Some s \<Rightarrow> if bval b s = r then Some s else None)"

lemma bfilter_None[simp]: "bfilter b r None = None"
by(simp add: bfilter_def split: option.split)

fun step1 :: "state option \<Rightarrow> state option acom \<Rightarrow> state option acom" where
"step1 so (SKIP {P}) = SKIP {so}" |
"step1 so (x::=e {P}) =
  x ::= e {case so of None \<Rightarrow> None | Some s \<Rightarrow> Some(s(x := aval e s))}" |
"step1 so (c1;c2) = step1 so c1; step1 (post c1) c2" |
"step1 so (IF b THEN c1 ELSE c2 {P}) =
  IF b THEN step1 (bfilter b True so) c1
  ELSE step1 (bfilter b False so) c2
  {join (post c1) (post c2)}" |
"step1 so ({I} WHILE b DO c {P}) =
  {join so (post c)}
  WHILE b DO step1 (bfilter b True I) c
  {bfilter b False I}"

definition "show_acom xs = map_acom (Option.map (show_state xs))"

definition
 "p1 = ''x'' ::= N 2; IF Less (V ''x'') (N 3) THEN ''x'' ::= N 1 ELSE com.SKIP"

definition "p2 =
 ''x'' ::= N 0; WHILE Less (V ''x'') (N 2) DO ''x'' ::= Plus (V ''x'') (N 1)"

value "show_acom [''x'']
 (((step1 None)^^6) (step1 (Some <>) (anno None p2)))"

subsubsection "Relating the small step and the collecting semantics"

hide_const (open) set

abbreviation set :: "'a option acom \<Rightarrow> 'a set acom" where
"set == map_acom Option.set"

definition some :: "'a option \<Rightarrow> nat" where
"some opt = (case opt of Some x \<Rightarrow> 1 | None \<Rightarrow> 0)"

lemma some[simp]: "some None = 0 \<and> some (Some x) = 1"
by(simp add: some_def split:option.split)

fun somes :: "'a option acom \<Rightarrow> nat" where
"somes(SKIP {p}) = some p" |
"somes(x::=e {p}) = some p" |
"somes(c1;c2) = somes c1 + somes c2" |
"somes(IF b THEN c1 ELSE c2 {p}) = somes c1 + somes c2 + some p" |
"somes({i} WHILE b DO c {p}) = some i + somes c + some p"

lemma some_anno_None: "somes(anno None c) = 0"
by(induction c) auto

lemma some_post: "some(post co) \<le> somes co"
by(induction co) auto

lemma some_join:
  "some so1 + some so2 \<le> 1 \<Longrightarrow> some(join so1 so2) = some so1 + some so2"
by(simp add: some_def split: option.splits)

lemma somes_step1: "some so + somes co \<le> 1 \<Longrightarrow>
 somes(step1 so co) + some(post co) = some so + somes co"
proof(induction co arbitrary: so)
  case SKIP thus ?case by simp
next
  case Assign thus ?case by (simp split:option.split)
next
  case (Semi co1 _)
  from Semi.prems Semi.IH(1)[of so] Semi.IH(2)[of "post co1"]
  show ?case by simp
next
  case (If b)
  from If.prems If.IH(1)[of "bfilter b True so"]
       If.prems If.IH(2)[of "bfilter b False so"]
  show ?case
    by (auto simp: bfilter_def some_join split:option.split)
next
  case (While i b c p)
  from While.prems While.IH[of "bfilter b True i"]
  show ?case
    by(auto simp: bfilter_def some_join split:option.split)
qed

lemma post_map_acom[simp]: "post(map_acom f c) = f(post c)"
by(induction c) auto

lemma join_eq_Some: "some so1 + some so2 \<le> 1 \<Longrightarrow>
  join so1 so2 = Some s =
 (so1 = Some s & so2 = None | so1 = None & so2 = Some s)"
apply(cases so1) apply simp
apply(cases so2) apply auto
done

lemma set_bfilter:
  "Option.set (bfilter b r so) = {s : Option.set so. bval b s = r}"
by(auto simp: bfilter_def split: option.splits)

lemma set_join:  "some so1 + some so2 \<le> 1 \<Longrightarrow>
  Option.set (join so1 so2) = Option.set so1 \<union> Option.set so2"
apply(cases so1) apply simp
apply(cases so2) apply auto
done

lemma add_le1_iff: "m + n \<le> (Suc 0) \<longleftrightarrow> (m=0 \<and> n\<le>1 | m\<le>1 & n=0)"
by arith

lemma some_0_iff: "some opt = 0 \<longleftrightarrow> opt = None"
by(auto simp add: some_def split: option.splits)

lemma some_le1[simp]: "some x \<le> Suc 0"
by(auto simp add: some_def split: option.splits)

lemma step1_preserves_le:
  "\<lbrakk> step_cs S cs = cs; Option.set so \<subseteq> S; set co \<le> cs;
    somes co + some so \<le> 1 \<rbrakk> \<Longrightarrow>
  set(step1 so co) \<le> cs"
proof(induction co arbitrary: S cs so)
  case SKIP thus ?case by (clarsimp simp: SKIP_le)
next
  case Assign thus ?case by (fastforce simp: Assign_le split: option.splits)
next
  case (Semi co1 co2)
  from Semi.prems show ?case using some_post[of co1]
    by (fastforce simp add: Semi_le add_le1_iff Semi.IH dest: le_post)
next
  case (If _ co1 co2)
  from If.prems show ?case
    using some_post[of co1] some_post[of co2]
    by (fastforce simp: If_le add_le1_iff some_0_iff set_bfilter subset_iff
      join_eq_Some If.IH dest: le_post)
next
  case (While _ _ co)
  from While.prems show ?case
    using some_post[of co]
    by (fastforce simp: While_le set_bfilter subset_iff join_eq_Some
      add_le1_iff some_0_iff While.IH dest: le_post)
qed

lemma step1_None_preserves_le:
  "\<lbrakk> step_cs S cs = cs; set co \<le> cs; somes co \<le> 1 \<rbrakk> \<Longrightarrow>
  set(step1 None co) \<le> cs"
by(auto dest: step1_preserves_le[of _ _ None])

lemma step1_Some_preserves_le:
  "\<lbrakk> step_cs S cs = cs; s : S; set co \<le> cs; somes co = 0 \<rbrakk> \<Longrightarrow>
  set(step1 (Some s) co) \<le> cs"
by(auto dest: step1_preserves_le[of _ _ "Some s"])

lemma steps_None_preserves_le: assumes "step_cs S cs = cs"
shows "set co \<le> cs \<Longrightarrow> somes co \<le> 1 \<Longrightarrow> set ((step1 None ^^ n) co) \<le> cs"
proof(induction n arbitrary: co)
  case 0 thus ?case by simp
next
  case (Suc n) thus ?case
    using somes_step1[of None co] step1_None_preserves_le[OF assms Suc.prems]
    by(simp add:funpow_swap1 Suc.IH)
qed


definition steps :: "state \<Rightarrow> com \<Rightarrow> nat \<Rightarrow> state option acom" where
"steps s c n = ((step1 None)^^n) (step1 (Some s) (anno None c))"

lemma steps_approx_fix_step_cs: assumes "step_cs S cs = cs" and "s:S"
shows "set (steps s (strip cs) n) \<le> cs"
proof-
  { fix c have "somes (anno None c) = 0" by(induction c) auto }
  note somes_None = this
  let ?cNone = "anno None (strip cs)"
  have "set ?cNone \<le> cs" by(induction cs) auto
  from step1_Some_preserves_le[OF assms this somes_None]
  have 1: "set(step1 (Some s) ?cNone) \<le> cs" .
  have 2: "somes (step1 (Some s) ?cNone) \<le> 1"
    using some_post somes_step1[of "Some s" ?cNone]
    by (simp add:some_anno_None[of "strip cs"])
  from steps_None_preserves_le[OF assms(1) 1 2]
  show ?thesis by(simp add: steps_def)
qed

theorem steps_approx_CS: "s:S \<Longrightarrow> set (steps s c n) \<le> CS S c"
by (metis CS_unfold steps_approx_fix_step_cs strip_CS)

lemma While_final_False: "(WHILE b DO c, s) \<Rightarrow> t \<Longrightarrow> \<not> bval b t"
by(induct "WHILE b DO c" s t rule: big_step_induct) simp_all

lemma step_cs_complete:
  "\<lbrakk> step_cs S c = c; (strip c,s) \<Rightarrow> t; s:S \<rbrakk> \<Longrightarrow> t : post c"
proof(induction c arbitrary: S s t)
  case (While Inv b c P)
  from While.prems have inv: "step_cs {s:Inv. bval b s} c = c"
    and "post c \<subseteq> Inv" and "S \<subseteq> Inv" and "{s:Inv. \<not> bval b s} \<subseteq> P"  by(auto)
  { fix s t have "(WHILE b DO strip c,s) \<Rightarrow> t \<Longrightarrow> s : Inv \<Longrightarrow> t : Inv"
    proof(induction "WHILE b DO strip c" s t rule: big_step_induct)
      case WhileFalse thus ?case by simp
    next
      case (WhileTrue s1 s2 s3)
      from WhileTrue.hyps(5) While.IH[OF inv `(strip c, s1) \<Rightarrow> s2`]
        `s1 : Inv` `post c \<subseteq> Inv` `bval b s1`
      show ?case by auto
    qed
  } note Inv = this
  from  While.prems(2) have "(WHILE b DO strip c, s) \<Rightarrow> t" and "\<not> bval b t"
    by(auto dest: While_final_False)
  from Inv[OF this(1)] `s : S` `S \<subseteq> Inv` have "t : Inv" by blast
  with `{s:Inv. \<not> bval b s} \<subseteq> P` show ?case using `\<not> bval b t` by auto
qed auto

theorem CS_complete: "\<lbrakk> (c,s) \<Rightarrow> t; s:S \<rbrakk> \<Longrightarrow> t : post(CS S c)"
by (metis CS_unfold step_cs_complete strip_CS)

end
