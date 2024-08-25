(*  Title:      HOL/Bali/Basis.thy
    Author:     David von Oheimb
*)
subsection \<open>Definitions extending HOL as logical basis of Bali\<close>

theory Basis
imports Main
begin

subsubsection "misc"

ML \<open>fun strip_tac ctxt i = REPEAT (resolve_tac ctxt [impI, allI] i)\<close>

declare if_split_asm  [split] option.split [split] option.split_asm [split]
setup \<open>map_theory_simpset (fn ctxt => ctxt addloop ("split_all_tac", split_all_tac))\<close>
declare if_weak_cong [cong del] option.case_cong_weak [cong del]
declare length_Suc_conv [iff]

lemma Collect_split_eq: "{p. P (case_prod f p)} = {(a,b). P (f a b)}"
  by auto

lemma subset_insertD: "A \<subseteq> insert x B \<Longrightarrow> A \<subseteq> B \<and> x \<notin> A \<or> (\<exists>B'. A = insert x B' \<and> B' \<subseteq> B)"
  apply (case_tac "x \<in> A")
   apply (rule disjI2)
   apply (rule_tac x = "A - {x}" in exI)
   apply fast+
  done

abbreviation nat3 :: nat  ("3") where "3 \<equiv> Suc 2"
abbreviation nat4 :: nat  ("4") where "4 \<equiv> Suc 3"

(* irrefl_tranclI in Transitive_Closure.thy is more general *)
lemma irrefl_tranclI': "r\<inverse> \<inter> r\<^sup>+ = {} \<Longrightarrow> \<forall>x. (x, x) \<notin> r\<^sup>+"
  by (blast elim: tranclE dest: trancl_into_rtrancl)


lemma trancl_rtrancl_trancl: "\<lbrakk>(x, y) \<in> r\<^sup>+; (y, z) \<in> r\<^sup>*\<rbrakk> \<Longrightarrow> (x, z) \<in> r\<^sup>+"
  by (auto dest: tranclD rtrancl_trans rtrancl_into_trancl2)

lemma rtrancl_into_trancl3: "\<lbrakk>(a, b) \<in> r\<^sup>*; a \<noteq> b\<rbrakk> \<Longrightarrow> (a, b) \<in> r\<^sup>+"
  apply (drule rtranclD)
  apply auto
  done

lemma rtrancl_into_rtrancl2: "\<lbrakk>(a, b) \<in>  r; (b, c) \<in> r\<^sup>*\<rbrakk> \<Longrightarrow> (a, c) \<in> r\<^sup>*"
  by (auto intro: rtrancl_trans)

lemma triangle_lemma:
  assumes unique: "\<And>a b c. \<lbrakk>(a,b)\<in>r; (a,c)\<in>r\<rbrakk> \<Longrightarrow> b = c"
    and ax: "(a,x)\<in>r\<^sup>*" and ay: "(a,y)\<in>r\<^sup>*"
  shows "(x,y)\<in>r\<^sup>* \<or> (y,x)\<in>r\<^sup>*"
  using ax ay
proof (induct rule: converse_rtrancl_induct)
  assume "(x,y)\<in>r\<^sup>*"
  then show ?thesis by blast
next
  fix a v
  assume a_v_r: "(a, v) \<in> r"
    and v_x_rt: "(v, x) \<in> r\<^sup>*"
    and a_y_rt: "(a, y) \<in> r\<^sup>*"
    and hyp: "(v, y) \<in> r\<^sup>* \<Longrightarrow> (x, y) \<in> r\<^sup>* \<or> (y, x) \<in> r\<^sup>*"
  from a_y_rt show "(x, y) \<in> r\<^sup>* \<or> (y, x) \<in> r\<^sup>*"
  proof (cases rule: converse_rtranclE)
    assume "a = y"
    with a_v_r v_x_rt have "(y,x) \<in> r\<^sup>*"
      by (auto intro: rtrancl_trans)
    then show ?thesis by blast
  next
    fix w
    assume a_w_r: "(a, w) \<in> r"
      and w_y_rt: "(w, y) \<in> r\<^sup>*"
    from a_v_r a_w_r unique have "v=w" by auto
    with w_y_rt hyp show ?thesis by blast
  qed
qed


lemma rtrancl_cases:
  assumes "(a,b)\<in>r\<^sup>*"
  obtains (Refl) "a = b"
    | (Trancl) "(a,b)\<in>r\<^sup>+"
  apply (rule rtranclE [OF assms])
   apply (auto dest: rtrancl_into_trancl1)
  done

lemma Ball_weaken: "\<lbrakk>Ball s P; \<And> x. P x\<longrightarrow>Q x\<rbrakk>\<Longrightarrow>Ball s Q"
  by auto

lemma finite_SetCompr2:
  "finite {f y x |x y. P y}" if "finite (Collect P)"
    "\<forall>y. P y \<longrightarrow> finite (range (f y))"
proof -
  have "{f y x |x y. P y} = (\<Union>y\<in>Collect P. range (f y))"
    by auto
  with that show ?thesis by simp
qed

lemma list_all2_trans: "\<forall>a b c. P1 a b \<longrightarrow> P2 b c \<longrightarrow> P3 a c \<Longrightarrow>
    \<forall>xs2 xs3. list_all2 P1 xs1 xs2 \<longrightarrow> list_all2 P2 xs2 xs3 \<longrightarrow> list_all2 P3 xs1 xs3"
  apply (induct_tac xs1)
   apply simp
  apply (rule allI)
  apply (induct_tac xs2)
   apply simp
  apply (rule allI)
  apply (induct_tac xs3)
   apply auto
  done


subsubsection "pairs"

lemma surjective_pairing5:
  "p = (fst p, fst (snd p), fst (snd (snd p)), fst (snd (snd (snd p))),
    snd (snd (snd (snd p))))"
  by auto

lemma fst_splitE [elim!]:
  assumes "fst s' = x'"
  obtains x s where "s' = (x,s)" and "x = x'"
  using assms by (cases s') auto

lemma fst_in_set_lemma: "(x, y) \<in> set l \<Longrightarrow> x \<in> fst ` set l"
  by (induct l) auto


subsubsection "quantifiers"

lemma All_Ex_refl_eq2 [simp]: "(\<forall>x. (\<exists>b. x = f b \<and> Q b) \<longrightarrow> P x) = (\<forall>b. Q b \<longrightarrow> P (f b))"
  by auto

lemma ex_ex_miniscope1 [simp]: "(\<exists>w v. P w v \<and> Q v) = (\<exists>v. (\<exists>w. P w v) \<and> Q v)"
  by auto

lemma ex_miniscope2 [simp]: "(\<exists>v. P v \<and> Q \<and> R v) = (Q \<and> (\<exists>v. P v \<and> R v))"
  by auto

lemma ex_reorder31: "(\<exists>z x y. P x y z) = (\<exists>x y z. P x y z)"
  by auto

lemma All_Ex_refl_eq1 [simp]: "(\<forall>x. (\<exists>b. x = f b) \<longrightarrow> P x) = (\<forall>b. P (f b))"
  by auto


subsubsection "sums"

notation case_sum  (infixr "'(+')" 80)

primrec the_Inl :: "'a + 'b \<Rightarrow> 'a"
  where "the_Inl (Inl a) = a"

primrec the_Inr :: "'a + 'b \<Rightarrow> 'b"
  where "the_Inr (Inr b) = b"

datatype ('a, 'b, 'c) sum3 = In1 'a | In2 'b | In3 'c

primrec the_In1 :: "('a, 'b, 'c) sum3 \<Rightarrow> 'a"
  where "the_In1 (In1 a) = a"

primrec the_In2 :: "('a, 'b, 'c) sum3 \<Rightarrow> 'b"
  where "the_In2 (In2 b) = b"

primrec the_In3 :: "('a, 'b, 'c) sum3 \<Rightarrow> 'c"
  where "the_In3 (In3 c) = c"

abbreviation In1l :: "'al \<Rightarrow> ('al + 'ar, 'b, 'c) sum3"
  where "In1l e \<equiv> In1 (Inl e)"

abbreviation In1r :: "'ar \<Rightarrow> ('al + 'ar, 'b, 'c) sum3"
  where "In1r c \<equiv> In1 (Inr c)"

abbreviation the_In1l :: "('al + 'ar, 'b, 'c) sum3 \<Rightarrow> 'al"
  where "the_In1l \<equiv> the_Inl \<circ> the_In1"

abbreviation the_In1r :: "('al + 'ar, 'b, 'c) sum3 \<Rightarrow> 'ar"
  where "the_In1r \<equiv> the_Inr \<circ> the_In1"

ML \<open>
fun sum3_instantiate ctxt thm =
  map (fn s =>
    simplify (ctxt delsimps @{thms not_None_eq})
      (Rule_Insts.read_instantiate ctxt [((("t", 0), Position.none), "In" ^ s ^ " x")] ["x"] thm))
    ["1l","2","3","1r"]
\<close>
(* e.g. lemmas is_stmt_rews = is_stmt_def [of "In1l x", simplified] *)


subsubsection "quantifiers for option type"

syntax
  "_Oall" :: "[pttrn, 'a option, bool] \<Rightarrow> bool"   ("(3! _:_:/ _)" [0,0,10] 10)
  "_Oex"  :: "[pttrn, 'a option, bool] \<Rightarrow> bool"   ("(3? _:_:/ _)" [0,0,10] 10)

syntax (symbols)
  "_Oall" :: "[pttrn, 'a option, bool] \<Rightarrow> bool"   ("(3\<forall>_\<in>_:/ _)"  [0,0,10] 10)
  "_Oex"  :: "[pttrn, 'a option, bool] \<Rightarrow> bool"   ("(3\<exists>_\<in>_:/ _)"  [0,0,10] 10)

syntax_consts
  "_Oall" \<rightleftharpoons> Ball and
  "_Oex" \<rightleftharpoons> Bex

translations
  "\<forall>x\<in>A: P" \<rightleftharpoons> "\<forall>x\<in>CONST set_option A. P"
  "\<exists>x\<in>A: P" \<rightleftharpoons> "\<exists>x\<in>CONST set_option A. P"


subsubsection "Special map update"

text\<open>Deemed too special for theory Map.\<close>

definition chg_map :: "('b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)"
  where "chg_map f a m = (case m a of None \<Rightarrow> m | Some b \<Rightarrow> m(a\<mapsto>f b))"

lemma chg_map_new[simp]: "m a = None \<Longrightarrow> chg_map f a m = m"
  unfolding chg_map_def by auto

lemma chg_map_upd[simp]: "m a = Some b \<Longrightarrow> chg_map f a m = m(a\<mapsto>f b)"
  unfolding chg_map_def by auto

lemma chg_map_other [simp]: "a \<noteq> b \<Longrightarrow> chg_map f a m b = m b"
  by (auto simp: chg_map_def)


subsubsection "unique association lists"

definition unique :: "('a \<times> 'b) list \<Rightarrow> bool"
  where "unique = distinct \<circ> map fst"

lemma uniqueD: "unique l \<Longrightarrow> (x, y) \<in> set l \<Longrightarrow> (x', y') \<in> set l \<Longrightarrow> x = x' \<Longrightarrow> y = y'"
  unfolding unique_def o_def
  by (induct l) (auto dest: fst_in_set_lemma)

lemma unique_Nil [simp]: "unique []"
  by (simp add: unique_def)

lemma unique_Cons [simp]: "unique ((x,y)#l) = (unique l \<and> (\<forall>y. (x,y) \<notin> set l))"
  by (auto simp: unique_def dest: fst_in_set_lemma)

lemma unique_ConsD: "unique (x#xs) \<Longrightarrow> unique xs"
  by (simp add: unique_def)

lemma unique_single [simp]: "\<And>p. unique [p]"
  by simp

lemma unique_append [rule_format (no_asm)]: "unique l' \<Longrightarrow> unique l \<Longrightarrow>
    (\<forall>(x,y)\<in>set l. \<forall>(x',y')\<in>set l'. x' \<noteq> x) \<longrightarrow> unique (l @ l')"
  by (induct l) (auto dest: fst_in_set_lemma)

lemma unique_map_inj: "unique l \<Longrightarrow> inj f \<Longrightarrow> unique (map (\<lambda>(k,x). (f k, g k x)) l)"
  by (induct l) (auto dest: fst_in_set_lemma simp add: inj_eq)

lemma map_of_SomeI: "unique l \<Longrightarrow> (k, x) \<in> set l \<Longrightarrow> map_of l k = Some x"
  by (induct l) auto


subsubsection "list patterns"

definition lsplit :: "[['a, 'a list] \<Rightarrow> 'b, 'a list] \<Rightarrow> 'b"
  where "lsplit = (\<lambda>f l. f (hd l) (tl l))"

text \<open>list patterns -- extends pre-defined type "pttrn" used in abstractions\<close>
syntax
  "_lpttrn" :: "[pttrn, pttrn] \<Rightarrow> pttrn"    ("_#/_" [901,900] 900)
syntax_consts
  "_lpttrn" \<rightleftharpoons> lsplit
translations
  "\<lambda>y # x # xs. b" \<rightleftharpoons> "CONST lsplit (\<lambda>y x # xs. b)"
  "\<lambda>x # xs. b" \<rightleftharpoons> "CONST lsplit (\<lambda>x xs. b)"

lemma lsplit [simp]: "lsplit c (x#xs) = c x xs"
  by (simp add: lsplit_def)

lemma lsplit2 [simp]: "lsplit P (x#xs) y z = P x xs y z"
  by (simp add: lsplit_def)

end
