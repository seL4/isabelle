(* Author: Tobias Nipkow *)

theory Abs_Int0
imports Abs_State
begin

subsection "Computable Abstract Interpretation"

text{* Abstract interpretation over type @{text st} instead of
functions. *}

context Gamma
begin

fun aval' :: "aexp \<Rightarrow> 'av st \<Rightarrow> 'av" where
"aval' (N n) S = num' n" |
"aval' (V x) S = lookup S x" |
"aval' (Plus a1 a2) S = plus' (aval' a1 S) (aval' a2 S)"

lemma aval'_sound: "s : \<gamma>\<^isub>f S \<Longrightarrow> aval a s : \<gamma>(aval' a S)"
by (induction a) (auto simp: gamma_num' gamma_plus' \<gamma>_st_def lookup_def)

end

text{* The for-clause (here and elsewhere) only serves the purpose of fixing
the name of the type parameter @{typ 'av} which would otherwise be renamed to
@{typ 'a}. *}

locale Abs_Int = Gamma where \<gamma>=\<gamma> for \<gamma> :: "'av::SL_top \<Rightarrow> val set"
begin

fun step' :: "'av st option \<Rightarrow> 'av st option acom \<Rightarrow> 'av st option acom" where
"step' S (SKIP {P}) = (SKIP {S})" |
"step' S (x ::= e {P}) =
  x ::= e {case S of None \<Rightarrow> None | Some S \<Rightarrow> Some(update S x (aval' e S))}" |
"step' S (c1; c2) = step' S c1; step' (post c1) c2" |
"step' S (IF b THEN c1 ELSE c2 {P}) =
  (let c1' = step' S c1; c2' = step' S c2
   in IF b THEN c1' ELSE c2' {post c1 \<squnion> post c2})" |
"step' S ({Inv} WHILE b DO c {P}) =
   {S \<squnion> post c} WHILE b DO step' Inv c {Inv}"

definition AI :: "com \<Rightarrow> 'av st option acom option" where
"AI = lpfp\<^isub>c (step' \<top>)"


lemma strip_step'[simp]: "strip(step' S c) = strip c"
by(induct c arbitrary: S) (simp_all add: Let_def)


text{* Soundness: *}

lemma in_gamma_update:
  "\<lbrakk> s : \<gamma>\<^isub>f S; i : \<gamma> a \<rbrakk> \<Longrightarrow> s(x := i) : \<gamma>\<^isub>f(update S x a)"
by(simp add: \<gamma>_st_def lookup_update)

text{* The soundness proofs are textually identical to the ones for the step
function operating on states as functions. *}

lemma step_preserves_le:
  "\<lbrakk> S \<subseteq> \<gamma>\<^isub>o S'; c \<le> \<gamma>\<^isub>c c' \<rbrakk> \<Longrightarrow> step S c \<le> \<gamma>\<^isub>c (step' S' c')"
proof(induction c arbitrary: c' S S')
  case SKIP thus ?case by(auto simp:SKIP_le map_acom_SKIP)
next
  case Assign thus ?case
    by (fastforce simp: Assign_le  map_acom_Assign intro: aval'_sound in_gamma_update
      split: option.splits del:subsetD)
next
  case Semi thus ?case apply (auto simp: Semi_le map_acom_Semi)
    by (metis le_post post_map_acom)
next
  case (If b c1 c2 P)
  then obtain c1' c2' P' where
      "c' = IF b THEN c1' ELSE c2' {P'}"
      "P \<subseteq> \<gamma>\<^isub>o P'" "c1 \<le> \<gamma>\<^isub>c c1'" "c2 \<le> \<gamma>\<^isub>c c2'"
    by (fastforce simp: If_le map_acom_If)
  moreover have "post c1 \<subseteq> \<gamma>\<^isub>o(post c1' \<squnion> post c2')"
    by (metis (no_types) `c1 \<le> \<gamma>\<^isub>c c1'` join_ge1 le_post mono_gamma_o order_trans post_map_acom)
  moreover have "post c2 \<subseteq> \<gamma>\<^isub>o(post c1' \<squnion> post c2')"
    by (metis (no_types) `c2 \<le> \<gamma>\<^isub>c c2'` join_ge2 le_post mono_gamma_o order_trans post_map_acom)
  ultimately show ?case using `S \<subseteq> \<gamma>\<^isub>o S'` by (simp add: If.IH subset_iff)
next
  case (While I b c1 P)
  then obtain c1' I' P' where
    "c' = {I'} WHILE b DO c1' {P'}"
    "I \<subseteq> \<gamma>\<^isub>o I'" "P \<subseteq> \<gamma>\<^isub>o P'" "c1 \<le> \<gamma>\<^isub>c c1'"
    by (fastforce simp: map_acom_While While_le)
  moreover have "S \<union> post c1 \<subseteq> \<gamma>\<^isub>o (S' \<squnion> post c1')"
    using `S \<subseteq> \<gamma>\<^isub>o S'` le_post[OF `c1 \<le> \<gamma>\<^isub>c c1'`, simplified]
    by (metis (no_types) join_ge1 join_ge2 le_sup_iff mono_gamma_o order_trans)
  ultimately show ?case by (simp add: While.IH subset_iff)
qed

lemma AI_sound: "AI c = Some c' \<Longrightarrow> CS c \<le> \<gamma>\<^isub>c c'"
proof(simp add: CS_def AI_def)
  assume 1: "lpfp\<^isub>c (step' \<top>) c = Some c'"
  have 2: "step' \<top> c' \<sqsubseteq> c'" by(rule lpfpc_pfp[OF 1])
  have 3: "strip (\<gamma>\<^isub>c (step' \<top> c')) = c"
    by(simp add: strip_lpfpc[OF _ 1])
  have "lfp (step UNIV) c \<le> \<gamma>\<^isub>c (step' \<top> c')"
  proof(rule lfp_lowerbound[simplified,OF 3])
    show "step UNIV (\<gamma>\<^isub>c (step' \<top> c')) \<le> \<gamma>\<^isub>c (step' \<top> c')"
    proof(rule step_preserves_le[OF _ _])
      show "UNIV \<subseteq> \<gamma>\<^isub>o \<top>" by simp
      show "\<gamma>\<^isub>c (step' \<top> c') \<le> \<gamma>\<^isub>c c'" by(rule mono_gamma_c[OF 2])
    qed
  qed
  from this 2 show "lfp (step UNIV) c \<le> \<gamma>\<^isub>c c'"
    by (blast intro: mono_gamma_c order_trans)
qed

end


subsubsection "Monotonicity"

locale Abs_Int_mono = Abs_Int +
assumes mono_plus': "a1 \<sqsubseteq> b1 \<Longrightarrow> a2 \<sqsubseteq> b2 \<Longrightarrow> plus' a1 a2 \<sqsubseteq> plus' b1 b2"
begin

lemma mono_aval': "S \<sqsubseteq> S' \<Longrightarrow> aval' e S \<sqsubseteq> aval' e S'"
by(induction e) (auto simp: le_st_def lookup_def mono_plus')

lemma mono_update: "a \<sqsubseteq> a' \<Longrightarrow> S \<sqsubseteq> S' \<Longrightarrow> update S x a \<sqsubseteq> update S' x a'"
by(auto simp add: le_st_def lookup_def update_def)

lemma mono_step': "S \<sqsubseteq> S' \<Longrightarrow> c \<sqsubseteq> c' \<Longrightarrow> step' S c \<sqsubseteq> step' S' c'"
apply(induction c c' arbitrary: S S' rule: le_acom.induct)
apply (auto simp: Let_def mono_update mono_aval' mono_post le_join_disj
            split: option.split)
done

end


subsubsection "Ascending Chain Condition"

hide_const (open) acc

abbreviation "strict r == r \<inter> -(r^-1)"
abbreviation "acc r == wf((strict r)^-1)"

lemma strict_inv_image: "strict(inv_image r f) = inv_image (strict r) f"
by(auto simp: inv_image_def)

lemma acc_inv_image:
  "acc r \<Longrightarrow> acc (inv_image r f)"
by (metis converse_inv_image strict_inv_image wf_inv_image)

text{* ACC for option type: *}

lemma acc_option: assumes "acc {(x,y::'a::preord). x \<sqsubseteq> y}"
shows "acc {(x,y::'a option). x \<sqsubseteq> y}"
proof(auto simp: wf_eq_minimal)
  fix xo :: "'a option" and Qo assume "xo : Qo"
  let ?Q = "{x. Some x \<in> Qo}"
  show "\<exists>yo\<in>Qo. \<forall>zo. yo \<sqsubseteq> zo \<and> ~ zo \<sqsubseteq> yo \<longrightarrow> zo \<notin> Qo" (is "\<exists>zo\<in>Qo. ?P zo")
  proof cases
    assume "?Q = {}"
    hence "?P None" by auto
    moreover have "None \<in> Qo" using `?Q = {}` `xo : Qo`
      by auto (metis not_Some_eq)
    ultimately show ?thesis by blast
  next
    assume "?Q \<noteq> {}"
    with assms show ?thesis
      apply(auto simp: wf_eq_minimal)
      apply(erule_tac x="?Q" in allE)
      apply auto
      apply(rule_tac x = "Some z" in bexI)
      by auto
  qed
qed

text{* ACC for abstract states, via measure functions. *}

(*FIXME mv*)
lemma setsum_strict_mono1:
fixes f :: "'a \<Rightarrow> 'b::{comm_monoid_add, ordered_cancel_ab_semigroup_add}"
assumes "finite A" and "ALL x:A. f x \<le> g x" and "EX a:A. f a < g a"
shows "setsum f A < setsum g A"
proof-
  from assms(3) obtain a where a: "a:A" "f a < g a" by blast
  have "setsum f A = setsum f ((A-{a}) \<union> {a})"
    by(simp add:insert_absorb[OF `a:A`])
  also have "\<dots> = setsum f (A-{a}) + setsum f {a}"
    using `finite A` by(subst setsum_Un_disjoint) auto
  also have "setsum f (A-{a}) \<le> setsum g (A-{a})"
    by(rule setsum_mono)(simp add: assms(2))
  also have "setsum f {a} < setsum g {a}" using a by simp
  also have "setsum g (A - {a}) + setsum g {a} = setsum g((A-{a}) \<union> {a})"
    using `finite A` by(subst setsum_Un_disjoint[symmetric]) auto
  also have "\<dots> = setsum g A" by(simp add:insert_absorb[OF `a:A`])
  finally show ?thesis by (metis add_right_mono add_strict_left_mono)
qed

lemma measure_st: assumes "(strict{(x,y::'a::SL_top). x \<sqsubseteq> y})^-1 <= measure m"
and "\<forall>x y::'a. x \<sqsubseteq> y \<and> y \<sqsubseteq> x \<longrightarrow> m x = m y"
shows "(strict{(S,S'::'a st). S \<sqsubseteq> S'})^-1 \<subseteq>
  measure(%fd. \<Sum>x| x\<in>set(dom fd) \<and> ~ \<top> \<sqsubseteq> fun fd x. m(fun fd x)+1)"
proof-
  { fix S S' :: "'a st" assume "S \<sqsubseteq> S'" "~ S' \<sqsubseteq> S"
    let ?X = "set(dom S)" let ?Y = "set(dom S')"
    let ?f = "fun S" let ?g = "fun S'"
    let ?X' = "{x:?X. ~ \<top> \<sqsubseteq> ?f x}" let ?Y' = "{y:?Y. ~ \<top> \<sqsubseteq> ?g y}"
    from `S \<sqsubseteq> S'` have "ALL y:?Y'\<inter>?X. ?f y \<sqsubseteq> ?g y"
      by(auto simp: le_st_def lookup_def)
    hence 1: "ALL y:?Y'\<inter>?X. m(?g y)+1 \<le> m(?f y)+1"
      using assms(1,2) by(fastforce)
    from `~ S' \<sqsubseteq> S` obtain u where u: "u : ?X" "~ lookup S' u \<sqsubseteq> ?f u"
      by(auto simp: le_st_def)
    hence "u : ?X'" by simp (metis preord_class.le_trans top)
    have "?Y'-?X = {}" using `S \<sqsubseteq> S'` by(fastforce simp: le_st_def lookup_def)
    have "?Y'\<inter>?X <= ?X'" apply auto
      apply (metis `S \<sqsubseteq> S'` le_st_def lookup_def preord_class.le_trans)
      done
    have "(\<Sum>y\<in>?Y'. m(?g y)+1) = (\<Sum>y\<in>(?Y'-?X) \<union> (?Y'\<inter>?X). m(?g y)+1)"
      by (metis Un_Diff_Int)
    also have "\<dots> = (\<Sum>y\<in>?Y'\<inter>?X. m(?g y)+1)"
      using `?Y'-?X = {}` by (metis Un_empty_left)
    also have "\<dots> < (\<Sum>x\<in>?X'. m(?f x)+1)"
    proof cases
      assume "u \<in> ?Y'"
      hence "m(?g u) < m(?f u)" using assms(1) `S \<sqsubseteq> S'` u
        by (fastforce simp: le_st_def lookup_def)
      have "(\<Sum>y\<in>?Y'\<inter>?X. m(?g y)+1) < (\<Sum>y\<in>?Y'\<inter>?X. m(?f y)+1)"
        using `u:?X` `u:?Y'` `m(?g u) < m(?f u)`
        by(fastforce intro!: setsum_strict_mono1[OF _ 1])
      also have "\<dots> \<le> (\<Sum>y\<in>?X'. m(?f y)+1)"
        by(simp add: setsum_mono3[OF _ `?Y'\<inter>?X <= ?X'`])
      finally show ?thesis .
    next
      assume "u \<notin> ?Y'"
      with `?Y'\<inter>?X <= ?X'` have "?Y'\<inter>?X - {u} <= ?X' - {u}" by blast
      have "(\<Sum>y\<in>?Y'\<inter>?X. m(?g y)+1) = (\<Sum>y\<in>?Y'\<inter>?X - {u}. m(?g y)+1)"
      proof-
        have "?Y'\<inter>?X = ?Y'\<inter>?X - {u}" using `u \<notin> ?Y'` by auto
        thus ?thesis by metis
      qed
      also have "\<dots> < (\<Sum>y\<in>?Y'\<inter>?X-{u}. m(?g y)+1) + (\<Sum>y\<in>{u}. m(?f y)+1)" by simp
      also have "(\<Sum>y\<in>?Y'\<inter>?X-{u}. m(?g y)+1) \<le> (\<Sum>y\<in>?Y'\<inter>?X-{u}. m(?f y)+1)"
        using 1 by(blast intro: setsum_mono)
      also have "\<dots> \<le> (\<Sum>y\<in>?X'-{u}. m(?f y)+1)"
        by(simp add: setsum_mono3[OF _ `?Y'\<inter>?X-{u} <= ?X'-{u}`])
      also have "\<dots> + (\<Sum>y\<in>{u}. m(?f y)+1)= (\<Sum>y\<in>(?X'-{u}) \<union> {u}. m(?f y)+1)"
        using `u:?X'` by(subst setsum_Un_disjoint[symmetric]) auto
      also have "\<dots> = (\<Sum>x\<in>?X'. m(?f x)+1)"
        using `u : ?X'` by(simp add:insert_absorb)
      finally show ?thesis by (blast intro: add_right_mono)
    qed
    finally have "(\<Sum>y\<in>?Y'. m(?g y)+1) < (\<Sum>x\<in>?X'. m(?f x)+1)" .
  } thus ?thesis by(auto simp add: measure_def inv_image_def)
qed

text{* ACC for acom. First the ordering on acom is related to an ordering on
lists of annotations. *}

(* FIXME mv and add [simp] *)
lemma listrel_Cons_iff:
  "(x#xs, y#ys) : listrel r \<longleftrightarrow> (x,y) \<in> r \<and> (xs,ys) \<in> listrel r"
by (blast intro:listrel.Cons)

lemma listrel_app: "(xs1,ys1) : listrel r \<Longrightarrow> (xs2,ys2) : listrel r
  \<Longrightarrow> (xs1@xs2, ys1@ys2) : listrel r"
by(auto simp add: listrel_iff_zip)

lemma listrel_app_same_size: "size xs1 = size ys1 \<Longrightarrow> size xs2 = size ys2 \<Longrightarrow>
  (xs1@xs2, ys1@ys2) : listrel r \<longleftrightarrow>
  (xs1,ys1) : listrel r \<and> (xs2,ys2) : listrel r"
by(auto simp add: listrel_iff_zip)

lemma listrel_converse: "listrel(r^-1) = (listrel r)^-1"
proof-
  { fix xs ys
    have "(xs,ys) : listrel(r^-1) \<longleftrightarrow> (ys,xs) : listrel r"
      apply(induct xs arbitrary: ys)
      apply (fastforce simp: listrel.Nil)
      apply (fastforce simp: listrel_Cons_iff)
      done
  } thus ?thesis by auto
qed

(* It would be nice to get rid of refl & trans and build them into the proof *)
lemma acc_listrel: fixes r :: "('a*'a)set" assumes "refl r" and "trans r"
and "acc r" shows "acc (listrel r - {([],[])})"
proof-
  have refl: "!!x. (x,x) : r" using `refl r` unfolding refl_on_def by blast
  have trans: "!!x y z. (x,y) : r \<Longrightarrow> (y,z) : r \<Longrightarrow> (x,z) : r"
    using `trans r` unfolding trans_def by blast
  from assms(3) obtain mx :: "'a set \<Rightarrow> 'a" where
    mx: "!!S x. x:S \<Longrightarrow> mx S : S \<and> (\<forall>y. (mx S,y) : strict r \<longrightarrow> y \<notin> S)"
    by(simp add: wf_eq_minimal) metis
  let ?R = "listrel r - {([], [])}"
  { fix Q and xs :: "'a list"
    have "xs \<in> Q \<Longrightarrow> \<exists>ys. ys\<in>Q \<and> (\<forall>zs. (ys, zs) \<in> strict ?R \<longrightarrow> zs \<notin> Q)"
      (is "_ \<Longrightarrow> \<exists>ys. ?P Q ys")
    proof(induction xs arbitrary: Q rule: length_induct)
      case (1 xs)
      { have "!!ys Q. size ys < size xs \<Longrightarrow> ys : Q \<Longrightarrow> EX ms. ?P Q ms"
          using "1.IH" by blast
      } note IH = this
      show ?case
      proof(cases xs)
        case Nil with `xs : Q` have "?P Q []" by auto
        thus ?thesis by blast
      next
        case (Cons x ys)
        let ?Q1 = "{a. \<exists>bs. size bs = size ys \<and> a#bs : Q}"
        have "x : ?Q1" using `xs : Q` Cons by auto
        from mx[OF this] obtain m1 where
          1: "m1 \<in> ?Q1 \<and> (\<forall>y. (m1,y) \<in> strict r \<longrightarrow> y \<notin> ?Q1)" by blast
        then obtain ms1 where "size ms1 = size ys" "m1#ms1 : Q" by blast+
        hence "size ms1 < size xs" using Cons by auto
        let ?Q2 = "{bs. \<exists>m1'. (m1',m1):r \<and> (m1,m1'):r \<and> m1'#bs : Q \<and> size bs = size ms1}"
        have "ms1 : ?Q2" using `m1#ms1 : Q` by(blast intro: refl)
        from IH[OF `size ms1 < size xs` this]
        obtain ms where 2: "?P ?Q2 ms" by auto
        then obtain m1' where m1': "(m1',m1) : r \<and> (m1,m1') : r \<and> m1'#ms : Q"
          by blast
        hence "\<forall>ab. (m1'#ms,ab) : strict ?R \<longrightarrow> ab \<notin> Q" using 1 2
          apply (auto simp: listrel_Cons_iff)
          apply (metis `length ms1 = length ys` listrel_eq_len trans)
          by (metis `length ms1 = length ys` listrel_eq_len trans)
        with m1' show ?thesis by blast
      qed
    qed
  }
  thus ?thesis unfolding wf_eq_minimal by (metis converse_iff)
qed


fun annos :: "'a acom \<Rightarrow> 'a list" where
"annos (SKIP {a}) = [a]" |
"annos (x::=e {a}) = [a]" |
"annos (c1;c2) = annos c1 @ annos c2" |
"annos (IF b THEN c1 ELSE c2 {a}) = a #  annos c1 @ annos c2" |
"annos ({i} WHILE b DO c {a}) = i # a # annos c"

lemma size_annos_same: "strip c1 = strip c2 \<Longrightarrow> size(annos c1) = size(annos c2)"
apply(induct c2 arbitrary: c1)
apply (auto simp: strip_eq_SKIP strip_eq_Assign strip_eq_Semi strip_eq_If strip_eq_While)
done

lemmas size_annos_same2 = eqTrueI[OF size_annos_same]

lemma set_annos_anno: "set (annos (anno a c)) = {a}"
by(induction c)(auto)

lemma le_iff_le_annos: "c1 \<sqsubseteq> c2 \<longleftrightarrow>
 (annos c1, annos c2) : listrel{(x,y). x \<sqsubseteq> y} \<and> strip c1 = strip c2"
apply(induct c1 c2 rule: le_acom.induct)
apply (auto simp: listrel.Nil listrel_Cons_iff listrel_app size_annos_same2)
apply (metis listrel_app_same_size size_annos_same)+
done

lemma le_acom_subset_same_annos:
 "(strict{(c,c'::'a::preord acom). c \<sqsubseteq> c'})^-1 \<subseteq>
  (strict(inv_image (listrel{(a,a'::'a). a \<sqsubseteq> a'} - {([],[])}) annos))^-1"
by(auto simp: le_iff_le_annos)

lemma acc_acom: "acc {(a,a'::'a::preord). a \<sqsubseteq> a'} \<Longrightarrow>
  acc {(c,c'::'a acom). c \<sqsubseteq> c'}"
apply(rule wf_subset[OF _ le_acom_subset_same_annos])
apply(rule acc_inv_image[OF acc_listrel])
apply(auto simp: refl_on_def trans_def intro: le_trans)
done

text{* Termination of the fixed-point finders, assuming monotone functions: *}

lemma pfp_termination:
fixes x0 :: "'a::preord"
assumes mono: "\<And>x y. x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> f y" and "acc {(x::'a,y). x \<sqsubseteq> y}"
and "x0 \<sqsubseteq> f x0" shows "EX x. pfp f x0 = Some x"
proof(simp add: pfp_def, rule wf_while_option_Some[where P = "%x. x \<sqsubseteq> f x"])
  show "wf {(x, s). (s \<sqsubseteq> f s \<and> \<not> f s \<sqsubseteq> s) \<and> x = f s}"
    by(rule wf_subset[OF assms(2)]) auto
next
  show "x0 \<sqsubseteq> f x0" by(rule assms)
next
  fix x assume "x \<sqsubseteq> f x" thus "f x \<sqsubseteq> f(f x)" by(rule mono)
qed

lemma lpfpc_termination:
  fixes f :: "(('a::SL_top)option acom \<Rightarrow> 'a option acom)"
  assumes "acc {(x::'a,y). x \<sqsubseteq> y}" and "\<And>x y. x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> f y"
  and "\<And>c. strip(f c) = strip c"
  shows "\<exists>c'. lpfp\<^isub>c f c = Some c'"
unfolding lpfp\<^isub>c_def
apply(rule pfp_termination)
  apply(erule assms(2))
 apply(rule acc_acom[OF acc_option[OF assms(1)]])
apply(simp add: bot_acom assms(3))
done

context Abs_Int_mono
begin

lemma AI_Some_measure:
assumes "(strict{(x,y::'a). x \<sqsubseteq> y})^-1 <= measure m"
and "\<forall>x y::'a. x \<sqsubseteq> y \<and> y \<sqsubseteq> x \<longrightarrow> m x = m y"
shows "\<exists>c'. AI c = Some c'"
unfolding AI_def
apply(rule lpfpc_termination)
apply(rule wf_subset[OF wf_measure measure_st[OF assms]])
apply(erule mono_step'[OF le_refl])
apply(rule strip_step')
done

end

end
