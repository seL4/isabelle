
(* Author: Andreas Lochbihler, Uni Karlsruhe *)

header {* Almost everywhere constant functions *}

theory Fin_Fun
imports Main Infinite_Set Enum
begin

text {*
  This theory defines functions which are constant except for finitely
  many points (FinFun) and introduces a type finfin along with a
  number of operators for them. The code generator is set up such that
  such functions can be represented as data in the generated code and
  all operators are executable.

  For details, see Formalising FinFuns - Generating Code for Functions as Data by A. Lochbihler in TPHOLs 2009.
*}


subsection {* The @{text "map_default"} operation *}

definition map_default :: "'b \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
where "map_default b f a \<equiv> case f a of None \<Rightarrow> b | Some b' \<Rightarrow> b'"

lemma map_default_delete [simp]:
  "map_default b (f(a := None)) = (map_default b f)(a := b)"
by(simp add: map_default_def expand_fun_eq)

lemma map_default_insert:
  "map_default b (f(a \<mapsto> b')) = (map_default b f)(a := b')"
by(simp add: map_default_def expand_fun_eq)

lemma map_default_empty [simp]: "map_default b empty = (\<lambda>a. b)"
by(simp add: expand_fun_eq map_default_def)

lemma map_default_inject:
  fixes g g' :: "'a \<rightharpoonup> 'b"
  assumes infin_eq: "\<not> finite (UNIV :: 'a set) \<or> b = b'"
  and fin: "finite (dom g)" and b: "b \<notin> ran g"
  and fin': "finite (dom g')" and b': "b' \<notin> ran g'"
  and eq': "map_default b g = map_default b' g'"
  shows "b = b'" "g = g'"
proof -
  from infin_eq show bb': "b = b'"
  proof
    assume infin: "\<not> finite (UNIV :: 'a set)"
    from fin fin' have "finite (dom g \<union> dom g')" by auto
    with infin have "UNIV - (dom g \<union> dom g') \<noteq> {}" by(auto dest: finite_subset)
    then obtain a where a: "a \<notin> dom g \<union> dom g'" by auto
    hence "map_default b g a = b" "map_default b' g' a = b'" by(auto simp add: map_default_def)
    with eq' show "b = b'" by simp
  qed

  show "g = g'"
  proof
    fix x
    show "g x = g' x"
    proof(cases "g x")
      case None
      hence "map_default b g x = b" by(simp add: map_default_def)
      with bb' eq' have "map_default b' g' x = b'" by simp
      with b' have "g' x = None" by(simp add: map_default_def ran_def split: option.split_asm)
      with None show ?thesis by simp
    next
      case (Some c)
      with b have cb: "c \<noteq> b" by(auto simp add: ran_def)
      moreover from Some have "map_default b g x = c" by(simp add: map_default_def)
      with eq' have "map_default b' g' x = c" by simp
      ultimately have "g' x = Some c" using b' bb' by(auto simp add: map_default_def split: option.splits)
      with Some show ?thesis by simp
    qed
  qed
qed

subsection {* The finfun type *}

typedef ('a,'b) finfun = "{f::'a\<Rightarrow>'b. \<exists>b. finite {a. f a \<noteq> b}}"
apply(auto)
apply(rule_tac x="\<lambda>x. arbitrary" in exI)
apply(auto)
done

syntax
  "finfun"      :: "type \<Rightarrow> type \<Rightarrow> type"         ("(_ \<Rightarrow>\<^isub>f /_)" [22, 21] 21)

lemma fun_upd_finfun: "y(a := b) \<in> finfun \<longleftrightarrow> y \<in> finfun"
proof -
  { fix b'
    have "finite {a'. (y(a := b)) a' \<noteq> b'} = finite {a'. y a' \<noteq> b'}"
    proof(cases "b = b'")
      case True
      hence "{a'. (y(a := b)) a' \<noteq> b'} = {a'. y a' \<noteq> b'} - {a}" by auto
      thus ?thesis by simp
    next
      case False
      hence "{a'. (y(a := b)) a' \<noteq> b'} = insert a {a'. y a' \<noteq> b'}" by auto
      thus ?thesis by simp
    qed }
  thus ?thesis unfolding finfun_def by blast
qed

lemma const_finfun: "(\<lambda>x. a) \<in> finfun"
by(auto simp add: finfun_def)

lemma finfun_left_compose:
  assumes "y \<in> finfun"
  shows "g \<circ> y \<in> finfun"
proof -
  from assms obtain b where "finite {a. y a \<noteq> b}"
    unfolding finfun_def by blast
  hence "finite {c. g (y c) \<noteq> g b}"
  proof(induct x\<equiv>"{a. y a \<noteq> b}" arbitrary: y)
    case empty
    hence "y = (\<lambda>a. b)" by(auto intro: ext)
    thus ?case by(simp)
  next
    case (insert x F)
    note IH = `\<And>y. F = {a. y a \<noteq> b} \<Longrightarrow> finite {c. g (y c) \<noteq> g b}`
    from `insert x F = {a. y a \<noteq> b}` `x \<notin> F`
    have F: "F = {a. (y(x := b)) a \<noteq> b}" by(auto)
    show ?case
    proof(cases "g (y x) = g b")
      case True
      hence "{c. g ((y(x := b)) c) \<noteq> g b} = {c. g (y c) \<noteq> g b}" by auto
      with IH[OF F] show ?thesis by simp
    next
      case False
      hence "{c. g (y c) \<noteq> g b} = insert x {c. g ((y(x := b)) c) \<noteq> g b}" by auto
      with IH[OF F] show ?thesis by(simp)
    qed
  qed
  thus ?thesis unfolding finfun_def by auto
qed

lemma assumes "y \<in> finfun"
  shows fst_finfun: "fst \<circ> y \<in> finfun"
  and snd_finfun: "snd \<circ> y \<in> finfun"
proof -
  from assms obtain b c where bc: "finite {a. y a \<noteq> (b, c)}"
    unfolding finfun_def by auto
  have "{a. fst (y a) \<noteq> b} \<subseteq> {a. y a \<noteq> (b, c)}"
    and "{a. snd (y a) \<noteq> c} \<subseteq> {a. y a \<noteq> (b, c)}" by auto
  hence "finite {a. fst (y a) \<noteq> b}" 
    and "finite {a. snd (y a) \<noteq> c}" using bc by(auto intro: finite_subset)
  thus "fst \<circ> y \<in> finfun" "snd \<circ> y \<in> finfun"
    unfolding finfun_def by auto
qed

lemma map_of_finfun: "map_of xs \<in> finfun"
unfolding finfun_def
by(induct xs)(auto simp add: Collect_neg_eq Collect_conj_eq Collect_imp_eq intro: finite_subset)

lemma Diag_finfun: "(\<lambda>x. (f x, g x)) \<in> finfun \<longleftrightarrow> f \<in> finfun \<and> g \<in> finfun"
by(auto intro: finite_subset simp add: Collect_neg_eq Collect_imp_eq Collect_conj_eq finfun_def)

lemma finfun_right_compose:
  assumes g: "g \<in> finfun" and inj: "inj f"
  shows "g o f \<in> finfun"
proof -
  from g obtain b where b: "finite {a. g a \<noteq> b}" unfolding finfun_def by blast
  moreover have "f ` {a. g (f a) \<noteq> b} \<subseteq> {a. g a \<noteq> b}" by auto
  moreover from inj have "inj_on f {a.  g (f a) \<noteq> b}" by(rule subset_inj_on) blast
  ultimately have "finite {a. g (f a) \<noteq> b}"
    by(blast intro: finite_imageD[where f=f] finite_subset)
  thus ?thesis unfolding finfun_def by auto
qed

lemma finfun_curry:
  assumes fin: "f \<in> finfun"
  shows "curry f \<in> finfun" "curry f a \<in> finfun"
proof -
  from fin obtain c where c: "finite {ab. f ab \<noteq> c}" unfolding finfun_def by blast
  moreover have "{a. \<exists>b. f (a, b) \<noteq> c} = fst ` {ab. f ab \<noteq> c}" by(force)
  hence "{a. curry f a \<noteq> (\<lambda>b. c)} = fst ` {ab. f ab \<noteq> c}"
    by(auto simp add: curry_def expand_fun_eq)
  ultimately have "finite {a. curry f a \<noteq> (\<lambda>b. c)}" by simp
  thus "curry f \<in> finfun" unfolding finfun_def by blast
  
  have "snd ` {ab. f ab \<noteq> c} = {b. \<exists>a. f (a, b) \<noteq> c}" by(force)
  hence "{b. f (a, b) \<noteq> c} \<subseteq> snd ` {ab. f ab \<noteq> c}" by auto
  hence "finite {b. f (a, b) \<noteq> c}" by(rule finite_subset)(rule finite_imageI[OF c])
  thus "curry f a \<in> finfun" unfolding finfun_def by auto
qed

lemmas finfun_simp = 
  fst_finfun snd_finfun Abs_finfun_inverse Rep_finfun_inverse Abs_finfun_inject Rep_finfun_inject Diag_finfun finfun_curry
lemmas finfun_iff = const_finfun fun_upd_finfun Rep_finfun map_of_finfun
lemmas finfun_intro = finfun_left_compose fst_finfun snd_finfun

lemma Abs_finfun_inject_finite:
  fixes x y :: "'a \<Rightarrow> 'b"
  assumes fin: "finite (UNIV :: 'a set)"
  shows "Abs_finfun x = Abs_finfun y \<longleftrightarrow> x = y"
proof
  assume "Abs_finfun x = Abs_finfun y"
  moreover have "x \<in> finfun" "y \<in> finfun" unfolding finfun_def
    by(auto intro: finite_subset[OF _ fin])
  ultimately show "x = y" by(simp add: Abs_finfun_inject)
qed simp

lemma Abs_finfun_inject_finite_class:
  fixes x y :: "('a :: finite) \<Rightarrow> 'b"
  shows "Abs_finfun x = Abs_finfun y \<longleftrightarrow> x = y"
using finite_UNIV
by(simp add: Abs_finfun_inject_finite)

lemma Abs_finfun_inj_finite:
  assumes fin: "finite (UNIV :: 'a set)"
  shows "inj (Abs_finfun :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow>\<^isub>f 'b)"
proof(rule inj_onI)
  fix x y :: "'a \<Rightarrow> 'b"
  assume "Abs_finfun x = Abs_finfun y"
  moreover have "x \<in> finfun" "y \<in> finfun" unfolding finfun_def
    by(auto intro: finite_subset[OF _ fin])
  ultimately show "x = y" by(simp add: Abs_finfun_inject)
qed

declare finfun_simp [simp] finfun_iff [iff] finfun_intro [intro]

lemma Abs_finfun_inverse_finite:
  fixes x :: "'a \<Rightarrow> 'b"
  assumes fin: "finite (UNIV :: 'a set)"
  shows "Rep_finfun (Abs_finfun x) = x"
proof -
  from fin have "x \<in> finfun"
    by(auto simp add: finfun_def intro: finite_subset)
  thus ?thesis by simp
qed

declare finfun_simp [simp del] finfun_iff [iff del] finfun_intro [rule del]

lemma Abs_finfun_inverse_finite_class:
  fixes x :: "('a :: finite) \<Rightarrow> 'b"
  shows "Rep_finfun (Abs_finfun x) = x"
using finite_UNIV by(simp add: Abs_finfun_inverse_finite)

lemma finfun_eq_finite_UNIV: "finite (UNIV :: 'a set) \<Longrightarrow> (finfun :: ('a \<Rightarrow> 'b) set) = UNIV"
unfolding finfun_def by(auto intro: finite_subset)

lemma finfun_finite_UNIV_class: "finfun = (UNIV :: ('a :: finite \<Rightarrow> 'b) set)"
by(simp add: finfun_eq_finite_UNIV)

lemma map_default_in_finfun:
  assumes fin: "finite (dom f)"
  shows "map_default b f \<in> finfun"
unfolding finfun_def
proof(intro CollectI exI)
  from fin show "finite {a. map_default b f a \<noteq> b}"
    by(auto simp add: map_default_def dom_def Collect_conj_eq split: option.splits)
qed

lemma finfun_cases_map_default:
  obtains b g where "f = Abs_finfun (map_default b g)" "finite (dom g)" "b \<notin> ran g"
proof -
  obtain y where f: "f = Abs_finfun y" and y: "y \<in> finfun" by(cases f)
  from y obtain b where b: "finite {a. y a \<noteq> b}" unfolding finfun_def by auto
  let ?g = "(\<lambda>a. if y a = b then None else Some (y a))"
  have "map_default b ?g = y" by(simp add: expand_fun_eq map_default_def)
  with f have "f = Abs_finfun (map_default b ?g)" by simp
  moreover from b have "finite (dom ?g)" by(auto simp add: dom_def)
  moreover have "b \<notin> ran ?g" by(auto simp add: ran_def)
  ultimately show ?thesis by(rule that)
qed


subsection {* Kernel functions for type @{typ "'a \<Rightarrow>\<^isub>f 'b"} *}

definition finfun_const :: "'b \<Rightarrow> 'a \<Rightarrow>\<^isub>f 'b" ("\<lambda>\<^isup>f/ _" [0] 1)
where [code del]: "(\<lambda>\<^isup>f b) = Abs_finfun (\<lambda>x. b)"

definition finfun_update :: "'a \<Rightarrow>\<^isub>f 'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow>\<^isub>f 'b" ("_'(\<^sup>f/ _ := _')" [1000,0,0] 1000)
where [code del]: "f(\<^sup>fa := b) = Abs_finfun ((Rep_finfun f)(a := b))"

declare finfun_simp [simp] finfun_iff [iff] finfun_intro [intro]

lemma finfun_update_twist: "a \<noteq> a' \<Longrightarrow> f(\<^sup>f a := b)(\<^sup>f a' := b') = f(\<^sup>f a' := b')(\<^sup>f a := b)"
by(simp add: finfun_update_def fun_upd_twist)

lemma finfun_update_twice [simp]:
  "finfun_update (finfun_update f a b) a b' = finfun_update f a b'"
by(simp add: finfun_update_def)

lemma finfun_update_const_same: "(\<lambda>\<^isup>f b)(\<^sup>f a := b) = (\<lambda>\<^isup>f b)"
by(simp add: finfun_update_def finfun_const_def expand_fun_eq)

declare finfun_simp [simp del] finfun_iff [iff del] finfun_intro [rule del]

subsection {* Code generator setup *}

definition finfun_update_code :: "'a \<Rightarrow>\<^isub>f 'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow>\<^isub>f 'b" ("_'(\<^sup>f\<^sup>c/ _ := _')" [1000,0,0] 1000)
where [simp, code del]: "finfun_update_code = finfun_update"

code_datatype finfun_const finfun_update_code

lemma finfun_update_const_code [code]:
  "(\<lambda>\<^isup>f b)(\<^sup>f a := b') = (if b = b' then (\<lambda>\<^isup>f b) else finfun_update_code (\<lambda>\<^isup>f b) a b')"
by(simp add: finfun_update_const_same)

lemma finfun_update_update_code [code]:
  "(finfun_update_code f a b)(\<^sup>f a' := b') = (if a = a' then f(\<^sup>f a := b') else finfun_update_code (f(\<^sup>f a' := b')) a b)"
by(simp add: finfun_update_twist)


subsection {* Setup for quickcheck *}

notation fcomp (infixl "o>" 60)
notation scomp (infixl "o\<rightarrow>" 60)

definition (in term_syntax) valtermify_finfun_const ::
  "'b\<Colon>typerep \<times> (unit \<Rightarrow> Code_Eval.term) \<Rightarrow> ('a\<Colon>typerep \<Rightarrow>\<^isub>f 'b) \<times> (unit \<Rightarrow> Code_Eval.term)" where
  "valtermify_finfun_const y = Code_Eval.valtermify finfun_const {\<cdot>} y"

definition (in term_syntax) valtermify_finfun_update_code ::
  "'a\<Colon>typerep \<times> (unit \<Rightarrow> Code_Eval.term) \<Rightarrow> 'b\<Colon>typerep \<times> (unit \<Rightarrow> Code_Eval.term) \<Rightarrow> ('a \<Rightarrow>\<^isub>f 'b) \<times> (unit \<Rightarrow> Code_Eval.term) \<Rightarrow> ('a \<Rightarrow>\<^isub>f 'b) \<times> (unit \<Rightarrow> Code_Eval.term)" where
  "valtermify_finfun_update_code x y f = Code_Eval.valtermify finfun_update_code {\<cdot>} f {\<cdot>} x {\<cdot>} y"

instantiation finfun :: (random, random) random
begin

primrec random_finfun' :: "code_numeral \<Rightarrow> code_numeral \<Rightarrow> Random.seed \<Rightarrow> ('a \<Rightarrow>\<^isub>f 'b \<times> (unit \<Rightarrow> Code_Eval.term)) \<times> Random.seed" where
    "random_finfun' 0 j = Quickcheck.collapse (Random.select_default 0
       (random j o\<rightarrow> (\<lambda>y. Pair (valtermify_finfun_const y)))
       (random j o\<rightarrow> (\<lambda>y. Pair (valtermify_finfun_const y))))"
  | "random_finfun' (Suc_code_numeral i) j = Quickcheck.collapse (Random.select_default i
       (random j o\<rightarrow> (\<lambda>x. random j o\<rightarrow> (\<lambda>y. random_finfun' i j o\<rightarrow> (\<lambda>f. Pair (valtermify_finfun_update_code x y f)))))
       (random j o\<rightarrow> (\<lambda>y. Pair (valtermify_finfun_const y))))"
                         
definition 
  "random i = random_finfun' i i"

instance ..

end

lemma select_default_zero:
  "Random.select_default 0 y y = Random.select_default 0 x y"
  by (simp add: select_default_def)

lemma random_finfun'_code [code]:
  "random_finfun' i j = Quickcheck.collapse (Random.select_default (i - 1)
    (random j o\<rightarrow> (\<lambda>x. random j o\<rightarrow> (\<lambda>y. random_finfun' (i - 1) j o\<rightarrow> (\<lambda>f. Pair (valtermify_finfun_update_code x y f)))))
    (random j o\<rightarrow> (\<lambda>y. Pair (valtermify_finfun_const y))))"
  apply (cases i rule: code_numeral.exhaust)
  apply (simp_all only: random_finfun'.simps code_numeral_zero_minus_one Suc_code_numeral_minus_one)
  apply (subst select_default_zero) apply (simp only:)
  done

no_notation fcomp (infixl "o>" 60)
no_notation scomp (infixl "o\<rightarrow>" 60)


subsection {* @{text "finfun_update"} as instance of @{text "fun_left_comm"} *}

declare finfun_simp [simp] finfun_iff [iff] finfun_intro [intro]

interpretation finfun_update: fun_left_comm "\<lambda>a f. f(\<^sup>f a :: 'a := b')"
proof
  fix a' a :: 'a
  fix b
  have "(Rep_finfun b)(a := b', a' := b') = (Rep_finfun b)(a' := b', a := b')"
    by(cases "a = a'")(auto simp add: fun_upd_twist)
  thus "b(\<^sup>f a := b')(\<^sup>f a' := b') = b(\<^sup>f a' := b')(\<^sup>f a := b')"
    by(auto simp add: finfun_update_def fun_upd_twist)
qed

lemma fold_finfun_update_finite_univ:
  assumes fin: "finite (UNIV :: 'a set)"
  shows "fold (\<lambda>a f. f(\<^sup>f a := b')) (\<lambda>\<^isup>f b) (UNIV :: 'a set) = (\<lambda>\<^isup>f b')"
proof -
  { fix A :: "'a set"
    from fin have "finite A" by(auto intro: finite_subset)
    hence "fold (\<lambda>a f. f(\<^sup>f a := b')) (\<lambda>\<^isup>f b) A = Abs_finfun (\<lambda>a. if a \<in> A then b' else b)"
    proof(induct)
      case (insert x F)
      have "(\<lambda>a. if a = x then b' else (if a \<in> F then b' else b)) = (\<lambda>a. if a = x \<or> a \<in> F then b' else b)"
        by(auto intro: ext)
      with insert show ?case
        by(simp add: finfun_const_def fun_upd_def)(simp add: finfun_update_def Abs_finfun_inverse_finite[OF fin] fun_upd_def)
    qed(simp add: finfun_const_def) }
  thus ?thesis by(simp add: finfun_const_def)
qed


subsection {* Default value for FinFuns *}

definition finfun_default_aux :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b"
where [code del]: "finfun_default_aux f = (if finite (UNIV :: 'a set) then arbitrary else THE b. finite {a. f a \<noteq> b})"

lemma finfun_default_aux_infinite:
  fixes f :: "'a \<Rightarrow> 'b"
  assumes infin: "infinite (UNIV :: 'a set)"
  and fin: "finite {a. f a \<noteq> b}"
  shows "finfun_default_aux f = b"
proof -
  let ?B = "{a. f a \<noteq> b}"
  from fin have "(THE b. finite {a. f a \<noteq> b}) = b"
  proof(rule the_equality)
    fix b'
    assume "finite {a. f a \<noteq> b'}" (is "finite ?B'")
    with infin fin have "UNIV - (?B' \<union> ?B) \<noteq> {}" by(auto dest: finite_subset)
    then obtain a where a: "a \<notin> ?B' \<union> ?B" by auto
    thus "b' = b" by auto
  qed
  thus ?thesis using infin by(simp add: finfun_default_aux_def)
qed


lemma finite_finfun_default_aux:
  fixes f :: "'a \<Rightarrow> 'b"
  assumes fin: "f \<in> finfun"
  shows "finite {a. f a \<noteq> finfun_default_aux f}"
proof(cases "finite (UNIV :: 'a set)")
  case True thus ?thesis using fin
    by(auto simp add: finfun_def finfun_default_aux_def intro: finite_subset)
next
  case False
  from fin obtain b where b: "finite {a. f a \<noteq> b}" (is "finite ?B")
    unfolding finfun_def by blast
  with False show ?thesis by(simp add: finfun_default_aux_infinite)
qed

lemma finfun_default_aux_update_const:
  fixes f :: "'a \<Rightarrow> 'b"
  assumes fin: "f \<in> finfun"
  shows "finfun_default_aux (f(a := b)) = finfun_default_aux f"
proof(cases "finite (UNIV :: 'a set)")
  case False
  from fin obtain b' where b': "finite {a. f a \<noteq> b'}" unfolding finfun_def by blast
  hence "finite {a'. (f(a := b)) a' \<noteq> b'}"
  proof(cases "b = b' \<and> f a \<noteq> b'") 
    case True
    hence "{a. f a \<noteq> b'} = insert a {a'. (f(a := b)) a' \<noteq> b'}" by auto
    thus ?thesis using b' by simp
  next
    case False
    moreover
    { assume "b \<noteq> b'"
      hence "{a'. (f(a := b)) a' \<noteq> b'} = insert a {a. f a \<noteq> b'}" by auto
      hence ?thesis using b' by simp }
    moreover
    { assume "b = b'" "f a = b'"
      hence "{a'. (f(a := b)) a' \<noteq> b'} = {a. f a \<noteq> b'}" by auto
      hence ?thesis using b' by simp }
    ultimately show ?thesis by blast
  qed
  with False b' show ?thesis by(auto simp del: fun_upd_apply simp add: finfun_default_aux_infinite)
next
  case True thus ?thesis by(simp add: finfun_default_aux_def)
qed

definition finfun_default :: "'a \<Rightarrow>\<^isub>f 'b \<Rightarrow> 'b"
  where [code del]: "finfun_default f = finfun_default_aux (Rep_finfun f)"

lemma finite_finfun_default: "finite {a. Rep_finfun f a \<noteq> finfun_default f}"
unfolding finfun_default_def by(simp add: finite_finfun_default_aux)

lemma finfun_default_const: "finfun_default ((\<lambda>\<^isup>f b) :: 'a \<Rightarrow>\<^isub>f 'b) = (if finite (UNIV :: 'a set) then arbitrary else b)"
apply(auto simp add: finfun_default_def finfun_const_def finfun_default_aux_infinite)
apply(simp add: finfun_default_aux_def)
done

lemma finfun_default_update_const:
  "finfun_default (f(\<^sup>f a := b)) = finfun_default f"
unfolding finfun_default_def finfun_update_def
by(simp add: finfun_default_aux_update_const)

subsection {* Recursion combinator and well-formedness conditions *}

definition finfun_rec :: "('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow>\<^isub>f 'b) \<Rightarrow> 'c"
where [code del]:
  "finfun_rec cnst upd f \<equiv>
   let b = finfun_default f;
       g = THE g. f = Abs_finfun (map_default b g) \<and> finite (dom g) \<and> b \<notin> ran g
   in fold (\<lambda>a. upd a (map_default b g a)) (cnst b) (dom g)"

locale finfun_rec_wf_aux =
  fixes cnst :: "'b \<Rightarrow> 'c"
  and upd :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'c"
  assumes upd_const_same: "upd a b (cnst b) = cnst b"
  and upd_commute: "a \<noteq> a' \<Longrightarrow> upd a b (upd a' b' c) = upd a' b' (upd a b c)"
  and upd_idemp: "b \<noteq> b' \<Longrightarrow> upd a b'' (upd a b' (cnst b)) = upd a b'' (cnst b)"
begin


lemma upd_left_comm: "fun_left_comm (\<lambda>a. upd a (f a))"
by(unfold_locales)(auto intro: upd_commute)

lemma upd_upd_twice: "upd a b'' (upd a b' (cnst b)) = upd a b'' (cnst b)"
by(cases "b \<noteq> b'")(auto simp add: fun_upd_def upd_const_same upd_idemp)

declare finfun_simp [simp] finfun_iff [iff] finfun_intro [intro]

lemma map_default_update_const:
  assumes fin: "finite (dom f)"
  and anf: "a \<notin> dom f"
  and fg: "f \<subseteq>\<^sub>m g"
  shows "upd a d  (fold (\<lambda>a. upd a (map_default d g a)) (cnst d) (dom f)) =
         fold (\<lambda>a. upd a (map_default d g a)) (cnst d) (dom f)"
proof -
  let ?upd = "\<lambda>a. upd a (map_default d g a)"
  let ?fr = "\<lambda>A. fold ?upd (cnst d) A"
  interpret gwf: fun_left_comm "?upd" by(rule upd_left_comm)
  
  from fin anf fg show ?thesis
  proof(induct A\<equiv>"dom f" arbitrary: f)
    case empty
    from `{} = dom f` have "f = empty" by(auto simp add: dom_def intro: ext)
    thus ?case by(simp add: finfun_const_def upd_const_same)
  next
    case (insert a' A)
    note IH = `\<And>f.  \<lbrakk> a \<notin> dom f; f \<subseteq>\<^sub>m g; A = dom f\<rbrakk> \<Longrightarrow> upd a d (?fr (dom f)) = ?fr (dom f)`
    note fin = `finite A` note anf = `a \<notin> dom f` note a'nA = `a' \<notin> A`
    note domf = `insert a' A = dom f` note fg = `f \<subseteq>\<^sub>m g`
    
    from domf obtain b where b: "f a' = Some b" by auto
    let ?f' = "f(a' := None)"
    have "upd a d (?fr (insert a' A)) = upd a d (upd a' (map_default d g a') (?fr A))"
      by(subst gwf.fold_insert[OF fin a'nA]) rule
    also from b fg have "g a' = f a'" by(auto simp add: map_le_def intro: domI dest: bspec)
    hence ga': "map_default d g a' = map_default d f a'" by(simp add: map_default_def)
    also from anf domf have "a \<noteq> a'" by auto note upd_commute[OF this]
    also from domf a'nA anf fg have "a \<notin> dom ?f'" "?f' \<subseteq>\<^sub>m g" and A: "A = dom ?f'" by(auto simp add: ran_def map_le_def)
    note A also note IH[OF `a \<notin> dom ?f'` `?f' \<subseteq>\<^sub>m g` A]
    also have "upd a' (map_default d f a') (?fr (dom (f(a' := None)))) = ?fr (dom f)"
      unfolding domf[symmetric] gwf.fold_insert[OF fin a'nA] ga' unfolding A ..
    also have "insert a' (dom ?f') = dom f" using domf by auto
    finally show ?case .
  qed
qed

lemma map_default_update_twice:
  assumes fin: "finite (dom f)"
  and anf: "a \<notin> dom f"
  and fg: "f \<subseteq>\<^sub>m g"
  shows "upd a d'' (upd a d' (fold (\<lambda>a. upd a (map_default d g a)) (cnst d) (dom f))) =
         upd a d'' (fold (\<lambda>a. upd a (map_default d g a)) (cnst d) (dom f))"
proof -
  let ?upd = "\<lambda>a. upd a (map_default d g a)"
  let ?fr = "\<lambda>A. fold ?upd (cnst d) A"
  interpret gwf: fun_left_comm "?upd" by(rule upd_left_comm)
  
  from fin anf fg show ?thesis
  proof(induct A\<equiv>"dom f" arbitrary: f)
    case empty
    from `{} = dom f` have "f = empty" by(auto simp add: dom_def intro: ext)
    thus ?case by(auto simp add: finfun_const_def finfun_update_def upd_upd_twice)
  next
    case (insert a' A)
    note IH = `\<And>f. \<lbrakk>a \<notin> dom f; f \<subseteq>\<^sub>m g; A = dom f\<rbrakk> \<Longrightarrow> upd a d'' (upd a d' (?fr (dom f))) = upd a d'' (?fr (dom f))`
    note fin = `finite A` note anf = `a \<notin> dom f` note a'nA = `a' \<notin> A`
    note domf = `insert a' A = dom f` note fg = `f \<subseteq>\<^sub>m g`
    
    from domf obtain b where b: "f a' = Some b" by auto
    let ?f' = "f(a' := None)"
    let ?b' = "case f a' of None \<Rightarrow> d | Some b \<Rightarrow> b"
    from domf have "upd a d'' (upd a d' (?fr (dom f))) = upd a d'' (upd a d' (?fr (insert a' A)))" by simp
    also note gwf.fold_insert[OF fin a'nA]
    also from b fg have "g a' = f a'" by(auto simp add: map_le_def intro: domI dest: bspec)
    hence ga': "map_default d g a' = map_default d f a'" by(simp add: map_default_def)
    also from anf domf have ana': "a \<noteq> a'" by auto note upd_commute[OF this]
    also note upd_commute[OF ana']
    also from domf a'nA anf fg have "a \<notin> dom ?f'" "?f' \<subseteq>\<^sub>m g" and A: "A = dom ?f'" by(auto simp add: ran_def map_le_def)
    note A also note IH[OF `a \<notin> dom ?f'` `?f' \<subseteq>\<^sub>m g` A]
    also note upd_commute[OF ana'[symmetric]] also note ga'[symmetric] also note A[symmetric]
    also note gwf.fold_insert[symmetric, OF fin a'nA] also note domf
    finally show ?case .
  qed
qed

declare finfun_simp [simp del] finfun_iff [iff del] finfun_intro [rule del]

lemma map_default_eq_id [simp]: "map_default d ((\<lambda>a. Some (f a)) |` {a. f a \<noteq> d}) = f"
by(auto simp add: map_default_def restrict_map_def intro: ext)

lemma finite_rec_cong1:
  assumes f: "fun_left_comm f" and g: "fun_left_comm g"
  and fin: "finite A"
  and eq: "\<And>a. a \<in> A \<Longrightarrow> f a = g a"
  shows "fold f z A = fold g z A"
proof -
  interpret f: fun_left_comm f by(rule f)
  interpret g: fun_left_comm g by(rule g)
  { fix B
    assume BsubA: "B \<subseteq> A"
    with fin have "finite B" by(blast intro: finite_subset)
    hence "B \<subseteq> A \<Longrightarrow> fold f z B = fold g z B"
    proof(induct)
      case empty thus ?case by simp
    next
      case (insert a B)
      note finB = `finite B` note anB = `a \<notin> B` note sub = `insert a B \<subseteq> A`
      note IH = `B \<subseteq> A \<Longrightarrow> fold f z B = fold g z B`
      from sub anB have BpsubA: "B \<subset> A" and BsubA: "B \<subseteq> A" and aA: "a \<in> A" by auto
      from IH[OF BsubA] eq[OF aA] finB anB
      show ?case by(auto)
    qed
    with BsubA have "fold f z B = fold g z B" by blast }
  thus ?thesis by blast
qed

declare finfun_simp [simp] finfun_iff [iff] finfun_intro [intro]

lemma finfun_rec_upd [simp]:
  "finfun_rec cnst upd (f(\<^sup>f a' := b')) = upd a' b' (finfun_rec cnst upd f)"
proof -
  obtain b where b: "b = finfun_default f" by auto
  let ?the = "\<lambda>f g. f = Abs_finfun (map_default b g) \<and> finite (dom g) \<and> b \<notin> ran g"
  obtain g where g: "g = The (?the f)" by blast
  obtain y where f: "f = Abs_finfun y" and y: "y \<in> finfun" by (cases f)
  from f y b have bfin: "finite {a. y a \<noteq> b}" by(simp add: finfun_default_def finite_finfun_default_aux)

  let ?g = "(\<lambda>a. Some (y a)) |` {a. y a \<noteq> b}"
  from bfin have fing: "finite (dom ?g)" by auto
  have bran: "b \<notin> ran ?g" by(auto simp add: ran_def restrict_map_def)
  have yg: "y = map_default b ?g" by simp
  have gg: "g = ?g" unfolding g
  proof(rule the_equality)
    from f y bfin show "?the f ?g"
      by(auto)(simp add: restrict_map_def ran_def split: split_if_asm)
  next
    fix g'
    assume "?the f g'"
    hence fin': "finite (dom g')" and ran': "b \<notin> ran g'"
      and eq: "Abs_finfun (map_default b ?g) = Abs_finfun (map_default b g')" using f yg by auto
    from fin' fing have "map_default b ?g \<in> finfun" "map_default b g' \<in> finfun" by(blast intro: map_default_in_finfun)+
    with eq have "map_default b ?g = map_default b g'" by simp
    with fing bran fin' ran' show "g' = ?g" by(rule map_default_inject[OF disjI2[OF refl], THEN sym])
  qed

  show ?thesis
  proof(cases "b' = b")
    case True
    note b'b = True

    let ?g' = "(\<lambda>a. Some ((y(a' := b)) a)) |` {a. (y(a' := b)) a \<noteq> b}"
    from bfin b'b have fing': "finite (dom ?g')"
      by(auto simp add: Collect_conj_eq Collect_imp_eq intro: finite_subset)
    have brang': "b \<notin> ran ?g'" by(auto simp add: ran_def restrict_map_def)

    let ?b' = "\<lambda>a. case ?g' a of None \<Rightarrow> b | Some b \<Rightarrow> b"
    let ?b = "map_default b ?g"
    from upd_left_comm upd_left_comm fing'
    have "fold (\<lambda>a. upd a (?b' a)) (cnst b) (dom ?g') = fold (\<lambda>a. upd a (?b a)) (cnst b) (dom ?g')"
      by(rule finite_rec_cong1)(auto simp add: restrict_map_def b'b b map_default_def)
    also interpret gwf: fun_left_comm "\<lambda>a. upd a (?b a)" by(rule upd_left_comm)
    have "fold (\<lambda>a. upd a (?b a)) (cnst b) (dom ?g') = upd a' b' (fold (\<lambda>a. upd a (?b a)) (cnst b) (dom ?g))"
    proof(cases "y a' = b")
      case True
      with b'b have g': "?g' = ?g" by(auto simp add: restrict_map_def intro: ext)
      from True have a'ndomg: "a' \<notin> dom ?g" by auto
      from f b'b b show ?thesis unfolding g'
        by(subst map_default_update_const[OF fing a'ndomg map_le_refl, symmetric]) simp
    next
      case False
      hence domg: "dom ?g = insert a' (dom ?g')" by auto
      from False b'b have a'ndomg': "a' \<notin> dom ?g'" by auto
      have "fold (\<lambda>a. upd a (?b a)) (cnst b) (insert a' (dom ?g')) = 
            upd a' (?b a') (fold (\<lambda>a. upd a (?b a)) (cnst b) (dom ?g'))"
        using fing' a'ndomg' unfolding b'b by(rule gwf.fold_insert)
      hence "upd a' b (fold (\<lambda>a. upd a (?b a)) (cnst b) (insert a' (dom ?g'))) =
             upd a' b (upd a' (?b a') (fold (\<lambda>a. upd a (?b a)) (cnst b) (dom ?g')))" by simp
      also from b'b have g'leg: "?g' \<subseteq>\<^sub>m ?g" by(auto simp add: restrict_map_def map_le_def)
      note map_default_update_twice[OF fing' a'ndomg' this, of b "?b a'" b]
      also note map_default_update_const[OF fing' a'ndomg' g'leg, of b]
      finally show ?thesis unfolding b'b domg[unfolded b'b] by(rule sym)
    qed
    also have "The (?the (f(\<^sup>f a' := b'))) = ?g'"
    proof(rule the_equality)
      from f y b b'b brang' fing' show "?the (f(\<^sup>f a' := b')) ?g'"
        by(auto simp del: fun_upd_apply simp add: finfun_update_def)
    next
      fix g'
      assume "?the (f(\<^sup>f a' := b')) g'"
      hence fin': "finite (dom g')" and ran': "b \<notin> ran g'"
        and eq: "f(\<^sup>f a' := b') = Abs_finfun (map_default b g')" 
        by(auto simp del: fun_upd_apply)
      from fin' fing' have "map_default b g' \<in> finfun" "map_default b ?g' \<in> finfun"
        by(blast intro: map_default_in_finfun)+
      with eq f b'b b have "map_default b ?g' = map_default b g'"
        by(simp del: fun_upd_apply add: finfun_update_def)
      with fing' brang' fin' ran' show "g' = ?g'"
        by(rule map_default_inject[OF disjI2[OF refl], THEN sym])
    qed
    ultimately show ?thesis unfolding finfun_rec_def Let_def b gg[unfolded g b] using bfin b'b b
      by(simp only: finfun_default_update_const map_default_def)
  next
    case False
    note b'b = this
    let ?g' = "?g(a' \<mapsto> b')"
    let ?b' = "map_default b ?g'"
    let ?b = "map_default b ?g"
    from fing have fing': "finite (dom ?g')" by auto
    from bran b'b have bnrang': "b \<notin> ran ?g'" by(auto simp add: ran_def)
    have ffmg': "map_default b ?g' = y(a' := b')" by(auto intro: ext simp add: map_default_def restrict_map_def)
    with f y have f_Abs: "f(\<^sup>f a' := b') = Abs_finfun (map_default b ?g')" by(auto simp add: finfun_update_def)
    have g': "The (?the (f(\<^sup>f a' := b'))) = ?g'"
    proof
      from fing' bnrang' f_Abs show "?the (f(\<^sup>f a' := b')) ?g'" by(auto simp add: finfun_update_def restrict_map_def)
    next
      fix g' assume "?the (f(\<^sup>f a' := b')) g'"
      hence f': "f(\<^sup>f a' := b') = Abs_finfun (map_default b g')"
        and fin': "finite (dom g')" and brang': "b \<notin> ran g'" by auto
      from fing' fin' have "map_default b ?g' \<in> finfun" "map_default b g' \<in> finfun"
        by(auto intro: map_default_in_finfun)
      with f' f_Abs have "map_default b g' = map_default b ?g'" by simp
      with fin' brang' fing' bnrang' show "g' = ?g'"
        by(rule map_default_inject[OF disjI2[OF refl]])
    qed
    have dom: "dom (((\<lambda>a. Some (y a)) |` {a. y a \<noteq> b})(a' \<mapsto> b')) = insert a' (dom ((\<lambda>a. Some (y a)) |` {a. y a \<noteq> b}))"
      by auto
    show ?thesis
    proof(cases "y a' = b")
      case True
      hence a'ndomg: "a' \<notin> dom ?g" by auto
      from f y b'b True have yff: "y = map_default b (?g' |` dom ?g)"
        by(auto simp add: restrict_map_def map_default_def intro!: ext)
      hence f': "f = Abs_finfun (map_default b (?g' |` dom ?g))" using f by simp
      interpret g'wf: fun_left_comm "\<lambda>a. upd a (?b' a)" by(rule upd_left_comm)
      from upd_left_comm upd_left_comm fing
      have "fold (\<lambda>a. upd a (?b a)) (cnst b) (dom ?g) = fold (\<lambda>a. upd a (?b' a)) (cnst b) (dom ?g)"
        by(rule finite_rec_cong1)(auto simp add: restrict_map_def b'b True map_default_def)
      thus ?thesis unfolding finfun_rec_def Let_def finfun_default_update_const b[symmetric]
        unfolding g' g[symmetric] gg g'wf.fold_insert[OF fing a'ndomg, of "cnst b", folded dom]
        by -(rule arg_cong2[where f="upd a'"], simp_all add: map_default_def)
    next
      case False
      hence "insert a' (dom ?g) = dom ?g" by auto
      moreover {
        let ?g'' = "?g(a' := None)"
        let ?b'' = "map_default b ?g''"
        from False have domg: "dom ?g = insert a' (dom ?g'')" by auto
        from False have a'ndomg'': "a' \<notin> dom ?g''" by auto
        have fing'': "finite (dom ?g'')" by(rule finite_subset[OF _ fing]) auto
        have bnrang'': "b \<notin> ran ?g''" by(auto simp add: ran_def restrict_map_def)
        interpret gwf: fun_left_comm "\<lambda>a. upd a (?b a)" by(rule upd_left_comm)
        interpret g'wf: fun_left_comm "\<lambda>a. upd a (?b' a)" by(rule upd_left_comm)
        have "upd a' b' (fold (\<lambda>a. upd a (?b a)) (cnst b) (insert a' (dom ?g''))) =
              upd a' b' (upd a' (?b a') (fold (\<lambda>a. upd a (?b a)) (cnst b) (dom ?g'')))"
          unfolding gwf.fold_insert[OF fing'' a'ndomg''] f ..
        also have g''leg: "?g |` dom ?g'' \<subseteq>\<^sub>m ?g" by(auto simp add: map_le_def)
        have "dom (?g |` dom ?g'') = dom ?g''" by auto
        note map_default_update_twice[where d=b and f = "?g |` dom ?g''" and a=a' and d'="?b a'" and d''=b' and g="?g",
                                     unfolded this, OF fing'' a'ndomg'' g''leg]
        also have b': "b' = ?b' a'" by(auto simp add: map_default_def)
        from upd_left_comm upd_left_comm fing''
        have "fold (\<lambda>a. upd a (?b a)) (cnst b) (dom ?g'') = fold (\<lambda>a. upd a (?b' a)) (cnst b) (dom ?g'')"
          by(rule finite_rec_cong1)(auto simp add: restrict_map_def b'b map_default_def)
        with b' have "upd a' b' (fold (\<lambda>a. upd a (?b a)) (cnst b) (dom ?g'')) =
                     upd a' (?b' a') (fold (\<lambda>a. upd a (?b' a)) (cnst b) (dom ?g''))" by simp
        also note g'wf.fold_insert[OF fing'' a'ndomg'', symmetric]
        finally have "upd a' b' (fold (\<lambda>a. upd a (?b a)) (cnst b) (dom ?g)) =
                   fold (\<lambda>a. upd a (?b' a)) (cnst b) (dom ?g)"
          unfolding domg . }
      ultimately have "fold (\<lambda>a. upd a (?b' a)) (cnst b) (insert a' (dom ?g)) =
                    upd a' b' (fold (\<lambda>a. upd a (?b a)) (cnst b) (dom ?g))" by simp
      thus ?thesis unfolding finfun_rec_def Let_def finfun_default_update_const b[symmetric] g[symmetric] g' dom[symmetric]
        using b'b gg by(simp add: map_default_insert)
    qed
  qed
qed

declare finfun_simp [simp del] finfun_iff [iff del] finfun_intro [rule del]

end

locale finfun_rec_wf = finfun_rec_wf_aux + 
  assumes const_update_all:
  "finite (UNIV :: 'a set) \<Longrightarrow> fold (\<lambda>a. upd a b') (cnst b) (UNIV :: 'a set) = cnst b'"
begin

declare finfun_simp [simp] finfun_iff [iff] finfun_intro [intro]

lemma finfun_rec_const [simp]:
  "finfun_rec cnst upd (\<lambda>\<^isup>f c) = cnst c"
proof(cases "finite (UNIV :: 'a set)")
  case False
  hence "finfun_default ((\<lambda>\<^isup>f c) :: 'a \<Rightarrow>\<^isub>f 'b) = c" by(simp add: finfun_default_const)
  moreover have "(THE g :: 'a \<rightharpoonup> 'b. (\<lambda>\<^isup>f c) = Abs_finfun (map_default c g) \<and> finite (dom g) \<and> c \<notin> ran g) = empty"
  proof
    show "(\<lambda>\<^isup>f c) = Abs_finfun (map_default c empty) \<and> finite (dom empty) \<and> c \<notin> ran empty"
      by(auto simp add: finfun_const_def)
  next
    fix g :: "'a \<rightharpoonup> 'b"
    assume "(\<lambda>\<^isup>f c) = Abs_finfun (map_default c g) \<and> finite (dom g) \<and> c \<notin> ran g"
    hence g: "(\<lambda>\<^isup>f c) = Abs_finfun (map_default c g)" and fin: "finite (dom g)" and ran: "c \<notin> ran g" by blast+
    from g map_default_in_finfun[OF fin, of c] have "map_default c g = (\<lambda>a. c)"
      by(simp add: finfun_const_def)
    moreover have "map_default c empty = (\<lambda>a. c)" by simp
    ultimately show "g = empty" by-(rule map_default_inject[OF disjI2[OF refl] fin ran], auto)
  qed
  ultimately show ?thesis by(simp add: finfun_rec_def)
next
  case True
  hence default: "finfun_default ((\<lambda>\<^isup>f c) :: 'a \<Rightarrow>\<^isub>f 'b) = arbitrary" by(simp add: finfun_default_const)
  let ?the = "\<lambda>g :: 'a \<rightharpoonup> 'b. (\<lambda>\<^isup>f c) = Abs_finfun (map_default arbitrary g) \<and> finite (dom g) \<and> arbitrary \<notin> ran g"
  show ?thesis
  proof(cases "c = arbitrary")
    case True
    have the: "The ?the = empty"
    proof
      from True show "?the empty" by(auto simp add: finfun_const_def)
    next
      fix g'
      assume "?the g'"
      hence fg: "(\<lambda>\<^isup>f c) = Abs_finfun (map_default arbitrary g')"
        and fin: "finite (dom g')" and g: "arbitrary \<notin> ran g'" by simp_all
      from fin have "map_default arbitrary g' \<in> finfun" by(rule map_default_in_finfun)
      with fg have "map_default arbitrary g' = (\<lambda>a. c)"
        by(auto simp add: finfun_const_def intro: Abs_finfun_inject[THEN iffD1])
      with True show "g' = empty"
        by -(rule map_default_inject(2)[OF _ fin g], auto)
    qed
    show ?thesis unfolding finfun_rec_def using `finite UNIV` True
      unfolding Let_def the default by(simp)
  next
    case False
    have the: "The ?the = (\<lambda>a :: 'a. Some c)"
    proof
      from False True show "?the (\<lambda>a :: 'a. Some c)"
        by(auto simp add: map_default_def_raw finfun_const_def dom_def ran_def)
    next
      fix g' :: "'a \<rightharpoonup> 'b"
      assume "?the g'"
      hence fg: "(\<lambda>\<^isup>f c) = Abs_finfun (map_default arbitrary g')"
        and fin: "finite (dom g')" and g: "arbitrary \<notin> ran g'" by simp_all
      from fin have "map_default arbitrary g' \<in> finfun" by(rule map_default_in_finfun)
      with fg have "map_default arbitrary g' = (\<lambda>a. c)"
        by(auto simp add: finfun_const_def intro: Abs_finfun_inject[THEN iffD1])
      with True False show "g' = (\<lambda>a::'a. Some c)"
        by -(rule map_default_inject(2)[OF _ fin g], auto simp add: dom_def ran_def map_default_def_raw)
    qed
    show ?thesis unfolding finfun_rec_def using True False
      unfolding Let_def the default by(simp add: dom_def map_default_def const_update_all)
  qed
qed

declare finfun_simp [simp del] finfun_iff [iff del] finfun_intro [rule del]

end

subsection {* Weak induction rule and case analysis for FinFuns *}

declare finfun_simp [simp] finfun_iff [iff] finfun_intro [intro]

lemma finfun_weak_induct [consumes 0, case_names const update]:
  assumes const: "\<And>b. P (\<lambda>\<^isup>f b)"
  and update: "\<And>f a b. P f \<Longrightarrow> P (f(\<^sup>f a := b))"
  shows "P x"
proof(induct x rule: Abs_finfun_induct)
  case (Abs_finfun y)
  then obtain b where "finite {a. y a \<noteq> b}" unfolding finfun_def by blast
  thus ?case using `y \<in> finfun`
  proof(induct x\<equiv>"{a. y a \<noteq> b}" arbitrary: y rule: finite_induct)
    case empty
    hence "\<And>a. y a = b" by blast
    hence "y = (\<lambda>a. b)" by(auto intro: ext)
    hence "Abs_finfun y = finfun_const b" unfolding finfun_const_def by simp
    thus ?case by(simp add: const)
  next
    case (insert a A)
    note IH = `\<And>y. \<lbrakk> y \<in> finfun; A = {a. y a \<noteq> b} \<rbrakk> \<Longrightarrow> P (Abs_finfun y)`
    note y = `y \<in> finfun`
    with `insert a A = {a. y a \<noteq> b}` `a \<notin> A`
    have "y(a := b) \<in> finfun" "A = {a'. (y(a := b)) a' \<noteq> b}" by auto
    from IH[OF this] have "P (finfun_update (Abs_finfun (y(a := b))) a (y a))" by(rule update)
    thus ?case using y unfolding finfun_update_def by simp
  qed
qed

declare finfun_simp [simp del] finfun_iff [iff del] finfun_intro [rule del]

lemma finfun_exhaust_disj: "(\<exists>b. x = finfun_const b) \<or> (\<exists>f a b. x = finfun_update f a b)"
by(induct x rule: finfun_weak_induct) blast+

lemma finfun_exhaust:
  obtains b where "x = (\<lambda>\<^isup>f b)"
        | f a b where "x = f(\<^sup>f a := b)"
by(atomize_elim)(rule finfun_exhaust_disj)

lemma finfun_rec_unique:
  fixes f :: "'a \<Rightarrow>\<^isub>f 'b \<Rightarrow> 'c"
  assumes c: "\<And>c. f (\<lambda>\<^isup>f c) = cnst c"
  and u: "\<And>g a b. f (g(\<^sup>f a := b)) = upd g a b (f g)"
  and c': "\<And>c. f' (\<lambda>\<^isup>f c) = cnst c"
  and u': "\<And>g a b. f' (g(\<^sup>f a := b)) = upd g a b (f' g)"
  shows "f = f'"
proof
  fix g :: "'a \<Rightarrow>\<^isub>f 'b"
  show "f g = f' g"
    by(induct g rule: finfun_weak_induct)(auto simp add: c u c' u')
qed


subsection {* Function application *}

definition finfun_apply :: "'a \<Rightarrow>\<^isub>f 'b \<Rightarrow> 'a \<Rightarrow> 'b" ("_\<^sub>f" [1000] 1000)
where [code del]: "finfun_apply = (\<lambda>f a. finfun_rec (\<lambda>b. b) (\<lambda>a' b c. if (a = a') then b else c) f)"

interpretation finfun_apply_aux: finfun_rec_wf_aux "\<lambda>b. b" "\<lambda>a' b c. if (a = a') then b else c"
by(unfold_locales) auto

interpretation finfun_apply: finfun_rec_wf "\<lambda>b. b" "\<lambda>a' b c. if (a = a') then b else c"
proof(unfold_locales)
  fix b' b :: 'a
  assume fin: "finite (UNIV :: 'b set)"
  { fix A :: "'b set"
    interpret fun_left_comm "\<lambda>a'. If (a = a') b'" by(rule finfun_apply_aux.upd_left_comm)
    from fin have "finite A" by(auto intro: finite_subset)
    hence "fold (\<lambda>a'. If (a = a') b') b A = (if a \<in> A then b' else b)"
      by induct auto }
  from this[of UNIV] show "fold (\<lambda>a'. If (a = a') b') b UNIV = b'" by simp
qed

lemma finfun_const_apply [simp, code]: "(\<lambda>\<^isup>f b)\<^sub>f a = b"
by(simp add: finfun_apply_def)

lemma finfun_upd_apply: "f(\<^sup>fa := b)\<^sub>f a' = (if a = a' then b else f\<^sub>f a')"
  and finfun_upd_apply_code [code]: "(finfun_update_code f a b)\<^sub>f a' = (if a = a' then b else f\<^sub>f a')"
by(simp_all add: finfun_apply_def)

lemma finfun_upd_apply_same [simp]:
  "f(\<^sup>fa := b)\<^sub>f a = b"
by(simp add: finfun_upd_apply)

lemma finfun_upd_apply_other [simp]:
  "a \<noteq> a' \<Longrightarrow> f(\<^sup>fa := b)\<^sub>f a' = f\<^sub>f a'"
by(simp add: finfun_upd_apply)

declare finfun_simp [simp] finfun_iff [iff] finfun_intro [intro]

lemma finfun_apply_Rep_finfun:
  "finfun_apply = Rep_finfun"
proof(rule finfun_rec_unique)
  fix c show "Rep_finfun (\<lambda>\<^isup>f c) = (\<lambda>a. c)" by(auto simp add: finfun_const_def)
next
  fix g a b show "Rep_finfun g(\<^sup>f a := b) = (\<lambda>c. if c = a then b else Rep_finfun g c)"
    by(auto simp add: finfun_update_def fun_upd_finfun Abs_finfun_inverse Rep_finfun intro: ext)
qed(auto intro: ext)

lemma finfun_ext: "(\<And>a. f\<^sub>f a = g\<^sub>f a) \<Longrightarrow> f = g"
by(auto simp add: finfun_apply_Rep_finfun Rep_finfun_inject[symmetric] simp del: Rep_finfun_inject intro: ext)

declare finfun_simp [simp del] finfun_iff [iff del] finfun_intro [rule del]

lemma expand_finfun_eq: "(f = g) = (f\<^sub>f = g\<^sub>f)"
by(auto intro: finfun_ext)

lemma finfun_const_inject [simp]: "(\<lambda>\<^isup>f b) = (\<lambda>\<^isup>f b') \<equiv> b = b'"
by(simp add: expand_finfun_eq expand_fun_eq)

lemma finfun_const_eq_update:
  "((\<lambda>\<^isup>f b) = f(\<^sup>f a := b')) = (b = b' \<and> (\<forall>a'. a \<noteq> a' \<longrightarrow> f\<^sub>f a' = b))"
by(auto simp add: expand_finfun_eq expand_fun_eq finfun_upd_apply)

subsection {* Function composition *}

definition finfun_comp :: "('a \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow>\<^isub>f 'a \<Rightarrow> 'c \<Rightarrow>\<^isub>f 'b" (infixr "\<circ>\<^isub>f" 55)
where [code del]: "g \<circ>\<^isub>f f  = finfun_rec (\<lambda>b. (\<lambda>\<^isup>f g b)) (\<lambda>a b c. c(\<^sup>f a := g b)) f"

interpretation finfun_comp_aux: finfun_rec_wf_aux "(\<lambda>b. (\<lambda>\<^isup>f g b))" "(\<lambda>a b c. c(\<^sup>f a := g b))"
by(unfold_locales)(auto simp add: finfun_upd_apply intro: finfun_ext)

interpretation finfun_comp: finfun_rec_wf "(\<lambda>b. (\<lambda>\<^isup>f g b))" "(\<lambda>a b c. c(\<^sup>f a := g b))"
proof
  fix b' b :: 'a
  assume fin: "finite (UNIV :: 'c set)"
  { fix A :: "'c set"
    from fin have "finite A" by(auto intro: finite_subset)
    hence "fold (\<lambda>(a :: 'c) c. c(\<^sup>f a := g b')) (\<lambda>\<^isup>f g b) A =
      Abs_finfun (\<lambda>a. if a \<in> A then g b' else g b)"
      by induct (simp_all add: finfun_const_def, auto simp add: finfun_update_def Abs_finfun_inverse_finite fun_upd_def Abs_finfun_inject_finite expand_fun_eq fin) }
  from this[of UNIV] show "fold (\<lambda>(a :: 'c) c. c(\<^sup>f a := g b')) (\<lambda>\<^isup>f g b) UNIV = (\<lambda>\<^isup>f g b')"
    by(simp add: finfun_const_def)
qed

lemma finfun_comp_const [simp, code]:
  "g \<circ>\<^isub>f (\<lambda>\<^isup>f c) = (\<lambda>\<^isup>f g c)"
by(simp add: finfun_comp_def)

lemma finfun_comp_update [simp]: "g \<circ>\<^isub>f (f(\<^sup>f a := b)) = (g \<circ>\<^isub>f f)(\<^sup>f a := g b)"
  and finfun_comp_update_code [code]: "g \<circ>\<^isub>f (finfun_update_code f a b) = finfun_update_code (g \<circ>\<^isub>f f) a (g b)"
by(simp_all add: finfun_comp_def)

lemma finfun_comp_apply [simp]:
  "(g \<circ>\<^isub>f f)\<^sub>f = g \<circ> f\<^sub>f"
by(induct f rule: finfun_weak_induct)(auto simp add: finfun_upd_apply intro: ext)

lemma finfun_comp_comp_collapse [simp]: "f \<circ>\<^isub>f g \<circ>\<^isub>f h = (f o g) \<circ>\<^isub>f h"
by(induct h rule: finfun_weak_induct) simp_all

lemma finfun_comp_const1 [simp]: "(\<lambda>x. c) \<circ>\<^isub>f f = (\<lambda>\<^isup>f c)"
by(induct f rule: finfun_weak_induct)(auto intro: finfun_ext simp add: finfun_upd_apply)

lemma finfun_comp_id1 [simp]: "(\<lambda>x. x) \<circ>\<^isub>f f = f" "id \<circ>\<^isub>f f = f"
by(induct f rule: finfun_weak_induct) auto

declare finfun_simp [simp] finfun_iff [iff] finfun_intro [intro]

lemma finfun_comp_conv_comp: "g \<circ>\<^isub>f f = Abs_finfun (g \<circ> finfun_apply f)"
proof -
  have "(\<lambda>f. g \<circ>\<^isub>f f) = (\<lambda>f. Abs_finfun (g \<circ> finfun_apply f))"
  proof(rule finfun_rec_unique)
    { fix c show "Abs_finfun (g \<circ> (\<lambda>\<^isup>f c)\<^sub>f) = (\<lambda>\<^isup>f g c)"
        by(simp add: finfun_comp_def o_def)(simp add: finfun_const_def) }
    { fix g' a b show "Abs_finfun (g \<circ> g'(\<^sup>f a := b)\<^sub>f) = (Abs_finfun (g \<circ> g'\<^sub>f))(\<^sup>f a := g b)"
      proof -
        obtain y where y: "y \<in> finfun" and g': "g' = Abs_finfun y" by(cases g')
        moreover hence "(g \<circ> g'\<^sub>f) \<in> finfun" by(simp add: finfun_apply_Rep_finfun finfun_left_compose)
        moreover have "g \<circ> y(a := b) = (g \<circ> y)(a := g b)" by(auto intro: ext)
        ultimately show ?thesis by(simp add: finfun_comp_def finfun_update_def finfun_apply_Rep_finfun)
      qed }
  qed auto
  thus ?thesis by(auto simp add: expand_fun_eq)
qed

declare finfun_simp [simp del] finfun_iff [iff del] finfun_intro [rule del]



definition finfun_comp2 :: "'b \<Rightarrow>\<^isub>f 'c \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow>\<^isub>f 'c" (infixr "\<^sub>f\<circ>" 55)
where [code del]: "finfun_comp2 g f = Abs_finfun (Rep_finfun g \<circ> f)"

declare finfun_simp [simp] finfun_iff [iff] finfun_intro [intro]

lemma finfun_comp2_const [code, simp]: "finfun_comp2 (\<lambda>\<^isup>f c) f = (\<lambda>\<^isup>f c)"
by(simp add: finfun_comp2_def finfun_const_def comp_def)

lemma finfun_comp2_update:
  assumes inj: "inj f"
  shows "finfun_comp2 (g(\<^sup>f b := c)) f = (if b \<in> range f then (finfun_comp2 g f)(\<^sup>f inv f b := c) else finfun_comp2 g f)"
proof(cases "b \<in> range f")
  case True
  from inj have "\<And>x. (Rep_finfun g)(f x := c) \<circ> f = (Rep_finfun g \<circ> f)(x := c)" by(auto intro!: ext dest: injD)
  with inj True show ?thesis by(auto simp add: finfun_comp2_def finfun_update_def finfun_right_compose)
next
  case False
  hence "(Rep_finfun g)(b := c) \<circ> f = Rep_finfun g \<circ> f" by(auto simp add: expand_fun_eq)
  with False show ?thesis by(auto simp add: finfun_comp2_def finfun_update_def)
qed

declare finfun_simp [simp del] finfun_iff [iff del] finfun_intro [rule del]

subsection {* A type class for computing the cardinality of a type's universe *}

class card_UNIV = 
  fixes card_UNIV :: "'a itself \<Rightarrow> nat"
  assumes card_UNIV: "card_UNIV x = card (UNIV :: 'a set)"
begin

lemma card_UNIV_neq_0_finite_UNIV:
  "card_UNIV x \<noteq> 0 \<longleftrightarrow> finite (UNIV :: 'a set)"
by(simp add: card_UNIV card_eq_0_iff)

lemma card_UNIV_ge_0_finite_UNIV:
  "card_UNIV x > 0 \<longleftrightarrow> finite (UNIV :: 'a set)"
by(auto simp add: card_UNIV intro: card_ge_0_finite finite_UNIV_card_ge_0)

lemma card_UNIV_eq_0_infinite_UNIV:
  "card_UNIV x = 0 \<longleftrightarrow> infinite (UNIV :: 'a set)"
by(simp add: card_UNIV card_eq_0_iff)

definition is_list_UNIV :: "'a list \<Rightarrow> bool"
where "is_list_UNIV xs = (let c = card_UNIV (TYPE('a)) in if c = 0 then False else size (remdups xs) = c)"

lemma is_list_UNIV_iff:
  fixes xs :: "'a list"
  shows "is_list_UNIV xs \<longleftrightarrow> set xs = UNIV"
proof
  assume "is_list_UNIV xs"
  hence c: "card_UNIV (TYPE('a)) > 0" and xs: "size (remdups xs) = card_UNIV (TYPE('a))"
    unfolding is_list_UNIV_def by(simp_all add: Let_def split: split_if_asm)
  from c have fin: "finite (UNIV :: 'a set)" by(auto simp add: card_UNIV_ge_0_finite_UNIV)
  have "card (set (remdups xs)) = size (remdups xs)" by(subst distinct_card) auto
  also note set_remdups
  finally show "set xs = UNIV" using fin unfolding xs card_UNIV by-(rule card_eq_UNIV_imp_eq_UNIV)
next
  assume xs: "set xs = UNIV"
  from finite_set[of xs] have fin: "finite (UNIV :: 'a set)" unfolding xs .
  hence "card_UNIV (TYPE ('a)) \<noteq> 0" unfolding card_UNIV_neq_0_finite_UNIV .
  moreover have "size (remdups xs) = card (set (remdups xs))"
    by(subst distinct_card) auto
  ultimately show "is_list_UNIV xs" using xs by(simp add: is_list_UNIV_def Let_def card_UNIV)
qed

lemma card_UNIV_eq_0_is_list_UNIV_False:
  assumes cU0: "card_UNIV x = 0"
  shows "is_list_UNIV = (\<lambda>xs. False)"
proof(rule ext)
  fix xs :: "'a list"
  from cU0 have "infinite (UNIV :: 'a set)"
    by(auto simp only: card_UNIV_eq_0_infinite_UNIV)
  moreover have "finite (set xs)" by(rule finite_set)
  ultimately have "(UNIV :: 'a set) \<noteq> set xs" by(auto simp del: finite_set)
  thus "is_list_UNIV xs = False" unfolding is_list_UNIV_iff by simp
qed

end

subsection {* Instantiations for @{text "card_UNIV"} *}

subsubsection {* @{typ "nat"} *}

instantiation nat :: card_UNIV begin

definition card_UNIV_nat_def:
  "card_UNIV_class.card_UNIV = (\<lambda>a :: nat itself. 0)"

instance proof
  fix x :: "nat itself"
  show "card_UNIV x = card (UNIV :: nat set)"
    unfolding card_UNIV_nat_def by simp
qed

end

subsubsection {* @{typ "int"} *}

instantiation int :: card_UNIV begin

definition card_UNIV_int_def:
  "card_UNIV_class.card_UNIV = (\<lambda>a :: int itself. 0)"

instance proof
  fix x :: "int itself"
  show "card_UNIV x = card (UNIV :: int set)"
    unfolding card_UNIV_int_def by simp
qed

end

subsubsection {* @{typ "'a list"} *}

instantiation list :: (type) card_UNIV begin

definition card_UNIV_list_def:
  "card_UNIV_class.card_UNIV = (\<lambda>a :: 'a list itself. 0)"

instance proof
  fix x :: "'a list itself"
  show "card_UNIV x = card (UNIV :: 'a list set)"
    unfolding card_UNIV_list_def by(simp add: infinite_UNIV_listI)
qed

end

subsubsection {* @{typ "unit"} *}

lemma card_UNIV_unit: "card (UNIV :: unit set) = 1"
  unfolding UNIV_unit by simp

instantiation unit :: card_UNIV begin

definition card_UNIV_unit_def: 
  "card_UNIV_class.card_UNIV = (\<lambda>a :: unit itself. 1)"

instance proof
  fix x :: "unit itself"
  show "card_UNIV x = card (UNIV :: unit set)"
    by(simp add: card_UNIV_unit_def card_UNIV_unit)
qed

end

subsubsection {* @{typ "bool"} *}

lemma card_UNIV_bool: "card (UNIV :: bool set) = 2"
  unfolding UNIV_bool by simp

instantiation bool :: card_UNIV begin

definition card_UNIV_bool_def: 
  "card_UNIV_class.card_UNIV = (\<lambda>a :: bool itself. 2)"

instance proof
  fix x :: "bool itself"
  show "card_UNIV x = card (UNIV :: bool set)"
    by(simp add: card_UNIV_bool_def card_UNIV_bool)
qed

end

subsubsection {* @{typ "char"} *}

lemma card_UNIV_char: "card (UNIV :: char set) = 256"
proof -
  from enum_distinct
  have "card (set (enum :: char list)) = length (enum :: char list)"
    by -(rule distinct_card)
  also have "set enum = (UNIV :: char set)" by auto
  also note enum_char
  finally show ?thesis by simp
qed

instantiation char :: card_UNIV begin

definition card_UNIV_char_def: 
  "card_UNIV_class.card_UNIV = (\<lambda>a :: char itself. 256)"

instance proof
  fix x :: "char itself"
  show "card_UNIV x = card (UNIV :: char set)"
    by(simp add: card_UNIV_char_def card_UNIV_char)
qed

end

subsubsection {* @{typ "'a \<times> 'b"} *}

instantiation * :: (card_UNIV, card_UNIV) card_UNIV begin

definition card_UNIV_product_def: 
  "card_UNIV_class.card_UNIV = (\<lambda>a :: ('a \<times> 'b) itself. card_UNIV (TYPE('a)) * card_UNIV (TYPE('b)))"

instance proof
  fix x :: "('a \<times> 'b) itself"
  show "card_UNIV x = card (UNIV :: ('a \<times> 'b) set)"
    by(simp add: card_UNIV_product_def card_UNIV UNIV_Times_UNIV[symmetric] card_cartesian_product del: UNIV_Times_UNIV)
qed

end

subsubsection {* @{typ "'a + 'b"} *}

instantiation "+" :: (card_UNIV, card_UNIV) card_UNIV begin

definition card_UNIV_sum_def: 
  "card_UNIV_class.card_UNIV = (\<lambda>a :: ('a + 'b) itself. let ca = card_UNIV (TYPE('a)); cb = card_UNIV (TYPE('b))
                           in if ca \<noteq> 0 \<and> cb \<noteq> 0 then ca + cb else 0)"

instance proof
  fix x :: "('a + 'b) itself"
  show "card_UNIV x = card (UNIV :: ('a + 'b) set)"
    by (auto simp add: card_UNIV_sum_def card_UNIV card_eq_0_iff UNIV_Plus_UNIV[symmetric] finite_Plus_iff Let_def card_Plus simp del: UNIV_Plus_UNIV dest!: card_ge_0_finite)
qed

end

subsubsection {* @{typ "'a \<Rightarrow> 'b"} *}

instantiation "fun" :: (card_UNIV, card_UNIV) card_UNIV begin

definition card_UNIV_fun_def: 
  "card_UNIV_class.card_UNIV = (\<lambda>a :: ('a \<Rightarrow> 'b) itself. let ca = card_UNIV (TYPE('a)); cb = card_UNIV (TYPE('b))
                           in if ca \<noteq> 0 \<and> cb \<noteq> 0 \<or> cb = 1 then cb ^ ca else 0)"

instance proof
  fix x :: "('a \<Rightarrow> 'b) itself"

  { assume "0 < card (UNIV :: 'a set)"
    and "0 < card (UNIV :: 'b set)"
    hence fina: "finite (UNIV :: 'a set)" and finb: "finite (UNIV :: 'b set)"
      by(simp_all only: card_ge_0_finite)
    from finite_distinct_list[OF finb] obtain bs 
      where bs: "set bs = (UNIV :: 'b set)" and distb: "distinct bs" by blast
    from finite_distinct_list[OF fina] obtain as
      where as: "set as = (UNIV :: 'a set)" and dista: "distinct as" by blast
    have cb: "card (UNIV :: 'b set) = length bs"
      unfolding bs[symmetric] distinct_card[OF distb] ..
    have ca: "card (UNIV :: 'a set) = length as"
      unfolding as[symmetric] distinct_card[OF dista] ..
    let ?xs = "map (\<lambda>ys. the o map_of (zip as ys)) (n_lists (length as) bs)"
    have "UNIV = set ?xs"
    proof(rule UNIV_eq_I)
      fix f :: "'a \<Rightarrow> 'b"
      from as have "f = the \<circ> map_of (zip as (map f as))"
        by(auto simp add: map_of_zip_map intro: ext)
      thus "f \<in> set ?xs" using bs by(auto simp add: set_n_lists)
    qed
    moreover have "distinct ?xs" unfolding distinct_map
    proof(intro conjI distinct_n_lists distb inj_onI)
      fix xs ys :: "'b list"
      assume xs: "xs \<in> set (n_lists (length as) bs)"
        and ys: "ys \<in> set (n_lists (length as) bs)"
        and eq: "the \<circ> map_of (zip as xs) = the \<circ> map_of (zip as ys)"
      from xs ys have [simp]: "length xs = length as" "length ys = length as"
        by(simp_all add: length_n_lists_elem)
      have "map_of (zip as xs) = map_of (zip as ys)"
      proof
        fix x
        from as bs have "\<exists>y. map_of (zip as xs) x = Some y" "\<exists>y. map_of (zip as ys) x = Some y"
          by(simp_all add: map_of_zip_is_Some[symmetric])
        with eq show "map_of (zip as xs) x = map_of (zip as ys) x"
          by(auto dest: fun_cong[where x=x])
      qed
      with dista show "xs = ys" by(simp add: map_of_zip_inject)
    qed
    hence "card (set ?xs) = length ?xs" by(simp only: distinct_card)
    moreover have "length ?xs = length bs ^ length as" by(simp add: length_n_lists)
    ultimately have "card (UNIV :: ('a \<Rightarrow> 'b) set) = card (UNIV :: 'b set) ^ card (UNIV :: 'a set)"
      using cb ca by simp }
  moreover {
    assume cb: "card (UNIV :: 'b set) = Suc 0"
    then obtain b where b: "UNIV = {b :: 'b}" by(auto simp add: card_Suc_eq)
    have eq: "UNIV = {\<lambda>x :: 'a. b ::'b}"
    proof(rule UNIV_eq_I)
      fix x :: "'a \<Rightarrow> 'b"
      { fix y
        have "x y \<in> UNIV" ..
        hence "x y = b" unfolding b by simp }
      thus "x \<in> {\<lambda>x. b}" by(auto intro: ext)
    qed
    have "card (UNIV :: ('a \<Rightarrow> 'b) set) = Suc 0" unfolding eq by simp }
  ultimately show "card_UNIV x = card (UNIV :: ('a \<Rightarrow> 'b) set)"
    unfolding card_UNIV_fun_def card_UNIV Let_def
    by(auto simp del: One_nat_def)(auto simp add: card_eq_0_iff dest: finite_fun_UNIVD2 finite_fun_UNIVD1)
qed

end

subsubsection {* @{typ "'a option"} *}

instantiation option :: (card_UNIV) card_UNIV
begin

definition card_UNIV_option_def: 
  "card_UNIV_class.card_UNIV = (\<lambda>a :: 'a option itself. let c = card_UNIV (TYPE('a))
                           in if c \<noteq> 0 then Suc c else 0)"

instance proof
  fix x :: "'a option itself"
  show "card_UNIV x = card (UNIV :: 'a option set)"
    unfolding UNIV_option_conv
    by(auto simp add: card_UNIV_option_def card_UNIV card_eq_0_iff Let_def intro: inj_Some dest: finite_imageD)
      (subst card_insert_disjoint, auto simp add: card_eq_0_iff card_image inj_Some intro: finite_imageI card_ge_0_finite)
qed

end


subsection {* Universal quantification *}

definition finfun_All_except :: "'a list \<Rightarrow> 'a \<Rightarrow>\<^isub>f bool \<Rightarrow> bool"
where [code del]: "finfun_All_except A P \<equiv> \<forall>a. a \<in> set A \<or> P\<^sub>f a"

lemma finfun_All_except_const: "finfun_All_except A (\<lambda>\<^isup>f b) \<longleftrightarrow> b \<or> set A = UNIV"
by(auto simp add: finfun_All_except_def)

lemma finfun_All_except_const_finfun_UNIV_code [code]:
  "finfun_All_except A (\<lambda>\<^isup>f b) = (b \<or> is_list_UNIV A)"
by(simp add: finfun_All_except_const is_list_UNIV_iff)

lemma finfun_All_except_update: 
  "finfun_All_except A f(\<^sup>f a := b) = ((a \<in> set A \<or> b) \<and> finfun_All_except (a # A) f)"
by(fastsimp simp add: finfun_All_except_def finfun_upd_apply)

lemma finfun_All_except_update_code [code]:
  fixes a :: "'a :: card_UNIV"
  shows "finfun_All_except A (finfun_update_code f a b) = ((a \<in> set A \<or> b) \<and> finfun_All_except (a # A) f)"
by(simp add: finfun_All_except_update)

definition finfun_All :: "'a \<Rightarrow>\<^isub>f bool \<Rightarrow> bool"
where "finfun_All = finfun_All_except []"

lemma finfun_All_const [simp]: "finfun_All (\<lambda>\<^isup>f b) = b"
by(simp add: finfun_All_def finfun_All_except_def)

lemma finfun_All_update: "finfun_All f(\<^sup>f a := b) = (b \<and> finfun_All_except [a] f)"
by(simp add: finfun_All_def finfun_All_except_update)

lemma finfun_All_All: "finfun_All P = All P\<^sub>f"
by(simp add: finfun_All_def finfun_All_except_def)


definition finfun_Ex :: "'a \<Rightarrow>\<^isub>f bool \<Rightarrow> bool"
where "finfun_Ex P = Not (finfun_All (Not \<circ>\<^isub>f P))"

lemma finfun_Ex_Ex: "finfun_Ex P = Ex P\<^sub>f"
unfolding finfun_Ex_def finfun_All_All by simp

lemma finfun_Ex_const [simp]: "finfun_Ex (\<lambda>\<^isup>f b) = b"
by(simp add: finfun_Ex_def)


subsection {* A diagonal operator for FinFuns *}

definition finfun_Diag :: "'a \<Rightarrow>\<^isub>f 'b \<Rightarrow> 'a \<Rightarrow>\<^isub>f 'c \<Rightarrow> 'a \<Rightarrow>\<^isub>f ('b \<times> 'c)" ("(1'(_,/ _')\<^sup>f)" [0, 0] 1000)
where [code del]: "finfun_Diag f g = finfun_rec (\<lambda>b. Pair b \<circ>\<^isub>f g) (\<lambda>a b c. c(\<^sup>f a := (b, g\<^sub>f a))) f"

interpretation finfun_Diag_aux: finfun_rec_wf_aux "\<lambda>b. Pair b \<circ>\<^isub>f g" "\<lambda>a b c. c(\<^sup>f a := (b, g\<^sub>f a))"
by(unfold_locales)(simp_all add: expand_finfun_eq expand_fun_eq finfun_upd_apply)

interpretation finfun_Diag: finfun_rec_wf "\<lambda>b. Pair b \<circ>\<^isub>f g" "\<lambda>a b c. c(\<^sup>f a := (b, g\<^sub>f a))"
proof
  fix b' b :: 'a
  assume fin: "finite (UNIV :: 'c set)"
  { fix A :: "'c set"
    interpret fun_left_comm "\<lambda>a c. c(\<^sup>f a := (b', g\<^sub>f a))" by(rule finfun_Diag_aux.upd_left_comm)
    from fin have "finite A" by(auto intro: finite_subset)
    hence "fold (\<lambda>a c. c(\<^sup>f a := (b', g\<^sub>f a))) (Pair b \<circ>\<^isub>f g) A =
      Abs_finfun (\<lambda>a. (if a \<in> A then b' else b, g\<^sub>f a))"
      by(induct)(simp_all add: finfun_const_def finfun_comp_conv_comp o_def,
                 auto simp add: finfun_update_def Abs_finfun_inverse_finite fun_upd_def Abs_finfun_inject_finite expand_fun_eq fin) }
  from this[of UNIV] show "fold (\<lambda>a c. c(\<^sup>f a := (b', g\<^sub>f a))) (Pair b \<circ>\<^isub>f g) UNIV = Pair b' \<circ>\<^isub>f g"
    by(simp add: finfun_const_def finfun_comp_conv_comp o_def)
qed

lemma finfun_Diag_const1: "(\<lambda>\<^isup>f b, g)\<^sup>f = Pair b \<circ>\<^isub>f g"
by(simp add: finfun_Diag_def)

text {*
  Do not use @{thm finfun_Diag_const1} for the code generator because @{term "Pair b"} is injective, i.e. if @{term g} is free of redundant updates, there is no need to check for redundant updates as is done for @{text "\<circ>\<^isub>f"}.
*}

lemma finfun_Diag_const_code [code]:
  "(\<lambda>\<^isup>f b, \<lambda>\<^isup>f c)\<^sup>f = (\<lambda>\<^isup>f (b, c))"
  "(\<lambda>\<^isup>f b, g(\<^sup>f\<^sup>c a := c))\<^sup>f = (\<lambda>\<^isup>f b, g)\<^sup>f(\<^sup>f\<^sup>c a := (b, c))"
by(simp_all add: finfun_Diag_const1)

lemma finfun_Diag_update1: "(f(\<^sup>f a := b), g)\<^sup>f = (f, g)\<^sup>f(\<^sup>f a := (b, g\<^sub>f a))"
  and finfun_Diag_update1_code [code]: "(finfun_update_code f a b, g)\<^sup>f = (f, g)\<^sup>f(\<^sup>f a := (b, g\<^sub>f a))"
by(simp_all add: finfun_Diag_def)

lemma finfun_Diag_const2: "(f, \<lambda>\<^isup>f c)\<^sup>f = (\<lambda>b. (b, c)) \<circ>\<^isub>f f"
by(induct f rule: finfun_weak_induct)(auto intro!: finfun_ext simp add: finfun_upd_apply finfun_Diag_const1 finfun_Diag_update1)

lemma finfun_Diag_update2: "(f, g(\<^sup>f a := c))\<^sup>f = (f, g)\<^sup>f(\<^sup>f a := (f\<^sub>f a, c))"
by(induct f rule: finfun_weak_induct)(auto intro!: finfun_ext simp add: finfun_upd_apply finfun_Diag_const1 finfun_Diag_update1)

lemma finfun_Diag_const_const [simp]: "(\<lambda>\<^isup>f b, \<lambda>\<^isup>f c)\<^sup>f = (\<lambda>\<^isup>f (b, c))"
by(simp add: finfun_Diag_const1)

lemma finfun_Diag_const_update:
  "(\<lambda>\<^isup>f b, g(\<^sup>f a := c))\<^sup>f = (\<lambda>\<^isup>f b, g)\<^sup>f(\<^sup>f a := (b, c))"
by(simp add: finfun_Diag_const1)

lemma finfun_Diag_update_const:
  "(f(\<^sup>f a := b), \<lambda>\<^isup>f c)\<^sup>f = (f, \<lambda>\<^isup>f c)\<^sup>f(\<^sup>f a := (b, c))"
by(simp add: finfun_Diag_def)

lemma finfun_Diag_update_update:
  "(f(\<^sup>f a := b), g(\<^sup>f a' := c))\<^sup>f = (if a = a' then (f, g)\<^sup>f(\<^sup>f a := (b, c)) else (f, g)\<^sup>f(\<^sup>f a := (b, g\<^sub>f a))(\<^sup>f a' := (f\<^sub>f a', c)))"
by(auto simp add: finfun_Diag_update1 finfun_Diag_update2)

lemma finfun_Diag_apply [simp]: "(f, g)\<^sup>f\<^sub>f = (\<lambda>x. (f\<^sub>f x, g\<^sub>f x))"
by(induct f rule: finfun_weak_induct)(auto simp add: finfun_Diag_const1 finfun_Diag_update1 finfun_upd_apply intro: ext)

declare finfun_simp [simp] finfun_iff [iff] finfun_intro [intro]

lemma finfun_Diag_conv_Abs_finfun:
  "(f, g)\<^sup>f = Abs_finfun ((\<lambda>x. (Rep_finfun f x, Rep_finfun g x)))"
proof -
  have "(\<lambda>f :: 'a \<Rightarrow>\<^isub>f 'b. (f, g)\<^sup>f) = (\<lambda>f. Abs_finfun ((\<lambda>x. (Rep_finfun f x, Rep_finfun g x))))"
  proof(rule finfun_rec_unique)
    { fix c show "Abs_finfun (\<lambda>x. (Rep_finfun (\<lambda>\<^isup>f c) x, Rep_finfun g x)) = Pair c \<circ>\<^isub>f g"
        by(simp add: finfun_comp_conv_comp finfun_apply_Rep_finfun o_def finfun_const_def) }
    { fix g' a b
      show "Abs_finfun (\<lambda>x. (Rep_finfun g'(\<^sup>f a := b) x, Rep_finfun g x)) =
            (Abs_finfun (\<lambda>x. (Rep_finfun g' x, Rep_finfun g x)))(\<^sup>f a := (b, g\<^sub>f a))"
        by(auto simp add: finfun_update_def expand_fun_eq finfun_apply_Rep_finfun simp del: fun_upd_apply) simp }
  qed(simp_all add: finfun_Diag_const1 finfun_Diag_update1)
  thus ?thesis by(auto simp add: expand_fun_eq)
qed

declare finfun_simp [simp del] finfun_iff [iff del] finfun_intro [rule del]

lemma finfun_Diag_eq: "(f, g)\<^sup>f = (f', g')\<^sup>f \<longleftrightarrow> f = f' \<and> g = g'"
by(auto simp add: expand_finfun_eq expand_fun_eq)

definition finfun_fst :: "'a \<Rightarrow>\<^isub>f ('b \<times> 'c) \<Rightarrow> 'a \<Rightarrow>\<^isub>f 'b"
where [code]: "finfun_fst f = fst \<circ>\<^isub>f f"

lemma finfun_fst_const: "finfun_fst (\<lambda>\<^isup>f bc) = (\<lambda>\<^isup>f fst bc)"
by(simp add: finfun_fst_def)

lemma finfun_fst_update: "finfun_fst (f(\<^sup>f a := bc)) = (finfun_fst f)(\<^sup>f a := fst bc)"
  and finfun_fst_update_code: "finfun_fst (finfun_update_code f a bc) = (finfun_fst f)(\<^sup>f a := fst bc)"
by(simp_all add: finfun_fst_def)

lemma finfun_fst_comp_conv: "finfun_fst (f \<circ>\<^isub>f g) = (fst \<circ> f) \<circ>\<^isub>f g"
by(simp add: finfun_fst_def)

lemma finfun_fst_conv [simp]: "finfun_fst (f, g)\<^sup>f = f"
by(induct f rule: finfun_weak_induct)(simp_all add: finfun_Diag_const1 finfun_fst_comp_conv o_def finfun_Diag_update1 finfun_fst_update)

lemma finfun_fst_conv_Abs_finfun: "finfun_fst = (\<lambda>f. Abs_finfun (fst o Rep_finfun f))"
by(simp add: finfun_fst_def_raw finfun_comp_conv_comp finfun_apply_Rep_finfun)


definition finfun_snd :: "'a \<Rightarrow>\<^isub>f ('b \<times> 'c) \<Rightarrow> 'a \<Rightarrow>\<^isub>f 'c"
where [code]: "finfun_snd f = snd \<circ>\<^isub>f f"

lemma finfun_snd_const: "finfun_snd (\<lambda>\<^isup>f bc) = (\<lambda>\<^isup>f snd bc)"
by(simp add: finfun_snd_def)

lemma finfun_snd_update: "finfun_snd (f(\<^sup>f a := bc)) = (finfun_snd f)(\<^sup>f a := snd bc)"
  and finfun_snd_update_code [code]: "finfun_snd (finfun_update_code f a bc) = (finfun_snd f)(\<^sup>f a := snd bc)"
by(simp_all add: finfun_snd_def)

lemma finfun_snd_comp_conv: "finfun_snd (f \<circ>\<^isub>f g) = (snd \<circ> f) \<circ>\<^isub>f g"
by(simp add: finfun_snd_def)

lemma finfun_snd_conv [simp]: "finfun_snd (f, g)\<^sup>f = g"
apply(induct f rule: finfun_weak_induct)
apply(auto simp add: finfun_Diag_const1 finfun_snd_comp_conv o_def finfun_Diag_update1 finfun_snd_update finfun_upd_apply intro: finfun_ext)
done

lemma finfun_snd_conv_Abs_finfun: "finfun_snd = (\<lambda>f. Abs_finfun (snd o Rep_finfun f))"
by(simp add: finfun_snd_def_raw finfun_comp_conv_comp finfun_apply_Rep_finfun)

lemma finfun_Diag_collapse [simp]: "(finfun_fst f, finfun_snd f)\<^sup>f = f"
by(induct f rule: finfun_weak_induct)(simp_all add: finfun_fst_const finfun_snd_const finfun_fst_update finfun_snd_update finfun_Diag_update_update)

subsection {* Currying for FinFuns *}

definition finfun_curry :: "('a \<times> 'b) \<Rightarrow>\<^isub>f 'c \<Rightarrow> 'a \<Rightarrow>\<^isub>f 'b \<Rightarrow>\<^isub>f 'c"
where [code del]: "finfun_curry = finfun_rec (finfun_const \<circ> finfun_const) (\<lambda>(a, b) c f. f(\<^sup>f a := (f\<^sub>f a)(\<^sup>f b := c)))"

interpretation finfun_curry_aux: finfun_rec_wf_aux "finfun_const \<circ> finfun_const" "\<lambda>(a, b) c f. f(\<^sup>f a := (f\<^sub>f a)(\<^sup>f b := c))"
apply(unfold_locales)
apply(auto simp add: split_def finfun_update_twist finfun_upd_apply split_paired_all finfun_update_const_same)
done

declare finfun_simp [simp] finfun_iff [iff] finfun_intro [intro]

interpretation finfun_curry: finfun_rec_wf "finfun_const \<circ> finfun_const" "\<lambda>(a, b) c f. f(\<^sup>f a := (f\<^sub>f a)(\<^sup>f b := c))"
proof(unfold_locales)
  fix b' b :: 'b
  assume fin: "finite (UNIV :: ('c \<times> 'a) set)"
  hence fin1: "finite (UNIV :: 'c set)" and fin2: "finite (UNIV :: 'a set)"
    unfolding UNIV_Times_UNIV[symmetric]
    by(fastsimp dest: finite_cartesian_productD1 finite_cartesian_productD2)+
  note [simp] = Abs_finfun_inverse_finite[OF fin] Abs_finfun_inverse_finite[OF fin1] Abs_finfun_inverse_finite[OF fin2]
  { fix A :: "('c \<times> 'a) set"
    interpret fun_left_comm "\<lambda>a :: 'c \<times> 'a. (\<lambda>(a, b) c f. f(\<^sup>f a := (f\<^sub>f a)(\<^sup>f b := c))) a b'"
      by(rule finfun_curry_aux.upd_left_comm)
    from fin have "finite A" by(auto intro: finite_subset)
    hence "fold (\<lambda>a :: 'c \<times> 'a. (\<lambda>(a, b) c f. f(\<^sup>f a := (f\<^sub>f a)(\<^sup>f b := c))) a b') ((finfun_const \<circ> finfun_const) b) A = Abs_finfun (\<lambda>a. Abs_finfun (\<lambda>b''. if (a, b'') \<in> A then b' else b))"
      by induct (simp_all, auto simp add: finfun_update_def finfun_const_def split_def finfun_apply_Rep_finfun intro!: arg_cong[where f="Abs_finfun"] ext) }
  from this[of UNIV]
  show "fold (\<lambda>a :: 'c \<times> 'a. (\<lambda>(a, b) c f. f(\<^sup>f a := (f\<^sub>f a)(\<^sup>f b := c))) a b') ((finfun_const \<circ> finfun_const) b) UNIV = (finfun_const \<circ> finfun_const) b'"
    by(simp add: finfun_const_def)
qed

declare finfun_simp [simp del] finfun_iff [iff del] finfun_intro [rule del]

lemma finfun_curry_const [simp, code]: "finfun_curry (\<lambda>\<^isup>f c) = (\<lambda>\<^isup>f \<lambda>\<^isup>f c)"
by(simp add: finfun_curry_def)

lemma finfun_curry_update [simp]:
  "finfun_curry (f(\<^sup>f (a, b) := c)) = (finfun_curry f)(\<^sup>f a := ((finfun_curry f)\<^sub>f a)(\<^sup>f b := c))"
  and finfun_curry_update_code [code]:
  "finfun_curry (f(\<^sup>f\<^sup>c (a, b) := c)) = (finfun_curry f)(\<^sup>f a := ((finfun_curry f)\<^sub>f a)(\<^sup>f b := c))"
by(simp_all add: finfun_curry_def)

declare finfun_simp [simp] finfun_iff [iff] finfun_intro [intro]

lemma finfun_Abs_finfun_curry: assumes fin: "f \<in> finfun"
  shows "(\<lambda>a. Abs_finfun (curry f a)) \<in> finfun"
proof -
  from fin obtain c where c: "finite {ab. f ab \<noteq> c}" unfolding finfun_def by blast
  have "{a. \<exists>b. f (a, b) \<noteq> c} = fst ` {ab. f ab \<noteq> c}" by(force)
  hence "{a. curry f a \<noteq> (\<lambda>x. c)} = fst ` {ab. f ab \<noteq> c}"
    by(auto simp add: curry_def expand_fun_eq)
  with fin c have "finite {a.  Abs_finfun (curry f a) \<noteq> (\<lambda>\<^isup>f c)}"
    by(simp add: finfun_const_def finfun_curry)
  thus ?thesis unfolding finfun_def by auto
qed

lemma finfun_curry_conv_curry:
  fixes f :: "('a \<times> 'b) \<Rightarrow>\<^isub>f 'c"
  shows "finfun_curry f = Abs_finfun (\<lambda>a. Abs_finfun (curry (Rep_finfun f) a))"
proof -
  have "finfun_curry = (\<lambda>f :: ('a \<times> 'b) \<Rightarrow>\<^isub>f 'c. Abs_finfun (\<lambda>a. Abs_finfun (curry (Rep_finfun f) a)))"
  proof(rule finfun_rec_unique)
    { fix c show "finfun_curry (\<lambda>\<^isup>f c) = (\<lambda>\<^isup>f \<lambda>\<^isup>f c)" by simp }
    { fix f a c show "finfun_curry (f(\<^sup>f a := c)) = (finfun_curry f)(\<^sup>f fst a := ((finfun_curry f)\<^sub>f (fst a))(\<^sup>f snd a := c))"
        by(cases a) simp }
    { fix c show "Abs_finfun (\<lambda>a. Abs_finfun (curry (Rep_finfun (\<lambda>\<^isup>f c)) a)) = (\<lambda>\<^isup>f \<lambda>\<^isup>f c)"
        by(simp add: finfun_curry_def finfun_const_def curry_def) }
    { fix g a b
      show "Abs_finfun (\<lambda>aa. Abs_finfun (curry (Rep_finfun g(\<^sup>f a := b)) aa)) =
       (Abs_finfun (\<lambda>a. Abs_finfun (curry (Rep_finfun g) a)))(\<^sup>f
       fst a := ((Abs_finfun (\<lambda>a. Abs_finfun (curry (Rep_finfun g) a)))\<^sub>f (fst a))(\<^sup>f snd a := b))"
        by(cases a)(auto intro!: ext arg_cong[where f=Abs_finfun] simp add: finfun_curry_def finfun_update_def finfun_apply_Rep_finfun finfun_curry finfun_Abs_finfun_curry) }
  qed
  thus ?thesis by(auto simp add: expand_fun_eq)
qed

subsection {* Executable equality for FinFuns *}

lemma eq_finfun_All_ext: "(f = g) \<longleftrightarrow> finfun_All ((\<lambda>(x, y). x = y) \<circ>\<^isub>f (f, g)\<^sup>f)"
by(simp add: expand_finfun_eq expand_fun_eq finfun_All_All o_def)

instantiation finfun :: ("{card_UNIV,eq}",eq) eq begin
definition eq_finfun_def: "eq_class.eq f g \<longleftrightarrow> finfun_All ((\<lambda>(x, y). x = y) \<circ>\<^isub>f (f, g)\<^sup>f)"
instance by(intro_classes)(simp add: eq_finfun_All_ext eq_finfun_def)
end

subsection {* Operator that explicitly removes all redundant updates in the generated representations *}

definition finfun_clearjunk :: "'a \<Rightarrow>\<^isub>f 'b \<Rightarrow> 'a \<Rightarrow>\<^isub>f 'b"
where [simp, code del]: "finfun_clearjunk = id"

lemma finfun_clearjunk_const [code]: "finfun_clearjunk (\<lambda>\<^isup>f b) = (\<lambda>\<^isup>f b)"
by simp

lemma finfun_clearjunk_update [code]: "finfun_clearjunk (finfun_update_code f a b) = f(\<^sup>f a := b)"
by simp

end