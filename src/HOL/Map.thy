(*  Title:      HOL/Map.thy
    Author:     Tobias Nipkow, based on a theory by David von Oheimb
    Copyright   1997-2003 TU Muenchen

The datatype of "maps"; strongly resembles maps in VDM.
*)

section \<open>Maps\<close>

theory Map
  imports List
  abbrevs "(=" = "\<subseteq>\<^sub>m"
begin

type_synonym ('a, 'b) "map" = "'a \<Rightarrow> 'b option" (infixr "\<rightharpoonup>" 0)

abbreviation
  empty :: "'a \<rightharpoonup> 'b" where
  "empty \<equiv> \<lambda>x. None"

definition
  map_comp :: "('b \<rightharpoonup> 'c) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'c)"  (infixl "\<circ>\<^sub>m" 55) where
  "f \<circ>\<^sub>m g = (\<lambda>k. case g k of None \<Rightarrow> None | Some v \<Rightarrow> f v)"

definition
  map_add :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)"  (infixl "++" 100) where
  "m1 ++ m2 = (\<lambda>x. case m2 x of None \<Rightarrow> m1 x | Some y \<Rightarrow> Some y)"

definition
  restrict_map :: "('a \<rightharpoonup> 'b) \<Rightarrow> 'a set \<Rightarrow> ('a \<rightharpoonup> 'b)"  (infixl "|`"  110) where
  "m|`A = (\<lambda>x. if x \<in> A then m x else None)"

notation (latex output)
  restrict_map  ("_\<restriction>\<^bsub>_\<^esub>" [111,110] 110)

definition
  dom :: "('a \<rightharpoonup> 'b) \<Rightarrow> 'a set" where
  "dom m = {a. m a \<noteq> None}"

definition
  ran :: "('a \<rightharpoonup> 'b) \<Rightarrow> 'b set" where
  "ran m = {b. \<exists>a. m a = Some b}"

definition
  graph :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<times> 'b) set" where
  "graph m = {(a, b) | a b. m a = Some b}"

definition
  map_le :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> bool"  (infix "\<subseteq>\<^sub>m" 50) where
  "(m\<^sub>1 \<subseteq>\<^sub>m m\<^sub>2) \<longleftrightarrow> (\<forall>a \<in> dom m\<^sub>1. m\<^sub>1 a = m\<^sub>2 a)"

nonterminal maplets and maplet

syntax
  "_maplet"  :: "['a, 'a] \<Rightarrow> maplet"             ("_ /\<mapsto>/ _")
  "_maplets" :: "['a, 'a] \<Rightarrow> maplet"             ("_ /[\<mapsto>]/ _")
  ""         :: "maplet \<Rightarrow> maplets"             ("_")
  "_Maplets" :: "[maplet, maplets] \<Rightarrow> maplets" ("_,/ _")
  "_MapUpd"  :: "['a \<rightharpoonup> 'b, maplets] \<Rightarrow> 'a \<rightharpoonup> 'b" ("_/'(_')" [900, 0] 900)
  "_Map"     :: "maplets \<Rightarrow> 'a \<rightharpoonup> 'b"            ("(1[_])")

syntax (ASCII)
  "_maplet"  :: "['a, 'a] \<Rightarrow> maplet"             ("_ /|->/ _")
  "_maplets" :: "['a, 'a] \<Rightarrow> maplet"             ("_ /[|->]/ _")

translations
  "_MapUpd m (_Maplets xy ms)"  \<rightleftharpoons> "_MapUpd (_MapUpd m xy) ms"
  "_MapUpd m (_maplet  x y)"    \<rightleftharpoons> "m(x := CONST Some y)"
  "_Map ms"                     \<rightleftharpoons> "_MapUpd (CONST empty) ms"
  "_Map (_Maplets ms1 ms2)"     \<leftharpoondown> "_MapUpd (_Map ms1) ms2"
  "_Maplets ms1 (_Maplets ms2 ms3)" \<leftharpoondown> "_Maplets (_Maplets ms1 ms2) ms3"

primrec map_of :: "('a \<times> 'b) list \<Rightarrow> 'a \<rightharpoonup> 'b"
where
  "map_of [] = empty"
| "map_of (p # ps) = (map_of ps)(fst p \<mapsto> snd p)"

definition map_upds :: "('a \<rightharpoonup> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'a \<rightharpoonup> 'b"
  where "map_upds m xs ys = m ++ map_of (rev (zip xs ys))"
translations
  "_MapUpd m (_maplets x y)" \<rightleftharpoons> "CONST map_upds m x y"

lemma map_of_Cons_code [code]:
  "map_of [] k = None"
  "map_of ((l, v) # ps) k = (if l = k then Some v else map_of ps k)"
  by simp_all


subsection \<open>@{term [source] empty}\<close>

lemma empty_upd_none [simp]: "empty(x := None) = empty"
  by (rule ext) simp


subsection \<open>@{term [source] map_upd}\<close>

lemma map_upd_triv: "t k = Some x \<Longrightarrow> t(k\<mapsto>x) = t"
  by (rule ext) simp

lemma map_upd_nonempty [simp]: "t(k\<mapsto>x) \<noteq> empty"
proof
  assume "t(k \<mapsto> x) = empty"
  then have "(t(k \<mapsto> x)) k = None" by simp
  then show False by simp
qed

lemma map_upd_eqD1:
  assumes "m(a\<mapsto>x) = n(a\<mapsto>y)"
  shows "x = y"
proof -
  from assms have "(m(a\<mapsto>x)) a = (n(a\<mapsto>y)) a" by simp
  then show ?thesis by simp
qed

lemma map_upd_Some_unfold:
  "((m(a\<mapsto>b)) x = Some y) = (x = a \<and> b = y \<or> x \<noteq> a \<and> m x = Some y)"
  by auto

lemma image_map_upd [simp]: "x \<notin> A \<Longrightarrow> m(x \<mapsto> y) ` A = m ` A"
  by auto

lemma finite_range_updI:
  assumes "finite (range f)" shows "finite (range (f(a\<mapsto>b)))"
proof -
  have "range (f(a\<mapsto>b)) \<subseteq> insert (Some b) (range f)"
    by auto
  then show ?thesis
    by (rule finite_subset) (use assms in auto)
qed


subsection \<open>@{term [source] map_of}\<close>

lemma map_of_eq_empty_iff [simp]:
  "map_of xys = empty \<longleftrightarrow> xys = []"
proof
  show "map_of xys = empty \<Longrightarrow> xys = []"
    by (induction xys) simp_all
qed simp

lemma empty_eq_map_of_iff [simp]:
  "empty = map_of xys \<longleftrightarrow> xys = []"
by(subst eq_commute) simp

lemma map_of_eq_None_iff:
  "(map_of xys x = None) = (x \<notin> fst ` (set xys))"
by (induct xys) simp_all

lemma map_of_eq_Some_iff [simp]:
  "distinct(map fst xys) \<Longrightarrow> (map_of xys x = Some y) = ((x,y) \<in> set xys)"
proof (induct xys)
  case (Cons xy xys)
  then show ?case
    by (cases xy) (auto simp flip: map_of_eq_None_iff)
qed auto

lemma Some_eq_map_of_iff [simp]:
  "distinct(map fst xys) \<Longrightarrow> (Some y = map_of xys x) = ((x,y) \<in> set xys)"
by (auto simp del: map_of_eq_Some_iff simp: map_of_eq_Some_iff [symmetric])

lemma map_of_is_SomeI [simp]: 
  "\<lbrakk>distinct(map fst xys); (x,y) \<in> set xys\<rbrakk> \<Longrightarrow> map_of xys x = Some y"
  by simp

lemma map_of_zip_is_None [simp]:
  "length xs = length ys \<Longrightarrow> (map_of (zip xs ys) x = None) = (x \<notin> set xs)"
by (induct rule: list_induct2) simp_all

lemma map_of_zip_is_Some:
  assumes "length xs = length ys"
  shows "x \<in> set xs \<longleftrightarrow> (\<exists>y. map_of (zip xs ys) x = Some y)"
using assms by (induct rule: list_induct2) simp_all

lemma map_of_zip_upd:
  fixes x :: 'a and xs :: "'a list" and ys zs :: "'b list"
  assumes "length ys = length xs"
    and "length zs = length xs"
    and "x \<notin> set xs"
    and "map_of (zip xs ys)(x \<mapsto> y) = map_of (zip xs zs)(x \<mapsto> z)"
  shows "map_of (zip xs ys) = map_of (zip xs zs)"
proof
  fix x' :: 'a
  show "map_of (zip xs ys) x' = map_of (zip xs zs) x'"
  proof (cases "x = x'")
    case True
    from assms True map_of_zip_is_None [of xs ys x']
      have "map_of (zip xs ys) x' = None" by simp
    moreover from assms True map_of_zip_is_None [of xs zs x']
      have "map_of (zip xs zs) x' = None" by simp
    ultimately show ?thesis by simp
  next
    case False from assms
      have "(map_of (zip xs ys)(x \<mapsto> y)) x' = (map_of (zip xs zs)(x \<mapsto> z)) x'" by auto
    with False show ?thesis by simp
  qed
qed

lemma map_of_zip_inject:
  assumes "length ys = length xs"
    and "length zs = length xs"
    and dist: "distinct xs"
    and map_of: "map_of (zip xs ys) = map_of (zip xs zs)"
  shows "ys = zs"
  using assms(1) assms(2)[symmetric]
  using dist map_of
proof (induct ys xs zs rule: list_induct3)
  case Nil show ?case by simp
next
  case (Cons y ys x xs z zs)
  from \<open>map_of (zip (x#xs) (y#ys)) = map_of (zip (x#xs) (z#zs))\<close>
    have map_of: "map_of (zip xs ys)(x \<mapsto> y) = map_of (zip xs zs)(x \<mapsto> z)" by simp
  from Cons have "length ys = length xs" and "length zs = length xs"
    and "x \<notin> set xs" by simp_all
  then have "map_of (zip xs ys) = map_of (zip xs zs)" using map_of by (rule map_of_zip_upd)
  with Cons.hyps \<open>distinct (x # xs)\<close> have "ys = zs" by simp
  moreover from map_of have "y = z" by (rule map_upd_eqD1)
  ultimately show ?case by simp
qed

lemma map_of_zip_nth:
  assumes "length xs = length ys"
  assumes "distinct xs"
  assumes "i < length ys"
  shows "map_of (zip xs ys) (xs ! i) = Some (ys ! i)"
using assms proof (induct arbitrary: i rule: list_induct2)
  case Nil
  then show ?case by simp
next
  case (Cons x xs y ys)
  then show ?case
    using less_Suc_eq_0_disj by auto
qed

lemma map_of_zip_map:
  "map_of (zip xs (map f xs)) = (\<lambda>x. if x \<in> set xs then Some (f x) else None)"
  by (induct xs) (simp_all add: fun_eq_iff)

lemma finite_range_map_of: "finite (range (map_of xys))"
proof (induct xys)
  case (Cons a xys)
  then show ?case
    using finite_range_updI by fastforce
qed auto

lemma map_of_SomeD: "map_of xs k = Some y \<Longrightarrow> (k, y) \<in> set xs"
  by (induct xs) (auto split: if_splits)

lemma map_of_mapk_SomeI:
  "inj f \<Longrightarrow> map_of t k = Some x \<Longrightarrow>
   map_of (map (case_prod (\<lambda>k. Pair (f k))) t) (f k) = Some x"
by (induct t) (auto simp: inj_eq)

lemma weak_map_of_SomeI: "(k, x) \<in> set l \<Longrightarrow> \<exists>x. map_of l k = Some x"
by (induct l) auto

lemma map_of_filter_in:
  "map_of xs k = Some z \<Longrightarrow> P k z \<Longrightarrow> map_of (filter (case_prod P) xs) k = Some z"
by (induct xs) auto

lemma map_of_map:
  "map_of (map (\<lambda>(k, v). (k, f v)) xs) = map_option f \<circ> map_of xs"
  by (induct xs) (auto simp: fun_eq_iff)

lemma dom_map_option:
  "dom (\<lambda>k. map_option (f k) (m k)) = dom m"
  by (simp add: dom_def)

lemma dom_map_option_comp [simp]:
  "dom (map_option g \<circ> m) = dom m"
  using dom_map_option [of "\<lambda>_. g" m] by (simp add: comp_def)


subsection \<open>\<^const>\<open>map_option\<close> related\<close>

lemma map_option_o_empty [simp]: "map_option f \<circ> empty = empty"
by (rule ext) simp

lemma map_option_o_map_upd [simp]:
  "map_option f \<circ> m(a\<mapsto>b) = (map_option f \<circ> m)(a\<mapsto>f b)"
by (rule ext) simp


subsection \<open>@{term [source] map_comp} related\<close>

lemma map_comp_empty [simp]:
  "m \<circ>\<^sub>m empty = empty"
  "empty \<circ>\<^sub>m m = empty"
by (auto simp: map_comp_def split: option.splits)

lemma map_comp_simps [simp]:
  "m2 k = None \<Longrightarrow> (m1 \<circ>\<^sub>m m2) k = None"
  "m2 k = Some k' \<Longrightarrow> (m1 \<circ>\<^sub>m m2) k = m1 k'"
by (auto simp: map_comp_def)

lemma map_comp_Some_iff:
  "((m1 \<circ>\<^sub>m m2) k = Some v) = (\<exists>k'. m2 k = Some k' \<and> m1 k' = Some v)"
by (auto simp: map_comp_def split: option.splits)

lemma map_comp_None_iff:
  "((m1 \<circ>\<^sub>m m2) k = None) = (m2 k = None \<or> (\<exists>k'. m2 k = Some k' \<and> m1 k' = None)) "
by (auto simp: map_comp_def split: option.splits)


subsection \<open>\<open>++\<close>\<close>

lemma map_add_empty[simp]: "m ++ empty = m"
by(simp add: map_add_def)

lemma empty_map_add[simp]: "empty ++ m = m"
by (rule ext) (simp add: map_add_def split: option.split)

lemma map_add_assoc[simp]: "m1 ++ (m2 ++ m3) = (m1 ++ m2) ++ m3"
by (rule ext) (simp add: map_add_def split: option.split)

lemma map_add_Some_iff:
  "((m ++ n) k = Some x) = (n k = Some x \<or> n k = None \<and> m k = Some x)"
by (simp add: map_add_def split: option.split)

lemma map_add_SomeD [dest!]:
  "(m ++ n) k = Some x \<Longrightarrow> n k = Some x \<or> n k = None \<and> m k = Some x"
by (rule map_add_Some_iff [THEN iffD1])

lemma map_add_find_right [simp]: "n k = Some xx \<Longrightarrow> (m ++ n) k = Some xx"
by (subst map_add_Some_iff) fast

lemma map_add_None [iff]: "((m ++ n) k = None) = (n k = None \<and> m k = None)"
by (simp add: map_add_def split: option.split)

lemma map_add_upd[simp]: "f ++ g(x\<mapsto>y) = (f ++ g)(x\<mapsto>y)"
by (rule ext) (simp add: map_add_def)

lemma map_add_upds[simp]: "m1 ++ (m2(xs[\<mapsto>]ys)) = (m1++m2)(xs[\<mapsto>]ys)"
by (simp add: map_upds_def)

lemma map_add_upd_left: "m\<notin>dom e2 \<Longrightarrow> e1(m \<mapsto> u1) ++ e2 = (e1 ++ e2)(m \<mapsto> u1)"
by (rule ext) (auto simp: map_add_def dom_def split: option.split)

lemma map_of_append[simp]: "map_of (xs @ ys) = map_of ys ++ map_of xs"
  unfolding map_add_def
proof (induct xs)
  case (Cons a xs)
  then show ?case
    by (force split: option.split)
qed auto

lemma finite_range_map_of_map_add:
  "finite (range f) \<Longrightarrow> finite (range (f ++ map_of l))"
proof (induct l)
case (Cons a l)
  then show ?case
    by (metis finite_range_updI map_add_upd map_of.simps(2))
qed auto

lemma inj_on_map_add_dom [iff]:
  "inj_on (m ++ m') (dom m') = inj_on m' (dom m')"
  by (fastforce simp: map_add_def dom_def inj_on_def split: option.splits)

lemma map_upds_fold_map_upd:
  "m(ks[\<mapsto>]vs) = foldl (\<lambda>m (k, v). m(k \<mapsto> v)) m (zip ks vs)"
unfolding map_upds_def proof (rule sym, rule zip_obtain_same_length)
  fix ks :: "'a list" and vs :: "'b list"
  assume "length ks = length vs"
  then show "foldl (\<lambda>m (k, v). m(k\<mapsto>v)) m (zip ks vs) = m ++ map_of (rev (zip ks vs))"
    by(induct arbitrary: m rule: list_induct2) simp_all
qed

lemma map_add_map_of_foldr:
  "m ++ map_of ps = foldr (\<lambda>(k, v) m. m(k \<mapsto> v)) ps m"
  by (induct ps) (auto simp: fun_eq_iff map_add_def)


subsection \<open>@{term [source] restrict_map}\<close>

lemma restrict_map_to_empty [simp]: "m|`{} = empty"
  by (simp add: restrict_map_def)

lemma restrict_map_insert: "f |` (insert a A) = (f |` A)(a := f a)"
  by (auto simp: restrict_map_def)

lemma restrict_map_empty [simp]: "empty|`D = empty"
  by (simp add: restrict_map_def)

lemma restrict_in [simp]: "x \<in> A \<Longrightarrow> (m|`A) x = m x"
  by (simp add: restrict_map_def)

lemma restrict_out [simp]: "x \<notin> A \<Longrightarrow> (m|`A) x = None"
  by (simp add: restrict_map_def)

lemma ran_restrictD: "y \<in> ran (m|`A) \<Longrightarrow> \<exists>x\<in>A. m x = Some y"
  by (auto simp: restrict_map_def ran_def split: if_split_asm)

lemma dom_restrict [simp]: "dom (m|`A) = dom m \<inter> A"
  by (auto simp: restrict_map_def dom_def split: if_split_asm)

lemma restrict_upd_same [simp]: "m(x\<mapsto>y)|`(-{x}) = m|`(-{x})"
  by (rule ext) (auto simp: restrict_map_def)

lemma restrict_restrict [simp]: "m|`A|`B = m|`(A\<inter>B)"
  by (rule ext) (auto simp: restrict_map_def)

lemma restrict_fun_upd [simp]:
  "m(x := y)|`D = (if x \<in> D then (m|`(D-{x}))(x := y) else m|`D)"
  by (simp add: restrict_map_def fun_eq_iff)

lemma fun_upd_None_restrict [simp]:
  "(m|`D)(x := None) = (if x \<in> D then m|`(D - {x}) else m|`D)"
  by (simp add: restrict_map_def fun_eq_iff)

lemma fun_upd_restrict: "(m|`D)(x := y) = (m|`(D-{x}))(x := y)"
  by (simp add: restrict_map_def fun_eq_iff)

lemma fun_upd_restrict_conv [simp]:
  "x \<in> D \<Longrightarrow> (m|`D)(x := y) = (m|`(D-{x}))(x := y)"
  by (rule fun_upd_restrict)

lemma map_of_map_restrict:
  "map_of (map (\<lambda>k. (k, f k)) ks) = (Some \<circ> f) |` set ks"
  by (induct ks) (simp_all add: fun_eq_iff restrict_map_insert)

lemma restrict_complement_singleton_eq:
  "f |` (- {x}) = f(x := None)"
  by auto


subsection \<open>@{term [source] map_upds}\<close>

lemma map_upds_Nil1 [simp]: "m([] [\<mapsto>] bs) = m"
  by (simp add: map_upds_def)

lemma map_upds_Nil2 [simp]: "m(as [\<mapsto>] []) = m"
  by (simp add:map_upds_def)

lemma map_upds_Cons [simp]: "m(a#as [\<mapsto>] b#bs) = (m(a\<mapsto>b))(as[\<mapsto>]bs)"
  by (simp add:map_upds_def)

lemma map_upds_append1 [simp]:
  "size xs < size ys \<Longrightarrow> m(xs@[x] [\<mapsto>] ys) = m(xs [\<mapsto>] ys)(x \<mapsto> ys!size xs)"
proof (induct xs arbitrary: ys m)
  case Nil
  then show ?case
    by (auto simp: neq_Nil_conv)
next
  case (Cons a xs)
  then show ?case
    by (cases ys) auto
qed

lemma map_upds_list_update2_drop [simp]:
  "size xs \<le> i \<Longrightarrow> m(xs[\<mapsto>]ys[i:=y]) = m(xs[\<mapsto>]ys)"
proof (induct xs arbitrary: m ys i)
  case Nil
  then show ?case
    by auto
next
  case (Cons a xs)
  then show ?case
    by (cases ys) (use Cons in \<open>auto split: nat.split\<close>)
qed

text \<open>Something weirdly sensitive about this proof, which needs only four lines in apply style\<close>
lemma map_upd_upds_conv_if:
  "(f(x\<mapsto>y))(xs [\<mapsto>] ys) =
   (if x \<in> set(take (length ys) xs) then f(xs [\<mapsto>] ys)
                                    else (f(xs [\<mapsto>] ys))(x\<mapsto>y))"
proof (induct xs arbitrary: x y ys f)
  case (Cons a xs)
  show ?case
  proof (cases ys)
    case (Cons z zs)
    then show ?thesis
      using Cons.hyps
      apply (auto split: if_split simp: fun_upd_twist)
      using Cons.hyps apply fastforce+
      done
  qed auto
qed auto


lemma map_upds_twist [simp]:
  "a \<notin> set as \<Longrightarrow> m(a\<mapsto>b)(as[\<mapsto>]bs) = m(as[\<mapsto>]bs)(a\<mapsto>b)"
using set_take_subset by (fastforce simp add: map_upd_upds_conv_if)

lemma map_upds_apply_nontin [simp]:
  "x \<notin> set xs \<Longrightarrow> (f(xs[\<mapsto>]ys)) x = f x"
proof (induct xs arbitrary: ys)
  case (Cons a xs)
  then show ?case
    by (cases ys) (auto simp: map_upd_upds_conv_if)
qed auto

lemma fun_upds_append_drop [simp]:
  "size xs = size ys \<Longrightarrow> m(xs@zs[\<mapsto>]ys) = m(xs[\<mapsto>]ys)"
proof (induct xs arbitrary: ys)
  case (Cons a xs)
  then show ?case
    by (cases ys) (auto simp: map_upd_upds_conv_if)
qed auto

lemma fun_upds_append2_drop [simp]:
  "size xs = size ys \<Longrightarrow> m(xs[\<mapsto>]ys@zs) = m(xs[\<mapsto>]ys)"
proof (induct xs arbitrary: ys)
  case (Cons a xs)
  then show ?case
    by (cases ys) (auto simp: map_upd_upds_conv_if)
qed auto

lemma restrict_map_upds[simp]:
  "\<lbrakk> length xs = length ys; set xs \<subseteq> D \<rbrakk>
    \<Longrightarrow> m(xs [\<mapsto>] ys)|`D = (m|`(D - set xs))(xs [\<mapsto>] ys)"
proof (induct xs arbitrary: m ys)
  case (Cons a xs)
  then show ?case
  proof (cases ys)
    case (Cons z zs)
    with Cons.hyps Cons.prems show ?thesis
      apply (simp add: insert_absorb flip: Diff_insert)
      apply (auto simp add: map_upd_upds_conv_if)
      done
  qed auto
qed auto


subsection \<open>@{term [source] dom}\<close>

lemma dom_eq_empty_conv [simp]: "dom f = {} \<longleftrightarrow> f = empty"
  by (auto simp: dom_def)

lemma domI: "m a = Some b \<Longrightarrow> a \<in> dom m"
  by (simp add: dom_def)
(* declare domI [intro]? *)

lemma domD: "a \<in> dom m \<Longrightarrow> \<exists>b. m a = Some b"
  by (cases "m a") (auto simp add: dom_def)

lemma domIff [iff, simp del, code_unfold]: "a \<in> dom m \<longleftrightarrow> m a \<noteq> None"
  by (simp add: dom_def)

lemma dom_empty [simp]: "dom empty = {}"
  by (simp add: dom_def)

lemma dom_fun_upd [simp]:
  "dom(f(x := y)) = (if y = None then dom f - {x} else insert x (dom f))"
  by (auto simp: dom_def)

lemma dom_if:
  "dom (\<lambda>x. if P x then f x else g x) = dom f \<inter> {x. P x} \<union> dom g \<inter> {x. \<not> P x}"
  by (auto split: if_splits)

lemma dom_map_of_conv_image_fst:
  "dom (map_of xys) = fst ` set xys"
  by (induct xys) (auto simp add: dom_if)

lemma dom_map_of_zip [simp]: "length xs = length ys \<Longrightarrow> dom (map_of (zip xs ys)) = set xs"
  by (induct rule: list_induct2) (auto simp: dom_if)

lemma finite_dom_map_of: "finite (dom (map_of l))"
  by (induct l) (auto simp: dom_def insert_Collect [symmetric])

lemma dom_map_upds [simp]:
  "dom(m(xs[\<mapsto>]ys)) = set(take (length ys) xs) \<union> dom m"
proof (induct xs arbitrary: ys)
  case (Cons a xs)
  then show ?case
    by (cases ys) (auto simp: map_upd_upds_conv_if)
qed auto


lemma dom_map_add [simp]: "dom (m ++ n) = dom n \<union> dom m"
  by (auto simp: dom_def)

lemma dom_override_on [simp]:
  "dom (override_on f g A) =
    (dom f  - {a. a \<in> A - dom g}) \<union> {a. a \<in> A \<inter> dom g}"
  by (auto simp: dom_def override_on_def)

lemma map_add_comm: "dom m1 \<inter> dom m2 = {} \<Longrightarrow> m1 ++ m2 = m2 ++ m1"
  by (rule ext) (force simp: map_add_def dom_def split: option.split)

lemma map_add_dom_app_simps:
  "m \<in> dom l2 \<Longrightarrow> (l1 ++ l2) m = l2 m"
  "m \<notin> dom l1 \<Longrightarrow> (l1 ++ l2) m = l2 m"
  "m \<notin> dom l2 \<Longrightarrow> (l1 ++ l2) m = l1 m"
  by (auto simp add: map_add_def split: option.split_asm)

lemma dom_const [simp]:
  "dom (\<lambda>x. Some (f x)) = UNIV"
  by auto

(* Due to John Matthews - could be rephrased with dom *)
lemma finite_map_freshness:
  "finite (dom (f :: 'a \<rightharpoonup> 'b)) \<Longrightarrow> \<not> finite (UNIV :: 'a set) \<Longrightarrow>
   \<exists>x. f x = None"
  by (bestsimp dest: ex_new_if_finite)

lemma dom_minus:
  "f x = None \<Longrightarrow> dom f - insert x A = dom f - A"
  unfolding dom_def by simp

lemma insert_dom:
  "f x = Some y \<Longrightarrow> insert x (dom f) = dom f"
  unfolding dom_def by auto

lemma map_of_map_keys:
  "set xs = dom m \<Longrightarrow> map_of (map (\<lambda>k. (k, the (m k))) xs) = m"
  by (rule ext) (auto simp add: map_of_map_restrict restrict_map_def)

lemma map_of_eqI:
  assumes set_eq: "set (map fst xs) = set (map fst ys)"
  assumes map_eq: "\<forall>k\<in>set (map fst xs). map_of xs k = map_of ys k"
  shows "map_of xs = map_of ys"
proof (rule ext)
  fix k show "map_of xs k = map_of ys k"
  proof (cases "map_of xs k")
    case None
    then have "k \<notin> set (map fst xs)" by (simp add: map_of_eq_None_iff)
    with set_eq have "k \<notin> set (map fst ys)" by simp
    then have "map_of ys k = None" by (simp add: map_of_eq_None_iff)
    with None show ?thesis by simp
  next
    case (Some v)
    then have "k \<in> set (map fst xs)" by (auto simp add: dom_map_of_conv_image_fst [symmetric])
    with map_eq show ?thesis by auto
  qed
qed

lemma map_of_eq_dom:
  assumes "map_of xs = map_of ys"
  shows "fst ` set xs = fst ` set ys"
proof -
  from assms have "dom (map_of xs) = dom (map_of ys)" by simp
  then show ?thesis by (simp add: dom_map_of_conv_image_fst)
qed

lemma finite_set_of_finite_maps:
  assumes "finite A" "finite B"
  shows "finite {m. dom m = A \<and> ran m \<subseteq> B}" (is "finite ?S")
proof -
  let ?S' = "{m. \<forall>x. (x \<in> A \<longrightarrow> m x \<in> Some ` B) \<and> (x \<notin> A \<longrightarrow> m x = None)}"
  have "?S = ?S'"
  proof
    show "?S \<subseteq> ?S'" by (auto simp: dom_def ran_def image_def)
    show "?S' \<subseteq> ?S"
    proof
      fix m assume "m \<in> ?S'"
      hence 1: "dom m = A" by force
      hence 2: "ran m \<subseteq> B" using \<open>m \<in> ?S'\<close> by (auto simp: dom_def ran_def)
      from 1 2 show "m \<in> ?S" by blast
    qed
  qed
  with assms show ?thesis by(simp add: finite_set_of_finite_funs)
qed


subsection \<open>@{term [source] ran}\<close>

lemma ranI: "m a = Some b \<Longrightarrow> b \<in> ran m"
  by (auto simp: ran_def)
(* declare ranI [intro]? *)

lemma ran_empty [simp]: "ran empty = {}"
  by (auto simp: ran_def)

lemma ran_map_upd [simp]:  "m a = None \<Longrightarrow> ran(m(a\<mapsto>b)) = insert b (ran m)"
  unfolding ran_def
  by force

lemma fun_upd_None_if_notin_dom[simp]: "k \<notin> dom m \<Longrightarrow> m(k := None) = m"
  by auto

lemma ran_map_add:
  assumes "dom m1 \<inter> dom m2 = {}"
  shows "ran (m1 ++ m2) = ran m1 \<union> ran m2"
proof
  show "ran (m1 ++ m2) \<subseteq> ran m1 \<union> ran m2"
    unfolding ran_def by auto
next
  show "ran m1 \<union> ran m2 \<subseteq> ran (m1 ++ m2)"
  proof -
    have "(m1 ++ m2) x = Some y" if "m1 x = Some y" for x y
      using assms map_add_comm that by fastforce
    moreover have "(m1 ++ m2) x = Some y" if "m2 x = Some y" for x y
      using assms that by auto
    ultimately show ?thesis
      unfolding ran_def by blast
  qed
qed

lemma finite_ran:
  assumes "finite (dom p)"
  shows "finite (ran p)"
proof -
  have "ran p = (\<lambda>x. the (p x)) ` dom p"
    unfolding ran_def by force
  from this \<open>finite (dom p)\<close> show ?thesis by auto
qed

lemma ran_distinct:
  assumes dist: "distinct (map fst al)"
  shows "ran (map_of al) = snd ` set al"
  using assms
proof (induct al)
  case Nil
  then show ?case by simp
next
  case (Cons kv al)
  then have "ran (map_of al) = snd ` set al" by simp
  moreover from Cons.prems have "map_of al (fst kv) = None"
    by (simp add: map_of_eq_None_iff)
  ultimately show ?case by (simp only: map_of.simps ran_map_upd) simp
qed

lemma ran_map_of_zip:
  assumes "length xs = length ys" "distinct xs"
  shows "ran (map_of (zip xs ys)) = set ys"
using assms by (simp add: ran_distinct set_map[symmetric])

lemma ran_map_option: "ran (\<lambda>x. map_option f (m x)) = f ` ran m"
  by (auto simp add: ran_def)

subsection \<open>@{term [source] graph}\<close>

lemma graph_empty[simp]: "graph empty = {}"
  unfolding graph_def by simp

lemma in_graphI: "m k = Some v \<Longrightarrow> (k, v) \<in> graph m"
  unfolding graph_def by blast

lemma in_graphD: "(k, v) \<in> graph m \<Longrightarrow> m k = Some v"
  unfolding graph_def by blast

lemma graph_map_upd[simp]: "graph (m(k \<mapsto> v)) = insert (k, v) (graph (m(k := None)))"
  unfolding graph_def by (auto split: if_splits)

lemma graph_fun_upd_None: "graph (m(k := None)) = {e \<in> graph m. fst e \<noteq> k}"
  unfolding graph_def by (auto split: if_splits)

lemma graph_restrictD:
  assumes "(k, v) \<in> graph (m |` A)"
  shows "k \<in> A" and "m k = Some v"
  using assms unfolding graph_def
  by (auto simp: restrict_map_def split: if_splits)

lemma graph_map_comp[simp]: "graph (m1 \<circ>\<^sub>m m2) = graph m2 O graph m1"
  unfolding graph_def by (auto simp: map_comp_Some_iff relcomp_unfold)

lemma graph_map_add: "dom m1 \<inter> dom m2 = {} \<Longrightarrow> graph (m1 ++ m2) = graph m1 \<union> graph m2"
  unfolding graph_def using map_add_comm by force

lemma graph_eq_to_snd_dom: "graph m = (\<lambda>x. (x, the (m x))) ` dom m"
  unfolding graph_def dom_def by force

lemma fst_graph_eq_dom: "fst ` graph m = dom m"
  unfolding graph_eq_to_snd_dom by force

lemma graph_domD: "x \<in> graph m \<Longrightarrow> fst x \<in> dom m"
  using fst_graph_eq_dom by (metis imageI)

lemma snd_graph_ran: "snd ` graph m = ran m"
  unfolding graph_def ran_def by force

lemma graph_ranD: "x \<in> graph m \<Longrightarrow> snd x \<in> ran m"
  using snd_graph_ran by (metis imageI)

lemma finite_graph_map_of: "finite (graph (map_of al))"
  unfolding graph_eq_to_snd_dom finite_dom_map_of
  using finite_dom_map_of by blast

lemma graph_map_of_if_distinct_ran: "distinct (map fst al) \<Longrightarrow> graph (map_of al) = set al"
  unfolding graph_def by auto

lemma finite_graph_iff_finite_dom[simp]: "finite (graph m) = finite (dom m)"
  by (metis graph_eq_to_snd_dom finite_imageI fst_graph_eq_dom)

lemma inj_on_fst_graph: "inj_on fst (graph m)"
  unfolding graph_def inj_on_def by force

subsection \<open>\<open>map_le\<close>\<close>

lemma map_le_empty [simp]: "empty \<subseteq>\<^sub>m g"
  by (simp add: map_le_def)

lemma upd_None_map_le [simp]: "f(x := None) \<subseteq>\<^sub>m f"
  by (force simp add: map_le_def)

lemma map_le_upd[simp]: "f \<subseteq>\<^sub>m g ==> f(a := b) \<subseteq>\<^sub>m g(a := b)"
  by (fastforce simp add: map_le_def)

lemma map_le_imp_upd_le [simp]: "m1 \<subseteq>\<^sub>m m2 \<Longrightarrow> m1(x := None) \<subseteq>\<^sub>m m2(x \<mapsto> y)"
  by (force simp add: map_le_def)

lemma map_le_upds [simp]:
  "f \<subseteq>\<^sub>m g \<Longrightarrow> f(as [\<mapsto>] bs) \<subseteq>\<^sub>m g(as [\<mapsto>] bs)"
proof (induct as arbitrary: f g bs)
  case (Cons a as)
  then show ?case
    by (cases bs) (use Cons in auto)
qed auto

lemma map_le_implies_dom_le: "(f \<subseteq>\<^sub>m g) \<Longrightarrow> (dom f \<subseteq> dom g)"
  by (fastforce simp add: map_le_def dom_def)

lemma map_le_refl [simp]: "f \<subseteq>\<^sub>m f"
  by (simp add: map_le_def)

lemma map_le_trans[trans]: "\<lbrakk> m1 \<subseteq>\<^sub>m m2; m2 \<subseteq>\<^sub>m m3\<rbrakk> \<Longrightarrow> m1 \<subseteq>\<^sub>m m3"
  by (auto simp add: map_le_def dom_def)

lemma map_le_antisym: "\<lbrakk> f \<subseteq>\<^sub>m g; g \<subseteq>\<^sub>m f \<rbrakk> \<Longrightarrow> f = g"
  unfolding map_le_def
  by (metis ext domIff)

lemma map_le_map_add [simp]: "f \<subseteq>\<^sub>m g ++ f"
  by (fastforce simp: map_le_def)

lemma map_le_iff_map_add_commute: "f \<subseteq>\<^sub>m f ++ g \<longleftrightarrow> f ++ g = g ++ f"
  by (fastforce simp: map_add_def map_le_def fun_eq_iff split: option.splits)

lemma map_add_le_mapE: "f ++ g \<subseteq>\<^sub>m h \<Longrightarrow> g \<subseteq>\<^sub>m h"
  by (fastforce simp: map_le_def map_add_def dom_def)

lemma map_add_le_mapI: "\<lbrakk> f \<subseteq>\<^sub>m h; g \<subseteq>\<^sub>m h \<rbrakk> \<Longrightarrow> f ++ g \<subseteq>\<^sub>m h"
  by (auto simp: map_le_def map_add_def dom_def split: option.splits)

lemma map_add_subsumed1: "f \<subseteq>\<^sub>m g \<Longrightarrow> f++g = g"
by (simp add: map_add_le_mapI map_le_antisym)

lemma map_add_subsumed2: "f \<subseteq>\<^sub>m g \<Longrightarrow> g++f = g"
by (metis map_add_subsumed1 map_le_iff_map_add_commute)

lemma dom_eq_singleton_conv: "dom f = {x} \<longleftrightarrow> (\<exists>v. f = [x \<mapsto> v])"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  then show ?lhs by (auto split: if_split_asm)
next
  assume ?lhs
  then obtain v where v: "f x = Some v" by auto
  show ?rhs
  proof
    show "f = [x \<mapsto> v]"
    proof (rule map_le_antisym)
      show "[x \<mapsto> v] \<subseteq>\<^sub>m f"
        using v by (auto simp add: map_le_def)
      show "f \<subseteq>\<^sub>m [x \<mapsto> v]"
        using \<open>dom f = {x}\<close> \<open>f x = Some v\<close> by (auto simp add: map_le_def)
    qed
  qed
qed

lemma map_add_eq_empty_iff[simp]:
  "(f++g = empty) \<longleftrightarrow> f = empty \<and> g = empty"
by (metis map_add_None)

lemma empty_eq_map_add_iff[simp]:
  "(empty = f++g) \<longleftrightarrow> f = empty \<and> g = empty"
by(subst map_add_eq_empty_iff[symmetric])(rule eq_commute)


subsection \<open>Various\<close>

lemma set_map_of_compr:
  assumes distinct: "distinct (map fst xs)"
  shows "set xs = {(k, v). map_of xs k = Some v}"
  using assms
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain k v where "x = (k, v)" by (cases x) blast
  with Cons.prems have "k \<notin> dom (map_of xs)"
    by (simp add: dom_map_of_conv_image_fst)
  then have *: "insert (k, v) {(k, v). map_of xs k = Some v} =
    {(k', v'). (map_of xs(k \<mapsto> v)) k' = Some v'}"
    by (auto split: if_splits)
  from Cons have "set xs = {(k, v). map_of xs k = Some v}" by simp
  with * \<open>x = (k, v)\<close> show ?case by simp
qed

lemma eq_key_imp_eq_value:
  "v1 = v2"
  if "distinct (map fst xs)" "(k, v1) \<in> set xs" "(k, v2) \<in> set xs"
proof -
  from that have "inj_on fst (set xs)"
    by (simp add: distinct_map)
  moreover have "fst (k, v1) = fst (k, v2)"
    by simp
  ultimately have "(k, v1) = (k, v2)"
    by (rule inj_onD) (fact that)+
  then show ?thesis
    by simp
qed

lemma map_of_inject_set:
  assumes distinct: "distinct (map fst xs)" "distinct (map fst ys)"
  shows "map_of xs = map_of ys \<longleftrightarrow> set xs = set ys" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  moreover from \<open>distinct (map fst xs)\<close> have "set xs = {(k, v). map_of xs k = Some v}"
    by (rule set_map_of_compr)
  moreover from \<open>distinct (map fst ys)\<close> have "set ys = {(k, v). map_of ys k = Some v}"
    by (rule set_map_of_compr)
  ultimately show ?rhs by simp
next
  assume ?rhs show ?lhs
  proof
    fix k
    show "map_of xs k = map_of ys k"
    proof (cases "map_of xs k")
      case None
      with \<open>?rhs\<close> have "map_of ys k = None"
        by (simp add: map_of_eq_None_iff)
      with None show ?thesis by simp
    next
      case (Some v)
      with distinct \<open>?rhs\<close> have "map_of ys k = Some v"
        by simp
      with Some show ?thesis by simp
    qed
  qed
qed

lemma finite_Map_induct[consumes 1, case_names empty update]:
  assumes "finite (dom m)"
  assumes "P Map.empty"
  assumes "\<And>k v m. finite (dom m) \<Longrightarrow> k \<notin> dom m \<Longrightarrow> P m \<Longrightarrow> P (m(k \<mapsto> v))"
  shows "P m"
  using assms(1)
proof(induction "dom m" arbitrary: m rule: finite_induct)
  case empty
  then show ?case using assms(2) unfolding dom_def by simp
next
  case (insert x F) 
  then have "finite (dom (m(x:=None)))" "x \<notin> dom (m(x:=None))" "P (m(x:=None))"
    by (metis Diff_insert_absorb dom_fun_upd)+
  with assms(3)[OF this] show ?case
    by (metis fun_upd_triv fun_upd_upd option.exhaust)
qed

hide_const (open) Map.empty Map.graph

end
