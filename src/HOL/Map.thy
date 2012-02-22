(*  Title:      HOL/Map.thy
    Author:     Tobias Nipkow, based on a theory by David von Oheimb
    Copyright   1997-2003 TU Muenchen

The datatype of `maps' (written ~=>); strongly resembles maps in VDM.
*)

header {* Maps *}

theory Map
imports List
begin

type_synonym ('a,'b) "map" = "'a => 'b option" (infixr "~=>" 0)

type_notation (xsymbols)
  "map" (infixr "\<rightharpoonup>" 0)

abbreviation
  empty :: "'a ~=> 'b" where
  "empty == %x. None"

definition
  map_comp :: "('b ~=> 'c) => ('a ~=> 'b) => ('a ~=> 'c)"  (infixl "o'_m" 55) where
  "f o_m g = (\<lambda>k. case g k of None \<Rightarrow> None | Some v \<Rightarrow> f v)"

notation (xsymbols)
  map_comp  (infixl "\<circ>\<^sub>m" 55)

definition
  map_add :: "('a ~=> 'b) => ('a ~=> 'b) => ('a ~=> 'b)"  (infixl "++" 100) where
  "m1 ++ m2 = (\<lambda>x. case m2 x of None => m1 x | Some y => Some y)"

definition
  restrict_map :: "('a ~=> 'b) => 'a set => ('a ~=> 'b)"  (infixl "|`"  110) where
  "m|`A = (\<lambda>x. if x : A then m x else None)"

notation (latex output)
  restrict_map  ("_\<restriction>\<^bsub>_\<^esub>" [111,110] 110)

definition
  dom :: "('a ~=> 'b) => 'a set" where
  "dom m = {a. m a ~= None}"

definition
  ran :: "('a ~=> 'b) => 'b set" where
  "ran m = {b. EX a. m a = Some b}"

definition
  map_le :: "('a ~=> 'b) => ('a ~=> 'b) => bool"  (infix "\<subseteq>\<^sub>m" 50) where
  "(m\<^isub>1 \<subseteq>\<^sub>m m\<^isub>2) = (\<forall>a \<in> dom m\<^isub>1. m\<^isub>1 a = m\<^isub>2 a)"

nonterminal maplets and maplet

syntax
  "_maplet"  :: "['a, 'a] => maplet"             ("_ /|->/ _")
  "_maplets" :: "['a, 'a] => maplet"             ("_ /[|->]/ _")
  ""         :: "maplet => maplets"             ("_")
  "_Maplets" :: "[maplet, maplets] => maplets" ("_,/ _")
  "_MapUpd"  :: "['a ~=> 'b, maplets] => 'a ~=> 'b" ("_/'(_')" [900,0]900)
  "_Map"     :: "maplets => 'a ~=> 'b"            ("(1[_])")

syntax (xsymbols)
  "_maplet"  :: "['a, 'a] => maplet"             ("_ /\<mapsto>/ _")
  "_maplets" :: "['a, 'a] => maplet"             ("_ /[\<mapsto>]/ _")

translations
  "_MapUpd m (_Maplets xy ms)"  == "_MapUpd (_MapUpd m xy) ms"
  "_MapUpd m (_maplet  x y)"    == "m(x := CONST Some y)"
  "_Map ms"                     == "_MapUpd (CONST empty) ms"
  "_Map (_Maplets ms1 ms2)"     <= "_MapUpd (_Map ms1) ms2"
  "_Maplets ms1 (_Maplets ms2 ms3)" <= "_Maplets (_Maplets ms1 ms2) ms3"

primrec
  map_of :: "('a \<times> 'b) list \<Rightarrow> 'a \<rightharpoonup> 'b" where
    "map_of [] = empty"
  | "map_of (p # ps) = (map_of ps)(fst p \<mapsto> snd p)"

definition
  map_upds :: "('a \<rightharpoonup> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'a \<rightharpoonup> 'b" where
  "map_upds m xs ys = m ++ map_of (rev (zip xs ys))"

translations
  "_MapUpd m (_maplets x y)"    == "CONST map_upds m x y"

lemma map_of_Cons_code [code]: 
  "map_of [] k = None"
  "map_of ((l, v) # ps) k = (if l = k then Some v else map_of ps k)"
  by simp_all


subsection {* @{term [source] empty} *}

lemma empty_upd_none [simp]: "empty(x := None) = empty"
by (rule ext) simp


subsection {* @{term [source] map_upd} *}

lemma map_upd_triv: "t k = Some x ==> t(k|->x) = t"
by (rule ext) simp

lemma map_upd_nonempty [simp]: "t(k|->x) ~= empty"
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
  "((m(a|->b)) x = Some y) = (x = a \<and> b = y \<or> x \<noteq> a \<and> m x = Some y)"
by auto

lemma image_map_upd [simp]: "x \<notin> A \<Longrightarrow> m(x \<mapsto> y) ` A = m ` A"
by auto

lemma finite_range_updI: "finite (range f) ==> finite (range (f(a|->b)))"
unfolding image_def
apply (simp (no_asm_use) add:full_SetCompr_eq)
apply (rule finite_subset)
 prefer 2 apply assumption
apply (auto)
done


subsection {* @{term [source] map_of} *}

lemma map_of_eq_None_iff:
  "(map_of xys x = None) = (x \<notin> fst ` (set xys))"
by (induct xys) simp_all

lemma map_of_is_SomeD: "map_of xys x = Some y \<Longrightarrow> (x,y) \<in> set xys"
apply (induct xys)
 apply simp
apply (clarsimp split: if_splits)
done

lemma map_of_eq_Some_iff [simp]:
  "distinct(map fst xys) \<Longrightarrow> (map_of xys x = Some y) = ((x,y) \<in> set xys)"
apply (induct xys)
 apply simp
apply (auto simp: map_of_eq_None_iff [symmetric])
done

lemma Some_eq_map_of_iff [simp]:
  "distinct(map fst xys) \<Longrightarrow> (Some y = map_of xys x) = ((x,y) \<in> set xys)"
by (auto simp del:map_of_eq_Some_iff simp add: map_of_eq_Some_iff [symmetric])

lemma map_of_is_SomeI [simp]: "\<lbrakk> distinct(map fst xys); (x,y) \<in> set xys \<rbrakk>
    \<Longrightarrow> map_of xys x = Some y"
apply (induct xys)
 apply simp
apply force
done

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
using assms(1) assms(2)[symmetric] using dist map_of proof (induct ys xs zs rule: list_induct3)
  case Nil show ?case by simp
next
  case (Cons y ys x xs z zs)
  from `map_of (zip (x#xs) (y#ys)) = map_of (zip (x#xs) (z#zs))`
    have map_of: "map_of (zip xs ys)(x \<mapsto> y) = map_of (zip xs zs)(x \<mapsto> z)" by simp
  from Cons have "length ys = length xs" and "length zs = length xs"
    and "x \<notin> set xs" by simp_all
  then have "map_of (zip xs ys) = map_of (zip xs zs)" using map_of by (rule map_of_zip_upd)
  with Cons.hyps `distinct (x # xs)` have "ys = zs" by simp
  moreover from map_of have "y = z" by (rule map_upd_eqD1)
  ultimately show ?case by simp
qed

lemma map_of_zip_map:
  "map_of (zip xs (map f xs)) = (\<lambda>x. if x \<in> set xs then Some (f x) else None)"
  by (induct xs) (simp_all add: fun_eq_iff)

lemma finite_range_map_of: "finite (range (map_of xys))"
apply (induct xys)
 apply (simp_all add: image_constant)
apply (rule finite_subset)
 prefer 2 apply assumption
apply auto
done

lemma map_of_SomeD: "map_of xs k = Some y \<Longrightarrow> (k, y) \<in> set xs"
by (induct xs) (simp, atomize (full), auto)

lemma map_of_mapk_SomeI:
  "inj f ==> map_of t k = Some x ==>
   map_of (map (split (%k. Pair (f k))) t) (f k) = Some x"
by (induct t) (auto simp add: inj_eq)

lemma weak_map_of_SomeI: "(k, x) : set l ==> \<exists>x. map_of l k = Some x"
by (induct l) auto

lemma map_of_filter_in:
  "map_of xs k = Some z \<Longrightarrow> P k z \<Longrightarrow> map_of (filter (split P) xs) k = Some z"
by (induct xs) auto

lemma map_of_map:
  "map_of (map (\<lambda>(k, v). (k, f v)) xs) = Option.map f \<circ> map_of xs"
  by (induct xs) (auto simp add: fun_eq_iff)

lemma dom_option_map:
  "dom (\<lambda>k. Option.map (f k) (m k)) = dom m"
  by (simp add: dom_def)


subsection {* @{const Option.map} related *}

lemma option_map_o_empty [simp]: "Option.map f o empty = empty"
by (rule ext) simp

lemma option_map_o_map_upd [simp]:
  "Option.map f o m(a|->b) = (Option.map f o m)(a|->f b)"
by (rule ext) simp


subsection {* @{term [source] map_comp} related *}

lemma map_comp_empty [simp]:
  "m \<circ>\<^sub>m empty = empty"
  "empty \<circ>\<^sub>m m = empty"
by (auto simp add: map_comp_def split: option.splits)

lemma map_comp_simps [simp]:
  "m2 k = None \<Longrightarrow> (m1 \<circ>\<^sub>m m2) k = None"
  "m2 k = Some k' \<Longrightarrow> (m1 \<circ>\<^sub>m m2) k = m1 k'"
by (auto simp add: map_comp_def)

lemma map_comp_Some_iff:
  "((m1 \<circ>\<^sub>m m2) k = Some v) = (\<exists>k'. m2 k = Some k' \<and> m1 k' = Some v)"
by (auto simp add: map_comp_def split: option.splits)

lemma map_comp_None_iff:
  "((m1 \<circ>\<^sub>m m2) k = None) = (m2 k = None \<or> (\<exists>k'. m2 k = Some k' \<and> m1 k' = None)) "
by (auto simp add: map_comp_def split: option.splits)


subsection {* @{text "++"} *}

lemma map_add_empty[simp]: "m ++ empty = m"
by(simp add: map_add_def)

lemma empty_map_add[simp]: "empty ++ m = m"
by (rule ext) (simp add: map_add_def split: option.split)

lemma map_add_assoc[simp]: "m1 ++ (m2 ++ m3) = (m1 ++ m2) ++ m3"
by (rule ext) (simp add: map_add_def split: option.split)

lemma map_add_Some_iff:
  "((m ++ n) k = Some x) = (n k = Some x | n k = None & m k = Some x)"
by (simp add: map_add_def split: option.split)

lemma map_add_SomeD [dest!]:
  "(m ++ n) k = Some x \<Longrightarrow> n k = Some x \<or> n k = None \<and> m k = Some x"
by (rule map_add_Some_iff [THEN iffD1])

lemma map_add_find_right [simp]: "!!xx. n k = Some xx ==> (m ++ n) k = Some xx"
by (subst map_add_Some_iff) fast

lemma map_add_None [iff]: "((m ++ n) k = None) = (n k = None & m k = None)"
by (simp add: map_add_def split: option.split)

lemma map_add_upd[simp]: "f ++ g(x|->y) = (f ++ g)(x|->y)"
by (rule ext) (simp add: map_add_def)

lemma map_add_upds[simp]: "m1 ++ (m2(xs[\<mapsto>]ys)) = (m1++m2)(xs[\<mapsto>]ys)"
by (simp add: map_upds_def)

lemma map_add_upd_left: "m\<notin>dom e2 \<Longrightarrow> e1(m \<mapsto> u1) ++ e2 = (e1 ++ e2)(m \<mapsto> u1)"
by (rule ext) (auto simp: map_add_def dom_def split: option.split)

lemma map_of_append[simp]: "map_of (xs @ ys) = map_of ys ++ map_of xs"
unfolding map_add_def
apply (induct xs)
 apply simp
apply (rule ext)
apply (simp split add: option.split)
done

lemma finite_range_map_of_map_add:
  "finite (range f) ==> finite (range (f ++ map_of l))"
apply (induct l)
 apply (auto simp del: fun_upd_apply)
apply (erule finite_range_updI)
done

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
  by (induct ps) (auto simp add: fun_eq_iff map_add_def)


subsection {* @{term [source] restrict_map} *}

lemma restrict_map_to_empty [simp]: "m|`{} = empty"
by (simp add: restrict_map_def)

lemma restrict_map_insert: "f |` (insert a A) = (f |` A)(a := f a)"
by (auto simp add: restrict_map_def)

lemma restrict_map_empty [simp]: "empty|`D = empty"
by (simp add: restrict_map_def)

lemma restrict_in [simp]: "x \<in> A \<Longrightarrow> (m|`A) x = m x"
by (simp add: restrict_map_def)

lemma restrict_out [simp]: "x \<notin> A \<Longrightarrow> (m|`A) x = None"
by (simp add: restrict_map_def)

lemma ran_restrictD: "y \<in> ran (m|`A) \<Longrightarrow> \<exists>x\<in>A. m x = Some y"
by (auto simp: restrict_map_def ran_def split: split_if_asm)

lemma dom_restrict [simp]: "dom (m|`A) = dom m \<inter> A"
by (auto simp: restrict_map_def dom_def split: split_if_asm)

lemma restrict_upd_same [simp]: "m(x\<mapsto>y)|`(-{x}) = m|`(-{x})"
by (rule ext) (auto simp: restrict_map_def)

lemma restrict_restrict [simp]: "m|`A|`B = m|`(A\<inter>B)"
by (rule ext) (auto simp: restrict_map_def)

lemma restrict_fun_upd [simp]:
  "m(x := y)|`D = (if x \<in> D then (m|`(D-{x}))(x := y) else m|`D)"
by (simp add: restrict_map_def fun_eq_iff)

lemma fun_upd_None_restrict [simp]:
  "(m|`D)(x := None) = (if x:D then m|`(D - {x}) else m|`D)"
by (simp add: restrict_map_def fun_eq_iff)

lemma fun_upd_restrict: "(m|`D)(x := y) = (m|`(D-{x}))(x := y)"
by (simp add: restrict_map_def fun_eq_iff)

lemma fun_upd_restrict_conv [simp]:
  "x \<in> D \<Longrightarrow> (m|`D)(x := y) = (m|`(D-{x}))(x := y)"
by (simp add: restrict_map_def fun_eq_iff)

lemma map_of_map_restrict:
  "map_of (map (\<lambda>k. (k, f k)) ks) = (Some \<circ> f) |` set ks"
  by (induct ks) (simp_all add: fun_eq_iff restrict_map_insert)

lemma restrict_complement_singleton_eq:
  "f |` (- {x}) = f(x := None)"
  by (simp add: restrict_map_def fun_eq_iff)


subsection {* @{term [source] map_upds} *}

lemma map_upds_Nil1 [simp]: "m([] [|->] bs) = m"
by (simp add: map_upds_def)

lemma map_upds_Nil2 [simp]: "m(as [|->] []) = m"
by (simp add:map_upds_def)

lemma map_upds_Cons [simp]: "m(a#as [|->] b#bs) = (m(a|->b))(as[|->]bs)"
by (simp add:map_upds_def)

lemma map_upds_append1 [simp]: "\<And>ys m. size xs < size ys \<Longrightarrow>
  m(xs@[x] [\<mapsto>] ys) = m(xs [\<mapsto>] ys)(x \<mapsto> ys!size xs)"
apply(induct xs)
 apply (clarsimp simp add: neq_Nil_conv)
apply (case_tac ys)
 apply simp
apply simp
done

lemma map_upds_list_update2_drop [simp]:
  "size xs \<le> i \<Longrightarrow> m(xs[\<mapsto>]ys[i:=y]) = m(xs[\<mapsto>]ys)"
apply (induct xs arbitrary: m ys i)
 apply simp
apply (case_tac ys)
 apply simp
apply (simp split: nat.split)
done

lemma map_upd_upds_conv_if:
  "(f(x|->y))(xs [|->] ys) =
   (if x : set(take (length ys) xs) then f(xs [|->] ys)
                                    else (f(xs [|->] ys))(x|->y))"
apply (induct xs arbitrary: x y ys f)
 apply simp
apply (case_tac ys)
 apply (auto split: split_if simp: fun_upd_twist)
done

lemma map_upds_twist [simp]:
  "a ~: set as ==> m(a|->b)(as[|->]bs) = m(as[|->]bs)(a|->b)"
using set_take_subset by (fastforce simp add: map_upd_upds_conv_if)

lemma map_upds_apply_nontin [simp]:
  "x ~: set xs ==> (f(xs[|->]ys)) x = f x"
apply (induct xs arbitrary: ys)
 apply simp
apply (case_tac ys)
 apply (auto simp: map_upd_upds_conv_if)
done

lemma fun_upds_append_drop [simp]:
  "size xs = size ys \<Longrightarrow> m(xs@zs[\<mapsto>]ys) = m(xs[\<mapsto>]ys)"
apply (induct xs arbitrary: m ys)
 apply simp
apply (case_tac ys)
 apply simp_all
done

lemma fun_upds_append2_drop [simp]:
  "size xs = size ys \<Longrightarrow> m(xs[\<mapsto>]ys@zs) = m(xs[\<mapsto>]ys)"
apply (induct xs arbitrary: m ys)
 apply simp
apply (case_tac ys)
 apply simp_all
done


lemma restrict_map_upds[simp]:
  "\<lbrakk> length xs = length ys; set xs \<subseteq> D \<rbrakk>
    \<Longrightarrow> m(xs [\<mapsto>] ys)|`D = (m|`(D - set xs))(xs [\<mapsto>] ys)"
apply (induct xs arbitrary: m ys)
 apply simp
apply (case_tac ys)
 apply simp
apply (simp add: Diff_insert [symmetric] insert_absorb)
apply (simp add: map_upd_upds_conv_if)
done


subsection {* @{term [source] dom} *}

lemma dom_eq_empty_conv [simp]: "dom f = {} \<longleftrightarrow> f = empty"
  by (auto simp: dom_def)

lemma domI: "m a = Some b ==> a : dom m"
by(simp add:dom_def)
(* declare domI [intro]? *)

lemma domD: "a : dom m ==> \<exists>b. m a = Some b"
by (cases "m a") (auto simp add: dom_def)

lemma domIff [iff, simp del]: "(a : dom m) = (m a ~= None)"
by(simp add:dom_def)

lemma dom_empty [simp]: "dom empty = {}"
by(simp add:dom_def)

lemma dom_fun_upd [simp]:
  "dom(f(x := y)) = (if y=None then dom f - {x} else insert x (dom f))"
by(auto simp add:dom_def)

lemma dom_if:
  "dom (\<lambda>x. if P x then f x else g x) = dom f \<inter> {x. P x} \<union> dom g \<inter> {x. \<not> P x}"
  by (auto split: if_splits)

lemma dom_map_of_conv_image_fst:
  "dom (map_of xys) = fst ` set xys"
  by (induct xys) (auto simp add: dom_if)

lemma dom_map_of_zip [simp]: "length xs = length ys ==> dom (map_of (zip xs ys)) = set xs"
by (induct rule: list_induct2) (auto simp add: dom_if)

lemma finite_dom_map_of: "finite (dom (map_of l))"
by (induct l) (auto simp add: dom_def insert_Collect [symmetric])

lemma dom_map_upds [simp]:
  "dom(m(xs[|->]ys)) = set(take (length ys) xs) Un dom m"
apply (induct xs arbitrary: m ys)
 apply simp
apply (case_tac ys)
 apply auto
done

lemma dom_map_add [simp]: "dom(m++n) = dom n Un dom m"
by(auto simp:dom_def)

lemma dom_override_on [simp]:
  "dom(override_on f g A) =
    (dom f  - {a. a : A - dom g}) Un {a. a : A Int dom g}"
by(auto simp: dom_def override_on_def)

lemma map_add_comm: "dom m1 \<inter> dom m2 = {} \<Longrightarrow> m1++m2 = m2++m1"
by (rule ext) (force simp: map_add_def dom_def split: option.split)

lemma map_add_dom_app_simps:
  "\<lbrakk> m\<in>dom l2 \<rbrakk> \<Longrightarrow> (l1++l2) m = l2 m"
  "\<lbrakk> m\<notin>dom l1 \<rbrakk> \<Longrightarrow> (l1++l2) m = l2 m"
  "\<lbrakk> m\<notin>dom l2 \<rbrakk> \<Longrightarrow> (l1++l2) m = l1 m"
by (auto simp add: map_add_def split: option.split_asm)

lemma dom_const [simp]:
  "dom (\<lambda>x. Some (f x)) = UNIV"
  by auto

(* Due to John Matthews - could be rephrased with dom *)
lemma finite_map_freshness:
  "finite (dom (f :: 'a \<rightharpoonup> 'b)) \<Longrightarrow> \<not> finite (UNIV :: 'a set) \<Longrightarrow>
   \<exists>x. f x = None"
by(bestsimp dest:ex_new_if_finite)

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
    case None then have "k \<notin> set (map fst xs)" by (simp add: map_of_eq_None_iff)
    with set_eq have "k \<notin> set (map fst ys)" by simp
    then have "map_of ys k = None" by (simp add: map_of_eq_None_iff)
    with None show ?thesis by simp
  next
    case (Some v) then have "k \<in> set (map fst xs)" by (auto simp add: dom_map_of_conv_image_fst [symmetric])
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


subsection {* @{term [source] ran} *}

lemma ranI: "m a = Some b ==> b : ran m"
by(auto simp: ran_def)
(* declare ranI [intro]? *)

lemma ran_empty [simp]: "ran empty = {}"
by(auto simp: ran_def)

lemma ran_map_upd [simp]: "m a = None ==> ran(m(a|->b)) = insert b (ran m)"
unfolding ran_def
apply auto
apply (subgoal_tac "aa ~= a")
 apply auto
done

lemma ran_distinct: 
  assumes dist: "distinct (map fst al)" 
  shows "ran (map_of al) = snd ` set al"
using assms proof (induct al)
  case Nil then show ?case by simp
next
  case (Cons kv al)
  then have "ran (map_of al) = snd ` set al" by simp
  moreover from Cons.prems have "map_of al (fst kv) = None"
    by (simp add: map_of_eq_None_iff)
  ultimately show ?case by (simp only: map_of.simps ran_map_upd) simp
qed


subsection {* @{text "map_le"} *}

lemma map_le_empty [simp]: "empty \<subseteq>\<^sub>m g"
by (simp add: map_le_def)

lemma upd_None_map_le [simp]: "f(x := None) \<subseteq>\<^sub>m f"
by (force simp add: map_le_def)

lemma map_le_upd[simp]: "f \<subseteq>\<^sub>m g ==> f(a := b) \<subseteq>\<^sub>m g(a := b)"
by (fastforce simp add: map_le_def)

lemma map_le_imp_upd_le [simp]: "m1 \<subseteq>\<^sub>m m2 \<Longrightarrow> m1(x := None) \<subseteq>\<^sub>m m2(x \<mapsto> y)"
by (force simp add: map_le_def)

lemma map_le_upds [simp]:
  "f \<subseteq>\<^sub>m g ==> f(as [|->] bs) \<subseteq>\<^sub>m g(as [|->] bs)"
apply (induct as arbitrary: f g bs)
 apply simp
apply (case_tac bs)
 apply auto
done

lemma map_le_implies_dom_le: "(f \<subseteq>\<^sub>m g) \<Longrightarrow> (dom f \<subseteq> dom g)"
by (fastforce simp add: map_le_def dom_def)

lemma map_le_refl [simp]: "f \<subseteq>\<^sub>m f"
by (simp add: map_le_def)

lemma map_le_trans[trans]: "\<lbrakk> m1 \<subseteq>\<^sub>m m2; m2 \<subseteq>\<^sub>m m3\<rbrakk> \<Longrightarrow> m1 \<subseteq>\<^sub>m m3"
by (auto simp add: map_le_def dom_def)

lemma map_le_antisym: "\<lbrakk> f \<subseteq>\<^sub>m g; g \<subseteq>\<^sub>m f \<rbrakk> \<Longrightarrow> f = g"
unfolding map_le_def
apply (rule ext)
apply (case_tac "x \<in> dom f", simp)
apply (case_tac "x \<in> dom g", simp, fastforce)
done

lemma map_le_map_add [simp]: "f \<subseteq>\<^sub>m (g ++ f)"
by (fastforce simp add: map_le_def)

lemma map_le_iff_map_add_commute: "(f \<subseteq>\<^sub>m f ++ g) = (f++g = g++f)"
by(fastforce simp: map_add_def map_le_def fun_eq_iff split: option.splits)

lemma map_add_le_mapE: "f++g \<subseteq>\<^sub>m h \<Longrightarrow> g \<subseteq>\<^sub>m h"
by (fastforce simp add: map_le_def map_add_def dom_def)

lemma map_add_le_mapI: "\<lbrakk> f \<subseteq>\<^sub>m h; g \<subseteq>\<^sub>m h \<rbrakk> \<Longrightarrow> f++g \<subseteq>\<^sub>m h"
by (clarsimp simp add: map_le_def map_add_def dom_def split: option.splits)

lemma dom_eq_singleton_conv: "dom f = {x} \<longleftrightarrow> (\<exists>v. f = [x \<mapsto> v])"
proof(rule iffI)
  assume "\<exists>v. f = [x \<mapsto> v]"
  thus "dom f = {x}" by(auto split: split_if_asm)
next
  assume "dom f = {x}"
  then obtain v where "f x = Some v" by auto
  hence "[x \<mapsto> v] \<subseteq>\<^sub>m f" by(auto simp add: map_le_def)
  moreover have "f \<subseteq>\<^sub>m [x \<mapsto> v]" using `dom f = {x}` `f x = Some v`
    by(auto simp add: map_le_def)
  ultimately have "f = [x \<mapsto> v]" by-(rule map_le_antisym)
  thus "\<exists>v. f = [x \<mapsto> v]" by blast
qed


subsection {* Various *}

lemma set_map_of_compr:
  assumes distinct: "distinct (map fst xs)"
  shows "set xs = {(k, v). map_of xs k = Some v}"
using assms proof (induct xs)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  obtain k v where "x = (k, v)" by (cases x) blast
  with Cons.prems have "k \<notin> dom (map_of xs)"
    by (simp add: dom_map_of_conv_image_fst)
  then have *: "insert (k, v) {(k, v). map_of xs k = Some v} =
    {(k', v'). (map_of xs(k \<mapsto> v)) k' = Some v'}"
    by (auto split: if_splits)
  from Cons have "set xs = {(k, v). map_of xs k = Some v}" by simp
  with * `x = (k, v)` show ?case by simp
qed

lemma map_of_inject_set:
  assumes distinct: "distinct (map fst xs)" "distinct (map fst ys)"
  shows "map_of xs = map_of ys \<longleftrightarrow> set xs = set ys" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  moreover from `distinct (map fst xs)` have "set xs = {(k, v). map_of xs k = Some v}"
    by (rule set_map_of_compr)
  moreover from `distinct (map fst ys)` have "set ys = {(k, v). map_of ys k = Some v}"
    by (rule set_map_of_compr)
  ultimately show ?rhs by simp
next
  assume ?rhs show ?lhs proof
    fix k
    show "map_of xs k = map_of ys k" proof (cases "map_of xs k")
      case None
      moreover with `?rhs` have "map_of ys k = None"
        by (simp add: map_of_eq_None_iff)
      ultimately show ?thesis by simp
    next
      case (Some v)
      moreover with distinct `?rhs` have "map_of ys k = Some v"
        by simp
      ultimately show ?thesis by simp
    qed
  qed
qed

end
