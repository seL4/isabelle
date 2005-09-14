(*  Title:      HOL/Map.thy
    ID:         $Id$
    Author:     Tobias Nipkow, based on a theory by David von Oheimb
    Copyright   1997-2003 TU Muenchen

The datatype of `maps' (written ~=>); strongly resembles maps in VDM.
*)

header {* Maps *}

theory Map
imports List
begin

types ('a,'b) "~=>" = "'a => 'b option" (infixr 0)
translations (type) "a ~=> b " <= (type) "a => b option"

consts
chg_map	:: "('b => 'b) => 'a => ('a ~=> 'b) => ('a ~=> 'b)"
map_add :: "('a ~=> 'b) => ('a ~=> 'b) => ('a ~=> 'b)" (infixl "++" 100)
restrict_map :: "('a ~=> 'b) => 'a set => ('a ~=> 'b)" (infixl "|`"  110)
dom	:: "('a ~=> 'b) => 'a set"
ran	:: "('a ~=> 'b) => 'b set"
map_of	:: "('a * 'b)list => 'a ~=> 'b"
map_upds:: "('a ~=> 'b) => 'a list => 'b list => 
	    ('a ~=> 'b)"
map_upd_s::"('a ~=> 'b) => 'a set => 'b => 
	    ('a ~=> 'b)"			 ("_/'(_{|->}_/')" [900,0,0]900)
map_subst::"('a ~=> 'b) => 'b => 'b => 
	    ('a ~=> 'b)"			 ("_/'(_~>_/')"    [900,0,0]900)
map_le  :: "('a ~=> 'b) => ('a ~=> 'b) => bool" (infix "\<subseteq>\<^sub>m" 50)

constdefs
  map_comp :: "('b ~=> 'c)  => ('a ~=> 'b) => ('a ~=> 'c)" (infixl "o'_m" 55)
  "f o_m g  == (\<lambda>k. case g k of None \<Rightarrow> None | Some v \<Rightarrow> f v)"

nonterminals
  maplets maplet

syntax
  empty	    ::  "'a ~=> 'b"
  "_maplet"  :: "['a, 'a] => maplet"             ("_ /|->/ _")
  "_maplets" :: "['a, 'a] => maplet"             ("_ /[|->]/ _")
  ""         :: "maplet => maplets"             ("_")
  "_Maplets" :: "[maplet, maplets] => maplets" ("_,/ _")
  "_MapUpd"  :: "['a ~=> 'b, maplets] => 'a ~=> 'b" ("_/'(_')" [900,0]900)
  "_Map"     :: "maplets => 'a ~=> 'b"            ("(1[_])")

syntax (xsymbols)
  "~=>"     :: "[type, type] => type"    (infixr "\<rightharpoonup>" 0)

  map_comp :: "('b ~=> 'c)  => ('a ~=> 'b) => ('a ~=> 'c)" (infixl "\<circ>\<^sub>m" 55)

  "_maplet"  :: "['a, 'a] => maplet"             ("_ /\<mapsto>/ _")
  "_maplets" :: "['a, 'a] => maplet"             ("_ /[\<mapsto>]/ _")

  map_upd_s  :: "('a ~=> 'b) => 'a set => 'b => ('a ~=> 'b)"
				    		 ("_/'(_/{\<mapsto>}/_')" [900,0,0]900)
  map_subst :: "('a ~=> 'b) => 'b => 'b => 
	        ('a ~=> 'b)"			 ("_/'(_\<leadsto>_/')"    [900,0,0]900)
 "@chg_map" :: "('a ~=> 'b) => 'a => ('b => 'b) => ('a ~=> 'b)"
					  ("_/'(_/\<mapsto>\<lambda>_. _')"  [900,0,0,0] 900)

syntax (latex output)
  restrict_map :: "('a ~=> 'b) => 'a set => ('a ~=> 'b)" ("_\<restriction>\<^bsub>_\<^esub>" [111,110] 110)
  --"requires amssymb!"

translations
  "empty"    => "_K None"
  "empty"    <= "%x. None"

  "m(x\<mapsto>\<lambda>y. f)" == "chg_map (\<lambda>y. f) x m"

  "_MapUpd m (_Maplets xy ms)"  == "_MapUpd (_MapUpd m xy) ms"
  "_MapUpd m (_maplet  x y)"    == "m(x:=Some y)"
  "_MapUpd m (_maplets x y)"    == "map_upds m x y"
  "_Map ms"                     == "_MapUpd empty ms"
  "_Map (_Maplets ms1 ms2)"     <= "_MapUpd (_Map ms1) ms2"
  "_Maplets ms1 (_Maplets ms2 ms3)" <= "_Maplets (_Maplets ms1 ms2) ms3"

defs
chg_map_def:  "chg_map f a m == case m a of None => m | Some b => m(a|->f b)"

map_add_def:   "m1++m2 == %x. case m2 x of None => m1 x | Some y => Some y"
restrict_map_def: "m|`A == %x. if x : A then m x else None"

map_upds_def: "m(xs [|->] ys) == m ++ map_of (rev(zip xs ys))"
map_upd_s_def: "m(as{|->}b) == %x. if x : as then Some b else m x"
map_subst_def: "m(a~>b)     == %x. if m x = Some a then Some b else m x"

dom_def: "dom(m) == {a. m a ~= None}"
ran_def: "ran(m) == {b. EX a. m a = Some b}"

map_le_def: "m\<^isub>1 \<subseteq>\<^sub>m m\<^isub>2  ==  ALL a : dom m\<^isub>1. m\<^isub>1 a = m\<^isub>2 a"

primrec
  "map_of [] = empty"
  "map_of (p#ps) = (map_of ps)(fst p |-> snd p)"


subsection {* @{term [source] empty} *}

lemma empty_upd_none[simp]: "empty(x := None) = empty"
apply (rule ext)
apply (simp (no_asm))
done


(* FIXME: what is this sum_case nonsense?? *)
lemma sum_case_empty_empty[simp]: "sum_case empty empty = empty"
apply (rule ext)
apply (simp (no_asm) split add: sum.split)
done

subsection {* @{term [source] map_upd} *}

lemma map_upd_triv: "t k = Some x ==> t(k|->x) = t"
apply (rule ext)
apply (simp (no_asm_simp))
done

lemma map_upd_nonempty[simp]: "t(k|->x) ~= empty"
apply safe
apply (drule_tac x = k in fun_cong)
apply (simp (no_asm_use))
done

lemma map_upd_eqD1: "m(a\<mapsto>x) = n(a\<mapsto>y) \<Longrightarrow> x = y"
by (drule fun_cong [of _ _ a], auto)

lemma map_upd_Some_unfold: 
  "((m(a|->b)) x = Some y) = (x = a \<and> b = y \<or> x \<noteq> a \<and> m x = Some y)"
by auto

lemma image_map_upd[simp]: "x \<notin> A \<Longrightarrow> m(x \<mapsto> y) ` A = m ` A"
by fastsimp

lemma finite_range_updI: "finite (range f) ==> finite (range (f(a|->b)))"
apply (unfold image_def)
apply (simp (no_asm_use) add: full_SetCompr_eq)
apply (rule finite_subset)
prefer 2 apply assumption
apply auto
done


(* FIXME: what is this sum_case nonsense?? *)
subsection {* @{term [source] sum_case} and @{term [source] empty}/@{term [source] map_upd} *}

lemma sum_case_map_upd_empty[simp]:
 "sum_case (m(k|->y)) empty =  (sum_case m empty)(Inl k|->y)"
apply (rule ext)
apply (simp (no_asm) split add: sum.split)
done

lemma sum_case_empty_map_upd[simp]:
 "sum_case empty (m(k|->y)) =  (sum_case empty m)(Inr k|->y)"
apply (rule ext)
apply (simp (no_asm) split add: sum.split)
done

lemma sum_case_map_upd_map_upd[simp]:
 "sum_case (m1(k1|->y1)) (m2(k2|->y2)) = (sum_case (m1(k1|->y1)) m2)(Inr k2|->y2)"
apply (rule ext)
apply (simp (no_asm) split add: sum.split)
done


subsection {* @{term [source] chg_map} *}

lemma chg_map_new[simp]: "m a = None   ==> chg_map f a m = m"
by (unfold chg_map_def, auto)

lemma chg_map_upd[simp]: "m a = Some b ==> chg_map f a m = m(a|->f b)"
by (unfold chg_map_def, auto)

lemma chg_map_other [simp]: "a \<noteq> b \<Longrightarrow> chg_map f a m b = m b"
by (auto simp: chg_map_def split add: option.split)


subsection {* @{term [source] map_of} *}

lemma map_of_eq_None_iff:
 "(map_of xys x = None) = (x \<notin> fst ` (set xys))"
by (induct xys) simp_all

lemma map_of_is_SomeD:
 "map_of xys x = Some y \<Longrightarrow> (x,y) \<in> set xys"
apply(induct xys)
 apply simp
apply(clarsimp split:if_splits)
done

lemma map_of_eq_Some_iff[simp]:
 "distinct(map fst xys) \<Longrightarrow> (map_of xys x = Some y) = ((x,y) \<in> set xys)"
apply(induct xys)
 apply(simp)
apply(auto simp:map_of_eq_None_iff[symmetric])
done

lemma Some_eq_map_of_iff[simp]:
 "distinct(map fst xys) \<Longrightarrow> (Some y = map_of xys x) = ((x,y) \<in> set xys)"
by(auto simp del:map_of_eq_Some_iff simp add:map_of_eq_Some_iff[symmetric])

lemma [simp]: "\<lbrakk> distinct(map fst xys); (x,y) \<in> set xys \<rbrakk>
  \<Longrightarrow> map_of xys x = Some y"
apply (induct xys)
 apply simp
apply force
done

lemma map_of_zip_is_None[simp]:
  "length xs = length ys \<Longrightarrow> (map_of (zip xs ys) x = None) = (x \<notin> set xs)"
by (induct rule:list_induct2, simp_all)

lemma finite_range_map_of: "finite (range (map_of xys))"
apply (induct xys)
apply  (simp_all (no_asm) add: image_constant)
apply (rule finite_subset)
prefer 2 apply assumption
apply auto
done

lemma map_of_SomeD [rule_format]: "map_of xs k = Some y --> (k,y):set xs"
by (induct "xs", auto)

lemma map_of_mapk_SomeI [rule_format]:
     "inj f ==> map_of t k = Some x -->  
        map_of (map (split (%k. Pair (f k))) t) (f k) = Some x"
apply (induct "t")
apply  (auto simp add: inj_eq)
done

lemma weak_map_of_SomeI [rule_format]:
     "(k, x) : set l --> (\<exists>x. map_of l k = Some x)"
by (induct "l", auto)

lemma map_of_filter_in: 
"[| map_of xs k = Some z; P k z |] ==> map_of (filter (split P) xs) k = Some z"
apply (rule mp)
prefer 2 apply assumption
apply (erule thin_rl)
apply (induct "xs", auto)
done

lemma map_of_map: "map_of (map (%(a,b). (a,f b)) xs) x = option_map f (map_of xs x)"
by (induct "xs", auto)


subsection {* @{term [source] option_map} related *}

lemma option_map_o_empty[simp]: "option_map f o empty = empty"
apply (rule ext)
apply (simp (no_asm))
done

lemma option_map_o_map_upd[simp]:
 "option_map f o m(a|->b) = (option_map f o m)(a|->f b)"
apply (rule ext)
apply (simp (no_asm))
done

subsection {* @{term [source] map_comp} related *}

lemma map_comp_empty [simp]: 
  "m \<circ>\<^sub>m empty = empty"
  "empty \<circ>\<^sub>m m = empty"
  by (auto simp add: map_comp_def intro: ext split: option.splits)

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
apply (unfold map_add_def)
apply (simp (no_asm))
done

lemma empty_map_add[simp]: "empty ++ m = m"
apply (unfold map_add_def)
apply (rule ext)
apply (simp split add: option.split)
done

lemma map_add_assoc[simp]: "m1 ++ (m2 ++ m3) = (m1 ++ m2) ++ m3"
apply(rule ext)
apply(simp add: map_add_def split:option.split)
done

lemma map_add_Some_iff: 
 "((m ++ n) k = Some x) = (n k = Some x | n k = None & m k = Some x)"
apply (unfold map_add_def)
apply (simp (no_asm) split add: option.split)
done

lemmas map_add_SomeD = map_add_Some_iff [THEN iffD1, standard]
declare map_add_SomeD [dest!]

lemma map_add_find_right[simp]: "!!xx. n k = Some xx ==> (m ++ n) k = Some xx"
by (subst map_add_Some_iff, fast)

lemma map_add_None [iff]: "((m ++ n) k = None) = (n k = None & m k = None)"
apply (unfold map_add_def)
apply (simp (no_asm) split add: option.split)
done

lemma map_add_upd[simp]: "f ++ g(x|->y) = (f ++ g)(x|->y)"
apply (unfold map_add_def)
apply (rule ext, auto)
done

lemma map_add_upds[simp]: "m1 ++ (m2(xs[\<mapsto>]ys)) = (m1++m2)(xs[\<mapsto>]ys)"
by(simp add:map_upds_def)

lemma map_of_append[simp]: "map_of (xs@ys) = map_of ys ++ map_of xs"
apply (unfold map_add_def)
apply (induct "xs")
apply (simp (no_asm))
apply (rule ext)
apply (simp (no_asm_simp) split add: option.split)
done

declare fun_upd_apply [simp del]
lemma finite_range_map_of_map_add:
 "finite (range f) ==> finite (range (f ++ map_of l))"
apply (induct "l", auto)
apply (erule finite_range_updI)
done
declare fun_upd_apply [simp]

lemma inj_on_map_add_dom[iff]:
 "inj_on (m ++ m') (dom m') = inj_on m' (dom m')"
by(fastsimp simp add:map_add_def dom_def inj_on_def split:option.splits)

subsection {* @{term [source] restrict_map} *}

lemma restrict_map_to_empty[simp]: "m|`{} = empty"
by(simp add: restrict_map_def)

lemma restrict_map_empty[simp]: "empty|`D = empty"
by(simp add: restrict_map_def)

lemma restrict_in [simp]: "x \<in> A \<Longrightarrow> (m|`A) x = m x"
by (auto simp: restrict_map_def)

lemma restrict_out [simp]: "x \<notin> A \<Longrightarrow> (m|`A) x = None"
by (auto simp: restrict_map_def)

lemma ran_restrictD: "y \<in> ran (m|`A) \<Longrightarrow> \<exists>x\<in>A. m x = Some y"
by (auto simp: restrict_map_def ran_def split: split_if_asm)

lemma dom_restrict [simp]: "dom (m|`A) = dom m \<inter> A"
by (auto simp: restrict_map_def dom_def split: split_if_asm)

lemma restrict_upd_same [simp]: "m(x\<mapsto>y)|`(-{x}) = m|`(-{x})"
by (rule ext, auto simp: restrict_map_def)

lemma restrict_restrict [simp]: "m|`A|`B = m|`(A\<inter>B)"
by (rule ext, auto simp: restrict_map_def)

lemma restrict_fun_upd[simp]:
 "m(x := y)|`D = (if x \<in> D then (m|`(D-{x}))(x := y) else m|`D)"
by(simp add: restrict_map_def expand_fun_eq)

lemma fun_upd_None_restrict[simp]:
  "(m|`D)(x := None) = (if x:D then m|`(D - {x}) else m|`D)"
by(simp add: restrict_map_def expand_fun_eq)

lemma fun_upd_restrict:
 "(m|`D)(x := y) = (m|`(D-{x}))(x := y)"
by(simp add: restrict_map_def expand_fun_eq)

lemma fun_upd_restrict_conv[simp]:
 "x \<in> D \<Longrightarrow> (m|`D)(x := y) = (m|`(D-{x}))(x := y)"
by(simp add: restrict_map_def expand_fun_eq)


subsection {* @{term [source] map_upds} *}

lemma map_upds_Nil1[simp]: "m([] [|->] bs) = m"
by(simp add:map_upds_def)

lemma map_upds_Nil2[simp]: "m(as [|->] []) = m"
by(simp add:map_upds_def)

lemma map_upds_Cons[simp]: "m(a#as [|->] b#bs) = (m(a|->b))(as[|->]bs)"
by(simp add:map_upds_def)

lemma map_upds_append1[simp]: "\<And>ys m. size xs < size ys \<Longrightarrow>
  m(xs@[x] [\<mapsto>] ys) = m(xs [\<mapsto>] ys)(x \<mapsto> ys!size xs)"
apply(induct xs)
 apply(clarsimp simp add:neq_Nil_conv)
apply (case_tac ys, simp, simp)
done

lemma map_upds_list_update2_drop[simp]:
 "\<And>m ys i. \<lbrakk>size xs \<le> i; i < size ys\<rbrakk>
     \<Longrightarrow> m(xs[\<mapsto>]ys[i:=y]) = m(xs[\<mapsto>]ys)"
apply (induct xs, simp)
apply (case_tac ys, simp)
apply(simp split:nat.split)
done

lemma map_upd_upds_conv_if: "!!x y ys f.
 (f(x|->y))(xs [|->] ys) =
 (if x : set(take (length ys) xs) then f(xs [|->] ys)
                                  else (f(xs [|->] ys))(x|->y))"
apply (induct xs, simp)
apply(case_tac ys)
 apply(auto split:split_if simp:fun_upd_twist)
done

lemma map_upds_twist [simp]:
 "a ~: set as ==> m(a|->b)(as[|->]bs) = m(as[|->]bs)(a|->b)"
apply(insert set_take_subset)
apply (fastsimp simp add: map_upd_upds_conv_if)
done

lemma map_upds_apply_nontin[simp]:
 "!!ys. x ~: set xs ==> (f(xs[|->]ys)) x = f x"
apply (induct xs, simp)
apply(case_tac ys)
 apply(auto simp: map_upd_upds_conv_if)
done

lemma fun_upds_append_drop[simp]:
  "!!m ys. size xs = size ys \<Longrightarrow> m(xs@zs[\<mapsto>]ys) = m(xs[\<mapsto>]ys)"
apply(induct xs)
 apply (simp)
apply(case_tac ys)
apply simp_all
done

lemma fun_upds_append2_drop[simp]:
  "!!m ys. size xs = size ys \<Longrightarrow> m(xs[\<mapsto>]ys@zs) = m(xs[\<mapsto>]ys)"
apply(induct xs)
 apply (simp)
apply(case_tac ys)
apply simp_all
done


lemma restrict_map_upds[simp]: "!!m ys.
 \<lbrakk> length xs = length ys; set xs \<subseteq> D \<rbrakk>
 \<Longrightarrow> m(xs [\<mapsto>] ys)|`D = (m|`(D - set xs))(xs [\<mapsto>] ys)"
apply (induct xs, simp)
apply (case_tac ys, simp)
apply(simp add:Diff_insert[symmetric] insert_absorb)
apply(simp add: map_upd_upds_conv_if)
done


subsection {* @{term [source] map_upd_s} *}

lemma map_upd_s_apply [simp]: 
  "(m(as{|->}b)) x = (if x : as then Some b else m x)"
by (simp add: map_upd_s_def)

lemma map_subst_apply [simp]: 
  "(m(a~>b)) x = (if m x = Some a then Some b else m x)" 
by (simp add: map_subst_def)

subsection {* @{term [source] dom} *}

lemma domI: "m a = Some b ==> a : dom m"
by (unfold dom_def, auto)
(* declare domI [intro]? *)

lemma domD: "a : dom m ==> \<exists>b. m a = Some b"
by (unfold dom_def, auto)

lemma domIff[iff]: "(a : dom m) = (m a ~= None)"
by (unfold dom_def, auto)
declare domIff [simp del]

lemma dom_empty[simp]: "dom empty = {}"
apply (unfold dom_def)
apply (simp (no_asm))
done

lemma dom_fun_upd[simp]:
 "dom(f(x := y)) = (if y=None then dom f - {x} else insert x (dom f))"
by (simp add:dom_def) blast

lemma dom_map_of: "dom(map_of xys) = {x. \<exists>y. (x,y) : set xys}"
apply(induct xys)
apply(auto simp del:fun_upd_apply)
done

lemma dom_map_of_conv_image_fst:
  "dom(map_of xys) = fst ` (set xys)"
by(force simp: dom_map_of)

lemma dom_map_of_zip[simp]: "[| length xs = length ys; distinct xs |] ==>
  dom(map_of(zip xs ys)) = set xs"
by(induct rule: list_induct2, simp_all)

lemma finite_dom_map_of: "finite (dom (map_of l))"
apply (unfold dom_def)
apply (induct "l")
apply (auto simp add: insert_Collect [symmetric])
done

lemma dom_map_upds[simp]:
 "!!m ys. dom(m(xs[|->]ys)) = set(take (length ys) xs) Un dom m"
apply (induct xs, simp)
apply (case_tac ys, auto)
done

lemma dom_map_add[simp]: "dom(m++n) = dom n Un dom m"
by (unfold dom_def, auto)

lemma dom_override_on[simp]:
 "dom(override_on f g A) =
 (dom f  - {a. a : A - dom g}) Un {a. a : A Int dom g}"
by(auto simp add: dom_def override_on_def)

lemma map_add_comm: "dom m1 \<inter> dom m2 = {} \<Longrightarrow> m1++m2 = m2++m1"
apply(rule ext)
apply(fastsimp simp:map_add_def split:option.split)
done

subsection {* @{term [source] ran} *}

lemma ranI: "m a = Some b ==> b : ran m" 
by (auto simp add: ran_def)
(* declare ranI [intro]? *)

lemma ran_empty[simp]: "ran empty = {}"
apply (unfold ran_def)
apply (simp (no_asm))
done

lemma ran_map_upd[simp]: "m a = None ==> ran(m(a|->b)) = insert b (ran m)"
apply (unfold ran_def, auto)
apply (subgoal_tac "~ (aa = a) ")
apply auto
done

subsection {* @{text "map_le"} *}

lemma map_le_empty [simp]: "empty \<subseteq>\<^sub>m g"
by(simp add:map_le_def)

lemma [simp]: "f(x := None) \<subseteq>\<^sub>m f"
by(force simp add:map_le_def)

lemma map_le_upd[simp]: "f \<subseteq>\<^sub>m g ==> f(a := b) \<subseteq>\<^sub>m g(a := b)"
by(fastsimp simp add:map_le_def)

lemma [simp]: "m1 \<subseteq>\<^sub>m m2 \<Longrightarrow> m1(x := None) \<subseteq>\<^sub>m m2(x \<mapsto> y)"
by(force simp add:map_le_def)

lemma map_le_upds[simp]:
 "!!f g bs. f \<subseteq>\<^sub>m g ==> f(as [|->] bs) \<subseteq>\<^sub>m g(as [|->] bs)"
apply (induct as, simp)
apply (case_tac bs, auto)
done

lemma map_le_implies_dom_le: "(f \<subseteq>\<^sub>m g) \<Longrightarrow> (dom f \<subseteq> dom g)"
  by (fastsimp simp add: map_le_def dom_def)

lemma map_le_refl [simp]: "f \<subseteq>\<^sub>m f"
  by (simp add: map_le_def)

lemma map_le_trans[trans]: "\<lbrakk> m1 \<subseteq>\<^sub>m m2; m2 \<subseteq>\<^sub>m m3\<rbrakk> \<Longrightarrow> m1 \<subseteq>\<^sub>m m3"
by(force simp add:map_le_def)

lemma map_le_antisym: "\<lbrakk> f \<subseteq>\<^sub>m g; g \<subseteq>\<^sub>m f \<rbrakk> \<Longrightarrow> f = g"
  apply (unfold map_le_def)
  apply (rule ext)
  apply (case_tac "x \<in> dom f", simp)
  apply (case_tac "x \<in> dom g", simp, fastsimp)
done

lemma map_le_map_add [simp]: "f \<subseteq>\<^sub>m (g ++ f)"
  by (fastsimp simp add: map_le_def)

lemma map_le_iff_map_add_commute: "(f \<subseteq>\<^sub>m f ++ g) = (f++g = g++f)"
by(fastsimp simp add:map_add_def map_le_def expand_fun_eq split:option.splits)

lemma map_add_le_mapE: "f++g \<subseteq>\<^sub>m h \<Longrightarrow> g \<subseteq>\<^sub>m h"
by (fastsimp simp add: map_le_def map_add_def dom_def)

lemma map_add_le_mapI: "\<lbrakk> f \<subseteq>\<^sub>m h; g \<subseteq>\<^sub>m h; f \<subseteq>\<^sub>m f++g \<rbrakk> \<Longrightarrow> f++g \<subseteq>\<^sub>m h"
by (clarsimp simp add: map_le_def map_add_def dom_def split:option.splits)

end
