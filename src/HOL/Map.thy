(*  Title:      HOL/Map.thy
    ID:         $Id$
    Author:     Tobias Nipkow, based on a theory by David von Oheimb
    Copyright   1997-2003 TU Muenchen

The datatype of `maps' (written ~=>); strongly resembles maps in VDM.
*)

header {* Maps *}

theory Map = List:

types ('a,'b) "~=>" = "'a => 'b option" (infixr 0)

consts
chg_map	:: "('b => 'b) => 'a => ('a ~=> 'b) => ('a ~=> 'b)"
override:: "('a ~=> 'b) => ('a ~=> 'b) => ('a ~=> 'b)" (infixl "++" 100)
dom	:: "('a ~=> 'b) => 'a set"
ran	:: "('a ~=> 'b) => 'b set"
map_of	:: "('a * 'b)list => 'a ~=> 'b"
map_upds:: "('a ~=> 'b) => 'a list => 'b list => 
	    ('a ~=> 'b)"		 ("_/'(_[|->]_/')" [900,0,0]900)
map_le  :: "('a ~=> 'b) => ('a ~=> 'b) => bool" (infix "\<subseteq>\<^sub>m" 50)

syntax
empty	::  "'a ~=> 'b"
map_upd	:: "('a ~=> 'b) => 'a => 'b => ('a ~=> 'b)"
					 ("_/'(_/|->_')"   [900,0,0]900)

syntax (xsymbols)
  "~=>"     :: "[type, type] => type"    (infixr "\<leadsto>" 0)
  map_upd   :: "('a ~=> 'b) => 'a      => 'b      => ('a ~=> 'b)"
					  ("_/'(_/\<mapsto>/_')"  [900,0,0]900)
  map_upds  :: "('a ~=> 'b) => 'a list => 'b list => ('a ~=> 'b)"
				         ("_/'(_/[\<mapsto>]/_')" [900,0,0]900)

translations
  "empty"    => "_K None"
  "empty"    <= "%x. None"

  "m(a|->b)" == "m(a:=Some b)"

defs
chg_map_def:  "chg_map f a m == case m a of None => m | Some b => m(a|->f b)"

override_def: "m1++m2 == %x. case m2 x of None => m1 x | Some y => Some y"

dom_def: "dom(m) == {a. m a ~= None}"
ran_def: "ran(m) == {b. ? a. m a = Some b}"

map_le_def: "m1 \<subseteq>\<^sub>m m2  ==  ALL a : dom m1. m1 a = m2 a"

primrec
  "map_of [] = empty"
  "map_of (p#ps) = (map_of ps)(fst p |-> snd p)"

primrec "t([]  [|->]bs) = t"
        "t(a#as[|->]bs) = t(a|->hd bs)(as[|->]tl bs)"


section {* empty *}

lemma empty_upd_none[simp]: "empty(x := None) = empty"
apply (rule ext)
apply (simp (no_asm))
done


(* FIXME: what is this sum_case nonsense?? *)
lemma sum_case_empty_empty[simp]: "sum_case empty empty = empty"
apply (rule ext)
apply (simp (no_asm) split add: sum.split)
done

section {* map\_upd *}

lemma map_upd_triv: "t k = Some x ==> t(k|->x) = t"
apply (rule ext)
apply (simp (no_asm_simp))
done

lemma map_upd_nonempty[simp]: "t(k|->x) ~= empty"
apply safe
apply (drule_tac x = "k" in fun_cong)
apply (simp (no_asm_use))
done

lemma finite_range_updI: "finite (range f) ==> finite (range (f(a|->b)))"
apply (unfold image_def)
apply (simp (no_asm_use) add: full_SetCompr_eq)
apply (rule finite_subset)
prefer 2 apply (assumption)
apply auto
done


(* FIXME: what is this sum_case nonsense?? *)
section {* sum\_case and empty/map\_upd *}

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


section {* map\_upds *}

lemma map_upd_upds_conv_if:
 "!!x y ys f. (f(x|->y))(xs [|->] ys) =
              (if x : set xs then f(xs [|->] ys) else (f(xs [|->] ys))(x|->y))"
apply(induct xs)
 apply simp
apply(simp split:split_if add:fun_upd_twist eq_sym_conv)
done

lemma map_upds_twist [simp]:
 "a ~: set as ==> m(a|->b)(as[|->]bs) = m(as[|->]bs)(a|->b)"
by (simp add: map_upd_upds_conv_if)

lemma map_upds_apply_nontin[simp]:
 "!!ys. x ~: set xs ==> (f(xs[|->]ys)) x = f x"
apply(induct xs)
 apply simp
apply(simp add: fun_upd_apply map_upd_upds_conv_if split:split_if)
done

section {* chg\_map *}

lemma chg_map_new[simp]: "m a = None   ==> chg_map f a m = m"
apply (unfold chg_map_def)
apply auto
done

lemma chg_map_upd[simp]: "m a = Some b ==> chg_map f a m = m(a|->f b)"
apply (unfold chg_map_def)
apply auto
done


section {* map\_of *}

lemma map_of_SomeD [rule_format (no_asm)]: "map_of xs k = Some y --> (k,y):set xs"
apply (induct_tac "xs")
apply  auto
done

lemma map_of_mapk_SomeI [rule_format (no_asm)]: "inj f ==> map_of t k = Some x -->  
   map_of (map (split (%k. Pair (f k))) t) (f k) = Some x"
apply (induct_tac "t")
apply  (auto simp add: inj_eq)
done

lemma weak_map_of_SomeI [rule_format (no_asm)]: "(k, x) : set l --> (? x. map_of l k = Some x)"
apply (induct_tac "l")
apply  auto
done

lemma map_of_filter_in: 
"[| map_of xs k = Some z; P k z |] ==> map_of (filter (split P) xs) k = Some z"
apply (rule mp)
prefer 2 apply (assumption)
apply (erule thin_rl)
apply (induct_tac "xs")
apply  auto
done

lemma finite_range_map_of: "finite (range (map_of l))"
apply (induct_tac "l")
apply  (simp_all (no_asm) add: image_constant)
apply (rule finite_subset)
prefer 2 apply (assumption)
apply auto
done

lemma map_of_map: "map_of (map (%(a,b). (a,f b)) xs) x = option_map f (map_of xs x)"
apply (induct_tac "xs")
apply auto
done


section {* option\_map related *}

lemma option_map_o_empty[simp]: "option_map f o empty = empty"
apply (rule ext)
apply (simp (no_asm))
done

lemma option_map_o_map_upd[simp]:
 "option_map f o m(a|->b) = (option_map f o m)(a|->f b)"
apply (rule ext)
apply (simp (no_asm))
done


section {* ++ *}

lemma override_empty[simp]: "m ++ empty = m"
apply (unfold override_def)
apply (simp (no_asm))
done

lemma empty_override[simp]: "empty ++ m = m"
apply (unfold override_def)
apply (rule ext)
apply (simp split add: option.split)
done

lemma override_Some_iff [rule_format (no_asm)]: 
 "((m ++ n) k = Some x) = (n k = Some x | n k = None & m k = Some x)"
apply (unfold override_def)
apply (simp (no_asm) split add: option.split)
done

lemmas override_SomeD = override_Some_iff [THEN iffD1, standard]
declare override_SomeD [dest!]

lemma override_find_right[simp]: "!!xx. n k = Some xx ==> (m ++ n) k = Some xx"
apply (subst override_Some_iff)
apply fast
done

lemma override_None [iff]: "((m ++ n) k = None) = (n k = None & m k = None)"
apply (unfold override_def)
apply (simp (no_asm) split add: option.split)
done

lemma override_upd[simp]: "f ++ g(x|->y) = (f ++ g)(x|->y)"
apply (unfold override_def)
apply (rule ext)
apply auto
done

lemma map_of_override[simp]: "map_of ys ++ map_of xs = map_of (xs@ys)"
apply (unfold override_def)
apply (rule sym)
apply (induct_tac "xs")
apply (simp (no_asm))
apply (rule ext)
apply (simp (no_asm_simp) split add: option.split)
done

declare fun_upd_apply [simp del]
lemma finite_range_map_of_override: "finite (range f) ==> finite (range (f ++ map_of l))"
apply (induct_tac "l")
apply  auto
apply (erule finite_range_updI)
done
declare fun_upd_apply [simp]


section {* dom *}

lemma domI: "m a = Some b ==> a : dom m"
apply (unfold dom_def)
apply auto
done

lemma domD: "a : dom m ==> ? b. m a = Some b"
apply (unfold dom_def)
apply auto
done

lemma domIff[iff]: "(a : dom m) = (m a ~= None)"
apply (unfold dom_def)
apply auto
done
declare domIff [simp del]

lemma dom_empty[simp]: "dom empty = {}"
apply (unfold dom_def)
apply (simp (no_asm))
done

lemma dom_fun_upd[simp]:
 "dom(f(x := y)) = (if y=None then dom f - {x} else insert x (dom f))"
by (simp add:dom_def) blast
(*
lemma dom_map_upd[simp]: "dom(m(a|->b)) = insert a (dom m)"
apply (unfold dom_def)
apply (simp (no_asm))
apply blast
done
*)

lemma finite_dom_map_of: "finite (dom (map_of l))"
apply (unfold dom_def)
apply (induct_tac "l")
apply (auto simp add: insert_Collect [symmetric])
done

lemma dom_map_upds[simp]: "!!m vs. dom(m(xs[|->]vs)) = set xs Un dom m"
by(induct xs, simp_all)

lemma dom_override[simp]: "dom(m++n) = dom n Un dom m"
apply (unfold dom_def)
apply auto
done

lemma dom_overwrite[simp]:
 "dom(f(g|A)) = (dom f  - {a. a : A - dom g}) Un {a. a : A Int dom g}"
by(auto simp add: dom_def overwrite_def)

section {* ran *}

lemma ran_empty[simp]: "ran empty = {}"
apply (unfold ran_def)
apply (simp (no_asm))
done

lemma ran_map_upd[simp]: "m a = None ==> ran(m(a|->b)) = insert b (ran m)"
apply (unfold ran_def)
apply auto
apply (subgoal_tac "~ (aa = a) ")
apply auto
done

section {* map\_le *}

lemma map_le_empty [simp]: "empty \<subseteq>\<^sub>m g"
by(simp add:map_le_def)

lemma map_le_upd[simp]: "f \<subseteq>\<^sub>m g ==> f(a := b) \<subseteq>\<^sub>m g(a := b)"
by(fastsimp simp add:map_le_def)

lemma map_le_upds[simp]:
 "!!f g bs. f \<subseteq>\<^sub>m g ==> f(as [|->] bs) \<subseteq>\<^sub>m g(as [|->] bs)"
by(induct as, auto)

end
