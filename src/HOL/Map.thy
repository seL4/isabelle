(*  Title:      HOL/Map.thy
    ID:         $Id$
    Author:     Tobias Nipkow, based on a theory by David von Oheimb
    Copyright   1997-2003 TU Muenchen

The datatype of `maps' (written ~=>); strongly resembles maps in VDM.
*)

theory Map = List:

types ('a,'b) "~=>" = "'a => 'b option" (infixr 0)

consts
chg_map	:: "('b => 'b) => 'a => ('a ~=> 'b) => ('a ~=> 'b)"
override:: "('a ~=> 'b) => ('a ~=> 'b) => ('a ~=> 'b)" (infixl "++" 100)
dom	:: "('a ~=> 'b) => 'a set"
ran	:: "('a ~=> 'b) => 'b set"
map_of	:: "('a * 'b)list => 'a ~=> 'b"
map_upds:: "('a ~=> 'b) => 'a list => 'b list => 
	    ('a ~=> 'b)"			 ("_/'(_[|->]_/')" [900,0,0]900)
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

primrec
  "map_of [] = empty"
  "map_of (p#ps) = (map_of ps)(fst p |-> snd p)"

primrec "t([]  [|->]bs) = t"
        "t(a#as[|->]bs) = t(a|->hd bs)(as[|->]tl bs)"


section "empty"

lemma empty_upd_none: "empty(x := None) = empty"
apply (rule ext)
apply (simp (no_asm))
done
declare empty_upd_none [simp]

(* FIXME: what is this sum_case nonsense?? *)
lemma sum_case_empty_empty: "sum_case empty empty = empty"
apply (rule ext)
apply (simp (no_asm) split add: sum.split)
done
declare sum_case_empty_empty [simp]


section "map_upd"

lemma map_upd_triv: "t k = Some x ==> t(k|->x) = t"
apply (rule ext)
apply (simp (no_asm_simp))
done

lemma map_upd_nonempty: "t(k|->x) ~= empty"
apply safe
apply (drule_tac x = "k" in fun_cong)
apply (simp (no_asm_use))
done
declare map_upd_nonempty [simp]

lemma finite_range_updI: "finite (range f) ==> finite (range (f(a|->b)))"
apply (unfold image_def)
apply (simp (no_asm_use) add: full_SetCompr_eq)
apply (rule finite_subset)
prefer 2 apply (assumption)
apply auto
done


(* FIXME: what is this sum_case nonsense?? *)
section "sum_case and empty/map_upd"

lemma sum_case_map_upd_empty: "sum_case (m(k|->y)) empty =  (sum_case m empty)(Inl k|->y)"
apply (rule ext)
apply (simp (no_asm) split add: sum.split)
done
declare sum_case_map_upd_empty [simp]

lemma sum_case_empty_map_upd: "sum_case empty (m(k|->y)) =  (sum_case empty m)(Inr k|->y)"
apply (rule ext)
apply (simp (no_asm) split add: sum.split)
done
declare sum_case_empty_map_upd [simp]

lemma sum_case_map_upd_map_upd: "sum_case (m1(k1|->y1)) (m2(k2|->y2)) = (sum_case (m1(k1|->y1)) m2)(Inr k2|->y2)"
apply (rule ext)
apply (simp (no_asm) split add: sum.split)
done
declare sum_case_map_upd_map_upd [simp]


section "map_upds"

lemma map_upds_twist [rule_format (no_asm)]: "a ~: set as --> (!m bs. (m(a|->b)(as[|->]bs)) = (m(as[|->]bs)(a|->b)))"
apply (induct_tac "as")
apply  (auto simp del: fun_upd_apply)
apply (drule spec)+
apply (rotate_tac -1)
apply (erule subst)
apply (erule fun_upd_twist [THEN subst])
apply (rule refl)
done
declare map_upds_twist [simp]


section "chg_map"

lemma chg_map_new: "m a = None   ==> chg_map f a m = m"
apply (unfold chg_map_def)
apply auto
done

lemma chg_map_upd: "m a = Some b ==> chg_map f a m = m(a|->f b)"
apply (unfold chg_map_def)
apply auto
done

declare chg_map_new [simp] chg_map_upd [simp]


section "map_of"

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


section "option_map related"

lemma option_map_o_empty: "option_map f o empty = empty"
apply (rule ext)
apply (simp (no_asm))
done

lemma option_map_o_map_upd: "option_map f o m(a|->b) = (option_map f o m)(a|->f b)"
apply (rule ext)
apply (simp (no_asm))
done

declare option_map_o_empty [simp] option_map_o_map_upd [simp]


section "++"

lemma override_empty: "m ++ empty = m"
apply (unfold override_def)
apply (simp (no_asm))
done
declare override_empty [simp]

lemma empty_override: "empty ++ m = m"
apply (unfold override_def)
apply (rule ext)
apply (simp split add: option.split)
done
declare empty_override [simp]

lemma override_Some_iff [rule_format (no_asm)]: 
 "((m ++ n) k = Some x) = (n k = Some x | n k = None & m k = Some x)"
apply (unfold override_def)
apply (simp (no_asm) split add: option.split)
done

lemmas override_SomeD = override_Some_iff [THEN iffD1, standard]
declare override_SomeD [dest!]

lemma override_find_right: "!!xx. n k = Some xx ==> (m ++ n) k = Some xx"
apply (subst override_Some_iff)
apply fast
done
declare override_find_right [simp]

lemma override_None: "((m ++ n) k = None) = (n k = None & m k = None)"
apply (unfold override_def)
apply (simp (no_asm) split add: option.split)
done
declare override_None [iff]

lemma override_upd: "f ++ g(x|->y) = (f ++ g)(x|->y)"
apply (unfold override_def)
apply (rule ext)
apply auto
done
declare override_upd [simp]

lemma map_of_override: "map_of ys ++ map_of xs = map_of (xs@ys)"
apply (unfold override_def)
apply (rule sym)
apply (induct_tac "xs")
apply (simp (no_asm))
apply (rule ext)
apply (simp (no_asm_simp) split add: option.split)
done
declare map_of_override [simp]

declare fun_upd_apply [simp del]
lemma finite_range_map_of_override: "finite (range f) ==> finite (range (f ++ map_of l))"
apply (induct_tac "l")
apply  auto
apply (erule finite_range_updI)
done
declare fun_upd_apply [simp]


section "dom"

lemma domI: "m a = Some b ==> a : dom m"
apply (unfold dom_def)
apply auto
done

lemma domD: "a : dom m ==> ? b. m a = Some b"
apply (unfold dom_def)
apply auto
done

lemma domIff: "(a : dom m) = (m a ~= None)"
apply (unfold dom_def)
apply auto
done
declare domIff [iff]
declare domIff [simp del]

lemma dom_empty: "dom empty = {}"
apply (unfold dom_def)
apply (simp (no_asm))
done
declare dom_empty [simp]

lemma dom_map_upd: "dom(m(a|->b)) = insert a (dom m)"
apply (unfold dom_def)
apply (simp (no_asm))
apply blast
done
declare dom_map_upd [simp]

lemma finite_dom_map_of: "finite (dom (map_of l))"
apply (unfold dom_def)
apply (induct_tac "l")
apply (auto simp add: insert_Collect [symmetric])
done

lemma dom_override: "dom(m++n) = dom n Un dom m"
apply (unfold dom_def)
apply auto
done
declare dom_override [simp]

section "ran"

lemma ran_empty: "ran empty = {}"
apply (unfold ran_def)
apply (simp (no_asm))
done
declare ran_empty [simp]

lemma ran_empty': "ran (%u. None) = {}"
apply (unfold ran_def)
apply auto
done
declare ran_empty' [simp]

lemma ran_map_upd: "m a = None ==> ran(m(a|->b)) = insert b (ran m)"
apply (unfold ran_def)
apply auto
apply (subgoal_tac "~ (aa = a) ")
apply auto
done
declare ran_map_upd [simp]

end
