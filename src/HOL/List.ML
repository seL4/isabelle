(*  Title:      HOL/List
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

List lemmas
*)

Goal "!x. xs ~= x#xs";
by (induct_tac "xs" 1);
by Auto_tac;
qed_spec_mp "not_Cons_self";
bind_thm("not_Cons_self2",not_Cons_self RS not_sym);
Addsimps [not_Cons_self,not_Cons_self2];

Goal "(xs ~= []) = (? y ys. xs = y#ys)";
by (induct_tac "xs" 1);
by Auto_tac;
qed "neq_Nil_conv";

(* Induction over the length of a list: *)
val [prem] = Goal
  "(!!xs. (!ys. length ys < length xs --> P ys) ==> P xs) ==> P(xs)";
by (rtac measure_induct 1 THEN etac prem 1);
qed "length_induct";


(** "lists": the list-forming operator over sets **)

Goalw lists.defs "A<=B ==> lists A <= lists B";
by (rtac lfp_mono 1);
by (REPEAT (ares_tac basic_monos 1));
qed "lists_mono";

bind_thm ("listsE", lists.mk_cases "x#l : lists A");
AddSEs [listsE];
AddSIs lists.intrs;

Goal "l: lists A ==> l: lists B --> l: lists (A Int B)";
by (etac lists.induct 1);
by (ALLGOALS Blast_tac);
qed_spec_mp "lists_IntI";

Goal "lists (A Int B) = lists A Int lists B";
by (rtac (mono_Int RS equalityI) 1);
by (simp_tac (simpset() addsimps [mono_def, lists_mono]) 1);
by (blast_tac (claset() addSIs [lists_IntI]) 1);
qed "lists_Int_eq";
Addsimps [lists_Int_eq];

Goal "(xs@ys : lists A) = (xs : lists A & ys : lists A)";
by(induct_tac "xs" 1);
by(Auto_tac);
qed "append_in_lists_conv";
AddIffs [append_in_lists_conv];

(** length **)
(* needs to come before "@" because of thm append_eq_append_conv *)

section "length";

Goal "length(xs@ys) = length(xs)+length(ys)";
by (induct_tac "xs" 1);
by Auto_tac;
qed"length_append";
Addsimps [length_append];

Goal "length (map f xs) = length xs";
by (induct_tac "xs" 1);
by Auto_tac;
qed "length_map";
Addsimps [length_map];

Goal "length(rev xs) = length(xs)";
by (induct_tac "xs" 1);
by Auto_tac;
qed "length_rev";
Addsimps [length_rev];

Goal "length(tl xs) = (length xs) - 1";
by (case_tac "xs" 1);
by Auto_tac;
qed "length_tl";
Addsimps [length_tl];

Goal "(length xs = 0) = (xs = [])";
by (induct_tac "xs" 1);
by Auto_tac;
qed "length_0_conv";
AddIffs [length_0_conv];

Goal "(0 < length xs) = (xs ~= [])";
by (induct_tac "xs" 1);
by Auto_tac;
qed "length_greater_0_conv";
AddIffs [length_greater_0_conv];

Goal "(length xs = Suc n) = (? y ys. xs = y#ys & length ys = n)";
by (induct_tac "xs" 1);
by Auto_tac;
qed "length_Suc_conv";

(** @ - append **)

section "@ - append";

Goal "(xs@ys)@zs = xs@(ys@zs)";
by (induct_tac "xs" 1);
by Auto_tac;
qed "append_assoc";
Addsimps [append_assoc];

Goal "xs @ [] = xs";
by (induct_tac "xs" 1);
by Auto_tac;
qed "append_Nil2";
Addsimps [append_Nil2];

Goal "(xs@ys = []) = (xs=[] & ys=[])";
by (induct_tac "xs" 1);
by Auto_tac;
qed "append_is_Nil_conv";
AddIffs [append_is_Nil_conv];

Goal "([] = xs@ys) = (xs=[] & ys=[])";
by (induct_tac "xs" 1);
by Auto_tac;
qed "Nil_is_append_conv";
AddIffs [Nil_is_append_conv];

Goal "(xs @ ys = xs) = (ys=[])";
by (induct_tac "xs" 1);
by Auto_tac;
qed "append_self_conv";

Goal "(xs = xs @ ys) = (ys=[])";
by (induct_tac "xs" 1);
by Auto_tac;
qed "self_append_conv";
AddIffs [append_self_conv,self_append_conv];

Goal "!ys. length xs = length ys | length us = length vs \
\              --> (xs@us = ys@vs) = (xs=ys & us=vs)";
by (induct_tac "xs" 1);
 by (rtac allI 1);
 by (case_tac "ys" 1);
  by (Asm_simp_tac 1);
 by (Force_tac 1);
by (rtac allI 1);
by (case_tac "ys" 1);
by (Force_tac 1);
by (Asm_simp_tac 1);
qed_spec_mp "append_eq_append_conv";
Addsimps [append_eq_append_conv];

Goal "(xs @ ys = xs @ zs) = (ys=zs)";
by (Simp_tac 1);
qed "same_append_eq";

Goal "(xs @ [x] = ys @ [y]) = (xs = ys & x = y)"; 
by (Simp_tac 1);
qed "append1_eq_conv";

Goal "(ys @ xs = zs @ xs) = (ys=zs)";
by (Simp_tac 1);
qed "append_same_eq";

AddIffs [same_append_eq, append1_eq_conv, append_same_eq];

Goal "(xs @ ys = ys) = (xs=[])";
by (cut_inst_tac [("zs","[]")] append_same_eq 1);
by Auto_tac;
qed "append_self_conv2";

Goal "(ys = xs @ ys) = (xs=[])";
by (simp_tac (simpset() addsimps
     [simplify (simpset()) (read_instantiate[("ys","[]")]append_same_eq)]) 1);
by (Blast_tac 1);
qed "self_append_conv2";
AddIffs [append_self_conv2,self_append_conv2];

Goal "xs ~= [] --> hd xs # tl xs = xs";
by (induct_tac "xs" 1);
by Auto_tac;
qed_spec_mp "hd_Cons_tl";
Addsimps [hd_Cons_tl];

Goal "hd(xs@ys) = (if xs=[] then hd ys else hd xs)";
by (induct_tac "xs" 1);
by Auto_tac;
qed "hd_append";

Goal "xs ~= [] ==> hd(xs @ ys) = hd xs";
by (asm_simp_tac (simpset() addsimps [hd_append]
                           addsplits [list.split]) 1);
qed "hd_append2";
Addsimps [hd_append2];

Goal "tl(xs@ys) = (case xs of [] => tl(ys) | z#zs => zs@ys)";
by (simp_tac (simpset() addsplits [list.split]) 1);
qed "tl_append";

Goal "xs ~= [] ==> tl(xs @ ys) = (tl xs) @ ys";
by (asm_simp_tac (simpset() addsimps [tl_append]
                           addsplits [list.split]) 1);
qed "tl_append2";
Addsimps [tl_append2];

(* trivial rules for solving @-equations automatically *)

Goal "xs = ys ==> xs = [] @ ys";
by (Asm_simp_tac 1);
qed "eq_Nil_appendI";

Goal "[| x#xs1 = ys; xs = xs1 @ zs |] ==> x#xs = ys@zs";
by (dtac sym 1);
by (Asm_simp_tac 1);
qed "Cons_eq_appendI";

Goal "[| xs@xs1 = zs; ys = xs1 @ us |] ==> xs@ys = zs@us";
by (dtac sym 1);
by (Asm_simp_tac 1);
qed "append_eq_appendI";


(***
Simplification procedure for all list equalities.
Currently only tries to rearranges @ to see if
- both lists end in a singleton list,
- or both lists end in the same list.
***)
local

val list_eq_pattern =
  Thm.read_cterm (Theory.sign_of (the_context ())) ("(xs::'a list) = ys",HOLogic.boolT);

fun last (cons as Const("List.list.Cons",_) $ _ $ xs) =
      (case xs of Const("List.list.Nil",_) => cons | _ => last xs)
  | last (Const("List.op @",_) $ _ $ ys) = last ys
  | last t = t;

fun list1 (Const("List.list.Cons",_) $ _ $ Const("List.list.Nil",_)) = true
  | list1 _ = false;

fun butlast ((cons as Const("List.list.Cons",_) $ x) $ xs) =
      (case xs of Const("List.list.Nil",_) => xs | _ => cons $ butlast xs)
  | butlast ((app as Const("List.op @",_) $ xs) $ ys) = app $ butlast ys
  | butlast xs = Const("List.list.Nil",fastype_of xs);

val rearr_tac =
  simp_tac (HOL_basic_ss addsimps [append_assoc,append_Nil,append_Cons]);

fun list_eq sg _ (F as (eq as Const(_,eqT)) $ lhs $ rhs) =
  let
    val lastl = last lhs and lastr = last rhs
    fun rearr conv =
      let val lhs1 = butlast lhs and rhs1 = butlast rhs
          val Type(_,listT::_) = eqT
          val appT = [listT,listT] ---> listT
          val app = Const("List.op @",appT)
          val F2 = eq $ (app$lhs1$lastl) $ (app$rhs1$lastr)
          val ct = cterm_of sg (HOLogic.mk_Trueprop(HOLogic.mk_eq(F,F2)))
          val thm = prove_goalw_cterm [] ct (K [rearr_tac 1])
            handle ERROR =>
            error("The error(s) above occurred while trying to prove " ^
                  string_of_cterm ct)
      in Some((conv RS (thm RS trans)) RS eq_reflection) end

  in if list1 lastl andalso list1 lastr
     then rearr append1_eq_conv
     else
     if lastl aconv lastr
     then rearr append_same_eq
     else None
  end;
in
val list_eq_simproc = mk_simproc "list_eq" [list_eq_pattern] list_eq;
end;

Addsimprocs [list_eq_simproc];


(** map **)

section "map";

Goal "(!x. x : set xs --> f x = g x) --> map f xs = map g xs";
by (induct_tac "xs" 1);
by Auto_tac;
bind_thm("map_ext", impI RS (allI RS (result() RS mp)));

Goal "map (%x. x) = (%xs. xs)";
by (rtac ext 1);
by (induct_tac "xs" 1);
by Auto_tac;
qed "map_ident";
Addsimps[map_ident];

Goal "map f (xs@ys) = map f xs @ map f ys";
by (induct_tac "xs" 1);
by Auto_tac;
qed "map_append";
Addsimps[map_append];

Goalw [o_def] "map (f o g) xs = map f (map g xs)";
by (induct_tac "xs" 1);
by Auto_tac;
qed "map_compose";
(*Addsimps[map_compose];*)

Goal "rev(map f xs) = map f (rev xs)";
by (induct_tac "xs" 1);
by Auto_tac;
qed "rev_map";

(* a congruence rule for map: *)
Goal "xs=ys ==> (!x. x : set ys --> f x = g x) --> map f xs = map g ys";
by (hyp_subst_tac 1);
by (induct_tac "ys" 1);
by Auto_tac;
bind_thm("map_cong", impI RSN (2,allI RSN (2, result() RS mp)));

Goal "(map f xs = []) = (xs = [])";
by (case_tac "xs" 1);
by Auto_tac;
qed "map_is_Nil_conv";
AddIffs [map_is_Nil_conv];

Goal "([] = map f xs) = (xs = [])";
by (case_tac "xs" 1);
by Auto_tac;
qed "Nil_is_map_conv";
AddIffs [Nil_is_map_conv];

Goal "(map f xs = y#ys) = (? x xs'. xs = x#xs' & f x = y & map f xs' = ys)";
by (case_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "map_eq_Cons";

Goal "!xs. map f xs = map f ys --> (!x y. f x = f y --> x=y) --> xs=ys";
by (induct_tac "ys" 1);
 by (Asm_simp_tac 1);
by (fast_tac (claset() addss (simpset() addsimps [map_eq_Cons])) 1);
qed_spec_mp "map_injective";

Goal "inj f ==> inj (map f)";
by (blast_tac (claset() addDs [map_injective,injD] addIs [injI]) 1);
qed "inj_mapI";

Goalw [inj_on_def] "inj (map f) ==> inj f";
by (Clarify_tac 1);
by (eres_inst_tac [("x","[x]")] ballE 1);
 by (eres_inst_tac [("x","[y]")] ballE 1);
  by (Asm_full_simp_tac 1);
 by (Blast_tac 1);
by (Blast_tac 1);
qed "inj_mapD";

Goal "inj (map f) = inj f";
by (blast_tac (claset() addDs [inj_mapD] addIs [inj_mapI]) 1);
qed "inj_map";

(** rev **)

section "rev";

Goal "rev(xs@ys) = rev(ys) @ rev(xs)";
by (induct_tac "xs" 1);
by Auto_tac;
qed "rev_append";
Addsimps[rev_append];

Goal "rev(rev l) = l";
by (induct_tac "l" 1);
by Auto_tac;
qed "rev_rev_ident";
Addsimps[rev_rev_ident];

Goal "(rev xs = []) = (xs = [])";
by (induct_tac "xs" 1);
by Auto_tac;
qed "rev_is_Nil_conv";
AddIffs [rev_is_Nil_conv];

Goal "([] = rev xs) = (xs = [])";
by (induct_tac "xs" 1);
by Auto_tac;
qed "Nil_is_rev_conv";
AddIffs [Nil_is_rev_conv];

Goal "!ys. (rev xs = rev ys) = (xs = ys)";
by (induct_tac "xs" 1);
 by (Force_tac 1);
by (rtac allI 1);
by (case_tac "ys" 1);
 by (Asm_simp_tac 1);
by (Force_tac 1);
qed_spec_mp "rev_is_rev_conv";
AddIffs [rev_is_rev_conv];

val prems = Goal "[| P []; !!x xs. P xs ==> P(xs@[x]) |] ==> P xs";
by (stac (rev_rev_ident RS sym) 1);
by (res_inst_tac [("list", "rev xs")] list.induct 1);
by (ALLGOALS Simp_tac);
by (resolve_tac prems 1);
by (eresolve_tac prems 1);
qed "rev_induct";

val rev_induct_tac = induct_thm_tac rev_induct;

Goal  "(xs = [] --> P) -->  (!ys y. xs = ys@[y] --> P) --> P";
by (rev_induct_tac "xs" 1);
by Auto_tac;
qed "rev_exhaust_aux";

bind_thm ("rev_exhaust", Rulify.rulify rev_exhaust_aux);


(** set **)

section "set";

Goal "finite (set xs)";
by (induct_tac "xs" 1);
by Auto_tac;
qed "finite_set";
AddIffs [finite_set];

Goal "set (xs@ys) = (set xs Un set ys)";
by (induct_tac "xs" 1);
by Auto_tac;
qed "set_append";
Addsimps[set_append];

Goal "set l <= set (x#l)";
by Auto_tac;
qed "set_subset_Cons";

Goal "(set xs = {}) = (xs = [])";
by (induct_tac "xs" 1);
by Auto_tac;
qed "set_empty";
Addsimps [set_empty];

Goal "set(rev xs) = set(xs)";
by (induct_tac "xs" 1);
by Auto_tac;
qed "set_rev";
Addsimps [set_rev];

Goal "set(map f xs) = f`(set xs)";
by (induct_tac "xs" 1);
by Auto_tac;
qed "set_map";
Addsimps [set_map];

Goal "set(filter P xs) = {x. x : set xs & P x}";
by (induct_tac "xs" 1);
by Auto_tac;
qed "set_filter";
Addsimps [set_filter];

Goal "set[i..j(] = {k. i <= k & k < j}";
by (induct_tac "j" 1);
by (ALLGOALS Asm_simp_tac);
by (etac ssubst 1);
by Auto_tac;
by (arith_tac 1);
qed "set_upt";
Addsimps [set_upt];

Goal "(x : set xs) = (? ys zs. xs = ys@x#zs)";
by (induct_tac "xs" 1);
 by (Simp_tac 1);
by (Asm_simp_tac 1);
by (rtac iffI 1);
by (blast_tac (claset() addIs [eq_Nil_appendI,Cons_eq_appendI]) 1);
by (REPEAT(etac exE 1));
by (case_tac "ys" 1);
by Auto_tac;
qed "in_set_conv_decomp";


(* eliminate `lists' in favour of `set' *)

Goal "(xs : lists A) = (!x : set xs. x : A)";
by (induct_tac "xs" 1);
by Auto_tac;
qed "in_lists_conv_set";

bind_thm("in_listsD",in_lists_conv_set RS iffD1);
AddSDs [in_listsD];
bind_thm("in_listsI",in_lists_conv_set RS iffD2);
AddSIs [in_listsI];

(** mem **)
 
section "mem";

Goal "(x mem xs) = (x: set xs)";
by (induct_tac "xs" 1);
by Auto_tac;
qed "set_mem_eq";


(** list_all **)

section "list_all";

Goal "list_all P xs = (!x:set xs. P x)";
by (induct_tac "xs" 1);
by Auto_tac;
qed "list_all_conv";

Goal "list_all P (xs@ys) = (list_all P xs & list_all P ys)";
by (induct_tac "xs" 1);
by Auto_tac;
qed "list_all_append";
Addsimps [list_all_append];


(** filter **)

section "filter";

Goal "filter P (xs@ys) = filter P xs @ filter P ys";
by (induct_tac "xs" 1);
by Auto_tac;
qed "filter_append";
Addsimps [filter_append];

Goal "filter (%x. True) xs = xs";
by (induct_tac "xs" 1);
by Auto_tac;
qed "filter_True";
Addsimps [filter_True];

Goal "filter (%x. False) xs = []";
by (induct_tac "xs" 1);
by Auto_tac;
qed "filter_False";
Addsimps [filter_False];

Goal "length (filter P xs) <= length xs";
by (induct_tac "xs" 1);
by Auto_tac;
by (asm_simp_tac (simpset() addsimps [le_SucI]) 1);
qed "length_filter";
Addsimps[length_filter];

Goal "set (filter P xs) <= set xs";
by Auto_tac;
qed "filter_is_subset";
Addsimps [filter_is_subset];


section "concat";

Goal  "concat(xs@ys) = concat(xs)@concat(ys)";
by (induct_tac "xs" 1);
by Auto_tac;
qed"concat_append";
Addsimps [concat_append];

Goal "(concat xss = []) = (!xs:set xss. xs=[])";
by (induct_tac "xss" 1);
by Auto_tac;
qed "concat_eq_Nil_conv";
AddIffs [concat_eq_Nil_conv];

Goal "([] = concat xss) = (!xs:set xss. xs=[])";
by (induct_tac "xss" 1);
by Auto_tac;
qed "Nil_eq_concat_conv";
AddIffs [Nil_eq_concat_conv];

Goal  "set(concat xs) = Union(set ` set xs)";
by (induct_tac "xs" 1);
by Auto_tac;
qed"set_concat";
Addsimps [set_concat];

Goal "map f (concat xs) = concat (map (map f) xs)"; 
by (induct_tac "xs" 1);
by Auto_tac;
qed "map_concat";

Goal "filter p (concat xs) = concat (map (filter p) xs)"; 
by (induct_tac "xs" 1);
by Auto_tac;
qed"filter_concat"; 

Goal "rev(concat xs) = concat (map rev (rev xs))";
by (induct_tac "xs" 1);
by Auto_tac;
qed "rev_concat";

(** nth **)

section "nth";

Goal "(x#xs)!0 = x";
by Auto_tac;
qed "nth_Cons_0";
Addsimps [nth_Cons_0];

Goal "(x#xs)!(Suc n) = xs!n";
by Auto_tac;
qed "nth_Cons_Suc";
Addsimps [nth_Cons_Suc];

Delsimps (thms "nth.simps");

Goal "!n. (xs@ys)!n = (if n < length xs then xs!n else ys!(n - length xs))";
by (induct_tac "xs" 1);
 by (Asm_simp_tac 1);
 by (rtac allI 1);
 by (case_tac "n" 1);
  by Auto_tac;
qed_spec_mp "nth_append";

Goal "!n. n < length xs --> (map f xs)!n = f(xs!n)";
by (induct_tac "xs" 1);
 by (Asm_full_simp_tac 1);
by (rtac allI 1);
by (induct_tac "n" 1);
by Auto_tac;
qed_spec_mp "nth_map";
Addsimps [nth_map];

Goal "set xs = {xs!i |i. i < length xs}";
by (induct_tac "xs" 1);
 by (Simp_tac 1);
by (Asm_simp_tac 1);
by Safe_tac;
  by (res_inst_tac [("x","0")] exI 1);
  by (Simp_tac 1);
 by (res_inst_tac [("x","Suc i")] exI 1);
 by (Asm_simp_tac 1);
by (case_tac "i" 1);
 by (Asm_full_simp_tac 1);
by (rename_tac "j" 1);
 by (res_inst_tac [("x","j")] exI 1);
by (Asm_simp_tac 1);
qed "set_conv_nth";

Goal "n < length xs ==> Ball (set xs) P --> P(xs!n)";
by (simp_tac (simpset() addsimps [set_conv_nth]) 1);
by (Blast_tac 1);
qed_spec_mp "list_ball_nth";

Goal "n < length xs ==> xs!n : set xs";
by (simp_tac (simpset() addsimps [set_conv_nth]) 1);
by (Blast_tac 1);
qed_spec_mp "nth_mem";
Addsimps [nth_mem];

Goal "(!i. i < length xs --> P(xs!i)) --> (!x : set xs. P x)";
by (simp_tac (simpset() addsimps [set_conv_nth]) 1);
by (Blast_tac 1);
qed_spec_mp "all_nth_imp_all_set";

Goal "(!x : set xs. P x) = (!i. i<length xs --> P (xs ! i))";
by (simp_tac (simpset() addsimps [set_conv_nth]) 1);
by (Blast_tac 1);
qed_spec_mp "all_set_conv_all_nth";


(** list update **)

section "list update";

Goal "!i. length(xs[i:=x]) = length xs";
by (induct_tac "xs" 1);
by (Simp_tac 1);
by (asm_full_simp_tac (simpset() addsplits [nat.split]) 1);
qed_spec_mp "length_list_update";
Addsimps [length_list_update];

Goal "!i j. i < length xs  --> (xs[i:=x])!j = (if i=j then x else xs!j)";
by (induct_tac "xs" 1);
 by (Simp_tac 1);
by (auto_tac (claset(), simpset() addsimps [nth_Cons] addsplits [nat.split]));
qed_spec_mp "nth_list_update";

Goal "i < length xs  ==> (xs[i:=x])!i = x";
by (asm_simp_tac (simpset() addsimps [nth_list_update]) 1);
qed "nth_list_update_eq";
Addsimps [nth_list_update_eq];

Goal "!i j. i ~= j --> xs[i:=x]!j = xs!j";
by (induct_tac "xs" 1);
 by (Simp_tac 1);
by (auto_tac (claset(), simpset() addsimps [nth_Cons] addsplits [nat.split]));
qed_spec_mp "nth_list_update_neq";
Addsimps [nth_list_update_neq];

Goal "!i. i < size xs --> xs[i:=x, i:=y] = xs[i:=y]";
by (induct_tac "xs" 1);
 by (Simp_tac 1);
by (asm_simp_tac (simpset() addsplits [nat.split]) 1);
qed_spec_mp "list_update_overwrite";
Addsimps [list_update_overwrite];

Goal "!i < length xs. (xs[i := x] = xs) = (xs!i = x)";
by (induct_tac "xs" 1);
 by (Simp_tac 1);
by (simp_tac (simpset() addsplits [nat.split]) 1);
by (Blast_tac 1);
qed_spec_mp "list_update_same_conv";

Goal "!i xy xs. length xs = length ys --> \
\     (zip xs ys)[i:=xy] = zip (xs[i:=fst xy]) (ys[i:=snd xy])";
by (induct_tac "ys" 1);
 by Auto_tac;
by (case_tac "xs" 1);
 by (auto_tac (claset(), simpset() addsplits [nat.split]));
qed_spec_mp "update_zip";

Goal "!i. set(xs[i:=x]) <= insert x (set xs)";
by (induct_tac "xs" 1);
 by (asm_full_simp_tac (simpset() addsimps []) 1);
by (asm_full_simp_tac (simpset() addsplits [nat.split]) 1);
by (Fast_tac  1);
qed_spec_mp "set_update_subset_insert";

Goal "[| set xs <= A; x:A |] ==> set(xs[i := x]) <= A";
by(fast_tac (claset() addSDs [set_update_subset_insert RS subsetD]) 1);
qed "set_update_subsetI";

(** last & butlast **)

section "last / butlast";

Goal "last(xs@[x]) = x";
by (induct_tac "xs" 1);
by Auto_tac;
qed "last_snoc";
Addsimps [last_snoc];

Goal "butlast(xs@[x]) = xs";
by (induct_tac "xs" 1);
by Auto_tac;
qed "butlast_snoc";
Addsimps [butlast_snoc];

Goal "length(butlast xs) = length xs - 1";
by (rev_induct_tac "xs" 1);
by Auto_tac;
qed "length_butlast";
Addsimps [length_butlast];

Goal "!ys. butlast (xs@ys) = (if ys=[] then butlast xs else xs@butlast ys)";
by (induct_tac "xs" 1);
by Auto_tac;
qed_spec_mp "butlast_append";

Goal "xs ~= [] --> butlast xs @ [last xs] = xs";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "append_butlast_last_id";
Addsimps [append_butlast_last_id];

Goal "x:set(butlast xs) --> x:set xs";
by (induct_tac "xs" 1);
by Auto_tac;
qed_spec_mp "in_set_butlastD";

Goal "x:set(butlast xs) | x:set(butlast ys) ==> x:set(butlast(xs@ys))";
by (auto_tac (claset() addDs [in_set_butlastD],
	      simpset() addsimps [butlast_append]));
qed "in_set_butlast_appendI";

(** take  & drop **)
section "take & drop";

Goal "take 0 xs = []";
by (induct_tac "xs" 1);
by Auto_tac;
qed "take_0";

Goal "drop 0 xs = xs";
by (induct_tac "xs" 1);
by Auto_tac;
qed "drop_0";

Goal "take (Suc n) (x#xs) = x # take n xs";
by (Simp_tac 1);
qed "take_Suc_Cons";

Goal "drop (Suc n) (x#xs) = drop n xs";
by (Simp_tac 1);
qed "drop_Suc_Cons";

Delsimps [take_Cons,drop_Cons];
Addsimps [take_0,take_Suc_Cons,drop_0,drop_Suc_Cons];

Goal "!xs. length(take n xs) = min (length xs) n";
by (induct_tac "n" 1);
 by Auto_tac;
by (case_tac "xs" 1);
 by Auto_tac;
qed_spec_mp "length_take";
Addsimps [length_take];

Goal "!xs. length(drop n xs) = (length xs - n)";
by (induct_tac "n" 1);
 by Auto_tac;
by (case_tac "xs" 1);
 by Auto_tac;
qed_spec_mp "length_drop";
Addsimps [length_drop];

Goal "!xs. length xs <= n --> take n xs = xs";
by (induct_tac "n" 1);
 by Auto_tac;
by (case_tac "xs" 1);
 by Auto_tac;
qed_spec_mp "take_all";
Addsimps [take_all];

Goal "!xs. length xs <= n --> drop n xs = []";
by (induct_tac "n" 1);
 by Auto_tac;
by (case_tac "xs" 1);
 by Auto_tac;
qed_spec_mp "drop_all";
Addsimps [drop_all];

Goal "!xs. take n (xs @ ys) = (take n xs @ take (n - length xs) ys)";
by (induct_tac "n" 1);
 by Auto_tac;
by (case_tac "xs" 1);
 by Auto_tac;
qed_spec_mp "take_append";
Addsimps [take_append];

Goal "!xs. drop n (xs@ys) = drop n xs @ drop (n - length xs) ys"; 
by (induct_tac "n" 1);
 by Auto_tac;
by (case_tac "xs" 1);
 by Auto_tac;
qed_spec_mp "drop_append";
Addsimps [drop_append];

Goal "!xs n. take n (take m xs) = take (min n m) xs"; 
by (induct_tac "m" 1);
 by Auto_tac;
by (case_tac "xs" 1);
 by Auto_tac;
by (case_tac "na" 1);
 by Auto_tac;
qed_spec_mp "take_take";
Addsimps [take_take];

Goal "!xs. drop n (drop m xs) = drop (n + m) xs"; 
by (induct_tac "m" 1);
 by Auto_tac;
by (case_tac "xs" 1);
 by Auto_tac;
qed_spec_mp "drop_drop";
Addsimps [drop_drop];

Goal "!xs n. take n (drop m xs) = drop m (take (n + m) xs)"; 
by (induct_tac "m" 1);
 by Auto_tac;
by (case_tac "xs" 1);
 by Auto_tac;
qed_spec_mp "take_drop";

Goal "!xs. take n xs @ drop n xs = xs";
by (induct_tac "n" 1);
 by Auto_tac;
by (case_tac "xs" 1);
 by Auto_tac;
qed_spec_mp "append_take_drop_id";
Addsimps [append_take_drop_id];

Goal "!xs. take n (map f xs) = map f (take n xs)"; 
by (induct_tac "n" 1);
 by Auto_tac;
by (case_tac "xs" 1);
 by Auto_tac;
qed_spec_mp "take_map"; 

Goal "!xs. drop n (map f xs) = map f (drop n xs)"; 
by (induct_tac "n" 1);
 by Auto_tac;
by (case_tac "xs" 1);
 by Auto_tac;
qed_spec_mp "drop_map";

Goal "!n i. i < n --> (take n xs)!i = xs!i";
by (induct_tac "xs" 1);
 by Auto_tac;
by (case_tac "n" 1);
 by (Blast_tac 1);
by (case_tac "i" 1);
 by Auto_tac;
qed_spec_mp "nth_take";
Addsimps [nth_take];

Goal  "!xs i. n + i <= length xs --> (drop n xs)!i = xs!(n+i)";
by (induct_tac "n" 1);
 by Auto_tac;
by (case_tac "xs" 1);
 by Auto_tac;
qed_spec_mp "nth_drop";
Addsimps [nth_drop];


Goal
 "!zs. (xs@ys = zs) = (xs = take (length xs) zs & ys = drop (length xs) zs)";
by (induct_tac "xs" 1);
 by (Simp_tac 1);
by (Asm_full_simp_tac 1);
by (Clarify_tac 1);
by (case_tac "zs" 1);
by (Auto_tac);
qed_spec_mp "append_eq_conv_conj";

(** takeWhile & dropWhile **)

section "takeWhile & dropWhile";

Goal "takeWhile P xs @ dropWhile P xs = xs";
by (induct_tac "xs" 1);
by Auto_tac;
qed "takeWhile_dropWhile_id";
Addsimps [takeWhile_dropWhile_id];

Goal  "x:set xs & ~P(x) --> takeWhile P (xs @ ys) = takeWhile P xs";
by (induct_tac "xs" 1);
by Auto_tac;
bind_thm("takeWhile_append1", conjI RS (result() RS mp));
Addsimps [takeWhile_append1];

Goal "(!x:set xs. P(x)) --> takeWhile P (xs @ ys) = xs @ takeWhile P ys";
by (induct_tac "xs" 1);
by Auto_tac;
bind_thm("takeWhile_append2", ballI RS (result() RS mp));
Addsimps [takeWhile_append2];

Goal "~P(x) ==> takeWhile P (xs @ (x#l)) = takeWhile P xs";
by (induct_tac "xs" 1);
by Auto_tac;
qed "takeWhile_tail";

Goal "x:set xs & ~P(x) --> dropWhile P (xs @ ys) = (dropWhile P xs)@ys";
by (induct_tac "xs" 1);
by Auto_tac;
bind_thm("dropWhile_append1", conjI RS (result() RS mp));
Addsimps [dropWhile_append1];

Goal "(!x:set xs. P(x)) --> dropWhile P (xs @ ys) = dropWhile P ys";
by (induct_tac "xs" 1);
by Auto_tac;
bind_thm("dropWhile_append2", ballI RS (result() RS mp));
Addsimps [dropWhile_append2];

Goal "x:set(takeWhile P xs) --> x:set xs & P x";
by (induct_tac "xs" 1);
by Auto_tac;
qed_spec_mp"set_take_whileD";

(** zip **)
section "zip";

Goal "zip [] ys = []";
by (induct_tac "ys" 1);
by Auto_tac;
qed "zip_Nil";
Addsimps [zip_Nil];

Goal "zip (x#xs) (y#ys) = (x,y)#zip xs ys";
by (Simp_tac 1);
qed "zip_Cons_Cons";
Addsimps [zip_Cons_Cons];

Delsimps(tl (thms"zip.simps"));

Goal "!xs. length (zip xs ys) = min (length xs) (length ys)";
by (induct_tac "ys" 1);
 by (Simp_tac 1);
by (Clarify_tac 1);
by (case_tac "xs" 1);
 by (Auto_tac);
qed_spec_mp "length_zip";
Addsimps [length_zip];

Goal
 "!xs. zip (xs@ys) zs = \
\      zip xs (take (length xs) zs) @ zip ys (drop (length xs) zs)";
by (induct_tac "zs" 1);
 by (Simp_tac 1);
by (Clarify_tac 1);
by (case_tac "xs" 1);
 by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
qed_spec_mp "zip_append1";

Goal
 "!ys. zip xs (ys@zs) = \
\      zip (take (length ys) xs) ys @ zip (drop (length ys) xs) zs";
by (induct_tac "xs" 1);
 by (Simp_tac 1);
by (Clarify_tac 1);
by (case_tac "ys" 1);
 by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
qed_spec_mp "zip_append2";

Goal
 "[| length xs = length us; length ys = length vs |] ==> \
\ zip (xs@ys) (us@vs) = zip xs us @ zip ys vs";
by (asm_simp_tac (simpset() addsimps [zip_append1]) 1);
qed_spec_mp "zip_append";
Addsimps [zip_append];

Goal "!xs. length xs = length ys --> zip (rev xs) (rev ys) = rev (zip xs ys)";
by (induct_tac "ys" 1);
 by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
by (Clarify_tac 1);
by (case_tac "xs" 1);
 by (Auto_tac);
qed_spec_mp "zip_rev";


Goal
"!i xs. i < length xs --> i < length ys --> (zip xs ys)!i = (xs!i, ys!i)";
by (induct_tac "ys" 1);
 by (Simp_tac 1);
by (Clarify_tac 1);
by (case_tac "xs" 1);
 by (Auto_tac);
by (asm_full_simp_tac (simpset() addsimps (thms"nth.simps") addsplits [nat.split]) 1);
qed_spec_mp "nth_zip";
Addsimps [nth_zip];

Goal "set(zip xs ys) = {(xs!i,ys!i) |i. i < min (length xs) (length ys)}";
by (simp_tac (simpset() addsimps [set_conv_nth]addcongs [rev_conj_cong]) 1);
qed_spec_mp "set_zip";

Goal
 "length xs = length ys ==> zip (xs[i:=x]) (ys[i:=y]) = (zip xs ys)[i:=(x,y)]";
by (rtac sym 1);
by (asm_simp_tac (simpset() addsimps [update_zip]) 1);
qed_spec_mp "zip_update";

Goal "!j. zip (replicate i x) (replicate j y) = replicate (min i j) (x,y)";
by (induct_tac "i" 1);
 by (Auto_tac);
by (case_tac "j" 1);
 by (Auto_tac);
qed "zip_replicate";
Addsimps [zip_replicate];

(** list_all2 **)
section "list_all2";

Goalw [list_all2_def] "list_all2 P xs ys ==> length xs = length ys";
by (Asm_simp_tac 1);
qed "list_all2_lengthD";

Goalw [list_all2_def] "list_all2 P [] ys = (ys=[])";
by (Simp_tac 1);
qed "list_all2_Nil";
AddIffs [list_all2_Nil];

Goalw [list_all2_def] "list_all2 P xs [] = (xs=[])";
by (Simp_tac 1);
qed "list_all2_Nil2";
AddIffs [list_all2_Nil2];

Goalw [list_all2_def]
 "list_all2 P (x#xs) (y#ys) = (P x y & list_all2 P xs ys)";
by (Auto_tac);
qed "list_all2_Cons";
AddIffs[list_all2_Cons];

Goalw [list_all2_def]
 "list_all2 P (x#xs) ys = (? z zs. ys = z#zs & P x z & list_all2 P xs zs)";
by (case_tac "ys" 1);
by (Auto_tac);
qed "list_all2_Cons1";

Goalw [list_all2_def]
 "list_all2 P xs (y#ys) = (? z zs. xs = z#zs & P z y & list_all2 P zs ys)";
by (case_tac "xs" 1);
by (Auto_tac);
qed "list_all2_Cons2";

Goalw [list_all2_def]
 "list_all2 P (xs@ys) zs = \
\ (EX us vs. zs = us@vs & length us = length xs & length vs = length ys & \
\            list_all2 P xs us & list_all2 P ys vs)";
by (simp_tac (simpset() addsimps [zip_append1]) 1);
by (rtac iffI 1);
 by (res_inst_tac [("x","take (length xs) zs")] exI 1);
 by (res_inst_tac [("x","drop (length xs) zs")] exI 1);
 by (force_tac (claset(),
		simpset() addsplits [nat_diff_split] addsimps [min_def]) 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [ball_Un]) 1);
qed "list_all2_append1";

Goalw [list_all2_def]
 "list_all2 P xs (ys@zs) = \
\ (EX us vs. xs = us@vs & length us = length ys & length vs = length zs & \
\            list_all2 P us ys & list_all2 P vs zs)";
by (simp_tac (simpset() addsimps [zip_append2]) 1);
by (rtac iffI 1);
 by (res_inst_tac [("x","take (length ys) xs")] exI 1);
 by (res_inst_tac [("x","drop (length ys) xs")] exI 1);
 by (force_tac (claset(),
		simpset() addsplits [nat_diff_split] addsimps [min_def]) 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [ball_Un]) 1);
qed "list_all2_append2";

Goalw [list_all2_def]
  "list_all2 P xs ys = \
\  (length xs = length ys & (!i<length xs. P (xs!i) (ys!i)))";
by (force_tac (claset(), simpset() addsimps [set_zip]) 1);
qed "list_all2_conv_all_nth";

(** foldl **)
section "foldl";

Goal "!a. foldl f a (xs @ ys) = foldl f (foldl f a xs) ys";
by (induct_tac "xs" 1);
by Auto_tac;
qed_spec_mp "foldl_append";
Addsimps [foldl_append];

(* Note: `n <= foldl op+ n ns' looks simpler, but is more difficult to use
   because it requires an additional transitivity step
*)
Goal "!n::nat. m <= n --> m <= foldl op+ n ns";
by (induct_tac "ns" 1);
by Auto_tac;
qed_spec_mp "start_le_sum";

Goal "!!n::nat. n : set ns ==> n <= foldl op+ 0 ns";
by (force_tac (claset() addIs [start_le_sum],
              simpset() addsimps [in_set_conv_decomp]) 1);
qed "elem_le_sum";

Goal "!m::nat. (foldl op+ m ns = 0) = (m=0 & (!n : set ns. n=0))";
by (induct_tac "ns" 1);
by Auto_tac;
qed_spec_mp "sum_eq_0_conv";
AddIffs [sum_eq_0_conv];

(** upto **)

(* Does not terminate! *)
Goal "[i..j(] = (if i<j then i#[Suc i..j(] else [])";
by (induct_tac "j" 1);
by Auto_tac;
qed "upt_rec";

Goal "j<=i ==> [i..j(] = []";
by (stac upt_rec 1);
by (Asm_simp_tac 1);
qed "upt_conv_Nil";
Addsimps [upt_conv_Nil];

(*Only needed if upt_Suc is deleted from the simpset*)
Goal "i<=j ==> [i..(Suc j)(] = [i..j(]@[j]";
by (Asm_simp_tac 1);
qed "upt_Suc_append";

Goal "i<j ==> [i..j(] = i#[Suc i..j(]";
by (rtac trans 1);
by (stac upt_rec 1);
by (rtac refl 2);
by (Asm_simp_tac 1);
qed "upt_conv_Cons";

(*LOOPS as a simprule, since j<=j*)
Goal "i<=j ==> [i..j+k(] = [i..j(]@[j..j+k(]";
by (induct_tac "k" 1);
by Auto_tac;
qed "upt_add_eq_append";

Goal "length [i..j(] = j-i";
by (induct_tac "j" 1);
 by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [Suc_diff_le]) 1);
qed "length_upt";
Addsimps [length_upt];

Goal "i+k < j --> [i..j(] ! k = i+k";
by (induct_tac "j" 1);
 by (asm_simp_tac (simpset() addsimps [less_Suc_eq, nth_append] 
                             addsplits [nat_diff_split]) 2);
by (Simp_tac 1);
qed_spec_mp "nth_upt";
Addsimps [nth_upt];

Goal "!i. i+m <= n --> take m [i..n(] = [i..i+m(]";
by (induct_tac "m" 1);
 by (Simp_tac 1);
by (Clarify_tac 1);
by (stac upt_rec 1);
by (rtac sym 1);
by (stac upt_rec 1);
by (asm_simp_tac (simpset() delsimps (thms"upt.simps")) 1);
qed_spec_mp "take_upt";
Addsimps [take_upt];

Goal "map Suc [m..n(] = [Suc m..n]";
by (induct_tac "n" 1);
by Auto_tac;
qed "map_Suc_upt";

Goal "ALL i. i < n-m --> (map f [m..n(]) ! i = f(m+i)";
by (induct_thm_tac diff_induct "n m" 1);
by (stac (map_Suc_upt RS sym) 3);
by (auto_tac (claset(), simpset() addsimps [less_diff_conv, nth_upt]));
qed_spec_mp "nth_map_upt";

Goal "ALL xs ys. k <= length xs --> k <= length ys -->  \
\        (ALL i. i < k --> xs!i = ys!i)  \
\     --> take k xs = take k ys";
by (induct_tac "k" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [less_Suc_eq_0_disj, 
						all_conj_distrib])));
by (Clarify_tac 1);
(*Both lists must be non-empty*)
by (case_tac "xs" 1);
by (case_tac "ys" 2);
by (ALLGOALS Clarify_tac);
(*prenexing's needed, not miniscoping*)
by (ALLGOALS (full_simp_tac (simpset() addsimps (all_simps RL [sym])  
                                       delsimps (all_simps))));
by (Blast_tac 1);
qed_spec_mp "nth_take_lemma";

Goal "[| length xs = length ys;  \
\        ALL i. i < length xs --> xs!i = ys!i |]  \
\     ==> xs = ys";
by (forward_tac [[le_refl, eq_imp_le] MRS nth_take_lemma] 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [take_all])));
qed_spec_mp "nth_equalityI";

(*The famous take-lemma*)
Goal "(ALL i. take i xs = take i ys) ==> xs = ys";
by (dres_inst_tac [("x", "max (length xs) (length ys)")] spec 1);
by (full_simp_tac (simpset() addsimps [le_max_iff_disj, take_all]) 1);
qed_spec_mp "take_equalityI";


(** nodups & remdups **)
section "nodups & remdups";

Goal "set(remdups xs) = set xs";
by (induct_tac "xs" 1);
 by (Simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [insert_absorb]) 1);
qed "set_remdups";
Addsimps [set_remdups];

Goal "nodups(remdups xs)";
by (induct_tac "xs" 1);
by Auto_tac;
qed "nodups_remdups";

Goal "nodups xs --> nodups (filter P xs)";
by (induct_tac "xs" 1);
by Auto_tac;
qed_spec_mp "nodups_filter";

(** replicate **)
section "replicate";

Goal "length(replicate n x) = n";
by (induct_tac "n" 1);
by Auto_tac;
qed "length_replicate";
Addsimps [length_replicate];

Goal "map f (replicate n x) = replicate n (f x)";
by (induct_tac "n" 1);
by Auto_tac;
qed "map_replicate";
Addsimps [map_replicate];

Goal "(replicate n x) @ (x#xs) = x # replicate n x @ xs";
by (induct_tac "n" 1);
by Auto_tac;
qed "replicate_app_Cons_same";

Goal "rev(replicate n x) = replicate n x";
by (induct_tac "n" 1);
 by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [replicate_app_Cons_same]) 1);
qed "rev_replicate";
Addsimps [rev_replicate];

Goal "replicate (n+m) x = replicate n x @ replicate m x";
by (induct_tac "n" 1);
by Auto_tac;
qed "replicate_add";

Goal"n ~= 0 --> hd(replicate n x) = x";
by (induct_tac "n" 1);
by Auto_tac;
qed_spec_mp "hd_replicate";
Addsimps [hd_replicate];

Goal "n ~= 0 --> tl(replicate n x) = replicate (n-1) x";
by (induct_tac "n" 1);
by Auto_tac;
qed_spec_mp "tl_replicate";
Addsimps [tl_replicate];

Goal "n ~= 0 --> last(replicate n x) = x";
by (induct_tac "n" 1);
by Auto_tac;
qed_spec_mp "last_replicate";
Addsimps [last_replicate];

Goal "!i. i<n --> (replicate n x)!i = x";
by (induct_tac "n" 1);
 by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [nth_Cons] addsplits [nat.split]) 1);
qed_spec_mp "nth_replicate";
Addsimps [nth_replicate];

Goal "set(replicate (Suc n) x) = {x}";
by (induct_tac "n" 1);
by Auto_tac;
val lemma = result();

Goal "n ~= 0 ==> set(replicate n x) = {x}";
by (fast_tac (claset() addSDs [not0_implies_Suc] addSIs [lemma]) 1);
qed "set_replicate";
Addsimps [set_replicate];

Goal "set(replicate n x) = (if n=0 then {} else {x})";
by (Auto_tac);
qed "set_replicate_conv_if";

Goal "x : set(replicate n y) --> x=y";
by (asm_simp_tac (simpset() addsimps [set_replicate_conv_if]) 1);
qed_spec_mp "in_set_replicateD";


(*** Lexcicographic orderings on lists ***)
section"Lexcicographic orderings on lists";

Goal "wf r ==> wf(lexn r n)";
by (induct_tac "n" 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (rtac wf_subset 1);
by (rtac Int_lower1 2);
by (rtac wf_prod_fun_image 1);
by (rtac injI 2);
by Auto_tac;
qed "wf_lexn";

Goal "!xs ys. (xs,ys) : lexn r n --> length xs = n & length ys = n";
by (induct_tac "n" 1);
by Auto_tac;
qed_spec_mp "lexn_length";

Goalw [lex_def] "wf r ==> wf(lex r)";
by (rtac wf_UN 1);
by (blast_tac (claset() addIs [wf_lexn]) 1);
by (Clarify_tac 1);
by (rename_tac "m n" 1);
by (subgoal_tac "m ~= n" 1);
 by (Blast_tac 2);
by (blast_tac (claset() addDs [lexn_length,not_sym]) 1);
qed "wf_lex";
AddSIs [wf_lex];


Goal
 "lexn r n = \
\ {(xs,ys). length xs = n & length ys = n & \
\           (? xys x y xs' ys'. xs= xys @ x#xs' & ys= xys @ y#ys' & (x,y):r)}";
by (induct_tac "n" 1);
 by (Simp_tac 1);
 by (Blast_tac 1);
by (asm_full_simp_tac (simpset() addsimps [image_Collect, lex_prod_def]) 1);
by Auto_tac;
  by (Blast_tac 1);
 by (rename_tac "a xys x xs' y ys'" 1);
 by (res_inst_tac [("x","a#xys")] exI 1);
 by (Simp_tac 1);
by (case_tac "xys" 1);
 by (ALLGOALS Asm_full_simp_tac);
by (Blast_tac 1);
qed "lexn_conv";

Goalw [lex_def]
 "lex r = \
\ {(xs,ys). length xs = length ys & \
\           (? xys x y xs' ys'. xs= xys @ x#xs' & ys= xys @ y#ys' & (x,y):r)}";
by (force_tac (claset(), simpset() addsimps [lexn_conv]) 1);
qed "lex_conv";

Goalw [lexico_def] "wf r ==> wf(lexico r)";
by (Blast_tac 1);
qed "wf_lexico";
AddSIs [wf_lexico];

Goalw [lexico_def,diag_def,lex_prod_def,measure_def,inv_image_def]
"lexico r = {(xs,ys). length xs < length ys | \
\                     length xs = length ys & (xs,ys) : lex r}";
by (Simp_tac 1);
qed "lexico_conv";

Goal "([],ys) ~: lex r";
by (simp_tac (simpset() addsimps [lex_conv]) 1);
qed "Nil_notin_lex";

Goal "(xs,[]) ~: lex r";
by (simp_tac (simpset() addsimps [lex_conv]) 1);
qed "Nil2_notin_lex";

AddIffs [Nil_notin_lex,Nil2_notin_lex];

Goal "((x#xs,y#ys) : lex r) = \
\     ((x,y) : r & length xs = length ys | x=y & (xs,ys) : lex r)";
by (simp_tac (simpset() addsimps [lex_conv]) 1);
by (rtac iffI 1);
 by (blast_tac (claset() addIs [Cons_eq_appendI]) 2);
by (Clarify_tac 1);
by (case_tac "xys" 1);
by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
by (Blast_tac 1);
qed "Cons_in_lex";
AddIffs [Cons_in_lex];


(*** sublist (a generalization of nth to sets) ***)

Goalw [sublist_def] "sublist l {} = []";
by Auto_tac;
qed "sublist_empty";

Goalw [sublist_def] "sublist [] A = []";
by Auto_tac;
qed "sublist_nil";

Goal "map fst [p:zip xs [i..i + length xs(] . snd p : A] =     \
\     map fst [p:zip xs [0..length xs(] . snd p + i : A]";
by (rev_induct_tac "xs" 1);
 by (asm_simp_tac (simpset() addsimps [add_commute]) 2);
by (Simp_tac 1);
qed "sublist_shift_lemma";

Goalw [sublist_def]
     "sublist (l@l') A = sublist l A @ sublist l' {j. j + length l : A}";
by (rev_induct_tac "l'" 1);
by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [inst "i" "0" upt_add_eq_append, 
	                              zip_append, sublist_shift_lemma]) 1);
by (asm_simp_tac (simpset() addsimps [add_commute]) 1);
qed "sublist_append";

Addsimps [sublist_empty, sublist_nil];

Goal "sublist (x#l) A = (if 0:A then [x] else []) @ sublist l {j. Suc j : A}";
by (rev_induct_tac "l" 1);
 by (asm_simp_tac (simpset() delsimps [append_Cons]
	 		     addsimps [append_Cons RS sym, sublist_append]) 2);
by (simp_tac (simpset() addsimps [sublist_def]) 1);
qed "sublist_Cons";

Goal "sublist [x] A = (if 0 : A then [x] else [])";
by (simp_tac (simpset() addsimps [sublist_Cons]) 1);
qed "sublist_singleton";
Addsimps [sublist_singleton];

Goal "sublist l {..n(} = take n l";
by (rev_induct_tac "l" 1);
 by (asm_simp_tac (simpset() addsplits [nat_diff_split]
                             addsimps [sublist_append]) 2);
by (Simp_tac 1);
qed "sublist_upt_eq_take";
Addsimps [sublist_upt_eq_take];


(*** Versions of some theorems above using binary numerals ***)

AddIffs (map rename_numerals
	  [length_0_conv, length_greater_0_conv, sum_eq_0_conv]);

Goal "take n (x#xs) = (if n = #0 then [] else x # take (n-#1) xs)";
by (case_tac "n" 1);
by (ALLGOALS 
    (asm_simp_tac (simpset() addsimps [numeral_0_eq_0, numeral_1_eq_1])));
qed "take_Cons'";

Goal "drop n (x#xs) = (if n = #0 then x#xs else drop (n-#1) xs)";
by (case_tac "n" 1);
by (ALLGOALS
    (asm_simp_tac (simpset() addsimps [numeral_0_eq_0, numeral_1_eq_1])));
qed "drop_Cons'";

Goal "(x#xs)!n = (if n = #0 then x else xs!(n-#1))";
by (case_tac "n" 1);
by (ALLGOALS
    (asm_simp_tac (simpset() addsimps [numeral_0_eq_0, numeral_1_eq_1])));
qed "nth_Cons'";

Addsimps (map (inst "n" "number_of ?v") [take_Cons', drop_Cons', nth_Cons']);

