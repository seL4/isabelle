(*  Title:      HOL/List
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

List lemmas
*)

Goal "!x. xs ~= x#xs";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "not_Cons_self";
bind_thm("not_Cons_self2",not_Cons_self RS not_sym);
Addsimps [not_Cons_self,not_Cons_self2];

Goal "(xs ~= []) = (? y ys. xs = y#ys)";
by (induct_tac "xs" 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "neq_Nil_conv";

(* Induction over the length of a list: *)
val [prem] = Goal
  "(!!xs. (!ys. length ys < length xs --> P ys) ==> P xs) ==> P(xs)";
by(rtac measure_induct 1 THEN etac prem 1);
qed "length_induct";


(** "lists": the list-forming operator over sets **)

Goalw lists.defs "!!A B. A<=B ==> lists A <= lists B";
by (rtac lfp_mono 1);
by (REPEAT (ares_tac basic_monos 1));
qed "lists_mono";

val listsE = lists.mk_cases list.simps  "x#l : lists A";
AddSEs [listsE];
AddSIs lists.intrs;

Goal "!!l. l: lists A ==> l: lists B --> l: lists (A Int B)";
by (etac lists.induct 1);
by (ALLGOALS Blast_tac);
qed_spec_mp "lists_IntI";

Goal "lists (A Int B) = lists A Int lists B";
by (rtac (mono_Int RS equalityI) 1);
by (simp_tac (simpset() addsimps [mono_def, lists_mono]) 1);
by (blast_tac (claset() addSIs [lists_IntI]) 1);
qed "lists_Int_eq";
Addsimps [lists_Int_eq];


(**  Case analysis **)
section "Case analysis";

val prems = Goal "[| P([]); !!x xs. P(x#xs) |] ==> P(xs)";
by (induct_tac "xs" 1);
by (REPEAT(resolve_tac prems 1));
qed "list_cases";

Goal "(xs=[] --> P([])) & (!y ys. xs=y#ys --> P(y#ys)) --> P(xs)";
by (induct_tac "xs" 1);
by (Blast_tac 1);
by (Blast_tac 1);
bind_thm("list_eq_cases",
  impI RSN (2,allI RSN (2,allI RSN (2,impI RS (conjI RS (result() RS mp))))));

(** length **)
(* needs to come before "@" because of thm append_eq_append_conv *)

section "length";

Goal "length(xs@ys) = length(xs)+length(ys)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed"length_append";
Addsimps [length_append];

Goal "length (map f l) = length l";
by (induct_tac "l" 1);
by (ALLGOALS Simp_tac);
qed "length_map";
Addsimps [length_map];

Goal "length(rev xs) = length(xs)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "length_rev";
Addsimps [length_rev];

Goal "!!xs. xs ~= [] ==> length(tl xs) = (length xs) - 1";
by (exhaust_tac "xs" 1);
by (ALLGOALS Asm_full_simp_tac);
qed "length_tl";
Addsimps [length_tl];

Goal "(length xs = 0) = (xs = [])";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "length_0_conv";
AddIffs [length_0_conv];

Goal "(0 = length xs) = (xs = [])";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "zero_length_conv";
AddIffs [zero_length_conv];

Goal "(0 < length xs) = (xs ~= [])";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "length_greater_0_conv";
AddIffs [length_greater_0_conv];

(** @ - append **)

section "@ - append";

Goal "(xs@ys)@zs = xs@(ys@zs)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "append_assoc";
Addsimps [append_assoc];

Goal "xs @ [] = xs";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "append_Nil2";
Addsimps [append_Nil2];

Goal "(xs@ys = []) = (xs=[] & ys=[])";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "append_is_Nil_conv";
AddIffs [append_is_Nil_conv];

Goal "([] = xs@ys) = (xs=[] & ys=[])";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
by (Blast_tac 1);
qed "Nil_is_append_conv";
AddIffs [Nil_is_append_conv];

Goal "(xs @ ys = xs) = (ys=[])";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "append_self_conv";

Goal "(xs = xs @ ys) = (ys=[])";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
by (Blast_tac 1);
qed "self_append_conv";
AddIffs [append_self_conv,self_append_conv];

Goal "!ys. length xs = length ys | length us = length vs \
\              --> (xs@us = ys@vs) = (xs=ys & us=vs)";
by (induct_tac "xs" 1);
 by (rtac allI 1);
 by (exhaust_tac "ys" 1);
  by (Asm_simp_tac 1);
 by (fast_tac (claset() addIs [less_add_Suc2] addss simpset()
                      addEs [less_not_refl2 RSN (2,rev_notE)]) 1);
by (rtac allI 1);
by (exhaust_tac "ys" 1);
 by (fast_tac (claset() addIs [less_add_Suc2] addss simpset()
                      addEs [(less_not_refl2 RS not_sym) RSN (2,rev_notE)]) 1);
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

AddSIs
 [same_append_eq RS iffD2, append1_eq_conv RS iffD2, append_same_eq RS iffD2];
AddSDs
 [same_append_eq RS iffD1, append1_eq_conv RS iffD1, append_same_eq RS iffD1];

Goal "(xs @ ys = ys) = (xs=[])";
by(cut_inst_tac [("zs","[]")] append_same_eq 1);
by(Asm_full_simp_tac 1);
qed "append_self_conv2";

Goal "(ys = xs @ ys) = (xs=[])";
by(simp_tac (simpset() addsimps
     [simplify (simpset()) (read_instantiate[("ys","[]")]append_same_eq)]) 1);
by(Blast_tac 1);
qed "self_append_conv2";
AddIffs [append_self_conv2,self_append_conv2];

Goal "xs ~= [] --> hd xs # tl xs = xs";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "hd_Cons_tl";
Addsimps [hd_Cons_tl];

Goal "hd(xs@ys) = (if xs=[] then hd ys else hd xs)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "hd_append";

Goal "!!xs. xs ~= [] ==> hd(xs @ ys) = hd xs";
by (asm_simp_tac (simpset() addsimps [hd_append]
                           addsplits [split_list_case]) 1);
qed "hd_append2";
Addsimps [hd_append2];

Goal "tl(xs@ys) = (case xs of [] => tl(ys) | z#zs => zs@ys)";
by (simp_tac (simpset() addsplits [split_list_case]) 1);
qed "tl_append";

Goal "!!xs. xs ~= [] ==> tl(xs @ ys) = (tl xs) @ ys";
by (asm_simp_tac (simpset() addsimps [tl_append]
                           addsplits [split_list_case]) 1);
qed "tl_append2";
Addsimps [tl_append2];


(** map **)

section "map";

Goal
  "(!x. x : set xs --> f x = g x) --> map f xs = map g xs";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
bind_thm("map_ext", impI RS (allI RS (result() RS mp)));

Goal "map (%x. x) = (%xs. xs)";
by (rtac ext 1);
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "map_ident";
Addsimps[map_ident];

Goal "map f (xs@ys) = map f xs @ map f ys";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "map_append";
Addsimps[map_append];

Goalw [o_def] "map (f o g) xs = map f (map g xs)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "map_compose";
Addsimps[map_compose];

Goal "rev(map f xs) = map f (rev xs)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "rev_map";

(* a congruence rule for map: *)
Goal
 "(xs=ys) --> (!x. x : set ys --> f x = g x) --> map f xs = map g ys";
by (rtac impI 1);
by (hyp_subst_tac 1);
by (induct_tac "ys" 1);
by (ALLGOALS Asm_simp_tac);
val lemma = result();
bind_thm("map_cong",impI RSN (2,allI RSN (2,lemma RS mp RS mp)));

Goal "(map f xs = []) = (xs = [])";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "map_is_Nil_conv";
AddIffs [map_is_Nil_conv];

Goal "([] = map f xs) = (xs = [])";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "Nil_is_map_conv";
AddIffs [Nil_is_map_conv];


(** rev **)

section "rev";

Goal "rev(xs@ys) = rev(ys) @ rev(xs)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "rev_append";
Addsimps[rev_append];

Goal "rev(rev l) = l";
by (induct_tac "l" 1);
by (ALLGOALS Asm_simp_tac);
qed "rev_rev_ident";
Addsimps[rev_rev_ident];

Goal "(rev xs = []) = (xs = [])";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "rev_is_Nil_conv";
AddIffs [rev_is_Nil_conv];

Goal "([] = rev xs) = (xs = [])";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "Nil_is_rev_conv";
AddIffs [Nil_is_rev_conv];

val prems = Goal "[| P []; !!x xs. P xs ==> P(xs@[x]) |] ==> P xs";
by(stac (rev_rev_ident RS sym) 1);
br(read_instantiate [("P","%xs. ?P(rev xs)")]list.induct)1;
by(ALLGOALS Simp_tac);
brs prems 1;
bes prems 1;
qed "rev_induct";

Goal  "(xs = [] --> P) -->  (!ys y. xs = ys@[y] --> P) --> P";
by(res_inst_tac [("xs","xs")] rev_induct 1);
by(ALLGOALS Asm_simp_tac);
bind_thm ("rev_exhaust",
  impI RSN (2,allI RSN (2,allI RSN (2,impI RS (result() RS mp RS mp)))));


(** mem **)

section "mem";

Goal "x mem (xs@ys) = (x mem xs | x mem ys)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "mem_append";
Addsimps[mem_append];

Goal "x mem [x:xs. P(x)] = (x mem xs & P(x))";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "mem_filter";
Addsimps[mem_filter];

(** set **)

section "set";

Goal "set (xs@ys) = (set xs Un set ys)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "set_append";
Addsimps[set_append];

Goal "(x mem xs) = (x: set xs)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
by (Blast_tac 1);
qed "set_mem_eq";

Goal "set l <= set (x#l)";
by (Simp_tac 1);
by (Blast_tac 1);
qed "set_subset_Cons";

Goal "(set xs = {}) = (xs = [])";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "set_empty";
Addsimps [set_empty];

Goal "set(rev xs) = set(xs)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "set_rev";
Addsimps [set_rev];

Goal "set(map f xs) = f``(set xs)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "set_map";
Addsimps [set_map];

Goal "set(map f xs) = f``(set xs)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "set_map";
Addsimps [set_map];

Goal "(x : set(filter P xs)) = (x : set xs & P x)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
by(Blast_tac 1);
qed "in_set_filter";
Addsimps [in_set_filter];


(** list_all **)

section "list_all";

Goal "list_all (%x. True) xs = True";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "list_all_True";
Addsimps [list_all_True];

Goal "list_all p (xs@ys) = (list_all p xs & list_all p ys)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "list_all_append";
Addsimps [list_all_append];

Goal "list_all P xs = (!x. x mem xs --> P(x))";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
by (Blast_tac 1);
qed "list_all_mem_conv";


(** filter **)

section "filter";

Goal "filter P (xs@ys) = filter P xs @ filter P ys";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "filter_append";
Addsimps [filter_append];

Goal "filter (%x. True) xs = xs";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "filter_True";
Addsimps [filter_True];

Goal "filter (%x. False) xs = []";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "filter_False";
Addsimps [filter_False];

Goal "length (filter P xs) <= length xs";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "length_filter";


(** concat **)

section "concat";

Goal  "concat(xs@ys) = concat(xs)@concat(ys)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed"concat_append";
Addsimps [concat_append];

Goal "(concat xss = []) = (!xs:set xss. xs=[])";
by (induct_tac "xss" 1);
by (ALLGOALS Asm_simp_tac);
qed "concat_eq_Nil_conv";
AddIffs [concat_eq_Nil_conv];

Goal "([] = concat xss) = (!xs:set xss. xs=[])";
by (induct_tac "xss" 1);
by (ALLGOALS Asm_simp_tac);
qed "Nil_eq_concat_conv";
AddIffs [Nil_eq_concat_conv];

Goal  "set(concat xs) = Union(set `` set xs)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed"set_concat";
Addsimps [set_concat];

Goal "map f (concat xs) = concat (map (map f) xs)"; 
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "map_concat";

Goal "filter p (concat xs) = concat (map (filter p) xs)"; 
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed"filter_concat"; 

Goal "rev(concat xs) = concat (map rev (rev xs))";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "rev_concat";

(** nth **)

section "nth";

Goal
  "!xs. (xs@ys)!n = (if n < length xs then xs!n else ys!(n - length xs))";
by (nat_ind_tac "n" 1);
 by (Asm_simp_tac 1);
 by (rtac allI 1);
 by (exhaust_tac "xs" 1);
  by (ALLGOALS Asm_simp_tac);
qed_spec_mp "nth_append";

Goal "!n. n < length xs --> (map f xs)!n = f(xs!n)";
by (induct_tac "xs" 1);
(* case [] *)
by (Asm_full_simp_tac 1);
(* case x#xl *)
by (rtac allI 1);
by (nat_ind_tac "n" 1);
by (ALLGOALS Asm_full_simp_tac);
qed_spec_mp "nth_map";
Addsimps [nth_map];

Goal "!n. n < length xs --> list_all P xs --> P(xs!n)";
by (induct_tac "xs" 1);
(* case [] *)
by (Simp_tac 1);
(* case x#xl *)
by (rtac allI 1);
by (nat_ind_tac "n" 1);
by (ALLGOALS Asm_full_simp_tac);
qed_spec_mp "list_all_nth";

Goal "!n. n < length xs --> xs!n mem xs";
by (induct_tac "xs" 1);
(* case [] *)
by (Simp_tac 1);
(* case x#xl *)
by (rtac allI 1);
by (nat_ind_tac "n" 1);
(* case 0 *)
by (Asm_full_simp_tac 1);
(* case Suc x *)
by (Asm_full_simp_tac 1);
qed_spec_mp "nth_mem";
Addsimps [nth_mem];

(** last & butlast **)

Goal "last(xs@[x]) = x";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "last_snoc";
Addsimps [last_snoc];

Goal "butlast(xs@[x]) = xs";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "butlast_snoc";
Addsimps [butlast_snoc];

Goal "length(butlast xs) = length xs - 1";
by (res_inst_tac [("xs","xs")] rev_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "length_butlast";
Addsimps [length_butlast];

Goal
  "!ys. butlast (xs@ys) = (if ys=[] then butlast xs else xs@butlast ys)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "butlast_append";

Goal "x:set(butlast xs) --> x:set xs";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "in_set_butlastD";

Goal "!!xs. x:set(butlast xs) ==> x:set(butlast(xs@ys))";
by (asm_simp_tac (simpset() addsimps [butlast_append]) 1);
by (blast_tac (claset() addDs [in_set_butlastD]) 1);
qed "in_set_butlast_appendI1";

Goal "!!xs. x:set(butlast ys) ==> x:set(butlast(xs@ys))";
by (asm_simp_tac (simpset() addsimps [butlast_append]) 1);
by (Clarify_tac 1);
by (Full_simp_tac 1);
qed "in_set_butlast_appendI2";

(** take  & drop **)
section "take & drop";

Goal "take 0 xs = []";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "take_0";

Goal "drop 0 xs = xs";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
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
by (nat_ind_tac "n" 1);
 by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (exhaust_tac "xs" 1);
 by (ALLGOALS Asm_simp_tac);
qed_spec_mp "length_take";
Addsimps [length_take];

Goal "!xs. length(drop n xs) = (length xs - n)";
by (nat_ind_tac "n" 1);
 by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (exhaust_tac "xs" 1);
 by (ALLGOALS Asm_simp_tac);
qed_spec_mp "length_drop";
Addsimps [length_drop];

Goal "!xs. length xs <= n --> take n xs = xs";
by (nat_ind_tac "n" 1);
 by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (exhaust_tac "xs" 1);
 by (ALLGOALS Asm_simp_tac);
qed_spec_mp "take_all";

Goal "!xs. length xs <= n --> drop n xs = []";
by (nat_ind_tac "n" 1);
 by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (exhaust_tac "xs" 1);
 by (ALLGOALS Asm_simp_tac);
qed_spec_mp "drop_all";

Goal 
  "!xs. take n (xs @ ys) = (take n xs @ take (n - length xs) ys)";
by (nat_ind_tac "n" 1);
 by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (exhaust_tac "xs" 1);
 by (ALLGOALS Asm_simp_tac);
qed_spec_mp "take_append";
Addsimps [take_append];

Goal "!xs. drop n (xs@ys) = drop n xs @ drop (n - length xs) ys"; 
by (nat_ind_tac "n" 1);
 by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (exhaust_tac "xs" 1);
 by (ALLGOALS Asm_simp_tac);
qed_spec_mp "drop_append";
Addsimps [drop_append];

Goal "!xs n. take n (take m xs) = take (min n m) xs"; 
by (nat_ind_tac "m" 1);
 by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (exhaust_tac "xs" 1);
 by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (exhaust_tac "n" 1);
 by (ALLGOALS Asm_simp_tac);
qed_spec_mp "take_take";

Goal "!xs. drop n (drop m xs) = drop (n + m) xs"; 
by (nat_ind_tac "m" 1);
 by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (exhaust_tac "xs" 1);
 by (ALLGOALS Asm_simp_tac);
qed_spec_mp "drop_drop";

Goal "!xs n. take n (drop m xs) = drop m (take (n + m) xs)"; 
by (nat_ind_tac "m" 1);
 by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (exhaust_tac "xs" 1);
 by (ALLGOALS Asm_simp_tac);
qed_spec_mp "take_drop";

Goal "!xs. take n (map f xs) = map f (take n xs)"; 
by (nat_ind_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (exhaust_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "take_map"; 

Goal "!xs. drop n (map f xs) = map f (drop n xs)"; 
by (nat_ind_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (exhaust_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "drop_map";

Goal "!n i. i < n --> (take n xs)!i = xs!i";
by (induct_tac "xs" 1);
 by (ALLGOALS Asm_simp_tac);
by (Clarify_tac 1);
by (exhaust_tac "n" 1);
 by (Blast_tac 1);
by (exhaust_tac "i" 1);
by (ALLGOALS Asm_full_simp_tac);
qed_spec_mp "nth_take";
Addsimps [nth_take];

Goal  "!xs i. n + i <= length xs --> (drop n xs)!i = xs!(n+i)";
by (nat_ind_tac "n" 1);
 by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (exhaust_tac "xs" 1);
 by (ALLGOALS Asm_simp_tac);
qed_spec_mp "nth_drop";
Addsimps [nth_drop];

(** takeWhile & dropWhile **)

section "takeWhile & dropWhile";

Goal "takeWhile P xs @ dropWhile P xs = xs";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_full_simp_tac);
qed "takeWhile_dropWhile_id";
Addsimps [takeWhile_dropWhile_id];

Goal  "x:set xs & ~P(x) --> takeWhile P (xs @ ys) = takeWhile P xs";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_full_simp_tac);
by (Blast_tac 1);
bind_thm("takeWhile_append1", conjI RS (result() RS mp));
Addsimps [takeWhile_append1];

Goal "(!x:set xs. P(x)) --> takeWhile P (xs @ ys) = xs @ takeWhile P ys";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_full_simp_tac);
bind_thm("takeWhile_append2", ballI RS (result() RS mp));
Addsimps [takeWhile_append2];

Goal "x:set xs & ~P(x) --> dropWhile P (xs @ ys) = (dropWhile P xs)@ys";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_full_simp_tac);
by (Blast_tac 1);
bind_thm("dropWhile_append1", conjI RS (result() RS mp));
Addsimps [dropWhile_append1];

Goal "(!x:set xs. P(x)) --> dropWhile P (xs @ ys) = dropWhile P ys";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_full_simp_tac);
bind_thm("dropWhile_append2", ballI RS (result() RS mp));
Addsimps [dropWhile_append2];

Goal "x:set(takeWhile P xs) --> x:set xs & P x";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_full_simp_tac);
qed_spec_mp"set_take_whileD";

qed_goal "zip_Nil_Nil"   thy "zip []     []     = []" (K [Simp_tac 1]);
qed_goal "zip_Cons_Cons" thy "zip (x#xs) (y#ys) = (x,y)#zip xs ys" 
						      (K [Simp_tac 1]);

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
by (ALLGOALS Asm_full_simp_tac);
qed "nodups_remdups";

Goal "nodups xs --> nodups (filter P xs)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_full_simp_tac);
qed_spec_mp "nodups_filter";

(** replicate **)
section "replicate";

Goal "set(replicate (Suc n) x) = {x}";
by (induct_tac "n" 1);
by (ALLGOALS Asm_full_simp_tac);
val lemma = result();

Goal "!!n. n ~= 0 ==> set(replicate n x) = {x}";
by (fast_tac (claset() addSDs [not0_implies_Suc] addSIs [lemma]) 1);
qed "set_replicate";
Addsimps [set_replicate];
