(*  Title:      HOL/List
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

List lemmas
*)

goal thy "!x. xs ~= x#xs";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "not_Cons_self";
bind_thm("not_Cons_self2",not_Cons_self RS not_sym);
Addsimps [not_Cons_self,not_Cons_self2];

goal thy "(xs ~= []) = (? y ys. xs = y#ys)";
by (induct_tac "xs" 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "neq_Nil_conv";


(** "lists": the list-forming operator over sets **)

goalw thy lists.defs "!!A B. A<=B ==> lists A <= lists B";
by (rtac lfp_mono 1);
by (REPEAT (ares_tac basic_monos 1));
qed "lists_mono";

val listsE = lists.mk_cases list.simps  "x#l : lists A";
AddSEs [listsE];
AddSIs lists.intrs;

goal thy "!!l. l: lists A ==> l: lists B --> l: lists (A Int B)";
by (etac lists.induct 1);
by (ALLGOALS Blast_tac);
qed_spec_mp "lists_IntI";

goal thy "lists (A Int B) = lists A Int lists B";
by (rtac (mono_Int RS equalityI) 1);
by (simp_tac (simpset() addsimps [mono_def, lists_mono]) 1);
by (blast_tac (claset() addSIs [lists_IntI]) 1);
qed "lists_Int_eq";
Addsimps [lists_Int_eq];


(**  Case analysis **)
section "Case analysis";

val prems = goal thy "[| P([]); !!x xs. P(x#xs) |] ==> P(xs)";
by (induct_tac "xs" 1);
by (REPEAT(resolve_tac prems 1));
qed "list_cases";

goal thy  "(xs=[] --> P([])) & (!y ys. xs=y#ys --> P(y#ys)) --> P(xs)";
by (induct_tac "xs" 1);
by (Blast_tac 1);
by (Blast_tac 1);
bind_thm("list_eq_cases",
  impI RSN (2,allI RSN (2,allI RSN (2,impI RS (conjI RS (result() RS mp))))));

(** length **)
(* needs to come before "@" because of thm append_eq_append_conv *)

section "length";

goal thy "length(xs@ys) = length(xs)+length(ys)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed"length_append";
Addsimps [length_append];

goal thy "length (map f l) = length l";
by (induct_tac "l" 1);
by (ALLGOALS Simp_tac);
qed "length_map";
Addsimps [length_map];

goal thy "length(rev xs) = length(xs)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "length_rev";
Addsimps [length_rev];

goal List.thy "!!xs. xs ~= [] ==> length(tl xs) = (length xs) - 1";
by (exhaust_tac "xs" 1);
by (ALLGOALS Asm_full_simp_tac);
qed "length_tl";
Addsimps [length_tl];

goal thy "(length xs = 0) = (xs = [])";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "length_0_conv";
AddIffs [length_0_conv];

goal thy "(0 = length xs) = (xs = [])";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "zero_length_conv";
AddIffs [zero_length_conv];

goal thy "(0 < length xs) = (xs ~= [])";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "length_greater_0_conv";
AddIffs [length_greater_0_conv];

(** @ - append **)

section "@ - append";

goal thy "(xs@ys)@zs = xs@(ys@zs)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "append_assoc";
Addsimps [append_assoc];

goal thy "xs @ [] = xs";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "append_Nil2";
Addsimps [append_Nil2];

goal thy "(xs@ys = []) = (xs=[] & ys=[])";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "append_is_Nil_conv";
AddIffs [append_is_Nil_conv];

goal thy "([] = xs@ys) = (xs=[] & ys=[])";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
by (Blast_tac 1);
qed "Nil_is_append_conv";
AddIffs [Nil_is_append_conv];

goal thy "(xs @ ys = xs) = (ys=[])";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "append_self_conv";

goal thy "(xs = xs @ ys) = (ys=[])";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
by (Blast_tac 1);
qed "self_append_conv";
AddIffs [append_self_conv,self_append_conv];

goal thy "!ys. length xs = length ys | length us = length vs \
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

goal thy "(xs @ ys = xs @ zs) = (ys=zs)";
by (Simp_tac 1);
qed "same_append_eq";

goal thy "(xs @ [x] = ys @ [y]) = (xs = ys & x = y)"; 
by (Simp_tac 1);
qed "append1_eq_conv";

goal thy "(ys @ xs = zs @ xs) = (ys=zs)";
by (Simp_tac 1);
qed "append_same_eq";

AddSIs
 [same_append_eq RS iffD2, append1_eq_conv RS iffD2, append_same_eq RS iffD2];
AddSDs
 [same_append_eq RS iffD1, append1_eq_conv RS iffD1, append_same_eq RS iffD1];

goal thy "(xs @ ys = ys) = (xs=[])";
by(cut_inst_tac [("zs","[]")] append_same_eq 1);
by(Asm_full_simp_tac 1);
qed "append_self_conv2";

goal thy "(ys = xs @ ys) = (xs=[])";
by(simp_tac (simpset() addsimps
     [simplify (simpset()) (read_instantiate[("ys","[]")]append_same_eq)]) 1);
by(Blast_tac 1);
qed "self_append_conv2";
AddIffs [append_self_conv2,self_append_conv2];

goal thy "xs ~= [] --> hd xs # tl xs = xs";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "hd_Cons_tl";
Addsimps [hd_Cons_tl];

goal thy "hd(xs@ys) = (if xs=[] then hd ys else hd xs)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "hd_append";

goal thy "!!xs. xs ~= [] ==> hd(xs @ ys) = hd xs";
by (asm_simp_tac (simpset() addsimps [hd_append]
                           addsplits [split_list_case]) 1);
qed "hd_append2";
Addsimps [hd_append2];

goal thy "tl(xs@ys) = (case xs of [] => tl(ys) | z#zs => zs@ys)";
by (simp_tac (simpset() addsplits [split_list_case]) 1);
qed "tl_append";

goal thy "!!xs. xs ~= [] ==> tl(xs @ ys) = (tl xs) @ ys";
by (asm_simp_tac (simpset() addsimps [tl_append]
                           addsplits [split_list_case]) 1);
qed "tl_append2";
Addsimps [tl_append2];

(** map **)

section "map";

goal thy
  "(!x. x : set xs --> f x = g x) --> map f xs = map g xs";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
bind_thm("map_ext", impI RS (allI RS (result() RS mp)));

goal thy "map (%x. x) = (%xs. xs)";
by (rtac ext 1);
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "map_ident";
Addsimps[map_ident];

goal thy "map f (xs@ys) = map f xs @ map f ys";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "map_append";
Addsimps[map_append];

goalw thy [o_def] "map (f o g) xs = map f (map g xs)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "map_compose";
Addsimps[map_compose];

goal thy "rev(map f xs) = map f (rev xs)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "rev_map";

(* a congruence rule for map: *)
goal thy
 "(xs=ys) --> (!x. x : set ys --> f x = g x) --> map f xs = map g ys";
by (rtac impI 1);
by (hyp_subst_tac 1);
by (induct_tac "ys" 1);
by (ALLGOALS Asm_simp_tac);
val lemma = result();
bind_thm("map_cong",impI RSN (2,allI RSN (2,lemma RS mp RS mp)));

goal List.thy "(map f xs = []) = (xs = [])";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "map_is_Nil_conv";
AddIffs [map_is_Nil_conv];

goal List.thy "([] = map f xs) = (xs = [])";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "Nil_is_map_conv";
AddIffs [Nil_is_map_conv];


(** rev **)

section "rev";

goal thy "rev(xs@ys) = rev(ys) @ rev(xs)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "rev_append";
Addsimps[rev_append];

goal thy "rev(rev l) = l";
by (induct_tac "l" 1);
by (ALLGOALS Asm_simp_tac);
qed "rev_rev_ident";
Addsimps[rev_rev_ident];

goal thy "(rev xs = []) = (xs = [])";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "rev_is_Nil_conv";
AddIffs [rev_is_Nil_conv];

goal thy "([] = rev xs) = (xs = [])";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "Nil_is_rev_conv";
AddIffs [Nil_is_rev_conv];


(** mem **)

section "mem";

goal thy "x mem (xs@ys) = (x mem xs | x mem ys)";
by (induct_tac "xs" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsplits [expand_if])));
qed "mem_append";
Addsimps[mem_append];

goal thy "x mem [x:xs. P(x)] = (x mem xs & P(x))";
by (induct_tac "xs" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsplits [expand_if])));
qed "mem_filter";
Addsimps[mem_filter];

(** set **)

section "set";

goal thy "set (xs@ys) = (set xs Un set ys)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "set_append";
Addsimps[set_append];

goal thy "(x mem xs) = (x: set xs)";
by (induct_tac "xs" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsplits [expand_if])));
by (Blast_tac 1);
qed "set_mem_eq";

goal thy "set l <= set (x#l)";
by (Simp_tac 1);
by (Blast_tac 1);
qed "set_subset_Cons";

goal thy "(set xs = {}) = (xs = [])";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "set_empty";
Addsimps [set_empty];

goal thy "set(rev xs) = set(xs)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "set_rev";
Addsimps [set_rev];

goal thy "set(map f xs) = f``(set xs)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "set_map";
Addsimps [set_map];

goal thy "set(map f xs) = f``(set xs)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "set_map";
Addsimps [set_map];

goal thy "(x : set(filter P xs)) = (x : set xs & P x)";
by (induct_tac "xs" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsplits [expand_if])));
by(Blast_tac 1);
qed "in_set_filter";
Addsimps [in_set_filter];


(** list_all **)

section "list_all";

goal thy "list_all (%x. True) xs = True";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "list_all_True";
Addsimps [list_all_True];

goal thy "list_all p (xs@ys) = (list_all p xs & list_all p ys)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "list_all_append";
Addsimps [list_all_append];

goal thy "list_all P xs = (!x. x mem xs --> P(x))";
by (induct_tac "xs" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsplits [expand_if])));
by (Blast_tac 1);
qed "list_all_mem_conv";


(** filter **)

section "filter";

goal thy "filter P (xs@ys) = filter P xs @ filter P ys";
by (induct_tac "xs" 1);
 by (ALLGOALS (asm_simp_tac (simpset() addsplits [expand_if])));
qed "filter_append";
Addsimps [filter_append];

goal thy "filter (%x. True) xs = xs";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "filter_True";
Addsimps [filter_True];

goal thy "filter (%x. False) xs = []";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "filter_False";
Addsimps [filter_False];

goal thy "length (filter P xs) <= length xs";
by (induct_tac "xs" 1);
 by (ALLGOALS (asm_simp_tac (simpset() addsplits [expand_if])));
qed "length_filter";


(** concat **)

section "concat";

goal thy  "concat(xs@ys) = concat(xs)@concat(ys)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed"concat_append";
Addsimps [concat_append];

goal thy "(concat xss = []) = (!xs:set xss. xs=[])";
by (induct_tac "xss" 1);
by (ALLGOALS Asm_simp_tac);
qed "concat_eq_Nil_conv";
AddIffs [concat_eq_Nil_conv];

goal thy "([] = concat xss) = (!xs:set xss. xs=[])";
by (induct_tac "xss" 1);
by (ALLGOALS Asm_simp_tac);
qed "Nil_eq_concat_conv";
AddIffs [Nil_eq_concat_conv];

goal thy  "set(concat xs) = Union(set `` set xs)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed"set_concat";
Addsimps [set_concat];

goal thy "map f (concat xs) = concat (map (map f) xs)"; 
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "map_concat";

goal thy "filter p (concat xs) = concat (map (filter p) xs)"; 
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed"filter_concat"; 

goal thy "rev(concat xs) = concat (map rev (rev xs))";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "rev_concat";

(** nth **)

section "nth";

goal thy
  "!xs. (xs@ys)!n = (if n < length xs then xs!n else ys!(n - length xs))";
by (nat_ind_tac "n" 1);
 by (Asm_simp_tac 1);
 by (rtac allI 1);
 by (exhaust_tac "xs" 1);
  by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (exhaust_tac "xs" 1);
 by (ALLGOALS Asm_simp_tac);
qed_spec_mp "nth_append";

goal thy "!n. n < length xs --> (map f xs)!n = f(xs!n)";
by (induct_tac "xs" 1);
(* case [] *)
by (Asm_full_simp_tac 1);
(* case x#xl *)
by (rtac allI 1);
by (nat_ind_tac "n" 1);
by (ALLGOALS Asm_full_simp_tac);
qed_spec_mp "nth_map";
Addsimps [nth_map];

goal thy "!n. n < length xs --> list_all P xs --> P(xs!n)";
by (induct_tac "xs" 1);
(* case [] *)
by (Simp_tac 1);
(* case x#xl *)
by (rtac allI 1);
by (nat_ind_tac "n" 1);
by (ALLGOALS Asm_full_simp_tac);
qed_spec_mp "list_all_nth";

goal thy "!n. n < length xs --> xs!n mem xs";
by (induct_tac "xs" 1);
(* case [] *)
by (Simp_tac 1);
(* case x#xl *)
by (rtac allI 1);
by (nat_ind_tac "n" 1);
(* case 0 *)
by (Asm_full_simp_tac 1);
(* case Suc x *)
by (asm_full_simp_tac (simpset() addsplits [expand_if]) 1);
qed_spec_mp "nth_mem";
Addsimps [nth_mem];

(**  More case analysis and induction **)
section "More case analysis and induction";

val [prem] = goal thy
  "(!!xs. (!ys. length ys < length xs --> P ys) ==> P xs) ==> P(xs)";
by(rtac measure_induct 1 THEN etac prem 1);
qed "length_induct";

goal thy "xs ~= [] --> (? ys y. xs = ys@[y])";
by(res_inst_tac [("xs","xs")] length_induct 1);
by(Clarify_tac 1);
bd (neq_Nil_conv RS iffD1) 1;
by(Clarify_tac 1);
by(rename_tac "ys" 1);
by(case_tac "ys = []" 1);
 by(res_inst_tac [("x","[]")] exI 1);
 by(Asm_full_simp_tac 1);
by(eres_inst_tac [("x","ys")] allE 1);
by(Asm_full_simp_tac 1);
by(REPEAT(etac exE 1));
by(rename_tac "zs z" 1);
by(hyp_subst_tac 1);
by(res_inst_tac [("x","y#zs")] exI 1);
by(Simp_tac 1);
qed_spec_mp "neq_Nil_snocD";

val prems = goal thy
  "[| xs=[] ==> P []; !!ys y. xs=ys@[y] ==> P(ys@[y]) |] ==> P xs";
by(case_tac "xs = []" 1);
 by(Asm_simp_tac 1);
 bes prems 1;
bd neq_Nil_snocD 1;
by(REPEAT(etac exE 1));
by(Asm_simp_tac 1);
bes prems 1;
qed "snoc_eq_cases";

val prems = goal thy
  "[| P []; !!x xs. P xs ==> P(xs@[x]) |] ==> P(xs)";
by(res_inst_tac [("xs","xs")] length_induct 1);
by(res_inst_tac [("xs","xs")] snoc_eq_cases 1);
 brs prems 1;
by(fast_tac (claset() addIs prems addss simpset()) 1);
qed "snoc_induct";

(** last & butlast **)

goal thy "last(xs@[x]) = x";
by (induct_tac "xs" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsplits [expand_if])));
qed "last_snoc";
Addsimps [last_snoc];

goal thy "butlast(xs@[x]) = xs";
by (induct_tac "xs" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsplits [expand_if])));
qed "butlast_snoc";
Addsimps [butlast_snoc];

goal thy "length(butlast xs) = length xs - 1";
by(res_inst_tac [("xs","xs")] snoc_induct 1);
by(ALLGOALS Asm_simp_tac);
qed "length_butlast";
Addsimps [length_butlast];

goal thy
  "!ys. butlast (xs@ys) = (if ys=[] then butlast xs else xs@butlast ys)";
by (induct_tac "xs" 1);
by (ALLGOALS(asm_simp_tac (simpset() addsplits [expand_if])));
qed_spec_mp "butlast_append";

goal thy "x:set(butlast xs) --> x:set xs";
by (induct_tac "xs" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsplits [expand_if])));
qed_spec_mp "in_set_butlastD";

goal thy "!!xs. x:set(butlast xs) ==> x:set(butlast(xs@ys))";
by (asm_simp_tac (simpset() addsimps [butlast_append]
                          addsplits [expand_if]) 1);
by (blast_tac (claset() addDs [in_set_butlastD]) 1);
qed "in_set_butlast_appendI1";

goal thy "!!xs. x:set(butlast ys) ==> x:set(butlast(xs@ys))";
by (asm_simp_tac (simpset() addsimps [butlast_append]
                          addsplits [expand_if]) 1);
by (Clarify_tac 1);
by (Full_simp_tac 1);
qed "in_set_butlast_appendI2";

(** take  & drop **)
section "take & drop";

goal thy "take 0 xs = []";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "take_0";

goal thy "drop 0 xs = xs";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "drop_0";

goal thy "take (Suc n) (x#xs) = x # take n xs";
by (Simp_tac 1);
qed "take_Suc_Cons";

goal thy "drop (Suc n) (x#xs) = drop n xs";
by (Simp_tac 1);
qed "drop_Suc_Cons";

Delsimps [take_Cons,drop_Cons];
Addsimps [take_0,take_Suc_Cons,drop_0,drop_Suc_Cons];

goal thy "!xs. length(take n xs) = min (length xs) n";
by (nat_ind_tac "n" 1);
 by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (exhaust_tac "xs" 1);
 by (ALLGOALS Asm_simp_tac);
qed_spec_mp "length_take";
Addsimps [length_take];

goal thy "!xs. length(drop n xs) = (length xs - n)";
by (nat_ind_tac "n" 1);
 by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (exhaust_tac "xs" 1);
 by (ALLGOALS Asm_simp_tac);
qed_spec_mp "length_drop";
Addsimps [length_drop];

goal thy "!xs. length xs <= n --> take n xs = xs";
by (nat_ind_tac "n" 1);
 by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (exhaust_tac "xs" 1);
 by (ALLGOALS Asm_simp_tac);
qed_spec_mp "take_all";

goal thy "!xs. length xs <= n --> drop n xs = []";
by (nat_ind_tac "n" 1);
 by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (exhaust_tac "xs" 1);
 by (ALLGOALS Asm_simp_tac);
qed_spec_mp "drop_all";

goal thy 
  "!xs. take n (xs @ ys) = (take n xs @ take (n - length xs) ys)";
by (nat_ind_tac "n" 1);
 by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (exhaust_tac "xs" 1);
 by (ALLGOALS Asm_simp_tac);
qed_spec_mp "take_append";
Addsimps [take_append];

goal thy "!xs. drop n (xs@ys) = drop n xs @ drop (n - length xs) ys"; 
by (nat_ind_tac "n" 1);
 by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (exhaust_tac "xs" 1);
 by (ALLGOALS Asm_simp_tac);
qed_spec_mp "drop_append";
Addsimps [drop_append];

goal thy "!xs n. take n (take m xs) = take (min n m) xs"; 
by (nat_ind_tac "m" 1);
 by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (exhaust_tac "xs" 1);
 by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (exhaust_tac "n" 1);
 by (ALLGOALS Asm_simp_tac);
qed_spec_mp "take_take";

goal thy "!xs. drop n (drop m xs) = drop (n + m) xs"; 
by (nat_ind_tac "m" 1);
 by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (exhaust_tac "xs" 1);
 by (ALLGOALS Asm_simp_tac);
qed_spec_mp "drop_drop";

goal thy "!xs n. take n (drop m xs) = drop m (take (n + m) xs)"; 
by (nat_ind_tac "m" 1);
 by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (exhaust_tac "xs" 1);
 by (ALLGOALS Asm_simp_tac);
qed_spec_mp "take_drop";

goal thy "!xs. take n (map f xs) = map f (take n xs)"; 
by (nat_ind_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (exhaust_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "take_map"; 

goal thy "!xs. drop n (map f xs) = map f (drop n xs)"; 
by (nat_ind_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (exhaust_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "drop_map";

goal thy "!n i. i < n --> (take n xs)!i = xs!i";
by (induct_tac "xs" 1);
 by (ALLGOALS Asm_simp_tac);
by (Clarify_tac 1);
by (exhaust_tac "n" 1);
 by (Blast_tac 1);
by (exhaust_tac "i" 1);
by (ALLGOALS Asm_full_simp_tac);
qed_spec_mp "nth_take";
Addsimps [nth_take];

goal thy  "!xs i. n + i <= length xs --> (drop n xs)!i = xs!(n+i)";
by (nat_ind_tac "n" 1);
 by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (exhaust_tac "xs" 1);
 by (ALLGOALS Asm_simp_tac);
qed_spec_mp "nth_drop";
Addsimps [nth_drop];

(** takeWhile & dropWhile **)

section "takeWhile & dropWhile";

goal thy "takeWhile P xs @ dropWhile P xs = xs";
by (induct_tac "xs" 1);
 by (Simp_tac 1);
by (asm_full_simp_tac (simpset() addsplits [expand_if]) 1);
qed "takeWhile_dropWhile_id";
Addsimps [takeWhile_dropWhile_id];

goal thy  "x:set xs & ~P(x) --> takeWhile P (xs @ ys) = takeWhile P xs";
by (induct_tac "xs" 1);
 by (Simp_tac 1);
by (asm_full_simp_tac (simpset() addsplits [expand_if]) 1);
by (Blast_tac 1);
bind_thm("takeWhile_append1", conjI RS (result() RS mp));
Addsimps [takeWhile_append1];

goal thy
  "(!x:set xs. P(x)) --> takeWhile P (xs @ ys) = xs @ takeWhile P ys";
by (induct_tac "xs" 1);
 by (Simp_tac 1);
by (asm_full_simp_tac (simpset() addsplits [expand_if]) 1);
bind_thm("takeWhile_append2", ballI RS (result() RS mp));
Addsimps [takeWhile_append2];

goal thy
  "x:set xs & ~P(x) --> dropWhile P (xs @ ys) = (dropWhile P xs)@ys";
by (induct_tac "xs" 1);
 by (Simp_tac 1);
by (asm_full_simp_tac (simpset() addsplits [expand_if]) 1);
by (Blast_tac 1);
bind_thm("dropWhile_append1", conjI RS (result() RS mp));
Addsimps [dropWhile_append1];

goal thy
  "(!x:set xs. P(x)) --> dropWhile P (xs @ ys) = dropWhile P ys";
by (induct_tac "xs" 1);
 by (Simp_tac 1);
by (asm_full_simp_tac (simpset() addsplits [expand_if]) 1);
bind_thm("dropWhile_append2", ballI RS (result() RS mp));
Addsimps [dropWhile_append2];

goal thy "x:set(takeWhile P xs) --> x:set xs & P x";
by (induct_tac "xs" 1);
 by (Simp_tac 1);
by (asm_full_simp_tac (simpset() addsplits [expand_if]) 1);
qed_spec_mp"set_take_whileD";

qed_goal "zip_Nil_Nil"   thy "zip []     []     = []" (K [Simp_tac 1]);
qed_goal "zip_Cons_Cons" thy "zip (x#xs) (y#ys) = (x,y)#zip xs ys" 
						      (K [Simp_tac 1]);

(** nodups & remdups **)
section "nodups & remdups";

goal thy "set(remdups xs) = set xs";
by (induct_tac "xs" 1);
 by (Simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [insert_absorb]
                                 addsplits [expand_if]) 1);
qed "set_remdups";
Addsimps [set_remdups];

goal thy "nodups(remdups xs)";
by (induct_tac "xs" 1);
 by (Simp_tac 1);
by (asm_full_simp_tac (simpset() addsplits [expand_if]) 1);
qed "nodups_remdups";

goal thy "nodups xs --> nodups (filter P xs)";
by (induct_tac "xs" 1);
 by (Simp_tac 1);
by (asm_full_simp_tac (simpset() addsplits [expand_if]) 1);
qed_spec_mp "nodups_filter";

(** replicate **)
section "replicate";

goal thy "set(replicate (Suc n) x) = {x}";
by (induct_tac "n" 1);
by (ALLGOALS Asm_full_simp_tac);
val lemma = result();

goal thy "!!n. n ~= 0 ==> set(replicate n x) = {x}";
by (fast_tac (claset() addSDs [not0_implies_Suc] addSIs [lemma]) 1);
qed "set_replicate";
Addsimps [set_replicate];
