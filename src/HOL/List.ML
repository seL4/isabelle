(*  Title:      HOL/List
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

List lemmas
*)

open List;

AddIffs list.distinct;
AddIffs list.inject;

bind_thm("Cons_inject", (hd list.inject) RS iffD1 RS conjE);

goal List.thy "!x. xs ~= x#xs";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "not_Cons_self";
Addsimps [not_Cons_self];

goal List.thy "(xs ~= []) = (? y ys. xs = y#ys)";
by (list.induct_tac "xs" 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "neq_Nil_conv";


(** list_case **)

goal List.thy
 "P(list_case a f xs) = ((xs=[] --> P(a)) & \
\                        (!y ys. xs=y#ys --> P(f y ys)))";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
by (Blast_tac 1);
qed "expand_list_case";

val prems = goal List.thy "[| P([]); !!x xs. P(x#xs) |] ==> P(xs)";
by(list.induct_tac "xs" 1);
by(REPEAT(resolve_tac prems 1));
qed "list_cases";

goal List.thy  "(xs=[] --> P([])) & (!y ys. xs=y#ys --> P(y#ys)) --> P(xs)";
by (list.induct_tac "xs" 1);
by (Blast_tac 1);
by (Blast_tac 1);
bind_thm("list_eq_cases",
  impI RSN (2,allI RSN (2,allI RSN (2,impI RS (conjI RS (result() RS mp))))));


(** @ - append **)

goal List.thy "(xs@ys)@zs = xs@(ys@zs)";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "append_assoc";
Addsimps [append_assoc];

goal List.thy "xs @ [] = xs";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "append_Nil2";
Addsimps [append_Nil2];

goal List.thy "(xs@ys = []) = (xs=[] & ys=[])";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "append_is_Nil_conv";
AddIffs [append_is_Nil_conv];

goal List.thy "([] = xs@ys) = (xs=[] & ys=[])";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
by(Blast_tac 1);
qed "Nil_is_append_conv";
AddIffs [Nil_is_append_conv];

goal List.thy "(xs @ ys = xs @ zs) = (ys=zs)";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "same_append_eq";
AddIffs [same_append_eq];

goal List.thy "!ys. (xs @ [x] = ys @ [y]) = (xs = ys & x = y)"; 
by(list.induct_tac "xs" 1);
 br allI 1;
 by(list.induct_tac "ys" 1);
  by(ALLGOALS Asm_simp_tac);
br allI 1;
by(list.induct_tac "ys" 1);
 by(ALLGOALS Asm_simp_tac);
qed_spec_mp "append1_eq_conv";
AddIffs [append1_eq_conv];

goal List.thy "xs ~= [] --> hd xs # tl xs = xs";
by(list.induct_tac "xs" 1);
by(ALLGOALS Asm_simp_tac);
qed_spec_mp "hd_Cons_tl";
Addsimps [hd_Cons_tl];

goal List.thy "hd(xs@ys) = (if xs=[] then hd ys else hd xs)";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "hd_append";

goal List.thy "tl(xs@ys) = (case xs of [] => tl(ys) | z#zs => zs@ys)";
by(simp_tac (!simpset setloop(split_tac[expand_list_case])) 1);
qed "tl_append";

(** map **)

goal List.thy
  "(!x. x : set_of_list xs --> f x = g x) --> map f xs = map g xs";
by(list.induct_tac "xs" 1);
by(ALLGOALS Asm_simp_tac);
bind_thm("map_ext", impI RS (allI RS (result() RS mp)));

goal List.thy "map (%x.x) = (%xs.xs)";
by (rtac ext 1);
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "map_ident";
Addsimps[map_ident];

goal List.thy "map f (xs@ys) = map f xs @ map f ys";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "map_append";
Addsimps[map_append];

goalw List.thy [o_def] "map (f o g) xs = map f (map g xs)";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "map_compose";
Addsimps[map_compose];

goal List.thy "rev(map f xs) = map f (rev xs)";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "rev_map";

(** rev **)

goal List.thy "rev(xs@ys) = rev(ys) @ rev(xs)";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "rev_append";
Addsimps[rev_append];

goal List.thy "rev(rev l) = l";
by (list.induct_tac "l" 1);
by (ALLGOALS Asm_simp_tac);
qed "rev_rev_ident";
Addsimps[rev_rev_ident];


(** mem **)

goal List.thy "x mem (xs@ys) = (x mem xs | x mem ys)";
by (list.induct_tac "xs" 1);
by (ALLGOALS (asm_simp_tac (!simpset setloop (split_tac [expand_if]))));
qed "mem_append";
Addsimps[mem_append];

goal List.thy "x mem [x:xs.P(x)] = (x mem xs & P(x))";
by (list.induct_tac "xs" 1);
by (ALLGOALS (asm_simp_tac (!simpset setloop (split_tac [expand_if]))));
qed "mem_filter";
Addsimps[mem_filter];

(** set_of_list **)

goal thy "set_of_list (xs@ys) = (set_of_list xs Un set_of_list ys)";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
by (Blast_tac 1);
qed "set_of_list_append";
Addsimps[set_of_list_append];

goal thy "(x mem xs) = (x: set_of_list xs)";
by (list.induct_tac "xs" 1);
by (ALLGOALS (asm_simp_tac (!simpset setloop (split_tac [expand_if]))));
by (Blast_tac 1);
qed "set_of_list_mem_eq";

goal List.thy "set_of_list l <= set_of_list (x#l)";
by (Simp_tac 1);
by (Blast_tac 1);
qed "set_of_list_subset_Cons";

goal List.thy "(set_of_list xs = {}) = (xs = [])";
by(list.induct_tac "xs" 1);
by(ALLGOALS Asm_simp_tac);
qed "set_of_list_empty";
Addsimps [set_of_list_empty];

goal List.thy "set_of_list(rev xs) = set_of_list(xs)";
by(list.induct_tac "xs" 1);
by(ALLGOALS Asm_simp_tac);
by(Blast_tac 1);
qed "set_of_list_rev";
Addsimps [set_of_list_rev];

goal List.thy "set_of_list(map f xs) = f``(set_of_list xs)";
by(list.induct_tac "xs" 1);
by(ALLGOALS Asm_simp_tac);
qed "set_of_list_map";
Addsimps [set_of_list_map];


(** list_all **)

goal List.thy "list_all (%x.True) xs = True";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "list_all_True";
Addsimps [list_all_True];

goal List.thy "list_all p (xs@ys) = (list_all p xs & list_all p ys)";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "list_all_append";
Addsimps [list_all_append];

goal List.thy "list_all P xs = (!x. x mem xs --> P(x))";
by (list.induct_tac "xs" 1);
by (ALLGOALS (asm_simp_tac (!simpset setloop (split_tac [expand_if]))));
by (Blast_tac 1);
qed "list_all_mem_conv";


(** filter **)

goal List.thy "[x:xs@ys . P] = [x:xs . P] @ [y:ys . P]";
by(list.induct_tac "xs" 1);
 by(ALLGOALS (asm_simp_tac (!simpset setloop (split_tac [expand_if]))));
qed "filter_append";
Addsimps [filter_append];


(** concat **)

goal List.thy  "concat(xs@ys) = concat(xs)@concat(ys)";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed"concat_append";
Addsimps [concat_append];

goal List.thy "rev(concat ls) = concat (map rev (rev ls))";
by (list.induct_tac "ls" 1);
by (ALLGOALS Asm_simp_tac);
qed "rev_concat";

(** length **)

goal List.thy "length(xs@ys) = length(xs)+length(ys)";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed"length_append";
Addsimps [length_append];

goal List.thy "length (map f l) = length l";
by (list.induct_tac "l" 1);
by (ALLGOALS Simp_tac);
qed "length_map";
Addsimps [length_map];

goal List.thy "length(rev xs) = length(xs)";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "length_rev";
Addsimps [length_rev];

goal List.thy "(length xs = 0) = (xs = [])";
by(list.induct_tac "xs" 1);
by(ALLGOALS Asm_simp_tac);
qed "length_0_conv";
AddIffs [length_0_conv];

goal List.thy "(0 < length xs) = (xs ~= [])";
by(list.induct_tac "xs" 1);
by(ALLGOALS Asm_simp_tac);
qed "length_greater_0_conv";
AddIffs [length_greater_0_conv];


(** nth **)

goal List.thy
  "!xs. nth n (xs@ys) = \
\          (if n < length xs then nth n xs else nth (n - length xs) ys)";
by(nat_ind_tac "n" 1);
 by(Asm_simp_tac 1);
 br allI 1;
 by(res_inst_tac [("xs","xs")]list_cases 1);
  by(ALLGOALS Asm_simp_tac);
br allI 1;
by(res_inst_tac [("xs","xs")]list_cases 1);
 by(ALLGOALS Asm_simp_tac);
qed_spec_mp "nth_append";

goal List.thy "!n. n < length xs --> nth n (map f xs) = f (nth n xs)";
by (list.induct_tac "xs" 1);
(* case [] *)
by (Asm_full_simp_tac 1);
(* case x#xl *)
by (rtac allI 1);
by (nat_ind_tac "n" 1);
by (ALLGOALS Asm_full_simp_tac);
qed_spec_mp "nth_map";
Addsimps [nth_map];

goal List.thy "!n. n < length xs --> list_all P xs --> P(nth n xs)";
by (list.induct_tac "xs" 1);
(* case [] *)
by (Simp_tac 1);
(* case x#xl *)
by (rtac allI 1);
by (nat_ind_tac "n" 1);
by (ALLGOALS Asm_full_simp_tac);
qed_spec_mp "list_all_nth";

goal List.thy "!n. n < length xs --> (nth n xs) mem xs";
by (list.induct_tac "xs" 1);
(* case [] *)
by (Simp_tac 1);
(* case x#xl *)
by (rtac allI 1);
by (nat_ind_tac "n" 1);
(* case 0 *)
by (Asm_full_simp_tac 1);
(* case Suc x *)
by (asm_full_simp_tac (!simpset setloop (split_tac [expand_if])) 1);
qed_spec_mp "nth_mem";
Addsimps [nth_mem];


(** take  & drop **)
section "take & drop";

goal thy "take 0 xs = []";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "take_0";

goal thy "drop 0 xs = xs";
by (list.induct_tac "xs" 1);
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

goal List.thy "!xs. length(take n xs) = min (length xs) n";
by(nat_ind_tac "n" 1);
 by(ALLGOALS Asm_simp_tac);
br allI 1;
by(res_inst_tac [("xs","xs")]list_cases 1);
 by(ALLGOALS Asm_simp_tac);
qed_spec_mp "length_take";
Addsimps [length_take];

goal List.thy "!xs. length(drop n xs) = (length xs - n)";
by(nat_ind_tac "n" 1);
 by(ALLGOALS Asm_simp_tac);
br allI 1;
by(res_inst_tac [("xs","xs")]list_cases 1);
 by(ALLGOALS Asm_simp_tac);
qed_spec_mp "length_drop";
Addsimps [length_drop];

goal List.thy "!xs. length xs <= n --> take n xs = xs";
by(nat_ind_tac "n" 1);
 by(ALLGOALS Asm_simp_tac);
br allI 1;
by(res_inst_tac [("xs","xs")]list_cases 1);
 by(ALLGOALS Asm_simp_tac);
qed_spec_mp "take_all";

goal List.thy "!xs. length xs <= n --> drop n xs = []";
by(nat_ind_tac "n" 1);
 by(ALLGOALS Asm_simp_tac);
br allI 1;
by(res_inst_tac [("xs","xs")]list_cases 1);
 by(ALLGOALS Asm_simp_tac);
qed_spec_mp "drop_all";

goal List.thy 
  "!xs. take n (xs @ ys) = (take n xs @ take (n - length xs) ys)";
by(nat_ind_tac "n" 1);
 by(ALLGOALS Asm_simp_tac);
br allI 1;
by(res_inst_tac [("xs","xs")]list_cases 1);
 by(ALLGOALS Asm_simp_tac);
qed_spec_mp "take_append";
Addsimps [take_append];

goal List.thy "!xs. drop n (xs@ys) = drop n xs @ drop (n - length xs) ys"; 
by(nat_ind_tac "n" 1);
 by(ALLGOALS Asm_simp_tac);
br allI 1;
by(res_inst_tac [("xs","xs")]list_cases 1);
 by(ALLGOALS Asm_simp_tac);
qed_spec_mp "drop_append";
Addsimps [drop_append];

goal List.thy "!xs n. take n (take m xs) = take (min n m) xs"; 
by(nat_ind_tac "m" 1);
 by(ALLGOALS Asm_simp_tac);
br allI 1;
by(res_inst_tac [("xs","xs")]list_cases 1);
 by(ALLGOALS Asm_simp_tac);
br allI 1;
by(res_inst_tac [("n","n")]natE 1);
 by(ALLGOALS Asm_simp_tac);
qed_spec_mp "take_take";

goal List.thy "!xs. drop n (drop m xs) = drop (n + m) xs"; 
by(nat_ind_tac "m" 1);
 by(ALLGOALS Asm_simp_tac);
br allI 1;
by(res_inst_tac [("xs","xs")]list_cases 1);
 by(ALLGOALS Asm_simp_tac);
qed_spec_mp "drop_drop";

goal List.thy "!xs n. take n (drop m xs) = drop m (take (n + m) xs)"; 
by(nat_ind_tac "m" 1);
 by(ALLGOALS Asm_simp_tac);
br allI 1;
by(res_inst_tac [("xs","xs")]list_cases 1);
 by(ALLGOALS Asm_simp_tac);
qed_spec_mp "take_drop";

goal List.thy "!xs. take n (map f xs) = map f (take n xs)"; 
by(nat_ind_tac "n" 1);
by(ALLGOALS Asm_simp_tac);
br allI 1;
by(res_inst_tac [("xs","xs")]list_cases 1);
by(ALLGOALS Asm_simp_tac);
qed_spec_mp "take_map"; 

goal List.thy "!xs. drop n (map f xs) = map f (drop n xs)"; 
by(nat_ind_tac "n" 1);
by(ALLGOALS Asm_simp_tac);
br allI 1;
by(res_inst_tac [("xs","xs")]list_cases 1);
by(ALLGOALS Asm_simp_tac);
qed_spec_mp "drop_map";

goal List.thy
  "!n i. i < n --> nth i (take n xs) = nth i xs";
by(list.induct_tac "xs" 1);
 by(ALLGOALS Asm_simp_tac);
by(strip_tac 1);
by(res_inst_tac [("n","n")] natE 1);
 by(Blast_tac 1);
by(res_inst_tac [("n","i")] natE 1);
by(ALLGOALS (hyp_subst_tac THEN' Asm_full_simp_tac));
qed_spec_mp "nth_take";
Addsimps [nth_take];

goal List.thy
  "!xs i. n + i < length xs --> nth i (drop n xs) = nth (n + i) xs";
by(nat_ind_tac "n" 1);
 by(ALLGOALS Asm_simp_tac);
br allI 1;
by(res_inst_tac [("xs","xs")]list_cases 1);
 by(ALLGOALS Asm_simp_tac);
qed_spec_mp "nth_drop";
Addsimps [nth_drop];

(** takeWhile & dropWhile **)

goal List.thy
  "x:set_of_list xs & ~P(x) --> takeWhile P (xs @ ys) = takeWhile P xs";
by(list.induct_tac "xs" 1);
 by(Simp_tac 1);
by(asm_full_simp_tac (!simpset setloop (split_tac[expand_if])) 1);
by(Blast_tac 1);
bind_thm("takeWhile_append1", conjI RS (result() RS mp));
Addsimps [takeWhile_append1];

goal List.thy
  "(!x:set_of_list xs.P(x)) --> takeWhile P (xs @ ys) = xs @ takeWhile P ys";
by(list.induct_tac "xs" 1);
 by(Simp_tac 1);
by(asm_full_simp_tac (!simpset setloop (split_tac[expand_if])) 1);
bind_thm("takeWhile_append2", ballI RS (result() RS mp));
Addsimps [takeWhile_append2];

goal List.thy
  "x:set_of_list xs & ~P(x) --> dropWhile P (xs @ ys) = (dropWhile P xs)@ys";
by(list.induct_tac "xs" 1);
 by(Simp_tac 1);
by(asm_full_simp_tac (!simpset setloop (split_tac[expand_if])) 1);
by(Blast_tac 1);
bind_thm("dropWhile_append1", conjI RS (result() RS mp));
Addsimps [dropWhile_append1];

goal List.thy
  "(!x:set_of_list xs.P(x)) --> dropWhile P (xs @ ys) = dropWhile P ys";
by(list.induct_tac "xs" 1);
 by(Simp_tac 1);
by(asm_full_simp_tac (!simpset setloop (split_tac[expand_if])) 1);
bind_thm("dropWhile_append2", ballI RS (result() RS mp));
Addsimps [dropWhile_append2];

goal List.thy "x:set_of_list(takeWhile P xs) --> x:set_of_list xs & P x";
by(list.induct_tac "xs" 1);
 by(Simp_tac 1);
by(asm_full_simp_tac (!simpset setloop (split_tac[expand_if])) 1);
qed_spec_mp"set_of_list_take_whileD";

