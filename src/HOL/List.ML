(*  Title:      HOL/List
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

List lemmas
*)

open List;

val [Nil_not_Cons,Cons_not_Nil] = list.distinct;

bind_thm("Cons_neq_Nil", Cons_not_Nil RS notE);
bind_thm("Nil_neq_Cons", sym RS Cons_neq_Nil);

bind_thm("Cons_inject", (hd list.inject) RS iffD1 RS conjE);

goal List.thy "!x. xs ~= x#xs";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "not_Cons_self";

goal List.thy "(xs ~= []) = (? y ys. xs = y#ys)";
by (list.induct_tac "xs" 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
by (REPEAT(resolve_tac [exI,refl,conjI] 1));
qed "neq_Nil_conv";


(** @ - append **)

goal List.thy "(xs@ys)@zs = xs@(ys@zs)";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "append_assoc";

goal List.thy "xs @ [] = xs";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "append_Nil2";

goal List.thy "(xs@ys = []) = (xs=[] & ys=[])";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "append_is_Nil";

goal List.thy "(xs @ ys = xs @ zs) = (ys=zs)";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "same_append_eq";

goal List.thy "hd(xs@ys) = (if xs=[] then hd ys else hd xs)";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "hd_append";

(** rev **)

goal List.thy "rev(xs@ys) = rev(ys) @ rev(xs)";
by (list.induct_tac "xs" 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [append_Nil2,append_assoc])));
qed "rev_append";

goal List.thy "rev(rev l) = l";
by (list.induct_tac "l" 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [rev_append])));
qed "rev_rev_ident";


(** mem **)

goal List.thy "x mem (xs@ys) = (x mem xs | x mem ys)";
by (list.induct_tac "xs" 1);
by (ALLGOALS (asm_simp_tac (!simpset setloop (split_tac [expand_if]))));
qed "mem_append";

goal List.thy "x mem [x:xs.P(x)] = (x mem xs & P(x))";
by (list.induct_tac "xs" 1);
by (ALLGOALS (asm_simp_tac (!simpset setloop (split_tac [expand_if]))));
qed "mem_filter";

(** list_all **)

goal List.thy "(Alls x:xs.True) = True";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "list_all_True";

goal List.thy "list_all p (xs@ys) = (list_all p xs & list_all p ys)";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "list_all_conj";

goal List.thy "(Alls x:xs.P(x)) = (!x. x mem xs --> P(x))";
by (list.induct_tac "xs" 1);
by (ALLGOALS (asm_simp_tac (!simpset setloop (split_tac [expand_if]))));
by (Fast_tac 1);
qed "list_all_mem_conv";


(** list_case **)

goal List.thy
 "P(list_case a f xs) = ((xs=[] --> P(a)) & \
\                         (!y ys. xs=y#ys --> P(f y ys)))";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
by (Fast_tac 1);
qed "expand_list_case";

goal List.thy  "(xs=[] --> P([])) & (!y ys. xs=y#ys --> P(y#ys)) --> P(xs)";
by (list.induct_tac "xs" 1);
by (Fast_tac 1);
by (Fast_tac 1);
bind_thm("list_eq_cases",
  impI RSN (2,allI RSN (2,allI RSN (2,impI RS (conjI RS (result() RS mp))))));

(** flat **)

goal List.thy  "flat(xs@ys) = flat(xs)@flat(ys)";
by (list.induct_tac "xs" 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [append_assoc])));
qed"flat_append";

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

(** nth **)

val [nth_0,nth_Suc] = nat_recs nth_def; 
store_thm("nth_0",nth_0);
store_thm("nth_Suc",nth_Suc);
Addsimps [nth_0,nth_Suc];

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

(** drop **)

goal thy "drop 0 xs = xs";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "drop_0";

goal thy "drop (Suc n) (x#xs) = drop n xs";
by (Simp_tac 1);
qed "drop_Suc_Cons";

Delsimps [drop_Cons];
Addsimps [drop_0,drop_Suc_Cons];

(** take **)

goal thy "take 0 xs = []";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "take_0";

goal thy "take (Suc n) (x#xs) = x # take n xs";
by (Simp_tac 1);
qed "take_Suc_Cons";

Delsimps [take_Cons];
Addsimps [take_0,take_Suc_Cons];

(** Additional mapping lemmas **)

goal List.thy "map (%x.x) = (%xs.xs)";
by (rtac ext 1);
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "map_ident";

goal List.thy "map f (xs@ys) = map f xs @ map f ys";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "map_append";

goalw List.thy [o_def] "map (f o g) xs = map f (map g xs)";
by (list.induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "map_compose";

goal List.thy "rev(map f l) = map f (rev l)";
by (list.induct_tac "l" 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [map_append])));
qed "rev_map_distrib";

goal List.thy "rev(flat ls) = flat (map rev (rev ls))";
by (list.induct_tac "ls" 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps 
       [map_append, flat_append, rev_append, append_Nil2])));
qed "rev_flat";

Addsimps
  [not_Cons_self, append_assoc, append_Nil2, append_is_Nil, same_append_eq,
   mem_append, mem_filter,
   rev_append, rev_rev_ident,
   map_ident, map_append, map_compose,
   flat_append, list_all_True, list_all_conj];

