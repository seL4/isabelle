(*  Title: 	HOL/List
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1994 TU Muenchen

List lemmas
*)

open List;

val [Nil_not_Cons,Cons_not_Nil] = list.distinct;

bind_thm("Cons_neq_Nil", Cons_not_Nil RS notE);
bind_thm("Nil_neq_Cons", sym RS Cons_neq_Nil);

bind_thm("Cons_inject", (hd list.inject) RS iffD1 RS conjE);

val list_ss = HOL_ss addsimps list.simps;

goal List.thy "!x. xs ~= x#xs";
by (list.induct_tac "xs" 1);
by (ALLGOALS (asm_simp_tac list_ss));
qed "not_Cons_self";

goal List.thy "(xs ~= []) = (? y ys. xs = y#ys)";
by (list.induct_tac "xs" 1);
by(simp_tac list_ss 1);
by(asm_simp_tac list_ss 1);
by(REPEAT(resolve_tac [exI,refl,conjI] 1));
qed "neq_Nil_conv";

val list_ss = arith_ss addsimps list.simps @
  [null_Nil, null_Cons, hd_Cons, tl_Cons, ttl_Nil, ttl_Cons,
   mem_Nil, mem_Cons,
   append_Nil, append_Cons,
   map_Nil, map_Cons,
   flat_Nil, flat_Cons,
   list_all_Nil, list_all_Cons,
   filter_Nil, filter_Cons];


(** @ - append **)

goal List.thy "(xs@ys)@zs = xs@(ys@zs)";
by (list.induct_tac "xs" 1);
by(ALLGOALS(asm_simp_tac list_ss));
qed "append_assoc";

goal List.thy "xs @ [] = xs";
by (list.induct_tac "xs" 1);
by(ALLGOALS(asm_simp_tac list_ss));
qed "append_Nil2";

goal List.thy "(xs@ys = []) = (xs=[] & ys=[])";
by (list.induct_tac "xs" 1);
by(ALLGOALS(asm_simp_tac list_ss));
qed "append_is_Nil";

goal List.thy "(xs @ ys = xs @ zs) = (ys=zs)";
by (list.induct_tac "xs" 1);
by(ALLGOALS(asm_simp_tac list_ss));
qed "same_append_eq";


(** mem **)

goal List.thy "x mem (xs@ys) = (x mem xs | x mem ys)";
by (list.induct_tac "xs" 1);
by(ALLGOALS(asm_simp_tac (list_ss setloop (split_tac [expand_if]))));
qed "mem_append";

goal List.thy "x mem [x:xs.P(x)] = (x mem xs & P(x))";
by (list.induct_tac "xs" 1);
by(ALLGOALS(asm_simp_tac (list_ss setloop (split_tac [expand_if]))));
qed "mem_filter";

(** list_all **)

goal List.thy "(Alls x:xs.True) = True";
by (list.induct_tac "xs" 1);
by(ALLGOALS(asm_simp_tac list_ss));
qed "list_all_True";

goal List.thy "list_all p (xs@ys) = (list_all p xs & list_all p ys)";
by (list.induct_tac "xs" 1);
by(ALLGOALS(asm_simp_tac list_ss));
qed "list_all_conj";

goal List.thy "(Alls x:xs.P(x)) = (!x. x mem xs --> P(x))";
by (list.induct_tac "xs" 1);
by(ALLGOALS(asm_simp_tac (list_ss setloop (split_tac [expand_if]))));
by(fast_tac HOL_cs 1);
qed "list_all_mem_conv";


(** list_case **)

goal List.thy
 "P(list_case a f xs) = ((xs=[] --> P(a)) & \
\                         (!y ys. xs=y#ys --> P(f y ys)))";
by (list.induct_tac "xs" 1);
by(ALLGOALS(asm_simp_tac list_ss));
by(fast_tac HOL_cs 1);
qed "expand_list_case";

goal List.thy  "(xs=[] --> P([])) & (!y ys. xs=y#ys --> P(y#ys)) --> P(xs)";
by(list.induct_tac "xs" 1);
by(fast_tac HOL_cs 1);
by(fast_tac HOL_cs 1);
bind_thm("list_eq_cases",
  impI RSN (2,allI RSN (2,allI RSN (2,impI RS (conjI RS (result() RS mp))))));

(** flat **)

goal List.thy  "flat(xs@ys) = flat(xs)@flat(ys)";
by (list.induct_tac "xs" 1);
by(ALLGOALS(asm_simp_tac (list_ss addsimps [append_assoc])));
qed"flat_append";

(** nth **)

val [nth_0,nth_Suc] = nat_recs nth_def; 
store_thm("nth_0",nth_0);
store_thm("nth_Suc",nth_Suc);

(** Additional mapping lemmas **)

goal List.thy "map (%x.x) xs = xs";
by (list.induct_tac "xs" 1);
by (ALLGOALS (asm_simp_tac list_ss));
qed "map_ident";

goal List.thy "map f (xs@ys) = map f xs @ map f ys";
by (list.induct_tac "xs" 1);
by (ALLGOALS (asm_simp_tac list_ss));
qed "map_append";

goalw List.thy [o_def] "map (f o g) xs = map f (map g xs)";
by (list.induct_tac "xs" 1);
by (ALLGOALS (asm_simp_tac list_ss));
qed "map_compose";

val list_ss = list_ss addsimps
  [not_Cons_self, append_assoc, append_Nil2, append_is_Nil, same_append_eq,
   mem_append, mem_filter,
   map_ident, map_append, map_compose,
   flat_append, list_all_True, list_all_conj, nth_0, nth_Suc];

