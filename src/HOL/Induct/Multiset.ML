(*  Title:      HOL/Induct/Multiset.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

Addsimps [Abs_multiset_inverse, Rep_multiset_inverse, Rep_multiset,
	  Zero_def];

(** Preservation of representing set `multiset' **)

Goalw [multiset_def] "(%a. 0) : multiset";
by (Simp_tac 1);
qed "const0_in_multiset";
Addsimps [const0_in_multiset];

Goalw [multiset_def] "(%b. if b=a then 1 else 0) : multiset";
by (Simp_tac 1);
qed "only1_in_multiset";
Addsimps [only1_in_multiset];

Goalw [multiset_def]
 "[| M : multiset; N : multiset |] ==> (%a. M a + N a) : multiset";
by (Asm_full_simp_tac 1);
by (dtac finite_UnI 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() delsimps [finite_Un]addsimps [Un_def]) 1);
qed "union_preserves_multiset";
Addsimps [union_preserves_multiset];

Goalw [multiset_def]
 "[| M : multiset |] ==> (%a. M a - N a) : multiset";
by (Asm_full_simp_tac 1);
by (etac (rotate_prems 1 finite_subset) 1);
by Auto_tac;
qed "diff_preserves_multiset";
Addsimps [diff_preserves_multiset];

(** Injectivity of Rep_multiset **)

Goal "(M = N) = (Rep_multiset M = Rep_multiset N)";
by (rtac iffI 1);
 by (Asm_simp_tac 1);
by (dres_inst_tac [("f","Abs_multiset")] arg_cong 1);
by (Asm_full_simp_tac 1);
qed "multiset_eq_conv_Rep_eq";
Addsimps [multiset_eq_conv_Rep_eq];
Addsimps [expand_fun_eq];

(*
Goal
 "[| f : multiset; g : multiset |] ==> \
\ (Abs_multiset f = Abs_multiset g) = (!x. f x = g x)";
by (rtac iffI 1);
 by (dres_inst_tac [("f","Rep_multiset")] arg_cong 1);
 by (Asm_full_simp_tac 1);
by (subgoal_tac "f = g" 1);
 by (Asm_simp_tac 1);
by (rtac ext 1);
by (Blast_tac 1);
qed "Abs_multiset_eq";
Addsimps [Abs_multiset_eq];
*)

(** Equations **)

(* union *)

Goalw [union_def,empty_def]
 "M + {#} = M & {#} + M = M";
by (Simp_tac 1);
qed "union_empty";
Addsimps [union_empty];

Goalw [union_def]
 "(M::'a multiset) + N = N + M";
by (simp_tac (simpset() addsimps add_ac) 1);
qed "union_commute";

Goalw [union_def]
 "((M::'a multiset)+N)+K = M+(N+K)";
by (simp_tac (simpset() addsimps add_ac) 1);
qed "union_assoc";

Goal "M+(N+K) = N+((M+K)::'a multiset)";
by (rtac (union_commute RS trans) 1);
by (rtac (union_assoc RS trans) 1);
by (rtac (union_commute RS arg_cong) 1);
qed "union_lcomm";

bind_thms ("union_ac", [union_assoc, union_commute, union_lcomm]);

(* diff *)

Goalw [empty_def,diff_def]
 "M-{#} = M & {#}-M = {#}";
by (Simp_tac 1);
qed "diff_empty";
Addsimps [diff_empty];

Goalw [union_def,diff_def]
 "M+{#a#}-{#a#} = M";
by (Simp_tac 1);
qed "diff_union_inverse2";
Addsimps [diff_union_inverse2];

(* count *)

Goalw [count_def,empty_def]
 "count {#} a = 0";
by (Simp_tac 1);
qed "count_empty";
Addsimps [count_empty];

Goalw [count_def,single_def]
 "count {#b#} a = (if b=a then 1 else 0)";
by (Simp_tac 1);
qed "count_single";
Addsimps [count_single];

Goalw [count_def,union_def]
 "count (M+N) a = count M a + count N a";
by (Simp_tac 1);
qed "count_union";
Addsimps [count_union];

Goalw [count_def,diff_def]
 "count (M-N) a = count M a - count N a";
by (Simp_tac 1);
qed "count_diff";
Addsimps [count_diff];

(* set_of *)

Goalw [set_of_def] "set_of {#} = {}";
by (Simp_tac 1);
qed "set_of_empty";
Addsimps [set_of_empty];

Goalw [set_of_def]
 "set_of {#b#} = {b}";
by (Simp_tac 1);
qed "set_of_single";
Addsimps [set_of_single];

Goalw [set_of_def]
 "set_of(M+N) = set_of M Un set_of N";
by Auto_tac;
qed "set_of_union";
Addsimps [set_of_union];

Goalw [set_of_def, empty_def, count_def] "(set_of M = {}) = (M = {#})";
by Auto_tac;
qed "set_of_eq_empty_iff";

Goalw [set_of_def] "(x : set_of M) = (x :# M)";
by Auto_tac; 
qed "mem_set_of_iff";

(* size *)

Goalw [size_def] "size {#} = 0";
by (Simp_tac 1);
qed "size_empty";
Addsimps [size_empty];

Goalw [size_def] "size {#b#} = 1";
by (Simp_tac 1);
qed "size_single";
Addsimps [size_single];

Goal "finite (set_of M)";
by (cut_inst_tac [("x", "M")] Rep_multiset 1);
by (asm_full_simp_tac
    (simpset() addsimps [multiset_def, set_of_def, count_def]) 1);
qed "finite_set_of";
AddIffs [finite_set_of];

Goal "finite A ==> setsum (count N) (A Int set_of N) = setsum (count N) A";
by (etac finite_induct 1);
by (Simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [Int_insert_left, set_of_def]) 1);
qed "setsum_count_Int";

Goalw [size_def] "size (M+N::'a multiset) = size M + size N";
by (subgoal_tac "count (M+N) = (%a. count M a + count N a)" 1);
by (rtac ext 2);
by (Simp_tac 2);
by (asm_simp_tac
    (simpset() addsimps [setsum_Un, setsum_addf, setsum_count_Int]) 1);
by (stac Int_commute 1);
by (asm_simp_tac (simpset() addsimps [setsum_count_Int]) 1);
qed "size_union";
Addsimps [size_union];

Goalw [size_def, empty_def, count_def] "(size M = 0) = (M = {#})";
by Auto_tac; 
by (asm_full_simp_tac (simpset() addsimps [set_of_def, count_def]) 1); 
qed "size_eq_0_iff_empty";
AddIffs [size_eq_0_iff_empty];

Goalw [size_def] "size M = Suc n ==> EX a. a :# M";
by (dtac setsum_SucD 1);
by Auto_tac; 
qed "size_eq_Suc_imp_elem";


(* equalities *)

Goalw [count_def] "(M = N) = (!a. count M a = count N a)";
by (Simp_tac 1);
qed "multiset_eq_conv_count_eq";

Goalw [single_def,empty_def] "{#a#} ~= {#}  &  {#} ~= {#a#}";
by (Simp_tac 1);
qed "single_not_empty";
Addsimps [single_not_empty];

Goalw [single_def] "({#a#}={#b#}) = (a=b)";
by Auto_tac;
qed "single_eq_single";
Addsimps [single_eq_single];

Goalw [union_def,empty_def]
 "(M+N = {#}) = (M = {#} & N = {#})";
by (Simp_tac 1);
by (Blast_tac 1);
qed "union_eq_empty";
AddIffs [union_eq_empty];

Goalw [union_def,empty_def]
 "({#} = M+N) = (M = {#} & N = {#})";
by (Simp_tac 1);
by (Blast_tac 1);
qed "empty_eq_union";
AddIffs [empty_eq_union];

Goalw [union_def]
 "(M+K = N+K) = (M=(N::'a multiset))";
by (Simp_tac 1);
qed "union_right_cancel";
Addsimps [union_right_cancel];

Goalw [union_def]
 "(K+M = K+N) = (M=(N::'a multiset))";
by (Simp_tac 1);
qed "union_left_cancel";
Addsimps [union_left_cancel];

Goalw [empty_def,single_def,union_def]
 "(M+N = {#a#}) = (M={#a#} & N={#} | M={#} & N={#a#})";
by (simp_tac (simpset() addsimps [add_is_1]) 1);
by (Blast_tac 1);
qed "union_is_single";

Goalw [empty_def,single_def,union_def]
 "({#a#} = M+N) = ({#a#}=M & N={#} | M={#} & {#a#}=N)";
by (simp_tac (simpset() addsimps [one_is_add]) 1);
by (blast_tac (claset() addDs [sym]) 1);
qed "single_is_union";

Goalw [single_def,union_def,diff_def]
 "(M+{#a#} = N+{#b#}) = (M=N & a=b | M = N-{#a#}+{#b#} & N = M-{#b#}+{#a#})";
by (Simp_tac 1);
by (rtac conjI 1);
 by (Force_tac 1);
by (Clarify_tac 1);
by (rtac conjI 1);
 by (Blast_tac 1);
by (Clarify_tac 1);
by (rtac iffI 1);
 by (rtac conjI 1);
 by (Clarify_tac 1);
  by (rtac conjI 1);
   by (asm_full_simp_tac (simpset() addsimps [eq_sym_conv]) 1);
(* PROOF FAILED:
by (Blast_tac 1);
*)
  by (Fast_tac 1);
 by (Asm_simp_tac 1);
by (Force_tac 1);
qed "add_eq_conv_diff";

(* FIXME
val prems = Goal
 "[| !!F. [| finite F; !G. G < F --> P G |] ==> P F |] ==> finite F --> P F";
by (res_inst_tac [("a","F"),("f","%A. if finite A then card A else 0")]
     measure_induct 1);
by (Clarify_tac 1);
by (resolve_tac prems 1);
 by (assume_tac 1);
by (Clarify_tac 1);
by (subgoal_tac "finite G" 1);
 by (fast_tac (claset() addDs [finite_subset,order_less_le RS iffD1]) 2);
by (etac allE 1);
by (etac impE 1);
 by (Blast_tac 2);
by (asm_simp_tac (simpset() addsimps [psubset_card]) 1);
no_qed();
val lemma = result();

val prems = Goal
 "[| finite F; !!F. [| finite F; !G. G < F --> P G |] ==> P F |] ==> P F";
by (rtac (lemma RS mp) 1);
by (REPEAT(ares_tac prems 1));
qed "finite_psubset_induct";

Better: use wf_finite_psubset in WF_Rel
*)


(** Towards the induction rule **)

Goal "[| finite F; 0 < f a |] ==> \
\     setsum (f(a:=f(a)-1)) F = (if a:F then setsum f F - 1 else setsum f F)";
by (etac finite_induct 1);
by Auto_tac;
 by (asm_simp_tac (simpset() addsimps add_ac) 1);
by (dres_inst_tac [("a","a")] mk_disjoint_insert 1);
by Auto_tac;
qed "setsum_decr";

val prems = Goalw [multiset_def]
 "[| P(%a.0); \
\    !!f b. [| f : multiset; P(f) |] ==> P(f(b:=f(b)+1)) |] \
\  ==> !f. f : multiset --> setsum f {x. 0 < f x} = n --> P(f)";
by (induct_tac "n" 1);
 by (Asm_simp_tac 1);
 by (Clarify_tac 1);
 by (subgoal_tac "f = (%a.0)" 1);
  by (Asm_simp_tac 1);
  by (resolve_tac prems 1);
 by (rtac ext 1);
 by (Force_tac 1);
by (Clarify_tac 1);
by (ftac setsum_SucD 1);
by (Clarify_tac 1);
by (rename_tac "a" 1);
by (subgoal_tac "finite{x. 0 < (f(a:=f(a)-1)) x}" 1);
 by (etac (rotate_prems 1 finite_subset) 2);
 by (Simp_tac 2);
 by (Blast_tac 2);
by (subgoal_tac
   "f = (f(a:=f(a)-1))(a:=(f(a:=f(a)-1))a+1)" 1);
 by (rtac ext 2);
 by (Asm_simp_tac 2);
by (EVERY1[etac ssubst, resolve_tac prems]);
 by (Blast_tac 1);
by (EVERY[etac allE 1, etac impE 1, etac mp 2]);
 by (Blast_tac 1);
by (asm_simp_tac (simpset() addsimps [setsum_decr] delsimps [fun_upd_apply]) 1);
by (subgoal_tac "{x. x ~= a --> 0 < f x} = {x. 0 < f x}" 1);
 by (Blast_tac 2);
by (subgoal_tac "{x. x ~= a & 0 < f x} = {x. 0 < f x} - {a}" 1);
 by (Blast_tac 2);
by (asm_simp_tac (simpset() addsimps [le_imp_diff_is_add,setsum_diff1]
                           addcongs [conj_cong]) 1);
no_qed();
val lemma = result();

val major::prems = Goal
 "[| f : multiset; \
\    P(%a.0); \
\    !!f b. [| f : multiset; P(f) |] ==> P(f(b:=f(b)+1)) |] ==> P(f)";
by (rtac (major RSN (3, lemma RS spec RS mp RS mp)) 1);
by (REPEAT(ares_tac (refl::prems) 1));
qed "Rep_multiset_induct";

val [prem1,prem2] = Goalw [union_def,single_def,empty_def]
 "[| P({#}); !!M x. P(M) ==> P(M + {#x#}) |] ==> P(M)";
by (rtac (Rep_multiset_inverse RS subst) 1);
by (rtac (Rep_multiset RS Rep_multiset_induct) 1);
 by (rtac prem1 1);
by (Clarify_tac 1);
by (subgoal_tac
    "f(b := f b + 1) = (%a. f a + (if a = b then 1 else 0))" 1);
 by (Simp_tac 2);
by (etac ssubst 1);
by (etac (Abs_multiset_inverse RS subst) 1);
by (etac(simplify (simpset()) prem2)1);
qed "multiset_induct";

Goal "M : multiset ==> (%x. if P x then M x else 0) : multiset";
by (asm_full_simp_tac (simpset() addsimps [multiset_def]) 1);
by (rtac finite_subset 1);
by Auto_tac; 
qed "MCollect_preserves_multiset";

Goalw [count_def,MCollect_def]
 "count {# x:M. P x #} a = (if P a then count M a else 0)";
by (asm_full_simp_tac (simpset() addsimps [MCollect_preserves_multiset]) 1); 
qed "count_MCollect";
Addsimps [count_MCollect];

Goalw [set_of_def]
 "set_of {# x:M. P x #} = set_of M Int {x. P x}";
by Auto_tac; 
qed "set_of_MCollect";
Addsimps [set_of_MCollect];

Goal "M = {# x:M. P x #} + {# x:M. ~ P x #}";
by (stac multiset_eq_conv_count_eq 1);
by Auto_tac; 
qed "multiset_partition";

Delsimps [multiset_eq_conv_Rep_eq, expand_fun_eq];
Delsimps [Abs_multiset_inverse,Rep_multiset_inverse,Rep_multiset];

Goal
 "(M+{#a#} = N+{#b#}) = (M = N & a = b | (? K. M = K+{#b#} & N = K+{#a#}))";
by (simp_tac (simpset() addsimps [add_eq_conv_diff]) 1);
by Auto_tac;
qed "add_eq_conv_ex";

(** order **)

Goalw [mult1_def] "(M, {#}) ~: mult1(r)";
by (Simp_tac 1);
qed "not_less_empty";
AddIffs [not_less_empty];

Goalw [mult1_def]
 "(N,M0 + {#a#}) : mult1(r) = \
\ ((? M. (M,M0) : mult1(r) & N = M + {#a#}) | \
\  (? K. (!b. b :# K --> (b,a) : r) & N = M0 + K))";
by (rtac iffI 1);
 by (asm_full_simp_tac (simpset() addsimps [add_eq_conv_ex]) 1);
 by (Clarify_tac 1);
 by (etac disjE 1);
  by (Blast_tac 1);
 by (Clarify_tac 1);
 by (res_inst_tac [("x","Ka+K")] exI 1);
 by (simp_tac (simpset() addsimps union_ac) 1);
 by (Blast_tac 1);
by (etac disjE 1);
 by (Clarify_tac 1);
 by (res_inst_tac [("x","aa")] exI 1);
 by (res_inst_tac [("x","M0+{#a#}")] exI 1);
 by (res_inst_tac [("x","K")] exI 1);
 by (simp_tac (simpset() addsimps union_ac) 1);
by (Blast_tac 1);
qed "less_add_conv";

Open_locale "MSOrd";

val W_def = thm "W_def";

Goalw [W_def]
 "[| !b. (b,a) : r --> (!M : W. M+{#b#} : W); M0 : W; \
\    !M. (M,M0) : mult1(r) --> M+{#a#} : W |] \
\ ==> M0+{#a#} : W";
by (rtac accI 1);
by (rename_tac "N" 1);
by (full_simp_tac (simpset() addsimps [less_add_conv]) 1);
by (etac disjE 1);
 by (Blast_tac 1);
by (Clarify_tac 1);
by (rotate_tac ~1 1);
by (etac rev_mp 1);
by (induct_thm_tac multiset_induct "K" 1);
 by (Asm_simp_tac 1);
by (simp_tac (simpset() addsimps [union_assoc RS sym]) 1);
by (Blast_tac 1);
qed "lemma1";

Goalw [W_def]
 "[| !b. (b,a) : r --> (!M : W. M+{#b#} : W); M : W |] ==> M+{#a#} : W";
by (etac acc_induct 1);
by (blast_tac (claset() addIs [export lemma1]) 1);
qed "lemma2";

Goalw [W_def]
 "wf(r) ==> !M:W. M+{#a#} : W";
by (eres_inst_tac [("a","a")] wf_induct 1);
by (blast_tac (claset() addIs [export lemma2]) 1);
qed "lemma3";

Goalw [W_def] "wf(r) ==> M : W";
by (induct_thm_tac multiset_induct "M" 1);
 by (rtac accI 1);
 by (Asm_full_simp_tac 1);
by (blast_tac (claset() addDs [export lemma3]) 1);
qed "all_accessible";

Close_locale "MSOrd";

Goal "wf(r) ==> wf(mult1 r)";
by (blast_tac (claset() addIs [acc_wfI, export all_accessible]) 1);
qed "wf_mult1";

Goalw [mult_def] "wf(r) ==> wf(mult r)";
by (blast_tac (claset() addIs [wf_trancl,wf_mult1]) 1);
qed "wf_mult";

(** Equivalence of mult with the usual (closure-free) def **)

(* Badly needed: a linear arithmetic tactic for multisets *)

Goal "a :# J ==> I+J - {#a#} = I + (J-{#a#})";
by (asm_simp_tac (simpset() addsimps [multiset_eq_conv_count_eq]) 1);
qed "diff_union_single_conv";

(* One direction *)
Goalw [mult_def,mult1_def,set_of_def]
 "trans r ==> \
\ (M,N) : mult r ==> (? I J K. N = I+J & M = I+K & J ~= {#} & \
\                            (!k : set_of K. ? j : set_of J. (k,j) : r))";
by (etac converse_trancl_induct 1);
 by (Clarify_tac 1);
 by (res_inst_tac [("x","M0")] exI 1);
 by (Simp_tac 1);
by (Clarify_tac 1);
by (case_tac "a :# K" 1);
 by (res_inst_tac [("x","I")] exI 1);
 by (Simp_tac 1);
 by (res_inst_tac [("x","(K - {#a#}) + Ka")] exI 1);
 by (asm_simp_tac (simpset() addsimps [union_assoc RS sym]) 1);
 by (dres_inst_tac[("f","%M. M-{#a#}")] arg_cong 1);
 by (asm_full_simp_tac (simpset() addsimps [diff_union_single_conv]) 1);
 by (full_simp_tac (simpset() addsimps [trans_def]) 1);
 by (Blast_tac 1);
by (subgoal_tac "a :# I" 1);
 by (res_inst_tac [("x","I-{#a#}")] exI 1);
 by (res_inst_tac [("x","J+{#a#}")] exI 1);
 by (res_inst_tac [("x","K + Ka")] exI 1);
 by (rtac conjI 1);
  by (asm_simp_tac (simpset() addsimps [multiset_eq_conv_count_eq]
                             addsplits [nat_diff_split]) 1);
 by (rtac conjI 1);
  by (dres_inst_tac[("f","%M. M-{#a#}")] arg_cong 1);
  by (Asm_full_simp_tac 1);
  by (asm_simp_tac (simpset() addsimps [multiset_eq_conv_count_eq]
                             addsplits [nat_diff_split]) 1);
 by (full_simp_tac (simpset() addsimps [trans_def]) 1);
 by (Blast_tac 1);
by (subgoal_tac "a :# (M0 +{#a#})" 1);
 by (Asm_full_simp_tac 1);
by (Simp_tac 1);
qed "mult_implies_one_step";

Goal "a :# M ==> M = M - {#a#} + {#a#}";
by (asm_simp_tac (simpset() addsimps [multiset_eq_conv_count_eq]) 1);
qed "elem_imp_eq_diff_union";

Goal "size M = Suc n ==> EX a N. M = N + {#a#}";
by (etac (size_eq_Suc_imp_elem RS exE) 1);
by (dtac elem_imp_eq_diff_union 1); 
by Auto_tac; 
qed "size_eq_Suc_imp_eq_union";


Goal  "trans r ==> \
\ ALL I J K. \
\  (size J = n & J ~= {#} & \
\   (! k : set_of K. ? j : set_of J. (k,j) : r)) --> (I+K, I+J) : mult r";
by (induct_tac "n" 1);
by Auto_tac; 
by (ftac size_eq_Suc_imp_eq_union 1);
by (Clarify_tac 1); 
ren "J'" 1;
by (Asm_full_simp_tac 1); 
by (etac notE 1); 
by Auto_tac; 
by (case_tac "J' = {#}" 1);
 by (asm_full_simp_tac (simpset() addsimps [mult_def]) 1); 
 by (rtac r_into_trancl 1); 
 by (asm_full_simp_tac (simpset() addsimps [mult1_def,set_of_def]) 1);
 by (Blast_tac 1); 
(*Now we know J' ~= {#}*)
by (cut_inst_tac [("M","K"),("P", "%x. (x,a):r")] multiset_partition 1);
by (eres_inst_tac [("P", "ALL k : set_of K. ?P k")] rev_mp 1); 
by (etac ssubst 1); 
by (asm_full_simp_tac (simpset() addsimps [Ball_def]) 1); 
by Auto_tac; 
by (subgoal_tac "((I + {# x : K. (x, a) : r#}) + {# x : K. (x, a) ~: r#}, \
\                 (I + {# x : K. (x, a) : r#}) + J') : mult r" 1);
 by (Force_tac 2);
by (full_simp_tac (simpset() addsimps [union_assoc RS sym, mult_def]) 1); 
by (etac trancl_trans 1); 
by (rtac r_into_trancl 1); 
by (asm_full_simp_tac (simpset() addsimps [mult1_def,set_of_def]) 1); 
by (res_inst_tac [("x", "a")] exI 1); 
by (res_inst_tac [("x", "I + J'")] exI 1); 
by (asm_simp_tac (simpset() addsimps union_ac) 1); 
qed_spec_mp "one_step_implies_mult_lemma";

Goal  "[| trans r;  J ~= {#};  \
\         ALL k : set_of K. EX j : set_of J. (k,j) : r |] \
\      ==> (I+K, I+J) : mult r";
by (rtac one_step_implies_mult_lemma 1); 
by Auto_tac; 
qed "one_step_implies_mult";


(** Proving that multisets are partially ordered **)

Goalw [trans_def] "trans {(x',x). x' < (x::'a::order)}";
by (blast_tac (claset() addIs [order_less_trans]) 1);
qed "trans_base_order";

Goal "finite A ==> (ALL x: A. EX y : A. x < (y::'a::order)) --> A={}";
by (etac finite_induct 1);
by Auto_tac;
by (blast_tac (claset() addIs [order_less_trans]) 1);
qed_spec_mp "mult_irrefl_lemma";

(*irreflexivity*)
Goalw [mult_less_def] "~ M < (M :: ('a::order)multiset)";
by Auto_tac;
by (dtac (trans_base_order RS mult_implies_one_step) 1);
by Auto_tac;
by (dtac (finite_set_of RS mult_irrefl_lemma) 1);
by (asm_full_simp_tac (simpset() addsimps [set_of_eq_empty_iff]) 1);
qed "mult_less_not_refl";

(* N<N ==> R *)
bind_thm ("mult_less_irrefl", mult_less_not_refl RS notE);
AddSEs [mult_less_irrefl];

(*transitivity*)
Goalw [mult_less_def, mult_def]
     "[| K < M; M < N |] ==> K < (N :: ('a::order)multiset)";
by (blast_tac (claset() addIs [trancl_trans]) 1);
qed "mult_less_trans";

(*asymmetry*)
Goal "M < N ==> ~ N < (M :: ('a::order)multiset)";
by Auto_tac;
by (rtac (mult_less_not_refl RS notE) 1);
by (etac mult_less_trans 1);
by (assume_tac 1);
qed "mult_less_not_sym";

(* [| M<N;  ~P ==> N<M |] ==> P *)
bind_thm ("mult_less_asym", mult_less_not_sym RS swap);

Goalw [mult_le_def] "M <= (M :: ('a::order)multiset)";
by Auto_tac;
qed "mult_le_refl";
AddIffs [mult_le_refl];

(*anti-symmetry*)
Goalw [mult_le_def] "[| M <= N;  N <= M |] ==> M = (N :: ('a::order)multiset)";
by (blast_tac (claset() addDs [mult_less_not_sym]) 1);
qed "mult_le_antisym";

(*transitivity*)
Goalw [mult_le_def]
     "[| K <= M; M <= N |] ==> K <= (N :: ('a::order)multiset)";
by (blast_tac (claset() addIs [mult_less_trans]) 1);
qed "mult_le_trans";

Goalw [mult_le_def] "M < N = (M <= N & M ~= (N :: ('a::order)multiset))";
by Auto_tac;
qed "mult_less_le";


(** Monotonicity of multiset union **)

Goalw [mult1_def]
     "[| (B,D) : mult1 r; trans r |] ==> (C + B, C + D) : mult1 r";
by Auto_tac; 
by (res_inst_tac [("x", "a")] exI 1); 
by (res_inst_tac [("x", "C+M0")] exI 1); 
by (asm_simp_tac (simpset() addsimps [union_assoc]) 1); 
qed "mult1_union";

Goalw [mult_less_def, mult_def]
     "!!C:: ('a::order) multiset. B<D ==> C+B < C+D";
by (etac trancl_induct 1); 
by (blast_tac (claset() addIs [mult1_union, transI, order_less_trans, 
                               r_into_trancl]) 1); 
by (blast_tac (claset() addIs [mult1_union, transI, order_less_trans, 
                               r_into_trancl, trancl_trans]) 1); 
qed "union_less_mono2";

Goal "!!C:: ('a::order) multiset. B<D ==> B+C < D+C";
by (simp_tac (simpset() addsimps [union_commute]) 1); 
by (etac union_less_mono2 1); 
qed "union_less_mono1";

Goal "!!C:: ('a::order) multiset. [| A<C; B<D |] ==> A+B < C+D";
by (blast_tac (claset() addIs [union_less_mono1, union_less_mono2,
                               mult_less_trans]) 1); 
qed "union_less_mono";

Goalw [mult_le_def]
     "!!D:: ('a::order) multiset. [| A<=C;  B<=D |] ==> A+B <= C+D";
by (blast_tac (claset() addIs [union_less_mono, union_less_mono1, 
                               union_less_mono2]) 1); 
qed "union_le_mono";



Goalw [mult_le_def, mult_less_def]
     "{#} <= (M :: ('a::order) multiset)";
by (case_tac "M={#}" 1);
by (subgoal_tac "({#} + {#}, {#} + M) : mult(Collect (split op <))" 2);
by (rtac one_step_implies_mult 3);
bw trans_def;
by Auto_tac; 
by (blast_tac (claset() addIs [order_less_trans]) 1); 
qed "empty_leI";
AddIffs [empty_leI];


Goal "!!A:: ('a::order) multiset. A <= A+B";
by (subgoal_tac "A+{#} <= A+B" 1);
by (rtac union_le_mono 2); 
by Auto_tac; 
qed "union_upper1";

Goal "!!A:: ('a::order) multiset. B <= A+B";
by (stac union_commute 1 THEN rtac union_upper1 1);
qed "union_upper2";
