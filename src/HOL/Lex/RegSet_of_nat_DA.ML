(*  Title:      HOL/Lex/RegSet_of_nat_DA.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

Addsimps [in_set_butlast_appendI1,in_set_butlast_appendI2];
AddIs    [in_set_butlast_appendI1,in_set_butlast_appendI2];
Addsimps [image_eqI];

(* Lists *)

goal thy "(butlast xs = []) = (case xs of [] => True | y#ys => ys=[])";
by (exhaust_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "butlast_empty";
AddIffs [butlast_empty];

goal thy "x:set(butlast xs) --> xs:set xss --> x:set(butlast(concat xss))";
by (induct_tac "xss" 1);
 by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [butlast_append] delsimps ball_simps) 1);
by (rtac conjI 1);
 by (Clarify_tac 1);
 by (rtac conjI 1);
  by (Blast_tac 1);
 by (Clarify_tac 1);
 by (subgoal_tac "xs=[]" 1);
  by (rotate_tac ~1 1);
  by (Asm_full_simp_tac 1);
 by (Blast_tac 1);
by (blast_tac (claset() addDs [in_set_butlastD]) 1);
qed_spec_mp "in_set_butlast_concatI";

(* Regular sets *)

(* The main lemma:
   how to decompose a trace into a prefix, a list of loops and a suffix.
*)
goal thy "!i. k : set(trace d i xs) --> (? pref mids suf. \
\ xs = pref @ concat mids @ suf & \
\ deltas d pref i = k & (!n:set(butlast(trace d i pref)). n ~= k) & \
\ (!mid:set mids. (deltas d mid k = k) & \
\                 (!n:set(butlast(trace d k mid)). n ~= k)) & \
\ (!n:set(butlast(trace d k suf)). n ~= k))";
by (induct_tac "xs" 1);
 by (Simp_tac 1);
by (rename_tac "a as" 1);
by (rtac allI 1);
by (case_tac "d a i = k" 1);
 by (strip_tac 1);
 by (res_inst_tac[("x","[a]")]exI 1);
 by (Asm_full_simp_tac 1);
 by (case_tac "k : set(trace d (d a i) as)" 1);
  by (etac allE 1);
  by (etac impE 1);
   by (assume_tac 1);
  by (REPEAT(etac exE 1));
  by (res_inst_tac[("x","pref#mids")]exI 1);
  by (res_inst_tac[("x","suf")]exI 1);
  by (Asm_full_simp_tac 1);
 by (res_inst_tac[("x","[]")]exI 1);
 by (res_inst_tac[("x","as")]exI 1);
 by (Asm_full_simp_tac 1);
 by (blast_tac (claset() addDs [in_set_butlastD]) 1);
by (Asm_simp_tac 1);
by (rtac conjI 1);
 by (Blast_tac 1);
by (strip_tac 1);
by (etac allE 1);
by (etac impE 1);
 by (assume_tac 1);
by (REPEAT(etac exE 1));
by (res_inst_tac[("x","a#pref")]exI 1);
by (res_inst_tac[("x","mids")]exI 1);
by (res_inst_tac[("x","suf")]exI 1);
by (Asm_simp_tac 1);
qed_spec_mp "decompose";

goal thy "!i. length(trace d i xs) = length xs";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "length_trace";
Addsimps [length_trace];

goal thy "!i. deltas d (xs@ys) i = deltas d ys (deltas d xs i)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "deltas_append";
Addsimps [deltas_append];

goal thy "!i. trace d i (xs@ys) = trace d i xs @ trace d (deltas d xs i) ys";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "trace_append";
Addsimps [trace_append];

goal thy "(!xs: set xss. deltas d xs i = i) --> \
\         trace d i (concat xss) = concat (map (trace d i) xss)";
by (induct_tac "xss" 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "trace_concat";
Addsimps [trace_concat];

goal thy "!i. (trace d i xs = []) = (xs = [])";
by (exhaust_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "trace_is_Nil";
Addsimps [trace_is_Nil];

goal thy "(trace d i xs = n#ns) = \
\         (case xs of [] => False | y#ys => n = d y i & ns = trace d n ys)";
by (exhaust_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
by (Blast_tac 1);
qed_spec_mp "trace_is_Cons_conv";
Addsimps [trace_is_Cons_conv];

goal thy "!i. set(trace d i xs) = \
\ (if xs=[] then {} else insert(deltas d xs i)(set(butlast(trace d i xs))))";
by (induct_tac "xs" 1);
 by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [insert_commute]) 1);
qed "set_trace_conv";

goal thy
 "(!mid:set mids. deltas d mid k = k) --> deltas d (concat mids) k = k";
by (induct_tac "mids" 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "deltas_concat";
Addsimps [deltas_concat];

goal Nat.thy "!!n. [| n < Suc k; n ~= k |] ==> n < k";
by (etac nat_neqE 1);
by (ALLGOALS trans_tac);
val lemma = result();


goal thy
 "!i j xs. xs : regset d i j k = \
\          ((!n:set(butlast(trace d i xs)). n < k) & deltas d xs i = j)";
by (induct_tac "k" 1);
 by (simp_tac (simpset() addcongs [conj_cong] addsplits [split_list_case]) 1);
by (strip_tac 1);
by (asm_simp_tac (simpset() addsimps [conc_def]) 1);
by (rtac iffI 1);
 by (etac disjE 1);
  by (Asm_simp_tac 1);
 by (REPEAT(eresolve_tac[exE,conjE] 1));
 by (Asm_full_simp_tac 1);
 by (subgoal_tac
      "(!n:set(butlast(trace d k xsb)). n < Suc k) & deltas d xsb k = k" 1);
  by (asm_simp_tac (simpset() addsimps [set_trace_conv,butlast_append,ball_Un]) 1);
 by (etac star.induct 1);
  by (Simp_tac 1);
 by (asm_full_simp_tac (simpset() addsimps [set_trace_conv,butlast_append,ball_Un]) 1);
by (case_tac "k : set(butlast(trace d i xs))" 1);
 by (rtac disjI1 2);
 by (blast_tac (claset() addIs [lemma]) 2);
by (rtac disjI2 1);
by (dtac (in_set_butlastD RS decompose) 1);
by (Clarify_tac 1);
by (res_inst_tac [("x","pref")] exI 1);
by (Asm_full_simp_tac 1);
by (rtac conjI 1);
 by (rtac ballI 1);
 by (rtac lemma 1);
  by (Asm_simp_tac 2);
 by (EVERY[dtac bspec 1, atac 2]);
 by (Asm_simp_tac 1);
by (res_inst_tac [("x","concat mids")] exI 1);
by (Simp_tac 1);
by (rtac conjI 1);
 by (rtac concat_in_star 1);
 by (Asm_simp_tac 1);
 by (rtac ballI 1);
 by (rtac ballI 1);
 by (rtac lemma 1);
  by (Asm_simp_tac 2);
 by (EVERY[dtac bspec 1, atac 2]);
 by (asm_simp_tac (simpset() addsimps [image_eqI,in_set_butlast_concatI]) 1);
by (rtac ballI 1);
by (rtac lemma 1);
 by (Asm_simp_tac 2);
by (EVERY[dtac bspec 1, atac 2]);
by (Asm_simp_tac 1);
qed_spec_mp "regset_spec";

goalw thy [bounded_def]
 "!!d. bounded d k ==> !i. i < k --> (!n:set(trace d i xs). n < k)";
by (induct_tac "xs" 1);
 by (ALLGOALS Simp_tac);
by (Blast_tac 1);
qed_spec_mp "trace_below";

goal thy "!!d. [| bounded d k; i < k; j < k |] ==> \
\         regset d i j k = {xs. deltas d xs i = j}";
by (rtac set_ext 1);
by (simp_tac (simpset() addsimps [regset_spec]) 1);
by (blast_tac (claset() addDs [trace_below,in_set_butlastD]) 1);
qed "regset_below";

goalw thy [bounded_def]
 "!!d. bounded d k ==> !i. i < k --> deltas d w i < k";
by (induct_tac "w" 1);
 by (ALLGOALS Simp_tac);
by (Blast_tac 1);
qed_spec_mp "deltas_below";

goalw thy [regset_of_DA_def]
 "!!d. [| bounded (next A) k; start A < k; j < k |] ==> \
\      w : regset_of_DA A k = accepts A w";
by(asm_simp_tac (simpset() addcongs [conj_cong] addsimps
 [regset_below,deltas_below,accepts_def,delta_def]) 1);
qed "regset_DA_equiv";
