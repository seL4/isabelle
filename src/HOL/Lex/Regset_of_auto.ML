Addsimps [in_set_butlast_appendI1,in_set_butlast_appendI2];
AddIs    [in_set_butlast_appendI1,in_set_butlast_appendI2];
Addsimps [image_eqI];

AddIffs [star.NilI];
Addsimps [star.ConsI];
AddIs [star.ConsI];

(* Lists *)

(*
(* could go into List. Needs WF_Rel as ancestor. *)
(* Induction over the length of a list: *)
val prems = goal thy
 "(!!xs::'a list. (!ys. length ys < length xs --> P ys) ==> P xs) ==> P xs";
by(res_inst_tac [("P","P"),("r","measure length::('a list * 'a list)set")]
     wf_induct 1);
by(Simp_tac 1);
by(asm_full_simp_tac (simpset() addsimps [measure_def,inv_image_def]) 1);
bes prems 1;
qed "list_length_induct";
*)

goal thy "(butlast xs = []) = (case xs of [] => True | y#ys => ys=[])";
by(exhaust_tac "xs" 1);
by(ALLGOALS (asm_simp_tac (simpset() addsplits [expand_if])));
qed "butlast_empty";
AddIffs [butlast_empty];

goal thy "x:set(butlast xs) --> xs:set xss --> x:set(butlast(concat xss))";
by(induct_tac "xss" 1);
 by(Simp_tac 1);
by(asm_simp_tac (simpset() addsimps [butlast_append] delsimps ball_simps
                           addsplits [expand_if]) 1);
br conjI 1;
 by(Clarify_tac 1);
 br conjI 1;
  by(Blast_tac 1);
 by(Clarify_tac 1);
 by(subgoal_tac "xs=[]" 1);
  by(rotate_tac ~1 1);
  by(Asm_full_simp_tac 1);
 by(Blast_tac 1);
by(blast_tac (claset() addDs [in_set_butlastD]) 1);
qed_spec_mp "in_set_butlast_concatI";

(* Regular sets *)

goal thy "(!xs: set xss. xs:A) --> concat xss : star A";
by(induct_tac "xss" 1);
by(ALLGOALS Asm_full_simp_tac);
qed_spec_mp "concat_in_star";

(* The main lemma:
   how to decompose a trace into a prefix, a list of loops and a suffix.
*)
goal thy "!i. k : set(trace A i xs) --> (? pref mids suf. \
\ xs = pref @ concat mids @ suf & \
\ deltas A pref i = k & (!n:set(butlast(trace A i pref)). n ~= k) & \
\ (!mid:set mids. (deltas A mid k = k) & \
\                 (!n:set(butlast(trace A k mid)). n ~= k)) & \
\ (!n:set(butlast(trace A k suf)). n ~= k))";
by(induct_tac "xs" 1);
 by(Simp_tac 1);
by(rename_tac "a as" 1);
br allI 1;
by(case_tac "A a i = k" 1);
 by(strip_tac 1);
 by(res_inst_tac[("x","[a]")]exI 1);
 by(Asm_full_simp_tac 1);
 by(case_tac "k : set(trace A (A a i) as)" 1);
  be allE 1;
  be impE 1;
   ba 1;
  by(REPEAT(etac exE 1));
  by(res_inst_tac[("x","pref#mids")]exI 1);
  by(res_inst_tac[("x","suf")]exI 1);
  by(Asm_full_simp_tac 1);
 by(res_inst_tac[("x","[]")]exI 1);
 by(res_inst_tac[("x","as")]exI 1);
 by(Asm_full_simp_tac 1);
 by(blast_tac (claset() addDs [in_set_butlastD]) 1);
by(Asm_simp_tac 1);
br conjI 1;
 by(Blast_tac 1);
by(strip_tac 1);
be allE 1;
be impE 1;
 ba 1;
by(REPEAT(etac exE 1));
by(res_inst_tac[("x","a#pref")]exI 1);
by(res_inst_tac[("x","mids")]exI 1);
by(res_inst_tac[("x","suf")]exI 1);
by(asm_simp_tac (simpset() addsplits [expand_if]) 1);
qed_spec_mp "decompose";

goal thy "!i. length(trace A i xs) = length xs";
by(induct_tac "xs" 1);
by(ALLGOALS Asm_simp_tac);
qed "length_trace";
Addsimps [length_trace];

goal thy "!i. deltas A (xs@ys) i = deltas A ys (deltas A xs i)";
by(induct_tac "xs" 1);
by(ALLGOALS Asm_simp_tac);
qed "deltas_append";
Addsimps [deltas_append];

goal thy "!i. trace A i (xs@ys) = trace A i xs @ trace A (deltas A xs i) ys";
by(induct_tac "xs" 1);
by(ALLGOALS Asm_simp_tac);
qed "trace_append";
Addsimps [trace_append];

goal thy "(!xs: set xss. deltas A xs i = i) --> \
\         trace A i (concat xss) = concat (map (trace A i) xss)";
by(induct_tac "xss" 1);
by(ALLGOALS Asm_simp_tac);
qed_spec_mp "trace_concat";
Addsimps [trace_concat];

goal thy "!i. (trace A i xs = []) = (xs = [])";
by(exhaust_tac "xs" 1);
by(ALLGOALS Asm_simp_tac);
qed "trace_is_Nil";
Addsimps [trace_is_Nil];

goal thy "(trace A i xs = n#ns) = \
\         (case xs of [] => False | y#ys => n = A y i & ns = trace A n ys)";
by(exhaust_tac "xs" 1);
by(ALLGOALS Asm_simp_tac);
by(Blast_tac 1);
qed_spec_mp "trace_is_Cons_conv";
Addsimps [trace_is_Cons_conv];

goal thy "!i. set(trace A i xs) = \
\ (if xs=[] then {} else insert(deltas A xs i)(set(butlast(trace A i xs))))";
by(induct_tac "xs" 1);
 by(Simp_tac 1);
by(asm_simp_tac (simpset() addsimps [insert_commute] addsplits [expand_if]) 1);
qed "set_trace_conv";

goal thy
 "(!mid:set mids. deltas A mid k = k) --> deltas A (concat mids) k = k";
by(induct_tac "mids" 1);
by(ALLGOALS Asm_simp_tac);
qed_spec_mp "deltas_concat";
Addsimps [deltas_concat];

goal Nat.thy "!!n. [| n < Suc k; n ~= k |] ==> n < k";
be nat_neqE 1;
by(ALLGOALS trans_tac);
val lemma = result();


goal thy
 "!i j xs. xs : regset_of A i j k = \
\          ((!n:set(butlast(trace A i xs)). n < k) & deltas A xs i = j)";
by(induct_tac "k" 1);
 by(simp_tac (simpset() addcongs [conj_cong]
                        addsplits [expand_if,split_list_case]) 1);
by(strip_tac 1);
by(asm_simp_tac (simpset() addsimps [conc_def]) 1);
br iffI 1;
 be disjE 1;
  by(Asm_simp_tac 1);
 by(REPEAT(eresolve_tac[exE,conjE] 1));
 by(Asm_full_simp_tac 1);
 by(subgoal_tac
      "(!n:set(butlast(trace A k xsb)). n < Suc k) & deltas A xsb k = k" 1);
  by(asm_simp_tac (simpset() addsplits [expand_if]
       addsimps [set_trace_conv,butlast_append,ball_Un]) 1);
 be star.induct 1;
  by(Simp_tac 1);
 by(asm_full_simp_tac (simpset() addsplits [expand_if]
       addsimps [set_trace_conv,butlast_append,ball_Un]) 1);
by(case_tac "k : set(butlast(trace A i xs))" 1);
 br disjI1 2;
 by(blast_tac (claset() addIs [lemma]) 2);
br disjI2 1;
bd (in_set_butlastD RS decompose) 1;
by(Clarify_tac 1);
by(res_inst_tac [("x","pref")] exI 1);
by(Asm_full_simp_tac 1);
br conjI 1;
 br ballI 1;
 br lemma 1;
  by(Asm_simp_tac 2);
 by(EVERY[dtac bspec 1, atac 2]);
 by(Asm_simp_tac 1);
by(res_inst_tac [("x","concat mids")] exI 1);
by(Simp_tac 1);
br conjI 1;
 br concat_in_star 1;
 by(Asm_simp_tac 1);
 br ballI 1;
 br ballI 1;
 br lemma 1;
  by(Asm_simp_tac 2);
 by(EVERY[dtac bspec 1, atac 2]);
 by(asm_simp_tac (simpset() addsimps [image_eqI,in_set_butlast_concatI]) 1);
br ballI 1;
br lemma 1;
 by(Asm_simp_tac 2);
by(EVERY[dtac bspec 1, atac 2]);
by(Asm_simp_tac 1);
qed_spec_mp "regset_of_spec";

goal thy "!!A. !n. n < k --> (!x. A x n < k) ==> \
\         !i. i < k --> (!n:set(trace A i xs). n < k)";
by(induct_tac "xs" 1);
 by(ALLGOALS Simp_tac);
by(Blast_tac 1);
qed_spec_mp "trace_below";

goal thy "!!A. [| !n. n < k --> (!x. A x n < k); i < k; j < k |] ==> \
\         regset_of A i j k = {xs. deltas A xs i = j}";
br set_ext 1;
by(simp_tac (simpset() addsimps [regset_of_spec]) 1);
by(blast_tac (claset() addDs [trace_below,in_set_butlastD]) 1);
qed "regset_of_below";
