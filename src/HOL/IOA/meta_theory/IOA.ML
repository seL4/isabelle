(*  Title:      HOL/IOA/meta_theory/IOA.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

The I/O automata of Lynch and Tuttle.
*)

open IOA Asig;

val ioa_projections = [asig_of_def, starts_of_def, trans_of_def];

val exec_rws = [executions_def,is_execution_fragment_def];

goal IOA.thy
"asig_of(<x,y,z>) = x & starts_of(<x,y,z>) = y & trans_of(<x,y,z>) = z";
  by (simp_tac (SS addsimps ioa_projections) 1);
  qed "ioa_triple_proj";

goalw IOA.thy [ioa_def,state_trans_def,actions_def, is_asig_def]
  "!!A. [| IOA(A); <s1,a,s2>:trans_of(A) |] ==> a:actions(asig_of(A))";
  by (REPEAT(etac conjE 1));
  by (EVERY1[etac allE, etac impE, atac]);
  by (asm_full_simp_tac SS 1);
qed "trans_in_actions";


goal IOA.thy "filter_oseq p (filter_oseq p s) = filter_oseq p s";
  by (simp_tac (SS addsimps [filter_oseq_def]) 1);
  by (rtac ext 1);
  by (Option.option.induct_tac "s(i)" 1);
  by (simp_tac SS 1);
  by (simp_tac (SS setloop (split_tac [expand_if])) 1);
qed "filter_oseq_idemp";

goalw IOA.thy [mk_behaviour_def,filter_oseq_def]
"(mk_behaviour A s n = None) =                                        \
\  (s(n)=None | (? a. s(n)=Some(a) & a ~: externals(asig_of(A))))     \
\  &                                                                  \
\  (mk_behaviour A s n = Some(a)) =                                   \
\   (s(n)=Some(a) & a : externals(asig_of(A)))";
  by (Option.option.induct_tac "s(n)" 1);
  by (ALLGOALS (simp_tac (SS setloop (split_tac [expand_if]))));
  by (fast_tac HOL_cs 1);
qed "mk_behaviour_thm";

goalw IOA.thy [reachable_def] "!!A. s:starts_of(A) ==> reachable A s";
  by (res_inst_tac [("x","<%i.None,%i.s>")] bexI 1);
  by (simp_tac SS 1);
  by (asm_simp_tac (SS addsimps exec_rws) 1);
qed "reachable_0";

goalw IOA.thy (reachable_def::exec_rws)
"!!A. [| reachable A s; <s,a,t> : trans_of(A) |] ==> reachable A t";
  by(asm_full_simp_tac SS 1);
  by(safe_tac set_cs);
  by(res_inst_tac [("x","<%i.if i<n then fst ex i                    \
\                            else (if i=n then Some a else None),    \
\                         %i.if i<Suc n then snd ex i else t>")] bexI 1);
  by(res_inst_tac [("x","Suc(n)")] exI 1);
  by(simp_tac SS 1);
  by(asm_simp_tac (SS delsimps [less_Suc_eq]) 1);
  by(REPEAT(rtac allI 1));
  by(res_inst_tac [("m","na"),("n","n")] (make_elim less_linear) 1);
  be disjE 1;
  by(asm_simp_tac SS 1);
  be disjE 1;
  by(asm_simp_tac SS 1);
  by(fast_tac HOL_cs 1);
  by(forward_tac [less_not_sym] 1);
  by(asm_simp_tac (SS addsimps [less_not_refl2]) 1);
qed "reachable_n";

val [p1,p2] = goalw IOA.thy [invariant_def]
  "[| !!s. s:starts_of(A) ==> P(s);                                          \
\     !!s t a. [|reachable A s; P(s)|] ==> <s,a,t>: trans_of(A) --> P(t) |] \
\  ==> invariant A P";
  by (rewrite_goals_tac(reachable_def::Let_def::exec_rws));
  by (safe_tac set_cs);
  by (res_inst_tac [("Q","reachable A (snd ex n)")] conjunct1 1);
  by (nat_ind_tac "n" 1);
  by (fast_tac (set_cs addIs [p1,reachable_0]) 1);
  by (eres_inst_tac[("x","n1")]allE 1);
  by (eres_inst_tac[("P","%x.!a.?Q x a"), ("opt","fst ex n1")] optE 1);
  by (asm_simp_tac HOL_ss 1);
  by (safe_tac HOL_cs);
  by (etac (p2 RS mp) 1);
  by (ALLGOALS(fast_tac(set_cs addDs [hd Option.option.inject RS iffD1,
                                      reachable_n])));
qed "invariantI";

val [p1,p2] = goal IOA.thy
 "[| !!s. s : starts_of(A) ==> P(s); \
\   !!s t a. reachable A s ==> P(s) --> <s,a,t>:trans_of(A) --> P(t) \
\ |] ==> invariant A P";
  by (fast_tac (HOL_cs addSIs [invariantI] addSDs [p1,p2]) 1);
qed "invariantI1";

val [p1,p2] = goalw IOA.thy [invariant_def]
"[| invariant A P; reachable A s |] ==> P(s)";
   br(p2 RS (p1 RS spec RS mp))1;
qed "invariantE";

goal IOA.thy 
"actions(asig_comp a b) = actions(a) Un actions(b)";
  by(simp_tac (prod_ss addsimps
               ([actions_def,asig_comp_def]@asig_projections)) 1);
  by(fast_tac eq_cs 1);
qed "actions_asig_comp";

goal IOA.thy
"starts_of(A || B) = {p. fst(p):starts_of(A) & snd(p):starts_of(B)}";
  by(simp_tac (SS addsimps (par_def::ioa_projections)) 1);
qed "starts_of_par";

(* Every state in an execution is reachable *)
goalw IOA.thy [reachable_def] 
"!!A. ex:executions(A) ==> !n. reachable A (snd ex n)";
  by (fast_tac set_cs 1);
qed "states_of_exec_reachable";


goal IOA.thy 
"<s,a,t> : trans_of(A || B || C || D) =                                      \
\ ((a:actions(asig_of(A)) | a:actions(asig_of(B)) | a:actions(asig_of(C)) |  \
\   a:actions(asig_of(D))) &                                                 \
\  (if a:actions(asig_of(A)) then <fst(s),a,fst(t)>:trans_of(A)              \
\   else fst t=fst s) &                                                      \
\  (if a:actions(asig_of(B)) then <fst(snd(s)),a,fst(snd(t))>:trans_of(B)    \
\   else fst(snd(t))=fst(snd(s))) &                                          \
\  (if a:actions(asig_of(C)) then                                            \
\     <fst(snd(snd(s))),a,fst(snd(snd(t)))>:trans_of(C)                      \
\   else fst(snd(snd(t)))=fst(snd(snd(s)))) &                                \
\  (if a:actions(asig_of(D)) then                                            \
\     <snd(snd(snd(s))),a,snd(snd(snd(t)))>:trans_of(D)                      \
\   else snd(snd(snd(t)))=snd(snd(snd(s)))))";
  by(simp_tac (SS addsimps ([par_def,actions_asig_comp,Pair_fst_snd_eq]@
                            ioa_projections)
                  setloop (split_tac [expand_if])) 1);
qed "trans_of_par4";

goal IOA.thy "starts_of(restrict ioa acts) = starts_of(ioa) &     \
\             trans_of(restrict ioa acts) = trans_of(ioa) &       \
\             reachable (restrict ioa acts) s = reachable ioa s";
by(simp_tac (SS addsimps ([is_execution_fragment_def,executions_def,
                           reachable_def,restrict_def]@ioa_projections)) 1);
qed "cancel_restrict";

goal IOA.thy "asig_of(A || B) = asig_comp (asig_of A) (asig_of B)";
  by(simp_tac (SS addsimps (par_def::ioa_projections)) 1);
qed "asig_of_par";
