(* Title:     HOL/W0/I.ML
   ID:        $Id$
   Author:    Thomas Stauner
   Copyright  1995 TU Muenchen

Equivalence of W and I.
*)

open I;

goal thy
  "! a m s s' t n.  \
\    (new_tv m a & new_tv m s) --> I e a m s = Ok(s',t,n) -->   \
\    ( ? r. W e ($ s a) m = Ok(r, $ s' t, n) & s' = ($ r o s) )";
by (expr.induct_tac "e" 1);

  (* case Var n *)
  by (simp_tac (!simpset addsimps [app_subst_list]
      setloop (split_inside_tac [expand_if])) 1);

 (* case Abs e *)
 by (asm_full_simp_tac (!simpset setloop (split_inside_tac [expand_bind])) 1);
 by (strip_tac 1);
 by (rtac conjI 1);
  by (strip_tac 1);
  by (REPEAT (etac allE 1));
  by (etac impE 1);
   by (fast_tac (HOL_cs addss (!simpset addsimps [new_tv_subst])) 2);
  by (fast_tac (HOL_cs addIs [new_tv_Suc_list RS mp,new_tv_subst_le,
                              less_imp_le,lessI]) 1); 
(** LEVEL 10 **)
 by (strip_tac 1);
 by (REPEAT (etac allE 1));
 by (etac impE 1);
  by (fast_tac (HOL_cs addss (!simpset addsimps [new_tv_subst])) 2);
 by (fast_tac (HOL_cs addIs [new_tv_Suc_list RS mp,new_tv_subst_le,
                             less_imp_le,lessI]) 1);
(** LEVEL 15 **)
(* case App e1 e2 *)
by (simp_tac (!simpset setloop (split_inside_tac [expand_bind])) 1);
by (strip_tac 1);
by (rename_tac "s1' t1 n1 s2' t2 n2 sa" 1);
by (rtac conjI 1);
 by (fast_tac (HOL_cs addss !simpset) 1);
by (strip_tac 1);
by (rename_tac "s1 t1' n1'" 1);
by (eres_inst_tac [("x","a")] allE 1);
by (eres_inst_tac [("x","m")] allE 1);
by (eres_inst_tac [("x","s")] allE 1);
by (eres_inst_tac [("x","s1'")] allE 1);
by (eres_inst_tac [("x","t1")] allE 1);
by (eres_inst_tac [("x","n1")] allE 1);
by (eres_inst_tac [("x","a")] allE 1);
by (eres_inst_tac [("x","n1")] allE 1);
by (eres_inst_tac [("x","s1'")] allE 1);
by (eres_inst_tac [("x","s2'")] allE 1);
by (eres_inst_tac [("x","t2")] allE 1);
by (eres_inst_tac [("x","n2")] allE 1);
(** LEVEL 34 **)
by (rtac conjI 1);
 by (strip_tac 1);
 by (mp_tac 1);
 by (mp_tac 1);
 by (etac exE 1);
 by (etac conjE 1);
 by (etac impE 1);
  by ((forward_tac [new_tv_subst_tel] 1) THEN (atac 1)); 
  by ((dres_inst_tac [("a","$ s a")] new_tv_W 1) THEN (atac 1));
  by (fast_tac (HOL_cs addDs [sym RS W_var_geD,new_tv_subst_le,new_tv_list_le] 
                       addss !simpset) 1);
 by (fast_tac (HOL_cs addss (!simpset addsimps [subst_comp_tel])) 1);
(** LEVEL 45 **)
by (strip_tac 1);
by (rename_tac "s2 t2' n2'" 1);
by (rtac conjI 1);
 by (strip_tac 1);
 by (mp_tac 1);
 by (mp_tac 1);
 by (etac exE 1);
 by (etac conjE 1);
 by (etac impE 1);
  by ((forward_tac [new_tv_subst_tel] 1) THEN (atac 1)); 
  by ((dres_inst_tac [("a","$ s a")] new_tv_W 1) THEN (atac 1));
  by (fast_tac (HOL_cs addDs [sym RS W_var_geD,new_tv_subst_le,new_tv_list_le] 
                       addss !simpset) 1);
 by (fast_tac (HOL_cs addss (!simpset addsimps [subst_comp_tel,subst_comp_te])) 1);
by (strip_tac 1);
by (mp_tac 1);
(** LEVEL 60 **)
by (mp_tac 1);
by (etac exE 1);
by (etac conjE 1);
by (etac impE 1);
 by ((forward_tac [new_tv_subst_tel] 1) THEN (atac 1)); 
 by ((dres_inst_tac [("a","$ s a")] new_tv_W 1) THEN (atac 1));
 by (fast_tac (HOL_cs addDs [sym RS W_var_geD,new_tv_subst_le,new_tv_list_le] 
                      addss !simpset) 1);
by (mp_tac 1);
by (REPEAT (eresolve_tac [exE,conjE] 1));
by (REPEAT(EVERY1
     [asm_full_simp_tac (!simpset addsimps [subst_comp_tel,subst_comp_te,o_def]),
      REPEAT o etac conjE, hyp_subst_tac]));
(** LEVEL 70 **)
by (subgoal_tac "new_tv n2 s & new_tv n2 r & new_tv n2 ra" 1);
 by (asm_full_simp_tac (!simpset addsimps [new_tv_subst]) 1);
by ((forward_tac [new_tv_subst_tel] 1) THEN (atac 1));
by ((dres_inst_tac [("a","$ s a")] new_tv_W 1) THEN (atac 1));
by (safe_tac HOL_cs);
  by (best_tac (HOL_cs addDs[sym RS W_var_geD,new_tv_subst_le,new_tv_list_le] 
                       addss !simpset) 1);
 by (fast_tac (HOL_cs addDs [sym RS W_var_geD,new_tv_subst_le,new_tv_list_le] 
                      addss !simpset) 1);
(** LEVEL 77 **)
by (dres_inst_tac [("e","expr1")] (sym RS W_var_geD) 1);
by ((dtac new_tv_subst_tel 1) THEN (atac 1));
by ((dres_inst_tac [("ts","$ s a")] new_tv_list_le 1) THEN (atac 1));
by ((dtac new_tv_subst_tel 1) THEN (atac 1));
by (best_tac (HOL_cs addDs [new_tv_W] 
                     addss (!simpset addsimps [subst_comp_tel])) 1);
(** LEVEL 82 **)
qed_spec_mp "I_correct_wrt_W";

(***
We actually want the corollary

goal I.thy
  "I e [] m id_subst = Ok(s,t,n) --> W e [] m = Ok(s, $s t, n)";
by (cut_facts_tac [(read_instantiate[("x","id_subst")]
 (read_instantiate[("x","[]")](thm RS spec)
  RS spec RS spec))] 1);
by (Full_simp_tac 1);
by (fast_tac HOL_cs 1);
qed;

assuming that thm is the undischarged version of I_correct_wrt_W.

Wait until simplification of thms is possible.
***)

val lemma = I_correct_wrt_W COMP swap_prems_rl;

Addsimps [split_paired_Ex];

goal I.thy "!a m s. \
\  new_tv m a & new_tv m s --> I e a m s = Fail --> W e ($s a) m = Fail";
by (expr.induct_tac "e" 1);
  by (simp_tac (!simpset addsimps [app_subst_list] addsplits [expand_if]) 1);
 by (Simp_tac 1);
 by (strip_tac 1);
 by (subgoal_tac "TVar m # $ s a = $s(TVar m # a)" 1);
  by (asm_simp_tac (HOL_ss addsimps
        [new_tv_Suc_list, lessI RS less_imp_le RS new_tv_subst_le]) 1);
 by (etac conjE 1);
 by (dtac (new_tv_not_free_tv RS not_free_impl_id) 1);
 by (Asm_simp_tac 1);
(** LEVEL 9 **)
by (Asm_simp_tac 1);
by (strip_tac 1);
by (REPEAT(etac exE 1));
by (REPEAT(etac conjE 1));
by (dtac lemma 1);
 by (fast_tac HOL_cs 1);
(** LEVEL 15 **)
by (etac exE 1);
by (etac conjE 1);
by (hyp_subst_tac 1);
by (Asm_simp_tac 1);
by (REPEAT(resolve_tac [exI,conjI,refl] 1));
by (etac disjE 1);
 by (rtac disjI1 1);
(** LEVEL 22 **)
 by (full_simp_tac (!simpset addsimps [o_def,subst_comp_tel]) 1);
 by (EVERY[etac allE 1, etac allE 1, etac allE 1,
          etac impE 1, etac impE 2, atac 2, atac 2]);
 by (rtac conjI 1);
  by (fast_tac (HOL_cs addIs [W_var_ge RS new_tv_list_le]) 1);
 by (rtac new_tv_subst_comp_2 1);
  by (fast_tac (HOL_cs addIs [W_var_ge RS new_tv_subst_le]) 1);
 by (fast_tac (HOL_cs addSIs [new_tv_subst_tel]addIs[new_tv_W RS conjunct1])1);
by (rtac disjI2 1);
by (REPEAT(etac exE 1));
by (etac conjE 1);
(** LEVEL 32 **)
by (dtac lemma 1);
 by (rtac conjI 1);
  by (fast_tac (HOL_cs addIs [W_var_ge RS new_tv_list_le]) 1);
 by (rtac new_tv_subst_comp_1 1);
  by (fast_tac (HOL_cs addIs [W_var_ge RS new_tv_subst_le]) 1);
 by (fast_tac (HOL_cs addSIs [new_tv_subst_tel]addIs[new_tv_W RS conjunct1])1);
by (etac exE 1);
by (etac conjE 1);
by (hyp_subst_tac 1);
(** LEVEL 41 **)
by (asm_full_simp_tac (!simpset addsimps
     [o_def,subst_comp_te RS sym,subst_comp_tel RS sym]) 1);
qed_spec_mp "I_complete_wrt_W";

(***
We actually want the corollary

  "I e [] m id_subst = Fail ==> W e [] m = Fail";

Wait until simplification of thms is possible.
***)
