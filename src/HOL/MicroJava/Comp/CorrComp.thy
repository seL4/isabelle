(*  Title:      HOL/MicroJava/Comp/CorrComp.thy
    ID:         $Id$
    Author:     Martin Strecker
    Copyright   GPL 2002
*)

(* Compiler correctness statement and proof *)

theory CorrComp =  JTypeSafe + LemmasComp:

declare wf_prog_ws_prog [simp add]

(* If no exception is present after evaluation/execution, 
  none can have been present before *)
lemma eval_evals_exec_xcpt:
 "((xs,ex,val,xs') \<in> Eval.eval G \<longrightarrow> gx xs' = None \<longrightarrow> gx xs = None) \<and>
  ((xs,exs,vals,xs') \<in> Eval.evals G \<longrightarrow> gx xs' = None \<longrightarrow> gx xs = None) \<and>
  ((xs,st,xs') \<in> Eval.exec G \<longrightarrow> gx xs' = None \<longrightarrow> gx xs = None)"
by (induct rule: eval_evals_exec.induct, auto)


(* instance of eval_evals_exec_xcpt for eval *)
lemma eval_xcpt: "(xs,ex,val,xs') \<in> Eval.eval G \<Longrightarrow> gx xs' = None \<Longrightarrow> gx xs = None"
 (is "?H1 \<Longrightarrow> ?H2 \<Longrightarrow> ?T")
proof-
  assume h1: ?H1
  assume h2: ?H2
  from h1 h2 eval_evals_exec_xcpt show "?T" by simp
qed

(* instance of eval_evals_exec_xcpt for evals *)
lemma evals_xcpt: "(xs,exs,vals,xs') \<in> Eval.evals G \<Longrightarrow> gx xs' = None \<Longrightarrow> gx xs = None"
 (is "?H1 \<Longrightarrow> ?H2 \<Longrightarrow> ?T")
proof-
  assume h1: ?H1
  assume h2: ?H2
  from h1 h2 eval_evals_exec_xcpt show "?T" by simp
qed

(* instance of eval_evals_exec_xcpt for exec *)
lemma exec_xcpt: "(xs,st,xs') \<in> Eval.exec G \<Longrightarrow> gx xs' = None \<Longrightarrow> gx xs = None"
 (is "?H1 \<Longrightarrow> ?H2 \<Longrightarrow> ?T")
proof-
  assume h1: ?H1
  assume h2: ?H2
  from h1 h2 eval_evals_exec_xcpt show "?T" by simp
qed

(**********************************************************************)

theorem exec_all_trans: "\<lbrakk>(exec_all G s0 s1); (exec_all G s1 s2)\<rbrakk> \<Longrightarrow> (exec_all G s0 s2)"
apply (auto simp: exec_all_def elim: Transitive_Closure.rtrancl_trans)
done

theorem exec_all_refl: "exec_all G s s"
by (simp only: exec_all_def, rule rtrancl_refl)


theorem exec_instr_in_exec_all:
  "\<lbrakk> exec_instr i G hp stk lvars C S pc frs =  (None, hp', frs');
             gis (gmb G C S) ! pc = i\<rbrakk>  \<Longrightarrow>
       G \<turnstile> (None, hp, (stk, lvars, C, S, pc) # frs) -jvm\<rightarrow> (None, hp', frs')"
apply (simp only: exec_all_def)
apply (rule rtrancl_refl [THEN rtrancl_into_rtrancl])
apply (simp add: gis_def gmb_def)
apply (case_tac frs', simp+)
done

theorem exec_all_one_step: "
  \<lbrakk> gis (gmb G C S) = pre @ (i # post); pc0 = length pre;
  (exec_instr i G hp0 stk0 lvars0 C S pc0 frs) = 
  (None, hp1, (stk1,lvars1,C,S, Suc pc0)#frs) \<rbrakk>
  \<Longrightarrow> 
  G \<turnstile> (None, hp0, (stk0,lvars0,C,S, pc0)#frs) -jvm\<rightarrow> 
  (None, hp1, (stk1,lvars1,C,S, Suc pc0)#frs)"
apply (unfold exec_all_def)
apply (rule r_into_rtrancl)
apply (simp add: gis_def gmb_def split_beta)
done


(***********************************************************************)

constdefs
  progression :: "jvm_prog \<Rightarrow> cname \<Rightarrow> sig \<Rightarrow> 
                 aheap \<Rightarrow> opstack \<Rightarrow> locvars \<Rightarrow>
                 bytecode \<Rightarrow>
                 aheap \<Rightarrow> opstack \<Rightarrow> locvars \<Rightarrow> 
                 bool"
  ("{_,_,_} \<turnstile> {_, _, _} >- _ \<rightarrow> {_, _, _}" [61,61,61,61,61,61,90,61,61,61]60)
  "{G,C,S} \<turnstile> {hp0, os0, lvars0} >- instrs \<rightarrow> {hp1, os1, lvars1} ==
  \<forall> pre post frs.
  (gis (gmb G C S) = pre @ instrs @ post) \<longrightarrow>
   G \<turnstile> (None,hp0,(os0,lvars0,C,S,length pre)#frs) -jvm\<rightarrow>
       (None,hp1,(os1,lvars1,C,S,(length pre) + (length instrs))#frs)"



lemma progression_call: 
  "\<lbrakk> \<forall> pc frs.
  exec_instr instr G hp0 os0 lvars0 C S pc frs =
      (None, hp', (os', lvars', C', S', 0) # (fr pc) # frs) \<and> 
  gis (gmb G C' S') = instrs' @ [Return] \<and> 
  {G, C', S'} \<turnstile> {hp', os', lvars'} >- instrs' \<rightarrow> {hp'', os'', lvars''}  \<and>
  exec_instr Return G hp'' os'' lvars'' C' S' (length instrs') 
                                               ((fr pc) # frs) =
      (None, hp2, (os2, lvars2, C, S, Suc pc) # frs) \<rbrakk> \<Longrightarrow>
  {G, C, S} \<turnstile> {hp0, os0, lvars0} >-[instr]\<rightarrow> {hp2,os2,lvars2}"
apply (simp only: progression_def)
apply (intro strip)
apply (drule_tac x="length pre" in spec)
apply (drule_tac x="frs" in spec)
apply clarify
apply (rule exec_all_trans)
apply (rule exec_instr_in_exec_all) apply simp
apply simp
apply (rule exec_all_trans)
apply (simp only: append_Nil)
apply (drule_tac x="[]" in spec)
apply (simp only: list.simps)
apply blast
apply (rule exec_instr_in_exec_all)
apply auto
done


lemma progression_transitive: 
  "\<lbrakk> instrs_comb = instrs0 @ instrs1; 
  {G, C, S} \<turnstile> {hp0, os0, lvars0} >- instrs0 \<rightarrow> {hp1, os1, lvars1};
  {G, C, S} \<turnstile> {hp1, os1, lvars1} >- instrs1 \<rightarrow> {hp2, os2, lvars2} \<rbrakk>
  \<Longrightarrow>
  {G, C, S} \<turnstile> {hp0, os0, lvars0} >- instrs_comb \<rightarrow> {hp2, os2, lvars2}"
apply (simp only: progression_def)
apply (intro strip)
apply (rule_tac ?s1.0 = "Norm (hp1, (os1, lvars1, C, S, 
                          length pre + length instrs0) # frs)"  
       in exec_all_trans)
apply (simp only: append_assoc)
apply (erule thin_rl, erule thin_rl)
apply (drule_tac x="pre @ instrs0" in spec)
apply (simp add: add_assoc)
done

lemma progression_refl: 
  "{G, C, S} \<turnstile> {hp0, os0, lvars0} >- [] \<rightarrow> {hp0, os0, lvars0}"
apply (simp add: progression_def)
apply (intro strip)
apply (rule exec_all_refl)
done

lemma progression_one_step: "
  \<forall> pc frs. 
  (exec_instr i G hp0 os0 lvars0 C S pc frs) = 
  (None, hp1, (os1,lvars1,C,S, Suc pc)#frs)
  \<Longrightarrow> {G, C, S} \<turnstile> {hp0, os0, lvars0} >- [i] \<rightarrow> {hp1, os1, lvars1}"
apply (unfold progression_def)
apply (intro strip)
apply simp
apply (rule exec_all_one_step)
apply auto
done

(*****)
constdefs
  jump_fwd :: "jvm_prog \<Rightarrow> cname \<Rightarrow> sig \<Rightarrow> 
                 aheap \<Rightarrow> locvars \<Rightarrow> opstack \<Rightarrow> opstack \<Rightarrow> 
                 instr \<Rightarrow> bytecode \<Rightarrow> bool"
  "jump_fwd G C S hp lvars os0 os1 instr instrs ==
  \<forall> pre post frs.
  (gis (gmb G C S) = pre @ instr # instrs @ post) \<longrightarrow>
   exec_all G (None,hp,(os0,lvars,C,S, length pre)#frs)
    (None,hp,(os1,lvars,C,S,(length pre) + (length instrs) + 1)#frs)"


lemma jump_fwd_one_step:
  "\<forall> pc frs.
  exec_instr instr G hp os0 lvars C S pc frs = 
    (None, hp, (os1, lvars, C, S, pc + (length instrs) + 1)#frs)
  \<Longrightarrow> jump_fwd G C S hp lvars os0 os1 instr instrs"
apply (unfold jump_fwd_def)
apply (intro strip)
apply (rule exec_instr_in_exec_all)
apply auto
done


lemma jump_fwd_progression_aux: 
  "\<lbrakk> instrs_comb = instr # instrs0 @ instrs1; 
     jump_fwd G C S hp lvars os0 os1 instr instrs0;
     {G, C, S} \<turnstile> {hp, os1, lvars} >- instrs1 \<rightarrow> {hp2, os2, lvars2} \<rbrakk> 
  \<Longrightarrow> {G, C, S} \<turnstile> {hp, os0, lvars} >- instrs_comb \<rightarrow> {hp2, os2, lvars2}"
apply (simp only: progression_def jump_fwd_def)
apply (intro strip)
apply (rule_tac ?s1.0 = "Norm(hp, (os1, lvars, C, S, length pre + length instrs0 + 1) # frs)" in exec_all_trans)
apply (simp only: append_assoc)
apply (subgoal_tac "pre @ (instr # instrs0 @ instrs1) @ post = pre @ instr # instrs0 @ (instrs1 @ post)")
apply blast
apply simp
apply (erule thin_rl, erule thin_rl)
apply (drule_tac x="pre @ instr # instrs0" in spec)
apply (simp add: add_assoc)
done


lemma jump_fwd_progression:
  "\<lbrakk> instrs_comb = instr # instrs0 @ instrs1; 
  \<forall> pc frs.
  exec_instr instr G hp os0 lvars C S pc frs = 
    (None, hp, (os1, lvars, C, S, pc + (length instrs0) + 1)#frs);
  {G, C, S} \<turnstile> {hp, os1, lvars} >- instrs1 \<rightarrow> {hp2, os2, lvars2} \<rbrakk> 
  \<Longrightarrow> {G, C, S}  \<turnstile> {hp, os0, lvars} >- instrs_comb \<rightarrow> {hp2, os2, lvars2}"
apply (rule jump_fwd_progression_aux)
apply assumption
apply (rule jump_fwd_one_step) apply assumption+
done


(* note: instrs and instr reversed wrt. jump_fwd *)
constdefs
  jump_bwd :: "jvm_prog \<Rightarrow> cname \<Rightarrow> sig \<Rightarrow> 
                 aheap \<Rightarrow> locvars \<Rightarrow> opstack \<Rightarrow> opstack \<Rightarrow> 
                 bytecode \<Rightarrow> instr \<Rightarrow> bool"
  "jump_bwd G C S hp lvars os0 os1 instrs instr ==
  \<forall> pre post frs.
  (gis (gmb G C S) = pre @ instrs @ instr # post) \<longrightarrow>
   exec_all G (None,hp,(os0,lvars,C,S, (length pre) + (length instrs))#frs)
    (None,hp,(os1,lvars,C,S, (length pre))#frs)"


lemma jump_bwd_one_step:
  "\<forall> pc frs.
  exec_instr instr G hp os0 lvars C S (pc + (length instrs)) frs = 
    (None, hp, (os1, lvars, C, S, pc)#frs)
  \<Longrightarrow> 
  jump_bwd G C S hp lvars os0 os1 instrs instr"
apply (unfold jump_bwd_def)
apply (intro strip)
apply (rule exec_instr_in_exec_all)
apply auto
done

lemma jump_bwd_progression: 
  "\<lbrakk> instrs_comb = instrs @ [instr]; 
  {G, C, S} \<turnstile> {hp0, os0, lvars0} >- instrs \<rightarrow> {hp1, os1, lvars1};
  jump_bwd G C S hp1 lvars1 os1 os2 instrs instr;
  {G, C, S} \<turnstile> {hp1, os2, lvars1} >- instrs_comb \<rightarrow> {hp3, os3, lvars3} \<rbrakk> 
  \<Longrightarrow> {G, C, S}  \<turnstile> {hp0, os0, lvars0} >- instrs_comb \<rightarrow> {hp3, os3, lvars3}"
apply (simp only: progression_def jump_bwd_def)
apply (intro strip)
apply (rule exec_all_trans, force)
apply (rule exec_all_trans, force)
apply (rule exec_all_trans, force)
apply simp
apply (rule exec_all_refl)
done


(**********************************************************************)

(* class C with signature S is defined in program G *)
constdefs class_sig_defined :: "'c prog \<Rightarrow> cname \<Rightarrow> sig \<Rightarrow> bool"
  "class_sig_defined G C S == 
  is_class G C \<and> (\<exists> D rT mb. (method (G, C) S = Some (D, rT, mb)))"


(* The environment of a java method body 
  (characterized by class and signature) *)
constdefs env_of_jmb :: "java_mb prog \<Rightarrow> cname \<Rightarrow> sig \<Rightarrow> java_mb env"
  "env_of_jmb G C S == 
  (let (mn,pTs) = S;
       (D,rT,(pns,lvars,blk,res)) = the(method (G, C) S) in
  (G,map_of lvars(pns[\<mapsto>]pTs)(This\<mapsto>Class C)))"

lemma env_of_jmb_fst [simp]: "fst (env_of_jmb G C S) = G"
by (simp add: env_of_jmb_def split_beta)


(**********************************************************************)


lemma method_preserves [rule_format (no_asm)]:
  "\<lbrakk> wf_prog wf_mb G; is_class G C; 
  \<forall> S rT mb. \<forall> cn \<in> fst ` set G. wf_mdecl wf_mb G cn (S,rT,mb)  \<longrightarrow> (P cn S (rT,mb))\<rbrakk>
 \<Longrightarrow> \<forall> D. 
  method (G, C) S = Some (D, rT, mb) \<longrightarrow> (P D S (rT,mb))"

apply (frule wf_prog_ws_prog [THEN wf_subcls1])
apply (rule subcls1_induct, assumption, assumption)

apply (intro strip)
apply ((drule spec)+, drule_tac x="Object" in bspec)
apply (simp add: wf_prog_def ws_prog_def wf_syscls_def)
apply (subgoal_tac "D=Object") apply simp
apply (drule mp)
apply (frule_tac C=Object in method_wf_mdecl)
 apply simp
 apply assumption apply simp apply assumption apply simp

apply (subst method_rec) apply simp
apply force
apply simp
apply (simp only: map_add_def)
apply (split option.split)
apply (rule conjI)
apply force
apply (intro strip)
apply (frule_tac
  ?P1.0 = "wf_mdecl wf_mb G Ca" and
  ?P2.0 = "%(S, (Da, rT, mb)). P Da S (rT, mb)" in map_of_map_prop)
apply (force simp: wf_cdecl_def)

apply clarify

apply (simp only: class_def)
apply (drule map_of_SomeD)+
apply (frule_tac A="set G" and f=fst in imageI, simp)
apply blast
apply simp
done


lemma method_preserves_length:
  "\<lbrakk> wf_java_prog G; is_class G C; 
  method (G, C) (mn,pTs) = Some (D, rT, pns, lvars, blk, res)\<rbrakk>
 \<Longrightarrow> length pns = length pTs"
apply (frule_tac 
  P="%D (mn,pTs) (rT, pns, lvars, blk, res). length pns = length pTs"
  in method_preserves)
apply (auto simp: wf_mdecl_def wf_java_mdecl_def)
done

(**********************************************************************)

constdefs wtpd_expr :: "java_mb env \<Rightarrow> expr \<Rightarrow> bool"
  "wtpd_expr E e == (\<exists> T. E\<turnstile>e :: T)"
  wtpd_exprs :: "java_mb env \<Rightarrow> (expr list) \<Rightarrow> bool"
  "wtpd_exprs E e == (\<exists> T. E\<turnstile>e [::] T)"
  wtpd_stmt :: "java_mb env \<Rightarrow> stmt \<Rightarrow> bool" 
  "wtpd_stmt E c == (E\<turnstile>c \<surd>)"

lemma wtpd_expr_newc: "wtpd_expr E (NewC C) \<Longrightarrow> is_class (prg E) C"
by (simp only: wtpd_expr_def, erule exE, erule ty_expr.cases, auto)

lemma wtpd_expr_cast: "wtpd_expr E (Cast cn e) \<Longrightarrow> (wtpd_expr E e)"
by (simp only: wtpd_expr_def, erule exE, erule ty_expr.cases, auto)

lemma wtpd_expr_lacc: "\<lbrakk> wtpd_expr (env_of_jmb G C S) (LAcc vn);
  class_sig_defined G C S \<rbrakk>
  \<Longrightarrow> vn \<in> set (gjmb_plns (gmb G C S)) \<or> vn = This"
apply (simp only: wtpd_expr_def env_of_jmb_def class_sig_defined_def galldefs)
apply clarify
apply (case_tac S)
apply simp
apply (erule ty_expr.cases)
apply (auto dest: map_upds_SomeD map_of_SomeD fst_in_set_lemma)
apply (drule map_upds_SomeD)
apply (erule disjE)
  apply assumption
  apply (drule map_of_SomeD) apply (auto dest: fst_in_set_lemma)
done

lemma wtpd_expr_lass: "wtpd_expr E (vn::=e)
  \<Longrightarrow> (vn \<noteq> This) & (wtpd_expr E (LAcc vn)) & (wtpd_expr E e)"
by (simp only: wtpd_expr_def, erule exE, erule ty_expr.cases, auto)

lemma wtpd_expr_facc: "wtpd_expr E ({fd}a..fn) 
  \<Longrightarrow> (wtpd_expr E a)"
by (simp only: wtpd_expr_def, erule exE, erule ty_expr.cases, auto)

lemma wtpd_expr_fass: "wtpd_expr E ({fd}a..fn:=v) 
  \<Longrightarrow> (wtpd_expr E ({fd}a..fn)) & (wtpd_expr E v)"
by (simp only: wtpd_expr_def, erule exE, erule ty_expr.cases, auto)


lemma wtpd_expr_binop: "wtpd_expr E (BinOp bop e1 e2)
  \<Longrightarrow> (wtpd_expr E e1) & (wtpd_expr E e2)"
by (simp only: wtpd_expr_def, erule exE, erule ty_expr.cases, auto)

lemma wtpd_exprs_cons: "wtpd_exprs E (e # es)
  \<Longrightarrow> (wtpd_expr E e) & (wtpd_exprs E es)"
by (simp only: wtpd_exprs_def wtpd_expr_def, erule exE, erule ty_exprs.cases, auto)

lemma wtpd_stmt_expr: "wtpd_stmt E (Expr e) \<Longrightarrow> (wtpd_expr E e)"
by (simp only: wtpd_stmt_def wtpd_expr_def, erule wt_stmt.cases, auto)

lemma wtpd_stmt_comp: "wtpd_stmt E (s1;; s2) \<Longrightarrow> 
   (wtpd_stmt E s1) &  (wtpd_stmt E s2)"
by (simp only: wtpd_stmt_def wtpd_expr_def, erule wt_stmt.cases, auto)

lemma wtpd_stmt_cond: "wtpd_stmt E (If(e) s1 Else s2) \<Longrightarrow>
   (wtpd_expr E e) & (wtpd_stmt E s1) &  (wtpd_stmt E s2)
  & (E\<turnstile>e::PrimT Boolean)"
by (simp only: wtpd_stmt_def wtpd_expr_def, erule wt_stmt.cases, auto)

lemma wtpd_stmt_loop: "wtpd_stmt E (While(e) s) \<Longrightarrow>
   (wtpd_expr E e) & (wtpd_stmt E s) & (E\<turnstile>e::PrimT Boolean)"
by (simp only: wtpd_stmt_def wtpd_expr_def, erule wt_stmt.cases, auto)

lemma wtpd_expr_call: "wtpd_expr E ({C}a..mn({pTs'}ps))
  \<Longrightarrow> (wtpd_expr E a) & (wtpd_exprs E ps) 
  & (length ps = length pTs') & (E\<turnstile>a::Class C)
  & (\<exists> pTs md rT. 
       E\<turnstile>ps[::]pTs & max_spec (prg E) C (mn, pTs) = {((md,rT),pTs')})"
apply (simp only: wtpd_expr_def wtpd_exprs_def)
apply (erule exE)
apply (ind_cases "E \<turnstile> {C}a..mn( {pTs'}ps) :: T")
apply (auto simp: max_spec_preserves_length)
done

lemma wtpd_blk: 
  "\<lbrakk> method (G, D) (md, pTs) = Some (D, rT, (pns, lvars, blk, res)); 
  wf_prog wf_java_mdecl G; is_class G D \<rbrakk>
 \<Longrightarrow> wtpd_stmt (env_of_jmb G D (md, pTs)) blk"
apply (simp add: wtpd_stmt_def env_of_jmb_def)
apply (frule_tac P="%D (md, pTs) (rT, (pns, lvars, blk, res)). (G, map_of lvars(pns[\<mapsto>]pTs)(This\<mapsto>Class D)) \<turnstile> blk \<surd> " in method_preserves)
apply (auto simp: wf_mdecl_def wf_java_mdecl_def)
done

lemma wtpd_res: 
  "\<lbrakk> method (G, D) (md, pTs) = Some (D, rT, (pns, lvars, blk, res)); 
  wf_prog wf_java_mdecl G; is_class G D \<rbrakk>
 \<Longrightarrow> wtpd_expr (env_of_jmb G D (md, pTs)) res"
apply (simp add: wtpd_expr_def env_of_jmb_def)
apply (frule_tac P="%D (md, pTs) (rT, (pns, lvars, blk, res)). \<exists>T. (G, map_of lvars(pns[\<mapsto>]pTs)(This\<mapsto>Class D)) \<turnstile> res :: T " in method_preserves)
apply (auto simp: wf_mdecl_def wf_java_mdecl_def)
done


(**********************************************************************)


(* Is there a more elegant proof? *)
lemma evals_preserves_length:
  "G\<turnstile> xs -es[\<succ>]vs-> (None, s) \<Longrightarrow> length es = length vs"
apply (subgoal_tac 
  "\<forall> xs'. (G \<turnstile> xk -xj\<succ>xi-> xh \<longrightarrow> True) & 
  (G\<turnstile> xs -es[\<succ>]vs-> xs' \<longrightarrow>  (\<exists> s. (xs' = (None, s))) \<longrightarrow> 
  length es = length vs) &
  ((xc, xb, xa) \<in> Eval.exec G \<longrightarrow> True)")
apply blast
apply (rule allI)
apply (rule Eval.eval_evals_exec.induct)
apply auto
done

(***********************************************************************)

(* required for translation of BinOp *)


lemma progression_Eq : "{G, C, S} \<turnstile>
  {hp, (v2 # v1 # os), lvars} 
  >- [Ifcmpeq 3, LitPush (Bool False), Goto 2, LitPush (Bool True)] \<rightarrow>
  {hp, (Bool (v1 = v2) # os), lvars}"
apply (case_tac "v1 = v2")

(* case v1 = v2 *)
apply (rule_tac ?instrs1.0 = "[LitPush (Bool True)]" in jump_fwd_progression)
apply (auto simp: nat_add_distrib)
apply (rule progression_one_step) apply simp

(* case v1 \<noteq> v2 *)
apply (rule progression_one_step [THEN HOL.refl [THEN progression_transitive], simplified])
apply auto
apply (rule progression_one_step [THEN HOL.refl [THEN progression_transitive], simplified]) 
apply auto
apply (rule_tac ?instrs1.0 = "[]" in jump_fwd_progression)
apply (auto simp: nat_add_distrib intro: progression_refl)
done


(**********************************************************************)


(* to avoid automatic pair splits *)

declare split_paired_All [simp del] split_paired_Ex [simp del]
ML_setup {*
simpset_ref() := simpset() delloop "split_all_tac"
*}

lemma distinct_method: "\<lbrakk> wf_java_prog G; is_class G C; 
  method (G, C) S = Some (D, rT, pns, lvars, blk, res) \<rbrakk> \<Longrightarrow> 
  distinct (gjmb_plns (gmb G C S))"
apply (frule method_wf_mdecl [THEN conjunct2],  assumption, assumption)
apply (case_tac S)
apply (simp add: wf_mdecl_def wf_java_mdecl_def galldefs distinct_append)
apply (simp add: unique_def map_of_in_set)
apply blast
done

lemma distinct_method_if_class_sig_defined : 
  "\<lbrakk> wf_java_prog G; class_sig_defined G C S \<rbrakk> \<Longrightarrow> 
  distinct (gjmb_plns (gmb G C S))"
by (auto intro: distinct_method simp: class_sig_defined_def)


lemma method_yields_wf_java_mdecl: "\<lbrakk> wf_java_prog G; is_class G C;
  method (G, C) S = Some (D, rT, pns, lvars, blk, res) \<rbrakk>  \<Longrightarrow> 
  wf_java_mdecl G D (S,rT,(pns,lvars,blk,res))"
apply (frule method_wf_mdecl)
apply (auto simp: wf_mdecl_def)
done

(**********************************************************************)


lemma progression_lvar_init_aux [rule_format (no_asm)]: "
  \<forall> zs prfx lvals lvars0. 
  lvars0 =  (zs @ lvars) \<longrightarrow>
  (disjoint_varnames pns lvars0 \<longrightarrow>
  (length lvars = length lvals) \<longrightarrow> 
  (Suc(length pns + length zs) = length prfx) \<longrightarrow> 
   ({cG, D, S} \<turnstile> 
    {h, os, (prfx @ lvals)}
    >- (concat (map (compInit (pns, lvars0, blk, res)) lvars)) \<rightarrow>
    {h, os, (prfx @ (map (\<lambda>p. (default_val (snd p))) lvars))}))"
apply simp
apply (induct lvars)
apply (clarsimp, rule progression_refl)
apply (intro strip)
apply (case_tac lvals) apply simp
apply (simp (no_asm_simp) )

apply (rule_tac ?lvars1.0 = "(prfx @ [default_val (snd a)]) @ lista" in progression_transitive, rule HOL.refl)
apply (case_tac a) apply (simp (no_asm_simp) add: compInit_def)
apply (rule_tac ?instrs0.0 = "[load_default_val b]" in progression_transitive, simp)
apply (rule progression_one_step)
apply (simp (no_asm_simp) add: load_default_val_def)
apply (rule conjI, simp)+ apply (rule HOL.refl)

apply (rule progression_one_step)
apply (simp (no_asm_simp))
apply (rule conjI, simp)+
apply (simp add: index_of_var2)
apply (drule_tac x="zs @ [a]" in spec) (* instantiate zs *)
apply (drule mp, simp)
apply (drule_tac x="(prfx @ [default_val (snd a)])" in spec) (* instantiate prfx *)
apply auto
done

lemma progression_lvar_init [rule_format (no_asm)]: 
  "\<lbrakk> wf_java_prog G; is_class G C;
  method (G, C) S = Some (D, rT, pns, lvars, blk, res) \<rbrakk> \<Longrightarrow> 
  length pns = length pvs \<longrightarrow> 
  (\<forall> lvals. 
  length lvars = length lvals \<longrightarrow>
   {cG, D, S} \<turnstile>
   {h, os, (a' # pvs @ lvals)}
   >- (compInitLvars (pns, lvars, blk, res) lvars) \<rightarrow>
   {h, os, (locvars_xstate G C S (Norm (h, init_vars lvars(pns[\<mapsto>]pvs)(This\<mapsto>a'))))})"
apply (simp only: compInitLvars_def)
apply (frule method_yields_wf_java_mdecl, assumption, assumption)

apply (simp only: wf_java_mdecl_def)
apply (subgoal_tac "(\<forall>y\<in>set pns. y \<notin> set (map fst lvars))")
apply (simp add: init_vars_def locvars_xstate_def locvars_locals_def galldefs unique_def split_def map_of_map_as_map_upd)
apply (intro strip)
apply (simp (no_asm_simp) only: append_Cons [THEN sym])
apply (rule progression_lvar_init_aux)
apply (auto simp: unique_def map_of_in_set disjoint_varnames_def)
done




(**********************************************************************)

lemma state_ok_eval: "\<lbrakk>xs::\<preceq>E; wf_java_prog (prg E); wtpd_expr E e;
  (prg E)\<turnstile>xs -e\<succ>v -> xs'\<rbrakk> \<Longrightarrow>  xs'::\<preceq>E"
apply (simp only: wtpd_expr_def)
apply (erule exE)
apply (case_tac xs', case_tac xs)
apply (auto intro: eval_type_sound [THEN conjunct1])
done

lemma state_ok_evals: "\<lbrakk>xs::\<preceq>E; wf_java_prog (prg E); wtpd_exprs E es;
  (xs,es,vs,xs') \<in> Eval.evals (prg E)\<rbrakk> \<Longrightarrow> xs'::\<preceq>E"
apply (simp only: wtpd_exprs_def)
apply (erule exE)
apply (case_tac xs) apply (case_tac xs')
apply (auto intro: evals_type_sound [THEN conjunct1])
done

lemma state_ok_exec: "\<lbrakk>xs::\<preceq>E; wf_java_prog (prg E); wtpd_stmt E st;
  (xs,st,xs') \<in> Eval.exec (prg E)\<rbrakk> \<Longrightarrow>  xs'::\<preceq>E"
apply (simp only: wtpd_stmt_def)
apply (case_tac xs', case_tac xs)
apply (auto dest: exec_type_sound)
done


lemma state_ok_init: 
  "\<lbrakk> wf_java_prog G; (x, h, l)::\<preceq>(env_of_jmb G C S); 
  is_class G dynT;
  method (G, dynT) (mn, pTs) = Some (md, rT, pns, lvars, blk, res);
  list_all2 (conf G h) pvs pTs; G,h \<turnstile> a' ::\<preceq> Class md\<rbrakk>
\<Longrightarrow>
(np a' x, h, init_vars lvars(pns[\<mapsto>]pvs)(This\<mapsto>a'))::\<preceq>(env_of_jmb G md (mn, pTs))"
apply (frule wf_prog_ws_prog)
apply (frule method_in_md [THEN conjunct2], assumption+)
apply (frule method_yields_wf_java_mdecl, assumption, assumption)
apply (simp add: env_of_jmb_def gs_def conforms_def split_beta)
apply (simp add: wf_java_mdecl_def)
apply (rule conjI)
apply (rule lconf_ext)
apply (rule lconf_ext_list)
apply (rule lconf_init_vars)
apply (auto dest: Ball_set_table)
apply (simp add: np_def xconf_raise_if)
done


lemma ty_exprs_list_all2 [rule_format (no_asm)]: 
  "(\<forall> Ts. (E \<turnstile> es [::] Ts) = list_all2 (\<lambda>e T. E \<turnstile> e :: T) es Ts)"
apply (rule list.induct)
apply simp
apply (rule allI)
apply (rule iffI)
  apply (ind_cases "E \<turnstile> [] [::] Ts", assumption)
  apply simp apply (rule WellType.Nil)
apply (simp add: list_all2_Cons1)
apply (rule allI)
apply (rule iffI)
  apply (rename_tac a exs Ts)
  apply (ind_cases "E \<turnstile> a # exs  [::] Ts") apply blast
  apply (auto intro: WellType.Cons)
done


lemma conf_bool: "G,h \<turnstile> v::\<preceq>PrimT Boolean \<Longrightarrow> \<exists> b. v = Bool b"
apply (simp add: conf_def)
apply (erule exE)
apply (case_tac v)
apply (auto elim: widen.cases)
done


lemma class_expr_is_class: "\<lbrakk>E \<turnstile> e :: Class C; ws_prog (prg E)\<rbrakk> 
  \<Longrightarrow> is_class (prg E) C"
by (case_tac E, auto dest: ty_expr_is_type)


lemma max_spec_widen: "max_spec G C (mn, pTs) = {((md,rT),pTs')} \<Longrightarrow> 
  list_all2 (\<lambda> T T'. G \<turnstile> T \<preceq> T') pTs pTs'"
by (blast dest: singleton_in_set max_spec2appl_meths appl_methsD)


lemma eval_conf: "\<lbrakk>G \<turnstile> s -e\<succ>v-> s'; wf_java_prog G; s::\<preceq>E;
  E\<turnstile>e::T; gx s' = None; prg E = G \<rbrakk> 
  \<Longrightarrow> G,gh s'\<turnstile>v::\<preceq>T"
apply (simp add: gh_def)
apply (rule_tac x3="fst s" and s3="snd s"and x'3="fst s'"  
  in eval_type_sound [THEN conjunct2 [THEN conjunct1 [THEN mp]], simplified])
apply assumption+
apply (simp (no_asm_use) add: surjective_pairing [THEN sym])
apply (simp only: surjective_pairing [THEN sym])
apply (auto simp add: gs_def gx_def)
done

lemma evals_preserves_conf:
  "\<lbrakk> G\<turnstile> s -es[\<succ>]vs-> s'; G,gh s \<turnstile> t ::\<preceq> T; E \<turnstile>es[::]Ts;
  wf_java_prog G; s::\<preceq>E; 
  prg E = G \<rbrakk> \<Longrightarrow> G,gh s' \<turnstile> t ::\<preceq> T"
apply (subgoal_tac "gh s\<le>| gh s'")
apply (frule conf_hext, assumption, assumption)
apply (frule eval_evals_exec_type_sound [THEN conjunct2 [THEN conjunct1 [THEN mp]]]) 
apply (subgoal_tac "G \<turnstile> (gx s, (gh s, gl s)) -es[\<succ>]vs-> (gx s', (gh s', gl s'))")
apply assumption
apply (simp add: gx_def gh_def gl_def surjective_pairing [THEN sym])
apply (case_tac E)
apply (simp add: gx_def gs_def gh_def gl_def surjective_pairing [THEN sym])
done

lemma eval_of_class: "\<lbrakk> G \<turnstile> s -e\<succ>a'-> s'; E \<turnstile> e :: Class C; 
  wf_java_prog G; s::\<preceq>E; gx s'=None; a' \<noteq> Null; G=prg E\<rbrakk>
  \<Longrightarrow> (\<exists> lc. a' = Addr lc)"
apply (case_tac s, case_tac s', simp)
apply (frule eval_type_sound, (simp add: gs_def)+)
apply (case_tac a')
apply (auto simp: conf_def)
done


lemma dynT_subcls: 
  "\<lbrakk> a' \<noteq> Null; G,h\<turnstile>a'::\<preceq> Class C; dynT = fst (the (h (the_Addr a')));
  is_class G dynT; ws_prog G \<rbrakk> \<Longrightarrow> G\<turnstile>dynT \<preceq>C C"
apply (case_tac "C = Object")
apply (simp, rule subcls_C_Object, assumption+)
apply simp
apply (frule non_np_objD, auto)
done


lemma method_defined: "\<lbrakk> 
  m = the (method (G, dynT) (mn, pTs)); 
  dynT = fst (the (h a)); is_class G dynT; wf_java_prog G; 
  a' \<noteq> Null; G,h\<turnstile>a'::\<preceq> Class C; a = the_Addr a';
  \<exists>pTsa md rT. max_spec G C (mn, pTsa) = {((md, rT), pTs)} \<rbrakk>
\<Longrightarrow> (method (G, dynT) (mn, pTs)) = Some m"
apply (erule exE)+
apply (drule singleton_in_set, drule max_spec2appl_meths)
apply (simp add: appl_methds_def)
apply ((erule exE)+, (erule conjE)+, (erule exE)+)
apply (drule widen_methd)
apply assumption
apply (rule dynT_subcls) apply assumption+ apply simp apply simp
apply (erule exE)+ apply simp
done



(**********************************************************************)


(* 1. any difference between locvars_xstate \<dots> and L ??? *)
(* 2. possibly skip env_of_jmb ??? *)
theorem compiler_correctness: 
  "wf_java_prog G \<Longrightarrow>
  ((xs,ex,val,xs') \<in> Eval.eval G \<longrightarrow>
  gx xs = None \<longrightarrow> gx xs' = None \<longrightarrow>
  (\<forall> os CL S.
  (class_sig_defined G CL S) \<longrightarrow> 
  (wtpd_expr (env_of_jmb G CL S) ex) \<longrightarrow>
  (xs ::\<preceq> (env_of_jmb G CL S)) \<longrightarrow>
  ( {TranslComp.comp G, CL, S} \<turnstile>
    {gh xs, os, (locvars_xstate G CL S xs)}
    >- (compExpr (gmb G CL S) ex) \<rightarrow>
    {gh xs', val#os, locvars_xstate G CL S xs'}))) \<and> 

 ((xs,exs,vals,xs') \<in> Eval.evals G \<longrightarrow>
  gx xs = None \<longrightarrow> gx xs' = None \<longrightarrow>
  (\<forall> os CL S.
  (class_sig_defined G CL S) \<longrightarrow> 
  (wtpd_exprs (env_of_jmb G CL S) exs) \<longrightarrow>
  (xs::\<preceq>(env_of_jmb G CL S)) \<longrightarrow>
  ( {TranslComp.comp G, CL, S} \<turnstile>
    {gh xs, os, (locvars_xstate G CL S xs)}
    >- (compExprs (gmb G CL S) exs) \<rightarrow>
    {gh xs', (rev vals)@os, (locvars_xstate G CL S xs')}))) \<and> 

  ((xs,st,xs') \<in> Eval.exec G \<longrightarrow>
   gx xs = None \<longrightarrow> gx xs' = None \<longrightarrow>
  (\<forall> os CL S.
  (class_sig_defined G CL S) \<longrightarrow> 
  (wtpd_stmt (env_of_jmb G CL S) st) \<longrightarrow>
  (xs::\<preceq>(env_of_jmb G CL S)) \<longrightarrow>
  ( {TranslComp.comp G, CL, S} \<turnstile>
    {gh xs, os, (locvars_xstate G CL S xs)}
    >- (compStmt (gmb G CL S) st) \<rightarrow>
    {gh xs', os, (locvars_xstate G CL S xs')})))"
apply (rule Eval.eval_evals_exec.induct)

(* case XcptE *)
apply simp

(* case NewC *) 
apply clarify 
apply (frule wf_prog_ws_prog [THEN wf_subcls1]) (* establish  wf ((subcls1 G)^-1) *)
apply (simp add: c_hupd_hp_invariant)
apply (rule progression_one_step)
apply (rotate_tac 1, drule sym) (* reverse equation (a, None) = new_Addr (fst s) *)
apply (simp add: locvars_xstate_def locvars_locals_def comp_fields)


(* case Cast *)
apply (intro allI impI)
apply simp
apply (frule raise_if_NoneD)
apply (frule wtpd_expr_cast)
apply simp
apply (rule_tac ?instrs0.0 = "(compExpr (gmb G CL S) e)" in progression_transitive, simp)
apply blast
apply (rule progression_one_step)
apply (simp add: raise_system_xcpt_def  gh_def comp_cast_ok)


(* case Lit *)
apply simp
apply (intro strip)
apply (rule progression_one_step)
apply simp


(* case BinOp *)
apply (intro allI impI)
apply (frule_tac xs=s1 in eval_xcpt, assumption) (* establish (gx s1 = None) *)
apply (frule wtpd_expr_binop)
(* establish (s1::\<preceq> \<dots>) *)
apply (frule_tac e=e1 in state_ok_eval) apply (simp (no_asm_simp)) apply simp apply (simp (no_asm_use) only: env_of_jmb_fst) 


apply (simp (no_asm_use) only: compExpr_compExprs.simps)
apply (rule_tac ?instrs0.0 = "compExpr (gmb G CL S) e1" in progression_transitive, simp) apply blast
apply (rule_tac ?instrs0.0 = "compExpr (gmb G CL S) e2" in progression_transitive, simp) apply blast
apply (case_tac bop)
  (*subcase bop = Eq *)  apply simp apply (rule progression_Eq)
  (*subcase bop = Add *) apply simp apply (rule progression_one_step) apply simp


(* case LAcc *)
apply simp
apply (intro strip)
apply (rule progression_one_step)
apply (simp add: locvars_xstate_def locvars_locals_def)
apply (frule wtpd_expr_lacc)
apply assumption
apply (simp add: gl_def)
apply (erule select_at_index)


(* case LAss *)
apply (intro allI impI)
apply (frule wtpd_expr_lass, erule conjE, erule conjE)
apply (simp add: compExpr_compExprs.simps)

apply (rule_tac ?instrs0.0 = "(compExpr (gmb G CL S) e)" in progression_transitive, rule HOL.refl)
apply blast

apply (rule_tac ?instrs0.0 = "[Dup]" in progression_transitive, simp)
apply (rule progression_one_step)
apply (simp add: gh_def)
apply (rule conjI, simp)+ apply simp
apply (rule progression_one_step)
apply (simp add: gh_def)
(* the following falls out of the general scheme *)
apply (frule wtpd_expr_lacc) apply assumption
apply (rule update_at_index)
apply (rule distinct_method_if_class_sig_defined) apply assumption
apply assumption apply simp apply assumption


(* case FAcc *)
apply (intro allI impI)
   (* establish x1 = None \<and> a' \<noteq> Null *)
apply (simp (no_asm_use) only: gx_conv, frule np_NoneD)
apply (frule wtpd_expr_facc)

apply (simp (no_asm_use) only: compExpr_compExprs.simps)
apply (rule_tac ?instrs0.0 = "(compExpr (gmb G CL S) e)" in progression_transitive, rule HOL.refl)
apply blast
apply (rule progression_one_step)
apply (simp add: gh_def)
apply (case_tac "(the (fst s1 (the_Addr a')))")
apply (simp add: raise_system_xcpt_def)


(* case FAss *)
apply (intro allI impI)
apply (frule wtpd_expr_fass) apply (erule conjE) apply (frule wtpd_expr_facc)
apply (simp only: c_hupd_xcpt_invariant) (* establish x2 = None *)
   (* establish x1 = None  and  a' \<noteq> Null  *)
apply (frule_tac xs="(np a' x1, s1)" in eval_xcpt)
apply (simp only: gx_conv, simp only: gx_conv, frule np_NoneD, erule conjE)


  (* establish ((Norm s1)::\<preceq> \<dots>) *)
apply (frule_tac e=e1 in state_ok_eval) apply (simp (no_asm_simp) only: env_of_jmb_fst) 
   apply assumption apply (simp (no_asm_use) only: env_of_jmb_fst) 

apply (simp only: compExpr_compExprs.simps)

apply (rule_tac ?instrs0.0 = "(compExpr (gmb G CL S) e1)" in progression_transitive, rule HOL.refl)
apply fast (* blast does not seem to work - why? *)
apply (rule_tac ?instrs0.0 = "(compExpr (gmb G CL S) e2)" in progression_transitive, rule HOL.refl)
apply fast
apply (rule_tac ?instrs0.0 = "[Dup_x1]" and ?instrs1.0 = "[Putfield fn T]" in progression_transitive, simp)

   (* Dup_x1 *)
   apply (rule progression_one_step)
   apply (simp add: gh_def)
   apply (rule conjI, simp)+ apply simp


   (* Putfield \<longrightarrow> still looks nasty*)
   apply (rule progression_one_step)
   apply simp
   apply (case_tac "(the (fst s2 (the_Addr a')))")
   apply (simp add: c_hupd_hp_invariant)
   apply (case_tac s2)
   apply (simp add: c_hupd_conv raise_system_xcpt_def)
   apply (rule locvars_xstate_par_dep, rule HOL.refl)

defer (* method call *)

(* case XcptEs *)
apply simp

(* case Nil *)
apply (simp add: compExpr_compExprs.simps)
apply (intro strip)
apply (rule progression_refl)

(* case Cons *)
apply (intro allI impI)
apply (frule_tac xs=s1 in evals_xcpt, simp only: gx_conv) (* establish gx s1 = None *)
apply (frule wtpd_exprs_cons)
   (* establish ((Norm s0)::\<preceq> \<dots>) *)
apply (frule_tac e=e in state_ok_eval) apply (simp (no_asm_simp) only: env_of_jmb_fst) apply simp apply (simp (no_asm_use) only: env_of_jmb_fst)

apply simp
apply (rule_tac ?instrs0.0 = "(compExpr (gmb G CL S) e)" in progression_transitive, rule HOL.refl)
apply fast
apply fast


(* case Statement: exception *)
apply simp

(* case Skip *)
apply (intro allI impI)
apply simp
apply (rule progression_refl)

(* case Expr *)
apply (intro allI impI)
apply (frule wtpd_stmt_expr)
apply simp
apply (rule_tac ?instrs0.0 = "(compExpr (gmb G CL S) e)" in progression_transitive, rule HOL.refl)
apply fast
apply (rule progression_one_step)
apply simp

(* case Comp *)
apply (intro allI impI)
apply (frule_tac xs=s1 in exec_xcpt, assumption) (* establish (gx s1 = None) *)
apply (frule wtpd_stmt_comp)

  (* establish (s1::\<preceq> \<dots>) *)
apply (frule_tac st=c1 in state_ok_exec) apply (simp (no_asm_simp) only: env_of_jmb_fst) apply simp apply (simp (no_asm_use) only: env_of_jmb_fst)

apply simp
apply (rule_tac ?instrs0.0 = "(compStmt (gmb G CL S) c1)" in progression_transitive, rule HOL.refl)
apply fast
apply fast


(* case Cond *)
apply (intro allI impI)
apply (frule_tac xs=s1 in exec_xcpt, assumption) (* establish (gx s1 = None) *)
apply (frule wtpd_stmt_cond, (erule conjE)+)
(* establish (s1::\<preceq> \<dots>) *)
apply (frule_tac e=e in state_ok_eval) 
apply (simp (no_asm_simp) only: env_of_jmb_fst)
apply assumption 
apply (simp (no_asm_use) only: env_of_jmb_fst) 
(* establish G,gh s1\<turnstile>v::\<preceq>PrimT Boolean *)
apply (frule eval_conf, assumption+, rule env_of_jmb_fst)
apply (frule conf_bool) (* establish \<exists>b. v = Bool b *)
apply (erule exE)

apply simp
apply (rule_tac ?instrs0.0 = "[LitPush (Bool False)]" in progression_transitive, simp (no_asm_simp))
apply (rule progression_one_step,  simp)
apply (rule conjI, rule HOL.refl)+ apply (rule HOL.refl)

apply (rule_tac ?instrs0.0 = "compExpr (gmb G CL S) e" in progression_transitive, rule HOL.refl)
apply fast

apply (case_tac b)
 (* case b= True *)
apply simp
apply (rule_tac ?instrs0.0 = "[Ifcmpeq (2 + int (length (compStmt (gmb G CL S) c1)))]" in progression_transitive, simp)
apply (rule progression_one_step) apply simp
apply (rule conjI, rule HOL.refl)+ apply (rule HOL.refl)
apply (rule_tac ?instrs0.0 = "(compStmt (gmb G CL S) c1)" in progression_transitive, simp)
apply fast
apply (rule_tac ?instrs1.0 = "[]" in jump_fwd_progression)
apply (simp, rule conjI, (rule HOL.refl)+)
apply simp apply (rule conjI, simp) apply (simp add: nat_add_distrib)
apply (rule progression_refl)

 (* case b= False *)
apply simp
apply (rule_tac ?instrs1.0 = "compStmt (gmb G CL S) c2" in jump_fwd_progression)
apply (simp, rule conjI, (rule HOL.refl)+)
apply (simp, rule conjI, rule HOL.refl, simp add: nat_add_distrib)
apply fast

(* case exit Loop *)
apply (intro allI impI)
apply (frule wtpd_stmt_loop, (erule conjE)+)

(* establish G,gh s1\<turnstile>v::\<preceq>PrimT Boolean *)
apply (frule eval_conf, assumption+, rule env_of_jmb_fst)
apply (frule conf_bool) (* establish \<exists>b. v = Bool b *)
apply (erule exE)
apply (case_tac b)

 (* case b= True \<longrightarrow> contradiction *)
apply simp

 (* case b= False *)
apply simp

apply (rule_tac ?instrs0.0 = "[LitPush (Bool False)]" in progression_transitive, simp (no_asm_simp))
apply (rule progression_one_step)
   apply simp 
   apply (rule conjI, rule HOL.refl)+ apply (rule HOL.refl)

apply (rule_tac ?instrs0.0 = "compExpr (gmb G CL S) e" in progression_transitive, rule HOL.refl)
apply fast
apply (rule_tac ?instrs1.0 = "[]" in jump_fwd_progression)
apply (simp, rule conjI, rule HOL.refl, rule HOL.refl)
apply (simp, rule conjI, rule HOL.refl, simp add: nat_add_distrib)
apply (rule progression_refl)


(* case continue Loop *)
apply (intro allI impI)
apply (frule_tac xs=s2 in exec_xcpt, assumption) (* establish (gx s2 = None) *)
apply (frule_tac xs=s1 in exec_xcpt, assumption) (* establish (gx s1 = None) *)
apply (frule wtpd_stmt_loop, (erule conjE)+)

(* establish (s1::\<preceq> \<dots>) *)
apply (frule_tac e=e in state_ok_eval) apply (simp (no_asm_simp) only: env_of_jmb_fst) apply simp apply (simp (no_asm_use) only: env_of_jmb_fst)
(* establish (s2::\<preceq> \<dots>) *)
apply (frule_tac xs=s1 and st=c in state_ok_exec)
apply (simp (no_asm_simp) only: env_of_jmb_fst) apply assumption apply (simp (no_asm_use) only: env_of_jmb_fst)

(* establish G,gh s1\<turnstile>v::\<preceq>PrimT Boolean *)
apply (frule eval_conf, assumption+, rule env_of_jmb_fst)
apply (frule conf_bool) (* establish \<exists>b. v = Bool b *)
apply (erule exE)

apply simp
apply (rule jump_bwd_progression) 
apply simp
apply (rule conjI, (rule HOL.refl)+)

apply (rule_tac ?instrs0.0 = "[LitPush (Bool False)]" in progression_transitive, simp (no_asm_simp))
apply (rule progression_one_step)
   apply simp 
   apply (rule conjI, simp)+ apply simp

apply (rule_tac ?instrs0.0 = "compExpr (gmb G CL S) e" in progression_transitive, rule HOL.refl)
apply fast

apply (case_tac b)
 (* case b= True *)
apply simp

apply (rule_tac ?instrs0.0 = "[Ifcmpeq (2 + int (length (compStmt (gmb G CL S) c)))]" in progression_transitive, simp)
apply (rule progression_one_step) apply simp
apply (rule conjI, rule HOL.refl)+ apply (rule HOL.refl)
apply fast

 (* case b= False \<longrightarrow> contradiction*)
apply simp

apply (rule jump_bwd_one_step)
apply simp
apply blast

(*****)
(* case method call *)

apply (intro allI impI)

apply (frule_tac xs=s3 in eval_xcpt, simp only: gx_conv) (* establish gx s3 = None *)
apply (frule exec_xcpt, assumption, simp (no_asm_use) only: gx_conv, frule np_NoneD) (* establish x = None \<and> a' \<noteq> Null *)
apply (frule evals_xcpt, simp only: gx_conv) (* establish gx s1 = None *)

apply (frule wtpd_expr_call, (erule conjE)+)


(* assumptions about state_ok and is_class *)

(* establish s1::\<preceq> (env_of_jmb G CL S) *)
apply (frule_tac xs="Norm s0" and e=e in state_ok_eval)
apply (simp (no_asm_simp) only: env_of_jmb_fst, assumption, simp (no_asm_use) only: env_of_jmb_fst)

(* establish (x, h, l)::\<preceq>(env_of_jmb G CL S) *)
apply (frule_tac xs=s1 and xs'="(x, h, l)" in state_ok_evals)
apply (simp (no_asm_simp) only: env_of_jmb_fst, assumption, simp only: env_of_jmb_fst)

(* establish \<exists> lc. a' = Addr lc *)
apply (frule (5) eval_of_class, rule env_of_jmb_fst [THEN sym])
apply (subgoal_tac "G,h \<turnstile> a' ::\<preceq> Class C")
apply (subgoal_tac "is_class G dynT")

(* establish method (G, dynT) (mn, pTs) = Some(md, rT, pns, lvars, blk, res) *)
apply (drule method_defined, assumption+)
apply (simp only: env_of_jmb_fst)
apply ((erule exE)+, erule conjE, (rule exI)+, assumption) 

apply (subgoal_tac "is_class G md")
apply (subgoal_tac "G\<turnstile>Class dynT \<preceq> Class md")
apply (subgoal_tac " method (G, md) (mn, pTs) = Some (md, rT, pns, lvars, blk, res)")
apply (subgoal_tac "list_all2 (conf G h) pvs pTs")

(* establish (np a' x, h, init_vars lvars(pns[\<mapsto>]pvs)(This\<mapsto>a'))::\<preceq>(env_of_jmb G md (mn, pTs)) *)
apply (subgoal_tac "G,h \<turnstile> a' ::\<preceq> Class dynT")
apply (frule (2) conf_widen)
apply (frule state_ok_init, assumption+)

apply (subgoal_tac "class_sig_defined G md (mn, pTs)")
apply (frule wtpd_blk, assumption, assumption)
apply (frule wtpd_res, assumption, assumption)
apply (subgoal_tac "s3::\<preceq>(env_of_jmb G md (mn, pTs))")

apply (subgoal_tac "method (TranslComp.comp G, md) (mn, pTs) =
          Some (md, rT, snd (snd (compMethod G md ((mn, pTs), rT, pns, lvars, blk, res))))")
prefer 2 apply (simp add: wf_prog_ws_prog [THEN comp_method])
apply (subgoal_tac "method (TranslComp.comp G, dynT) (mn, pTs) =
          Some (md, rT, snd (snd (compMethod G md ((mn, pTs), rT, pns, lvars, blk, res))))")
prefer 2 apply (simp add: wf_prog_ws_prog [THEN comp_method])
 apply (simp only: fst_conv snd_conv)

(* establish length pns = length pTs *)
apply (frule method_preserves_length, assumption, assumption) 
(* establish length pvs = length ps *)
apply (frule evals_preserves_length [THEN sym])

(** start evaluating subexpressions **)
apply (simp (no_asm_use) only: compExpr_compExprs.simps)

  (* evaluate e *)
apply (rule_tac ?instrs0.0 = "(compExpr (gmb G CL S) e)" in progression_transitive, rule HOL.refl)
apply fast

  (* evaluate parameters *)
apply (rule_tac ?instrs0.0 = "compExprs (gmb G CL S) ps" in progression_transitive, rule HOL.refl)
apply fast

  (* invokation *)
apply (rule progression_call)
apply (intro allI impI conjI)
     (* execute Invoke statement *)
apply (simp (no_asm_use) only: exec_instr.simps)
apply (erule thin_rl, erule thin_rl, erule thin_rl)
apply (simp add: compMethod_def raise_system_xcpt_def)
apply (rule conjI, simp)+ apply (rule HOL.refl)

     (* get instructions of invoked method *)
apply (simp (no_asm_simp) add: gis_def gmb_def compMethod_def)

       (* var. initialization *)
apply (rule_tac ?instrs0.0 = "(compInitLvars (pns, lvars, blk, res) lvars)" in progression_transitive, rule HOL.refl)
apply (rule_tac C=md in progression_lvar_init, assumption, assumption, assumption)
apply (simp (no_asm_simp)) (* length pns = length pvs *)
apply (simp (no_asm_simp)) (* length lvars = length (replicate (length lvars) arbitrary) *)


       (* body statement *)
apply (rule_tac ?instrs0.0 = "compStmt (pns, lvars, blk, res) blk" in progression_transitive, rule HOL.refl)
apply (subgoal_tac "(pns, lvars, blk, res) = gmb G md (mn, pTs)")
apply (simp (no_asm_simp))
apply (simp only: gh_conv)
apply ((drule mp, rule TrueI)+, (drule spec)+, (drule mp, assumption)+, assumption)
apply (simp (no_asm_use))
apply (simp (no_asm_simp) add: gmb_def)

       (* return expression *) 
apply (subgoal_tac "(pns, lvars, blk, res) = gmb G md (mn, pTs)")
apply (simp (no_asm_simp))
apply (simp only: gh_conv)
apply ((drule mp, rule TrueI)+, (drule spec)+, (drule mp, assumption)+, assumption)
apply (simp (no_asm_use))
apply (simp (no_asm_simp) add: gmb_def)

      (* execute return statement *)
apply (simp (no_asm_use) add: gh_def locvars_xstate_def gl_def del: drop_append)
apply (subgoal_tac "rev pvs @ a' # os = (rev (a' # pvs)) @ os")
apply (simp only: drop_append)
apply (simp (no_asm_simp))
apply (simp (no_asm_simp))

(* show s3::\<preceq>\<dots> *)
apply (rule_tac xs = "(np a' x, h, init_vars lvars(pns[\<mapsto>]pvs)(This\<mapsto>a'))" and st=blk in state_ok_exec)
apply assumption apply (simp (no_asm_simp) only: env_of_jmb_fst) 
apply assumption apply (simp (no_asm_use) only: env_of_jmb_fst)

(* show class_sig_defined G md (mn, pTs) *)
apply (simp (no_asm_simp) add: class_sig_defined_def)

(* show G,h \<turnstile> a' ::\<preceq> Class dynT *)
apply (frule non_npD) apply assumption
apply (erule exE)+ apply simp
apply (rule conf_obj_AddrI) apply simp 
apply (rule conjI, (rule HOL.refl)+)
apply (rule widen_Class_Class [THEN iffD1], rule widen.refl)


  (* show list_all2 (conf G h) pvs pTs *)
apply (erule exE)+ apply (erule conjE)+
apply (rule_tac Ts="pTsa" in conf_list_gext_widen) apply assumption
apply (subgoal_tac "((gx s1, gs s1), ps, pvs, x, h, l) \<in> evals G")
apply (frule_tac E="env_of_jmb G CL S" in evals_type_sound)
apply assumption+
apply (simp only: env_of_jmb_fst) 
apply (simp add: conforms_def xconf_def gs_def)
apply simp
apply (simp (no_asm_use) only: gx_def gs_def surjective_pairing [THEN sym])
apply (simp (no_asm_use) only: ty_exprs_list_all2) apply simp
apply simp
apply (simp (no_asm_use) only: gx_def gs_def surjective_pairing [THEN sym])
    (* list_all2 (\<lambda>T T'. G \<turnstile> T \<preceq> T') pTsa pTs *)
    apply (rule max_spec_widen, simp only: env_of_jmb_fst)


(* show method (G, md) (mn, pTs) = Some (md, rT, pns, lvars, blk, res) *)
apply (frule wf_prog_ws_prog [THEN method_in_md [THEN conjunct2]], assumption+)

  (* show G\<turnstile>Class dynT \<preceq> Class md *)
apply (simp (no_asm_use) only: widen_Class_Class)
apply (rule method_wf_mdecl [THEN conjunct1], assumption+)

  (* is_class G md *)
apply (rule wf_prog_ws_prog [THEN method_in_md [THEN conjunct1]], assumption+)

  (* show is_class G dynT *)
apply (frule non_npD) apply assumption
apply (erule exE)+ apply (erule conjE)+
apply simp
apply (rule subcls_is_class2) apply assumption
apply (frule class_expr_is_class) apply (simp only: env_of_jmb_fst)
apply (rule wf_prog_ws_prog, assumption)
apply (simp only: env_of_jmb_fst)

 (* show G,h \<turnstile> a' ::\<preceq> Class C *)
apply (simp only: wtpd_exprs_def, erule exE)
apply (frule evals_preserves_conf)
apply (rule eval_conf, assumption+)
apply (rule env_of_jmb_fst, assumption+)
apply (rule env_of_jmb_fst)
apply (simp only: gh_conv)
done


theorem compiler_correctness_eval: "
  \<lbrakk> G \<turnstile> (None,hp,loc) -ex \<succ> val-> (None,hp',loc');
  wf_java_prog G;
  class_sig_defined G C S;
  wtpd_expr (env_of_jmb G C S) ex;
  (None,hp,loc) ::\<preceq> (env_of_jmb G C S) \<rbrakk> \<Longrightarrow>
  {(TranslComp.comp G), C, S} \<turnstile> 
    {hp, os, (locvars_locals G C S loc)}
      >- (compExpr (gmb G C S) ex) \<rightarrow> 
    {hp', val#os, (locvars_locals G C S loc')}"
apply (frule compiler_correctness [THEN conjunct1])
apply (auto simp: gh_def gx_def gs_def gl_def locvars_xstate_def)
done

theorem compiler_correctness_exec: "
  \<lbrakk> ((None,hp,loc), st, (None,hp',loc')) \<in> Eval.exec G;
  wf_java_prog G;
  class_sig_defined G C S;
  wtpd_stmt (env_of_jmb G C S) st;
  (None,hp,loc) ::\<preceq> (env_of_jmb G C S) \<rbrakk> \<Longrightarrow>
  {(TranslComp.comp G), C, S} \<turnstile> 
    {hp, os, (locvars_locals G C S loc)}
      >- (compStmt (gmb G C S) st) \<rightarrow>
    {hp', os, (locvars_locals G C S loc')}"
apply (frule compiler_correctness [THEN conjunct2 [THEN conjunct2]])
apply (auto simp: gh_def gx_def gs_def gl_def locvars_xstate_def)
done

(**********************************************************************)


(* reinstall pair splits *)
declare split_paired_All [simp] split_paired_Ex [simp]
ML_setup {*
simpset_ref() := simpset() addloop ("split_all_tac", split_all_tac)
*}

declare wf_prog_ws_prog [simp del]

end
