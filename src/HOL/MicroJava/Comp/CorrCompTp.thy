(*  Title:      HOL/MicroJava/Comp/CorrCompTp.thy
    ID:         $Id$
    Author:     Martin Strecker
*)

theory CorrCompTp =  LemmasComp + JVM + TypeInf + Altern:

declare split_paired_All [simp del]
declare split_paired_Ex [simp del]


(**********************************************************************)

constdefs     
   inited_LT :: "[cname, ty list, (vname \<times> ty) list] \<Rightarrow> locvars_type"
  "inited_LT C pTs lvars == (OK (Class C))#((map OK pTs))@(map (Fun.comp OK snd) lvars)"
   is_inited_LT :: "[cname, ty list, (vname \<times> ty) list, locvars_type] \<Rightarrow> bool"
  "is_inited_LT C pTs lvars LT == (LT = (inited_LT C pTs lvars))"

  local_env :: "[java_mb prog, cname, sig, vname list,(vname \<times> ty) list] \<Rightarrow> java_mb env"
  "local_env G C S pns lvars == 
     let (mn, pTs) = S in (G,map_of lvars(pns[\<mapsto>]pTs)(This\<mapsto>Class C))"

lemma local_env_fst [simp]: "fst (local_env G C S pns lvars) = G"
by (simp add: local_env_def split_beta)


lemma wt_class_expr_is_class: "\<lbrakk> ws_prog G; E \<turnstile> expr :: Class cname;
  E = local_env G C (mn, pTs) pns lvars\<rbrakk>
  \<Longrightarrow> is_class G cname "
apply (subgoal_tac "((fst E), (snd E)) \<turnstile> expr :: Class cname")
apply (frule ty_expr_is_type) apply simp
apply simp apply (simp (no_asm_use))
done



(********************************************************************************)
section "index"

lemma local_env_snd: "
  snd (local_env G C (mn, pTs) pns lvars) = map_of lvars(pns[\<mapsto>]pTs)(This\<mapsto>Class C)"
by (simp add: local_env_def)



lemma index_in_bounds: " length pns = length pTs \<Longrightarrow>
  snd (local_env G C (mn, pTs) pns lvars) vname = Some T
       \<Longrightarrow> index (pns, lvars, blk, res) vname < length (inited_LT C pTs lvars)"
apply (simp add: local_env_snd index_def split_beta)
apply (case_tac "vname = This")
apply (simp add: inited_LT_def)
apply simp
apply (drule map_of_upds_SomeD)
apply (drule length_takeWhile)
apply (simp add: inited_LT_def)
done


lemma map_upds_append [rule_format (no_asm)]: 
  "\<forall> x1s m. (length k1s = length x1s 
  \<longrightarrow> m(k1s[\<mapsto>]x1s)(k2s[\<mapsto>]x2s) = m ((k1s@k2s)[\<mapsto>](x1s@x2s)))"
apply (induct k1s)
apply simp
apply (intro strip)
apply (subgoal_tac "\<exists> x xr. x1s = x # xr")
apply clarify
apply simp
  (* subgoal *)
apply (case_tac x1s)
apply auto
done


lemma map_of_append [rule_format]: 
  "\<forall> ys. (map_of ((rev xs) @ ys) = (map_of ys) ((map fst xs) [\<mapsto>] (map snd xs)))"
apply (induct xs)
apply simp
apply (rule allI)
apply (drule_tac x="a # ys" in spec)
apply (simp only: rev.simps append_assoc append_Cons append_Nil
  map.simps map_of.simps map_upds_Cons hd.simps tl.simps)
done

lemma map_of_as_map_upds: "map_of (rev xs) = empty ((map fst xs) [\<mapsto>] (map snd xs))"
by (rule map_of_append [of _ "[]", simplified])

lemma map_of_rev: "unique xs \<Longrightarrow> map_of (rev xs) = map_of xs"
apply (induct xs)
apply simp
apply (simp add: unique_def map_of_append map_of_as_map_upds [THEN sym]
                 Map.map_of_append[symmetric] del:Map.map_of_append)
done

lemma map_upds_rev [rule_format]: "\<forall> xs. (distinct ks \<longrightarrow> length ks = length xs 
  \<longrightarrow> m (rev ks [\<mapsto>] rev xs) = m (ks [\<mapsto>] xs))"
apply (induct ks)
apply simp
apply (intro strip)
apply (subgoal_tac "\<exists> x xr. xs = x # xr")
apply clarify
apply (drule_tac x=xr in spec)
apply (simp add: map_upds_append [THEN sym])
  (* subgoal *)
apply (case_tac xs)
apply auto
done

lemma map_upds_takeWhile [rule_format]:
  "\<forall> ks. (empty(rev ks[\<mapsto>]rev xs)) k = Some x \<longrightarrow> length ks = length xs \<longrightarrow>
    xs ! length (takeWhile (\<lambda>z. z \<noteq> k) ks) = x"
apply (induct xs)
apply simp
apply (intro strip)
apply (subgoal_tac "\<exists> k' kr. ks = k' # kr")
apply (clarify)
apply (drule_tac x=kr in spec)
apply (simp only: rev.simps)
apply (subgoal_tac "(empty(rev kr @ [k'][\<mapsto>]rev list @ [a])) = empty (rev kr[\<mapsto>]rev list)([k'][\<mapsto>][a])")
apply (simp only:)
apply (case_tac "k' = k")
apply simp
apply simp 
apply (case_tac "k = k'")
apply simp
apply (simp add: empty_def)
apply (simp add: map_upds_append [THEN sym])
apply (case_tac ks)
apply auto
done


lemma local_env_inited_LT: "\<lbrakk> snd (local_env G C (mn, pTs) pns lvars) vname = Some T;
  length pns = length pTs; distinct pns; unique lvars \<rbrakk>
  \<Longrightarrow> (inited_LT C pTs lvars ! index (pns, lvars, blk, res) vname) = OK T"
apply (simp add: local_env_snd index_def)
apply (case_tac "vname = This")
apply (simp add: inited_LT_def)
apply (simp add: inited_LT_def)
apply (simp (no_asm_simp) only: map_compose map_append [THEN sym] map.simps [THEN sym])
apply (subgoal_tac "length (takeWhile (\<lambda>z. z \<noteq> vname) (pns @ map fst lvars)) < length (pTs @ map snd lvars)")
apply (simp (no_asm_simp) only: List.nth_map ok_val.simps)
apply (subgoal_tac "map_of lvars = map_of (map (\<lambda> p. (fst p, snd p)) lvars)")
apply (simp only:)
apply (subgoal_tac "distinct (map fst lvars)") 
apply (frule_tac g=snd in AuxLemmas.map_of_map_as_map_upd)
apply (simp only:)
apply (simp add: map_upds_append)
apply (frule map_upds_SomeD)
apply (rule map_upds_takeWhile)
apply (simp (no_asm_simp))
apply (simp add: map_upds_append [THEN sym])
apply (simp add: map_upds_rev)

  (* show length (pns @ map fst lvars) = length (pTs @ map snd lvars) *)
apply simp

  (* show distinct (map fst lvars) *)
apply (simp only: unique_def Fun.comp_def)

  (* show map_of lvars = map_of (map (\<lambda>p. (fst p, snd p)) lvars) *)
apply simp

  (* show length (takeWhile (\<lambda>z. z \<noteq> vname) (pns @ map fst lvars)) < length (pTs @ map snd lvars) *)
apply (drule map_of_upds_SomeD)
apply (drule length_takeWhile)
apply simp
done


lemma inited_LT_at_index_no_err: " i < length (inited_LT C pTs lvars)
  \<Longrightarrow> inited_LT C pTs lvars ! i \<noteq> Err"
apply (simp only: inited_LT_def)
apply (simp only: map_compose map_append [THEN sym] map.simps [THEN sym] length_map)
apply (simp only: nth_map)
apply simp
done


lemma sup_loc_update_index: "
  \<lbrakk> G \<turnstile> T \<preceq> T'; is_type G T'; length pns = length pTs; distinct pns; unique lvars;
  snd (local_env G C (mn, pTs) pns lvars) vname = Some T' \<rbrakk>
  \<Longrightarrow> 
  comp G \<turnstile> 
  inited_LT C pTs lvars [index (pns, lvars, blk, res) vname := OK T] <=l 
  inited_LT C pTs lvars"
apply (subgoal_tac " index (pns, lvars, blk, res) vname < length (inited_LT C pTs lvars)")
apply (frule_tac blk=blk and res=res in local_env_inited_LT, assumption+)
apply (rule sup_loc_trans)
apply (rule_tac b="OK T'" in sup_loc_update)
apply (simp add: comp_widen) 
apply assumption
apply (rule sup_loc_refl)
apply (simp add: list_update_same_conv [THEN iffD2])
  (* subgoal *)
apply (rule index_in_bounds)
apply simp+
done


(********************************************************************************)

section "Preservation of ST and LT by compTpExpr / compTpStmt"

lemma sttp_of_comb_nil [simp]: "sttp_of (comb_nil sttp) = sttp"
by (simp add: comb_nil_def)

lemma mt_of_comb_nil [simp]: "mt_of (comb_nil sttp) = []"
by (simp add: comb_nil_def)


lemma sttp_of_comb [simp]: "sttp_of ((f1 \<box> f2) sttp) = sttp_of (f2 (sttp_of (f1 sttp)))"
apply (case_tac "f1 sttp")
apply (case_tac "(f2 (sttp_of (f1 sttp)))")
apply (simp add: comb_def)
done

lemma mt_of_comb: "(mt_of ((f1 \<box> f2) sttp)) = 
  (mt_of (f1 sttp)) @ (mt_of (f2 (sttp_of (f1 sttp))))"
by (simp add: comb_def split_beta)


lemma mt_of_comb_length [simp]: "\<lbrakk> n1 = length (mt_of (f1 sttp)); n1 \<le> n \<rbrakk>
  \<Longrightarrow> (mt_of ((f1 \<box> f2) sttp) ! n) = (mt_of (f2 (sttp_of (f1 sttp))) ! (n - n1))"
by (simp add: comb_def nth_append split_beta)


lemma compTpExpr_Exprs_LT_ST: "
  \<lbrakk>jmb = (pns, lvars, blk, res); 
  wf_prog wf_java_mdecl G;
  wf_java_mdecl G C ((mn, pTs), rT, jmb);
  E = local_env G C (mn, pTs) pns lvars \<rbrakk>
 \<Longrightarrow> 
  (\<forall> ST LT T. 
  E \<turnstile> ex :: T \<longrightarrow>
  is_inited_LT C pTs lvars LT \<longrightarrow>
  sttp_of (compTpExpr jmb G ex (ST, LT)) = (T # ST, LT))
 \<and>
 (\<forall> ST LT Ts. 
  E \<turnstile> exs [::] Ts \<longrightarrow>
  is_inited_LT C pTs lvars LT \<longrightarrow>
  sttp_of (compTpExprs jmb G exs (ST, LT)) = ((rev Ts) @ ST, LT))"

apply (rule expr.induct)

(* expresssions *)

(* NewC *) 
apply (intro strip)
apply (drule NewC_invers)
apply (simp add: pushST_def)

(* Cast *)
apply (intro strip)
apply (drule Cast_invers, clarify)
apply ((drule_tac x=ST in spec), (drule spec)+, (drule mp, assumption)+)
apply (simp add: replST_def split_beta)

(* Lit *)
apply (intro strip)
apply (drule Lit_invers)
apply (simp add: pushST_def)

(* BinOp *)
apply (intro strip)
apply (drule BinOp_invers, clarify)
apply (drule_tac x=ST in spec)
apply (drule_tac x="Ta # ST" in spec)
apply ((drule spec)+, (drule mp, assumption)+)
  apply (case_tac binop)
  apply (simp (no_asm_simp))
    apply (simp (no_asm_simp) add: popST_def pushST_def)
  apply (simp)
    apply (simp (no_asm_simp) add: replST_def)


(* LAcc *)
apply (intro strip)
apply (drule LAcc_invers)
apply (simp add: pushST_def is_inited_LT_def)
apply (simp add: wf_prog_def)
apply (frule wf_java_mdecl_disjoint_varnames) 
  apply (simp add: disjoint_varnames_def)
apply (frule wf_java_mdecl_length_pTs_pns)
apply (erule conjE)+
apply (simp (no_asm_simp) add: local_env_inited_LT)

(* LAss *)
apply (intro strip)
apply (drule LAss_invers, clarify)
apply (drule LAcc_invers)
apply ((drule_tac x=ST in spec), (drule spec)+, (drule mp, assumption)+)
apply (simp add: popST_def dupST_def)

(* FAcc *)
apply (intro strip)
apply (drule FAcc_invers, clarify)
apply ((drule_tac x=ST in spec), (drule spec)+, (drule mp, assumption)+)
apply (simp add: replST_def)

  (* show   snd (the (field (G, cname) vname)) = T *)
  apply (subgoal_tac "is_class G Ca")
  apply (subgoal_tac "is_class G cname \<and> field (G, cname) vname = Some (cname, T)")
  apply simp

  (* show is_class G cname \<and> field (G, cname) vname = Some (cname, T) *)
  apply (rule field_in_fd) apply assumption+
  (* show is_class G Ca *)
  apply (fast intro: wt_class_expr_is_class)

(* FAss *)
apply (intro strip)
apply (drule FAss_invers, clarify)
apply (drule FAcc_invers, clarify)
apply (drule_tac x=ST in spec)
apply (drule_tac x="Class Ca # ST" in spec)
apply ((drule spec)+, (drule mp, assumption)+)
apply (simp add: popST_def dup_x1ST_def)


(* Call *)
apply (intro strip)
apply (drule Call_invers, clarify)
apply (drule_tac x=ST in spec)
apply (drule_tac x="Class cname # ST" in spec)
apply ((drule spec)+, (drule mp, assumption)+)
apply (simp add: replST_def)


(* expression lists *)
(* nil *) 

apply (intro strip)
apply (drule Nil_invers)
apply (simp add: comb_nil_def)

(* cons *)

apply (intro strip)
apply (drule Cons_invers, clarify)
apply (drule_tac x=ST in spec)
apply (drule_tac x="T # ST" in spec)
apply ((drule spec)+, (drule mp, assumption)+)
apply simp

done



lemmas compTpExpr_LT_ST [rule_format (no_asm)] = 
  compTpExpr_Exprs_LT_ST [THEN conjunct1]

lemmas compTpExprs_LT_ST [rule_format (no_asm)] = 
  compTpExpr_Exprs_LT_ST [THEN conjunct2]

lemma compTpStmt_LT_ST [rule_format (no_asm)]: "
  \<lbrakk> jmb = (pns,lvars,blk,res); 
  wf_prog wf_java_mdecl G;
  wf_java_mdecl G C ((mn, pTs), rT, jmb);
  E = (local_env G C (mn, pTs) pns lvars)\<rbrakk> 
\<Longrightarrow> (\<forall> ST LT.
  E \<turnstile> s\<surd> \<longrightarrow>
  (is_inited_LT C pTs lvars LT)
\<longrightarrow> sttp_of (compTpStmt jmb G s (ST, LT)) = (ST, LT))"

apply (rule stmt.induct)

(* Skip *) 
apply (intro strip)
apply simp

(* Expr *)
apply (intro strip)
apply (drule Expr_invers, erule exE)
apply (simp (no_asm_simp) add: compTpExpr_LT_ST)
apply (frule_tac ST=ST in compTpExpr_LT_ST, assumption+)
apply (simp add: popST_def)

(* Comp *)
apply (intro strip)
apply (drule Comp_invers, clarify)
apply (simp (no_asm_use))
apply simp

(* Cond *)
apply (intro strip)
apply (drule Cond_invers)
apply (erule conjE)+
apply (drule_tac x=ST in spec)
apply (drule_tac x=ST in spec)
apply (drule spec)+ apply (drule mp, assumption)+
apply (drule_tac ST="PrimT Boolean # ST" in compTpExpr_LT_ST, assumption+)
apply (simp add: popST_def pushST_def nochangeST_def)

(* Loop *)
apply (intro strip)
apply (drule Loop_invers)
apply (erule conjE)+
apply (drule_tac x=ST in spec)
apply (drule spec)+ apply (drule mp, assumption)+
apply (drule_tac ST="PrimT Boolean # ST" in compTpExpr_LT_ST, assumption+)
apply (simp add: popST_def pushST_def nochangeST_def)
done



lemma compTpInit_LT_ST: "
  sttp_of (compTpInit jmb (vn,ty) (ST, LT)) = (ST, LT[(index jmb vn):= OK ty])"
by (simp add: compTpInit_def storeST_def pushST_def)


lemma compTpInitLvars_LT_ST_aux [rule_format (no_asm)]:
  "\<forall> pre lvars_pre lvars0.
  jmb = (pns,lvars0,blk,res) \<and>
  lvars0 = (lvars_pre @ lvars) \<and>
  (length pns) + (length lvars_pre) + 1 = length pre \<and>
  disjoint_varnames pns (lvars_pre @ lvars)
  \<longrightarrow>
sttp_of (compTpInitLvars jmb lvars (ST, pre @ replicate (length lvars) Err))
    = (ST, pre @ map (Fun.comp OK snd) lvars)"
apply (induct lvars)
apply simp

apply (intro strip)
apply (subgoal_tac "\<exists> vn ty. a = (vn, ty)")
  prefer 2 apply (simp (no_asm_simp)) 
  apply ((erule exE)+, simp (no_asm_simp))

apply (drule_tac x="pre @ [OK ty]" in spec)
apply (drule_tac x="lvars_pre @ [a]" in spec)
apply (drule_tac x="lvars0" in spec)
apply (simp add: compTpInit_LT_ST index_of_var2)
done

lemma compTpInitLvars_LT_ST: 
  "\<lbrakk> jmb = (pns, lvars, blk, res); wf_java_mdecl G C ((mn, pTs), rT, jmb) \<rbrakk>
\<Longrightarrow>(sttp_of (compTpInitLvars jmb lvars (ST, start_LT C pTs (length lvars))))
  = (ST, inited_LT C pTs lvars)"
apply (simp add: start_LT_def inited_LT_def)
apply (simp only: append_Cons [THEN sym])
apply (rule compTpInitLvars_LT_ST_aux)
apply (auto dest: wf_java_mdecl_length_pTs_pns wf_java_mdecl_disjoint_varnames)
done



(********************************************************************************)

lemma max_of_list_elem: "x \<in> set xs \<Longrightarrow> x \<le> (max_of_list xs)"
by (induct xs, auto intro: le_maxI1 simp: le_max_iff_disj max_of_list_def)

lemma max_of_list_sublist: "set xs \<subseteq> set ys 
  \<Longrightarrow> (max_of_list xs) \<le> (max_of_list ys)"
by (induct xs, auto dest: max_of_list_elem simp: max_of_list_def)

lemma max_of_list_append [simp]:
  "max_of_list (xs @ ys) = max (max_of_list xs) (max_of_list ys)" 
apply (simp add: max_of_list_def)
apply (induct xs)
apply simp
apply simp
apply arith
done


lemma app_mono_mxs: "\<lbrakk> app i G mxs rT pc et s; mxs \<le> mxs' \<rbrakk> 
  \<Longrightarrow> app i G mxs' rT pc et s"
apply (case_tac s)
apply (simp add: app_def)
apply (case_tac i)
apply (auto intro: less_trans)
done



lemma err_mono [simp]: "A \<subseteq> B \<Longrightarrow> err A \<subseteq> err B"
by (auto simp: err_def)

lemma opt_mono [simp]: "A \<subseteq> B \<Longrightarrow> opt A \<subseteq> opt B"
by (auto simp: opt_def)


lemma states_mono: "\<lbrakk> mxs \<le> mxs' \<rbrakk>
  \<Longrightarrow> states G mxs mxr \<subseteq> states G mxs' mxr"
apply (simp add: states_def JVMType.sl_def)
apply (simp add: Product.esl_def stk_esl_def reg_sl_def 
  upto_esl_def Listn.sl_def Err.sl_def  JType.esl_def)
apply (simp add: Err.esl_def Err.le_def Listn.le_def)
apply (simp add: Product.le_def Product.sup_def Err.sup_def)
apply (simp add: Opt.esl_def Listn.sup_def)
apply (rule err_mono)
apply (rule opt_mono)
apply (rule Sigma_mono)
apply (rule Union_mono)
apply auto 
done


lemma check_type_mono: "\<lbrakk> check_type G mxs mxr s; mxs \<le> mxs' \<rbrakk> 
  \<Longrightarrow> check_type G mxs' mxr s"
apply (simp add: check_type_def)
apply (frule_tac G=G and mxr=mxr in states_mono)
apply auto
done


  (* wt is preserved when adding instructions/state-types at the end *)
lemma wt_instr_prefix: "
 \<lbrakk> wt_instr_altern (bc ! pc) cG rT mt mxs mxr max_pc et pc; 
  bc' = bc @ bc_post; mt' = mt @ mt_post; 
  mxs \<le> mxs'; max_pc \<le> max_pc'; 
  pc < length bc; pc < length mt; 
  max_pc = (length mt)\<rbrakk>
\<Longrightarrow> wt_instr_altern (bc' ! pc) cG rT mt' mxs' mxr max_pc' et pc"
apply (simp add: wt_instr_altern_def nth_append)
apply (auto intro: app_mono_mxs check_type_mono)
done


(************************************************************************)



lemma pc_succs_shift: "pc'\<in>set (succs i (pc'' + n))
 \<Longrightarrow> ((pc' - n) \<in>set (succs i pc''))"
apply (induct i)
apply simp+
  (* case Goto *)
apply arith
  (* case Ifcmpeq *)
apply simp
apply (erule disjE)
apply arith
apply arith
  (* case Throw *)
apply simp
done


lemma pc_succs_le: "\<lbrakk> pc' \<in> set (succs i (pc'' + n));   
  \<forall> b. ((i = (Goto b) \<or> i=(Ifcmpeq b)) \<longrightarrow> 0 \<le> (int pc'' + b)) \<rbrakk> 
  \<Longrightarrow> n \<le> pc'"
apply (induct i)
apply simp+
  (* case Goto *)
apply arith
  (* case Ifcmpeq *)
apply simp
apply (erule disjE)
apply simp
apply arith
  (* case Throw *)
apply simp
done


(**********************************************************************)

constdefs
  offset_xcentry :: "[nat, exception_entry] \<Rightarrow> exception_entry"
  "offset_xcentry == 
      \<lambda> n (start_pc, end_pc, handler_pc, catch_type).
          (start_pc + n, end_pc + n, handler_pc + n, catch_type)"

  offset_xctable :: "[nat, exception_table] \<Rightarrow> exception_table"
  "offset_xctable n == (map (offset_xcentry n))"

lemma match_xcentry_offset [simp]: "
  match_exception_entry G cn (pc + n) (offset_xcentry n ee) = 
  match_exception_entry G cn pc ee"
by (simp add: match_exception_entry_def offset_xcentry_def split_beta)

lemma match_xctable_offset: "
  (match_exception_table G cn (pc + n) (offset_xctable n et)) =
  (option_map (\<lambda> pc'. pc' + n) (match_exception_table G cn pc et))"
apply (induct et)
apply (simp add: offset_xctable_def)+
apply (case_tac "match_exception_entry G cn pc a")
apply (simp add: offset_xcentry_def split_beta)+
done


lemma match_offset [simp]: "
  match G cn (pc + n) (offset_xctable n et) = match G cn pc et"
apply (induct et)
apply (simp add: offset_xctable_def)+
done

lemma match_any_offset [simp]: "
  match_any G (pc + n) (offset_xctable n et) = match_any G pc et"
apply (induct et)
apply (simp add: offset_xctable_def offset_xcentry_def split_beta)+
done

lemma app_mono_pc: "\<lbrakk> app i G mxs rT pc et s; pc'= pc + n \<rbrakk> 
  \<Longrightarrow> app i G mxs rT pc' (offset_xctable n et) s"
apply (case_tac s)
apply (simp add: app_def)
apply (case_tac i)
apply (auto)
done

(**********************************************************************)

  (* Currently: empty exception_table *)

syntax
  empty_et :: exception_table
translations
  "empty_et" => "[]"



  (* move into Effect.thy *)
lemma xcpt_names_Nil [simp]: "(xcpt_names (i, G, pc, [])) = []"
by (induct i, simp_all)

lemma xcpt_eff_Nil [simp]: "(xcpt_eff i G pc s []) = []"
by (simp add: xcpt_eff_def)


lemma app_jumps_lem: "\<lbrakk> app i cG mxs rT pc empty_et s; s=(Some st) \<rbrakk>
  \<Longrightarrow>  \<forall> b. ((i = (Goto b) \<or> i=(Ifcmpeq b)) \<longrightarrow> 0 \<le> (int pc + b))"
apply (simp only:)
apply (induct i)
apply auto
done


(* wt is preserved when adding instructions/state-types to the front *)
lemma wt_instr_offset: "
 \<lbrakk> \<forall> pc'' < length mt. 
    wt_instr_altern ((bc@bc_post) ! pc'') cG rT (mt@mt_post) mxs mxr max_pc empty_et pc''; 
  bc' = bc_pre @ bc @ bc_post; mt' = mt_pre @ mt @ mt_post; 
  length bc_pre = length mt_pre; length bc = length mt;
  length mt_pre \<le> pc; pc < length (mt_pre @ mt); 
  mxs \<le> mxs'; max_pc + length mt_pre \<le> max_pc' \<rbrakk>
\<Longrightarrow> wt_instr_altern (bc' ! pc) cG rT mt' mxs' mxr max_pc' empty_et pc"

apply (simp add: wt_instr_altern_def)
apply (subgoal_tac "\<exists> pc''. pc = pc'' + length mt_pre", erule exE)
prefer 2 apply (rule_tac x="pc - length mt_pre" in exI, arith)

apply (drule_tac x=pc'' in spec)
apply (drule mp) apply arith	(* show pc'' < length mt *)
apply clarify

apply (rule conjI)
  (* app *)
  apply (simp add: nth_append)
  apply (rule app_mono_mxs)
  apply (frule app_mono_pc) apply (rule HOL.refl) apply (simp add: offset_xctable_def)
  apply assumption+

  (* check_type *)
apply (rule conjI)
apply (simp add: nth_append)
apply (rule  check_type_mono) apply assumption+

  (* ..eff.. *)
apply (intro ballI)
apply (subgoal_tac "\<exists> pc' s'. x = (pc', s')", (erule exE)+, simp)

apply (case_tac s')
  (* s' = None *)
apply (simp add: eff_def nth_append norm_eff_def)
apply (frule_tac x="(pc', None)" and  f=fst and b=pc' in rev_image_eqI) 
  apply (simp (no_asm_simp))
  apply (simp only: fst_conv image_compose [THEN sym] Fun.comp_def)
  apply simp
  apply (frule pc_succs_shift)
apply (drule bspec, assumption)
apply arith

  (* s' = Some a *)
apply (drule_tac x="(pc' - length mt_pre, s')" in bspec)

  (* show  (pc' - length mt_pre, s') \<in> set (eff \<dots>) *)
apply (simp add: eff_def)
    (* norm_eff *)
  apply (clarsimp simp: nth_append pc_succs_shift)

  (* show P x of bspec *)
apply simp
  apply (subgoal_tac "length mt_pre \<le> pc'")
  apply (simp add: nth_append) apply arith

  (* subgoals *)
apply (simp add: eff_def xcpt_eff_def)
apply (clarsimp)
apply (rule pc_succs_le) apply assumption+
apply (subgoal_tac "\<exists> st. mt ! pc'' = Some st", erule exE)
 apply (rule_tac s="Some st" and st=st and cG=cG and mxs=mxs and rT=rT
        in app_jumps_lem)
  apply (simp add: nth_append)+
    (* subgoal \<exists> st. mt ! pc'' = Some st *)
  apply (simp add: norm_eff_def option_map_def nth_append)
  apply (case_tac "mt ! pc''")
apply simp+
done


(**********************************************************************)


constdefs
  start_sttp_resp_cons :: "[state_type \<Rightarrow> method_type \<times> state_type] \<Rightarrow> bool"
  "start_sttp_resp_cons f == 
     (\<forall> sttp. let (mt', sttp') = (f sttp) in (\<exists>mt'_rest. mt' = Some sttp # mt'_rest))"

  start_sttp_resp :: "[state_type \<Rightarrow> method_type \<times> state_type] \<Rightarrow> bool"
  "start_sttp_resp f == (f = comb_nil) \<or> (start_sttp_resp_cons f)"

lemma start_sttp_resp_comb_nil [simp]: "start_sttp_resp comb_nil"
by (simp add: start_sttp_resp_def)

lemma start_sttp_resp_cons_comb_cons [simp]: "start_sttp_resp_cons f 
  \<Longrightarrow> start_sttp_resp_cons (f \<box> f')"
apply (simp add: start_sttp_resp_cons_def comb_def split_beta)
apply (rule allI)
apply (drule_tac x=sttp in spec)
apply auto
done

lemma start_sttp_resp_cons_comb_cons_r: "\<lbrakk> start_sttp_resp f; start_sttp_resp_cons f'\<rbrakk>
  \<Longrightarrow> start_sttp_resp_cons (f \<box> f')"
apply (simp add: start_sttp_resp_def)
apply (erule disjE)
apply simp+
done

lemma start_sttp_resp_cons_comb [simp]: "start_sttp_resp_cons f 
  \<Longrightarrow> start_sttp_resp (f \<box> f')"
by (simp add: start_sttp_resp_def)

lemma start_sttp_resp_comb: "\<lbrakk> start_sttp_resp f; start_sttp_resp f' \<rbrakk>
  \<Longrightarrow> start_sttp_resp (f \<box> f')"
apply (simp add: start_sttp_resp_def)
apply (erule disjE)
apply simp
apply (erule disjE)
apply simp+
done

lemma start_sttp_resp_cons_nochangeST [simp]: "start_sttp_resp_cons nochangeST"
by (simp add: start_sttp_resp_cons_def nochangeST_def)

lemma start_sttp_resp_cons_pushST [simp]: "start_sttp_resp_cons (pushST Ts)"
by (simp add: start_sttp_resp_cons_def pushST_def split_beta)

lemma start_sttp_resp_cons_dupST [simp]: "start_sttp_resp_cons dupST"
by (simp add: start_sttp_resp_cons_def dupST_def split_beta)

lemma start_sttp_resp_cons_dup_x1ST [simp]: "start_sttp_resp_cons dup_x1ST"
by (simp add: start_sttp_resp_cons_def dup_x1ST_def split_beta)

lemma start_sttp_resp_cons_popST [simp]: "start_sttp_resp_cons (popST n)"
by (simp add: start_sttp_resp_cons_def popST_def split_beta)

lemma start_sttp_resp_cons_replST [simp]: "start_sttp_resp_cons (replST n tp)"
by (simp add: start_sttp_resp_cons_def replST_def split_beta)

lemma start_sttp_resp_cons_storeST [simp]: "start_sttp_resp_cons (storeST i tp)"
by (simp add: start_sttp_resp_cons_def storeST_def split_beta)

lemma start_sttp_resp_cons_compTpExpr [simp]: "start_sttp_resp_cons (compTpExpr jmb G ex)"
apply (induct ex)
apply simp+
apply (simp add: start_sttp_resp_cons_def comb_def pushST_def split_beta) (* LAcc *)
apply simp+
done

lemma start_sttp_resp_cons_compTpInit [simp]: "start_sttp_resp_cons (compTpInit jmb lv)"
by (simp add: compTpInit_def split_beta)


lemma start_sttp_resp_nochangeST [simp]: "start_sttp_resp nochangeST"
by (simp add: start_sttp_resp_def)

lemma start_sttp_resp_pushST [simp]: "start_sttp_resp (pushST Ts)"
by (simp add: start_sttp_resp_def)

lemma start_sttp_resp_dupST [simp]: "start_sttp_resp dupST"
by (simp add: start_sttp_resp_def)

lemma start_sttp_resp_dup_x1ST [simp]: "start_sttp_resp dup_x1ST"
by (simp add: start_sttp_resp_def)

lemma start_sttp_resp_popST [simp]: "start_sttp_resp (popST n)"
by (simp add: start_sttp_resp_def)

lemma start_sttp_resp_replST [simp]: "start_sttp_resp (replST n tp)"
by (simp add: start_sttp_resp_def)

lemma start_sttp_resp_storeST [simp]: "start_sttp_resp (storeST i tp)"
by (simp add: start_sttp_resp_def)

lemma start_sttp_resp_compTpExpr [simp]: "start_sttp_resp (compTpExpr jmb G ex)"
by (simp add: start_sttp_resp_def)

lemma start_sttp_resp_compTpExprs [simp]: "start_sttp_resp (compTpExprs jmb G exs)"
by (induct exs, (simp add: start_sttp_resp_comb)+)

lemma start_sttp_resp_compTpStmt [simp]: "start_sttp_resp (compTpStmt jmb G s)"
by (induct s, (simp add: start_sttp_resp_comb)+)

lemma start_sttp_resp_compTpInitLvars [simp]: "start_sttp_resp (compTpInitLvars jmb lvars)"
by (induct lvars, simp+)




  (* ********************************************************************** *)
section "length of compExpr/ compTpExprs"
  (* ********************************************************************** *)

lemma length_comb [simp]:  "length (mt_of ((f1 \<box> f2) sttp)) = 
  length (mt_of (f1 sttp)) + length (mt_of (f2 (sttp_of (f1 sttp))))"
by (simp add: comb_def split_beta)


lemma length_comb_nil [simp]: "length (mt_of (comb_nil sttp)) = 0"
by (simp add: comb_nil_def)

lemma length_nochangeST [simp]: "length (mt_of (nochangeST sttp)) = 1"
by (simp add: nochangeST_def)

lemma length_pushST [simp]: "length (mt_of (pushST Ts sttp)) = 1"
by (simp add: pushST_def split_beta)

lemma length_dupST [simp]: "length (mt_of (dupST sttp)) = 1"
by (simp add: dupST_def split_beta)

lemma length_dup_x1ST [simp]: "length (mt_of (dup_x1ST sttp)) = 1"
by (simp add: dup_x1ST_def split_beta)

lemma length_popST [simp]: "length (mt_of (popST n sttp)) = 1"
by (simp add: popST_def split_beta)

lemma length_replST [simp]: "length (mt_of (replST n tp sttp)) = 1"
by (simp add: replST_def split_beta)

lemma length_storeST [simp]: "length (mt_of (storeST i tp sttp)) = 1"
by (simp add: storeST_def split_beta)


lemma length_compTpExpr_Exprs [rule_format]: "
  (\<forall> sttp. (length (mt_of (compTpExpr jmb G ex sttp)) = length (compExpr jmb ex)))
  \<and> (\<forall> sttp. (length (mt_of (compTpExprs jmb G exs sttp)) = length (compExprs jmb exs)))"
apply (rule  expr.induct)
apply simp+
apply (case_tac binop)
apply simp+
apply (simp add: pushST_def split_beta)
apply simp+
done

lemma length_compTpExpr: "length (mt_of (compTpExpr jmb G ex sttp)) = length (compExpr jmb ex)"
by (rule length_compTpExpr_Exprs [THEN conjunct1 [THEN spec]])

lemma length_compTpExprs: "length (mt_of (compTpExprs jmb G exs sttp)) = length (compExprs jmb exs)"
by (rule length_compTpExpr_Exprs [THEN conjunct2 [THEN spec]])

lemma length_compTpStmt [rule_format]: "
  (\<forall> sttp. (length (mt_of (compTpStmt jmb G s sttp)) = length (compStmt jmb s)))"
apply (rule stmt.induct)
apply (simp add: length_compTpExpr)+
done


lemma length_compTpInit: "length (mt_of (compTpInit jmb lv sttp)) = length (compInit jmb lv)"
by (simp add: compTpInit_def compInit_def split_beta)

lemma length_compTpInitLvars [rule_format]: 
  "\<forall> sttp. length (mt_of (compTpInitLvars jmb lvars sttp)) = length (compInitLvars jmb lvars)"
by (induct lvars,  (simp add: compInitLvars_def length_compTpInit split_beta)+)


  (* ********************************************************************** *)
section "Correspondence bytecode - method types"
  (* ********************************************************************** *)

syntax
  ST_of :: "state_type \<Rightarrow> opstack_type"
  LT_of :: "state_type \<Rightarrow> locvars_type"
translations
  "ST_of" => "fst"
  "LT_of" => "snd"

lemma states_lower:
  "\<lbrakk> OK (Some (ST, LT)) \<in> states cG mxs mxr; length ST \<le> mxs\<rbrakk>
  \<Longrightarrow> OK (Some (ST, LT)) \<in> states cG (length ST) mxr"
apply (simp add: states_def JVMType.sl_def)
apply (simp add: Product.esl_def stk_esl_def reg_sl_def upto_esl_def Listn.sl_def Err.sl_def
  JType.esl_def)
apply (simp add: Err.esl_def Err.le_def Listn.le_def)
apply (simp add: Product.le_def Product.sup_def Err.sup_def)
apply (simp add: Opt.esl_def Listn.sup_def)
apply clarify
apply auto
done

lemma check_type_lower:
  "\<lbrakk> check_type cG mxs mxr (OK (Some (ST, LT))); length ST \<le> mxs\<rbrakk>
  \<Longrightarrow>check_type cG (length ST) mxr (OK (Some (ST, LT)))"
by (simp add: check_type_def states_lower)

lemma max_same_iter [simp]: "max (x::'a::linorder) (max x y) = max x y"
by (simp del: max_assoc add: max_assoc [THEN sym])

  (* ******************************************************************* *)

constdefs
   bc_mt_corresp :: "
  [bytecode, state_type \<Rightarrow> method_type \<times> state_type, state_type, jvm_prog, ty, nat, p_count]
  \<Rightarrow> bool"

  "bc_mt_corresp bc f sttp0 cG rT mxr idx ==
  let (mt, sttp) = f sttp0 in
  (length bc = length mt \<and> 
    ((check_type cG (length (ST_of sttp0)) mxr (OK (Some sttp0))) \<longrightarrow>
    (\<forall>  mxs. 
     mxs = max_ssize (mt@[Some sttp]) \<longrightarrow>
     (\<forall> pc. pc < idx \<longrightarrow> 
      wt_instr_altern (bc ! pc) cG rT (mt@[Some sttp]) mxs mxr (length mt + 1) empty_et pc)
     \<and> 
     check_type cG mxs mxr (OK ((mt@[Some sttp]) ! idx)))))"


lemma bc_mt_corresp_comb: "
  \<lbrakk> bc' = (bc1@bc2); l' = (length bc');
  bc_mt_corresp bc1 f1 sttp0 cG rT mxr (length bc1);
  bc_mt_corresp bc2 f2 (sttp_of (f1 sttp0)) cG rT mxr (length bc2);
  start_sttp_resp f2\<rbrakk>
\<Longrightarrow> bc_mt_corresp bc' (f1 \<box> f2) sttp0 cG rT mxr l'"
apply (subgoal_tac "\<exists> mt1 sttp1. (f1 sttp0) = (mt1, sttp1)", (erule exE)+)
apply (subgoal_tac "\<exists> mt2 sttp2. (f2 sttp1) = (mt2, sttp2)", (erule exE)+)

  (* unfold start_sttp_resp and make case distinction *)
apply (simp only: start_sttp_resp_def)
apply (erule disjE)
  (* case f2 = comb_nil *)
apply (simp add: bc_mt_corresp_def comb_nil_def start_sttp_resp_cons_def)
apply (erule conjE)+
apply (intro strip)
apply simp

  (* case start_sttp_resp_cons f2 *)
apply (simp add: bc_mt_corresp_def comb_def start_sttp_resp_cons_def del: all_simps)
apply (intro strip)
apply (erule conjE)+
apply (drule mp, assumption)
apply (subgoal_tac "check_type cG (length (fst sttp1)) mxr (OK (Some sttp1))")
apply (erule conjE)+
apply (drule mp, assumption)
apply (erule conjE)+

apply (rule conjI)
  (* show wt_instr  \<dots> *)

apply (drule_tac x=sttp1 in spec, simp)
apply (erule exE)
apply (intro strip)
apply (case_tac "pc < length mt1")

  (* case pc < length mt1 *)
apply (drule spec, drule mp, simp)
apply simp 
apply (rule_tac mt="mt1 @ [Some sttp1]" in wt_instr_prefix)
  apply assumption+ apply (rule HOL.refl)
  apply (simp (no_asm_simp))
  apply (simp (no_asm_simp) add: max_ssize_def)
  apply (simp add: max_of_list_def max_ac)
  apply arith
  apply (simp (no_asm_simp))+

  (* case pc \<ge> length mt1 *)
apply (rule_tac bc=bc2 and mt=mt2 and bc_post="[]" and mt_post="[Some sttp2]" 
  and mxr=mxr 
  in wt_instr_offset)
apply simp
apply (simp (no_asm_simp))+
apply simp
apply (simp add: max_ssize_def max_of_list_append) apply (simp (no_asm_simp) add: max_def)
apply (simp (no_asm_simp))+

  (* show check_type \<dots> *)
apply (subgoal_tac "((mt2 @ [Some sttp2]) ! length bc2) = Some sttp2")
apply (simp only:)
apply (rule check_type_mono) apply assumption
apply (simp (no_asm_simp)  add: max_ssize_def max_of_list_append max_ac)
apply arith
apply (simp add: nth_append)

apply (erule conjE)+
apply (case_tac sttp1)
apply (simp add: check_type_def)
apply (rule states_lower, assumption)
apply (simp (no_asm_simp) add: max_ssize_def max_of_list_append)
apply (simp (no_asm_simp) add: max_of_list_def ssize_sto_def max_def)
apply (simp (no_asm_simp))+
done


lemma bc_mt_corresp_zero [simp]: "\<lbrakk> length (mt_of (f sttp)) = length bc; start_sttp_resp f\<rbrakk>
  \<Longrightarrow> bc_mt_corresp bc f sttp cG rT mxr 0"
apply (simp add: bc_mt_corresp_def start_sttp_resp_def split_beta)
apply (erule disjE)
apply (simp add: max_ssize_def max_of_list_def ssize_sto_def split_beta)
apply (intro strip)
apply (simp add: start_sttp_resp_cons_def split_beta)
apply (drule_tac x=sttp in spec, erule exE)
apply simp
apply (rule check_type_mono, assumption)
apply (simp add: max_ssize_def max_of_list_def ssize_sto_def max_def split_beta)
done

  (* ********************************************************************** *)


constdefs
  mt_sttp_flatten :: "method_type \<times> state_type \<Rightarrow> method_type"
  "mt_sttp_flatten mt_sttp == (mt_of mt_sttp) @ [Some (sttp_of mt_sttp)]"


lemma mt_sttp_flatten_length [simp]: "n = (length (mt_of (f sttp)))
 \<Longrightarrow> (mt_sttp_flatten (f sttp)) ! n = Some (sttp_of (f sttp))"
by (simp add: mt_sttp_flatten_def)

lemma mt_sttp_flatten_comb: "(mt_sttp_flatten ((f1 \<box> f2) sttp)) = 
  (mt_of (f1 sttp)) @ (mt_sttp_flatten (f2 (sttp_of (f1 sttp))))"
by (simp add: mt_sttp_flatten_def comb_def split_beta)

lemma mt_sttp_flatten_comb_length [simp]: "\<lbrakk> n1 = length (mt_of (f1 sttp)); n1 \<le> n \<rbrakk>
  \<Longrightarrow> (mt_sttp_flatten ((f1 \<box> f2) sttp) ! n) = (mt_sttp_flatten (f2 (sttp_of (f1 sttp))) ! (n - n1))"
by (simp add: mt_sttp_flatten_comb nth_append)

lemma mt_sttp_flatten_comb_zero [simp]: "start_sttp_resp f 
  \<Longrightarrow> (mt_sttp_flatten (f sttp)) ! 0 = Some sttp"
apply (simp only: start_sttp_resp_def)
apply (erule disjE)
apply (simp add: comb_nil_def mt_sttp_flatten_def)
apply (simp add: start_sttp_resp_cons_def mt_sttp_flatten_def split_beta)
apply (drule_tac x=sttp in spec)
apply (erule exE)
apply simp
done


(* move into prelude -- compare with nat_int_length *)
lemma int_outside_right: "0 \<le> (m::int) \<Longrightarrow> m + (int n) = int ((nat m) + n)"
by simp

lemma int_outside_left: "0 \<le> (m::int) \<Longrightarrow> (int n) + m = int (n + (nat m))"
by simp




  (* ********************************************************************** *)
  (* bc_mt_corresp for individual instructions                              *)
  (* ---------------------------------------------------------------------- *)

lemma less_Suc [simp] : "n \<le> k \<Longrightarrow> (k < Suc n) = (k = n)"
  by arith

lemmas check_type_simps = check_type_def states_def JVMType.sl_def
   Product.esl_def stk_esl_def reg_sl_def upto_esl_def Listn.sl_def Err.sl_def
  JType.esl_def Err.esl_def Err.le_def Listn.le_def Product.le_def Product.sup_def Err.sup_def
  Opt.esl_def Listn.sup_def


lemma check_type_push: "\<lbrakk> 
  is_class cG cname; check_type cG (length ST) mxr (OK (Some (ST, LT))) \<rbrakk>
  \<Longrightarrow> check_type cG (Suc (length ST)) mxr (OK (Some (Class cname # ST, LT)))"
apply (simp add: check_type_simps)
apply clarify
apply (rule_tac x="Suc (length ST)" in exI)
apply simp+
done

lemma bc_mt_corresp_New: "\<lbrakk>is_class cG cname \<rbrakk>
  \<Longrightarrow> bc_mt_corresp [New cname] (pushST [Class cname]) (ST, LT) cG rT mxr (Suc 0)"
apply (simp add: bc_mt_corresp_def pushST_def wt_instr_altern_def
    max_ssize_def max_of_list_def ssize_sto_def max_def 
    eff_def norm_eff_def)
apply (intro strip)
apply (rule conjI)
apply (rule check_type_mono, assumption, simp)
apply (simp add: check_type_push)
done

lemma bc_mt_corresp_Pop: "
  bc_mt_corresp [Pop] (popST (Suc 0)) (T # ST, LT) cG rT mxr (Suc 0)"
  apply (simp add: bc_mt_corresp_def popST_def wt_instr_altern_def eff_def norm_eff_def)
  apply (simp add: max_ssize_def ssize_sto_def max_of_list_def) 
  apply (simp add: max_def)
  apply (simp add: check_type_simps)
  apply clarify
  apply (rule_tac x="(length ST)" in exI)
  apply simp+
  done

lemma bc_mt_corresp_Checkcast: "\<lbrakk> is_class cG cname; sttp = (ST, LT); 
  (\<exists>rT STo. ST = RefT rT # STo) \<rbrakk>
  \<Longrightarrow> bc_mt_corresp [Checkcast cname] (replST (Suc 0) (Class cname)) sttp cG rT mxr (Suc 0)"
  apply (erule exE)+
  apply (simp add: bc_mt_corresp_def replST_def wt_instr_altern_def eff_def norm_eff_def)
  apply (simp add: max_ssize_def max_of_list_def ssize_sto_def max_def)
  apply (simp add: check_type_simps)
  apply clarify
  apply (rule_tac x="Suc (length STo)" in exI)
  apply simp+
  done


lemma bc_mt_corresp_LitPush: "\<lbrakk> typeof (\<lambda>v. None) val = Some T \<rbrakk>
  \<Longrightarrow> bc_mt_corresp [LitPush val] (pushST [T]) sttp cG rT mxr (Suc 0)"
apply (subgoal_tac "\<exists> ST LT. sttp= (ST, LT)", (erule exE)+)
  apply (simp add: bc_mt_corresp_def pushST_def wt_instr_altern_def
                 max_ssize_def max_of_list_def ssize_sto_def max_def
                 eff_def norm_eff_def)
  apply (intro strip)
  apply (rule conjI)
  apply (rule check_type_mono, assumption, simp)
  apply (simp add: check_type_simps)
apply clarify
apply (rule_tac x="Suc (length ST)" in exI)
apply simp
apply (drule sym)
apply (case_tac val)
apply simp+
done


lemma bc_mt_corresp_LitPush_CT: "\<lbrakk> typeof (\<lambda>v. None) val = Some T \<and> cG \<turnstile> T \<preceq> T';
  is_type cG T' \<rbrakk>
  \<Longrightarrow> bc_mt_corresp [LitPush val] (pushST [T']) sttp cG rT mxr (Suc 0)"
apply (subgoal_tac "\<exists> ST LT. sttp= (ST, LT)", (erule exE)+)
  apply (simp add: bc_mt_corresp_def pushST_def wt_instr_altern_def
                 max_ssize_def max_of_list_def ssize_sto_def max_def
                 eff_def norm_eff_def)
  apply (intro strip)
  apply (rule conjI)
  apply (rule check_type_mono, assumption, simp)
  apply (simp add: check_type_simps)
  apply (simp add: sup_state_Cons)
apply clarify
apply (rule_tac x="Suc (length ST)" in exI)
apply simp
apply simp+
done

lemma bc_mt_corresp_Load: "\<lbrakk> i < length LT; LT ! i \<noteq> Err; mxr = length LT \<rbrakk>
  \<Longrightarrow> bc_mt_corresp [Load i] 
         (\<lambda>(ST, LT). pushST [ok_val (LT ! i)] (ST, LT)) (ST, LT) cG rT mxr (Suc 0)"
apply (simp add: bc_mt_corresp_def pushST_def wt_instr_altern_def
                 max_ssize_def max_of_list_def ssize_sto_def max_def
                 eff_def norm_eff_def)
  apply (intro strip)
  apply (rule conjI)
  apply (rule check_type_mono, assumption, simp)
apply (simp add: check_type_simps)
apply clarify
apply (rule_tac x="Suc (length ST)" in exI)
apply (simp (no_asm_simp))
  apply (simp only: err_def)
  apply (frule listE_nth_in) apply assumption
apply (subgoal_tac "LT ! i \<in> {x. \<exists>y\<in>types cG. x = OK y}")
apply (drule CollectD) apply (erule bexE)
apply (simp (no_asm_simp) )
apply blast
apply blast
done


lemma bc_mt_corresp_Store_init: "\<lbrakk> i < length LT \<rbrakk>
  \<Longrightarrow> bc_mt_corresp [Store i] (storeST i T) (T # ST, LT) cG rT mxr (Suc 0)"
 apply (simp add: bc_mt_corresp_def storeST_def wt_instr_altern_def eff_def norm_eff_def)
  apply (simp add: max_ssize_def  max_of_list_def )
  apply (simp add: ssize_sto_def) apply (simp add: max_def)
  apply (intro strip)
apply (simp add: check_type_simps)
apply clarify
apply (rule conjI)
apply (rule_tac x="(length ST)" in exI)
apply simp+
done



lemma bc_mt_corresp_Store: "\<lbrakk> i < length LT; cG  \<turnstile>  LT[i := OK T] <=l LT \<rbrakk>
  \<Longrightarrow> bc_mt_corresp [Store i] (popST (Suc 0)) (T # ST, LT) cG rT mxr (Suc 0)"
  apply (simp add: bc_mt_corresp_def popST_def wt_instr_altern_def eff_def norm_eff_def)
  apply (simp add: sup_state_conv)
  apply (simp add: max_ssize_def max_of_list_def ssize_sto_def)
  apply (simp add: max_def)
 apply (intro strip)
apply (simp add: check_type_simps)
apply clarify
apply (rule_tac x="(length ST)" in exI)
apply simp+
done


lemma bc_mt_corresp_Dup: "
  bc_mt_corresp [Dup] dupST (T # ST, LT) cG rT mxr (Suc 0)"
 apply (simp add: bc_mt_corresp_def dupST_def wt_instr_altern_def
                 max_ssize_def max_of_list_def ssize_sto_def max_def
                 eff_def norm_eff_def)
  apply (intro strip)
  apply (rule conjI)
  apply (rule check_type_mono, assumption, simp)
apply (simp add: check_type_simps)
apply clarify
apply (rule_tac x="Suc (Suc (length ST))" in exI)
apply simp+
done

lemma bc_mt_corresp_Dup_x1: "
  bc_mt_corresp [Dup_x1] dup_x1ST (T1 # T2 # ST, LT) cG rT mxr (Suc 0)"
  apply (simp add: bc_mt_corresp_def dup_x1ST_def wt_instr_altern_def
                 max_ssize_def max_of_list_def ssize_sto_def max_def
                 eff_def norm_eff_def)
  apply (intro strip)
  apply (rule conjI)
  apply (rule check_type_mono, assumption, simp)
apply (simp add: check_type_simps)
apply clarify
apply (rule_tac x="Suc (Suc (Suc (length ST)))" in exI)
apply simp+
done



lemma bc_mt_corresp_IAdd: "
  bc_mt_corresp [IAdd] (replST 2 (PrimT Integer)) 
         (PrimT Integer # PrimT Integer # ST, LT) cG rT mxr (Suc 0)"
  apply (simp add: bc_mt_corresp_def replST_def wt_instr_altern_def eff_def norm_eff_def)
  apply (simp add: max_ssize_def max_of_list_def ssize_sto_def max_def)
  apply (simp add: check_type_simps)
  apply clarify
  apply (rule_tac x="Suc (length ST)" in exI)
  apply simp+
  done

lemma bc_mt_corresp_Getfield: "\<lbrakk> wf_prog wf_mb G; 
  field (G, C) vname = Some (cname, T);  is_class G C \<rbrakk>
  \<Longrightarrow> bc_mt_corresp [Getfield vname cname] 
        (replST (Suc 0) (snd (the (field (G, cname) vname))))
        (Class C # ST, LT) (comp G) rT mxr (Suc 0)"
  apply (frule wf_prog_ws_prog [THEN wf_subcls1])
  apply (frule field_in_fd, assumption+)
  apply (frule widen_field, assumption+)
  apply (simp add: bc_mt_corresp_def replST_def wt_instr_altern_def eff_def norm_eff_def)
  apply (simp add: comp_field comp_subcls1 comp_widen comp_is_class)
  apply (simp add: max_ssize_def max_of_list_def ssize_sto_def)
  apply (intro strip)
apply (simp add: check_type_simps)
apply clarify
apply (rule_tac x="Suc (length ST)" in exI)
apply simp+
apply (simp only: comp_is_type)
apply (rule_tac C=cname in fields_is_type)
apply (simp add: field_def)
apply (drule JBasis.table_of_remap_SomeD)+
apply assumption+
apply (erule wf_prog_ws_prog)
apply assumption
done

lemma bc_mt_corresp_Putfield: "\<lbrakk> wf_prog wf_mb G; 
  field (G, C) vname = Some (cname, Ta); G \<turnstile> T \<preceq> Ta; is_class G C \<rbrakk>
  \<Longrightarrow> bc_mt_corresp [Putfield vname cname] (popST 2) (T # Class C # T # ST, LT)
           (comp G) rT mxr (Suc 0)"
  apply (frule wf_prog_ws_prog [THEN wf_subcls1])
  apply (frule field_in_fd, assumption+)
  apply (frule widen_field, assumption+)
  apply (simp add: bc_mt_corresp_def popST_def wt_instr_altern_def eff_def norm_eff_def)
  apply (simp add: comp_field comp_subcls1 comp_widen comp_is_class)
  apply (simp add: max_ssize_def max_of_list_def ssize_sto_def max_def)

  apply (intro strip)
apply (simp add: check_type_simps)
apply clarify
apply (rule_tac x="Suc (length ST)" in exI)
apply simp+
done



lemma Call_app: "\<lbrakk> wf_prog wf_mb G; is_class G cname;
STs = rev pTsa @ Class cname # ST;
max_spec G cname (mname, pTsa) = {((md, T), pTs')} \<rbrakk>
  \<Longrightarrow> app (Invoke cname mname pTs') (comp G) (length (T # ST)) rT 0 empty_et (Some (STs, LTs))"
  apply (subgoal_tac "(\<exists>mD' rT' comp_b. 
    method (comp G, cname) (mname, pTs') = Some (mD', rT', comp_b))")
  apply (simp add: comp_is_class)
  apply (rule_tac x=pTsa in exI)
  apply (rule_tac x="Class cname" in exI)
  apply (simp add: max_spec_preserves_length comp_is_class)
  apply (frule max_spec2mheads, (erule exE)+, (erule conjE)+)
  apply (simp add: split_paired_all comp_widen list_all2_def)
  apply (frule max_spec2mheads, (erule exE)+, (erule conjE)+)
  apply (rule exI)+
  apply (simp add: wf_prog_ws_prog [THEN comp_method])
  apply auto
  done


lemma bc_mt_corresp_Invoke: "\<lbrakk> wf_prog wf_mb G; 
  max_spec G cname (mname, pTsa) = {((md, T), fpTs)};
  is_class G cname \<rbrakk>
 \<Longrightarrow> bc_mt_corresp [Invoke cname mname fpTs] (replST (Suc (length pTsa)) T)
           (rev pTsa @ Class cname # ST, LT) (comp G) rT mxr (Suc 0)"
  apply (simp add: bc_mt_corresp_def wt_instr_altern_def eff_def norm_eff_def)
  apply (simp add: replST_def del: appInvoke)
  apply (intro strip)
  apply (rule conjI)

  -- "app"
  apply (rule Call_app [THEN app_mono_mxs]) apply assumption+
    apply (rule HOL.refl) apply assumption
    apply (simp add: max_ssize_def max_of_list_elem ssize_sto_def)

  -- {* @{text "<=s"} *}
  apply (frule max_spec2mheads, (erule exE)+, (erule conjE)+)
  apply (simp add: wf_prog_ws_prog [THEN comp_method])
  apply (simp add: max_spec_preserves_length [THEN sym])

  -- "@{text check_type}"
apply (simp add: max_ssize_def ssize_sto_def max_def)
apply (simp add: max_of_list_def)
apply (subgoal_tac "(max (length pTsa + length ST) (length ST)) = (length pTsa + length ST)")
apply simp
apply (simp add: check_type_simps)
apply clarify
apply (rule_tac x="Suc (length ST)" in exI)
apply simp+
apply (simp only: comp_is_type)
apply (frule method_wf_mdecl) apply assumption apply assumption
apply (simp add: wf_mdecl_def wf_mhead_def)
apply (simp add: max_def)
  done


lemma wt_instr_Ifcmpeq: "\<lbrakk>Suc pc < max_pc; 
  0 \<le> (int pc + i);  nat (int pc + i) < max_pc;
  (mt_sttp_flatten f ! pc = Some (ts#ts'#ST,LT)) \<and> 
  ((\<exists>p. ts = PrimT p \<and> ts' = PrimT p) \<or> (\<exists>r r'. ts = RefT r \<and> ts' = RefT r'));
  mt_sttp_flatten f ! Suc pc = Some (ST,LT);
  mt_sttp_flatten f ! nat (int pc + i) = Some (ST,LT);
  check_type (TranslComp.comp G) mxs mxr (OK (Some (ts # ts' # ST, LT))) \<rbrakk>
    \<Longrightarrow>  wt_instr_altern (Ifcmpeq i) (comp G) rT  (mt_sttp_flatten f) mxs mxr max_pc empty_et pc"
by (simp  add: wt_instr_altern_def eff_def norm_eff_def)


lemma wt_instr_Goto: "\<lbrakk> 0 \<le> (int pc + i); nat (int pc + i) < max_pc;
  mt_sttp_flatten f ! nat (int pc + i) = (mt_sttp_flatten f ! pc);
  check_type (TranslComp.comp G) mxs mxr (OK (mt_sttp_flatten f ! pc)) \<rbrakk>
  \<Longrightarrow> wt_instr_altern (Goto i) (comp G) rT  (mt_sttp_flatten f) mxs mxr max_pc empty_et pc"
apply (case_tac "(mt_sttp_flatten f ! pc)")
apply (simp  add: wt_instr_altern_def eff_def norm_eff_def app_def xcpt_app_def)+
done




  (* ********************************************************************** *)



lemma bc_mt_corresp_comb_inside: "
  \<lbrakk> 
  bc_mt_corresp bc' f' sttp0 cG rT mxr l1;
  bc' = (bc1@bc2@bc3); f'= (f1 \<box> f2 \<box> f3); 
  l1 = (length bc1); l12 = (length (bc1@bc2));
  bc_mt_corresp bc2 f2 (sttp_of (f1 sttp0)) cG rT mxr (length bc2);
  length bc1 = length (mt_of (f1 sttp0));
  start_sttp_resp f2; start_sttp_resp f3\<rbrakk>
\<Longrightarrow> bc_mt_corresp bc' f' sttp0 cG rT mxr l12"
apply (subgoal_tac "\<exists> mt1 sttp1. (f1 sttp0) = (mt1, sttp1)", (erule exE)+)
apply (subgoal_tac "\<exists> mt2 sttp2. (f2 sttp1) = (mt2, sttp2)", (erule exE)+)
apply (subgoal_tac "\<exists> mt3 sttp3. (f3 sttp2) = (mt3, sttp3)", (erule exE)+)

  (* unfold start_sttp_resp and make case distinction *)
apply (simp only: start_sttp_resp_def)
apply (erule_tac Q="start_sttp_resp_cons f2" in disjE)
  (* case f2 = comb_nil *)
apply (simp add: bc_mt_corresp_def comb_nil_def start_sttp_resp_cons_def)

  (* case start_sttp_resp_cons f2 *)
apply (simp add: bc_mt_corresp_def comb_def start_sttp_resp_cons_def)
apply (drule_tac x=sttp1 in spec, simp, erule exE)
apply (intro strip, (erule conjE)+)


  (* get rid of all check_type info *)
apply (subgoal_tac "check_type cG (length (fst sttp1)) mxr (OK (Some sttp1))")
apply (subgoal_tac "check_type cG (max_ssize (mt2 @ [Some sttp2])) mxr (OK (Some sttp2))")
apply (subgoal_tac "check_type cG (max_ssize (mt1 @ mt2 @ mt3 @ [Some sttp3])) mxr
           (OK ((mt2 @ mt3 @ [Some sttp3]) ! length mt2))")
apply simp



apply (intro strip, (erule conjE)+)
apply (case_tac "pc < length mt1")

  (* case pc < length mt1 *)
apply (drule spec, drule mp, assumption)
apply assumption

  (* case pc \<ge> length mt1 *)
  (* case distinction on start_sttp_resp f3 *)
apply (erule_tac P="f3 = comb_nil" in disjE)

  (* case f3 = comb_nil *)
apply (subgoal_tac "mt3 = [] \<and> sttp2 = sttp3")  apply (erule conjE)+
apply (subgoal_tac "bc3=[]")

apply (rule_tac bc_pre=bc1 and bc=bc2 and bc_post=bc3
  and mt_pre=mt1 and mt=mt2 and mt_post="mt3@ [Some sttp3]" 
  and mxs="(max_ssize (mt2 @ [(Some sttp2)]))"
  and max_pc="(Suc (length mt2))"
  in wt_instr_offset)
  apply simp
  apply (rule HOL.refl)+
  apply (simp (no_asm_simp))+

  apply (simp (no_asm_simp) add: max_ssize_def del: max_of_list_append)
    apply (rule max_of_list_sublist)
    apply (simp (no_asm_simp) only: set_append set.simps map.simps) apply blast
  apply (simp (no_asm_simp))
  apply simp			(* subgoal bc3 = [] *)
  apply (simp add: comb_nil_def) (* subgoal mt3 = [] \<and> sttp2 = sttp3 *)

  (* case start_sttp_resp_cons f3 *)
apply (subgoal_tac "\<exists>mt3_rest. (mt3 = Some sttp2 # mt3_rest)", erule exE)
apply (rule_tac bc_pre=bc1 and bc=bc2 and bc_post=bc3
  and mt_pre=mt1 and mt=mt2 and mt_post="mt3@ [Some sttp3]" 
  and mxs="(max_ssize (mt2 @ [Some sttp2]))"
  and max_pc="(Suc (length mt2))"
  in wt_instr_offset)
apply (intro strip)
apply (rule_tac bc=bc2 and mt="(mt2 @ [Some sttp2])"
  and mxs="(max_ssize (mt2 @ [Some sttp2]))"
  and max_pc="(Suc (length mt2))"
  in wt_instr_prefix)


     (* preconditions of  wt_instr_prefix *)
  apply simp
  apply (rule HOL.refl)
  apply (simp (no_asm_simp))+
  apply simp+
     (* (some) preconditions of  wt_instr_offset *)
  apply (simp (no_asm_simp) add: max_ssize_def del: max_of_list_append)
  apply (rule max_of_list_sublist)
    apply (simp (no_asm_simp) only: set_append set.simps map.simps) apply blast
  apply (simp (no_asm_simp))

apply (drule_tac x=sttp2 in spec, simp) (* subgoal \<exists>mt3_rest. \<dots> *)

  (* subgoals check_type*)
  (* \<dots> ! length mt2 *)
apply simp

apply (erule_tac P="f3 = comb_nil" in disjE)

  (* -- case f3 = comb_nil *)
apply (subgoal_tac "mt3 = [] \<and> sttp2 = sttp3")  apply (erule conjE)+
apply simp
apply (rule check_type_mono, assumption)
apply (simp only: max_ssize_def) apply (rule max_of_list_sublist) apply (simp (no_asm_simp))
apply blast
  apply simp			(* subgoal bc3 = [] *)
  apply (simp add: comb_nil_def) (* subgoal mt3 = [] \<and> sttp2 = sttp3 *)


  (* -- case start_sttp_resp_cons f3 *)
apply (subgoal_tac "\<exists>mt3_rest. (mt3 = Some sttp2 # mt3_rest)", erule exE)
apply (simp (no_asm_simp) add: nth_append)
apply (erule conjE)+
apply (rule check_type_mono, assumption)
apply (simp only: max_ssize_def) apply (rule max_of_list_sublist) apply (simp (no_asm_simp))
apply blast
apply (drule_tac x=sttp2 in spec, simp) (* subgoal \<exists>mt3_rest. \<dots> *)


  (* subgoal check_type \<dots> Some sttp2 *)
apply (simp add: nth_append)

  (* subgoal check_type \<dots> Some sttp1 *)
apply (simp add: nth_append)
apply (erule conjE)+
apply (case_tac "sttp1", simp)
apply (rule check_type_lower) apply assumption
apply (simp (no_asm_simp) add: max_ssize_def ssize_sto_def)
apply (simp (no_asm_simp) add: max_of_list_def max_def)

  (* subgoals \<exists> ... *)
apply (rule surj_pair)+
done


  (* ******************** *)
constdefs 
  contracting :: "(state_type \<Rightarrow> method_type \<times> state_type) \<Rightarrow> bool"
  "contracting f == (\<forall> ST LT. 
                    let (ST', LT') = sttp_of (f (ST, LT)) 
                    in (length ST' \<le> length ST \<and> set ST' \<subseteq> set ST  \<and>
                        length LT' = length LT \<and> set LT' \<subseteq> set LT))"


  (* ### possibly move into HOL *)
lemma set_drop_Suc [rule_format]: "\<forall> xs. set (drop (Suc n) xs) \<subseteq> set (drop n xs)"
apply (induct n)
apply simp
apply (intro strip)
apply (rule list.induct)
apply simp
apply simp apply blast
apply (intro strip)
apply (rule_tac 
  P="\<lambda> xs. set (drop (Suc (Suc n)) xs) \<subseteq> set (drop (Suc n) xs)" in list.induct)
apply simp+
done

lemma set_drop_le [rule_format,simp]: "\<forall> n xs. n \<le> m \<longrightarrow> set (drop m xs) \<subseteq> set (drop n xs)"
apply (induct m)
apply simp
apply (intro strip)
apply (subgoal_tac "na \<le> n \<or> na = Suc n")
apply (erule disjE)
apply (frule_tac x=na in spec, drule_tac x=xs in spec, drule mp, assumption)
apply (rule set_drop_Suc [THEN subset_trans], assumption)
apply auto
done

lemma set_drop [simp] : "set (drop m xs) \<subseteq> set xs"
apply (rule_tac B="set (drop 0 xs)" in subset_trans)
apply (rule set_drop_le)
apply simp+
done



lemma contracting_popST [simp]: "contracting (popST n)"
by (simp add: contracting_def popST_def)

lemma contracting_nochangeST [simp]: "contracting nochangeST"
by (simp add: contracting_def nochangeST_def)


lemma check_type_contracting: "\<lbrakk> check_type cG mxs mxr (OK (Some sttp)); contracting f\<rbrakk> 
  \<Longrightarrow> check_type cG mxs mxr (OK (Some (sttp_of (f sttp))))"
apply (subgoal_tac "\<exists> ST LT. sttp = (ST, LT)", (erule exE)+)
apply (simp add: check_type_simps contracting_def)
apply clarify
apply (drule_tac x=ST in spec, drule_tac x=LT in spec)
apply (case_tac "(sttp_of (f (ST, LT)))")
apply simp
apply (erule conjE)+

apply (drule listE_set)+
apply (rule conjI)
apply (rule_tac x="length a" in exI) apply simp
apply (rule listI) apply simp apply blast
apply (rule listI) apply simp apply blast
apply auto
done

  (* ******************** *)


lemma bc_mt_corresp_comb_wt_instr: "
  \<lbrakk> bc_mt_corresp bc' f' sttp0 cG rT mxr l1;
  bc' = (bc1@[inst]@bc3); f'= (f1 \<box> f2 \<box> f3); 
  l1 = (length bc1); 
  length bc1 = length (mt_of (f1 sttp0));
  length (mt_of (f2 (sttp_of (f1 sttp0)))) = 1;
  start_sttp_resp_cons f1; start_sttp_resp_cons f2; start_sttp_resp f3;

  check_type cG (max_ssize (mt_sttp_flatten (f' sttp0))) mxr
             (OK ((mt_sttp_flatten (f' sttp0)) ! (length bc1)))
  \<longrightarrow>
  wt_instr_altern inst cG rT 
      (mt_sttp_flatten (f' sttp0)) 
      (max_ssize (mt_sttp_flatten (f' sttp0)))
      mxr
      (Suc (length bc'))
      empty_et
      (length bc1);
  contracting f2
 \<rbrakk>
\<Longrightarrow> bc_mt_corresp bc' f' sttp0 cG rT mxr (length (bc1@[inst]))"
apply (subgoal_tac "\<exists> mt1 sttp1. (f1 sttp0) = (mt1, sttp1)", (erule exE)+)
apply (subgoal_tac "\<exists> mt2 sttp2. (f2 sttp1) = (mt2, sttp2)", (erule exE)+)
apply (subgoal_tac "\<exists> mt3 sttp3. (f3 sttp2) = (mt3, sttp3)", (erule exE)+)

apply (simp add: bc_mt_corresp_def comb_def start_sttp_resp_cons_def
  mt_sttp_flatten_def)

apply (intro strip, (erule conjE)+)
apply (drule mp, assumption)+ apply (erule conjE)+
apply (drule mp, assumption)
apply (rule conjI)

  (* wt_instr \<dots> *)
apply (intro strip)
apply (case_tac "pc < length mt1")

  (* case pc < length mt1 *)
apply (drule spec, drule mp, assumption)
apply assumption

  (* case pc \<ge> length mt1 *)
apply (subgoal_tac "pc = length mt1") prefer 2 apply arith
apply (simp only:)
apply (simp add: nth_append mt_sttp_flatten_def)


  (* check_type \<dots> *)
apply (simp add: start_sttp_resp_def)
apply (drule_tac x="sttp0" in spec, simp, erule exE)
apply (drule_tac x="sttp1" in spec, simp, erule exE)

apply (subgoal_tac "check_type cG (max_ssize (mt1 @ mt2 @ mt3 @ [Some sttp3])) mxr 
                    (OK (Some (sttp_of (f2 sttp1))))")

apply (simp only:)

apply (erule disjE)
    (* case f3 = comb_nil *)
apply (subgoal_tac "((mt1 @ mt2 @ mt3 @ [Some sttp3]) ! Suc (length mt1)) = (Some (snd (f2 sttp1)))")apply (subgoal_tac "mt3 = [] \<and> sttp2 = sttp3")  apply (erule conjE)+
apply (simp add: nth_append)
apply (simp add: comb_nil_def) (* subgoal mt3 = [] \<and> sttp2 = sttp3 *)
apply (simp add: nth_append comb_nil_def) (* subgoal \<dots> ! Suc (length mt1) *)

    (* case start_sttp_resp_cons f3 *)
apply (simp add: start_sttp_resp_cons_def)  
apply (drule_tac x="sttp2" in spec, simp, erule exE)
apply (simp  add: nth_append)

  (* subgoal check_type *)
apply (rule check_type_contracting)
apply (subgoal_tac "((mt1 @ mt2 @ mt3 @ [Some sttp3]) ! length mt1) = (Some sttp1)")
apply (simp add: nth_append)
apply (simp add: nth_append)

apply assumption

(* subgoals *)
apply (rule surj_pair)+
done


lemma compTpExpr_LT_ST_rewr [simp]: "\<lbrakk>
  wf_java_prog G;
  wf_java_mdecl G C ((mn, pTs), rT, (pns, lvars, blk, res));
  local_env G C (mn, pTs) pns lvars \<turnstile> ex :: T;
  is_inited_LT C pTs lvars LT\<rbrakk>
\<Longrightarrow> sttp_of (compTpExpr (pns, lvars, blk, res) G ex (ST, LT)) = (T # ST, LT)"
apply (rule compTpExpr_LT_ST)
apply auto
done




lemma wt_method_compTpExpr_Exprs_corresp: "
  \<lbrakk> jmb = (pns,lvars,blk,res); 
  wf_prog wf_java_mdecl G;
  wf_java_mdecl G C ((mn, pTs), rT, jmb);
  E = (local_env G C (mn, pTs) pns lvars)\<rbrakk> 
\<Longrightarrow> 
 (\<forall> ST LT T bc' f'.
  E \<turnstile> ex :: T \<longrightarrow>  
  (is_inited_LT C pTs lvars LT) \<longrightarrow>
  bc' = (compExpr jmb ex) \<longrightarrow>
  f' = (compTpExpr jmb G ex)
  \<longrightarrow> bc_mt_corresp bc' f' (ST, LT) (comp G) rT (length LT) (length bc'))
 \<and>
 (\<forall> ST LT Ts.
  E \<turnstile> exs [::] Ts \<longrightarrow>
  (is_inited_LT C pTs lvars LT) 
  \<longrightarrow> bc_mt_corresp (compExprs jmb exs) (compTpExprs jmb G exs) (ST, LT) (comp G) rT (length LT) (length (compExprs jmb exs)))"

apply (rule  expr.induct)


(* expresssions *)

(* NewC *)
apply (intro allI impI)
apply (simp only:)
apply (drule NewC_invers)
apply (simp (no_asm_use))
apply (rule bc_mt_corresp_New)
apply (simp add: comp_is_class)

(* Cast *)
apply (intro allI impI)
apply (simp only:)
apply (drule Cast_invers)
apply clarify
apply (simp (no_asm_use))
apply (rule bc_mt_corresp_comb) apply (rule HOL.refl, simp (no_asm_simp), blast)
apply (simp (no_asm_simp), rule bc_mt_corresp_Checkcast)
apply (simp add: comp_is_class)
apply (simp only: compTpExpr_LT_ST)
apply (drule cast_RefT)
apply blast
apply (simp add: start_sttp_resp_def)

(* Lit *)
apply (intro allI impI)
apply (simp only:)
apply (drule Lit_invers)
(* apply (simp (no_asm_use)) *)
apply simp
apply (rule bc_mt_corresp_LitPush)
   apply assumption


(* BinOp *)

apply (intro allI impI)
apply (simp (no_asm_simp) only:)
apply (drule BinOp_invers, erule exE, (erule conjE)+)
apply (case_tac binop)
apply (simp (no_asm_simp))

  (* case Eq *)
apply (subgoal_tac "bc_mt_corresp bc' f' (ST, LT) (comp G) rT (length LT) 0")
prefer 2
  apply (rule bc_mt_corresp_zero) apply (simp add: length_compTpExpr) 
  apply (simp (no_asm_simp))

apply (drule_tac ?bc1.0="[]" and ?bc2.0 = "compExpr jmb expr1" 
  and ?f1.0=comb_nil and ?f2.0 = "compTpExpr jmb G expr1" 
  in bc_mt_corresp_comb_inside)
  apply (simp (no_asm_simp))+
  apply blast
  apply (simp (no_asm_simp) add: length_compTpExpr)+

apply (drule_tac ?bc2.0 = "compExpr jmb expr2" and ?f2.0 = "compTpExpr jmb G expr2" 
  in bc_mt_corresp_comb_inside)
  apply (simp (no_asm_simp))+
  apply (simp only: compTpExpr_LT_ST)
  apply (simp (no_asm_simp) add: length_compTpExpr)
  apply (simp (no_asm_simp))
  apply (simp (no_asm_simp))

apply (drule_tac ?bc1.0 = "compExpr jmb expr1 @ compExpr jmb expr2" 
    and inst = "Ifcmpeq 3" and ?bc3.0 = "[LitPush (Bool False),Goto 2, LitPush (Bool True)]"
  and ?f1.0="compTpExpr jmb G expr1 \<box> compTpExpr jmb G expr2"
  and ?f2.0="popST 2" and ?f3.0="pushST [PrimT Boolean] \<box> popST 1 \<box> pushST [PrimT Boolean]"
  in bc_mt_corresp_comb_wt_instr)
  apply (simp (no_asm_simp) add: length_compTpExpr)+

    (* wt_instr *)
  apply (intro strip)
  apply (simp (no_asm_simp) add: wt_instr_altern_def length_compTpExpr eff_def)
  apply (simp (no_asm_simp) add: norm_eff_def)
  apply (simp (no_asm_simp) only: int_outside_left nat_int)
  apply (simp (no_asm_simp) add: length_compTpExpr)
  apply (simp only: compTpExpr_LT_ST)+
  apply (simp add: eff_def norm_eff_def popST_def pushST_def mt_sttp_flatten_def)
  apply (case_tac Ta) apply (simp (no_asm_simp)) apply (simp (no_asm_simp))
  apply (rule contracting_popST)		(* contracting (popST 2)  *)

apply (drule_tac ?bc1.0 = "compExpr jmb expr1 @ compExpr jmb expr2 @ [Ifcmpeq 3]"
  and ?bc2.0 = "[LitPush (Bool False)]" 
  and ?bc3.0 = "[Goto 2, LitPush (Bool True)]" 
  and ?f1.0 = "compTpExpr jmb G expr1 \<box> compTpExpr jmb G expr2 \<box> popST 2"
  and ?f2.0 = "pushST [PrimT Boolean]" 
  and ?f3.0 = "popST (Suc 0) \<box> pushST [PrimT Boolean]"
  in bc_mt_corresp_comb_inside)
  apply (simp (no_asm_simp))+
  apply (simp add: compTpExpr_LT_ST_rewr popST_def)
  apply (rule_tac T="(PrimT Boolean)" in bc_mt_corresp_LitPush) apply (simp (no_asm_simp))
  apply (simp (no_asm_simp) add: length_compTpExpr)
  apply (simp (no_asm_simp))
  apply (simp (no_asm_simp) add: start_sttp_resp_def)


apply (drule_tac ?bc1.0 = "compExpr jmb expr1 @ compExpr jmb expr2 @ [Ifcmpeq 3, LitPush (Bool False)]" 
    and inst = "Goto 2" and ?bc3.0 = "[LitPush (Bool True)]"
  and ?f1.0="compTpExpr jmb G expr1 \<box> compTpExpr jmb G expr2 \<box> popST 2 \<box> pushST [PrimT Boolean]"
  and ?f2.0="popST 1" and ?f3.0="pushST [PrimT Boolean]"
  in bc_mt_corresp_comb_wt_instr)
  apply (simp (no_asm_simp) add: length_compTpExpr)+

    (* wt_instr *)
  apply (simp (no_asm_simp) add: wt_instr_altern_def length_compTpExpr)
  apply (simp (no_asm_simp) add: eff_def norm_eff_def)
  apply (simp (no_asm_simp) only: int_outside_right nat_int)
  apply (simp (no_asm_simp) add: length_compTpExpr)
  apply (simp only: compTpExpr_LT_ST)+
  apply (simp add: eff_def norm_eff_def popST_def pushST_def)
  apply (rule contracting_popST)		(* contracting (popST 1) *)

apply (drule_tac 
  ?bc1.0 = "compExpr jmb expr1 @ compExpr jmb expr2 @ [Ifcmpeq 3, LitPush (Bool False), Goto 2]" 
  and ?bc2.0 = "[LitPush (Bool True)]"
  and ?bc3.0 = "[]"
  and ?f1.0 = "compTpExpr jmb G expr1 \<box> compTpExpr jmb G expr2 \<box> popST 2 \<box> 
                pushST [PrimT Boolean] \<box> popST (Suc 0)"
  and ?f2.0 = "pushST [PrimT Boolean]"
  and ?f3.0 = "comb_nil" 
  in bc_mt_corresp_comb_inside)
  apply (simp (no_asm_simp))+
  apply (simp add: compTpExpr_LT_ST_rewr popST_def) 
  apply (rule_tac T="(PrimT Boolean)" in bc_mt_corresp_LitPush) apply (simp (no_asm_simp))
  apply (simp (no_asm_simp) add: length_compTpExpr)
  apply (simp (no_asm_simp) add: start_sttp_resp_def)
  apply (simp (no_asm_simp))

apply simp

  (* case Add *)
apply simp
apply (rule bc_mt_corresp_comb) apply (rule HOL.refl) apply simp apply blast
apply (rule bc_mt_corresp_comb, rule HOL.refl) 
   apply (simp only: compTpExpr_LT_ST) 
apply (simp only: compTpExpr_LT_ST) apply blast

apply (simp only: compTpExpr_LT_ST)
apply simp
apply (rule bc_mt_corresp_IAdd)
apply (simp (no_asm_simp) add: start_sttp_resp_def)
apply (simp (no_asm_simp) add: start_sttp_resp_def)


  (* LAcc *)
apply (intro allI impI)
apply (simp only:)
apply (drule LAcc_invers)
apply (frule wf_java_mdecl_length_pTs_pns)
apply clarify
apply (simp add: is_inited_LT_def)
apply (rule bc_mt_corresp_Load)
  apply (rule index_in_bounds) apply simp apply assumption
  apply (rule inited_LT_at_index_no_err)
  apply (rule index_in_bounds) apply simp apply assumption
apply (rule HOL.refl)


  (* LAss *)
apply (intro allI impI)
apply (simp only:)
apply (drule LAss_invers, erule exE, (erule conjE)+)
apply (drule LAcc_invers)
apply (frule wf_java_mdecl_disjoint_varnames, simp add: disjoint_varnames_def)
apply (frule wf_java_mdecl_length_pTs_pns)
apply clarify
apply (simp (no_asm_use))
apply (rule bc_mt_corresp_comb) apply (rule HOL.refl, simp (no_asm_simp), blast)
apply (rule_tac ?bc1.0="[Dup]" and ?bc2.0="[Store (index (pns, lvars, blk, res) vname)]" 
       and ?f1.0="dupST" and ?f2.0="popST (Suc 0)"
       in bc_mt_corresp_comb) 
  apply (simp (no_asm_simp))+
  apply (rule bc_mt_corresp_Dup)
  apply (simp only: compTpExpr_LT_ST)
  apply (simp add: dupST_def is_inited_LT_def)
  apply (rule bc_mt_corresp_Store)
  apply (rule index_in_bounds)
    apply simp apply assumption
  apply (rule sup_loc_update_index, assumption+) 
    apply simp apply assumption+
apply (simp add: start_sttp_resp_def)
apply (simp add: start_sttp_resp_def)

  (* FAcc *)
apply (intro allI impI)
apply (simp only:)
apply (drule FAcc_invers)
apply clarify
apply (simp (no_asm_use))
apply (rule bc_mt_corresp_comb) apply (rule HOL.refl, simp (no_asm_simp), blast) 
  apply (simp (no_asm_simp))
  apply (rule bc_mt_corresp_Getfield) apply assumption+
     apply (fast intro: wt_class_expr_is_class)
apply (simp (no_asm_simp) add: start_sttp_resp_def)


  (* FAss *)
apply (intro allI impI)
apply (simp only:)
apply (drule FAss_invers, erule exE, (erule conjE)+)
apply (drule FAcc_invers)
apply clarify
apply (simp (no_asm_use))
apply (rule bc_mt_corresp_comb) apply (rule HOL.refl) apply simp apply blast
  apply (simp only: compTpExpr_LT_ST)
apply (rule bc_mt_corresp_comb, (rule HOL.refl)+) apply blast
  apply (simp only: compTpExpr_LT_ST)
apply (rule_tac ?bc1.0="[Dup_x1]" and ?bc2.0="[Putfield vname cname]" in bc_mt_corresp_comb) 
  apply (simp (no_asm_simp))+
apply (rule bc_mt_corresp_Dup_x1)
  apply (simp (no_asm_simp) add: dup_x1ST_def)
apply (rule bc_mt_corresp_Putfield) apply assumption+
     apply (fast intro: wt_class_expr_is_class)
apply (simp (no_asm_simp) add: start_sttp_resp_def)
apply (simp (no_asm_simp) add: start_sttp_resp_def)
apply (simp (no_asm_simp) add: start_sttp_resp_def)

(* Call *)
apply (intro allI impI)
apply (simp only:)
apply (drule Call_invers)
apply clarify
apply (simp (no_asm_use))
apply (rule bc_mt_corresp_comb) apply (rule HOL.refl) apply simp apply blast
  apply (simp only: compTpExpr_LT_ST)
apply (rule bc_mt_corresp_comb, (rule HOL.refl)+) apply blast
  apply (simp only: compTpExprs_LT_ST)
  apply (simp (no_asm_simp))
apply (rule bc_mt_corresp_Invoke) apply assumption+
     apply (fast intro: wt_class_expr_is_class)
apply (simp (no_asm_simp) add: start_sttp_resp_def)
apply (rule start_sttp_resp_comb) 
  apply (simp (no_asm_simp))
  apply (simp (no_asm_simp) add: start_sttp_resp_def)


(* expression lists *)
(* nil *) 

apply (intro allI impI)
apply (drule Nil_invers)
apply simp

(* cons *)

apply (intro allI impI)
apply (drule Cons_invers, (erule exE)+, (erule conjE)+)
apply clarify
apply (simp (no_asm_use))
apply (rule bc_mt_corresp_comb) apply (rule HOL.refl) apply simp apply blast
  apply (simp only: compTpExpr_LT_ST)
apply blast
apply simp

done


lemmas wt_method_compTpExpr_corresp [rule_format (no_asm)] = 
  wt_method_compTpExpr_Exprs_corresp [THEN conjunct1]


  (* ********************************************************************** *)




lemma wt_method_compTpStmt_corresp [rule_format (no_asm)]: "
  \<lbrakk> jmb = (pns,lvars,blk,res); 
  wf_prog wf_java_mdecl G;
  wf_java_mdecl G C ((mn, pTs), rT, jmb);
  E = (local_env G C (mn, pTs) pns lvars)\<rbrakk> 
\<Longrightarrow> 
 (\<forall> ST LT T bc' f'.
  E \<turnstile> s\<surd> \<longrightarrow>
  (is_inited_LT C pTs lvars LT) \<longrightarrow>
  bc' = (compStmt jmb s) \<longrightarrow>
  f' = (compTpStmt jmb G s)
  \<longrightarrow> bc_mt_corresp bc' f' (ST, LT) (comp G) rT (length LT) (length bc'))"

apply (rule stmt.induct)

(* Skip *) 
apply (intro allI impI)
apply simp


(* Expr *)
apply (intro allI impI)
apply (drule Expr_invers, erule exE)
apply (simp (no_asm_simp))
apply (rule bc_mt_corresp_comb) apply (rule HOL.refl, simp (no_asm_simp))
apply (rule wt_method_compTpExpr_corresp) apply assumption+
apply (simp add: compTpExpr_LT_ST [of _ pns lvars blk res])+
apply (rule bc_mt_corresp_Pop)
apply (simp add: start_sttp_resp_def)


(* Comp *)
apply (intro allI impI)
apply (drule Comp_invers)
apply clarify
apply (simp (no_asm_use))
apply (rule bc_mt_corresp_comb) apply (rule HOL.refl) 
   apply (simp (no_asm_simp)) apply blast
apply (simp only: compTpStmt_LT_ST) 
apply (simp (no_asm_simp))

(* Cond *)
apply (intro allI impI)
apply (simp (no_asm_simp) only:)
apply (drule Cond_invers, (erule conjE)+)
apply (simp (no_asm_simp))

apply (subgoal_tac "bc_mt_corresp bc' f' (ST, LT) (comp G) rT (length LT) 0")
prefer 2 
apply (rule bc_mt_corresp_zero) 
  apply (simp (no_asm_simp) add: length_compTpStmt length_compTpExpr)
  apply (simp (no_asm_simp))

apply (drule_tac ?bc1.0="[]" and ?bc2.0 = "[LitPush (Bool False)]" 
  and ?bc3.0="compExpr jmb expr @ Ifcmpeq (2 + int (length (compStmt jmb stmt1))) #
            compStmt jmb stmt1 @ Goto (1 + int (length (compStmt jmb stmt2))) #
            compStmt jmb stmt2" 
  and ?f1.0=comb_nil and ?f2.0 = "pushST [PrimT Boolean]" 
  and ?f3.0="compTpExpr jmb G expr \<box> popST 2 \<box> compTpStmt jmb G stmt1 \<box>
            nochangeST \<box> compTpStmt jmb G stmt2"
  in bc_mt_corresp_comb_inside)
  apply (simp (no_asm_simp))+
  apply (rule_tac T="(PrimT Boolean)" in bc_mt_corresp_LitPush)
  apply (simp (no_asm_simp) add: start_sttp_resp_def)+

apply (drule_tac ?bc1.0="[LitPush (Bool False)]" and ?bc2.0 = "compExpr jmb expr"
  and ?bc3.0="Ifcmpeq (2 + int (length (compStmt jmb stmt1))) #
            compStmt jmb stmt1 @ Goto (1 + int (length (compStmt jmb stmt2))) #
            compStmt jmb stmt2" 
  and ?f1.0="pushST [PrimT Boolean]" and ?f2.0 = "compTpExpr jmb G expr"
  and ?f3.0="popST 2 \<box> compTpStmt jmb G stmt1 \<box>
            nochangeST \<box> compTpStmt jmb G stmt2"
  in bc_mt_corresp_comb_inside)
  apply (simp (no_asm_simp))+
  apply (simp (no_asm_simp)  add: pushST_def)
  apply (rule  wt_method_compTpExpr_corresp) apply assumption+ 
      apply (simp (no_asm_simp))+


apply (drule_tac ?bc1.0 = "[LitPush (Bool False)] @ compExpr jmb expr" 
    and inst = "Ifcmpeq (2 + int (length (compStmt jmb stmt1)))" 
  and ?bc3.0 = "compStmt jmb stmt1 @ Goto (1 + int (length (compStmt jmb stmt2))) #
            compStmt jmb stmt2"
  and ?f1.0="pushST [PrimT Boolean] \<box> compTpExpr jmb G expr" and ?f2.0 = "popST 2"
  and ?f3.0="compTpStmt jmb G stmt1 \<box> nochangeST \<box> compTpStmt jmb G stmt2"
  in bc_mt_corresp_comb_wt_instr)
  apply (simp (no_asm_simp) add: length_compTpExpr)+
  apply (simp (no_asm_simp) add: start_sttp_resp_comb)

    (* wt_instr *)
  apply (intro strip)
  apply (rule_tac ts="PrimT Boolean" and ts'="PrimT Boolean" 
    and ST=ST and LT=LT 
    in wt_instr_Ifcmpeq)
  apply (simp (no_asm_simp))
  apply (simp (no_asm_simp) only: int_outside_right nat_int, simp (no_asm_simp))
  apply (simp (no_asm_simp) only: int_outside_right nat_int, simp (no_asm_simp))
    (* current pc *)
  apply (simp add: length_compTpExpr pushST_def)
  apply (simp only: compTpExpr_LT_ST) 
    (* Suc pc *)
  apply (simp add: length_compTpExpr pushST_def)
  apply (simp add: popST_def start_sttp_resp_comb)
    (* jump goal *)
  apply (simp (no_asm_simp) only: int_outside_right nat_int, simp (no_asm_simp))
  apply (simp add: length_compTpExpr pushST_def)
  apply (simp add: popST_def start_sttp_resp_comb length_compTpStmt)
  apply (simp only: compTpStmt_LT_ST)
  apply (simp add: nochangeST_def)
    (* check_type *)
  apply (subgoal_tac "
    (mt_sttp_flatten (f' (ST, LT)) ! length ([LitPush (Bool False)] @ compExpr jmb expr)) = 
    (Some (PrimT Boolean # PrimT Boolean # ST, LT))")
  apply (simp only:)
  apply (simp (no_asm_simp)) apply (rule trans, rule mt_sttp_flatten_comb_length) 
    apply (rule HOL.refl) apply (simp (no_asm_simp) add: length_compTpExpr)
    apply (simp (no_asm_simp) add: length_compTpExpr pushST_def)
    apply (simp only: compTpExpr_LT_ST_rewr) 
    (* contracting\<dots> *)
  apply (rule contracting_popST)

apply (drule_tac 
  ?bc1.0="[LitPush (Bool False)] @ compExpr jmb expr @ 
           [Ifcmpeq (2 + int (length (compStmt jmb stmt1)))] " 
  and ?bc2.0 = "compStmt jmb stmt1"
  and ?bc3.0="Goto (1 + int (length (compStmt jmb stmt2))) # compStmt jmb stmt2"
  and ?f1.0="pushST [PrimT Boolean] \<box> compTpExpr jmb G expr \<box> popST 2" 
  and ?f2.0 = "compTpStmt jmb G stmt1"
  and ?f3.0="nochangeST \<box> compTpStmt jmb G stmt2"
  in bc_mt_corresp_comb_inside)
  apply (simp (no_asm_simp))+
  apply (simp (no_asm_simp) add: pushST_def popST_def compTpExpr_LT_ST)
  apply (simp only: compTpExpr_LT_ST)
  apply (simp (no_asm_simp))
  apply (simp (no_asm_simp) add: length_compTpExpr)+


apply (drule_tac ?bc1.0 = "[LitPush (Bool False)] @ compExpr jmb expr @ [Ifcmpeq (2 + int (length (compStmt jmb stmt1)))] @ compStmt jmb stmt1" 
    and inst = "Goto (1 + int (length (compStmt jmb stmt2)))"
  and ?bc3.0 = "compStmt jmb stmt2"
  and ?f1.0="pushST [PrimT Boolean] \<box> compTpExpr jmb G expr \<box> popST 2 \<box> 
              compTpStmt jmb G stmt1" 
  and ?f2.0 = "nochangeST"
  and ?f3.0="compTpStmt jmb G stmt2"
  in bc_mt_corresp_comb_wt_instr)
  apply (simp (no_asm_simp) add: length_compTpExpr length_compTpStmt)+
  apply (intro strip)
  apply (rule wt_instr_Goto)
  apply (simp (no_asm_simp) only: int_outside_right nat_int, simp (no_asm_simp))
  apply (simp (no_asm_simp) only: int_outside_right nat_int, simp (no_asm_simp))
    (* \<dots> ! nat (int pc + i) = \<dots> ! pc *)
  apply (simp (no_asm_simp) only: int_outside_right nat_int, simp (no_asm_simp))
  apply (simp (no_asm_simp) add: length_compTpExpr length_compTpStmt)
  apply (simp (no_asm_simp) add: pushST_def popST_def nochangeST_def)
  apply (simp only: compTpExpr_LT_ST compTpStmt_LT_ST)
  apply (simp (no_asm_simp) add: pushST_def popST_def nochangeST_def)
  apply (simp only: compTpExpr_LT_ST compTpStmt_LT_ST)
  apply (simp only:)
  apply (simp add: length_compTpExpr length_compTpStmt)
  apply (rule contracting_nochangeST)


apply (drule_tac 
  ?bc1.0= "[LitPush (Bool False)] @ compExpr jmb expr @ 
            [Ifcmpeq (2 + int (length (compStmt jmb stmt1)))] @ 
            compStmt jmb stmt1 @ [Goto (1 + int (length (compStmt jmb stmt2)))]"
  and ?bc2.0 = "compStmt jmb stmt2"
  and ?bc3.0="[]"
  and ?f1.0="pushST [PrimT Boolean] \<box> compTpExpr jmb G expr \<box> popST 2 \<box> 
              compTpStmt jmb G stmt1 \<box> nochangeST"
  and ?f2.0 = "compTpStmt jmb G stmt2"
  and ?f3.0="comb_nil"
  in bc_mt_corresp_comb_inside)
  apply (simp (no_asm_simp))+
  apply (simp (no_asm_simp) add: pushST_def popST_def nochangeST_def compTpExpr_LT_ST)
  apply (simp only: compTpExpr_LT_ST)
  apply (simp (no_asm_simp))
  apply (simp only: compTpStmt_LT_ST)
  apply (simp (no_asm_simp) add: length_compTpExpr length_compTpStmt)+

apply simp


(* Loop *)
apply (intro allI impI)
apply (simp (no_asm_simp) only:)
apply (drule Loop_invers, (erule conjE)+)
apply (simp (no_asm_simp))

apply (subgoal_tac "bc_mt_corresp bc' f' (ST, LT) (comp G) rT (length LT) 0")
prefer 2 
apply (rule bc_mt_corresp_zero) 
  apply (simp (no_asm_simp) add: length_compTpStmt length_compTpExpr)
  apply (simp (no_asm_simp))

apply (drule_tac ?bc1.0="[]" and ?bc2.0 = "[LitPush (Bool False)]" 
  and ?bc3.0="compExpr jmb expr @ Ifcmpeq (2 + int (length (compStmt jmb stmt))) #
            compStmt jmb stmt @ 
            [Goto (-2 + (- int (length (compStmt jmb stmt)) - int (length (compExpr jmb expr))))]" 
  and ?f1.0=comb_nil and ?f2.0 = "pushST [PrimT Boolean]" 
  and ?f3.0="compTpExpr jmb G expr \<box> popST 2 \<box> compTpStmt jmb G stmt \<box> nochangeST"
  in bc_mt_corresp_comb_inside)
  apply (simp (no_asm_simp))+
  apply (rule_tac T="(PrimT Boolean)" in bc_mt_corresp_LitPush)
  apply (simp (no_asm_simp) add: start_sttp_resp_def)+

apply (drule_tac ?bc1.0="[LitPush (Bool False)]" and ?bc2.0 = "compExpr jmb expr"
  and ?bc3.0="Ifcmpeq (2 + int (length (compStmt jmb stmt))) #
            compStmt jmb stmt @ 
            [Goto (-2 + (- int (length (compStmt jmb stmt)) - int (length (compExpr jmb expr))))]" 
  and ?f1.0="pushST [PrimT Boolean]" and ?f2.0 = "compTpExpr jmb G expr"
  and ?f3.0="popST 2 \<box> compTpStmt jmb G stmt \<box> nochangeST"
  in bc_mt_corresp_comb_inside)
  apply (simp (no_asm_simp))+
  apply (simp (no_asm_simp)  add: pushST_def)
  apply (rule  wt_method_compTpExpr_corresp) apply assumption+ 
      apply (simp (no_asm_simp))+


apply (drule_tac ?bc1.0 = "[LitPush (Bool False)] @ compExpr jmb expr" 
    and inst = "Ifcmpeq (2 + int (length (compStmt jmb stmt)))" 
  and ?bc3.0 = "compStmt jmb stmt @ 
       [Goto (-2 + (- int (length (compStmt jmb stmt)) - int (length (compExpr jmb expr))))]"
  and ?f1.0="pushST [PrimT Boolean] \<box> compTpExpr jmb G expr" and ?f2.0 = "popST 2"
  and ?f3.0="compTpStmt jmb G stmt \<box> nochangeST"
  in bc_mt_corresp_comb_wt_instr)
  apply (simp (no_asm_simp) add: length_compTpExpr)+
  apply (simp (no_asm_simp) add: start_sttp_resp_comb)

    (* wt_instr *)
  apply (intro strip)
  apply (rule_tac ts="PrimT Boolean" and ts'="PrimT Boolean" 
    and ST=ST and LT=LT 
    in wt_instr_Ifcmpeq)
  apply (simp (no_asm_simp))
  apply (simp (no_asm_simp) only: int_outside_right nat_int, simp (no_asm_simp))
  apply (simp (no_asm_simp) only: int_outside_right nat_int, simp (no_asm_simp))
    (* current pc *)
  apply (simp add: length_compTpExpr pushST_def)
  apply (simp only: compTpExpr_LT_ST) 
    (* Suc pc *)
  apply (simp add: length_compTpExpr pushST_def)
  apply (simp add: popST_def start_sttp_resp_comb)
    (* jump goal *)
  apply (simp (no_asm_simp) only: int_outside_right nat_int, simp (no_asm_simp))
  apply (simp add: length_compTpExpr pushST_def)
  apply (simp add: popST_def start_sttp_resp_comb length_compTpStmt)
  apply (simp only: compTpStmt_LT_ST)
  apply (simp add: nochangeST_def)
    (* check_type *)
  apply (subgoal_tac "
    (mt_sttp_flatten (f' (ST, LT)) ! length ([LitPush (Bool False)] @ compExpr jmb expr)) = 
    (Some (PrimT Boolean # PrimT Boolean # ST, LT))")
  apply (simp only:)
  apply (simp (no_asm_simp)) apply (rule trans, rule mt_sttp_flatten_comb_length) 
    apply (rule HOL.refl) apply (simp (no_asm_simp) add: length_compTpExpr)
    apply (simp (no_asm_simp) add: length_compTpExpr pushST_def)
    apply (simp only: compTpExpr_LT_ST_rewr) 
    (* contracting\<dots> *)
  apply (rule contracting_popST)

apply (drule_tac 
  ?bc1.0="[LitPush (Bool False)] @ compExpr jmb expr @ 
           [Ifcmpeq (2 + int (length (compStmt jmb stmt)))] " 
  and ?bc2.0 = "compStmt jmb stmt"
  and ?bc3.0="[Goto (-2 + (- int (length (compStmt jmb stmt)) - int (length (compExpr jmb expr))))]"
  and ?f1.0="pushST [PrimT Boolean] \<box> compTpExpr jmb G expr \<box> popST 2" 
  and ?f2.0 = "compTpStmt jmb G stmt"
  and ?f3.0="nochangeST"
  in bc_mt_corresp_comb_inside)
  apply (simp (no_asm_simp))+
  apply (simp (no_asm_simp) add: pushST_def popST_def compTpExpr_LT_ST)
  apply (simp only: compTpExpr_LT_ST)
  apply (simp (no_asm_simp))
  apply (simp (no_asm_simp) add: length_compTpExpr)+


apply (drule_tac ?bc1.0 = "[LitPush (Bool False)] @ compExpr jmb expr @ [Ifcmpeq (2 + int (length (compStmt jmb stmt)))] @ compStmt jmb stmt" 
    and inst = "Goto (-2 + (- int (length (compStmt jmb stmt)) - int (length (compExpr jmb expr))))"
  and ?bc3.0 = "[]"
  and ?f1.0="pushST [PrimT Boolean] \<box> compTpExpr jmb G expr \<box> popST 2 \<box> 
              compTpStmt jmb G stmt" 
  and ?f2.0 = "nochangeST"
  and ?f3.0="comb_nil"
  in bc_mt_corresp_comb_wt_instr)
  apply (simp (no_asm_simp) add: length_compTpExpr length_compTpStmt)+ 
  apply (intro strip)
  apply (rule wt_instr_Goto)
  apply arith
  apply arith
    (* \<dots> ! nat (int pc + i) = \<dots> ! pc *)
  apply (simp (no_asm_simp))
  apply (simp (no_asm_simp) add: length_compTpExpr length_compTpStmt)
  apply (simp (no_asm_simp) add: pushST_def popST_def nochangeST_def)
  apply (simp only: compTpExpr_LT_ST compTpStmt_LT_ST)
  apply (simp (no_asm_simp) add: length_compTpExpr length_compTpStmt)
  apply (simp only: compTpExpr_LT_ST compTpStmt_LT_ST)
  apply (simp (no_asm_simp) add: pushST_def popST_def nochangeST_def)
  apply (simp (no_asm_simp) add: length_compTpExpr length_compTpStmt)
  apply (simp only: compTpExpr_LT_ST compTpStmt_LT_ST)

  apply (simp add: length_compTpExpr length_compTpStmt) (* check_type *)
    apply (simp add: pushST_def popST_def compTpExpr_LT_ST compTpStmt_LT_ST)
  apply (rule contracting_nochangeST)
apply simp

done


  (**********************************************************************************)



lemma wt_method_compTpInit_corresp: "\<lbrakk> jmb = (pns,lvars,blk,res); 
  wf_java_mdecl G C ((mn, pTs), rT, jmb); mxr = length LT;
  length LT = (length pns) + (length lvars) + 1;  vn \<in> set (map fst lvars);
  bc = (compInit jmb (vn,ty)); f = (compTpInit jmb (vn,ty));
  is_type G ty \<rbrakk>
  \<Longrightarrow> bc_mt_corresp bc f (ST, LT) (comp G) rT mxr (length bc)"
apply (simp add: compInit_def compTpInit_def split_beta)
apply (rule_tac ?bc1.0="[load_default_val ty]" and ?bc2.0="[Store (index jmb vn)]" 
  in bc_mt_corresp_comb) 
  apply simp+
  apply (simp add: load_default_val_def)
   apply (rule typeof_default_val [THEN exE]) 

  apply (rule bc_mt_corresp_LitPush_CT) apply assumption
    apply (simp add: comp_is_type)
apply (simp add: pushST_def)
  apply (rule bc_mt_corresp_Store_init)
  apply simp
  apply (rule index_length_lvars [THEN conjunct2])
apply auto
done


lemma wt_method_compTpInitLvars_corresp_aux [rule_format (no_asm)]: "
  \<forall> lvars_pre lvars0 ST LT.
  jmb = (pns,lvars0,blk,res) \<and>
  lvars0 = (lvars_pre @ lvars) \<and>
  length LT = (length pns) + (length lvars0) + 1 \<and>
  wf_java_mdecl G C ((mn, pTs), rT, jmb)
 \<longrightarrow> bc_mt_corresp (compInitLvars jmb lvars) (compTpInitLvars jmb lvars) (ST, LT) (comp G) rT 
       (length LT) (length (compInitLvars jmb lvars))"
apply (induct lvars)
apply (simp add: compInitLvars_def)

apply (intro strip, (erule conjE)+)
apply (subgoal_tac "\<exists> vn ty. a = (vn, ty)")
  prefer 2 apply (simp (no_asm_simp)) 
  apply ((erule exE)+, simp (no_asm_simp))
apply (drule_tac x="lvars_pre @ [a]" in spec)
apply (drule_tac x="lvars0" in spec)
apply (simp (no_asm_simp) add: compInitLvars_def)
apply (rule_tac ?bc1.0="compInit jmb a" and ?bc2.0="compInitLvars jmb list"
  in bc_mt_corresp_comb)
apply (simp (no_asm_simp) add: compInitLvars_def)+

apply (rule_tac vn=vn and ty=ty in wt_method_compTpInit_corresp)
apply assumption+
apply (simp (no_asm_simp))+ 
apply (simp add: wf_java_mdecl_def)	(* is_type G ty *)
apply (simp add: compTpInit_def storeST_def pushST_def)
apply simp
done


lemma wt_method_compTpInitLvars_corresp: "\<lbrakk> jmb = (pns,lvars,blk,res); 
  wf_java_mdecl G C ((mn, pTs), rT, jmb);
  length LT = (length pns) + (length lvars) + 1; mxr = (length LT);
  bc = (compInitLvars jmb lvars); f= (compTpInitLvars jmb lvars) \<rbrakk>
  \<Longrightarrow> bc_mt_corresp bc f (ST, LT) (comp G) rT mxr (length bc)"
apply (simp only:)
apply (subgoal_tac "bc_mt_corresp (compInitLvars (pns, lvars, blk, res) lvars)
        (compTpInitLvars (pns, lvars, blk, res) lvars) (ST, LT) (TranslComp.comp G) rT
        (length LT) (length (compInitLvars (pns, lvars, blk, res) lvars))")
apply simp
apply (rule_tac lvars_pre="[]" in wt_method_compTpInitLvars_corresp_aux)
apply auto
done


  (**********************************************************************************)



lemma wt_method_comp_wo_return: "\<lbrakk> wf_prog wf_java_mdecl G;
  wf_java_mdecl G C ((mn, pTs), rT, jmb); 
  bc = compInitLvars jmb lvars @ compStmt jmb blk @ compExpr jmb res;
  jmb = (pns,lvars,blk,res); 
  f = (compTpInitLvars jmb lvars \<box> compTpStmt jmb G blk \<box> compTpExpr jmb G res);
  sttp = (start_ST, start_LT C pTs (length lvars));
  li = (length (inited_LT C pTs lvars))
  \<rbrakk>
\<Longrightarrow> bc_mt_corresp bc f sttp (comp G) rT  li (length bc)"
apply (subgoal_tac "\<exists> E. (E = (local_env G C (mn, pTs) pns lvars) \<and> E \<turnstile> blk \<surd> \<and> 
                         (\<exists>T. E\<turnstile>res::T \<and> G\<turnstile>T\<preceq>rT))")
   apply (erule exE, (erule conjE)+)+
apply (simp only:)
apply (rule bc_mt_corresp_comb) apply (rule HOL.refl)+

  (* InitLvars *)
apply (rule wt_method_compTpInitLvars_corresp) 
   apply assumption+
   apply (simp only:)
   apply (simp (no_asm_simp) add: start_LT_def) 
       apply (rule wf_java_mdecl_length_pTs_pns, assumption)
   apply (simp (no_asm_simp) only: start_LT_def)
   apply (simp (no_asm_simp) add: inited_LT_def)+

apply (rule bc_mt_corresp_comb) apply (rule HOL.refl)+
   apply (simp (no_asm_simp) add: compTpInitLvars_LT_ST)

     (* stmt *)
apply (simp only: compTpInitLvars_LT_ST)
apply (subgoal_tac "(Suc (length pTs + length lvars)) = (length (inited_LT C pTs lvars))")
   prefer 2 apply (simp (no_asm_simp) add: inited_LT_def)
apply (simp only:)
apply (rule_tac s=blk in wt_method_compTpStmt_corresp)
   apply assumption+
   apply (simp only:)+
   apply (simp (no_asm_simp) add: is_inited_LT_def)
   apply (simp only:)+

     (* expr *)
apply (simp only: compTpInitLvars_LT_ST compTpStmt_LT_ST is_inited_LT_def)
apply (subgoal_tac "(Suc (length pTs + length lvars)) = (length (inited_LT C pTs lvars))")
   prefer 2 apply (simp (no_asm_simp) add: inited_LT_def)
apply (simp only:)
apply (rule_tac ex=res in wt_method_compTpExpr_corresp)
   apply assumption+
   apply (simp only:)+
   apply (simp (no_asm_simp) add: is_inited_LT_def)
   apply (simp only:)+

     (* start_sttp_resp *)
apply (simp add: start_sttp_resp_comb)+

  (* subgoal *)
apply (simp add: wf_java_mdecl_def local_env_def) 
done


  (**********************************************************************************)



lemma check_type_start: "\<lbrakk> wf_mhead cG (mn, pTs) rT; is_class cG C\<rbrakk>
  \<Longrightarrow> check_type cG (length start_ST) (Suc (length pTs + mxl))
              (OK (Some (start_ST, start_LT C pTs mxl)))"
apply (simp add: check_type_def wf_mhead_def start_ST_def start_LT_def)
apply (simp add: check_type_simps)
apply (simp only: list_def)
apply (auto simp: err_def)
apply (subgoal_tac "set (replicate mxl Err) \<subseteq>  {Err}")
apply blast
apply (rule subset_replicate)
done


lemma wt_method_comp_aux: "\<lbrakk>   bc' = bc @ [Return]; f' = (f \<box> nochangeST);
  bc_mt_corresp bc f sttp0 cG rT (1+length pTs+mxl) (length bc);
  start_sttp_resp_cons f';
  sttp0 = (start_ST, start_LT C pTs mxl);
  mxs = max_ssize (mt_of (f' sttp0));
  wf_mhead cG (mn, pTs) rT; is_class cG C;
  sttp_of (f sttp0) = (T # ST, LT);

  check_type cG mxs (1+length pTs+mxl) (OK (Some (T # ST, LT))) \<longrightarrow>
  wt_instr_altern Return cG rT (mt_of (f' sttp0)) mxs (1+length pTs+mxl) 
         (Suc (length bc)) empty_et (length bc)
\<rbrakk>
\<Longrightarrow> wt_method_altern cG C pTs rT mxs mxl bc' empty_et (mt_of (f' sttp0))"
apply (subgoal_tac "check_type cG (length start_ST) (Suc (length pTs + mxl))
              (OK (Some (start_ST, start_LT C pTs mxl)))")
apply (subgoal_tac "check_type cG mxs (1+length pTs+mxl) (OK (Some (T # ST, LT)))")

apply (simp add: wt_method_altern_def)

  (* length (.. f ..) = length bc *)
apply (rule conjI)
apply (simp add: bc_mt_corresp_def split_beta)

  (* check_bounded *)
apply (rule conjI)
apply (simp add: bc_mt_corresp_def split_beta check_bounded_def) 
apply (erule conjE)+
apply (intro strip)
apply (subgoal_tac "pc < (length bc) \<or> pc = length bc")
  apply (erule disjE)
    (* case  pc < length bc *)
    apply (subgoal_tac "(bc' ! pc) = (bc ! pc)")
    apply (simp add: wt_instr_altern_def eff_def)
      (* subgoal *)
    apply (simp add: nth_append)
    (* case  pc = length bc *)
    apply (subgoal_tac "(bc' ! pc) = Return")
    apply (simp add: wt_instr_altern_def)
      (* subgoal *)
    apply (simp add: nth_append)

    (* subgoal pc < length bc \<or> pc = length bc *)
apply arith

  (* wt_start *)
apply (rule conjI)
apply (simp add: wt_start_def start_sttp_resp_cons_def split_beta)
  apply (drule_tac x=sttp0 in spec) apply (erule exE)
  apply (simp add: mt_sttp_flatten_def start_ST_def start_LT_def)

  (* wt_instr *)
apply (intro strip)
apply (subgoal_tac "pc < (length bc) \<or> pc = length bc")
apply (erule disjE)

  (* pc < (length bc) *)
apply (simp (no_asm_use) add: bc_mt_corresp_def mt_sttp_flatten_def split_beta)
apply (erule conjE)+
apply (drule mp, assumption)+
apply (erule conjE)+
apply (drule spec, drule mp, assumption)
apply (simp add: nth_append)
apply (simp (no_asm_simp) add: comb_def split_beta nochangeST_def)

  (* pc = length bc *)
apply (simp add: nth_append)

  (* subgoal pc < (length bc) \<or> pc = length bc *)
apply arith

  (* subgoals *)
apply (simp (no_asm_use) add: bc_mt_corresp_def split_beta)
apply (subgoal_tac "check_type cG (length (fst sttp0)) (Suc (length pTs + mxl))
         (OK (Some sttp0))")
apply ((erule conjE)+, drule mp, assumption)
apply (simp add: nth_append)
apply (simp (no_asm_simp) add: comb_def nochangeST_def split_beta)
apply (simp (no_asm_simp))

apply (rule check_type_start, assumption+)
done


lemma wt_instr_Return: "\<lbrakk>fst f ! pc = Some (T # ST, LT); (G \<turnstile> T \<preceq> rT); pc < max_pc;
  check_type (TranslComp.comp G) mxs mxr (OK (Some (T # ST, LT)))
  \<rbrakk>
  \<Longrightarrow> wt_instr_altern Return (comp G) rT  (mt_of f) mxs mxr max_pc empty_et pc"
  apply (case_tac "(mt_of f ! pc)")
  apply (simp  add: wt_instr_altern_def eff_def norm_eff_def app_def)+
  apply (drule sym)
  apply (simp add: comp_widen xcpt_app_def)
  done


theorem wt_method_comp: "
  \<lbrakk> wf_java_prog G; (C, D, fds, mths) \<in> set G; jmdcl \<in> set mths;
  jmdcl = ((mn,pTs), rT, jmb);
  mt = (compTpMethod G C jmdcl);
  (mxs, mxl, bc, et) = mtd_mb (compMethod G C jmdcl) \<rbrakk>
  \<Longrightarrow> wt_method (comp G) C pTs rT mxs mxl bc et mt"

  (* show statement for wt_method_altern *)
apply (rule wt_method_altern_wt_method)

apply (subgoal_tac "wf_java_mdecl G C jmdcl")
apply (subgoal_tac "wf_mhead G (mn, pTs) rT")
apply (subgoal_tac "is_class G C")
apply (subgoal_tac "\<forall> jmb. \<exists> pns lvars blk res. jmb = (pns, lvars, blk, res)")
   apply (drule_tac x=jmb in spec, (erule exE)+)
apply (subgoal_tac "\<exists> E. (E = (local_env G C (mn, pTs) pns lvars) \<and> E \<turnstile> blk \<surd> \<and> 
                         (\<exists>T. E\<turnstile>res::T \<and> G\<turnstile>T\<preceq>rT))")
   apply (erule exE, (erule conjE)+)+
apply (simp add: compMethod_def compTpMethod_def split_beta)
apply (rule_tac T=T and LT="inited_LT C pTs lvars" and ST=start_ST in wt_method_comp_aux)

  (* bc *)
apply (simp only: append_assoc [THEN sym])

  (* comb *)
apply (simp only: comb_assoc [THEN sym])

  (* bc_corresp *)
apply (rule wt_method_comp_wo_return)
  apply assumption+
  apply (simp (no_asm_use) only: append_assoc)
  apply (rule HOL.refl)
  apply (simp (no_asm_simp))+
  apply (simp (no_asm_simp) add: inited_LT_def)

  (* start_sttp_resp *)
apply (simp add: start_sttp_resp_cons_comb_cons_r)+

  (* wf_mhead / is_class *)
apply (simp add: wf_mhead_def comp_is_type)
apply (simp add: comp_is_class)

  (* sttp_of .. = (T # ST, LT) *)
apply (simp (no_asm_simp) add: compTpInitLvars_LT_ST compTpExpr_LT_ST compTpStmt_LT_ST is_inited_LT_def)
apply (subgoal_tac "(snd (compTpInitLvars (pns, lvars, blk, res) lvars
                              (start_ST, start_LT C pTs (length lvars))))
                = (start_ST, inited_LT C pTs lvars)") 
   prefer 2 apply (rule compTpInitLvars_LT_ST) apply (rule HOL.refl) apply assumption
apply (simp only:)
apply (subgoal_tac "(snd (compTpStmt (pns, lvars, blk, res) G blk
                       (start_ST, inited_LT C pTs lvars))) 
                = (start_ST, inited_LT C pTs lvars)") 
   prefer 2 apply (erule conjE)+
   apply (rule compTpStmt_LT_ST) apply (rule HOL.refl) apply assumption+
   apply (simp only:)+ apply (simp (no_asm_simp) add: is_inited_LT_def)
apply (simp only:)
apply (rule compTpExpr_LT_ST) apply (rule HOL.refl) apply assumption+
   apply (simp only:)+ apply (simp (no_asm_simp) add: is_inited_LT_def)


   (* Return *)
apply (intro strip)
apply (rule_tac T=T and ST=start_ST and LT="inited_LT C pTs lvars" in wt_instr_Return)
apply (simp (no_asm_simp) add: nth_append 
  length_compTpInitLvars length_compTpStmt length_compTpExpr)
apply (simp only: compTpInitLvars_LT_ST compTpStmt_LT_ST compTpExpr_LT_ST 
  nochangeST_def)
apply (simp only: is_inited_LT_def compTpStmt_LT_ST compTpExpr_LT_ST)
apply (simp (no_asm_simp))+
apply simp

  (* subgoal \<exists> E. \<dots> *)
apply (simp add: wf_java_mdecl_def local_env_def)

  (* subgoal jmb = (\<dots>) *)
apply (simp only: split_paired_All, simp)

  (* subgoal is_class / wf_mhead / wf_java_mdecl *)
apply (blast intro: methd [THEN conjunct2])
apply (frule wf_prog_wf_mdecl, assumption+) apply (simp only:) apply (simp add: wf_mdecl_def)
apply (rule wf_java_prog_wf_java_mdecl, assumption+)
done


lemma comp_set_ms: "(C, D, fs, cms)\<in>set (comp G) 
  \<Longrightarrow> \<exists> ms. (C, D, fs, ms) \<in>set G   \<and> cms = map (compMethod G C) ms"
by (auto simp: comp_def compClass_def)


  (* ---------------------------------------------------------------------- *)

section "Main Theorem"
  (* MAIN THEOREM: 
  Methodtype computed by comp is correct for bytecode generated by compTp *)
theorem wt_prog_comp: "wf_java_prog G  \<Longrightarrow> wt_jvm_prog (comp G) (compTp G)"
apply (simp add: wf_prog_def)

apply (subgoal_tac "wf_java_prog G") prefer 2 apply (simp add: wf_prog_def)
apply (simp (no_asm_simp) add: wf_prog_def wt_jvm_prog_def)
apply (simp add: comp_ws_prog)

apply (intro strip)
apply (subgoal_tac "\<exists> C D fs cms. c = (C, D, fs, cms)")
apply clarify
apply (frule comp_set_ms)
apply clarify
apply (drule bspec, assumption)
apply (rule conjI)

  (* wf_mrT *)
apply (case_tac "C = Object")
apply (simp add: wf_mrT_def)
apply (subgoal_tac "is_class G D")
apply (simp add: comp_wf_mrT)
apply (simp add: wf_prog_def ws_prog_def ws_cdecl_def)
apply blast

  (* wf_cdecl_mdecl *)
apply (simp add: wf_cdecl_mdecl_def)
apply (simp add: split_beta)
apply (intro strip)

  (* show wt_method \<dots> *)
apply (subgoal_tac "\<exists> sig rT mb. x = (sig, rT, mb)") 
apply (erule exE)+
apply (simp (no_asm_simp) add: compMethod_def split_beta)
apply (erule conjE)+
apply (drule_tac x="(sig, rT, mb)" in bspec) apply simp
apply (rule_tac mn="fst sig" and pTs="snd sig" in wt_method_comp)
  apply assumption+
  apply simp
apply (simp (no_asm_simp) add: compTp_def)
apply (simp (no_asm_simp) add: compMethod_def split_beta)
apply (frule WellForm.methd) apply assumption+
apply simp
apply simp
apply (simp add: compMethod_def split_beta)
apply auto
done



  (**********************************************************************************)

declare split_paired_All [simp add]
declare split_paired_Ex [simp add]


end
