(*  Title:      HOL/MicroJava/Comp/LemmasComp.thy
    ID:         $Id$
    Author:     Martin Strecker
    Copyright   GPL 2002
*)

(* Lemmas for compiler correctness proof *)

theory LemmasComp = TranslComp:

(**********************************************************************)
(* misc lemmas *)

lemma split_pairs: "(\<lambda>(a,b). (F a b)) (ab) = F (fst ab) (snd ab)"
proof -
  have "(\<lambda>(a,b). (F a b)) (fst ab,snd ab) = F (fst ab) (snd ab)"
    by (simp add: split_def)
  then show ?thesis by simp
qed


lemma c_hupd_conv: 
  "c_hupd h' (xo, (h,l)) = (xo, (if xo = None then h' else h),l)"
by (simp add: c_hupd_def)

lemma gl_c_hupd [simp]: "(gl (c_hupd h xs)) = (gl xs)"
by (simp add: gl_def c_hupd_def split_pairs)

lemma c_hupd_xcpt_invariant [simp]: "gx (c_hupd h' (xo, st)) = xo"
by (case_tac st, simp only: c_hupd_conv gx_conv)

(* not added to simpset because of interference with c_hupd_conv *)
lemma c_hupd_hp_invariant: "gh (c_hupd hp (None, st)) = hp"
by (case_tac st, simp add: c_hupd_conv gh_def)


(**********************************************************************)
(* invariance of properties under compilation *)

lemma comp_class_imp:
  "(class G C = Some(D, fs, ms)) \<Longrightarrow> 
  (class (comp G) C = Some(D, fs, map (compMethod G C) ms))"
apply (simp add: class_def comp_def compClass_def)
apply (rule HOL.trans)
apply (rule map_of_map2)
apply auto
done

lemma comp_class_None: 
"(class G C = None) = (class (comp G) C = None)"
apply (simp add: class_def comp_def compClass_def)
apply (simp add: map_of_in_set)
apply (simp add: image_compose [THEN sym] o_def split_beta del: image_compose)
done

lemma comp_is_class: "is_class G C = is_class (comp G) C"
by (case_tac "class G C", auto simp: is_class_def comp_class_None dest: comp_class_imp)


lemma comp_is_type: "is_type G T = is_type (comp G) T"
  by ((cases T),simp,(induct G)) ((simp),(simp only: comp_is_class),(simp add: comp_is_class),(simp only: comp_is_class))

lemma SIGMA_cong: "\<lbrakk> A = B; !!x. x \<in> B \<Longrightarrow> C x = D x \<rbrakk> \<Longrightarrow> (\<Sigma> x \<in> A. C x) = (\<Sigma> x \<in> B. D x)"
by auto

lemma comp_classname: "is_class G C \<Longrightarrow> fst (the (class G C)) = fst (the (class (comp G) C))"
by (case_tac "class G C", auto simp: is_class_def dest: comp_class_imp)


lemma comp_subcls1: "subcls1 G = subcls1 (comp G)"
apply (simp add: subcls1_def2 comp_is_class)
apply (rule SIGMA_cong, simp)
apply (simp add: comp_is_class [THEN sym])
apply (simp add: comp_classname)
done

lemma comp_subcls: "(subcls1 G)^* = (subcls1 (comp G))^*"
  by (induct G) (simp_all add: comp_def comp_subcls1)

lemma comp_widen: "((ty1,ty2) \<in> widen G) = ((ty1,ty2) \<in> widen (comp G))"
  apply rule
  apply (cases "(ty1,ty2)" G rule: widen.cases) 
  apply (simp_all add: comp_subcls widen.null)
  apply (cases "(ty1,ty2)" "comp G" rule: widen.cases) 
  apply (simp_all add: comp_subcls widen.null)
  done

lemma comp_cast: "((ty1,ty2) \<in> cast G) = ((ty1,ty2) \<in> cast (comp G))"
  apply rule
  apply (cases "(ty1,ty2)" G rule: cast.cases)
  apply (simp_all add: comp_subcls cast.widen cast.subcls)
  apply (cases "(ty1,ty2)" "comp G" rule: cast.cases) 
  apply (simp_all add: comp_subcls cast.widen cast.subcls)
  done

lemma comp_cast_ok: "cast_ok G = cast_ok (comp G)"
  by (simp add: expand_fun_eq cast_ok_def comp_widen)


lemma comp_wf_fdecl: "wf_fdecl G fd  \<Longrightarrow> wf_fdecl (comp G) fd"
apply (case_tac fd)
apply (simp add: wf_fdecl_def comp_is_type)
done

lemma comp_wf_syscls: "wf_syscls G = wf_syscls (comp G)"
apply (simp add: wf_syscls_def comp_def compClass_def split_beta)
apply (simp only: image_compose [THEN sym])
apply (subgoal_tac "(Fun.comp fst (\<lambda>(C, cno::cname, fdls::fdecl list, jmdls). (C, cno, fdls, map (compMethod G C) jmdls))) = fst")
(*
apply (subgoal_tac "(fst o (\<lambda>(C, cno::cname, fdls::fdecl list, jmdls). (C, cno, fdls, map (compMethod G C) jmdls))) = fst")
*)
apply (simp del: image_compose)
apply (simp add: expand_fun_eq split_beta)
done


lemma comp_wf_mhead: "wf_mhead G S rT =  wf_mhead (comp G) S rT"
by (simp add: wf_mhead_def split_beta comp_is_type)

lemma comp_wf_mdecl: "\<lbrakk> wf_mdecl wf_mb G C jmdl;
  (wf_mb G C jmdl) \<longrightarrow> (wf_mb_comp (comp G) C (compMethod G C jmdl)) \<rbrakk> 
 \<Longrightarrow> 
  wf_mdecl wf_mb_comp (comp G) C (compMethod G C jmdl)"
by (simp add: wf_mdecl_def wf_mhead_def comp_is_type split_beta compMethod_def)


lemma comp_class_rec: " wf ((subcls1 G)^-1) \<Longrightarrow> 
class_rec (comp G) C t f = 
  class_rec G C t (\<lambda> C' fs' ms' r'. f C' fs' (map (compMethod G C') ms') r')"
apply (rule_tac a = C in  wf_induct) apply assumption
apply (subgoal_tac "wf ((subcls1 (comp G))\<inverse>)")
apply (subgoal_tac "(class G x = None) \<or> (\<exists> D fs ms. (class G x = Some (D, fs, ms)))")
apply (erule disjE)

  (* case class G x = None *)
apply (simp (no_asm_simp) add: class_rec_def comp_subcls1 wfrec cut_apply)
apply (simp add: comp_class_None)

  (* case \<exists> D fs ms. (class G x = Some (D, fs, ms)) *)
apply (erule exE)+
apply (frule comp_class_imp)
apply (frule_tac G="comp G" and C=x and t=t and f=f in class_rec_lemma)
  apply assumption
apply (frule_tac G=G and C=x and t=t 
   and f="(\<lambda>C' fs' ms'. f C' fs' (map (compMethod G C') ms'))" in class_rec_lemma)
  apply assumption
apply (simp only:)

apply (case_tac "x = Object")
  apply simp
  apply (frule subcls1I, assumption)
    apply (drule_tac x=D in spec, drule mp, simp)
    apply simp

  (* subgoals *)
apply (case_tac "class G x")
apply auto
apply (simp add: comp_subcls1)
done

lemma comp_fields: "wf ((subcls1 G)^-1) \<Longrightarrow> 
  fields (G,C) = fields (comp G,C)" 
by (simp add: fields_def comp_class_rec)

lemma comp_field: "wf ((subcls1 G)^-1) \<Longrightarrow> 
  field (G,C) = field (comp G,C)" 
by (simp add: field_def comp_fields)



lemma class_rec_relation [rule_format (no_asm)]: "\<lbrakk>  wf_prog wf_mb G;
  \<forall> fs ms. R (f1 Object fs ms t1) (f2 Object fs ms t2);
   \<forall> C fs ms r1 r2. (R r1 r2) \<longrightarrow> (R (f1 C fs ms r1) (f2 C fs ms r2)) \<rbrakk>
  \<Longrightarrow> ((class G C) \<noteq> None) \<longrightarrow> 
  R (class_rec G C t1 f1) (class_rec G C t2 f2)"
apply (frule wf_subcls1) (* establish wf ((subcls1 G)^-1) *)
apply (rule_tac a = C in  wf_induct) apply assumption
apply (intro strip)
apply (subgoal_tac "(\<exists>D rT mb. class G x = Some (D, rT, mb))")
  apply (erule exE)+
apply (frule_tac C=x and t=t1 and f=f1 in class_rec_lemma)
  apply assumption
apply (frule_tac C=x and t=t2 and f=f2 in class_rec_lemma)
  apply assumption
apply (simp only:)

apply (case_tac "x = Object")
  apply simp
  apply (frule subcls1I, assumption)
    apply (drule_tac x=D in spec, drule mp, simp)
    apply simp
    apply (subgoal_tac "(\<exists>D' rT' mb'. class G D = Some (D', rT', mb'))")
    apply blast

  (* subgoals *)

apply (frule class_wf) apply assumption
apply (simp add: wf_cdecl_def is_class_def)

apply (simp add: subcls1_def2 is_class_def)
done


syntax
  mtd_mb :: "cname \<times> ty \<times> 'c \<Rightarrow> 'c"
translations
  "mtd_mb" => "Fun.comp snd snd"


lemma map_of_map_fst: "\<lbrakk> map_of (map f xs) k = Some e; inj f;
  \<forall>x\<in>set xs. fst (f x) = fst x; \<forall>x\<in>set xs. fst (g x) = fst x \<rbrakk>
  \<Longrightarrow>  map_of (map g xs) k = Some (snd (g ((inv f) (k, e))))"
apply (induct xs)
apply simp
apply (simp del: split_paired_All)
apply (case_tac "k = fst a")
apply (simp del: split_paired_All)
apply (subgoal_tac "(fst a, e)  = f a")
apply simp
apply (rule_tac s= "(fst (f a), snd (f a))" in trans)
apply simp
apply (rule surjective_pairing [THEN sym])
apply (simp del: split_paired_All)
done


lemma comp_method [rule_format (no_asm)]: "\<lbrakk> wf_prog wf_mb G; is_class G C\<rbrakk> \<Longrightarrow> 
  (method (G, C) S) = Some (D, rT, mb) \<longrightarrow> 
  (method (comp G, C) S) = Some (D, rT, mtd_mb (compMethod G D (S, rT, mb)))"
apply (simp add: method_def)
apply (frule wf_subcls1)
apply (simp add: comp_class_rec)
apply (simp add: map_compose [THEN sym] split_iter split_compose del: map_compose)
apply (rule_tac R="%x y. (x S) = Some (D, rT, mb) \<longrightarrow> (y S) = Some (D, rT, snd (snd (compMethod G D (S, rT, mb))))" in  class_rec_relation) apply assumption

apply (intro strip)
apply simp

apply (frule_tac f="(\<lambda>(s, m). (s, Object, m))" 
  and g="(Fun.comp (\<lambda>(s, m). (s, Object, m)) (compMethod G Object))" in map_of_map_fst)
(*
apply (frule_tac f="(\<lambda>(s, m). (s, Object, m))" 
  and g="((\<lambda>(s, m). (s, Object, m)) \<circ> compMethod G Object)" in map_of_map_fst)
*)
apply (simp add: inj_on_def)
apply (simp add: split_beta compMethod_def)
apply (simp add: split_beta compMethod_def)
apply (simp only:)
apply (subgoal_tac "(inv (\<lambda>(s, m). (s, Object, m)) (S, D, rT, mb)) = (S, rT, mb)")
apply (simp only:)
apply (simp add: compMethod_def split_beta)
apply (simp add: map_of_map) apply (erule exE)+ apply simp
apply (simp add: map_of_map) apply (erule exE)+ apply simp
apply (rule inv_f_eq) apply (simp add: inj_on_def) apply simp

apply (intro strip)
apply (simp add: override_Some_iff map_of_map del: split_paired_Ex)
apply (subgoal_tac "\<forall>x\<in>set ms. fst ((Fun.comp (\<lambda>(s, m). (s, Ca, m)) (compMethod G Ca)) x) = fst x")
(*
apply (subgoal_tac "\<forall>x\<in>set ms. fst (((\<lambda>(s, m). (s, Ca, m)) \<circ> compMethod G Ca) x) = fst x")
*)
apply (erule disjE)
apply (rule disjI1)
apply (simp add: map_of_map2)
apply (simp (no_asm_simp) add: compMethod_def split_beta)

apply (rule disjI2)
apply (simp add: map_of_map2)

  -- "subgoal"
apply (simp (no_asm_simp) add: compMethod_def split_beta)

apply (simp add: is_class_def)
done


constdefs comp_method_result :: "java_mb prog \<Rightarrow> sig \<Rightarrow> 
  (cname \<times> ty \<times> java_mb) option \<Rightarrow> (cname \<times> ty \<times> jvm_method) option"
  "comp_method_result G S m ==  case m of 
    None \<Rightarrow> None
  | Some (D, rT, mb) \<Rightarrow> Some (D, rT, mtd_mb (compMethod G D (S, rT, mb)))"


lemma map_of_map_compMethod: "map_of (map (\<lambda>(s, m). (s, C, m)) (map (compMethod G C) ms)) S =
          (case map_of (map (\<lambda>(s, m). (s, C, m)) ms) S of None \<Rightarrow> None
           | Some (D, rT, mb) \<Rightarrow> Some (D, rT, mtd_mb (compMethod G D (S, rT, mb))))"
apply (induct ms)
apply simp
apply (simp only: map_compose [THEN sym])
apply (simp add: o_def split_beta del: map.simps)
apply (simp (no_asm_simp) only: map.simps map_of.simps)
apply (simp add: compMethod_def split_beta)
done

  (* the following is more expressive than comp_method and should replace it *)
lemma comp_method_eq [rule_format (no_asm)]: "wf_prog wf_mb G \<Longrightarrow> is_class G C \<longrightarrow>
method (comp G, C) S = comp_method_result G S (method (G,C) S)"
apply (subgoal_tac "wf ((subcls1 G)^-1)") prefer 2 apply (rule wf_subcls1, assumption) 

apply (rule subcls_induct)
apply assumption
apply (intro strip)
apply (subgoal_tac "\<exists> D fs ms. class G C = Some (D, fs, ms)") 
   prefer 2 apply (simp add: is_class_def)
apply (erule exE)+

apply (case_tac "C = Object")

  (* C = Object *)
apply (subst method_rec_lemma) apply assumption+ apply simp 
apply (subst method_rec_lemma) apply (frule comp_class_imp) apply assumption+ 
   apply (simp add: comp_subcls1) 
apply (simp add: comp_method_result_def)
apply (rule map_of_map_compMethod) 

  (* C \<noteq> Object *)
apply (subgoal_tac "(C, D) \<in> (subcls1 G)\<^sup>+") 
   prefer 2 apply (frule subcls1I, assumption+) apply blast
apply (subgoal_tac "is_class G D")
apply (drule spec, drule mp, assumption, drule mp, assumption)
apply (frule wf_subcls1) 
apply (subgoal_tac "wf ((subcls1 (comp G))\<inverse>)")
apply (frule_tac G=G in method_rec_lemma, assumption)
apply (frule comp_class_imp)
apply (frule_tac G="comp G" in method_rec_lemma, assumption)
apply (simp only:)
apply (simp (no_asm_simp) add: comp_method_result_def expand_fun_eq)

apply (case_tac "(method (G, D) ++  map_of (map (\<lambda>(s, m). (s, C, m)) ms)) S")

  (* case None *)
apply (simp (no_asm_simp) add: override_None)
apply (simp add: map_of_map_compMethod comp_method_result_def) 

  (* case Some *)
apply (simp add: override_Some_iff)
apply (erule disjE)
  apply (simp add: split_beta map_of_map_compMethod)
  apply (simp add: override_def comp_method_result_def map_of_map_compMethod)

  (* show subgoals *)
apply (simp add: comp_subcls1) 
  (* show is_class G D *)
apply (simp add: wf_prog_def wf_cdecl_def)
apply (subgoal_tac "(C, D, fs, ms)\<in>set G")
apply blast
apply (simp add: class_def map_of_SomeD)
done

  (* ### this proof is horrid and has to be redone *)
lemma unique_map_fst [rule_format]: "(\<forall> x \<in> set xs. (fst x = fst (f x) )) \<longrightarrow>
  unique xs = unique (map f xs)"
apply (induct_tac "xs")
apply simp
apply (intro strip)
apply simp
apply (case_tac a, simp)
apply (case_tac "f (aa, b)")
apply (simp only:)
apply (simp only: unique_Cons)

apply simp
apply (subgoal_tac "(\<exists>y. (ab, y) \<in> set list) = (\<exists>y. (ab, y) \<in> f ` set list)")
apply blast
apply (rule iffI)

apply clarify
apply (rule_tac x="(snd (f(ab, y)))" in exI)
apply simp
apply (subgoal_tac "(ab, snd (f (ab, y))) = (fst (f (ab, y)), snd (f (ab, y)))")
apply (simp only:)
apply (simp add: surjective_pairing [THEN sym])
apply (subgoal_tac "fst (f (ab, y)) = fst (ab, y)")
apply simp
apply (drule bspec) apply assumption apply simp

apply clarify
apply (drule bspec) apply assumption apply simp
apply (subgoal_tac "ac = ab")
apply simp
apply blast
apply (drule sym)
apply (drule sym)
apply (drule_tac f=fst in arg_cong)
apply simp
done

lemma comp_unique: "unique G = unique (comp G)"
apply (simp add: comp_def)
apply (rule unique_map_fst)
apply (simp add: compClass_def split_beta)
done


(**********************************************************************)
  (* DIVERSE OTHER LEMMAS *)
(**********************************************************************)


(* already proved less elegantly in CorrComp.thy;
  to be moved into a common super-theory *)
lemma max_spec_preserves_length:
  "max_spec G C (mn, pTs) = {((md,rT),pTs')} 
  \<Longrightarrow> length pTs = length pTs'"
apply (frule max_spec2mheads)
apply (erule exE)+
apply (simp add: list_all2_def)
done


(* already proved in CorrComp.thy \<longrightarrow> into common supertheory *)
lemma ty_exprs_length [simp]: "(E\<turnstile>es[::]Ts \<longrightarrow> length es = length Ts)"
apply (subgoal_tac "(E\<turnstile>e::T \<longrightarrow> True) \<and> (E\<turnstile>es[::]Ts \<longrightarrow> length es = length Ts) \<and> (E\<turnstile>s\<surd> \<longrightarrow> True)")
apply blast
apply (rule ty_expr_ty_exprs_wt_stmt.induct)
apply auto
done


lemma max_spec_preserves_method_rT [simp]:
  "max_spec G C (mn, pTs) = {((md,rT),pTs')}
  \<Longrightarrow> method_rT (the (method (G, C) (mn, pTs'))) = rT"
apply (frule max_spec2mheads)
apply (erule exE)+
apply (simp add: method_rT_def)
done


end
