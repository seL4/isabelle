(*  Title:      HOL/MicroJava/Comp/LemmasComp.thy
    ID:         $Id$
    Author:     Martin Strecker
    Copyright   GPL 2002
*)

(* Lemmas for compiler correctness proof *)

theory LemmasComp = TranslComp:


declare split_paired_All [simp del]
declare split_paired_Ex [simp del]


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


lemma unique_map_fst [rule_format]: "(\<forall> x \<in> set xs. (fst x = fst (f x) )) \<longrightarrow>
  unique (map f xs) = unique xs"
proof (induct xs)
  case Nil show ?case by simp
next
  case (Cons a list)
  show ?case
  proof
    assume fst_eq: "\<forall>x\<in>set (a # list). fst x = fst (f x)"

    have fst_set: "(fst a \<in> fst ` set list) = (fst (f a) \<in> fst ` f ` set list)" 
    proof 
      assume as: "fst a \<in> fst ` set list" 
      then obtain x where fst_a_x: "x\<in>set list \<and> fst a = fst x" 
	by (auto simp add: image_iff)
      then have "fst (f a) = fst (f x)" by (simp add: fst_eq)
      with as show "(fst (f a) \<in> fst ` f ` set list)" by (simp add: fst_a_x)
    next
      assume as: "fst (f a) \<in> fst ` f ` set list"
      then obtain x where fst_a_x: "x\<in>set list \<and> fst (f a) = fst (f x)"
	by (auto simp add: image_iff)
      then have "fst a = fst x" by (simp add: fst_eq)
      with as show "fst a \<in> fst ` set list" by (simp add: fst_a_x)
    qed

    with fst_eq Cons 
    show "unique (map f (a # list)) = unique (a # list)"
      by (simp add: unique_def fst_set)
  qed
qed

lemma comp_unique: "unique (comp G) = unique G"
apply (simp add: comp_def)
apply (rule unique_map_fst)
apply (simp add: compClass_def split_beta)
done


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

lemma comp_is_class: "is_class (comp G) C = is_class G C"
by (case_tac "class G C", auto simp: is_class_def comp_class_None dest: comp_class_imp)


lemma comp_is_type: "is_type (comp G) T = is_type G T"
  by ((cases T),simp,(induct G)) ((simp),(simp only: comp_is_class),(simp add: comp_is_class),(simp only: comp_is_class))

lemma SIGMA_cong: "\<lbrakk> A = B; !!x. x \<in> B \<Longrightarrow> C x = D x \<rbrakk> 
  \<Longrightarrow> (\<Sigma> x \<in> A. C x) = (\<Sigma> x \<in> B. D x)"
by auto

lemma comp_classname: "is_class G C 
  \<Longrightarrow> fst (the (class G C)) = fst (the (class (comp G) C))"
by (case_tac "class G C", auto simp: is_class_def dest: comp_class_imp)


lemma comp_subcls1: "subcls1 (comp G) = subcls1 G"
apply (simp add: subcls1_def2 comp_is_class)
apply (rule SIGMA_cong, simp)
apply (simp add: comp_is_class)
apply (simp add: comp_classname)
done

lemma comp_widen: "((ty1,ty2) \<in> widen (comp G)) = ((ty1,ty2) \<in> widen G)"
  apply rule
  apply (cases "(ty1,ty2)" "comp G" rule: widen.cases) 
  apply (simp_all add: comp_subcls1 widen.null)
  apply (cases "(ty1,ty2)" G rule: widen.cases) 
  apply (simp_all add: comp_subcls1 widen.null)
  done

lemma comp_cast: "((ty1,ty2) \<in> cast (comp G)) = ((ty1,ty2) \<in> cast G)"
  apply rule
  apply (cases "(ty1,ty2)" "comp G" rule: cast.cases) 
  apply (simp_all add: comp_subcls1 cast.widen cast.subcls)
  apply (rule cast.widen) apply (simp add: comp_widen)
  apply (cases "(ty1,ty2)" G rule: cast.cases)
  apply (simp_all add: comp_subcls1 cast.widen cast.subcls)
  apply (rule cast.widen) apply (simp add: comp_widen)
  done

lemma comp_cast_ok: "cast_ok (comp G) = cast_ok G"
  by (simp add: expand_fun_eq cast_ok_def comp_widen)


lemma compClass_fst [simp]: "(fst (compClass G C)) = (fst C)"
by (simp add: compClass_def split_beta)

lemma compClass_fst_snd [simp]: "(fst (snd (compClass G C))) = (fst (snd C))"
by (simp add: compClass_def split_beta)

lemma compClass_fst_snd_snd [simp]: "(fst (snd (snd (compClass G C)))) = (fst (snd (snd C)))"
by (simp add: compClass_def split_beta)

lemma comp_wf_fdecl [simp]: "wf_fdecl (comp G) fd = wf_fdecl G fd"
by (case_tac fd, simp add: wf_fdecl_def comp_is_type)


lemma compClass_forall [simp]: "
  (\<forall>x\<in>set (snd (snd (snd (compClass G C)))). P (fst x) (fst (snd x))) =
  (\<forall>x\<in>set (snd (snd (snd C))). P (fst x) (fst (snd x)))"
by (simp add: compClass_def compMethod_def split_beta)

lemma comp_wf_mhead: "wf_mhead (comp G) S rT =  wf_mhead G S rT"
by (simp add: wf_mhead_def split_beta comp_is_type)

lemma comp_ws_cdecl: "
  ws_cdecl (TranslComp.comp G) (compClass G C) = ws_cdecl G C"
apply (simp add: ws_cdecl_def split_beta comp_is_class comp_subcls1)
apply (simp (no_asm_simp) add: comp_wf_mhead)
apply (simp add: compClass_def compMethod_def split_beta unique_map_fst)
done


lemma comp_wf_syscls: "wf_syscls (comp G) = wf_syscls G"
apply (simp add: wf_syscls_def comp_def compClass_def split_beta)
apply (simp only: image_compose [THEN sym])
apply (subgoal_tac "(Fun.comp fst (\<lambda>(C, cno::cname, fdls::fdecl list, jmdls).
  (C, cno, fdls, map (compMethod G C) jmdls))) = fst")
apply (simp del: image_compose)
apply (simp add: expand_fun_eq split_beta)
done


lemma comp_ws_prog: "ws_prog (comp G) = ws_prog G"
apply (rule sym)
apply (simp add: ws_prog_def comp_ws_cdecl comp_unique)
apply (simp add: comp_wf_syscls)
apply (auto simp add: comp_ws_cdecl [THEN sym] TranslComp.comp_def)
done


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
  fields (comp G,C) = fields (G,C)" 
by (simp add: fields_def comp_class_rec)

lemma comp_field: "wf ((subcls1 G)^-1) \<Longrightarrow> 
  field (comp G,C) = field (G,C)" 
by (simp add: field_def comp_fields)



lemma class_rec_relation [rule_format (no_asm)]: "\<lbrakk>  ws_prog G;
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

apply (frule class_wf_struct) apply assumption
apply (simp add: ws_cdecl_def is_class_def)

apply (simp add: subcls1_def2 is_class_def)
apply auto
done


syntax
  mtd_mb :: "cname \<times> ty \<times> 'c \<Rightarrow> 'c"
translations
  "mtd_mb" => "Fun.comp snd snd"

lemma map_of_map_fst: "\<lbrakk> inj f;
  \<forall>x\<in>set xs. fst (f x) = fst x; \<forall>x\<in>set xs. fst (g x) = fst x \<rbrakk>
  \<Longrightarrow>  map_of (map g xs) k 
  = option_map (\<lambda> e. (snd (g ((inv f) (k, e))))) (map_of (map f xs) k)"
apply (induct xs)
apply simp
apply (simp del: split_paired_All)
apply (case_tac "k = fst a")
apply (simp del: split_paired_All)
apply (subgoal_tac "(inv f (fst a, snd (f a))) = a", simp)
apply (subgoal_tac "(fst a, snd (f a)) = f a", simp)
apply (erule conjE)+
apply (drule_tac s ="fst (f a)" and t="fst a" in sym)
apply simp
apply (simp add: surjective_pairing)
done


lemma comp_method [rule_format (no_asm)]: "\<lbrakk> ws_prog G; is_class G C\<rbrakk> \<Longrightarrow> 
  ((method (comp G, C) S) = 
  option_map (\<lambda> (D,rT,b).  (D, rT, mtd_mb (compMethod G D (S, rT, b))))
             (method (G, C) S))"
apply (simp add: method_def)
apply (frule wf_subcls1)
apply (simp add: comp_class_rec)
apply (simp add: map_compose [THEN sym] split_iter split_compose del: map_compose)
apply (rule_tac R="%x y. ((x S) = (option_map (\<lambda>(D, rT, b). 
  (D, rT, snd (snd (compMethod G D (S, rT, b))))) (y S)))" 
  in class_rec_relation)
apply assumption

apply (intro strip)
apply simp

apply (rule trans)

apply (rule_tac f="(\<lambda>(s, m). (s, Object, m))" and
  g="(Fun.comp (\<lambda>(s, m). (s, Object, m)) (compMethod G Object))" 
  in map_of_map_fst)
defer				(* inj \<dots> *)
apply (simp add: inj_on_def split_beta) 
apply (simp add: split_beta compMethod_def)
apply (simp add: map_of_map [THEN sym])
apply (simp add: split_beta)
apply (simp add: map_compose [THEN sym] Fun.comp_def split_beta)
apply (subgoal_tac "(\<lambda>x\<Colon>(vname list \<times> fdecl list \<times> stmt \<times> expr) mdecl.
                    (fst x, Object,
                     snd (compMethod G Object
                           (inv (\<lambda>(s\<Colon>sig, m\<Colon>ty \<times> vname list \<times> fdecl list \<times> stmt \<times> expr).
                                    (s, Object, m))
                             (S, Object, snd x)))))
  = (\<lambda>x. (fst x, Object, fst (snd x),
                        snd (snd (compMethod G Object (S, snd x)))))")
apply (simp only:)
apply (simp add: expand_fun_eq)
apply (intro strip)
apply (subgoal_tac "(inv (\<lambda>(s, m). (s, Object, m)) (S, Object, snd x)) = (S, snd x)")
apply (simp only:)
apply (simp add: compMethod_def split_beta)
apply (rule inv_f_eq) 
defer
defer

apply (intro strip)
apply (simp add: map_add_Some_iff map_of_map del: split_paired_Ex)
apply (simp add: map_add_def)
apply (subgoal_tac "inj (\<lambda>(s, m). (s, Ca, m))")
apply (drule_tac g="(Fun.comp (\<lambda>(s, m). (s, Ca, m)) (compMethod G Ca))" and xs=ms
  and k=S in map_of_map_fst) 
apply (simp add: split_beta) 
apply (simp add: compMethod_def split_beta)
apply (case_tac "(map_of (map (\<lambda>(s, m). (s, Ca, m)) ms) S)")
apply simp
apply simp apply (simp add: split_beta map_of_map) apply (erule exE) apply (erule conjE)+
apply (drule_tac t=a in sym)
apply (subgoal_tac "(inv (\<lambda>(s, m). (s, Ca, m)) (S, a)) = (S, snd a)")
apply simp
apply (subgoal_tac "\<forall>x\<in>set ms. fst ((Fun.comp (\<lambda>(s, m). (s, Ca, m)) (compMethod G Ca)) x) = fst x")
   prefer 2 apply (simp (no_asm_simp) add: compMethod_def split_beta)
apply (simp add: map_of_map2)
apply (simp (no_asm_simp) add: compMethod_def split_beta)

  -- "remaining subgoals"
apply (auto intro: inv_f_eq simp add: inj_on_def is_class_def)
done



lemma comp_wf_mrT: "\<lbrakk> ws_prog G; is_class G D\<rbrakk> \<Longrightarrow> 
  wf_mrT (TranslComp.comp G) (C, D, fs, map (compMethod G a) ms) =
  wf_mrT G (C, D, fs, ms)"
apply (simp add: wf_mrT_def compMethod_def split_beta)
apply (simp add: comp_widen)
apply (rule iffI)
apply (intro strip)
apply simp
apply (drule bspec) apply assumption
apply (drule_tac x=D' in spec) apply (drule_tac x=rT' in spec) apply (drule mp)
prefer 2 apply assumption
apply (simp add: comp_method [of G D])
apply (erule exE)+
apply (subgoal_tac "z =(fst z, fst (snd z), snd (snd z))")
apply (rule exI)
apply (simp)
apply (simp add: split_paired_all)
apply (intro strip)
apply (simp add: comp_method)
apply auto
done


(**********************************************************************)
  (* DIVERSE OTHER LEMMAS *)
(**********************************************************************)

lemma max_spec_preserves_length:
  "max_spec G C (mn, pTs) = {((md,rT),pTs')} 
  \<Longrightarrow> length pTs = length pTs'"
apply (frule max_spec2mheads)
apply (erule exE)+
apply (simp add: list_all2_def)
done


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

  (**********************************************************************************)

declare compClass_fst [simp del]
declare compClass_fst_snd [simp del]
declare compClass_fst_snd_snd [simp del]

declare split_paired_All [simp add]
declare split_paired_Ex [simp add]

end
