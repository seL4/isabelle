
theory Class 
imports "../nominal" 
begin

section {* Term-Calculus from Urban's PhD *}

atom_decl name coname

nominal_datatype trm = 
    Ax   "name" "coname"
  | Cut  "\<guillemotleft>coname\<guillemotright>trm" "\<guillemotleft>name\<guillemotright>trm"            ("Cut <_>._ [_]._" [100,100,100,100] 100)
  | NotR "\<guillemotleft>name\<guillemotright>trm" "coname"                 ("NotR [_]._ _" [100,100,100] 100)
  | NotL "\<guillemotleft>coname\<guillemotright>trm" "name"                 ("NotL <_>._ _" [100,100,100] 100)
  | AndR "\<guillemotleft>coname\<guillemotright>trm" "\<guillemotleft>coname\<guillemotright>trm" "coname" ("AndR <_>._ <_>._ _" [100,100,100,100,100] 100)
  | AndL1 "\<guillemotleft>name\<guillemotright>trm" "name"                  ("AndL1 [_]._ _" [100,100,100] 100)
  | AndL2 "\<guillemotleft>name\<guillemotright>trm" "name"                  ("AndL2 [_]._ _" [100,100,100] 100)
  | OrR1 "\<guillemotleft>coname\<guillemotright>trm" "coname"               ("OrR1 <_>._ _" [100,100,100] 100)
  | OrR2 "\<guillemotleft>coname\<guillemotright>trm" "coname"               ("OrR2 <_>._ _" [100,100,100] 100)
  | OrL "\<guillemotleft>name\<guillemotright>trm" "\<guillemotleft>name\<guillemotright>trm" "name"        ("OrL [_]._ [_]._ _" [100,100,100,100,100] 100)
  | ImpR "\<guillemotleft>name\<guillemotright>(\<guillemotleft>coname\<guillemotright>trm)" "coname"       ("ImpR [_].<_>._ _" [100,100,100,100] 100)
  | ImpL "\<guillemotleft>coname\<guillemotright>trm" "\<guillemotleft>name\<guillemotright>trm" "name"     ("ImpL <_>._ [_]._ _" [100,100,100,100,100] 100)

thm trm_rec_set.intros[no_vars]
  
lemma rec_total:
  shows "\<exists>r. (t,r) \<in> trm_rec_set f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12"
  by (induct t rule: trm.induct_weak, auto intro: trm_rec_set.intros)

lemma rec_prm_eq:
  assumes a: "(t,y) \<in> trm_rec_set f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12" 
  and     b: "pi1 \<triangleq> pi2"
  and     c: "pi3 \<triangleq> pi4"
  shows "y pi1 pi3 = y pi2 pi4"
using a b c
apply(induct fixing: pi1 pi2 pi3 pi4)
(* axiom *)
apply(simp add: pt3[OF pt_name_inst] pt3[OF pt_coname_inst])
(* Cut *)
apply(rule_tac f="fresh_fun" in arg_cong)
apply(simp add: expand_fun_eq)
apply(rule allI)
apply(rule_tac f="fresh_fun" in arg_cong)
apply(simp add: expand_fun_eq)
apply(rule allI)
apply(tactic {* DatatypeAux.cong_tac 1 *})+
apply(simp_all add: pt2[OF pt_name_inst] pt2[OF pt_coname_inst] 
                    pt3[OF pt_name_inst] pt3[OF pt_coname_inst])
apply(drule meta_spec)+
apply(drule meta_mp, erule_tac [2] meta_mp)
apply(rule at_prm_eq_append'[OF at_coname_inst], assumption, assumption)
apply(drule meta_spec)+
apply(drule meta_mp, erule_tac [2] meta_mp)
apply(assumption, rule at_prm_eq_append'[OF at_name_inst], assumption)
(* NotR *)
apply(rule_tac f="fresh_fun" in arg_cong)
apply(simp add: expand_fun_eq)
apply(rule allI)
apply(tactic {* DatatypeAux.cong_tac 1 *})+
apply(simp_all add: pt2[OF pt_name_inst] pt2[OF pt_coname_inst] 
                    pt3[OF pt_name_inst] pt3[OF pt_coname_inst])
apply(drule meta_spec)+
apply(drule meta_mp, erule_tac [2] meta_mp)
apply(assumption, rule at_prm_eq_append'[OF at_name_inst], assumption)
(* NotL *)
apply(rule_tac f="fresh_fun" in arg_cong)
apply(simp add: expand_fun_eq)
apply(rule allI)
apply(tactic {* DatatypeAux.cong_tac 1 *})+
apply(simp_all add: pt2[OF pt_name_inst] pt2[OF pt_coname_inst] 
                    pt3[OF pt_name_inst] pt3[OF pt_coname_inst])
apply(drule meta_spec)+
apply(drule meta_mp, erule_tac [2] meta_mp)
apply(rule at_prm_eq_append'[OF at_coname_inst], assumption, assumption)
(* AndR *)
apply(rule_tac f="fresh_fun" in arg_cong)
apply(simp add: expand_fun_eq)
apply(rule allI)
apply(rule_tac f="fresh_fun" in arg_cong)
apply(simp add: expand_fun_eq)
apply(rule allI)
apply(tactic {* DatatypeAux.cong_tac 1 *})+
apply(simp_all add: pt2[OF pt_name_inst] pt2[OF pt_coname_inst] 
                    pt3[OF pt_name_inst] pt3[OF pt_coname_inst])
apply(drule meta_spec)+
apply(drule meta_mp, erule_tac [2] meta_mp)
apply(rule at_prm_eq_append'[OF at_coname_inst], assumption, assumption)
apply(drule meta_spec)+
apply(drule meta_mp, erule_tac [2] meta_mp)
apply(rule at_prm_eq_append'[OF at_coname_inst], assumption, assumption)
(* AndL1 *)
apply(rule_tac f="fresh_fun" in arg_cong)
apply(simp add: expand_fun_eq)
apply(rule allI)
apply(tactic {* DatatypeAux.cong_tac 1 *})+
apply(simp_all add: pt2[OF pt_name_inst] pt2[OF pt_coname_inst] 
                    pt3[OF pt_name_inst] pt3[OF pt_coname_inst])
apply(drule meta_spec)+
apply(drule meta_mp, erule_tac [2] meta_mp)
apply(assumption, rule at_prm_eq_append'[OF at_name_inst], assumption)
(* AndL1 *)
apply(rule_tac f="fresh_fun" in arg_cong)
apply(simp add: expand_fun_eq)
apply(rule allI)
apply(tactic {* DatatypeAux.cong_tac 1 *})+
apply(simp_all add: pt2[OF pt_name_inst] pt2[OF pt_coname_inst] 
                    pt3[OF pt_name_inst] pt3[OF pt_coname_inst])
apply(drule meta_spec)+
apply(drule meta_mp, erule_tac [2] meta_mp)
apply(assumption, rule at_prm_eq_append'[OF at_name_inst], assumption)
(* OrR1 *)
apply(rule_tac f="fresh_fun" in arg_cong)
apply(simp add: expand_fun_eq)
apply(rule allI)
apply(tactic {* DatatypeAux.cong_tac 1 *})+
apply(simp_all add: pt2[OF pt_name_inst] pt2[OF pt_coname_inst] 
                    pt3[OF pt_name_inst] pt3[OF pt_coname_inst])
apply(drule meta_spec)+
apply(drule meta_mp, erule_tac [2] meta_mp)
apply(rule at_prm_eq_append'[OF at_coname_inst], assumption, assumption)
(* OrR2 *)
apply(rule_tac f="fresh_fun" in arg_cong)
apply(simp add: expand_fun_eq)
apply(rule allI)
apply(tactic {* DatatypeAux.cong_tac 1 *})+
apply(simp_all add: pt2[OF pt_name_inst] pt2[OF pt_coname_inst] 
                    pt3[OF pt_name_inst] pt3[OF pt_coname_inst])
apply(drule meta_spec)+
apply(drule meta_mp, erule_tac [2] meta_mp)
apply(rule at_prm_eq_append'[OF at_coname_inst], assumption, assumption)
(* OrL *)
apply(rule_tac f="fresh_fun" in arg_cong)
apply(simp add: expand_fun_eq)
apply(rule allI)
apply(rule_tac f="fresh_fun" in arg_cong)
apply(simp add: expand_fun_eq)
apply(rule allI)
apply(tactic {* DatatypeAux.cong_tac 1 *})+
apply(simp_all add: pt2[OF pt_name_inst] pt2[OF pt_coname_inst] 
                    pt3[OF pt_name_inst] pt3[OF pt_coname_inst])
apply(drule meta_spec)+
apply(drule meta_mp, erule_tac [2] meta_mp)
apply(assumption, rule at_prm_eq_append'[OF at_name_inst], assumption)
apply(drule meta_spec)+
apply(drule meta_mp, erule_tac [2] meta_mp)
apply(assumption, rule at_prm_eq_append'[OF at_name_inst], assumption)
(* ImpR *)
apply(rule_tac f="fresh_fun" in arg_cong)
apply(simp add: expand_fun_eq)
apply(rule allI)
apply(rule_tac f="fresh_fun" in arg_cong)
apply(simp add: expand_fun_eq)
apply(rule allI)
apply(tactic {* DatatypeAux.cong_tac 1 *})+
apply(simp_all add: pt2[OF pt_name_inst] pt2[OF pt_coname_inst] 
                    pt3[OF pt_name_inst] pt3[OF pt_coname_inst])
apply(drule meta_spec)+
apply(drule meta_mp, erule_tac [2] meta_mp)
apply(rule at_prm_eq_append'[OF at_coname_inst], assumption)
apply(rule at_prm_eq_append'[OF at_name_inst], assumption)
(* ImpL *)
apply(rule_tac f="fresh_fun" in arg_cong)
apply(simp add: expand_fun_eq)
apply(rule allI)
apply(rule_tac f="fresh_fun" in arg_cong)
apply(simp add: expand_fun_eq)
apply(rule allI)
apply(tactic {* DatatypeAux.cong_tac 1 *})+
apply(simp_all add: pt2[OF pt_name_inst] pt2[OF pt_coname_inst] 
                    pt3[OF pt_name_inst] pt3[OF pt_coname_inst])
apply(drule meta_spec)+
apply(drule meta_mp, erule_tac [2] meta_mp)
apply(rule at_prm_eq_append'[OF at_coname_inst], assumption, assumption)
apply(drule meta_spec)+
apply(drule meta_mp, erule_tac [2] meta_mp)
apply(assumption, rule at_prm_eq_append'[OF at_name_inst], assumption)
done

lemma rec_fin_supp: 
assumes f: "finite ((supp (f1,f2,f3,f3,f4,f5,f6,f7,f8,f9,f10,f11,f12))::name set)"
  and   c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>t (r::'a::pt_name). a\<sharp>f3 a t r)"
  and   a: "(t,r) \<in> trm_rec_set f1 f2 f3"
  shows "finite ((supp r)::name set)"
using a 
proof (induct)
  case goal1 thus ?case using f by (finite_guess add: supp_prod fs_name1)
next
  case goal2 thus ?case using f by (finite_guess add: supp_prod fs_name1)
next
  case (goal3 c t r)
  have ih: "finite ((supp r)::name set)" by fact
  let ?g' = "\<lambda>pi a'. f3 a' ((pi@[(c,a')])\<bullet>t) (r (pi@[(c,a')]))"     --"helper function"
  have fact1: "\<forall>pi. finite ((supp (?g' pi))::name set)" using f ih
    by (rule_tac allI, finite_guess add: perm_append supp_prod fs_name1)
  have fact2: "\<forall>pi. \<exists>(a''::name). a''\<sharp>(?g' pi) \<and> a''\<sharp>((?g' pi) a'')" 
  proof 
    fix pi::"name prm"
    show "\<exists>(a''::name). a''\<sharp>(?g' pi) \<and> a''\<sharp>((?g' pi) a'')" using f c ih 
      by (rule_tac f3_freshness_conditions_simple, simp_all add: supp_prod)
  qed
  show ?case using fact1 fact2 ih f by (finite_guess add: fresh_fun_eqvt perm_append supp_prod fs_name1)
qed 

text {* Induction principles *}

thm trm.induct_weak --"weak"
thm trm.induct      --"strong"
thm trm.induct'     --"strong with explicit context (rarely needed)"

text {* named terms *}

nominal_datatype ntrm = N "\<guillemotleft>name\<guillemotright>trm" ("N (_)._" [100,100] 100)

text {* conamed terms *}

nominal_datatype ctrm = C "\<guillemotleft>coname\<guillemotright>trm" ("C <_>._" [100,100] 100)

text {* We should now define the two forms of substitition :o( *}

consts
  substn :: "trm \<Rightarrow> name   \<Rightarrow> ctrm \<Rightarrow> trm" ("_[_::=_]" [100,100,100] 100) 
  substc :: "trm \<Rightarrow> coname \<Rightarrow> ntrm \<Rightarrow> trm" ("_[_::=_]" [100,100,100] 100)

text {* does not work yet *}