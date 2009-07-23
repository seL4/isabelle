(*  Title:      HOLCF/FOCUS/Buffer.thy
    Author:     David von Oheimb, TU Muenchen

Formalization of section 4 of

@inproceedings {broy_mod94,
    author = {Manfred Broy},
    title = {{Specification and Refinement of a Buffer of Length One}},
    booktitle = {Deductive Program Design},
    year = {1994},
    editor = {Manfred Broy},
    volume = {152},
    series = {ASI Series, Series F: Computer and System Sciences},
    pages = {273 -- 304},
    publisher = {Springer}
}

Slides available from http://ddvo.net/talks/1-Buffer.ps.gz

*)

theory Buffer
imports FOCUS
begin

typedecl D

datatype

  M     = Md D | Mreq ("\<bullet>")

datatype

  State = Sd D | Snil ("\<currency>")

types

  SPF11         = "M fstream \<rightarrow> D fstream"
  SPEC11        = "SPF11 set"
  SPSF11        = "State \<Rightarrow> SPF11"
  SPECS11       = "SPSF11 set"

definition
  BufEq_F       :: "SPEC11 \<Rightarrow> SPEC11" where
  "BufEq_F B = {f. \<forall>d. f\<cdot>(Md d\<leadsto><>) = <> \<and>
                (\<forall>x. \<exists>ff\<in>B. f\<cdot>(Md d\<leadsto>\<bullet>\<leadsto>x) = d\<leadsto>ff\<cdot>x)}"

definition
  BufEq         :: "SPEC11" where
  "BufEq = gfp BufEq_F"

definition
  BufEq_alt     :: "SPEC11" where
  "BufEq_alt = gfp (\<lambda>B. {f. \<forall>d. f\<cdot>(Md d\<leadsto><> ) = <> \<and>
                         (\<exists>ff\<in>B. (\<forall>x. f\<cdot>(Md d\<leadsto>\<bullet>\<leadsto>x) = d\<leadsto>ff\<cdot>x))})"

definition
  BufAC_Asm_F   :: " (M fstream set) \<Rightarrow> (M fstream set)" where
  "BufAC_Asm_F A = {s. s = <> \<or>
                  (\<exists>d x. s = Md d\<leadsto>x \<and> (x = <> \<or> (ft\<cdot>x = Def \<bullet> \<and> (rt\<cdot>x)\<in>A)))}"

definition
  BufAC_Asm     :: " (M fstream set)" where
  "BufAC_Asm = gfp BufAC_Asm_F"

definition
  BufAC_Cmt_F   :: "((M fstream * D fstream) set) \<Rightarrow>
                    ((M fstream * D fstream) set)" where
  "BufAC_Cmt_F C = {(s,t). \<forall>d x.
                           (s = <>         \<longrightarrow>     t = <>                 ) \<and>
                           (s = Md d\<leadsto><>   \<longrightarrow>     t = <>                 ) \<and>
                           (s = Md d\<leadsto>\<bullet>\<leadsto>x \<longrightarrow> (ft\<cdot>t = Def d \<and> (x,rt\<cdot>t)\<in>C))}"

definition
  BufAC_Cmt     :: "((M fstream * D fstream) set)" where
  "BufAC_Cmt = gfp BufAC_Cmt_F"

definition
  BufAC         :: "SPEC11" where
  "BufAC = {f. \<forall>x. x\<in>BufAC_Asm \<longrightarrow> (x,f\<cdot>x)\<in>BufAC_Cmt}"

definition
  BufSt_F       :: "SPECS11 \<Rightarrow> SPECS11" where
  "BufSt_F H = {h. \<forall>s  . h s      \<cdot><>        = <>         \<and>
                                 (\<forall>d x. h \<currency>     \<cdot>(Md d\<leadsto>x) = h (Sd d)\<cdot>x \<and>
                                (\<exists>hh\<in>H. h (Sd d)\<cdot>(\<bullet>   \<leadsto>x) = d\<leadsto>(hh \<currency>\<cdot>x)))}"

definition
  BufSt_P       :: "SPECS11" where
  "BufSt_P = gfp BufSt_F"

definition
  BufSt         :: "SPEC11" where
  "BufSt = {f. \<exists>h\<in>BufSt_P. f = h \<currency>}"


lemma set_cong: "!!X. A = B ==> (x:A) = (x:B)"
by (erule subst, rule refl)


(**** BufEq *******************************************************************)

lemma mono_BufEq_F: "mono BufEq_F"
by (unfold mono_def BufEq_F_def, fast)

lemmas BufEq_fix = mono_BufEq_F [THEN BufEq_def [THEN eq_reflection, THEN def_gfp_unfold]]

lemma BufEq_unfold: "(f:BufEq) = (!d. f\<cdot>(Md d\<leadsto><>) = <> &
                 (!x. ? ff:BufEq. f\<cdot>(Md d\<leadsto>\<bullet>\<leadsto>x) = d\<leadsto>(ff\<cdot>x)))"
apply (subst BufEq_fix [THEN set_cong])
apply (unfold BufEq_F_def)
apply (simp)
done

lemma Buf_f_empty: "f:BufEq \<Longrightarrow> f\<cdot><> = <>"
by (drule BufEq_unfold [THEN iffD1], auto)

lemma Buf_f_d: "f:BufEq \<Longrightarrow> f\<cdot>(Md d\<leadsto><>) = <>"
by (drule BufEq_unfold [THEN iffD1], auto)

lemma Buf_f_d_req:
        "f:BufEq \<Longrightarrow> \<exists>ff. ff:BufEq \<and> f\<cdot>(Md d\<leadsto>\<bullet>\<leadsto>x) = d\<leadsto>ff\<cdot>x"
by (drule BufEq_unfold [THEN iffD1], auto)


(**** BufAC_Asm ***************************************************************)

lemma mono_BufAC_Asm_F: "mono BufAC_Asm_F"
by (unfold mono_def BufAC_Asm_F_def, fast)

lemmas BufAC_Asm_fix =
  mono_BufAC_Asm_F [THEN BufAC_Asm_def [THEN eq_reflection, THEN def_gfp_unfold]]

lemma BufAC_Asm_unfold: "(s:BufAC_Asm) = (s = <> | (? d x. 
        s = Md d\<leadsto>x & (x = <> | (ft\<cdot>x = Def \<bullet> & (rt\<cdot>x):BufAC_Asm))))"
apply (subst BufAC_Asm_fix [THEN set_cong])
apply (unfold BufAC_Asm_F_def)
apply (simp)
done

lemma BufAC_Asm_empty: "<>     :BufAC_Asm"
by (rule BufAC_Asm_unfold [THEN iffD2], auto)

lemma BufAC_Asm_d: "Md d\<leadsto><>:BufAC_Asm"
by (rule BufAC_Asm_unfold [THEN iffD2], auto)
lemma BufAC_Asm_d_req: "x:BufAC_Asm ==> Md d\<leadsto>\<bullet>\<leadsto>x:BufAC_Asm"
by (rule BufAC_Asm_unfold [THEN iffD2], auto)
lemma BufAC_Asm_prefix2: "a\<leadsto>b\<leadsto>s:BufAC_Asm ==> s:BufAC_Asm"
by (drule BufAC_Asm_unfold [THEN iffD1], auto)


(**** BBufAC_Cmt **************************************************************)

lemma mono_BufAC_Cmt_F: "mono BufAC_Cmt_F"
by (unfold mono_def BufAC_Cmt_F_def, fast)

lemmas BufAC_Cmt_fix =
  mono_BufAC_Cmt_F [THEN BufAC_Cmt_def [THEN eq_reflection, THEN def_gfp_unfold]]

lemma BufAC_Cmt_unfold: "((s,t):BufAC_Cmt) = (!d x. 
     (s = <>       -->      t = <>) & 
     (s = Md d\<leadsto><>  -->      t = <>) & 
     (s = Md d\<leadsto>\<bullet>\<leadsto>x --> ft\<cdot>t = Def d & (x, rt\<cdot>t):BufAC_Cmt))"
apply (subst BufAC_Cmt_fix [THEN set_cong])
apply (unfold BufAC_Cmt_F_def)
apply (simp)
done

lemma BufAC_Cmt_empty: "f:BufEq ==> (<>, f\<cdot><>):BufAC_Cmt"
by (rule BufAC_Cmt_unfold [THEN iffD2], auto simp add: Buf_f_empty)

lemma BufAC_Cmt_d: "f:BufEq ==> (a\<leadsto>\<bottom>, f\<cdot>(a\<leadsto>\<bottom>)):BufAC_Cmt"
by (rule BufAC_Cmt_unfold [THEN iffD2], auto simp add: Buf_f_d)

lemma BufAC_Cmt_d2:
 "(Md d\<leadsto>\<bottom>, f\<cdot>(Md d\<leadsto>\<bottom>)):BufAC_Cmt ==> f\<cdot>(Md d\<leadsto>\<bottom>) = \<bottom>"
by (drule BufAC_Cmt_unfold [THEN iffD1], auto)

lemma BufAC_Cmt_d3:
"(Md d\<leadsto>\<bullet>\<leadsto>x, f\<cdot>(Md d\<leadsto>\<bullet>\<leadsto>x)):BufAC_Cmt ==> (x, rt\<cdot>(f\<cdot>(Md d\<leadsto>\<bullet>\<leadsto>x))):BufAC_Cmt"
by (drule BufAC_Cmt_unfold [THEN iffD1], auto)

lemma BufAC_Cmt_d32:
"(Md d\<leadsto>\<bullet>\<leadsto>x, f\<cdot>(Md d\<leadsto>\<bullet>\<leadsto>x)):BufAC_Cmt ==> ft\<cdot>(f\<cdot>(Md d\<leadsto>\<bullet>\<leadsto>x)) = Def d"
by (drule BufAC_Cmt_unfold [THEN iffD1], auto)

(**** BufAC *******************************************************************)

lemma BufAC_f_d: "f \<in> BufAC \<Longrightarrow> f\<cdot>(Md d\<leadsto>\<bottom>) = \<bottom>"
apply (unfold BufAC_def)
apply (fast intro: BufAC_Cmt_d2 BufAC_Asm_d)
done

lemma ex_elim_lemma: "(? ff:B. (!x. f\<cdot>(a\<leadsto>b\<leadsto>x) = d\<leadsto>ff\<cdot>x)) = 
    ((!x. ft\<cdot>(f\<cdot>(a\<leadsto>b\<leadsto>x)) = Def d) & (LAM x. rt\<cdot>(f\<cdot>(a\<leadsto>b\<leadsto>x))):B)"
(*  this is an instance (though unification cannot handle this) of
lemma "(? ff:B. (!x. f\<cdot>x = d\<leadsto>ff\<cdot>x)) = \
   \((!x. ft\<cdot>(f\<cdot>x) = Def d) & (LAM x. rt\<cdot>(f\<cdot>x)):B)"*)
apply safe
apply (  rule_tac [2] P="(%x. x:B)" in ssubst)
prefer 3
apply (   assumption)
apply (  rule_tac [2] ext_cfun)
apply (  drule_tac [2] spec)
apply (  drule_tac [2] f="rt" in cfun_arg_cong)
prefer 2
apply (  simp)
prefer 2
apply ( simp)
apply (rule_tac bexI)
apply auto
apply (drule spec)
apply (erule exE)
apply (erule ssubst)
apply (simp)
done

lemma BufAC_f_d_req: "f\<in>BufAC \<Longrightarrow> \<exists>ff\<in>BufAC. \<forall>x. f\<cdot>(Md d\<leadsto>\<bullet>\<leadsto>x) = d\<leadsto>ff\<cdot>x"
apply (unfold BufAC_def)
apply (rule ex_elim_lemma [THEN iffD2])
apply safe
apply  (fast intro: BufAC_Cmt_d32 [THEN Def_maximal]
             monofun_cfun_arg BufAC_Asm_empty [THEN BufAC_Asm_d_req])
apply (auto intro: BufAC_Cmt_d3 BufAC_Asm_d_req)
done


(**** BufSt *******************************************************************)

lemma mono_BufSt_F: "mono BufSt_F"
by (unfold mono_def BufSt_F_def, fast)

lemmas BufSt_P_fix =
  mono_BufSt_F [THEN BufSt_P_def [THEN eq_reflection, THEN def_gfp_unfold]]

lemma BufSt_P_unfold: "(h:BufSt_P) = (!s. h s\<cdot><> = <> & 
           (!d x. h \<currency>     \<cdot>(Md d\<leadsto>x)   =    h (Sd d)\<cdot>x & 
      (? hh:BufSt_P. h (Sd d)\<cdot>(\<bullet>\<leadsto>x)   = d\<leadsto>(hh \<currency>    \<cdot>x))))"
apply (subst BufSt_P_fix [THEN set_cong])
apply (unfold BufSt_F_def)
apply (simp)
done

lemma BufSt_P_empty: "h:BufSt_P ==> h s     \<cdot> <>       = <>"
by (drule BufSt_P_unfold [THEN iffD1], auto)
lemma BufSt_P_d: "h:BufSt_P ==> h  \<currency>    \<cdot>(Md d\<leadsto>x) = h (Sd d)\<cdot>x"
by (drule BufSt_P_unfold [THEN iffD1], auto)
lemma BufSt_P_d_req: "h:BufSt_P ==> \<exists>hh\<in>BufSt_P.
                                          h (Sd d)\<cdot>(\<bullet>   \<leadsto>x) = d\<leadsto>(hh \<currency>    \<cdot>x)"
by (drule BufSt_P_unfold [THEN iffD1], auto)


(**** Buf_AC_imp_Eq ***********************************************************)

lemma Buf_AC_imp_Eq: "BufAC \<subseteq> BufEq"
apply (unfold BufEq_def)
apply (rule gfp_upperbound)
apply (unfold BufEq_F_def)
apply safe
apply  (erule BufAC_f_d)
apply (drule BufAC_f_d_req)
apply (fast)
done


(**** Buf_Eq_imp_AC by coinduction ********************************************)

lemma BufAC_Asm_cong_lemma [rule_format]: "\<forall>s f ff. f\<in>BufEq \<longrightarrow> ff\<in>BufEq \<longrightarrow> 
  s\<in>BufAC_Asm \<longrightarrow> stream_take n\<cdot>(f\<cdot>s) = stream_take n\<cdot>(ff\<cdot>s)"
apply (induct_tac "n")
apply  (simp)
apply (intro strip)
apply (drule BufAC_Asm_unfold [THEN iffD1])
apply safe
apply   (simp add: Buf_f_empty)
apply  (simp add: Buf_f_d)
apply (drule ft_eq [THEN iffD1])
apply (clarsimp)
apply (drule Buf_f_d_req)+
apply safe
apply (erule ssubst)+
apply (simp (no_asm))
apply (fast)
done

lemma BufAC_Asm_cong: "\<lbrakk>f \<in> BufEq; ff \<in> BufEq; s \<in> BufAC_Asm\<rbrakk> \<Longrightarrow> f\<cdot>s = ff\<cdot>s"
apply (rule stream.take_lemmas)
apply (erule (2) BufAC_Asm_cong_lemma)
done

lemma Buf_Eq_imp_AC_lemma: "\<lbrakk>f \<in> BufEq; x \<in> BufAC_Asm\<rbrakk> \<Longrightarrow> (x, f\<cdot>x) \<in> BufAC_Cmt"
apply (unfold BufAC_Cmt_def)
apply (rotate_tac)
apply (erule weak_coinduct_image)
apply (unfold BufAC_Cmt_F_def)
apply safe
apply    (erule Buf_f_empty)
apply   (erule Buf_f_d)
apply  (drule Buf_f_d_req)
apply  (clarsimp)
apply  (erule exI)
apply (drule BufAC_Asm_prefix2)
apply (frule Buf_f_d_req)
apply (clarsimp)
apply (erule ssubst)
apply (simp)
apply (drule (2) BufAC_Asm_cong)
apply (erule subst)
apply (erule imageI)
done
lemma Buf_Eq_imp_AC: "BufEq \<subseteq> BufAC"
apply (unfold BufAC_def)
apply (clarify)
apply (erule (1) Buf_Eq_imp_AC_lemma)
done

(**** Buf_Eq_eq_AC ************************************************************)

lemmas Buf_Eq_eq_AC = Buf_AC_imp_Eq [THEN Buf_Eq_imp_AC [THEN subset_antisym]]


(**** alternative (not strictly) stronger version of Buf_Eq *******************)

lemma Buf_Eq_alt_imp_Eq: "BufEq_alt \<subseteq> BufEq"
apply (unfold BufEq_def BufEq_alt_def)
apply (rule gfp_mono)
apply (unfold BufEq_F_def)
apply (fast)
done

(* direct proof of "BufEq \<subseteq> BufEq_alt" seems impossible *)


lemma Buf_AC_imp_Eq_alt: "BufAC <= BufEq_alt"
apply (unfold BufEq_alt_def)
apply (rule gfp_upperbound)
apply (fast elim: BufAC_f_d BufAC_f_d_req)
done

lemmas Buf_Eq_imp_Eq_alt = subset_trans [OF Buf_Eq_imp_AC Buf_AC_imp_Eq_alt]

lemmas Buf_Eq_alt_eq = subset_antisym [OF Buf_Eq_alt_imp_Eq Buf_Eq_imp_Eq_alt]


(**** Buf_Eq_eq_St ************************************************************)

lemma Buf_St_imp_Eq: "BufSt <= BufEq"
apply (unfold BufSt_def BufEq_def)
apply (rule gfp_upperbound)
apply (unfold BufEq_F_def)
apply safe
apply ( simp add: BufSt_P_d BufSt_P_empty)
apply (simp add: BufSt_P_d)
apply (drule BufSt_P_d_req)
apply (force)
done

lemma Buf_Eq_imp_St: "BufEq <= BufSt"
apply (unfold BufSt_def BufSt_P_def)
apply safe
apply (rename_tac f)
apply (rule_tac x="\<lambda>s. case s of Sd d => \<Lambda> x. f\<cdot>(Md d\<leadsto>x)| \<currency> => f" in bexI)
apply ( simp)
apply (erule weak_coinduct_image)
apply (unfold BufSt_F_def)
apply (simp)
apply safe
apply (  rename_tac "s")
apply (  induct_tac "s")
apply (   simp add: Buf_f_d)
apply (  simp add: Buf_f_empty)
apply ( simp)
apply (simp)
apply (rename_tac f d x)
apply (drule_tac d="d" and x="x" in Buf_f_d_req)
apply auto
done

lemmas Buf_Eq_eq_St = Buf_St_imp_Eq [THEN Buf_Eq_imp_St [THEN subset_antisym]]

end
