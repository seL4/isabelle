
header {* \section{Operational Semantics} *}

theory RG_Tran = RG_Com:

subsection {* Semantics of Component Programs *}

subsubsection {* Environment transitions *}

types 'a conf = "(('a com) option) \<times> 'a"

consts etran    :: "('a conf \<times> 'a conf) set" 
syntax  "_etran"  :: "'a conf \<Rightarrow> 'a conf \<Rightarrow> bool"  ("_ -e\<rightarrow> _" [81,81] 80)
translations  "P -e\<rightarrow> Q"  \<rightleftharpoons> "(P,Q) \<in> etran"
inductive etran
intros
  Env: "(P, s) -e\<rightarrow> (P, t)"

subsubsection {* Component transitions *}

consts ctran    :: "('a conf \<times> 'a conf) set"
syntax
  "_ctran"  :: "'a conf \<Rightarrow> 'a conf \<Rightarrow> bool"   ("_ -c\<rightarrow> _" [81,81] 80)
  "_ctran_*":: "'a conf \<Rightarrow> 'a conf \<Rightarrow> bool"   ("_ -c*\<rightarrow> _" [81,81] 80)
translations
  "P -c\<rightarrow> Q"  \<rightleftharpoons> "(P,Q) \<in> ctran"
  "P -c*\<rightarrow> Q" \<rightleftharpoons> "(P,Q) \<in> ctran^*"

inductive  ctran 
intros
  Basic:  "(Some(Basic f), s) -c\<rightarrow> (None, f s)"

  Seq1:   "(Some P0, s) -c\<rightarrow> (None, t) \<Longrightarrow> (Some(Seq P0 P1), s) -c\<rightarrow> (Some P1, t)"

  Seq2:   "(Some P0, s) -c\<rightarrow> (Some P2, t) \<Longrightarrow> (Some(Seq P0 P1), s) -c\<rightarrow> (Some(Seq P2 P1), t)"

  CondT: "s\<in>b  \<Longrightarrow> (Some(Cond b P1 P2), s) -c\<rightarrow> (Some P1, s)"
  CondF: "s\<notin>b \<Longrightarrow> (Some(Cond b P1 P2), s) -c\<rightarrow> (Some P2, s)"

  WhileF: "s\<notin>b \<Longrightarrow> (Some(While b P), s) -c\<rightarrow> (None, s)"
  WhileT: "s\<in>b  \<Longrightarrow> (Some(While b P), s) -c\<rightarrow> (Some(Seq P (While b P)), s)"

  Await:  "\<lbrakk>s\<in>b; (Some P, s) -c*\<rightarrow> (None, t)\<rbrakk> \<Longrightarrow> (Some(Await b P), s) -c\<rightarrow> (None, t)" 

monos "rtrancl_mono"

subsection {* Semantics of Parallel Programs *}

types 'a par_conf = "('a par_com) \<times> 'a"
consts
  par_etran :: "('a par_conf \<times> 'a par_conf) set"
  par_ctran :: "('a par_conf \<times> 'a par_conf) set"
syntax
  "_par_etran":: "['a par_conf,'a par_conf] \<Rightarrow> bool" ("_ -pe\<rightarrow> _" [81,81] 80)
  "_par_ctran":: "['a par_conf,'a par_conf] \<Rightarrow> bool" ("_ -pc\<rightarrow> _" [81,81] 80)
translations
  "P -pe\<rightarrow> Q"  \<rightleftharpoons> "(P,Q) \<in> par_etran"
  "P -pc\<rightarrow> Q"  \<rightleftharpoons> "(P,Q) \<in> par_ctran"

inductive  par_etran
intros
  ParEnv:  "(Ps, s) -pe\<rightarrow> (Ps, t)"

inductive  par_ctran
intros
  ParComp: "\<lbrakk>i<length Ps; (Ps!i, s) -c\<rightarrow> (r, t)\<rbrakk> \<Longrightarrow> (Ps, s) -pc\<rightarrow> (Ps[i:=r], t)"

subsection {* Computations *}

subsubsection {* Sequential computations *}

types 'a confs = "('a conf) list"
consts cptn :: "('a confs) set"
inductive  "cptn"
intros
  CptnOne: "[(P,s)] \<in> cptn"
  CptnEnv: "(P, t)#xs \<in> cptn \<Longrightarrow> (P,s)#(P,t)#xs \<in> cptn"
  CptnComp: "\<lbrakk>(P,s) -c\<rightarrow> (Q,t); (Q, t)#xs \<in> cptn \<rbrakk> \<Longrightarrow> (P,s)#(Q,t)#xs \<in> cptn"

constdefs
  cp :: "('a com) option \<Rightarrow> 'a \<Rightarrow> ('a confs) set"
  "cp P s \<equiv> {l. l!0=(P,s) \<and> l \<in> cptn}"  

subsubsection {* Parallel computations *}

types  'a par_confs = "('a par_conf) list"
consts par_cptn :: "('a par_confs) set"
inductive  "par_cptn"
intros
  ParCptnOne: "[(P,s)] \<in> par_cptn"
  ParCptnEnv: "(P,t)#xs \<in> par_cptn \<Longrightarrow> (P,s)#(P,t)#xs \<in> par_cptn"
  ParCptnComp: "\<lbrakk> (P,s) -pc\<rightarrow> (Q,t); (Q,t)#xs \<in> par_cptn \<rbrakk> \<Longrightarrow> (P,s)#(Q,t)#xs \<in> par_cptn"

constdefs
  par_cp :: "'a par_com \<Rightarrow> 'a \<Rightarrow> ('a par_confs) set"
  "par_cp P s \<equiv> {l. l!0=(P,s) \<and> l \<in> par_cptn}"  

subsection{* Modular Definition of Computation *}

constdefs 
  lift :: "'a com \<Rightarrow> 'a conf \<Rightarrow> 'a conf"
  "lift Q \<equiv> \<lambda>(P, s). (if P=None then (Some Q,s) else (Some(Seq (the P) Q), s))"

consts  cptn_mod :: "('a confs) set"
inductive  "cptn_mod"
intros
  CptnModOne: "[(P, s)] \<in> cptn_mod"
  CptnModEnv: "(P, t)#xs \<in> cptn_mod \<Longrightarrow> (P, s)#(P, t)#xs \<in> cptn_mod"
  CptnModNone: "\<lbrakk>(Some P, s) -c\<rightarrow> (None, t); (None, t)#xs \<in> cptn_mod \<rbrakk> \<Longrightarrow> (Some P,s)#(None, t)#xs \<in>cptn_mod"
  CptnModCondT: "\<lbrakk>(Some P0, s)#ys \<in> cptn_mod; s \<in> b \<rbrakk> \<Longrightarrow> (Some(Cond b P0 P1), s)#(Some P0, s)#ys \<in> cptn_mod"
  CptnModCondF: "\<lbrakk>(Some P1, s)#ys \<in> cptn_mod; s \<notin> b \<rbrakk> \<Longrightarrow> (Some(Cond b P0 P1), s)#(Some P1, s)#ys \<in> cptn_mod"
  CptnModSeq1: "\<lbrakk>(Some P0, s)#xs \<in> cptn_mod; zs=map (lift P1) xs \<rbrakk>
                 \<Longrightarrow> (Some(Seq P0 P1), s)#zs \<in> cptn_mod"
  CptnModSeq2: 
  "\<lbrakk>(Some P0, s)#xs \<in> cptn_mod; fst(last ((Some P0, s)#xs)) = None; 
  (Some P1, snd(last ((Some P0, s)#xs)))#ys \<in> cptn_mod; 
  zs=(map (lift P1) xs)@ys \<rbrakk> \<Longrightarrow> (Some(Seq P0 P1), s)#zs \<in> cptn_mod"

  CptnModWhile1: 
  "\<lbrakk> (Some P, s)#xs \<in> cptn_mod; s \<in> b; zs=map (lift (While b P)) xs \<rbrakk> 
  \<Longrightarrow> (Some(While b P), s)#(Some(Seq P (While b P)), s)#zs \<in> cptn_mod"
  CptnModWhile2: 
  "\<lbrakk> (Some P, s)#xs \<in> cptn_mod; fst(last ((Some P, s)#xs))=None; s \<in> b; 
  zs=(map (lift (While b P)) xs)@ys; 
  (Some(While b P), snd(last ((Some P, s)#xs)))#ys \<in> cptn_mod\<rbrakk> 
  \<Longrightarrow> (Some(While b P), s)#(Some(Seq P (While b P)), s)#zs \<in> cptn_mod"

subsection {* Equivalence of Both Definitions.*}

lemma last_length: "((a#xs)!(length xs))=last (a#xs)"
apply simp
apply(induct xs,simp+)
apply(case_tac list)
apply simp_all
done

lemma div_seq [rule_format]: "list \<in> cptn_mod \<Longrightarrow>
 (\<forall>s P Q zs. list=(Some (Seq P Q), s)#zs \<longrightarrow>
  (\<exists>xs. (Some P, s)#xs \<in> cptn_mod  \<and> (zs=(map (lift Q) xs) \<or>
  ( fst(((Some P, s)#xs)!length xs)=None \<and> 
  (\<exists>ys. (Some Q, snd(((Some P, s)#xs)!length xs))#ys \<in> cptn_mod  
  \<and> zs=(map (lift (Q)) xs)@ys)))))"
apply(erule cptn_mod.induct)
apply simp_all
    apply clarify
    apply(force intro:CptnModOne)
   apply clarify
   apply(erule_tac x=Pa in allE)
   apply(erule_tac x=Q in allE)
   apply simp
   apply clarify
   apply(erule disjE)
    apply(rule_tac x="(Some Pa,t)#xsa" in exI)
    apply(rule conjI)
     apply clarify
     apply(erule CptnModEnv)
    apply(rule disjI1)
    apply(simp add:lift_def)
   apply clarify
   apply(rule_tac x="(Some Pa,t)#xsa" in exI)
   apply(rule conjI)
    apply(erule CptnModEnv)
   apply(rule disjI2)
   apply(rule conjI)
    apply(case_tac xsa,simp,simp)
   apply(rule_tac x="ys" in exI)
   apply(rule conjI)
    apply simp
   apply(simp add:lift_def)
  apply clarify
  apply(erule ctran.elims,simp_all)
 apply clarify
 apply(rule_tac x="xs" in exI)
 apply simp
 apply clarify
apply(rule_tac x="xs" in exI)
apply(simp add: last_length)
done

lemma cptn_onlyif_cptn_mod_aux [rule_format]:
  "\<forall>s Q t xs.((Some a, s), Q, t) \<in> ctran \<longrightarrow> (Q, t) # xs \<in> cptn_mod 
  \<longrightarrow> (Some a, s) # (Q, t) # xs \<in> cptn_mod"
apply(induct a)
apply simp_all
--{* basic *}
apply clarify
apply(erule ctran.elims,simp_all)
apply(rule CptnModNone,rule Basic,simp)
apply clarify
apply(erule ctran.elims,simp_all)
--{* Seq1 *}
apply(rule_tac xs="[(None,ta)]" in CptnModSeq2)
  apply(erule CptnModNone)
  apply(rule CptnModOne)
 apply simp
apply simp
apply(simp add:lift_def)
--{* Seq2 *}
apply(erule_tac x=sa in allE)
apply(erule_tac x="Some P2" in allE)
apply(erule allE,erule impE, assumption)
apply(drule div_seq,simp)
apply force
apply clarify
apply(erule disjE)
 apply clarify
 apply(erule allE,erule impE, assumption)
 apply(erule_tac CptnModSeq1)
 apply(simp add:lift_def)
apply clarify 
apply(erule allE,erule impE, assumption)
apply(erule_tac CptnModSeq2)
  apply (simp add:last_length)
 apply (simp add:last_length)
apply(simp add:lift_def)
--{* Cond *}
apply clarify
apply(erule ctran.elims,simp_all)
apply(force elim: CptnModCondT)
apply(force elim: CptnModCondF)
--{* While *}
apply  clarify
apply(erule ctran.elims,simp_all)
apply(rule CptnModNone,erule WhileF,simp)
apply(drule div_seq,force)
apply clarify
apply (erule disjE)
 apply(force elim:CptnModWhile1)
apply clarify
apply(force simp add:last_length elim:CptnModWhile2)
--{* await *}
apply clarify
apply(erule ctran.elims,simp_all)
apply(rule CptnModNone,erule Await,simp+)
done

lemma cptn_onlyif_cptn_mod [rule_format]: "c \<in> cptn \<Longrightarrow> c \<in> cptn_mod"
apply(erule cptn.induct)
  apply(rule CptnModOne)
 apply(erule CptnModEnv)
apply(case_tac P)
 apply simp
 apply(erule ctran.elims,simp_all)
apply(force elim:cptn_onlyif_cptn_mod_aux)
done

lemma lift_is_cptn: "c\<in>cptn \<Longrightarrow> map (lift P) c \<in> cptn"
apply(erule cptn.induct)
  apply(force simp add:lift_def CptnOne)
 apply(force intro:CptnEnv simp add:lift_def)
apply(force simp add:lift_def intro:CptnComp Seq2 Seq1 elim:ctran.elims)
done

lemma cptn_append_is_cptn [rule_format]: 
 "\<forall>b a. b#c1\<in>cptn \<longrightarrow>  a#c2\<in>cptn \<longrightarrow> (b#c1)!length c1=a \<longrightarrow> b#c1@c2\<in>cptn"
apply(induct c1)
 apply simp
apply clarify
apply(erule cptn.elims,simp_all)
 apply(force intro:CptnEnv)
apply(force elim:CptnComp)
done

lemma last_lift: "\<lbrakk>xs\<noteq>[]; fst(xs!(length xs - (Suc 0)))=None\<rbrakk> 
 \<Longrightarrow> fst((map (lift P) xs)!(length (map (lift P) xs)- (Suc 0)))=(Some P)"
apply(case_tac "(xs ! (length xs - (Suc 0)))")
apply (simp add:lift_def)
done

lemma last_fst [rule_format]: "P((a#x)!length x) \<longrightarrow> \<not>P a \<longrightarrow> P (x!(length x - (Suc 0)))" 
apply(induct x,simp+)
done

lemma last_fst_esp: 
 "fst(((Some a,s)#xs)!(length xs))=None \<Longrightarrow> fst(xs!(length xs - (Suc 0)))=None" 
apply(erule last_fst)
apply simp
done

lemma last_snd: "xs\<noteq>[] \<Longrightarrow> 
  snd(((map (lift P) xs))!(length (map (lift P) xs) - (Suc 0)))=snd(xs!(length xs - (Suc 0)))"
apply(case_tac "(xs ! (length xs - (Suc 0)))",simp)
apply (simp add:lift_def)
done

lemma Cons_lift: "(Some (Seq P Q), s) # (map (lift Q) xs) = map (lift Q) ((Some P, s) # xs)"
by(simp add:lift_def)

lemma Cons_lift_append: 
  "(Some (Seq P Q), s) # (map (lift Q) xs) @ ys = map (lift Q) ((Some P, s) # xs)@ ys "
by(simp add:lift_def)

lemma lift_nth: "i<length xs \<Longrightarrow> map (lift Q) xs ! i = lift Q  (xs! i)"
by (simp add:lift_def)

lemma snd_lift: "i< length xs \<Longrightarrow> snd(lift Q (xs ! i))= snd (xs ! i)"
apply(case_tac "xs!i")
apply(simp add:lift_def)
done

lemma cptn_if_cptn_mod: "c \<in> cptn_mod \<Longrightarrow> c \<in> cptn"
apply(erule cptn_mod.induct)
        apply(rule CptnOne)
       apply(erule CptnEnv)
      apply(erule CptnComp,simp)
     apply(rule CptnComp)
     apply(erule CondT,simp)
    apply(rule CptnComp)
    apply(erule CondF,simp)
--{* Seq1 *}   
apply(erule cptn.elims,simp_all)
  apply(rule CptnOne)
 apply clarify
 apply(drule_tac P=P1 in lift_is_cptn)
 apply(simp add:lift_def)
 apply(rule CptnEnv,simp)
apply clarify
apply(simp add:lift_def)
apply(rule conjI)
 apply clarify
 apply(rule CptnComp)
  apply(rule Seq1,simp)
 apply(drule_tac P=P1 in lift_is_cptn)
 apply(simp add:lift_def)
apply clarify
apply(rule CptnComp)
 apply(rule Seq2,simp)
apply(drule_tac P=P1 in lift_is_cptn)
apply(simp add:lift_def)
--{* Seq2 *}
apply(rule cptn_append_is_cptn)
  apply(drule_tac P=P1 in lift_is_cptn)
  apply(simp add:lift_def)
 apply simp
apply(case_tac "xs\<noteq>[]")
 apply(drule_tac P=P1 in last_lift)
  apply(rule last_fst_esp)
  apply (simp add:last_length)
 apply(simp add:Cons_lift del:map.simps)
 apply(rule conjI, clarify, simp)
 apply(case_tac "(((Some P0, s) # xs) ! length xs)")
 apply clarify
 apply (simp add:lift_def last_length)
apply (simp add:last_length)
--{* While1 *}
apply(rule CptnComp)
apply(rule WhileT,simp)
apply(drule_tac P="While b P" in lift_is_cptn)
apply(simp add:lift_def)
--{* While2 *}
apply(rule CptnComp)
apply(rule WhileT,simp)
apply(rule cptn_append_is_cptn)
apply(drule_tac P="While b P" in lift_is_cptn)
  apply(simp add:lift_def)
 apply simp
apply(case_tac "xs\<noteq>[]")
 apply(drule_tac P="While b P" in last_lift)
  apply(rule last_fst_esp,simp add:last_length)
 apply(simp add:Cons_lift del:map.simps)
 apply(rule conjI, clarify, simp)
 apply(case_tac "(((Some P, s) # xs) ! length xs)")
 apply clarify
 apply (simp add:last_length lift_def)
apply simp
done

theorem cptn_iff_cptn_mod: "(c \<in> cptn) = (c \<in> cptn_mod)"
apply(rule iffI)
 apply(erule cptn_onlyif_cptn_mod)
apply(erule cptn_if_cptn_mod)
done

section {* Validity  of Correctness Formulas*}

subsection {* Validity for Component Programs. *}

types 'a rgformula = "'a com \<times> 'a set \<times> ('a \<times> 'a) set \<times> ('a \<times> 'a) set \<times> 'a set"

constdefs
  assum :: "('a set \<times> ('a \<times> 'a) set) \<Rightarrow> ('a confs) set"
  "assum \<equiv> \<lambda>(pre, rely). {c. snd(c!0) \<in> pre \<and> (\<forall>i. Suc i<length c \<longrightarrow> 
               c!i -e\<rightarrow> c!(Suc i) \<longrightarrow> (snd(c!i), snd(c!Suc i)) \<in> rely)}"

  comm :: "(('a \<times> 'a) set \<times> 'a set) \<Rightarrow> ('a confs) set"
  "comm \<equiv> \<lambda>(guar, post). {c. (\<forall>i. Suc i<length c \<longrightarrow> 
               c!i -c\<rightarrow> c!(Suc i) \<longrightarrow> (snd(c!i), snd(c!Suc i)) \<in> guar) \<and> 
               (fst (last c) = None \<longrightarrow> snd (last c) \<in> post)}"

  com_validity :: "'a com \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> bool" 
                 ("\<Turnstile> _ sat [_, _, _, _]" [60,0,0,0,0] 45)
  "\<Turnstile> P sat [pre, rely, guar, post] \<equiv> 
   \<forall>s. cp (Some P) s \<inter> assum(pre, rely) \<subseteq> comm(guar, post)"

subsection {* Validity for Parallel Programs. *}

constdefs
  All_None :: "(('a com) option) list \<Rightarrow> bool"
  "All_None xs \<equiv> \<forall>c\<in>set xs. c=None"

  par_assum :: "('a set \<times> ('a \<times> 'a) set) \<Rightarrow> ('a par_confs) set"
  "par_assum \<equiv> \<lambda>(pre, rely). {c. snd(c!0) \<in> pre \<and> (\<forall>i. Suc i<length c \<longrightarrow> 
             c!i -pe\<rightarrow> c!Suc i \<longrightarrow> (snd(c!i), snd(c!Suc i)) \<in> rely)}"

  par_comm :: "(('a \<times> 'a) set \<times> 'a set) \<Rightarrow> ('a par_confs) set"
  "par_comm \<equiv> \<lambda>(guar, post). {c. (\<forall>i. Suc i<length c \<longrightarrow>   
        c!i -pc\<rightarrow> c!Suc i \<longrightarrow> (snd(c!i), snd(c!Suc i)) \<in> guar) \<and> 
         (All_None (fst (last c)) \<longrightarrow> snd( last c) \<in> post)}"

  par_com_validity :: "'a  par_com \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set 
\<Rightarrow> 'a set \<Rightarrow> bool"  ("\<Turnstile> _ SAT [_, _, _, _]" [60,0,0,0,0] 45)
  "\<Turnstile> Ps SAT [pre, rely, guar, post] \<equiv> 
   \<forall>s. par_cp Ps s \<inter> par_assum(pre, rely) \<subseteq> par_comm(guar, post)"

subsection {* Compositionality of the Semantics *}

subsubsection {* Definition of the conjoin operator *}

constdefs
  same_length :: "'a par_confs \<Rightarrow> ('a confs) list \<Rightarrow> bool"
  "same_length c clist \<equiv> (\<forall>i<length clist. length(clist!i)=length c)"
 
  same_state :: "'a par_confs \<Rightarrow> ('a confs) list \<Rightarrow> bool"
  "same_state c clist \<equiv> (\<forall>i <length clist. \<forall>j<length c. snd(c!j) = snd((clist!i)!j))"

  same_program :: "'a par_confs \<Rightarrow> ('a confs) list \<Rightarrow> bool"
  "same_program c clist \<equiv> (\<forall>j<length c. fst(c!j) = map (\<lambda>x. fst(nth x j)) clist)"

  compat_label :: "'a par_confs \<Rightarrow> ('a confs) list \<Rightarrow> bool"
  "compat_label c clist \<equiv> (\<forall>j. Suc j<length c \<longrightarrow> 
         (c!j -pc\<rightarrow> c!Suc j \<and> (\<exists>i<length clist. (clist!i)!j -c\<rightarrow> (clist!i)! Suc j \<and> 
                       (\<forall>l<length clist. l\<noteq>i \<longrightarrow> (clist!l)!j -e\<rightarrow> (clist!l)! Suc j))) \<or> 
         (c!j -pe\<rightarrow> c!Suc j \<and> (\<forall>i<length clist. (clist!i)!j -e\<rightarrow> (clist!i)! Suc j)))"

  conjoin :: "'a par_confs \<Rightarrow> ('a confs) list \<Rightarrow> bool"  ("_ \<propto> _" [65,65] 64)
  "c \<propto> clist \<equiv> (same_length c clist) \<and> (same_state c clist) \<and> (same_program c clist) \<and> (compat_label c clist)"

subsubsection {* Some previous lemmas *}

lemma list_eq_if [rule_format]: 
  "\<forall>ys. xs=ys \<longrightarrow> (length xs = length ys) \<longrightarrow> (\<forall>i<length xs. xs!i=ys!i)"
apply (induct xs)
 apply simp
apply clarify
done

lemma list_eq: "(length xs = length ys \<and> (\<forall>i<length xs. xs!i=ys!i)) = (xs=ys)"
apply(rule iffI)
 apply clarify
 apply(erule nth_equalityI)
 apply simp+
done

lemma nth_tl: "\<lbrakk> ys!0=a; ys\<noteq>[] \<rbrakk> \<Longrightarrow> ys=(a#(tl ys))"
apply(case_tac ys)
 apply simp+
done

lemma nth_tl_if [rule_format]: "ys\<noteq>[] \<longrightarrow> ys!0=a \<longrightarrow> P ys \<longrightarrow> P (a#(tl ys))"
apply(induct ys)
 apply simp+
done

lemma nth_tl_onlyif [rule_format]: "ys\<noteq>[] \<longrightarrow> ys!0=a \<longrightarrow> P (a#(tl ys)) \<longrightarrow> P ys"
apply(induct ys)
 apply simp+
done

lemma seq_not_eq1: "Seq c1 c2\<noteq>c1"
apply(rule com.induct)
apply simp_all
apply clarify
done

lemma seq_not_eq2: "Seq c1 c2\<noteq>c2"
apply(rule com.induct)
apply simp_all
apply clarify
done

lemma if_not_eq1: "Cond b c1 c2 \<noteq>c1"
apply(rule com.induct)
apply simp_all
apply clarify
done

lemma if_not_eq2: "Cond b c1 c2\<noteq>c2"
apply(rule com.induct)
apply simp_all
apply clarify
done

lemmas seq_and_if_not_eq [simp] = seq_not_eq1 seq_not_eq2 
seq_not_eq1 [THEN not_sym] seq_not_eq2 [THEN not_sym] 
if_not_eq1 if_not_eq2 if_not_eq1 [THEN not_sym] if_not_eq2 [THEN not_sym]

lemma prog_not_eq_in_ctran_aux [rule_format]: "(P,s) -c\<rightarrow> (Q,t) \<Longrightarrow> (P\<noteq>Q)"
apply(erule ctran.induct)
apply simp_all
done

lemma prog_not_eq_in_ctran [simp]: "\<not> (P,s) -c\<rightarrow> (P,t)"
apply clarify
apply(drule prog_not_eq_in_ctran_aux)
apply simp
done

lemma prog_not_eq_in_par_ctran_aux [rule_format]: "(P,s) -pc\<rightarrow> (Q,t) \<Longrightarrow> (P\<noteq>Q)"
apply(erule par_ctran.induct)
apply(drule prog_not_eq_in_ctran_aux)
apply clarify
apply(drule list_eq_if)
 apply simp_all
apply force
done

lemma prog_not_eq_in_par_ctran [simp]: "\<not> (P,s) -pc\<rightarrow> (P,t)"
apply clarify
apply(drule prog_not_eq_in_par_ctran_aux)
apply simp
done

lemma tl_in_cptn: "\<lbrakk> a#xs \<in>cptn; xs\<noteq>[] \<rbrakk> \<Longrightarrow> xs\<in>cptn"
apply(force elim:cptn.elims)
done

lemma tl_zero[rule_format]: 
  "P (ys!Suc j) \<longrightarrow> Suc j<length ys \<longrightarrow> ys\<noteq>[] \<longrightarrow> P (tl(ys)!j)"
apply(induct ys)
 apply simp_all
done

subsection {* The Semantics is Compositional *}

lemma aux_if [rule_format]: 
  "\<forall>xs s clist. (length clist = length xs \<and> (\<forall>i<length xs. (xs!i,s)#clist!i \<in> cptn) 
  \<and> ((xs, s)#ys \<propto> map (\<lambda>i. (fst i,s)#snd i) (zip xs clist)) 
   \<longrightarrow> (xs, s)#ys \<in> par_cptn)"
apply(induct ys)
 apply(clarify)
 apply(rule ParCptnOne)
apply(clarify)
apply(simp add:conjoin_def compat_label_def)
apply clarify
apply(erule_tac x="0" and P="\<lambda>j. ?H j \<longrightarrow> (?P j \<or> ?Q j)" in all_dupE,simp)
apply(erule disjE)
--{* first step is a Component step *}
 apply clarify 
 apply simp
 apply(subgoal_tac "a=(xs[i:=(fst(clist!i!0))])")
  apply(subgoal_tac "b=snd(clist!i!0)",simp)
   prefer 2
   apply(simp add: same_state_def)
   apply(erule_tac x=i in allE,erule impE,assumption, 
         erule_tac x=1 and P="\<lambda>j. (?H j) \<longrightarrow> (snd (?d j))=(snd (?e j))" in allE,simp)
  prefer 2
  apply(simp add:same_program_def)
  apply(erule_tac x=1 and P="\<lambda>j. ?H j \<longrightarrow> (fst (?s j))=(?t j)" in allE,simp)
  apply(rule nth_equalityI,simp)
  apply clarify
  apply(case_tac "i=ia",simp,simp)
  apply(erule_tac x=ia and P="\<lambda>j. ?H j \<longrightarrow> ?I j \<longrightarrow> ?J j" in allE)
  apply(drule_tac t=i in not_sym,simp)
  apply(erule etran.elims,simp)
 apply(rule ParCptnComp)
  apply(erule ParComp,simp)
--{* applying the induction hypothesis *}
 apply(erule_tac x="xs[i := fst (clist ! i ! 0)]" in allE)
 apply(erule_tac x="snd (clist ! i ! 0)" in allE)
 apply(erule mp)
 apply(rule_tac x="map tl clist" in exI,simp)
 apply(rule conjI,clarify)
  apply(case_tac "i=ia",simp)
   apply(rule nth_tl_if)
     apply(force simp add:same_length_def length_Suc_conv)
    apply simp
   apply(erule allE,erule impE,assumption,erule tl_in_cptn)
   apply(force simp add:same_length_def length_Suc_conv)
  apply(rule nth_tl_if)
    apply(force simp add:same_length_def length_Suc_conv)
   apply(simp add:same_state_def)
   apply(erule_tac x=ia in allE, erule impE, assumption, 
     erule_tac x=1 and P="\<lambda>j. ?H j \<longrightarrow> (snd (?d j))=(snd (?e j))" in allE)
   apply(erule_tac x=ia and P="\<lambda>j. ?H j \<longrightarrow> ?I j \<longrightarrow> ?J j" in allE)
   apply(drule_tac t=i  in not_sym,simp)
   apply(erule etran.elims,simp)
  apply(erule allE,erule impE,assumption,erule tl_in_cptn)
  apply(force simp add:same_length_def length_Suc_conv)
 apply(simp add:same_length_def same_state_def)
 apply(rule conjI)
  apply clarify
  apply(case_tac j,simp,simp)
  apply(erule_tac x=ia in allE, erule impE, assumption,
        erule_tac x="Suc(Suc nat)" and P="\<lambda>j. ?H j \<longrightarrow> (snd (?d j))=(snd (?e j))" in allE,simp)
  apply(force simp add:same_length_def length_Suc_conv)
 apply(rule conjI)
  apply(simp add:same_program_def)
  apply clarify
  apply(case_tac j,simp)
   apply(rule nth_equalityI,simp)
   apply clarify
   apply(case_tac "i=ia",simp,simp)
  apply(erule_tac x="Suc(Suc nat)" and P="\<lambda>j. ?H j \<longrightarrow> (fst (?s j))=(?t j)" in allE,simp)
  apply(rule nth_equalityI,simp,simp)
  apply(force simp add:length_Suc_conv)
 apply(rule allI,rule impI)
 apply(erule_tac x="Suc j" and P="\<lambda>j. ?H j \<longrightarrow> (?I j \<or> ?J j)" in allE,simp)
 apply(erule disjE) 
  apply clarify
  apply(rule_tac x=ia in exI,simp)
  apply(case_tac "i=ia",simp)
   apply(rule conjI)
    apply(force simp add: length_Suc_conv)
   apply clarify
   apply(erule_tac x=l and P="\<lambda>j. ?H j \<longrightarrow> ?I j \<longrightarrow> ?J j" in allE,erule impE,assumption)
   apply(erule_tac x=l and P="\<lambda>j. ?H j \<longrightarrow> ?I j \<longrightarrow> ?J j" in allE,erule impE,assumption)
   apply simp
   apply(case_tac j,simp)
    apply(rule tl_zero)
      apply(drule_tac t=l in not_sym,simp)
      apply(erule_tac x=l in allE, erule impE, assumption, 
            erule_tac x=1 and P="\<lambda>j.  (?H j) \<longrightarrow> (snd (?d j))=(snd (?e j))" in allE,simp)
      apply(force elim:etran.elims intro:Env)
     apply force
    apply force
   apply simp
   apply(rule tl_zero)
     apply(erule tl_zero)
      apply force
     apply force
    apply force
   apply force
  apply(rule conjI,simp)
   apply(rule nth_tl_if)
     apply force
    apply(erule_tac x=ia  in allE, erule impE, assumption,
          erule_tac x=1 and P="\<lambda>j. ?H j \<longrightarrow> (snd (?d j))=(snd (?e j))" in allE)
    apply(erule_tac x=ia and P="\<lambda>j. ?H j \<longrightarrow> ?I j \<longrightarrow> ?J j" in allE)
    apply(drule_tac t=i  in not_sym,simp)
    apply(erule etran.elims,simp)
   apply(erule tl_zero)
    apply force
   apply force
  apply clarify
  apply(case_tac "i=l",simp)
   apply(rule nth_tl_if)
     apply(erule_tac x=l and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE,force)
    apply simp
   apply(erule_tac P="\<lambda>j. ?H j \<longrightarrow> ?I j \<longrightarrow> ?J j" in allE,erule impE,assumption,erule impE,assumption)
   apply(erule tl_zero,force)
   apply(erule_tac x=l and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE,force)
   apply(rule nth_tl_if)
     apply(erule_tac x=l and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE,force)
    apply(erule_tac x=l  in allE, erule impE, assumption,
          erule_tac x=1 and P="\<lambda>j. ?H j \<longrightarrow> (snd (?d j))=(snd (?e j))" in allE)
    apply(erule_tac x=l and P="\<lambda>j. ?H j \<longrightarrow> ?I j \<longrightarrow> ?J j" in allE,erule impE, assumption,simp)
    apply(drule not_sym,erule impE,assumption )
    apply(erule etran.elims,simp)
   apply(rule tl_zero)
    apply force
   apply force
  apply(erule_tac x=l and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE,force)
 apply(rule disjI2)
 apply(case_tac j,simp)
  apply clarify
  apply(rule tl_zero)
    apply(erule_tac x=ia and P="\<lambda>j. ?H j \<longrightarrow> ?I j\<in>etran" in allE,erule impE, assumption)
    apply(case_tac "i=ia",simp,simp)
    apply(erule_tac x=ia  in allE, erule impE, assumption,
    erule_tac x=1 and P="\<lambda>j. ?H j \<longrightarrow> (snd (?d j))=(snd (?e j))" in allE)
    apply(erule_tac x=ia and P="\<lambda>j. ?H j \<longrightarrow> ?I j \<longrightarrow> ?J j" in allE,erule impE, assumption,simp)
    apply(drule not_sym,erule impE,assumption)
    apply(force elim:etran.elims intro:Env)
   apply force
  apply(erule_tac x=ia and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE,force)
 apply simp
 apply clarify
 apply(rule tl_zero)
   apply(rule tl_zero,force)
    apply force
   apply(erule_tac x=ia and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE,force)
  apply force
 apply(erule_tac x=ia and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE,force)
--{* first step is an environmental step *}
apply clarify
apply(erule par_etran.elims)
apply simp
apply(rule ParCptnEnv)
apply(erule_tac x="Ps" in allE)
apply(erule_tac x="t" in allE)
apply(erule mp)
apply(rule_tac x="map tl clist" in exI,simp)
apply(rule conjI)
 apply clarify
 apply(erule_tac x=i and P="\<lambda>j. ?H j \<longrightarrow> (?I ?s j) \<in> cptn" in allE,simp)
 apply(erule cptn.elims)
   apply(simp add:same_length_def)
   apply(erule_tac x=i and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE,force)
  apply(simp add:same_state_def)
  apply(erule_tac x=i  in allE, erule impE, assumption,
   erule_tac x=1 and P="\<lambda>j. ?H j \<longrightarrow> (snd (?d j))=(snd (?e j))" in allE,simp)
 apply(erule_tac x=i and P="\<lambda>j. ?H j \<longrightarrow> ?J j \<in>etran" in allE,simp)
 apply(erule etran.elims,simp)
apply(simp add:same_state_def same_length_def)
apply(rule conjI,clarify)
 apply(case_tac j,simp,simp)
 apply(erule_tac x=i  in allE, erule impE, assumption,
       erule_tac x="Suc(Suc nat)" and P="\<lambda>j. ?H j \<longrightarrow> (snd (?d j))=(snd (?e j))" in allE,simp)
 apply(rule tl_zero)
   apply(simp)
  apply force
 apply(erule_tac x=i and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE,force)
apply(rule conjI)
 apply(simp add:same_program_def)
 apply clarify
 apply(case_tac j,simp)
  apply(rule nth_equalityI,simp)
  apply clarify
  apply simp
 apply(erule_tac x="Suc(Suc nat)" and P="\<lambda>j. ?H j \<longrightarrow> (fst (?s j))=(?t j)" in allE,simp)
 apply(rule nth_equalityI,simp,simp)
 apply(force simp add:length_Suc_conv)
apply(rule allI,rule impI)
apply(erule_tac x="Suc j" and P="\<lambda>j. ?H j \<longrightarrow> (?I j \<or> ?J j)" in allE,simp)
apply(erule disjE) 
 apply clarify
 apply(rule_tac x=i in exI,simp)
 apply(rule conjI)
  apply(erule_tac x=i and P="\<lambda>i. ?H i \<longrightarrow> ?J i \<in>etran" in allE, erule impE, assumption)
  apply(erule etran.elims,simp)
  apply(erule_tac x=i  in allE, erule impE, assumption,
        erule_tac x=1 and P="\<lambda>j.  (?H j) \<longrightarrow> (snd (?d j))=(snd (?e j))" in allE,simp)
  apply(rule nth_tl_if)
   apply(erule_tac x=i and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE,force)
  apply simp
 apply(erule tl_zero,force) 
  apply(erule_tac x=i and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE,force)
 apply clarify
 apply(erule_tac x=l and P="\<lambda>i. ?H i \<longrightarrow> ?J i \<in>etran" in allE, erule impE, assumption)
 apply(erule etran.elims,simp)
 apply(erule_tac x=l  in allE, erule impE, assumption,
       erule_tac x=1 and P="\<lambda>j.  (?H j) \<longrightarrow> (snd (?d j))=(snd (?e j))" in allE,simp)
 apply(rule nth_tl_if)
   apply(erule_tac x=l and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE,force)
  apply simp
  apply(rule tl_zero,force)
  apply force
 apply(erule_tac x=l and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE,force)
apply(rule disjI2)
apply simp
apply clarify
apply(case_tac j,simp)
 apply(rule tl_zero)
   apply(erule_tac x=i and P="\<lambda>i. ?H i \<longrightarrow> ?J i \<in>etran" in allE, erule impE, assumption)
   apply(erule_tac x=i and P="\<lambda>i. ?H i \<longrightarrow> ?J i \<in>etran" in allE, erule impE, assumption)
   apply(force elim:etran.elims intro:Env)
  apply force
 apply(erule_tac x=i and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE,force)
apply simp
apply(rule tl_zero)
  apply(rule tl_zero,force)
   apply force
  apply(erule_tac x=i and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE,force)
 apply force
apply(erule_tac x=i and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE,force)
done

lemma less_Suc_0 [iff]: "(n < Suc 0) = (n = 0)"
by auto

lemma aux_onlyif [rule_format]: "\<forall>xs s. (xs, s)#ys \<in> par_cptn \<longrightarrow> 
  (\<exists>clist. (length clist = length xs) \<and> 
  (xs, s)#ys \<propto> map (\<lambda>i. (fst i,s)#(snd i)) (zip xs clist) \<and> 
  (\<forall>i<length xs. (xs!i,s)#(clist!i) \<in> cptn))"
apply(induct ys)
 apply(clarify)
 apply(rule_tac x="map (\<lambda>i. []) [0..length xs(]" in exI)
 apply(simp add: conjoin_def same_length_def same_state_def same_program_def compat_label_def)
 apply(rule conjI)
  apply(rule nth_equalityI,simp,simp)
 apply(force intro: cptn.intros)
apply(clarify)
apply(erule par_cptn.elims,simp)
 apply simp
 apply(erule_tac x="xs" in allE)
 apply(erule_tac x="t" in allE,simp)
 apply clarify
 apply(rule_tac x="(map (\<lambda>j. (P!j, t)#(clist!j)) [0..length P(])" in exI,simp)
 apply(rule conjI)
  prefer 2
  apply clarify
  apply(rule CptnEnv,simp)
 apply(simp add:conjoin_def same_length_def same_state_def)
 apply (rule conjI)
  apply clarify
  apply(case_tac j,simp,simp)
 apply(rule conjI)
  apply(simp add:same_program_def)
  apply clarify
  apply(case_tac j,simp)
   apply(rule nth_equalityI,simp,simp)
  apply simp
  apply(rule nth_equalityI,simp,simp)
 apply(simp add:compat_label_def)
 apply clarify
 apply(case_tac j,simp)
  apply(simp add:ParEnv)
  apply clarify
  apply(simp add:Env)
 apply simp
 apply(erule_tac x=nat in allE,erule impE, assumption)
 apply(erule disjE,simp)
  apply clarify
  apply(rule_tac x=i in exI,simp)
 apply force
apply(erule par_ctran.elims,simp)
apply(erule_tac x="Ps[i:=r]" in allE)
apply(erule_tac x="ta" in allE,simp)
apply clarify
apply(rule_tac x="(map (\<lambda>j. (Ps!j, ta)#(clist!j)) [0..length Ps(]) [i:=((r, ta)#(clist!i))]" in exI,simp)
apply(rule conjI)
 prefer 2
 apply clarify
 apply(case_tac "i=ia",simp)
  apply(erule CptnComp)
  apply(erule_tac x=ia and P="\<lambda>j. ?H j \<longrightarrow> (?I j \<in> cptn)" in allE,simp)
 apply simp
 apply(erule_tac x=ia in allE)
 apply(rule CptnEnv,simp)
apply(simp add:conjoin_def)
apply (rule conjI)
 apply(simp add:same_length_def)
 apply clarify
 apply(case_tac "i=ia",simp,simp)
apply(rule conjI)
 apply(simp add:same_state_def)
 apply clarify
 apply(case_tac j,simp,simp)
 apply(case_tac "i=ia",simp,simp)
apply(rule conjI)
 apply(simp add:same_program_def)
 apply clarify
 apply(case_tac j,simp)
  apply(rule nth_equalityI,simp,simp)
 apply simp
 apply(rule nth_equalityI,simp,simp)
 apply(erule_tac x=nat and P="\<lambda>j. ?H j \<longrightarrow> (fst (?a j))=((?b j))" in allE)
 apply(case_tac nat)
  apply clarify
  apply(case_tac "i=ia",simp,simp)
 apply clarify
 apply(case_tac "i=ia",simp,simp)
apply(simp add:compat_label_def)
apply clarify
apply(case_tac j)
 apply(rule conjI,simp)
  apply(erule ParComp,assumption)
  apply clarify
  apply(rule_tac x=i in exI,simp)
 apply clarify
 apply(drule not_sym,simp)
 apply(rule Env)
apply simp
apply(erule_tac x=nat and P="\<lambda>j. ?H j \<longrightarrow> (?P j \<or> ?Q j)" in allE,simp)
apply(erule disjE)
 apply clarify
 apply(rule_tac x=ia in exI,simp)
 apply(rule conjI)
  apply(case_tac "i=ia",simp,simp)
  apply(rotate_tac -1,simp)
 apply clarify
 apply(case_tac "i=l",simp)
  apply(case_tac "l=ia",simp,simp)
  apply(erule_tac x=l in allE,erule impE,assumption,erule impE, assumption,simp)
 apply simp
 apply(erule_tac x=l in allE,erule impE,assumption,erule impE, assumption,simp)
apply clarify
apply(erule_tac x=ia and P="\<lambda>j. ?H j \<longrightarrow> (?P j)\<in>etran" in allE, erule impE, assumption)
apply(case_tac "i=ia",simp)
apply(rotate_tac -1,simp)
done

lemma one_iff_aux: "xs\<noteq>[] \<Longrightarrow> (\<forall>ys. ((xs, s)#ys \<in> par_cptn) = 
 (\<exists>clist. length clist= length xs \<and> 
 ((xs, s)#ys \<propto> map (\<lambda>i. (fst i,s)#(snd i)) (zip xs clist)) \<and> 
 (\<forall>i<length xs. (xs!i,s)#(clist!i) \<in> cptn))) = 
 (par_cp (xs) s = {c. \<exists>clist. (length clist)=(length xs) \<and>
 (\<forall>i<length clist. (clist!i) \<in> cp(xs!i) s) \<and> c \<propto> clist})" 
apply (rule iffI)
 apply(rule subset_antisym)
  apply(rule subsetI) 
  apply(clarify)
  apply(simp add:par_cp_def cp_def)
  apply(case_tac x)
   apply(force elim:par_cptn.elims)
  apply simp
  apply(erule_tac x="list" in allE)
  apply clarify
  apply simp
  apply(rule_tac x="map (\<lambda>i. (fst i, s) # snd i) (zip xs clist)" in exI,simp)
 apply(rule subsetI) 
 apply(clarify)
 apply(case_tac x)
  apply(erule_tac x=0 in allE)
  apply(simp add:cp_def conjoin_def same_length_def same_program_def same_state_def compat_label_def)
  apply clarify
  apply(erule cptn.elims,force,force,force)
 apply(simp add:par_cp_def conjoin_def  same_length_def same_program_def same_state_def compat_label_def)
 apply clarify
 apply(erule_tac x=0 and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in all_dupE)
 apply(subgoal_tac "a = xs")
  apply(subgoal_tac "b = s",simp)
   prefer 3
   apply(erule_tac x=0 and P="\<lambda>j. ?H j \<longrightarrow> (fst (?s j))=((?t j))" in allE)
   apply (simp add:cp_def)
   apply(rule nth_equalityI,simp,simp)
  prefer 2
  apply(erule_tac x=0 in allE)
  apply (simp add:cp_def)
  apply(erule_tac x=0 and P="\<lambda>j. ?H j \<longrightarrow> (\<forall>i. ?T i \<longrightarrow> (snd (?d j i))=(snd (?e j i)))" in allE,simp)
  apply(erule_tac x=0 and P="\<lambda>j. ?H j \<longrightarrow> (snd (?d j))=(snd (?e j))" in allE,simp)
 apply(erule_tac x=list in allE)
 apply(rule_tac x="map tl clist" in exI,simp) 
 apply(rule conjI)
  apply clarify
  apply(case_tac j,simp)
   apply(erule_tac x=i  in allE, erule impE, assumption,
        erule_tac x="0" and P="\<lambda>j. ?H j \<longrightarrow> (snd (?d j))=(snd (?e j))" in allE,simp)
  apply(erule_tac x=i  in allE, erule impE, assumption,
        erule_tac x="Suc nat" and P="\<lambda>j. ?H j \<longrightarrow> (snd (?d j))=(snd (?e j))" in allE)
  apply(erule_tac x=i and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE)
  apply(case_tac "clist!i",simp,simp)
 apply(rule conjI)
  apply clarify
  apply(rule nth_equalityI,simp,simp)
  apply(case_tac j)
   apply clarify
   apply(erule_tac x=i in allE)
   apply(simp add:cp_def)
  apply clarify
  apply simp
  apply(erule_tac x=i and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE)
  apply(case_tac "clist!i",simp,simp)
 apply(thin_tac "?H = (\<exists>i. ?J i)")
 apply(rule conjI)
  apply clarify
  apply(erule_tac x=j in allE,erule impE, assumption,erule disjE)
   apply clarify
   apply(rule_tac x=i in exI,simp)
   apply(case_tac j,simp)
    apply(rule conjI)
     apply(erule_tac x=i in allE)
     apply(simp add:cp_def)
     apply(erule_tac x=i and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE)
     apply(case_tac "clist!i",simp,simp)
    apply clarify
    apply(erule_tac x=l in allE)
    apply(erule_tac x=l and P="\<lambda>j. ?H j \<longrightarrow> ?I j \<longrightarrow> ?J j" in allE)
    apply clarify
    apply(simp add:cp_def)
    apply(erule_tac x=l and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE)
    apply(case_tac "clist!l",simp,simp)
   apply simp
   apply(rule conjI)
    apply(erule_tac x=i and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE)
    apply(case_tac "clist!i",simp,simp)
   apply clarify
   apply(erule_tac x=l and P="\<lambda>j. ?H j \<longrightarrow> ?I j \<longrightarrow> ?J j" in allE)
   apply(erule_tac x=l and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE)
   apply(case_tac "clist!l",simp,simp)
  apply clarify
  apply(erule_tac x=i in allE)
  apply(simp add:cp_def)
  apply(erule_tac x=i and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE)
  apply(case_tac "clist!i",simp)
  apply(rule nth_tl_if,simp,simp)
  apply(erule_tac x=i and P="\<lambda>j. ?H j \<longrightarrow> (?P j)\<in>etran" in allE, erule impE, assumption,simp)
  apply(simp add:cp_def)
  apply clarify
  apply(rule nth_tl_if)
   apply(erule_tac x=i and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE)
   apply(case_tac "clist!i",simp,simp)
  apply force
 apply force
apply clarify
apply(rule iffI)
 apply(simp add:par_cp_def)
 apply(erule_tac c="(xs, s) # ys" in equalityCE)
  apply simp
  apply clarify
  apply(rule_tac x="map tl clist" in exI)
  apply simp
  apply (rule conjI)
   apply(simp add:conjoin_def cp_def)
   apply(rule conjI)
    apply clarify
    apply(unfold same_length_def)
    apply clarify
    apply(erule_tac x=i and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE,simp)
   apply(rule conjI)
    apply(simp add:same_state_def)
    apply clarify
    apply(erule_tac x=i in allE, erule impE, assumption,
       erule_tac x=j and P="\<lambda>j. ?H j \<longrightarrow> (snd (?d j))=(snd (?e j))" in allE)
    apply(case_tac j,simp)
    apply(erule_tac x=i and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE)
    apply(case_tac "clist!i",simp,simp)
   apply(rule conjI)
    apply(simp add:same_program_def)
    apply clarify
    apply(rule nth_equalityI,simp,simp)
    apply(case_tac j,simp)
    apply clarify
    apply(erule_tac x=i and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE)
    apply(case_tac "clist!i",simp,simp)
   apply clarify
   apply(simp add:compat_label_def)
   apply(rule allI,rule impI)
   apply(erule_tac x=j in allE,erule impE, assumption)
   apply(erule disjE)
    apply clarify
    apply(rule_tac x=i in exI,simp)
    apply(rule conjI)
     apply(erule_tac x=i in allE)
     apply(case_tac j,simp)
      apply(erule_tac x=i and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE)
      apply(case_tac "clist!i",simp,simp)
     apply(erule_tac x=i and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE)
     apply(case_tac "clist!i",simp,simp)
    apply clarify
    apply(erule_tac x=l and P="\<lambda>j. ?H j \<longrightarrow> ?I j \<longrightarrow> ?J j" in allE)
    apply(erule_tac x=l and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE)
    apply(case_tac "clist!l",simp,simp)
    apply(erule_tac x=l in allE,simp)
   apply(rule disjI2)
   apply clarify
   apply(rule tl_zero)
     apply(case_tac j,simp,simp)
     apply(rule tl_zero,force)   
      apply force
     apply(erule_tac x=i and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE,force)
    apply force
   apply(erule_tac x=i and P="\<lambda>j. ?H j \<longrightarrow> (length (?s j) = ?t)" in allE,force)
  apply clarify
  apply(erule_tac x=i in allE)
  apply(simp add:cp_def)
  apply(rule nth_tl_if)
    apply(simp add:conjoin_def)
    apply clarify
    apply(simp add:same_length_def)
    apply(erule_tac x=i in allE,simp)
   apply simp
  apply simp
 apply simp
apply clarify
apply(erule_tac c="(xs, s) # ys" in equalityCE)
 apply(simp add:par_cp_def)
apply simp
apply(erule_tac x="map (\<lambda>i. (fst i, s) # snd i) (zip xs clist)" in allE)
apply simp
apply clarify
apply(simp add:cp_def)
done

theorem one: "xs\<noteq>[] \<Longrightarrow> 
 par_cp xs s = {c. \<exists>clist. (length clist)=(length xs) \<and> 
               (\<forall>i<length clist. (clist!i) \<in> cp(xs!i) s) \<and> c \<propto> clist}"
apply(frule one_iff_aux)
apply(drule sym)
apply(erule iffD2)
apply clarify
apply(rule iffI)
 apply(erule aux_onlyif)
apply clarify
apply(force intro:aux_if)
done

end