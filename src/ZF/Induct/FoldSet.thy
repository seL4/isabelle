(*  Title:      ZF/Induct/FoldSet.thy
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory


A "fold" functional for finite sets.  For n non-negative we have
fold f e {x1,...,xn} = f x1 (... (f xn e)) where f is at
least left-commutative.  
*)

theory FoldSet = Main:

consts fold_set :: "[i, i, [i,i]=>i, i] => i"

inductive
  domains "fold_set(A, B, f,e)" <= "Fin(A)*B"
  intros
    emptyI: "e\<in>B ==> <0, e>\<in>fold_set(A, B, f,e)"
    consI:  "[| x\<in>A; x \<notin>C;  <C,y> : fold_set(A, B,f,e); f(x,y):B |]
		==>  <cons(x,C), f(x,y)>\<in>fold_set(A, B, f, e)"
  type_intros Fin.intros
  
constdefs
  
  fold :: "[i, [i,i]=>i, i, i] => i"  ("fold[_]'(_,_,_')")
   "fold[B](f,e, A) == THE x. <A, x>\<in>fold_set(A, B, f,e)"

   setsum :: "[i=>i, i] => i"
   "setsum(g, C) == if Finite(C) then
                     fold[int](%x y. g(x) $+ y, #0, C) else #0"

(** foldSet **)

inductive_cases empty_fold_setE: "<0, x> : fold_set(A, B, f,e)"
inductive_cases cons_fold_setE: "<cons(x,C), y> : fold_set(A, B, f,e)"

(* add-hoc lemmas *)                                                

lemma cons_lemma1: "[| x\<notin>C; x\<notin>B |] ==> cons(x,B)=cons(x,C) <-> B = C"
by (auto elim: equalityE)

lemma cons_lemma2: "[| cons(x, B)=cons(y, C); x\<noteq>y; x\<notin>B; y\<notin>C |]  
    ==>  B - {y} = C-{x} & x\<in>C & y\<in>B"
apply (auto elim: equalityE)
done

(* fold_set monotonicity *)
lemma fold_set_mono_lemma:
     "<C, x> : fold_set(A, B, f, e)  
      ==> ALL D. A<=D --> <C, x> : fold_set(D, B, f, e)"
apply (erule fold_set.induct)
apply (auto intro: fold_set.intros)
done

lemma fold_set_mono: " C<=A ==> fold_set(C, B, f, e) <= fold_set(A, B, f, e)"
apply clarify
apply (frule fold_set.dom_subset [THEN subsetD], clarify)
apply (auto dest: fold_set_mono_lemma)
done

lemma fold_set_lemma:
     "<C, x>\<in>fold_set(A, B, f, e) ==> <C, x>\<in>fold_set(C, B, f, e) & C<=A"
apply (erule fold_set.induct)
apply (auto intro!: fold_set.intros intro: fold_set_mono [THEN subsetD])
done

(* Proving that fold_set is deterministic *)
lemma Diff1_fold_set:
     "[| <C-{x},y> : fold_set(A, B, f,e);  x\<in>C; x\<in>A; f(x, y):B |]  
      ==> <C, f(x, y)> : fold_set(A, B, f, e)"
apply (frule fold_set.dom_subset [THEN subsetD])
apply (erule cons_Diff [THEN subst], rule fold_set.intros, auto)
done


locale fold_typing =
 fixes A and B and e and f
 assumes ftype [intro,simp]:  "[|x \<in> A; y \<in> B|] ==> f(x,y) \<in> B"
     and etype [intro,simp]:  "e \<in> B"
     and fcomm:  "[|x \<in> A; y \<in> A; z \<in> B|] ==> f(x, f(y, z))=f(y, f(x, z))"


lemma (in fold_typing) Fin_imp_fold_set:
     "C\<in>Fin(A) ==> (EX x. <C, x> : fold_set(A, B, f,e))"
apply (erule Fin_induct)
apply (auto dest: fold_set.dom_subset [THEN subsetD] 
            intro: fold_set.intros etype ftype)
done

lemma Diff_sing_imp:
     "[|C - {b} = D - {a}; a \<noteq> b; b \<in> C|] ==> C = cons(b,D) - {a}"
by (blast elim: equalityE)

lemma (in fold_typing) fold_set_determ_lemma [rule_format]: 
"n\<in>nat
 ==> ALL C. |C|<n -->  
   (ALL x. <C, x> : fold_set(A, B, f,e)--> 
           (ALL y. <C, y> : fold_set(A, B, f,e) --> y=x))"
apply (erule nat_induct)
 apply (auto simp add: le_iff)
apply (erule fold_set.cases)
 apply (force elim!: empty_fold_setE)
apply (erule fold_set.cases)
 apply (force elim!: empty_fold_setE, clarify)
(*force simplification of "|C| < |cons(...)|"*)
apply (frule_tac a = Ca in fold_set.dom_subset [THEN subsetD, THEN SigmaD1])
apply (frule_tac a = Cb in fold_set.dom_subset [THEN subsetD, THEN SigmaD1])
apply (simp add: Fin_into_Finite [THEN Finite_imp_cardinal_cons])
apply (case_tac "x=xb", auto) 
apply (simp add: cons_lemma1, blast)
txt{*case @{term "x\<noteq>xb"}*}
apply (drule cons_lemma2, safe)
apply (frule Diff_sing_imp, assumption+) 
txt{** LEVEL 17*}
apply (subgoal_tac "|Ca| le |Cb|")
 prefer 2
 apply (rule succ_le_imp_le)
 apply (simp add: Fin_into_Finite Finite_imp_succ_cardinal_Diff 
                  Fin_into_Finite [THEN Finite_imp_cardinal_cons])
apply (rule_tac C1 = "Ca-{xb}" in Fin_imp_fold_set [THEN exE])
 apply (blast intro: Diff_subset [THEN Fin_subset])
txt{** LEVEL 24 **}
apply (frule Diff1_fold_set, blast, blast)
apply (blast dest!: ftype fold_set.dom_subset [THEN subsetD])
apply (subgoal_tac "ya = f(xb,xa) ")
 prefer 2 apply (blast del: equalityCE)
apply (subgoal_tac "<Cb-{x}, xa> : fold_set(A,B,f,e)")
 prefer 2 apply simp
apply (subgoal_tac "yb = f (x, xa) ")
 apply (drule_tac [2] C = Cb in Diff1_fold_set, simp_all)
  apply (blast intro: fcomm dest!: fold_set.dom_subset [THEN subsetD])
 apply (blast intro: ftype dest!: fold_set.dom_subset [THEN subsetD], blast) 
done

lemma (in fold_typing) fold_set_determ: 
     "[| <C, x>\<in>fold_set(A, B, f, e);  
         <C, y>\<in>fold_set(A, B, f, e)|] ==> y=x"
apply (frule fold_set.dom_subset [THEN subsetD], clarify)
apply (drule Fin_into_Finite)
apply (unfold Finite_def, clarify)
apply (rule_tac n = "succ (n)" in fold_set_determ_lemma) 
apply (auto intro: eqpoll_imp_lepoll [THEN lepoll_cardinal_le])
done

(** The fold function **)

lemma (in fold_typing) fold_equality: 
     "<C,y> : fold_set(A,B,f,e) ==> fold[B](f,e,C) = y"
apply (unfold fold_def)
apply (frule fold_set.dom_subset [THEN subsetD], clarify)
apply (rule the_equality)
 apply (rule_tac [2] A=C in fold_typing.fold_set_determ)
apply (force dest: fold_set_lemma)
apply (auto dest: fold_set_lemma)
apply (simp add: fold_typing_def, auto) 
apply (auto dest: fold_set_lemma intro: ftype etype fcomm)
done

lemma fold_0 [simp]: "e : B ==> fold[B](f,e,0) = e"
apply (unfold fold_def)
apply (blast elim!: empty_fold_setE intro: fold_set.intros)
done

text{*This result is the right-to-left direction of the subsequent result*}
lemma (in fold_typing) fold_set_imp_cons: 
     "[| <C, y> : fold_set(C, B, f, e); C : Fin(A); c : A; c\<notin>C |]
      ==> <cons(c, C), f(c,y)> : fold_set(cons(c, C), B, f, e)"
apply (frule FinD [THEN fold_set_mono, THEN subsetD])
 apply assumption
apply (frule fold_set.dom_subset [of A, THEN subsetD])
apply (blast intro!: fold_set.consI intro: fold_set_mono [THEN subsetD])
done

lemma (in fold_typing) fold_cons_lemma [rule_format]: 
"[| C : Fin(A); c : A; c\<notin>C |]   
     ==> <cons(c, C), v> : fold_set(cons(c, C), B, f, e) <->   
         (EX y. <C, y> : fold_set(C, B, f, e) & v = f(c, y))"
apply auto
 prefer 2 apply (blast intro: fold_set_imp_cons) 
 apply (frule_tac Fin.consI [of c, THEN FinD, THEN fold_set_mono, THEN subsetD], assumption+)
apply (frule_tac fold_set.dom_subset [of A, THEN subsetD])
apply (drule FinD) 
apply (rule_tac A1 = "cons(c,C)" and f1=f and B1=B and C1=C and e1=e in fold_typing.Fin_imp_fold_set [THEN exE])
apply (blast intro: fold_typing.intro ftype etype fcomm) 
apply (blast intro: Fin_subset [of _ "cons(c,C)"] Finite_into_Fin 
             dest: Fin_into_Finite)  
apply (rule_tac x = x in exI)
apply (auto intro: fold_set.intros)
apply (drule_tac fold_set_lemma [of C], blast)
apply (blast intro!: fold_set.consI
             intro: fold_set_determ fold_set_mono [THEN subsetD] 
             dest: fold_set.dom_subset [THEN subsetD]) 
done

lemma (in fold_typing) fold_cons: 
     "[| C\<in>Fin(A); c\<in>A; c\<notin>C|] 
      ==> fold[B](f, e, cons(c, C)) = f(c, fold[B](f, e, C))"
apply (unfold fold_def)
apply (simp add: fold_cons_lemma)
apply (rule the_equality, auto) 
 apply (subgoal_tac [2] "\<langle>C, y\<rangle> \<in> fold_set(A, B, f, e)")
  apply (drule Fin_imp_fold_set)
apply (auto dest: fold_set_lemma  simp add: fold_def [symmetric] fold_equality) 
apply (blast intro: fold_set_mono [THEN subsetD] dest!: FinD) 
done

lemma (in fold_typing) fold_type [simp,TC]: 
     "C\<in>Fin(A) ==> fold[B](f,e,C):B"
apply (erule Fin_induct)
apply (simp_all add: fold_cons ftype etype)
done

lemma (in fold_typing) fold_commute [rule_format]: 
     "[| C\<in>Fin(A); c\<in>A |]  
      ==> (\<forall>y\<in>B. f(c, fold[B](f, y, C)) = fold[B](f, f(c, y), C))"
apply (erule Fin_induct)
apply (simp_all add: fold_typing.fold_cons [of A B _ f] 
                     fold_typing.fold_type [of A B _ f] 
                     fold_typing_def fcomm)
done

lemma (in fold_typing) fold_nest_Un_Int: 
     "[| C\<in>Fin(A); D\<in>Fin(A) |]
      ==> fold[B](f, fold[B](f, e, D), C) =
          fold[B](f, fold[B](f, e, (C Int D)), C Un D)"
apply (erule Fin_induct, auto)
apply (simp add: Un_cons Int_cons_left fold_type fold_commute
                 fold_typing.fold_cons [of A _ _ f] 
                 fold_typing_def fcomm cons_absorb)
done

lemma (in fold_typing) fold_nest_Un_disjoint:
     "[| C\<in>Fin(A); D\<in>Fin(A); C Int D = 0 |]  
      ==> fold[B](f,e,C Un D) =  fold[B](f, fold[B](f,e,D), C)"
by (simp add: fold_nest_Un_Int)

lemma Finite_cons_lemma: "Finite(C) ==> C\<in>Fin(cons(c, C))"
apply (drule Finite_into_Fin)
apply (blast intro: Fin_mono [THEN subsetD])
done

subsection{*The Operator @{term setsum}*}

lemma setsum_0 [simp]: "setsum(g, 0) = #0"
by (simp add: setsum_def)

lemma setsum_cons [simp]: 
     "Finite(C) ==> 
      setsum(g, cons(c,C)) = 
        (if c : C then setsum(g,C) else g(c) $+ setsum(g,C))"
apply (auto simp add: setsum_def Finite_cons cons_absorb)
apply (rule_tac A = "cons (c, C)" in fold_typing.fold_cons)
apply (auto intro: fold_typing.intro Finite_cons_lemma)
done

lemma setsum_K0: "setsum((%i. #0), C) = #0"
apply (case_tac "Finite (C) ")
 prefer 2 apply (simp add: setsum_def)
apply (erule Finite_induct, auto)
done

(*The reversed orientation looks more natural, but LOOPS as a simprule!*)
lemma setsum_Un_Int:
     "[| Finite(C); Finite(D) |]  
      ==> setsum(g, C Un D) $+ setsum(g, C Int D)  
        = setsum(g, C) $+ setsum(g, D)"
apply (erule Finite_induct)
apply (simp_all add: Int_cons_right cons_absorb Un_cons Int_commute Finite_Un
                     Int_lower1 [THEN subset_Finite]) 
done

lemma setsum_type [simp,TC]: "setsum(g, C):int"
apply (case_tac "Finite (C) ")
 prefer 2 apply (simp add: setsum_def)
apply (erule Finite_induct, auto)
done

lemma setsum_Un_disjoint:
     "[| Finite(C); Finite(D); C Int D = 0 |]  
      ==> setsum(g, C Un D) = setsum(g, C) $+ setsum(g,D)"
apply (subst setsum_Un_Int [symmetric])
apply (subgoal_tac [3] "Finite (C Un D) ")
apply (auto intro: Finite_Un)
done

lemma Finite_RepFun [rule_format (no_asm)]:
     "Finite(I) ==> (\<forall>i\<in>I. Finite(C(i))) --> Finite(RepFun(I, C))"
apply (erule Finite_induct, auto)
done

lemma setsum_UN_disjoint [rule_format (no_asm)]:
     "Finite(I)  
      ==> (\<forall>i\<in>I. Finite(C(i))) -->  
          (\<forall>i\<in>I. \<forall>j\<in>I. i\<noteq>j --> C(i) Int C(j) = 0) -->  
          setsum(f, \<Union>i\<in>I. C(i)) = setsum (%i. setsum(f, C(i)), I)"
apply (erule Finite_induct, auto)
apply (subgoal_tac "\<forall>i\<in>B. x \<noteq> i")
 prefer 2 apply blast
apply (subgoal_tac "C (x) Int (\<Union>i\<in>B. C (i)) = 0")
 prefer 2 apply blast
apply (subgoal_tac "Finite (\<Union>i\<in>B. C (i)) & Finite (C (x)) & Finite (B) ")
apply (simp (no_asm_simp) add: setsum_Un_disjoint)
apply (auto intro: Finite_Union Finite_RepFun)
done


lemma setsum_addf: "setsum(%x. f(x) $+ g(x),C) = setsum(f, C) $+ setsum(g, C)"
apply (case_tac "Finite (C) ")
 prefer 2 apply (simp add: setsum_def)
apply (erule Finite_induct, auto)
done


lemma fold_set_cong:
     "[| A=A'; B=B'; e=e'; (\<forall>x\<in>A'. \<forall>y\<in>B'. f(x,y) = f'(x,y)) |] 
      ==> fold_set(A,B,f,e) = fold_set(A',B',f',e')"
apply (simp add: fold_set_def)
apply (intro refl iff_refl lfp_cong Collect_cong disj_cong ex_cong, auto)
done

lemma fold_cong:
"[| B=B'; A=A'; e=e';   
    !!x y. [|x\<in>A'; y\<in>B'|] ==> f(x,y) = f'(x,y) |] ==>  
   fold[B](f,e,A) = fold[B'](f', e', A')"
apply (simp add: fold_def)
apply (subst fold_set_cong)
apply (rule_tac [5] refl, simp_all)
done

lemma setsum_cong:
 "[| A=B; !!x. x\<in>B ==> f(x) = g(x) |] ==>  
     setsum(f, A) = setsum(g, B)"
by (simp add: setsum_def cong add: fold_cong)

lemma setsum_Un:
     "[| Finite(A); Finite(B) |]  
      ==> setsum(f, A Un B) =  
          setsum(f, A) $+ setsum(f, B) $- setsum(f, A Int B)"
apply (subst setsum_Un_Int [symmetric], auto)
done


lemma setsum_zneg_or_0 [rule_format (no_asm)]:
     "Finite(A) ==> (\<forall>x\<in>A. g(x) $<= #0) --> setsum(g, A) $<= #0"
apply (erule Finite_induct)
apply (auto intro: zneg_or_0_add_zneg_or_0_imp_zneg_or_0)
done

lemma setsum_succD_lemma [rule_format]:
     "Finite(A)  
      ==> \<forall>n\<in>nat. setsum(f,A) = $# succ(n) --> (\<exists>a\<in>A. #0 $< f(a))"
apply (erule Finite_induct)
apply (auto simp del: int_of_0 int_of_succ simp add: not_zless_iff_zle int_of_0 [symmetric])
apply (subgoal_tac "setsum (f, B) $<= #0")
apply simp_all
prefer 2 apply (blast intro: setsum_zneg_or_0)
apply (subgoal_tac "$# 1 $<= f (x) $+ setsum (f, B) ")
apply (drule zdiff_zle_iff [THEN iffD2])
apply (subgoal_tac "$# 1 $<= $# 1 $- setsum (f,B) ")
apply (drule_tac x = "$# 1" in zle_trans)
apply (rule_tac [2] j = "#1" in zless_zle_trans, auto)
done

lemma setsum_succD:
     "[| setsum(f, A) = $# succ(n); n\<in>nat |]==> \<exists>a\<in>A. #0 $< f(a)"
apply (case_tac "Finite (A) ")
apply (blast intro: setsum_succD_lemma)
apply (unfold setsum_def)
apply (auto simp del: int_of_0 int_of_succ simp add: int_succ_int_1 [symmetric] int_of_0 [symmetric])
done

lemma g_zpos_imp_setsum_zpos [rule_format]:
     "Finite(A) ==> (\<forall>x\<in>A. #0 $<= g(x)) --> #0 $<= setsum(g, A)"
apply (erule Finite_induct)
apply (simp (no_asm))
apply (auto intro: zpos_add_zpos_imp_zpos)
done

lemma g_zpos_imp_setsum_zpos2 [rule_format]:
     "[| Finite(A); \<forall>x. #0 $<= g(x) |] ==> #0 $<= setsum(g, A)"
apply (erule Finite_induct)
apply (auto intro: zpos_add_zpos_imp_zpos)
done

lemma g_zspos_imp_setsum_zspos [rule_format]:
     "Finite(A)  
      ==> (\<forall>x\<in>A. #0 $< g(x)) --> A \<noteq> 0 --> (#0 $< setsum(g, A))"
apply (erule Finite_induct)
apply (auto intro: zspos_add_zspos_imp_zspos)
done

lemma setsum_Diff [rule_format]:
     "Finite(A) ==> \<forall>a. M(a) = #0 --> setsum(M, A) = setsum(M, A-{a})"
apply (erule Finite_induct) 
apply (simp_all add: Diff_cons_eq Finite_Diff) 
done

ML
{*
val fold_set_mono = thm "fold_set_mono";
val Diff1_fold_set = thm "Diff1_fold_set";
val Diff_sing_imp = thm "Diff_sing_imp";
val fold_0 = thm "fold_0";
val setsum_0 = thm "setsum_0";
val setsum_cons = thm "setsum_cons";
val setsum_K0 = thm "setsum_K0";
val setsum_Un_Int = thm "setsum_Un_Int";
val setsum_type = thm "setsum_type";
val setsum_Un_disjoint = thm "setsum_Un_disjoint";
val Finite_RepFun = thm "Finite_RepFun";
val setsum_UN_disjoint = thm "setsum_UN_disjoint";
val setsum_addf = thm "setsum_addf";
val fold_set_cong = thm "fold_set_cong";
val fold_cong = thm "fold_cong";
val setsum_cong = thm "setsum_cong";
val setsum_Un = thm "setsum_Un";
val setsum_zneg_or_0 = thm "setsum_zneg_or_0";
val setsum_succD = thm "setsum_succD";
val g_zpos_imp_setsum_zpos = thm "g_zpos_imp_setsum_zpos";
val g_zpos_imp_setsum_zpos2 = thm "g_zpos_imp_setsum_zpos2";
val g_zspos_imp_setsum_zspos = thm "g_zspos_imp_setsum_zspos";
val setsum_Diff = thm "setsum_Diff";
*}


end