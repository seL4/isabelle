(*  Title:      ZF/Induct/Primrec.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Primitive Recursive Functions: the inductive definition

Proof adopted from
Nora Szasz, 
A Machine Checked Proof that Ackermann's Function is not Primitive Recursive,
In: Huet & Plotkin, eds., Logical Environments (CUP, 1993), 317-338.

See also E. Mendelson, Introduction to Mathematical Logic.
(Van Nostrand, 1964), page 250, exercise 11.
*)

theory Primrec = Main:

constdefs
  SC      :: "i"
    "SC == \<lambda>l \<in> list(nat). list_case(0, %x xs. succ(x), l)"

  CONST   :: "i=>i"
    "CONST(k) == \<lambda>l \<in> list(nat). k"

  PROJ    :: "i=>i"
    "PROJ(i) == \<lambda>l \<in> list(nat). list_case(0, %x xs. x, drop(i,l))"

  COMP    :: "[i,i]=>i"
    "COMP(g,fs) == \<lambda>l \<in> list(nat). g ` List.map(%f. f`l, fs)"

  PREC    :: "[i,i]=>i"
		(*Note that g is applied first to PREC(f,g)`y and then to y!*)
  "PREC(f,g) == 
     \<lambda>l \<in> list(nat). list_case(0, 
                      %x xs. rec(x, f`xs, %y r. g ` Cons(r, Cons(y, xs))), l)"

consts
  ACK     :: "i=>i"

primrec
  ACK_0:     "ACK(0) = SC"
  ACK_succ:  "ACK(succ(i)) = PREC (CONST (ACK(i) ` [1]),
		 	 	   COMP(ACK(i), [PROJ(0)]))"

syntax
  ack     :: "[i,i]=>i"  

translations
  "ack(x,y)"  == "ACK(x) ` [y]"



(** Useful special cases of evaluation ***)

lemma SC: "[| x \<in> nat;  l \<in> list(nat) |] ==> SC ` (Cons(x,l)) = succ(x)"
by (simp add: SC_def) 

lemma CONST: "l \<in> list(nat) ==> CONST(k) ` l = k"
by (simp add: CONST_def) 

lemma PROJ_0: "[| x \<in> nat;  l \<in> list(nat) |] ==> PROJ(0) ` (Cons(x,l)) = x"
by (simp add: PROJ_def) 

lemma COMP_1: "l \<in> list(nat) ==> COMP(g,[f]) ` l = g` [f`l]"
by (simp add: COMP_def) 

lemma PREC_0: "l \<in> list(nat) ==> PREC(f,g) ` (Cons(0,l)) = f`l"
by (simp add: PREC_def) 

lemma PREC_succ: 
    "[| x \<in> nat;  l \<in> list(nat) |] 
     ==> PREC(f,g) ` (Cons(succ(x),l)) = 
         g ` Cons(PREC(f,g)`(Cons(x,l)), Cons(x,l))"
by (simp add: PREC_def) 


consts
    prim_rec :: "i"

inductive
  domains "prim_rec" <= "list(nat)->nat"
  intros
    "SC \<in> prim_rec"
    "k \<in> nat ==> CONST(k) \<in> prim_rec"
    "i \<in> nat ==> PROJ(i) \<in> prim_rec"
    "[| g \<in> prim_rec; fs\<in>list(prim_rec) |] ==> COMP(g,fs): prim_rec"
    "[| f \<in> prim_rec; g \<in> prim_rec |] ==> PREC(f,g): prim_rec"
  monos        list_mono
  con_defs     SC_def CONST_def PROJ_def COMP_def PREC_def
  type_intros  nat_typechecks list.intros
               lam_type list_case_type drop_type List.map_type   
               apply_type rec_type


(*** Inductive definition of the PR functions ***)

(* c \<in> prim_rec ==> c \<in> list(nat) -> nat *)
lemmas prim_rec_into_fun [TC] = subsetD [OF prim_rec.dom_subset]
lemmas [TC] = apply_type [OF prim_rec_into_fun]

declare prim_rec.intros [TC]
declare nat_into_Ord [TC]
declare rec_type [TC]

lemma ACK_in_prim_rec [TC]: "i \<in> nat ==> ACK(i): prim_rec"
by (induct_tac "i", simp_all)

lemma ack_type [TC]: "[| i \<in> nat;  j \<in> nat |] ==>  ack(i,j): nat"
by auto

(** Ackermann's function cases **)

(*PROPERTY A 1*)
lemma ack_0: "j \<in> nat ==> ack(0,j) = succ(j)"
by (simp add: SC)

(*PROPERTY A 2*)
lemma ack_succ_0: "ack(succ(i), 0) = ack(i,1)"
by (simp add: CONST PREC_0)

(*PROPERTY A 3*)
lemma ack_succ_succ:
 "[| i\<in>nat;  j\<in>nat |] ==> ack(succ(i), succ(j)) = ack(i, ack(succ(i), j))"
by (simp add: CONST PREC_succ COMP_1 PROJ_0)

declare ack_0 [simp] ack_succ_0 [simp] ack_succ_succ [simp] ack_type [simp]
declare ACK_0 [simp del] ACK_succ [simp del]


(*PROPERTY A 4*)
lemma lt_ack2 [rule_format]: "i \<in> nat ==> \<forall>j \<in> nat. j < ack(i,j)"
apply (induct_tac "i")
apply simp
apply (rule ballI)
apply (induct_tac "j")
apply (erule_tac [2] succ_leI [THEN lt_trans1])
apply (rule nat_0I [THEN nat_0_le, THEN lt_trans])
apply auto
done

(*PROPERTY A 5-, the single-step lemma*)
lemma ack_lt_ack_succ2: "[|i\<in>nat; j\<in>nat|] ==> ack(i,j) < ack(i, succ(j))"
by (induct_tac "i", simp_all add: lt_ack2)

(*PROPERTY A 5, monotonicity for < *)
lemma ack_lt_mono2: "[| j<k; i \<in> nat; k \<in> nat |] ==> ack(i,j) < ack(i,k)"
apply (frule lt_nat_in_nat , assumption)
apply (erule succ_lt_induct)
apply assumption
apply (rule_tac [2] lt_trans)
apply (auto intro: ack_lt_ack_succ2)
done

(*PROPERTY A 5', monotonicity for\<le>*)
lemma ack_le_mono2: "[|j\<le>k;  i\<in>nat;  k\<in>nat|] ==> ack(i,j) \<le> ack(i,k)"
apply (rule_tac f = "%j. ack (i,j) " in Ord_lt_mono_imp_le_mono)
apply (assumption | rule ack_lt_mono2 ack_type [THEN nat_into_Ord])+;
done

(*PROPERTY A 6*)
lemma ack2_le_ack1:
     "[| i\<in>nat;  j\<in>nat |] ==> ack(i, succ(j)) \<le> ack(succ(i), j)"
apply (induct_tac "j")
apply (simp_all)
apply (rule ack_le_mono2)
apply (rule lt_ack2 [THEN succ_leI, THEN le_trans])
apply auto
done

(*PROPERTY A 7-, the single-step lemma*)
lemma ack_lt_ack_succ1: "[| i \<in> nat; j \<in> nat |] ==> ack(i,j) < ack(succ(i),j)"
apply (rule ack_lt_mono2 [THEN lt_trans2])
apply (rule_tac [4] ack2_le_ack1)
apply auto
done

(*PROPERTY A 7, monotonicity for < *)
lemma ack_lt_mono1: "[| i<j; j \<in> nat; k \<in> nat |] ==> ack(i,k) < ack(j,k)"
apply (frule lt_nat_in_nat , assumption)
apply (erule succ_lt_induct)
apply assumption
apply (rule_tac [2] lt_trans)
apply (auto intro: ack_lt_ack_succ1)
done

(*PROPERTY A 7', monotonicity for\<le>*)
lemma ack_le_mono1: "[| i\<le>j; j \<in> nat; k \<in> nat |] ==> ack(i,k) \<le> ack(j,k)"
apply (rule_tac f = "%j. ack (j,k) " in Ord_lt_mono_imp_le_mono)
apply (assumption | rule ack_lt_mono1 ack_type [THEN nat_into_Ord])+;
done

(*PROPERTY A 8*)
lemma ack_1: "j \<in> nat ==> ack(1,j) = succ(succ(j))"
by (induct_tac "j", simp_all)

(*PROPERTY A 9*)
lemma ack_2: "j \<in> nat ==> ack(succ(1),j) = succ(succ(succ(j#+j)))"
by (induct_tac "j", simp_all add: ack_1)

(*PROPERTY A 10*)
lemma ack_nest_bound:
     "[| i1 \<in> nat; i2 \<in> nat; j \<in> nat |] 
      ==> ack(i1, ack(i2,j)) < ack(succ(succ(i1#+i2)), j)"
apply (rule lt_trans2 [OF _ ack2_le_ack1]) 
apply simp
apply (rule add_le_self [THEN ack_le_mono1, THEN lt_trans1])
apply auto
apply (force intro: add_le_self2 [THEN ack_lt_mono1, THEN ack_lt_mono2])
done

(*PROPERTY A 11*)
lemma ack_add_bound:
     "[| i1 \<in> nat; i2 \<in> nat; j \<in> nat |] 
      ==> ack(i1,j) #+ ack(i2,j) < ack(succ(succ(succ(succ(i1#+i2)))), j)"
apply (rule_tac j = "ack (succ (1) , ack (i1 #+ i2, j))" in lt_trans)
apply (simp add: ack_2)
apply (rule_tac [2] ack_nest_bound [THEN lt_trans2])
apply (rule add_le_mono [THEN leI, THEN leI])
apply (auto intro: add_le_self add_le_self2 ack_le_mono1)
done

(*PROPERTY A 12.  Article uses existential quantifier but the ALF proof
  used k#+4.  Quantified version must be nested \<exists>k'. \<forall>i,j... *)
lemma ack_add_bound2:
     "[| i < ack(k,j);  j \<in> nat;  k \<in> nat |] 
      ==> i#+j < ack(succ(succ(succ(succ(k)))), j)"
apply (rule_tac j = "ack (k,j) #+ ack (0,j) " in lt_trans)
apply (rule_tac [2] ack_add_bound [THEN lt_trans2])
apply (rule add_lt_mono)
apply auto
done

(*** MAIN RESULT ***)

declare list_add_type [simp]

lemma SC_case: "l \<in> list(nat) ==> SC ` l < ack(1, list_add(l))"
apply (unfold SC_def)
apply (erule list.cases)
apply (simp add: succ_iff)
apply (simp add: ack_1 add_le_self)
done

(*PROPERTY A 4'? Extra lemma needed for CONST case, constant functions*)
lemma lt_ack1: "[| i \<in> nat; j \<in> nat |] ==> i < ack(i,j)"
apply (induct_tac "i")
apply (simp add: nat_0_le)
apply (erule lt_trans1 [OF succ_leI ack_lt_ack_succ1])
apply auto
done

lemma CONST_case: 
    "[| l \<in> list(nat);  k \<in> nat |] ==> CONST(k) ` l < ack(k, list_add(l))"
by (simp add: CONST_def lt_ack1)

lemma PROJ_case [rule_format]: 
    "l \<in> list(nat) ==> \<forall>i \<in> nat. PROJ(i) ` l < ack(0, list_add(l))"
apply (unfold PROJ_def)
apply simp
apply (erule list.induct)
apply (simp add: nat_0_le)
apply simp
apply (rule ballI)
apply (erule_tac n = "x" in natE)
apply (simp add: add_le_self)
apply simp
apply (erule bspec [THEN lt_trans2])
apply (rule_tac [2] add_le_self2 [THEN succ_leI])
apply auto
done

(** COMP case **)

lemma COMP_map_lemma:
     "fs \<in> list({f \<in> prim_rec .                                  
                   \<exists>kf \<in> nat. \<forall>l \<in> list(nat). f`l < ack(kf, list_add(l))})
      ==> \<exists>k \<in> nat. \<forall>l \<in> list(nat).                           
                 list_add(map(%f. f ` l, fs)) < ack(k, list_add(l))"
apply (erule list.induct)
apply (rule_tac x = "0" in bexI)
apply (simp_all add: lt_ack1 nat_0_le)
apply clarify
apply (rule ballI [THEN bexI])
apply (rule add_lt_mono [THEN lt_trans])
apply (rule_tac [5] ack_add_bound)
apply blast
apply auto
done

lemma COMP_case: 
 "[| kg\<in>nat;                                  
     \<forall>l \<in> list(nat). g`l < ack(kg, list_add(l));           
     fs \<in> list({f \<in> prim_rec .                                
                 \<exists>kf \<in> nat. \<forall>l \<in> list(nat).                 
                        f`l < ack(kf, list_add(l))}) |]
   ==> \<exists>k \<in> nat. \<forall>l \<in> list(nat). COMP(g,fs)`l < ack(k, list_add(l))"
apply (simp add: COMP_def)
apply (frule list_CollectD)
apply (erule COMP_map_lemma [THEN bexE])
apply (rule ballI [THEN bexI])
apply (erule bspec [THEN lt_trans])
apply (rule_tac [2] lt_trans)
apply (rule_tac [3] ack_nest_bound)
apply (erule_tac [2] bspec [THEN ack_lt_mono2])
apply auto
done

(** PREC case **)

lemma PREC_case_lemma: 
 "[| \<forall>l \<in> list(nat). f`l #+ list_add(l) < ack(kf, list_add(l));  
     \<forall>l \<in> list(nat). g`l #+ list_add(l) < ack(kg, list_add(l));  
     f \<in> prim_rec;  kf\<in>nat;                                        
     g \<in> prim_rec;  kg\<in>nat;                                        
     l \<in> list(nat) |]
  ==> PREC(f,g)`l #+ list_add(l) < ack(succ(kf#+kg), list_add(l))"
apply (unfold PREC_def)
apply (erule list.cases) 
apply (simp add: lt_trans [OF nat_le_refl lt_ack2])
apply simp
apply (erule ssubst) (*get rid of the needless assumption*)
apply (induct_tac "a")
apply simp_all 
(*base case*)
apply (rule lt_trans, erule bspec, assumption); 
apply (simp add: add_le_self [THEN ack_lt_mono1]) 
(*ind step*)
apply (rule succ_leI [THEN lt_trans1])
apply (rule_tac j = "g ` ?ll #+ ?mm" in lt_trans1)
apply (erule_tac [2] bspec)
apply (rule nat_le_refl [THEN add_le_mono])
apply typecheck
apply (simp add: add_le_self2)
(*final part of the simplification*)
apply simp
apply (rule add_le_self2 [THEN ack_le_mono1, THEN lt_trans1])
apply (erule_tac [4] ack_lt_mono2)
apply auto
done

lemma PREC_case:
     "[| f \<in> prim_rec;  kf\<in>nat;                                
         g \<in> prim_rec;  kg\<in>nat;                                
         \<forall>l \<in> list(nat). f`l < ack(kf, list_add(l));         
         \<forall>l \<in> list(nat). g`l < ack(kg, list_add(l)) |]
      ==> \<exists>k \<in> nat. \<forall>l \<in> list(nat). PREC(f,g)`l< ack(k, list_add(l))"
apply (rule ballI [THEN bexI])
apply (rule lt_trans1 [OF add_le_self PREC_case_lemma])
apply typecheck
apply (blast intro: ack_add_bound2 list_add_type)+ 
done

lemma ack_bounds_prim_rec:
     "f \<in> prim_rec ==> \<exists>k \<in> nat. \<forall>l \<in> list(nat). f`l < ack(k, list_add(l))"
apply (erule prim_rec.induct)
apply (auto intro: SC_case CONST_case PROJ_case COMP_case PREC_case)
done

lemma ack_not_prim_rec:
     "~ (\<lambda>l \<in> list(nat). list_case(0, %x xs. ack(x,x), l)) \<in> prim_rec"
apply (rule notI)
apply (drule ack_bounds_prim_rec)
apply force
done

end



