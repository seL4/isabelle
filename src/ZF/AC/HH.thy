(*  Title:      ZF/AC/HH.thy
    ID:         $Id$
    Author:     Krzysztof Grabczewski

Some properties of the recursive definition of HH used in the proofs of
  AC17 ==> AC1
  AC1 ==> WO2
  AC15 ==> WO6
*)

theory HH = AC_Equiv + Hartog:

constdefs
 
  HH :: "[i, i, i] => i"
    "HH(f,x,a) == transrec(a, %b r. let z = x - (\<Union>c \<in> b. r`c)
                                    in  if f`z \<in> Pow(z)-{0} then f`z else {x})"


(* ********************************************************************** *)
(* Lemmas useful in each of the three proofs                              *)
(* ********************************************************************** *)

lemma HH_def_satisfies_eq:
     "HH(f,x,a) = (let z = x - (\<Union>b \<in> a. HH(f,x,b))   
                   in  if f`z \<in> Pow(z)-{0} then f`z else {x})"
by (rule HH_def [THEN def_transrec, THEN trans], simp)

lemma HH_values: "HH(f,x,a) \<in> Pow(x)-{0} | HH(f,x,a)={x}"
apply (rule HH_def_satisfies_eq [THEN ssubst])
apply (simp add: Let_def Diff_subset [THEN PowI], fast)
done

lemma subset_imp_Diff_eq:
     "B \<subseteq> A ==> X-(\<Union>a \<in> A. P(a)) = X-(\<Union>a \<in> A-B. P(a))-(\<Union>b \<in> B. P(b))"
by fast

lemma Ord_DiffE: "[| c \<in> a-b; b<a |] ==> c=b | b<c & c<a"
apply (erule ltE)
apply (drule Ord_linear [of _ c])
apply (fast elim: Ord_in_Ord)
apply (fast intro!: ltI intro: Ord_in_Ord)
done

lemma Diff_UN_eq_self:
     "(!!y. y \<in> A ==> P(y) = {x}) ==> x - (\<Union>y \<in> A. P(y)) = x" 
apply (simp, fast elim!: mem_irrefl)
done

lemma HH_eq: "x - (\<Union>b \<in> a. HH(f,x,b)) = x - (\<Union>b \<in> a1. HH(f,x,b))   
              ==> HH(f,x,a) = HH(f,x,a1)"
apply (subst HH_def_satisfies_eq) 
apply (rule HH_def_satisfies_eq [THEN trans], simp) 
done

lemma HH_is_x_gt_too: "[| HH(f,x,b)={x}; b<a |] ==> HH(f,x,a)={x}"
apply (rule_tac P = "b<a" in impE)
prefer 2 apply assumption+
apply (erule lt_Ord2 [THEN trans_induct])
apply (rule impI)
apply (rule HH_eq [THEN trans])
prefer 2 apply assumption+
apply (rule leI [THEN le_imp_subset, THEN subset_imp_Diff_eq, THEN ssubst], 
       assumption)
apply (rule_tac t = "%z. z-?X" in subst_context)
apply (rule Diff_UN_eq_self)
apply (drule Ord_DiffE, assumption) 
apply (fast elim: ltE, auto) 
done

lemma HH_subset_x_lt_too:
     "[| HH(f,x,a) \<in> Pow(x)-{0}; b<a |] ==> HH(f,x,b) \<in> Pow(x)-{0}"
apply (rule HH_values [THEN disjE], assumption)
apply (drule HH_is_x_gt_too, assumption)
apply (drule subst, assumption)
apply (fast elim!: mem_irrefl)
done

lemma HH_subset_x_imp_subset_Diff_UN:
    "HH(f,x,a) \<in> Pow(x)-{0} ==> HH(f,x,a) \<in> Pow(x - (\<Union>b \<in> a. HH(f,x,b)))-{0}"
apply (drule HH_def_satisfies_eq [THEN subst])
apply (rule HH_def_satisfies_eq [THEN ssubst])
apply (simp add: Let_def Diff_subset [THEN PowI])
apply (drule split_if [THEN iffD1])
apply (fast elim!: mem_irrefl)
done

lemma HH_eq_arg_lt:
     "[| HH(f,x,v)=HH(f,x,w); HH(f,x,v) \<in> Pow(x)-{0}; v \<in> w |] ==> P"
apply (frule_tac P = "%y. y \<in> Pow (x) -{0}" in subst, assumption)
apply (drule_tac a = "w" in HH_subset_x_imp_subset_Diff_UN)
apply (drule subst_elem, assumption)
apply (fast intro!: singleton_iff [THEN iffD2] equals0I)
done

lemma HH_eq_imp_arg_eq:
  "[| HH(f,x,v)=HH(f,x,w); HH(f,x,w) \<in> Pow(x)-{0}; Ord(v); Ord(w) |] ==> v=w"
apply (rule_tac j = "w" in Ord_linear_lt)
apply (simp_all (no_asm_simp))
 apply (drule subst_elem, assumption) 
 apply (blast dest: ltD HH_eq_arg_lt)
apply (blast dest: HH_eq_arg_lt [OF sym] ltD) 
done

lemma HH_subset_x_imp_lepoll: 
     "[| HH(f, x, i) \<in> Pow(x)-{0}; Ord(i) |] ==> i lepoll Pow(x)-{0}"
apply (unfold lepoll_def inj_def)
apply (rule_tac x = "\<lambda>j \<in> i. HH (f, x, j) " in exI)
apply (simp (no_asm_simp))
apply (fast del: DiffE
	    elim!: HH_eq_imp_arg_eq Ord_in_Ord HH_subset_x_lt_too 
            intro!: lam_type ballI ltI intro: bexI)
done

lemma HH_Hartog_is_x: "HH(f, x, Hartog(Pow(x)-{0})) = {x}"
apply (rule HH_values [THEN disjE])
prefer 2 apply assumption 
apply (fast del: DiffE
            intro!: Ord_Hartog 
	    dest!: HH_subset_x_imp_lepoll 
            elim!: Hartog_lepoll_selfE)
done

lemma HH_Least_eq_x: "HH(f, x, LEAST i. HH(f, x, i) = {x}) = {x}"
by (fast intro!: Ord_Hartog HH_Hartog_is_x LeastI)

lemma less_Least_subset_x:
     "a \<in> (LEAST i. HH(f,x,i)={x}) ==> HH(f,x,a) \<in> Pow(x)-{0}"
apply (rule HH_values [THEN disjE], assumption)
apply (rule less_LeastE)
apply (erule_tac [2] ltI [OF _ Ord_Least], assumption)
done

(* ********************************************************************** *)
(* Lemmas used in the proofs of AC1 ==> WO2 and AC17 ==> AC1              *)
(* ********************************************************************** *)

lemma lam_Least_HH_inj_Pow: 
        "(\<lambda>a \<in> (LEAST i. HH(f,x,i)={x}). HH(f,x,a))   
         \<in> inj(LEAST i. HH(f,x,i)={x}, Pow(x)-{0})"
apply (unfold inj_def, simp)
apply (fast intro!: lam_type dest: less_Least_subset_x 
            elim!: HH_eq_imp_arg_eq Ord_Least [THEN Ord_in_Ord])
done

lemma lam_Least_HH_inj:
     "\<forall>a \<in> (LEAST i. HH(f,x,i)={x}). \<exists>z \<in> x. HH(f,x,a) = {z}   
      ==> (\<lambda>a \<in> (LEAST i. HH(f,x,i)={x}). HH(f,x,a))   
          \<in> inj(LEAST i. HH(f,x,i)={x}, {{y}. y \<in> x})"
by (rule lam_Least_HH_inj_Pow [THEN inj_strengthen_type], simp)

lemma lam_surj_sing: 
        "[| x - (\<Union>a \<in> A. F(a)) = 0;  \<forall>a \<in> A. \<exists>z \<in> x. F(a) = {z} |]   
         ==> (\<lambda>a \<in> A. F(a)) \<in> surj(A, {{y}. y \<in> x})"
apply (simp add: surj_def lam_type Diff_eq_0_iff)
apply (blast elim: equalityE) 
done

lemma not_emptyI2: "y \<in> Pow(x)-{0} ==> x \<noteq> 0"
by auto

lemma f_subset_imp_HH_subset:
     "f`(x - (\<Union>j \<in> i. HH(f,x,j))) \<in> Pow(x - (\<Union>j \<in> i. HH(f,x,j)))-{0}   
      ==> HH(f, x, i) \<in> Pow(x) - {0}"
apply (rule HH_def_satisfies_eq [THEN ssubst])
apply (simp add: Let_def Diff_subset [THEN PowI] not_emptyI2 [THEN if_P], fast)
done

lemma f_subsets_imp_UN_HH_eq_x:
     "\<forall>z \<in> Pow(x)-{0}. f`z \<in> Pow(z)-{0}
      ==> x - (\<Union>j \<in> (LEAST i. HH(f,x,i)={x}). HH(f,x,j)) = 0"
apply (case_tac "?P \<in> {0}", fast)
apply (drule Diff_subset [THEN PowI, THEN DiffI])
apply (drule bspec, assumption) 
apply (drule f_subset_imp_HH_subset) 
apply (blast dest!: subst_elem [OF _ HH_Least_eq_x [symmetric]] 
             elim!: mem_irrefl)
done

lemma HH_values2: "HH(f,x,i) = f`(x - (\<Union>j \<in> i. HH(f,x,j))) | HH(f,x,i)={x}"
apply (rule HH_def_satisfies_eq [THEN ssubst])
apply (simp add: Let_def Diff_subset [THEN PowI])
done

lemma HH_subset_imp_eq:
     "HH(f,x,i): Pow(x)-{0} ==> HH(f,x,i)=f`(x - (\<Union>j \<in> i. HH(f,x,j)))"
apply (rule HH_values2 [THEN disjE], assumption)
apply (fast elim!: equalityE mem_irrefl dest!: singleton_subsetD)
done

lemma f_sing_imp_HH_sing:
     "[| f \<in> (Pow(x)-{0}) -> {{z}. z \<in> x};   
         a \<in> (LEAST i. HH(f,x,i)={x}) |] ==> \<exists>z \<in> x. HH(f,x,a) = {z}"
apply (drule less_Least_subset_x)
apply (frule HH_subset_imp_eq)
apply (drule apply_type)
apply (rule Diff_subset [THEN PowI, THEN DiffI])
apply (fast dest!: HH_subset_x_imp_subset_Diff_UN [THEN not_emptyI2], force) 
done

lemma f_sing_lam_bij: 
     "[| x - (\<Union>j \<in> (LEAST i. HH(f,x,i)={x}). HH(f,x,j)) = 0;   
         f \<in> (Pow(x)-{0}) -> {{z}. z \<in> x} |]   
      ==> (\<lambda>a \<in> (LEAST i. HH(f,x,i)={x}). HH(f,x,a))   
          \<in> bij(LEAST i. HH(f,x,i)={x}, {{y}. y \<in> x})"
apply (unfold bij_def)
apply (fast intro!: lam_Least_HH_inj lam_surj_sing f_sing_imp_HH_sing)
done

lemma lam_singI:
     "f \<in> (\<Pi>X \<in> Pow(x)-{0}. F(X))   
      ==> (\<lambda>X \<in> Pow(x)-{0}. {f`X}) \<in> (\<Pi>X \<in> Pow(x)-{0}. {{z}. z \<in> F(X)})"
by (fast del: DiffI DiffE
	    intro!: lam_type singleton_eq_iff [THEN iffD2] dest: apply_type)

(*FIXME: both uses have the form ...[THEN bij_converse_bij], so 
  simplification is needed!*)
lemmas bij_Least_HH_x =  
    comp_bij [OF f_sing_lam_bij [OF _ lam_singI] 
              lam_sing_bij [THEN bij_converse_bij], standard]


(* ********************************************************************** *)
(*                     The proof of AC1 ==> WO2                           *)
(* ********************************************************************** *)

(*Establishing the existence of a bijection, namely
converse
 (converse(\<lambda>x\<in>x. {x}) O
  Lambda
   (LEAST i. HH(\<lambda>X\<in>Pow(x) - {0}. {f ` X}, x, i) = {x},
    HH(\<lambda>X\<in>Pow(x) - {0}. {f ` X}, x)))
Perhaps it could be simplified. *)

lemma bijection:
     "f \<in> (\<Pi>X \<in> Pow(x) - {0}. X) 
      ==> \<exists>g. g \<in> bij(x, LEAST i. HH(\<lambda>X \<in> Pow(x)-{0}. {f`X}, x, i) = {x})"
apply (rule exI) 
apply (rule bij_Least_HH_x [THEN bij_converse_bij])
apply (rule f_subsets_imp_UN_HH_eq_x)
apply (intro ballI apply_type) 
apply (fast intro: lam_type apply_type del: DiffE, assumption) 
apply (fast intro: Pi_weaken_type)
done

lemma AC1_WO2: "AC1 ==> WO2"
apply (unfold AC1_def WO2_def eqpoll_def)
apply (intro allI) 
apply (drule_tac x = "Pow(A) - {0}" in spec) 
apply (blast dest: bijection)
done

end


