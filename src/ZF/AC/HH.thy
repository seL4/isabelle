(*  Title:      ZF/AC/HH.thy
    Author:     Krzysztof Grabczewski

Some properties of the recursive definition of HH used in the proofs of
  AC17 \<Longrightarrow> AC1
  AC1 \<Longrightarrow> WO2
  AC15 \<Longrightarrow> WO6
*)

theory HH
imports AC_Equiv Hartog
begin

definition
  HH :: "[i, i, i] => i"  where
    "HH(f,x,a) \<equiv> transrec(a, %b r. let z = x - (\<Union>c \<in> b. r`c)
                                    in  if f`z \<in> Pow(z)-{0} then f`z else {x})"

subsection\<open>Lemmas useful in each of the three proofs\<close>

lemma HH_def_satisfies_eq:
     "HH(f,x,a) = (let z = x - (\<Union>b \<in> a. HH(f,x,b))   
                   in  if f`z \<in> Pow(z)-{0} then f`z else {x})"
by (rule HH_def [THEN def_transrec, THEN trans], simp)

lemma HH_values: "HH(f,x,a) \<in> Pow(x)-{0} | HH(f,x,a)={x}"
apply (rule HH_def_satisfies_eq [THEN ssubst])
apply (simp add: Let_def Diff_subset [THEN PowI], fast)
done

lemma subset_imp_Diff_eq:
     "B \<subseteq> A \<Longrightarrow> X-(\<Union>a \<in> A. P(a)) = X-(\<Union>a \<in> A-B. P(a))-(\<Union>b \<in> B. P(b))"
by fast

lemma Ord_DiffE: "\<lbrakk>c \<in> a-b; b<a\<rbrakk> \<Longrightarrow> c=b | b<c & c<a"
apply (erule ltE)
apply (drule Ord_linear [of _ c])
apply (fast elim: Ord_in_Ord)
apply (fast intro!: ltI intro: Ord_in_Ord)
done

lemma Diff_UN_eq_self: "(\<And>y. y\<in>A \<Longrightarrow> P(y) = {x}) \<Longrightarrow> x - (\<Union>y \<in> A. P(y)) = x" 
by (simp, fast elim!: mem_irrefl)

lemma HH_eq: "x - (\<Union>b \<in> a. HH(f,x,b)) = x - (\<Union>b \<in> a1. HH(f,x,b))   
              \<Longrightarrow> HH(f,x,a) = HH(f,x,a1)"
apply (subst HH_def_satisfies_eq [of _ _ a1]) 
apply (rule HH_def_satisfies_eq [THEN trans], simp) 
done

lemma HH_is_x_gt_too: "\<lbrakk>HH(f,x,b)={x}; b<a\<rbrakk> \<Longrightarrow> HH(f,x,a)={x}"
apply (rule_tac P = "b<a" in impE)
prefer 2 apply assumption+
apply (erule lt_Ord2 [THEN trans_induct])
apply (rule impI)
apply (rule HH_eq [THEN trans])
prefer 2 apply assumption+
apply (rule leI [THEN le_imp_subset, THEN subset_imp_Diff_eq, THEN ssubst], 
       assumption)
apply (rule_tac t = "%z. z-X" for X in subst_context)
apply (rule Diff_UN_eq_self)
apply (drule Ord_DiffE, assumption) 
apply (fast elim: ltE, auto) 
done

lemma HH_subset_x_lt_too:
     "\<lbrakk>HH(f,x,a) \<in> Pow(x)-{0}; b<a\<rbrakk> \<Longrightarrow> HH(f,x,b) \<in> Pow(x)-{0}"
apply (rule HH_values [THEN disjE], assumption)
apply (drule HH_is_x_gt_too, assumption)
apply (drule subst, assumption)
apply (fast elim!: mem_irrefl)
done

lemma HH_subset_x_imp_subset_Diff_UN:
    "HH(f,x,a) \<in> Pow(x)-{0} \<Longrightarrow> HH(f,x,a) \<in> Pow(x - (\<Union>b \<in> a. HH(f,x,b)))-{0}"
apply (drule HH_def_satisfies_eq [THEN subst])
apply (rule HH_def_satisfies_eq [THEN ssubst])
apply (simp add: Let_def Diff_subset [THEN PowI])
apply (drule split_if [THEN iffD1])
apply (fast elim!: mem_irrefl)
done

lemma HH_eq_arg_lt:
     "\<lbrakk>HH(f,x,v)=HH(f,x,w); HH(f,x,v) \<in> Pow(x)-{0}; v \<in> w\<rbrakk> \<Longrightarrow> P"
apply (frule_tac P = "%y. y \<in> Pow (x) -{0}" in subst, assumption)
apply (drule_tac a = w in HH_subset_x_imp_subset_Diff_UN)
apply (drule subst_elem, assumption)
apply (fast intro!: singleton_iff [THEN iffD2] equals0I)
done

lemma HH_eq_imp_arg_eq:
  "\<lbrakk>HH(f,x,v)=HH(f,x,w); HH(f,x,w) \<in> Pow(x)-{0}; Ord(v); Ord(w)\<rbrakk> \<Longrightarrow> v=w"
apply (rule_tac j = w in Ord_linear_lt)
apply (simp_all (no_asm_simp))
 apply (drule subst_elem, assumption) 
 apply (blast dest: ltD HH_eq_arg_lt)
apply (blast dest: HH_eq_arg_lt [OF sym] ltD) 
done

lemma HH_subset_x_imp_lepoll: 
     "\<lbrakk>HH(f, x, i) \<in> Pow(x)-{0}; Ord(i)\<rbrakk> \<Longrightarrow> i \<lesssim> Pow(x)-{0}"
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

lemma HH_Least_eq_x: "HH(f, x, \<mu> i. HH(f, x, i) = {x}) = {x}"
by (fast intro!: Ord_Hartog HH_Hartog_is_x LeastI)

lemma less_Least_subset_x:
     "a \<in> (\<mu> i. HH(f,x,i)={x}) \<Longrightarrow> HH(f,x,a) \<in> Pow(x)-{0}"
apply (rule HH_values [THEN disjE], assumption)
apply (rule less_LeastE)
apply (erule_tac [2] ltI [OF _ Ord_Least], assumption)
done

subsection\<open>Lemmas used in the proofs of AC1 \<Longrightarrow> WO2 and AC17 \<Longrightarrow> AC1\<close>

lemma lam_Least_HH_inj_Pow: 
        "(\<lambda>a \<in> (\<mu> i. HH(f,x,i)={x}). HH(f,x,a))   
         \<in> inj(\<mu> i. HH(f,x,i)={x}, Pow(x)-{0})"
apply (unfold inj_def, simp)
apply (fast intro!: lam_type dest: less_Least_subset_x 
            elim!: HH_eq_imp_arg_eq Ord_Least [THEN Ord_in_Ord])
done

lemma lam_Least_HH_inj:
     "\<forall>a \<in> (\<mu> i. HH(f,x,i)={x}). \<exists>z \<in> x. HH(f,x,a) = {z}   
      \<Longrightarrow> (\<lambda>a \<in> (\<mu> i. HH(f,x,i)={x}). HH(f,x,a))   
          \<in> inj(\<mu> i. HH(f,x,i)={x}, {{y}. y \<in> x})"
by (rule lam_Least_HH_inj_Pow [THEN inj_strengthen_type], simp)

lemma lam_surj_sing: 
        "\<lbrakk>x - (\<Union>a \<in> A. F(a)) = 0;  \<forall>a \<in> A. \<exists>z \<in> x. F(a) = {z}\<rbrakk>   
         \<Longrightarrow> (\<lambda>a \<in> A. F(a)) \<in> surj(A, {{y}. y \<in> x})"
apply (simp add: surj_def lam_type Diff_eq_0_iff)
apply (blast elim: equalityE) 
done

lemma not_emptyI2: "y \<in> Pow(x)-{0} \<Longrightarrow> x \<noteq> 0"
by auto

lemma f_subset_imp_HH_subset:
     "f`(x - (\<Union>j \<in> i. HH(f,x,j))) \<in> Pow(x - (\<Union>j \<in> i. HH(f,x,j)))-{0}   
      \<Longrightarrow> HH(f, x, i) \<in> Pow(x) - {0}"
apply (rule HH_def_satisfies_eq [THEN ssubst])
apply (simp add: Let_def Diff_subset [THEN PowI] not_emptyI2 [THEN if_P], fast)
done

lemma f_subsets_imp_UN_HH_eq_x:
     "\<forall>z \<in> Pow(x)-{0}. f`z \<in> Pow(z)-{0}
      \<Longrightarrow> x - (\<Union>j \<in> (\<mu> i. HH(f,x,i)={x}). HH(f,x,j)) = 0"
apply (case_tac "P \<in> {0}" for P, fast)
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
     "HH(f,x,i): Pow(x)-{0} \<Longrightarrow> HH(f,x,i)=f`(x - (\<Union>j \<in> i. HH(f,x,j)))"
apply (rule HH_values2 [THEN disjE], assumption)
apply (fast elim!: equalityE mem_irrefl dest!: singleton_subsetD)
done

lemma f_sing_imp_HH_sing:
     "\<lbrakk>f \<in> (Pow(x)-{0}) -> {{z}. z \<in> x};   
         a \<in> (\<mu> i. HH(f,x,i)={x})\<rbrakk> \<Longrightarrow> \<exists>z \<in> x. HH(f,x,a) = {z}"
apply (drule less_Least_subset_x)
apply (frule HH_subset_imp_eq)
apply (drule apply_type)
apply (rule Diff_subset [THEN PowI, THEN DiffI])
apply (fast dest!: HH_subset_x_imp_subset_Diff_UN [THEN not_emptyI2], force) 
done

lemma f_sing_lam_bij: 
     "\<lbrakk>x - (\<Union>j \<in> (\<mu> i. HH(f,x,i)={x}). HH(f,x,j)) = 0;   
         f \<in> (Pow(x)-{0}) -> {{z}. z \<in> x}\<rbrakk>   
      \<Longrightarrow> (\<lambda>a \<in> (\<mu> i. HH(f,x,i)={x}). HH(f,x,a))   
          \<in> bij(\<mu> i. HH(f,x,i)={x}, {{y}. y \<in> x})"
apply (unfold bij_def)
apply (fast intro!: lam_Least_HH_inj lam_surj_sing f_sing_imp_HH_sing)
done

lemma lam_singI:
     "f \<in> (\<Prod>X \<in> Pow(x)-{0}. F(X))   
      \<Longrightarrow> (\<lambda>X \<in> Pow(x)-{0}. {f`X}) \<in> (\<Prod>X \<in> Pow(x)-{0}. {{z}. z \<in> F(X)})"
by (fast del: DiffI DiffE
            intro!: lam_type singleton_eq_iff [THEN iffD2] dest: apply_type)

(*FIXME: both uses have the form ...[THEN bij_converse_bij], so 
  simplification is needed!*)
lemmas bij_Least_HH_x =  
    comp_bij [OF f_sing_lam_bij [OF _ lam_singI] 
              lam_sing_bij [THEN bij_converse_bij]]


subsection\<open>The proof of AC1 \<Longrightarrow> WO2\<close>

(*Establishing the existence of a bijection, namely
converse
 (converse(\<lambda>x\<in>x. {x}) O
  Lambda
   (\<mu> i. HH(\<lambda>X\<in>Pow(x) - {0}. {f ` X}, x, i) = {x},
    HH(\<lambda>X\<in>Pow(x) - {0}. {f ` X}, x)))
Perhaps it could be simplified. *)

lemma bijection:
     "f \<in> (\<Prod>X \<in> Pow(x) - {0}. X) 
      \<Longrightarrow> \<exists>g. g \<in> bij(x, \<mu> i. HH(\<lambda>X \<in> Pow(x)-{0}. {f`X}, x, i) = {x})"
apply (rule exI) 
apply (rule bij_Least_HH_x [THEN bij_converse_bij])
apply (rule f_subsets_imp_UN_HH_eq_x)
apply (intro ballI apply_type) 
apply (fast intro: lam_type apply_type del: DiffE, assumption) 
apply (fast intro: Pi_weaken_type)
done

lemma AC1_WO2: "AC1 \<Longrightarrow> WO2"
apply (unfold AC1_def WO2_def eqpoll_def)
apply (intro allI) 
apply (drule_tac x = "Pow(A) - {0}" in spec) 
apply (blast dest: bijection)
done

end

