(*  Title:      HOL/Matrix/cplex/MatrixLP.thy
    ID:         $Id$
    Author:     Steven Obua
*)

theory MatrixLP 
imports Cplex
begin

constdefs
  list_case_compute :: "'b list \<Rightarrow> 'a \<Rightarrow> ('b \<Rightarrow> 'b list \<Rightarrow> 'a) \<Rightarrow> 'a"
  "list_case_compute l a f == list_case a f l"

lemma list_case_compute: "list_case = (\<lambda> (a::'a) f (l::'b list). list_case_compute l a f)"
  apply (rule ext)+
  apply (simp add: list_case_compute_def)
  done

lemma list_case_compute_empty: "list_case_compute ([]::'b list) = (\<lambda> (a::'a) f. a)"
  apply (rule ext)+
  apply (simp add: list_case_compute_def)
  done

lemma list_case_compute_cons: "list_case_compute (u#v) = (\<lambda> (a::'a) f. (f (u::'b) v))"
  apply (rule ext)+
  apply (simp add: list_case_compute_def)
  done

lemma If_True: "(If True) = (\<lambda> x y. x)"
  apply (rule ext)+
  apply auto
  done

lemma If_False: "(If False) = (\<lambda> x y. y)"
  apply (rule ext)+
  apply auto
  done

lemma Let_compute: "Let (x::'a) f = ((f x)::'b)"
  by (simp add: Let_def)

lemma fst_compute: "fst (a::'a, b::'b) = a"
  by auto

lemma snd_compute: "snd (a::'a, b::'b) = b"
  by auto

lemma bool1: "(\<not> True) = False"  by blast
lemma bool2: "(\<not> False) = True"  by blast
lemma bool3: "((P\<Colon>bool) \<and> True) = P" by blast
lemma bool4: "(True \<and> (P\<Colon>bool)) = P" by blast
lemma bool5: "((P\<Colon>bool) \<and> False) = False" by blast
lemma bool6: "(False \<and> (P\<Colon>bool)) = False" by blast
lemma bool7: "((P\<Colon>bool) \<or> True) = True" by blast
lemma bool8: "(True \<or> (P\<Colon>bool)) = True" by blast
lemma bool9: "((P\<Colon>bool) \<or> False) = P" by blast
lemma bool10: "(False \<or> (P\<Colon>bool)) = P" by blast
lemmas boolarith = bool1 bool2 bool3 bool4 bool5 bool6 bool7 bool8 bool9 bool10

lemmas float_arith = Float.arith
lemmas sparse_row_matrix_arith_simps = SparseMatrix.sparse_row_matrix_arith_simps
lemmas sorted_sp_simps = SparseMatrix.sorted_sp_simps
lemmas fst_snd_conv = Product_Type.fst_conv Product_Type.snd_conv

end

