theory ComputeHOL
imports Complex_Main "Compute_Oracle/Compute_Oracle"
begin

lemma Trueprop_eq_eq: "Trueprop X == (X == True)" by (simp add: atomize_eq)
lemma meta_eq_trivial: "x == y \<Longrightarrow> x == y" by simp
lemma meta_eq_imp_eq: "x == y \<Longrightarrow> x = y" by auto
lemma eq_trivial: "x = y \<Longrightarrow> x = y" by auto
lemma bool_to_true: "x :: bool \<Longrightarrow> x == True"  by simp
lemma transmeta_1: "x = y \<Longrightarrow> y == z \<Longrightarrow> x = z" by simp
lemma transmeta_2: "x == y \<Longrightarrow> y = z \<Longrightarrow> x = z" by simp
lemma transmeta_3: "x == y \<Longrightarrow> y == z \<Longrightarrow> x = z" by simp


(**** compute_if ****)

lemma If_True: "If True = (\<lambda> x y. x)" by ((rule ext)+,auto)
lemma If_False: "If False = (\<lambda> x y. y)" by ((rule ext)+, auto)

lemmas compute_if = If_True If_False

(**** compute_bool ****)

lemma bool1: "(\<not> True) = False"  by blast
lemma bool2: "(\<not> False) = True"  by blast
lemma bool3: "(P \<and> True) = P" by blast
lemma bool4: "(True \<and> P) = P" by blast
lemma bool5: "(P \<and> False) = False" by blast
lemma bool6: "(False \<and> P) = False" by blast
lemma bool7: "(P \<or> True) = True" by blast
lemma bool8: "(True \<or> P) = True" by blast
lemma bool9: "(P \<or> False) = P" by blast
lemma bool10: "(False \<or> P) = P" by blast
lemma bool11: "(True \<longrightarrow> P) = P" by blast
lemma bool12: "(P \<longrightarrow> True) = True" by blast
lemma bool13: "(True \<longrightarrow> P) = P" by blast
lemma bool14: "(P \<longrightarrow> False) = (\<not> P)" by blast
lemma bool15: "(False \<longrightarrow> P) = True" by blast
lemma bool16: "(False = False) = True" by blast
lemma bool17: "(True = True) = True" by blast
lemma bool18: "(False = True) = False" by blast
lemma bool19: "(True = False) = False" by blast

lemmas compute_bool = bool1 bool2 bool3 bool4 bool5 bool6 bool7 bool8 bool9 bool10 bool11 bool12 bool13 bool14 bool15 bool16 bool17 bool18 bool19


(*** compute_pair ***)

lemma compute_fst: "fst (x,y) = x" by simp
lemma compute_snd: "snd (x,y) = y" by simp
lemma compute_pair_eq: "((a, b) = (c, d)) = (a = c \<and> b = d)" by auto

lemma prod_case_simp: "prod_case f (x,y) = f x y" by simp

lemmas compute_pair = compute_fst compute_snd compute_pair_eq prod_case_simp

(*** compute_option ***)

lemma compute_the: "the (Some x) = x" by simp
lemma compute_None_Some_eq: "(None = Some x) = False" by auto
lemma compute_Some_None_eq: "(Some x = None) = False" by auto
lemma compute_None_None_eq: "(None = None) = True" by auto
lemma compute_Some_Some_eq: "(Some x = Some y) = (x = y)" by auto

definition option_case_compute :: "'b option \<Rightarrow> 'a \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a"
  where "option_case_compute opt a f = option_case a f opt"

lemma option_case_compute: "option_case = (\<lambda> a f opt. option_case_compute opt a f)"
  by (simp add: option_case_compute_def)

lemma option_case_compute_None: "option_case_compute None = (\<lambda> a f. a)"
  apply (rule ext)+
  apply (simp add: option_case_compute_def)
  done

lemma option_case_compute_Some: "option_case_compute (Some x) = (\<lambda> a f. f x)"
  apply (rule ext)+
  apply (simp add: option_case_compute_def)
  done

lemmas compute_option_case = option_case_compute option_case_compute_None option_case_compute_Some

lemmas compute_option = compute_the compute_None_Some_eq compute_Some_None_eq compute_None_None_eq compute_Some_Some_eq compute_option_case

(**** compute_list_length ****)

lemma length_cons:"length (x#xs) = 1 + (length xs)"
  by simp

lemma length_nil: "length [] = 0"
  by simp

lemmas compute_list_length = length_nil length_cons

(*** compute_list_case ***)

definition list_case_compute :: "'b list \<Rightarrow> 'a \<Rightarrow> ('b \<Rightarrow> 'b list \<Rightarrow> 'a) \<Rightarrow> 'a"
  where "list_case_compute l a f = list_case a f l"

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

lemmas compute_list_case = list_case_compute list_case_compute_empty list_case_compute_cons

(*** compute_list_nth ***)
(* Of course, you will need computation with nats for this to work \<dots> *)

lemma compute_list_nth: "((x#xs) ! n) = (if n = 0 then x else (xs ! (n - 1)))"
  by (cases n, auto)
  
(*** compute_list ***)

lemmas compute_list = compute_list_case compute_list_length compute_list_nth

(*** compute_let ***)

lemmas compute_let = Let_def

(***********************)
(* Everything together *)
(***********************)

lemmas compute_hol = compute_if compute_bool compute_pair compute_option compute_list compute_let

ML {*
signature ComputeHOL =
sig
  val prep_thms : thm list -> thm list
  val to_meta_eq : thm -> thm
  val to_hol_eq : thm -> thm
  val symmetric : thm -> thm 
  val trans : thm -> thm -> thm
end

structure ComputeHOL : ComputeHOL =
struct

local
fun lhs_of eq = fst (Thm.dest_equals (cprop_of eq));
in
fun rewrite_conv [] ct = raise CTERM ("rewrite_conv", [ct])
  | rewrite_conv (eq :: eqs) ct =
      Thm.instantiate (Thm.match (lhs_of eq, ct)) eq
      handle Pattern.MATCH => rewrite_conv eqs ct;
end

val convert_conditions = Conv.fconv_rule (Conv.prems_conv ~1 (Conv.try_conv (rewrite_conv [@{thm "Trueprop_eq_eq"}])))

val eq_th = @{thm "HOL.eq_reflection"}
val meta_eq_trivial = @{thm "ComputeHOL.meta_eq_trivial"}
val bool_to_true = @{thm "ComputeHOL.bool_to_true"}

fun to_meta_eq th = eq_th OF [th] handle THM _ => meta_eq_trivial OF [th] handle THM _ => bool_to_true OF [th]

fun to_hol_eq th = @{thm "meta_eq_imp_eq"} OF [th] handle THM _ => @{thm "eq_trivial"} OF [th] 

fun prep_thms ths = map (convert_conditions o to_meta_eq) ths

fun symmetric th = @{thm "HOL.sym"} OF [th] handle THM _ => @{thm "Pure.symmetric"} OF [th]

local
    val trans_HOL = @{thm "HOL.trans"}
    val trans_HOL_1 = @{thm "ComputeHOL.transmeta_1"}
    val trans_HOL_2 = @{thm "ComputeHOL.transmeta_2"}
    val trans_HOL_3 = @{thm "ComputeHOL.transmeta_3"}
    fun tr [] th1 th2 = trans_HOL OF [th1, th2]
      | tr (t::ts) th1 th2 = (t OF [th1, th2] handle THM _ => tr ts th1 th2) 
in
  fun trans th1 th2 = tr [trans_HOL, trans_HOL_1, trans_HOL_2, trans_HOL_3] th1 th2
end

end
*}

end
