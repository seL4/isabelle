(*  Title:      HOL/HOLCF/IOA/TLS.thy
    Author:     Olaf Müller
*)

section \<open>Temporal Logic of Steps -- tailored for I/O automata\<close>

theory TLS
imports IOA TL
begin

default_sort type

type_synonym ('a, 's) ioa_temp  = "('a option, 's) transition temporal"

type_synonym ('a, 's) step_pred = "('a option, 's) transition predicate"

type_synonym 's state_pred = "'s predicate"

definition mkfin :: "'a Seq \<Rightarrow> 'a Seq"
  where "mkfin s = (if Partial s then SOME t. Finite t \<and> s = t @@ UU else s)"

definition option_lift :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a option \<Rightarrow> 'b"
  where "option_lift f s y = (case y of None \<Rightarrow> s | Some x \<Rightarrow> f x)"

definition plift :: "('a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> bool"
(* plift is used to determine that None action is always false in
   transition predicates *)
  where "plift P = option_lift P False"

definition xt1 :: "'s predicate \<Rightarrow> ('a, 's) step_pred"
  where "xt1 P tr = P (fst tr)"

definition xt2 :: "'a option predicate \<Rightarrow> ('a, 's) step_pred"
  where "xt2 P tr = P (fst (snd tr))"

definition ex2seqC :: "('a, 's) pairs \<rightarrow> ('s \<Rightarrow> ('a option, 's) transition Seq)"
  where "ex2seqC =
    (fix \<cdot> (LAM h ex. (\<lambda>s. case ex of
      nil \<Rightarrow> (s, None, s) \<leadsto> nil
    | x ## xs \<Rightarrow> (flift1 (\<lambda>pr. (s, Some (fst pr), snd pr) \<leadsto> (h \<cdot> xs) (snd pr)) \<cdot> x))))"

definition ex2seq :: "('a, 's) execution \<Rightarrow> ('a option, 's) transition Seq"
  where "ex2seq ex = (ex2seqC \<cdot> (mkfin (snd ex))) (fst ex)"

definition temp_sat :: "('a, 's) execution \<Rightarrow> ('a, 's) ioa_temp \<Rightarrow> bool"  (infixr \<open>\<TTurnstile>\<close> 22)
  where "(ex \<TTurnstile> P) \<longleftrightarrow> ((ex2seq ex) \<Turnstile> P)"

definition validTE :: "('a, 's) ioa_temp \<Rightarrow> bool"
  where "validTE P \<longleftrightarrow> (\<forall>ex. (ex \<TTurnstile> P))"

definition validIOA :: "('a, 's) ioa \<Rightarrow> ('a, 's) ioa_temp \<Rightarrow> bool"
  where "validIOA A P \<longleftrightarrow> (\<forall>ex \<in> executions A. (ex \<TTurnstile> P))"


lemma IMPLIES_temp_sat [simp]: "(ex \<TTurnstile> P \<^bold>\<longrightarrow> Q) \<longleftrightarrow> ((ex \<TTurnstile> P) \<longrightarrow> (ex \<TTurnstile> Q))"
  by (simp add: IMPLIES_def temp_sat_def satisfies_def)

lemma AND_temp_sat [simp]: "(ex \<TTurnstile> P \<^bold>\<and> Q) \<longleftrightarrow> ((ex \<TTurnstile> P) \<and> (ex \<TTurnstile> Q))"
  by (simp add: AND_def temp_sat_def satisfies_def)

lemma OR_temp_sat [simp]: "(ex \<TTurnstile> P \<^bold>\<or> Q) \<longleftrightarrow> ((ex \<TTurnstile> P) \<or> (ex \<TTurnstile> Q))"
  by (simp add: OR_def temp_sat_def satisfies_def)

lemma NOT_temp_sat [simp]: "(ex \<TTurnstile> \<^bold>\<not> P) \<longleftrightarrow> (\<not> (ex \<TTurnstile> P))"
  by (simp add: NOT_def temp_sat_def satisfies_def)


axiomatization
where mkfin_UU [simp]: "mkfin UU = nil"
  and mkfin_nil [simp]: "mkfin nil = nil"
  and mkfin_cons [simp]: "mkfin (a \<leadsto> s) = a \<leadsto> mkfin s"


lemmas [simp del] = HOL.ex_simps HOL.all_simps split_paired_Ex

setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper "split_all_tac")\<close>


subsection \<open>ex2seqC\<close>

lemma ex2seqC_unfold:
  "ex2seqC =
    (LAM ex. (\<lambda>s. case ex of
      nil \<Rightarrow> (s, None, s) \<leadsto> nil
    | x ## xs \<Rightarrow>
        (flift1 (\<lambda>pr. (s, Some (fst pr), snd pr) \<leadsto> (ex2seqC \<cdot> xs) (snd pr)) \<cdot> x)))"
  apply (rule trans)
  apply (rule fix_eq4)
  apply (rule ex2seqC_def)
  apply (rule beta_cfun)
  apply (simp add: flift1_def)
  done

lemma ex2seqC_UU [simp]: "(ex2seqC \<cdot> UU) s = UU"
  apply (subst ex2seqC_unfold)
  apply simp
  done

lemma ex2seqC_nil [simp]: "(ex2seqC \<cdot> nil) s = (s, None, s) \<leadsto> nil"
  apply (subst ex2seqC_unfold)
  apply simp
  done

lemma ex2seqC_cons [simp]: "(ex2seqC \<cdot> ((a, t) \<leadsto> xs)) s = (s, Some a,t ) \<leadsto> (ex2seqC \<cdot> xs) t"
  apply (rule trans)
  apply (subst ex2seqC_unfold)
  apply (simp add: Consq_def flift1_def)
  apply (simp add: Consq_def flift1_def)
  done


lemma ex2seq_UU: "ex2seq (s, UU) = (s, None, s) \<leadsto> nil"
  by (simp add: ex2seq_def)

lemma ex2seq_nil: "ex2seq (s, nil) = (s, None, s) \<leadsto> nil"
  by (simp add: ex2seq_def)

lemma ex2seq_cons: "ex2seq (s, (a, t) \<leadsto> ex) = (s, Some a, t) \<leadsto> ex2seq (t, ex)"
  by (simp add: ex2seq_def)

declare ex2seqC_UU [simp del] ex2seqC_nil [simp del] ex2seqC_cons [simp del]
declare ex2seq_UU [simp] ex2seq_nil [simp] ex2seq_cons [simp]


lemma ex2seq_nUUnnil: "ex2seq exec \<noteq> UU \<and> ex2seq exec \<noteq> nil"
  apply (pair exec)
  apply (Seq_case_simp x2)
  apply (pair a)
  done


subsection \<open>Interface TL -- TLS\<close>

(* uses the fact that in executions states overlap, which is lost in
   after the translation via ex2seq !! *)

lemma TL_TLS:
  "\<forall>s a t. (P s) \<and> s \<midarrow>a\<midarrow>A\<rightarrow> t \<longrightarrow> (Q t)
    \<Longrightarrow> ex \<TTurnstile> (Init (\<lambda>(s, a, t). P s) \<^bold>\<and> Init (\<lambda>(s, a, t). s \<midarrow>a\<midarrow>A\<rightarrow> t)
              \<^bold>\<longrightarrow> (\<circle>(Init (\<lambda>(s, a, t). Q s))))"
  apply (unfold Init_def Next_def temp_sat_def satisfies_def IMPLIES_def AND_def)
  apply clarify
  apply (simp split: if_split)
  text \<open>\<open>TL = UU\<close>\<close>
  apply (rule conjI)
  apply (pair ex)
  apply (Seq_case_simp x2)
  apply (pair a)
  apply (Seq_case_simp s)
  apply (pair a)
  text \<open>\<open>TL = nil\<close>\<close>
  apply (rule conjI)
  apply (pair ex)
  apply (Seq_case x2)
  apply (simp add: unlift_def)
  apply (simp add: unlift_def)
  apply (simp add: unlift_def)
  apply (pair a)
  apply (Seq_case_simp s)
  apply (pair a)
  text \<open>\<open>TL = cons\<close>\<close>
  apply (simp add: unlift_def)
  apply (pair ex)
  apply (Seq_case_simp x2)
  apply (pair a)
  apply (Seq_case_simp s)
  apply (pair a)
  done

end
