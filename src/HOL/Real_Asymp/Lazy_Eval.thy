section \<open>Lazy evaluation within the logic\<close>
theory Lazy_Eval
imports
  Complex_Main
begin

text \<open>  
  This is infrastructure to lazily evaluate an expression (typically something corecursive)
  within the logic by simple rewriting. A signature of supported (co-)datatype constructures 
  upon which pattern matching is allowed and a list of function equations that are used in
  rewriting must be provided.

  One can then e.\,g.\ determine whether a given pattern matches a given expression. To do this,
  the expression will be rewritten using the given function equations until enough constructors
  have been exposed to decide whether the pattern matches.

  This infrastructure was developed specifically for evaluating Multiseries expressions, but
  can, in principle, be used for other purposes as well.
\<close>

lemma meta_eq_TrueE: "PROP P \<equiv> Trueprop True \<Longrightarrow> PROP P" by simp

datatype cmp_result = LT | EQ | GT

definition COMPARE :: "real \<Rightarrow> real \<Rightarrow> cmp_result" where
  "COMPARE x y = (if x < y then LT else if x > y then GT else EQ)"

lemma COMPARE_intros: 
  "x < y \<Longrightarrow> COMPARE x y \<equiv> LT" "x > y \<Longrightarrow> COMPARE x y \<equiv> GT" "x = y \<Longrightarrow> COMPARE x y \<equiv> EQ"
  by (simp_all add: COMPARE_def)
  
primrec CMP_BRANCH :: "cmp_result \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "CMP_BRANCH LT x y z = x"
| "CMP_BRANCH EQ x y z = y"
| "CMP_BRANCH GT x y z = z"  

ML_file \<open>lazy_eval.ML\<close>

end