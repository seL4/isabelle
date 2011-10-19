header "Security Type Systems"

theory Sec_Type_Expr imports Big_Step
begin

subsection "Security Levels and Expressions"

type_synonym level = nat

text{* The security/confidentiality level of each variable is globally fixed
for simplicity. For the sake of examples --- the general theory does not rely
on it! --- a variable of length @{text n} has security level @{text n}: *}

definition sec :: "name \<Rightarrow> level" where 
  "sec n = size n"

fun sec_aexp :: "aexp \<Rightarrow> level" where
"sec_aexp (N n) = 0" |
"sec_aexp (V x) = sec x" |
"sec_aexp (Plus a\<^isub>1 a\<^isub>2) = max (sec_aexp a\<^isub>1) (sec_aexp a\<^isub>2)"

fun sec_bexp :: "bexp \<Rightarrow> level" where
"sec_bexp (Bc v) = 0" |
"sec_bexp (Not b) = sec_bexp b" |
"sec_bexp (And b\<^isub>1 b\<^isub>2) = max (sec_bexp b\<^isub>1) (sec_bexp b\<^isub>2)" |
"sec_bexp (Less a\<^isub>1 a\<^isub>2) = max (sec_aexp a\<^isub>1) (sec_aexp a\<^isub>2)"


abbreviation eq_le :: "state \<Rightarrow> state \<Rightarrow> level \<Rightarrow> bool"
  ("(_ = _ '(\<le> _'))" [51,51,0] 50) where
"s = s' (\<le> l) == (\<forall> x. sec x \<le> l \<longrightarrow> s x = s' x)"

abbreviation eq_less :: "state \<Rightarrow> state \<Rightarrow> level \<Rightarrow> bool"
  ("(_ = _ '(< _'))" [51,51,0] 50) where
"s = s' (< l) == (\<forall> x. sec x < l \<longrightarrow> s x = s' x)"

lemma aval_eq_if_eq_le:
  "\<lbrakk> s\<^isub>1 = s\<^isub>2 (\<le> l);  sec_aexp a \<le> l \<rbrakk> \<Longrightarrow> aval a s\<^isub>1 = aval a s\<^isub>2"
by (induct a) auto

lemma bval_eq_if_eq_le:
  "\<lbrakk> s\<^isub>1 = s\<^isub>2 (\<le> l);  sec_bexp b \<le> l \<rbrakk> \<Longrightarrow> bval b s\<^isub>1 = bval b s\<^isub>2"
by (induct b) (auto simp add: aval_eq_if_eq_le)

end
