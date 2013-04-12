(* Author: Tobias Nipkow *)

header "Definite Initialization Analysis"

theory Vars imports Com
begin

subsection "The Variables in an Expression"

text{* We need to collect the variables in both arithmetic and boolean
expressions. For a change we do not introduce two functions, e.g.\ @{text
avars} and @{text bvars}, but we overload the name @{text vars}
via a \emph{type class}, a device that originated with Haskell: *}
 
class vars =
fixes vars :: "'a \<Rightarrow> vname set"

text{* This defines a type class ``vars'' with a single
function of (coincidentally) the same name. Then we define two separated
instances of the class, one for @{typ aexp} and one for @{typ bexp}: *}

instantiation aexp :: vars
begin

fun vars_aexp :: "aexp \<Rightarrow> vname set" where
"vars (N n) = {}" |
"vars (V x) = {x}" |
"vars (Plus a\<^isub>1 a\<^isub>2) = vars a\<^isub>1 \<union> vars a\<^isub>2"

instance ..

end

value "vars (Plus (V ''x'') (V ''y''))"

instantiation bexp :: vars
begin

fun vars_bexp :: "bexp \<Rightarrow> vname set" where
"vars (Bc v) = {}" |
"vars (Not b) = vars b" |
"vars (And b\<^isub>1 b\<^isub>2) = vars b\<^isub>1 \<union> vars b\<^isub>2" |
"vars (Less a\<^isub>1 a\<^isub>2) = vars a\<^isub>1 \<union> vars a\<^isub>2"

instance ..

end

value "vars (Less (Plus (V ''z'') (V ''y'')) (V ''x''))"

abbreviation
  eq_on :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> bool"
 ("(_ =/ _/ on _)" [50,0,50] 50) where
"f = g on X == \<forall> x \<in> X. f x = g x"

lemma aval_eq_if_eq_on_vars[simp]:
  "s\<^isub>1 = s\<^isub>2 on vars a \<Longrightarrow> aval a s\<^isub>1 = aval a s\<^isub>2"
apply(induction a)
apply simp_all
done

lemma bval_eq_if_eq_on_vars:
  "s\<^isub>1 = s\<^isub>2 on vars b \<Longrightarrow> bval b s\<^isub>1 = bval b s\<^isub>2"
proof(induction b)
  case (Less a1 a2)
  hence "aval a1 s\<^isub>1 = aval a1 s\<^isub>2" and "aval a2 s\<^isub>1 = aval a2 s\<^isub>2" by simp_all
  thus ?case by simp
qed simp_all


instantiation com :: vars
begin

fun vars_com :: "com \<Rightarrow> vname set" where
"vars com.SKIP = {}" |
"vars (x::=e) = {x} \<union> vars e" |
"vars (c1;c2) = vars c1 \<union> vars c2" |
"vars (IF b THEN c1 ELSE c2) = vars b \<union> vars c1 \<union> vars c2" |
"vars (WHILE b DO c) = vars b \<union> vars c"

instance ..

end


lemma finite_avars[simp]: "finite(vars(a::aexp))"
by(induction a) simp_all

lemma finite_bvars[simp]: "finite(vars(b::bexp))"
by(induction b) (simp_all add: finite_avars)

lemma finite_cvars[simp]: "finite(vars(c::com))"
by(induction c) (simp_all add: finite_avars finite_bvars)

end
