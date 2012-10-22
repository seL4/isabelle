(* Author: Tobias Nipkow *)

header "Definite Assignment Analysis"

theory Vars imports BExp
begin

subsection "Show sets of variables as lists"

text {* Sets may be infinite and are not always displayed by element 
  if computed as values. Lists do not have this problem. 

  We define a function @{text show} that converts a set of
  variable names into a list. To keep things simple, we rely on
  the convention that we only use single letter names.
*}
definition 
  letters :: "string list" where
  "letters = map (\<lambda>c. [c]) Enum.enum"

definition 
  "show" :: "string set \<Rightarrow> string list" where
  "show S = filter (\<lambda>x. x \<in> S) letters" 

value "show {''x'', ''z''}"

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

value "vars(Plus (V ''x'') (V ''y''))"

text{* We need to convert functions to lists before we can view them: *}

value "show  (vars(Plus (V ''x'') (V ''y'')))"

instantiation bexp :: vars
begin

fun vars_bexp :: "bexp \<Rightarrow> vname set" where
"vars (Bc v) = {}" |
"vars (Not b) = vars b" |
"vars (And b\<^isub>1 b\<^isub>2) = vars b\<^isub>1 \<union> vars b\<^isub>2" |
"vars (Less a\<^isub>1 a\<^isub>2) = vars a\<^isub>1 \<union> vars a\<^isub>2"

instance ..

end

value "show  (vars(Less (Plus (V ''z'') (V ''y'')) (V ''x'')))"

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

end

