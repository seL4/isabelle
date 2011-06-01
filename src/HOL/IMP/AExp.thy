header "Arithmetic and Boolean Expressions"

theory AExp imports Main begin

subsection "Arithmetic Expressions"

type_synonym name = string
type_synonym val = int
type_synonym state = "name \<Rightarrow> val"

datatype aexp = N int | V name | Plus aexp aexp

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) _ = n" |
"aval (V x) s = s x" |
"aval (Plus a1 a2) s = aval a1 s + aval a2 s"


value "aval (Plus (V ''x'') (N 5)) (%x. if x = ''x'' then 7 else 0)"

fun lookup :: "(string * val)list \<Rightarrow> string \<Rightarrow> val" where
"lookup ((x,i)#xis) y = (if x=y then i else lookup xis y)"

value "aval (Plus (V ''x'') (N 5)) (lookup [(''x'',7)])"

value "aval (Plus (V ''x'') (N 5)) (lookup [(''y'',7)])"


subsection "Optimization"

text{* Evaluate constant subsexpressions: *}

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N n) = N n" |
"asimp_const (V x) = V x" |
"asimp_const (Plus a1 a2) =
  (case (asimp_const a1, asimp_const a2) of
    (N n1, N n2) \<Rightarrow> N(n1+n2) |
    (a1',a2') \<Rightarrow> Plus a1' a2')"

theorem aval_asimp_const[simp]:
  "aval (asimp_const a) s = aval a s"
apply(induct a)
apply (auto split: aexp.split)
done

text{* Now we also eliminate all occurrences 0 in additions. The standard
method: optimized versions of the constructors: *}

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N i1) (N i2) = N(i1+i2)" |
"plus (N i) a = (if i=0 then a else Plus (N i) a)" |
"plus a (N i) = (if i=0 then a else Plus a (N i))" |
"plus a1 a2 = Plus a1 a2"

text ""
code_thms plus
code_thms plus

(* FIXME: dropping subsumed code eqns?? *)
lemma aval_plus[simp]:
  "aval (plus a1 a2) s = aval a1 s + aval a2 s"
apply(induct a1 a2 rule: plus.induct)
apply simp_all (* just for a change from auto *)
done
code_thms plus

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x) = V x" |
"asimp (Plus a1 a2) = plus (asimp a1) (asimp a2)"

text{* Note that in @{const asimp_const} the optimized constructor was
inlined. Making it a separate function @{const plus} improves modularity of
the code and the proofs. *}

value "asimp (Plus (Plus (N 0) (N 0)) (Plus (V ''x'') (N 0)))"

theorem aval_asimp[simp]:
  "aval (asimp a) s = aval a s"
apply(induct a)
apply simp_all
done

end
