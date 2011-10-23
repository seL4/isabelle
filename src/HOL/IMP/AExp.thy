header "Arithmetic and Boolean Expressions"

theory AExp imports Main begin

subsection "Arithmetic Expressions"

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

text_raw{*\begin{isaverbatimwrite}\newcommand{\AExpaexpdef}{% *}
datatype aexp = N int | V vname | Plus aexp aexp
text_raw{*}\end{isaverbatimwrite}*}

text_raw{*\begin{isaverbatimwrite}\newcommand{\AExpavaldef}{% *}
fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a1 a2) s = aval a1 s + aval a2 s"
text_raw{*}\end{isaverbatimwrite}*}


value "aval (Plus (V ''x'') (N 5)) (\<lambda>x. if x = ''x'' then 7 else 0)"

text {* The same state more concisely: *}
value "aval (Plus (V ''x'') (N 5)) ((\<lambda>x. 0) (''x'':= 7))"

text {* A little syntax magic to write larger states compactly: *}

definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax 
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" => "_Update <> ms"

text {* 
  We can now write a series of updates to the function @{text "\<lambda>x. 0"} compactly:
*}
lemma "<a := Suc 0, b := 2> = (<> (a := Suc 0)) (b := 2)"
  by (rule refl)

value "aval (Plus (V ''x'') (N 5)) <''x'' := 7>"


text {* Variables that are not mentioned in the state are 0 by default in 
  the @{term "<a := b::int>"} syntax: 
*}
value "aval (Plus (V ''x'') (N 5)) <''y'' := 7>"

text{* Note that this @{text"<\<dots>>"} syntax works for any function space
@{text"\<tau>\<^isub>1 \<Rightarrow> \<tau>\<^isub>2"} where @{text "\<tau>\<^isub>2"} has a @{text 0}. *}


subsection "Constant Folding"

text{* Evaluate constant subsexpressions: *}

text_raw{*\begin{isaverbatimwrite}\newcommand{\AExpasimpconstdef}{% *}
fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N n) = N n" |
"asimp_const (V x) = V x" |
"asimp_const (Plus a\<^isub>1 a\<^isub>2) =
  (case (asimp_const a\<^isub>1, asimp_const a\<^isub>2) of
    (N n\<^isub>1, N n\<^isub>2) \<Rightarrow> N(n\<^isub>1+n\<^isub>2) |
    (b\<^isub>1,b\<^isub>2) \<Rightarrow> Plus b\<^isub>1 b\<^isub>2)"
text_raw{*}\end{isaverbatimwrite}*}

theorem aval_asimp_const:
  "aval (asimp_const a) s = aval a s"
apply(induction a)
apply (auto split: aexp.split)
done

text{* Now we also eliminate all occurrences 0 in additions. The standard
method: optimized versions of the constructors: *}

text_raw{*\begin{isaverbatimwrite}\newcommand{\AExpplusdef}{% *}
fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N i\<^isub>1) (N i\<^isub>2) = N(i\<^isub>1+i\<^isub>2)" |
"plus (N i) a = (if i=0 then a else Plus (N i) a)" |
"plus a (N i) = (if i=0 then a else Plus a (N i))" |
"plus a\<^isub>1 a\<^isub>2 = Plus a\<^isub>1 a\<^isub>2"
text_raw{*}\end{isaverbatimwrite}*}

lemma aval_plus[simp]:
  "aval (plus a1 a2) s = aval a1 s + aval a2 s"
apply(induction a1 a2 rule: plus.induct)
apply simp_all (* just for a change from auto *)
done

text_raw{*\begin{isaverbatimwrite}\newcommand{\AExpasimpdef}{% *}
fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x) = V x" |
"asimp (Plus a\<^isub>1 a\<^isub>2) = plus (asimp a\<^isub>1) (asimp a\<^isub>2)"
text_raw{*}\end{isaverbatimwrite}*}

text{* Note that in @{const asimp_const} the optimized constructor was
inlined. Making it a separate function @{const plus} improves modularity of
the code and the proofs. *}

value "asimp (Plus (Plus (N 0) (N 0)) (Plus (V ''x'') (N 0)))"

theorem aval_asimp[simp]:
  "aval (asimp a) s = aval a s"
apply(induction a)
apply simp_all
done

end
