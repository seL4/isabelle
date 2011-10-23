theory BExp imports AExp begin

subsection "Boolean Expressions"

text_raw{*\begin{isaverbatimwrite}\newcommand{\BExpbexpdef}{% *}
datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp
text_raw{*}\end{isaverbatimwrite}*}

text_raw{*\begin{isaverbatimwrite}\newcommand{\BExpbvaldef}{% *}
fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"bval (Bc v) s = v" |
"bval (Not b) s = (\<not> bval b s)" |
"bval (And b\<^isub>1 b\<^isub>2) s = (bval b\<^isub>1 s \<and> bval b\<^isub>2 s)" |
"bval (Less a\<^isub>1 a\<^isub>2) s = (aval a\<^isub>1 s < aval a\<^isub>2 s)"
text_raw{*}\end{isaverbatimwrite}*}

value "bval (Less (V ''x'') (Plus (N 3) (V ''y'')))
            <''x'' := 3, ''y'' := 1>"


text{* To improve automation: *}

lemma bval_And_if[simp]:
  "bval (And b1 b2) s = (if bval b1 s then bval b2 s else False)"
by(simp)

declare bval.simps(3)[simp del]  --"remove the original eqn"


subsection "Constant Folding"

text{* Optimizing constructors: *}

text_raw{*\begin{isaverbatimwrite}\newcommand{\BExplessdef}{% *}
fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"less (N n\<^isub>1) (N n\<^isub>2) = Bc(n\<^isub>1 < n\<^isub>2)" |
"less a\<^isub>1 a\<^isub>2 = Less a\<^isub>1 a\<^isub>2"
text_raw{*}\end{isaverbatimwrite}*}

lemma [simp]: "bval (less a1 a2) s = (aval a1 s < aval a2 s)"
apply(induction a1 a2 rule: less.induct)
apply simp_all
done

text_raw{*\begin{isaverbatimwrite}\newcommand{\BExpanddef}{% *}
fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"and (Bc True) b = b" |
"and b (Bc True) = b" |
"and (Bc False) b = Bc False" |
"and b (Bc False) = Bc False" |
"and b\<^isub>1 b\<^isub>2 = And b\<^isub>1 b\<^isub>2"
text_raw{*}\end{isaverbatimwrite}*}

lemma bval_and[simp]: "bval (and b1 b2) s = (bval b1 s \<and> bval b2 s)"
apply(induction b1 b2 rule: and.induct)
apply simp_all
done

text_raw{*\begin{isaverbatimwrite}\newcommand{\BExpnotdef}{% *}
fun not :: "bexp \<Rightarrow> bexp" where
"not (Bc True) = Bc False" |
"not (Bc False) = Bc True" |
"not b = Not b"
text_raw{*}\end{isaverbatimwrite}*}

lemma bval_not[simp]: "bval (not b) s = (\<not> bval b s)"
apply(induction b rule: not.induct)
apply simp_all
done

text{* Now the overall optimizer: *}

text_raw{*\begin{isaverbatimwrite}\newcommand{\BExpbsimpdef}{% *}
fun bsimp :: "bexp \<Rightarrow> bexp" where
"bsimp (Less a\<^isub>1 a\<^isub>2) = less (asimp a\<^isub>1) (asimp a\<^isub>2)" |
"bsimp (And b\<^isub>1 b\<^isub>2) = and (bsimp b\<^isub>1) (bsimp b\<^isub>2)" |
"bsimp (Not b) = not(bsimp b)" |
"bsimp (Bc v) = Bc v"
text_raw{*}\end{isaverbatimwrite}*}

value "bsimp (And (Less (N 0) (N 1)) b)"

value "bsimp (And (Less (N 1) (N 0)) (B True))"

theorem "bval (bsimp b) s = bval b s"
apply(induction b)
apply simp_all
done

end
