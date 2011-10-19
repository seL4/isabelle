theory Poly_Types imports Types begin

subsection "Type Variables"

datatype ty = Ity | Rty | TV nat

text{* Everything else remains the same. *}

type_synonym tyenv = "name \<Rightarrow> ty"

inductive atyping :: "tyenv \<Rightarrow> aexp \<Rightarrow> ty \<Rightarrow> bool"
  ("(1_/ \<turnstile>p/ (_ :/ _))" [50,0,50] 50)
where
"\<Gamma> \<turnstile>p Ic i : Ity" |
"\<Gamma> \<turnstile>p Rc r : Rty" |
"\<Gamma> \<turnstile>p V x : \<Gamma> x" |
"\<Gamma> \<turnstile>p a1 : \<tau> \<Longrightarrow> \<Gamma> \<turnstile>p a2 : \<tau> \<Longrightarrow> \<Gamma> \<turnstile>p Plus a1 a2 : \<tau>"

inductive btyping :: "tyenv \<Rightarrow> bexp \<Rightarrow> bool" (infix "\<turnstile>p" 50)
where
"\<Gamma> \<turnstile>p Bc v" |
"\<Gamma> \<turnstile>p b \<Longrightarrow> \<Gamma> \<turnstile>p Not b" |
"\<Gamma> \<turnstile>p b1 \<Longrightarrow> \<Gamma> \<turnstile>p b2 \<Longrightarrow> \<Gamma> \<turnstile>p And b1 b2" |
"\<Gamma> \<turnstile>p a1 : \<tau> \<Longrightarrow> \<Gamma> \<turnstile>p a2 : \<tau> \<Longrightarrow> \<Gamma> \<turnstile>p Less a1 a2"

inductive ctyping :: "tyenv \<Rightarrow> com \<Rightarrow> bool" (infix "\<turnstile>p" 50) where
"\<Gamma> \<turnstile>p SKIP" |
"\<Gamma> \<turnstile>p a : \<Gamma>(x) \<Longrightarrow> \<Gamma> \<turnstile>p x ::= a" |
"\<Gamma> \<turnstile>p c1 \<Longrightarrow> \<Gamma> \<turnstile>p c2 \<Longrightarrow> \<Gamma> \<turnstile>p c1;c2" |
"\<Gamma> \<turnstile>p b \<Longrightarrow> \<Gamma> \<turnstile>p c1 \<Longrightarrow> \<Gamma> \<turnstile>p c2 \<Longrightarrow> \<Gamma> \<turnstile>p IF b THEN c1 ELSE c2" |
"\<Gamma> \<turnstile>p b \<Longrightarrow> \<Gamma> \<turnstile>p c \<Longrightarrow> \<Gamma> \<turnstile>p WHILE b DO c"

fun type :: "val \<Rightarrow> ty" where
"type (Iv i) = Ity" |
"type (Rv r) = Rty"

definition styping :: "tyenv \<Rightarrow> state \<Rightarrow> bool" (infix "\<turnstile>p" 50)
where "\<Gamma> \<turnstile>p s  \<longleftrightarrow>  (\<forall>x. type (s x) = \<Gamma> x)"

fun tsubst :: "(nat \<Rightarrow> ty) \<Rightarrow> ty \<Rightarrow> ty" where
"tsubst S (TV n) = S n" |
"tsubst S t = t"


subsection{* Typing is Preserved by Substitution *}

lemma subst_atyping: "E \<turnstile>p a : t \<Longrightarrow> tsubst S \<circ> E \<turnstile>p a : tsubst S t"
apply(induction rule: atyping.induct)
apply(auto intro: atyping.intros)
done

lemma subst_btyping: "E \<turnstile>p (b::bexp) \<Longrightarrow> tsubst S \<circ> E \<turnstile>p b"
apply(induction rule: btyping.induct)
apply(auto intro: btyping.intros)
apply(drule subst_atyping[where S=S])
apply(drule subst_atyping[where S=S])
apply(simp add: o_def btyping.intros)
done

lemma subst_ctyping: "E \<turnstile>p (c::com) \<Longrightarrow> tsubst S \<circ> E \<turnstile>p c"
apply(induction rule: ctyping.induct)
apply(auto intro: ctyping.intros)
apply(drule subst_atyping[where S=S])
apply(simp add: o_def ctyping.intros)
apply(drule subst_btyping[where S=S])
apply(simp add: o_def ctyping.intros)
apply(drule subst_btyping[where S=S])
apply(simp add: o_def ctyping.intros)
done

end
