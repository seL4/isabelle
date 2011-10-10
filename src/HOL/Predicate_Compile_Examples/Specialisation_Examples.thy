theory Specialisation_Examples
imports Main "~~/src/HOL/Library/Predicate_Compile_Alternative_Defs"
begin

declare [[values_timeout = 960.0]]

section {* Specialisation Examples *}

primrec nth_el'
where
  "nth_el' [] i = None"
| "nth_el' (x # xs) i = (case i of 0 => Some x | Suc j => nth_el' xs j)"

definition
  "greater_than_index xs = (\<forall>i x. nth_el' xs i = Some x --> x > i)"

code_pred (expected_modes: i => bool) [inductify, skip_proof, specialise] greater_than_index .
ML {* Core_Data.intros_of @{context} @{const_name specialised_nth_el'P} *}

thm greater_than_index.equation

values [expected "{()}"] "{x. greater_than_index [1,2,4,6]}"
values [expected "{}"] "{x. greater_than_index [0,2,3,2]}"

subsection {* Common subterms *}

text {* If a predicate is called with common subterms as arguments,
  this predicate should be specialised. 
*}

definition max_nat :: "nat => nat => nat"
  where "max_nat a b = (if a <= b then b else a)"

lemma [code_pred_inline]:
  "max = max_nat"
by (simp add: fun_eq_iff max_def max_nat_def)

definition
  "max_of_my_Suc x = max x (Suc x)"

text {* In this example, max is specialised, hence the mode o => i => bool is possible *}

code_pred (modes: o => i => bool) [inductify, specialise, skip_proof] max_of_my_Suc .

thm max_of_my_SucP.equation

ML {* Core_Data.intros_of @{context} @{const_name specialised_max_natP} *}

values "{x. max_of_my_SucP x 6}"

subsection {* Sorts *}

declare sorted.Nil [code_pred_intro]
  sorted_single [code_pred_intro]
  sorted_many [code_pred_intro]

code_pred sorted proof -
  assume "sorted xa"
  assume 1: "xa = [] \<Longrightarrow> thesis"
  assume 2: "\<And>x. xa = [x] \<Longrightarrow> thesis"
  assume 3: "\<And>x y zs. xa = x # y # zs \<Longrightarrow> x \<le> y \<Longrightarrow> sorted (y # zs) \<Longrightarrow> thesis"
  show thesis proof (cases xa)
    case Nil with 1 show ?thesis .
  next
    case (Cons x xs) show ?thesis proof (cases xs)
      case Nil with Cons 2 show ?thesis by simp
    next
      case (Cons y zs) with `xa = x # xs` have "xa = x # y # zs" by simp
      moreover with `sorted xa` have "x \<le> y" and "sorted (y # zs)" by simp_all
      ultimately show ?thesis by (rule 3)
    qed
  qed
qed
thm sorted.equation

section {* Specialisation in POPLmark theory *}

notation
  Some ("\<lfloor>_\<rfloor>")

notation
  None ("\<bottom>")

notation
  length ("\<parallel>_\<parallel>")

notation
  Cons ("_ \<Colon>/ _" [66, 65] 65)

primrec
  nth_el :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" ("_\<langle>_\<rangle>" [90, 0] 91)
where
  "[]\<langle>i\<rangle> = \<bottom>"
| "(x # xs)\<langle>i\<rangle> = (case i of 0 \<Rightarrow> \<lfloor>x\<rfloor> | Suc j \<Rightarrow> xs \<langle>j\<rangle>)"

primrec assoc :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b option" ("_\<langle>_\<rangle>\<^isub>?" [90, 0] 91)
where
  "[]\<langle>a\<rangle>\<^isub>? = \<bottom>"
| "(x # xs)\<langle>a\<rangle>\<^isub>? = (if fst x = a then \<lfloor>snd x\<rfloor> else xs\<langle>a\<rangle>\<^isub>?)"

primrec unique :: "('a \<times> 'b) list \<Rightarrow> bool"
where
  "unique [] = True"
| "unique (x # xs) = (xs\<langle>fst x\<rangle>\<^isub>? = \<bottom> \<and> unique xs)"

datatype type =
    TVar nat
  | Top
  | Fun type type    (infixr "\<rightarrow>" 200)
  | TyAll type type  ("(3\<forall><:_./ _)" [0, 10] 10)

datatype binding = VarB type | TVarB type
type_synonym env = "binding list"

primrec is_TVarB :: "binding \<Rightarrow> bool"
where
  "is_TVarB (VarB T) = False"
| "is_TVarB (TVarB T) = True"

primrec type_ofB :: "binding \<Rightarrow> type"
where
  "type_ofB (VarB T) = T"
| "type_ofB (TVarB T) = T"

primrec mapB :: "(type \<Rightarrow> type) \<Rightarrow> binding \<Rightarrow> binding"
where
  "mapB f (VarB T) = VarB (f T)"
| "mapB f (TVarB T) = TVarB (f T)"

datatype trm =
    Var nat
  | Abs type trm   ("(3\<lambda>:_./ _)" [0, 10] 10)
  | TAbs type trm  ("(3\<lambda><:_./ _)" [0, 10] 10)
  | App trm trm    (infixl "\<bullet>" 200)
  | TApp trm type  (infixl "\<bullet>\<^isub>\<tau>" 200)

primrec liftT :: "nat \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> type" ("\<up>\<^isub>\<tau>")
where
  "\<up>\<^isub>\<tau> n k (TVar i) = (if i < k then TVar i else TVar (i + n))"
| "\<up>\<^isub>\<tau> n k Top = Top"
| "\<up>\<^isub>\<tau> n k (T \<rightarrow> U) = \<up>\<^isub>\<tau> n k T \<rightarrow> \<up>\<^isub>\<tau> n k U"
| "\<up>\<^isub>\<tau> n k (\<forall><:T. U) = (\<forall><:\<up>\<^isub>\<tau> n k T. \<up>\<^isub>\<tau> n (k + 1) U)"

primrec lift :: "nat \<Rightarrow> nat \<Rightarrow> trm \<Rightarrow> trm" ("\<up>")
where
  "\<up> n k (Var i) = (if i < k then Var i else Var (i + n))"
| "\<up> n k (\<lambda>:T. t) = (\<lambda>:\<up>\<^isub>\<tau> n k T. \<up> n (k + 1) t)"
| "\<up> n k (\<lambda><:T. t) = (\<lambda><:\<up>\<^isub>\<tau> n k T. \<up> n (k + 1) t)"
| "\<up> n k (s \<bullet> t) = \<up> n k s \<bullet> \<up> n k t"
| "\<up> n k (t \<bullet>\<^isub>\<tau> T) = \<up> n k t \<bullet>\<^isub>\<tau> \<up>\<^isub>\<tau> n k T"

primrec substTT :: "type \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> type"  ("_[_ \<mapsto>\<^isub>\<tau> _]\<^isub>\<tau>" [300, 0, 0] 300)
where
  "(TVar i)[k \<mapsto>\<^isub>\<tau> S]\<^isub>\<tau> =
     (if k < i then TVar (i - 1) else if i = k then \<up>\<^isub>\<tau> k 0 S else TVar i)"
| "Top[k \<mapsto>\<^isub>\<tau> S]\<^isub>\<tau> = Top"
| "(T \<rightarrow> U)[k \<mapsto>\<^isub>\<tau> S]\<^isub>\<tau> = T[k \<mapsto>\<^isub>\<tau> S]\<^isub>\<tau> \<rightarrow> U[k \<mapsto>\<^isub>\<tau> S]\<^isub>\<tau>"
| "(\<forall><:T. U)[k \<mapsto>\<^isub>\<tau> S]\<^isub>\<tau> = (\<forall><:T[k \<mapsto>\<^isub>\<tau> S]\<^isub>\<tau>. U[k+1 \<mapsto>\<^isub>\<tau> S]\<^isub>\<tau>)"

primrec decT :: "nat \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> type"  ("\<down>\<^isub>\<tau>")
where
  "\<down>\<^isub>\<tau> 0 k T = T"
| "\<down>\<^isub>\<tau> (Suc n) k T = \<down>\<^isub>\<tau> n k (T[k \<mapsto>\<^isub>\<tau> Top]\<^isub>\<tau>)"

primrec subst :: "trm \<Rightarrow> nat \<Rightarrow> trm \<Rightarrow> trm"  ("_[_ \<mapsto> _]" [300, 0, 0] 300)
where
  "(Var i)[k \<mapsto> s] = (if k < i then Var (i - 1) else if i = k then \<up> k 0 s else Var i)"
| "(t \<bullet> u)[k \<mapsto> s] = t[k \<mapsto> s] \<bullet> u[k \<mapsto> s]"
| "(t \<bullet>\<^isub>\<tau> T)[k \<mapsto> s] = t[k \<mapsto> s] \<bullet>\<^isub>\<tau> \<down>\<^isub>\<tau> 1 k T"
| "(\<lambda>:T. t)[k \<mapsto> s] = (\<lambda>:\<down>\<^isub>\<tau> 1 k T. t[k+1 \<mapsto> s])"
| "(\<lambda><:T. t)[k \<mapsto> s] = (\<lambda><:\<down>\<^isub>\<tau> 1 k T. t[k+1 \<mapsto> s])"

primrec substT :: "trm \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> trm"    ("_[_ \<mapsto>\<^isub>\<tau> _]" [300, 0, 0] 300)
where
  "(Var i)[k \<mapsto>\<^isub>\<tau> S] = (if k < i then Var (i - 1) else Var i)"
| "(t \<bullet> u)[k \<mapsto>\<^isub>\<tau> S] = t[k \<mapsto>\<^isub>\<tau> S] \<bullet> u[k \<mapsto>\<^isub>\<tau> S]"
| "(t \<bullet>\<^isub>\<tau> T)[k \<mapsto>\<^isub>\<tau> S] = t[k \<mapsto>\<^isub>\<tau> S] \<bullet>\<^isub>\<tau> T[k \<mapsto>\<^isub>\<tau> S]\<^isub>\<tau>"
| "(\<lambda>:T. t)[k \<mapsto>\<^isub>\<tau> S] = (\<lambda>:T[k \<mapsto>\<^isub>\<tau> S]\<^isub>\<tau>. t[k+1 \<mapsto>\<^isub>\<tau> S])"
| "(\<lambda><:T. t)[k \<mapsto>\<^isub>\<tau> S] = (\<lambda><:T[k \<mapsto>\<^isub>\<tau> S]\<^isub>\<tau>. t[k+1 \<mapsto>\<^isub>\<tau> S])"

primrec liftE :: "nat \<Rightarrow> nat \<Rightarrow> env \<Rightarrow> env" ("\<up>\<^isub>e")
where
  "\<up>\<^isub>e n k [] = []"
| "\<up>\<^isub>e n k (B \<Colon> \<Gamma>) = mapB (\<up>\<^isub>\<tau> n (k + \<parallel>\<Gamma>\<parallel>)) B \<Colon> \<up>\<^isub>e n k \<Gamma>"

primrec substE :: "env \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> env"  ("_[_ \<mapsto>\<^isub>\<tau> _]\<^isub>e" [300, 0, 0] 300)
where
  "[][k \<mapsto>\<^isub>\<tau> T]\<^isub>e = []"
| "(B \<Colon> \<Gamma>)[k \<mapsto>\<^isub>\<tau> T]\<^isub>e = mapB (\<lambda>U. U[k + \<parallel>\<Gamma>\<parallel> \<mapsto>\<^isub>\<tau> T]\<^isub>\<tau>) B \<Colon> \<Gamma>[k \<mapsto>\<^isub>\<tau> T]\<^isub>e"

primrec decE :: "nat \<Rightarrow> nat \<Rightarrow> env \<Rightarrow> env"  ("\<down>\<^isub>e")
where
  "\<down>\<^isub>e 0 k \<Gamma> = \<Gamma>"
| "\<down>\<^isub>e (Suc n) k \<Gamma> = \<down>\<^isub>e n k (\<Gamma>[k \<mapsto>\<^isub>\<tau> Top]\<^isub>e)"

inductive
  well_formed :: "env \<Rightarrow> type \<Rightarrow> bool"  ("_ \<turnstile>\<^bsub>wf\<^esub> _" [50, 50] 50)
where
  wf_TVar: "\<Gamma>\<langle>i\<rangle> = \<lfloor>TVarB T\<rfloor> \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> TVar i"
| wf_Top: "\<Gamma> \<turnstile>\<^bsub>wf\<^esub> Top"
| wf_arrow: "\<Gamma> \<turnstile>\<^bsub>wf\<^esub> T \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> U \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> T \<rightarrow> U"
| wf_all: "\<Gamma> \<turnstile>\<^bsub>wf\<^esub> T \<Longrightarrow> TVarB T \<Colon> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> U \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> (\<forall><:T. U)"

inductive
  well_formedE :: "env \<Rightarrow> bool"  ("_ \<turnstile>\<^bsub>wf\<^esub>" [50] 50)
  and well_formedB :: "env \<Rightarrow> binding \<Rightarrow> bool"  ("_ \<turnstile>\<^bsub>wfB\<^esub> _" [50, 50] 50)
where
  "\<Gamma> \<turnstile>\<^bsub>wfB\<^esub> B \<equiv> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> type_ofB B"
| wf_Nil: "[] \<turnstile>\<^bsub>wf\<^esub>"
| wf_Cons: "\<Gamma> \<turnstile>\<^bsub>wfB\<^esub> B \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> \<Longrightarrow> B \<Colon> \<Gamma> \<turnstile>\<^bsub>wf\<^esub>"

inductive_cases well_formed_cases:
  "\<Gamma> \<turnstile>\<^bsub>wf\<^esub> TVar i"
  "\<Gamma> \<turnstile>\<^bsub>wf\<^esub> Top"
  "\<Gamma> \<turnstile>\<^bsub>wf\<^esub> T \<rightarrow> U"
  "\<Gamma> \<turnstile>\<^bsub>wf\<^esub> (\<forall><:T. U)"

inductive_cases well_formedE_cases:
  "B \<Colon> \<Gamma> \<turnstile>\<^bsub>wf\<^esub>"

inductive
  subtyping :: "env \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool"  ("_ \<turnstile> _ <: _" [50, 50, 50] 50)
where
  SA_Top: "\<Gamma> \<turnstile>\<^bsub>wf\<^esub> \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> S \<Longrightarrow> \<Gamma> \<turnstile> S <: Top"
| SA_refl_TVar: "\<Gamma> \<turnstile>\<^bsub>wf\<^esub> \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>wf\<^esub> TVar i \<Longrightarrow> \<Gamma> \<turnstile> TVar i <: TVar i"
| SA_trans_TVar: "\<Gamma>\<langle>i\<rangle> = \<lfloor>TVarB U\<rfloor> \<Longrightarrow>
    \<Gamma> \<turnstile> \<up>\<^isub>\<tau> (Suc i) 0 U <: T \<Longrightarrow> \<Gamma> \<turnstile> TVar i <: T"
| SA_arrow: "\<Gamma> \<turnstile> T\<^isub>1 <: S\<^isub>1 \<Longrightarrow> \<Gamma> \<turnstile> S\<^isub>2 <: T\<^isub>2 \<Longrightarrow> \<Gamma> \<turnstile> S\<^isub>1 \<rightarrow> S\<^isub>2 <: T\<^isub>1 \<rightarrow> T\<^isub>2"
| SA_all: "\<Gamma> \<turnstile> T\<^isub>1 <: S\<^isub>1 \<Longrightarrow> TVarB T\<^isub>1 \<Colon> \<Gamma> \<turnstile> S\<^isub>2 <: T\<^isub>2 \<Longrightarrow>
    \<Gamma> \<turnstile> (\<forall><:S\<^isub>1. S\<^isub>2) <: (\<forall><:T\<^isub>1. T\<^isub>2)"

inductive
  typing :: "env \<Rightarrow> trm \<Rightarrow> type \<Rightarrow> bool"    ("_ \<turnstile> _ : _" [50, 50, 50] 50)
where
  T_Var: "\<Gamma> \<turnstile>\<^bsub>wf\<^esub> \<Longrightarrow> \<Gamma>\<langle>i\<rangle> = \<lfloor>VarB U\<rfloor> \<Longrightarrow> T = \<up>\<^isub>\<tau> (Suc i) 0 U \<Longrightarrow> \<Gamma> \<turnstile> Var i : T"
| T_Abs: "VarB T\<^isub>1 \<Colon> \<Gamma> \<turnstile> t\<^isub>2 : T\<^isub>2 \<Longrightarrow> \<Gamma> \<turnstile> (\<lambda>:T\<^isub>1. t\<^isub>2) : T\<^isub>1 \<rightarrow> \<down>\<^isub>\<tau> 1 0 T\<^isub>2"
| T_App: "\<Gamma> \<turnstile> t\<^isub>1 : T\<^isub>11 \<rightarrow> T\<^isub>12 \<Longrightarrow> \<Gamma> \<turnstile> t\<^isub>2 : T\<^isub>11 \<Longrightarrow> \<Gamma> \<turnstile> t\<^isub>1 \<bullet> t\<^isub>2 : T\<^isub>12"
| T_TAbs: "TVarB T\<^isub>1 \<Colon> \<Gamma> \<turnstile> t\<^isub>2 : T\<^isub>2 \<Longrightarrow> \<Gamma> \<turnstile> (\<lambda><:T\<^isub>1. t\<^isub>2) : (\<forall><:T\<^isub>1. T\<^isub>2)"
| T_TApp: "\<Gamma> \<turnstile> t\<^isub>1 : (\<forall><:T\<^isub>11. T\<^isub>12) \<Longrightarrow> \<Gamma> \<turnstile> T\<^isub>2 <: T\<^isub>11 \<Longrightarrow>
    \<Gamma> \<turnstile> t\<^isub>1 \<bullet>\<^isub>\<tau> T\<^isub>2 : T\<^isub>12[0 \<mapsto>\<^isub>\<tau> T\<^isub>2]\<^isub>\<tau>"
| T_Sub: "\<Gamma> \<turnstile> t : S \<Longrightarrow> \<Gamma> \<turnstile> S <: T \<Longrightarrow> \<Gamma> \<turnstile> t : T"

code_pred [inductify, skip_proof, specialise] typing .

thm typing.equation

values 6 "{(E, t, T). typing E t T}"

subsection {* Higher-order predicate *}

code_pred [inductify] mapB .

subsection {* Multiple instances *}

inductive subtype_refl' where
  "\<Gamma> \<turnstile> t : T ==> \<not> (\<Gamma> \<turnstile> T <: T) ==> subtype_refl' t T"

code_pred (modes: i => i => bool, o => i => bool, i => o => bool, o => o => bool) [inductify] subtype_refl' .

thm subtype_refl'.equation


end
