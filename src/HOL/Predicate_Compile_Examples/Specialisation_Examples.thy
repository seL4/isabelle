theory Specialisation_Examples
imports Main "HOL-Library.Predicate_Compile_Alternative_Defs"
begin

declare [[values_timeout = 960.0]]

section \<open>Specialisation Examples\<close>

primrec nth_el'
where
  "nth_el' [] i = None"
| "nth_el' (x # xs) i = (case i of 0 => Some x | Suc j => nth_el' xs j)"

definition
  "greater_than_index xs = (\<forall>i x. nth_el' xs i = Some x --> x > i)"

code_pred (expected_modes: i => bool) [inductify, skip_proof, specialise] greater_than_index .
ML_val \<open>Core_Data.intros_of \<^context> \<^const_name>\<open>specialised_nth_el'P\<close>\<close>

thm greater_than_index.equation

values [expected "{()}"] "{x. greater_than_index [1,2,4,6]}"
values [expected "{}"] "{x. greater_than_index [0,2,3,2]}"

subsection \<open>Common subterms\<close>

text \<open>If a predicate is called with common subterms as arguments,
  this predicate should be specialised. 
\<close>

definition max_nat :: "nat => nat => nat"
  where "max_nat a b = (if a <= b then b else a)"

lemma [code_pred_inline]:
  "max = max_nat"
by (simp add: fun_eq_iff max_def max_nat_def)

definition
  "max_of_my_Suc x = max x (Suc x)"

text \<open>In this example, max is specialised, hence the mode o => i => bool is possible\<close>

code_pred (modes: o => i => bool) [inductify, specialise, skip_proof] max_of_my_Suc .

thm max_of_my_SucP.equation

ML_val \<open>Core_Data.intros_of \<^context> \<^const_name>\<open>specialised_max_natP\<close>\<close>

values "{x. max_of_my_SucP x 6}"

subsection \<open>Sorts\<close>

inductive sorted :: "'a::linorder list \<Rightarrow> bool" where
  Nil [simp]: "sorted []"
| Cons: "\<forall>y\<in>set xs. x \<le> y \<Longrightarrow> sorted xs \<Longrightarrow> sorted (x # xs)"

lemma sorted_single [simp]: "sorted [x]"
by (rule sorted.Cons) auto

lemma sorted_many: "x \<le> y \<Longrightarrow> sorted (y # zs) \<Longrightarrow> sorted (x # y # zs)"
by (rule sorted.Cons) (cases "y # zs" rule: sorted.cases, auto)

lemma sorted_many_eq [simp]:
  "sorted (x # y # zs) \<longleftrightarrow> x \<le> y \<and> sorted (y # zs)"
by (auto intro: sorted_many elim: sorted.cases)

declare sorted.Nil [code_pred_intro]
  sorted_single [code_pred_intro]
  sorted_many [code_pred_intro]

code_pred sorted
proof -
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
      case (Cons y zs)
      show ?thesis
      proof (rule 3)
        from Cons \<open>xa = x # xs\<close> show "xa = x # y # zs" by simp
        with \<open>sorted xa\<close> show "x \<le> y" and "sorted (y # zs)" by simp_all
      qed
    qed
  qed
qed
thm sorted.equation


section \<open>Specialisation in POPLmark theory\<close>

notation
  Some (\<open>\<lfloor>_\<rfloor>\<close>)

notation
  None (\<open>\<bottom>\<close>)

notation
  length (\<open>\<parallel>_\<parallel>\<close>)

notation
  Cons (\<open>_ \<Colon>/ _\<close> [66, 65] 65)

primrec
  nth_el :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" (\<open>_\<langle>_\<rangle>\<close> [90, 0] 91)
where
  "[]\<langle>i\<rangle> = \<bottom>"
| "(x # xs)\<langle>i\<rangle> = (case i of 0 \<Rightarrow> \<lfloor>x\<rfloor> | Suc j \<Rightarrow> xs \<langle>j\<rangle>)"

primrec assoc :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b option" (\<open>_\<langle>_\<rangle>\<^sub>?\<close> [90, 0] 91)
where
  "[]\<langle>a\<rangle>\<^sub>? = \<bottom>"
| "(x # xs)\<langle>a\<rangle>\<^sub>? = (if fst x = a then \<lfloor>snd x\<rfloor> else xs\<langle>a\<rangle>\<^sub>?)"

primrec unique :: "('a \<times> 'b) list \<Rightarrow> bool"
where
  "unique [] = True"
| "unique (x # xs) = (xs\<langle>fst x\<rangle>\<^sub>? = \<bottom> \<and> unique xs)"

datatype type =
    TVar nat
  | Top
  | Fun type type    (infixr \<open>\<rightarrow>\<close> 200)
  | TyAll type type  (\<open>(3\<forall><:_./ _)\<close> [0, 10] 10)

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
  | Abs type trm   (\<open>(3\<lambda>:_./ _)\<close> [0, 10] 10)
  | TAbs type trm  (\<open>(3\<lambda><:_./ _)\<close> [0, 10] 10)
  | App trm trm    (infixl \<open>\<bullet>\<close> 200)
  | TApp trm type  (infixl \<open>\<bullet>\<^sub>\<tau>\<close> 200)

primrec liftT :: "nat \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> type" (\<open>\<up>\<^sub>\<tau>\<close>)
where
  "\<up>\<^sub>\<tau> n k (TVar i) = (if i < k then TVar i else TVar (i + n))"
| "\<up>\<^sub>\<tau> n k Top = Top"
| "\<up>\<^sub>\<tau> n k (T \<rightarrow> U) = \<up>\<^sub>\<tau> n k T \<rightarrow> \<up>\<^sub>\<tau> n k U"
| "\<up>\<^sub>\<tau> n k (\<forall><:T. U) = (\<forall><:\<up>\<^sub>\<tau> n k T. \<up>\<^sub>\<tau> n (k + 1) U)"

primrec lift :: "nat \<Rightarrow> nat \<Rightarrow> trm \<Rightarrow> trm" (\<open>\<up>\<close>)
where
  "\<up> n k (Var i) = (if i < k then Var i else Var (i + n))"
| "\<up> n k (\<lambda>:T. t) = (\<lambda>:\<up>\<^sub>\<tau> n k T. \<up> n (k + 1) t)"
| "\<up> n k (\<lambda><:T. t) = (\<lambda><:\<up>\<^sub>\<tau> n k T. \<up> n (k + 1) t)"
| "\<up> n k (s \<bullet> t) = \<up> n k s \<bullet> \<up> n k t"
| "\<up> n k (t \<bullet>\<^sub>\<tau> T) = \<up> n k t \<bullet>\<^sub>\<tau> \<up>\<^sub>\<tau> n k T"

primrec substTT :: "type \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> type"  (\<open>_[_ \<mapsto>\<^sub>\<tau> _]\<^sub>\<tau>\<close> [300, 0, 0] 300)
where
  "(TVar i)[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau> =
     (if k < i then TVar (i - 1) else if i = k then \<up>\<^sub>\<tau> k 0 S else TVar i)"
| "Top[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau> = Top"
| "(T \<rightarrow> U)[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau> = T[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau> \<rightarrow> U[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>"
| "(\<forall><:T. U)[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau> = (\<forall><:T[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>. U[k+1 \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>)"

primrec decT :: "nat \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> type"  (\<open>\<down>\<^sub>\<tau>\<close>)
where
  "\<down>\<^sub>\<tau> 0 k T = T"
| "\<down>\<^sub>\<tau> (Suc n) k T = \<down>\<^sub>\<tau> n k (T[k \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>)"

primrec subst :: "trm \<Rightarrow> nat \<Rightarrow> trm \<Rightarrow> trm"  (\<open>_[_ \<mapsto> _]\<close> [300, 0, 0] 300)
where
  "(Var i)[k \<mapsto> s] = (if k < i then Var (i - 1) else if i = k then \<up> k 0 s else Var i)"
| "(t \<bullet> u)[k \<mapsto> s] = t[k \<mapsto> s] \<bullet> u[k \<mapsto> s]"
| "(t \<bullet>\<^sub>\<tau> T)[k \<mapsto> s] = t[k \<mapsto> s] \<bullet>\<^sub>\<tau> \<down>\<^sub>\<tau> 1 k T"
| "(\<lambda>:T. t)[k \<mapsto> s] = (\<lambda>:\<down>\<^sub>\<tau> 1 k T. t[k+1 \<mapsto> s])"
| "(\<lambda><:T. t)[k \<mapsto> s] = (\<lambda><:\<down>\<^sub>\<tau> 1 k T. t[k+1 \<mapsto> s])"

primrec substT :: "trm \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> trm"    (\<open>_[_ \<mapsto>\<^sub>\<tau> _]\<close> [300, 0, 0] 300)
where
  "(Var i)[k \<mapsto>\<^sub>\<tau> S] = (if k < i then Var (i - 1) else Var i)"
| "(t \<bullet> u)[k \<mapsto>\<^sub>\<tau> S] = t[k \<mapsto>\<^sub>\<tau> S] \<bullet> u[k \<mapsto>\<^sub>\<tau> S]"
| "(t \<bullet>\<^sub>\<tau> T)[k \<mapsto>\<^sub>\<tau> S] = t[k \<mapsto>\<^sub>\<tau> S] \<bullet>\<^sub>\<tau> T[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>"
| "(\<lambda>:T. t)[k \<mapsto>\<^sub>\<tau> S] = (\<lambda>:T[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>. t[k+1 \<mapsto>\<^sub>\<tau> S])"
| "(\<lambda><:T. t)[k \<mapsto>\<^sub>\<tau> S] = (\<lambda><:T[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>. t[k+1 \<mapsto>\<^sub>\<tau> S])"

primrec liftE :: "nat \<Rightarrow> nat \<Rightarrow> env \<Rightarrow> env" (\<open>\<up>\<^sub>e\<close>)
where
  "\<up>\<^sub>e n k [] = []"
| "\<up>\<^sub>e n k (B \<Colon> \<Gamma>) = mapB (\<up>\<^sub>\<tau> n (k + \<parallel>\<Gamma>\<parallel>)) B \<Colon> \<up>\<^sub>e n k \<Gamma>"

primrec substE :: "env \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> env"  (\<open>_[_ \<mapsto>\<^sub>\<tau> _]\<^sub>e\<close> [300, 0, 0] 300)
where
  "[][k \<mapsto>\<^sub>\<tau> T]\<^sub>e = []"
| "(B \<Colon> \<Gamma>)[k \<mapsto>\<^sub>\<tau> T]\<^sub>e = mapB (\<lambda>U. U[k + \<parallel>\<Gamma>\<parallel> \<mapsto>\<^sub>\<tau> T]\<^sub>\<tau>) B \<Colon> \<Gamma>[k \<mapsto>\<^sub>\<tau> T]\<^sub>e"

primrec decE :: "nat \<Rightarrow> nat \<Rightarrow> env \<Rightarrow> env"  (\<open>\<down>\<^sub>e\<close>)
where
  "\<down>\<^sub>e 0 k \<Gamma> = \<Gamma>"
| "\<down>\<^sub>e (Suc n) k \<Gamma> = \<down>\<^sub>e n k (\<Gamma>[k \<mapsto>\<^sub>\<tau> Top]\<^sub>e)"

inductive
  well_formed :: "env \<Rightarrow> type \<Rightarrow> bool"  (\<open>_ \<turnstile>\<^sub>w\<^sub>f _\<close> [50, 50] 50)
where
  wf_TVar: "\<Gamma>\<langle>i\<rangle> = \<lfloor>TVarB T\<rfloor> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f TVar i"
| wf_Top: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f Top"
| wf_arrow: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f U \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<rightarrow> U"
| wf_all: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> TVarB T \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f U \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f (\<forall><:T. U)"

inductive
  well_formedE :: "env \<Rightarrow> bool"  (\<open>_ \<turnstile>\<^sub>w\<^sub>f\<close> [50] 50)
  and well_formedB :: "env \<Rightarrow> binding \<Rightarrow> bool"  (\<open>_ \<turnstile>\<^sub>w\<^sub>f\<^sub>B _\<close> [50, 50] 50)
where
  "\<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>B B \<equiv> \<Gamma> \<turnstile>\<^sub>w\<^sub>f type_ofB B"
| wf_Nil: "[] \<turnstile>\<^sub>w\<^sub>f"
| wf_Cons: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>B B \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"

inductive_cases well_formed_cases:
  "\<Gamma> \<turnstile>\<^sub>w\<^sub>f TVar i"
  "\<Gamma> \<turnstile>\<^sub>w\<^sub>f Top"
  "\<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<rightarrow> U"
  "\<Gamma> \<turnstile>\<^sub>w\<^sub>f (\<forall><:T. U)"

inductive_cases well_formedE_cases:
  "B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"

inductive
  subtyping :: "env \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool"  (\<open>_ \<turnstile> _ <: _\<close> [50, 50, 50] 50)
where
  SA_Top: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f S \<Longrightarrow> \<Gamma> \<turnstile> S <: Top"
| SA_refl_TVar: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f TVar i \<Longrightarrow> \<Gamma> \<turnstile> TVar i <: TVar i"
| SA_trans_TVar: "\<Gamma>\<langle>i\<rangle> = \<lfloor>TVarB U\<rfloor> \<Longrightarrow>
    \<Gamma> \<turnstile> \<up>\<^sub>\<tau> (Suc i) 0 U <: T \<Longrightarrow> \<Gamma> \<turnstile> TVar i <: T"
| SA_arrow: "\<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile> S\<^sub>2 <: T\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> S\<^sub>1 \<rightarrow> S\<^sub>2 <: T\<^sub>1 \<rightarrow> T\<^sub>2"
| SA_all: "\<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 \<Longrightarrow> TVarB T\<^sub>1 \<Colon> \<Gamma> \<turnstile> S\<^sub>2 <: T\<^sub>2 \<Longrightarrow>
    \<Gamma> \<turnstile> (\<forall><:S\<^sub>1. S\<^sub>2) <: (\<forall><:T\<^sub>1. T\<^sub>2)"

inductive
  typing :: "env \<Rightarrow> trm \<Rightarrow> type \<Rightarrow> bool"    (\<open>_ \<turnstile> _ : _\<close> [50, 50, 50] 50)
where
  T_Var: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma>\<langle>i\<rangle> = \<lfloor>VarB U\<rfloor> \<Longrightarrow> T = \<up>\<^sub>\<tau> (Suc i) 0 U \<Longrightarrow> \<Gamma> \<turnstile> Var i : T"
| T_Abs: "VarB T\<^sub>1 \<Colon> \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> (\<lambda>:T\<^sub>1. t\<^sub>2) : T\<^sub>1 \<rightarrow> \<down>\<^sub>\<tau> 1 0 T\<^sub>2"
| T_App: "\<Gamma> \<turnstile> t\<^sub>1 : T\<^sub>11 \<rightarrow> T\<^sub>12 \<Longrightarrow> \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>11 \<Longrightarrow> \<Gamma> \<turnstile> t\<^sub>1 \<bullet> t\<^sub>2 : T\<^sub>12"
| T_TAbs: "TVarB T\<^sub>1 \<Colon> \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> (\<lambda><:T\<^sub>1. t\<^sub>2) : (\<forall><:T\<^sub>1. T\<^sub>2)"
| T_TApp: "\<Gamma> \<turnstile> t\<^sub>1 : (\<forall><:T\<^sub>11. T\<^sub>12) \<Longrightarrow> \<Gamma> \<turnstile> T\<^sub>2 <: T\<^sub>11 \<Longrightarrow>
    \<Gamma> \<turnstile> t\<^sub>1 \<bullet>\<^sub>\<tau> T\<^sub>2 : T\<^sub>12[0 \<mapsto>\<^sub>\<tau> T\<^sub>2]\<^sub>\<tau>"
| T_Sub: "\<Gamma> \<turnstile> t : S \<Longrightarrow> \<Gamma> \<turnstile> S <: T \<Longrightarrow> \<Gamma> \<turnstile> t : T"

code_pred [inductify, skip_proof, specialise] typing .

thm typing.equation

values 6 "{(E, t, T). typing E t T}"

subsection \<open>Higher-order predicate\<close>

code_pred [inductify] mapB .

subsection \<open>Multiple instances\<close>

inductive subtype_refl' where
  "\<Gamma> \<turnstile> t : T ==> \<not> (\<Gamma> \<turnstile> T <: T) ==> subtype_refl' t T"

code_pred (modes: i => i => bool, o => i => bool, i => o => bool, o => o => bool) [inductify] subtype_refl' .

thm subtype_refl'.equation


end
