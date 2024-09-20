(*  Title:      HOL/Induct/QuoNestedDataType.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2004  University of Cambridge
*)

section\<open>Quotienting a Free Algebra Involving Nested Recursion\<close>

text \<open>This is the development promised in Lawrence Paulson's paper ``Defining functions on equivalence classes''
\emph{ACM Transactions on Computational Logic} \textbf{7}:40 (2006), 658--675,
illustrating bare-bones quotient constructions. Any comparison using lifting and transfer
should be done in a separate theory.\<close>

theory QuoNestedDataType imports Main begin

subsection\<open>Defining the Free Algebra\<close>

text\<open>Messages with encryption and decryption as free constructors.\<close>
datatype
     freeExp = VAR  nat
             | PLUS  freeExp freeExp
             | FNCALL  nat "freeExp list"

datatype_compat freeExp

text\<open>The equivalence relation, which makes PLUS associative.\<close>

text\<open>The first rule is the desired equation. The next three rules
make the equations applicable to subterms. The last two rules are symmetry
and transitivity.\<close>
inductive_set
  exprel :: "(freeExp * freeExp) set"
  and exp_rel :: "[freeExp, freeExp] => bool"  (infixl \<open>\<sim>\<close> 50)
  where
    "X \<sim> Y \<equiv> (X,Y) \<in> exprel"
  | ASSOC: "PLUS X (PLUS Y Z) \<sim> PLUS (PLUS X Y) Z"
  | VAR: "VAR N \<sim> VAR N"
  | PLUS: "\<lbrakk>X \<sim> X'; Y \<sim> Y'\<rbrakk> \<Longrightarrow> PLUS X Y \<sim> PLUS X' Y'"
  | FNCALL: "(Xs,Xs') \<in> listrel exprel \<Longrightarrow> FNCALL F Xs \<sim> FNCALL F Xs'"
  | SYM:   "X \<sim> Y \<Longrightarrow> Y \<sim> X"
  | TRANS: "\<lbrakk>X \<sim> Y; Y \<sim> Z\<rbrakk> \<Longrightarrow> X \<sim> Z"
  monos listrel_mono


text\<open>Proving that it is an equivalence relation\<close>

lemma exprel_refl: "X \<sim> X"
  and list_exprel_refl: "(Xs,Xs) \<in> listrel(exprel)"
  by (induct X and Xs rule: compat_freeExp.induct compat_freeExp_list.induct)
    (blast intro: exprel.intros listrel.intros)+

theorem equiv_exprel: "equiv UNIV exprel"
proof (rule equivI)
  show "refl exprel" by (simp add: refl_on_def exprel_refl)
  show "sym exprel" by (simp add: sym_def, blast intro: exprel.SYM)
  show "trans exprel" by (simp add: trans_def, blast intro: exprel.TRANS)
qed

theorem equiv_list_exprel: "equiv UNIV (listrel exprel)"
  using equiv_listrel [OF equiv_exprel] by simp

lemma FNCALL_Cons:
  "\<lbrakk>X \<sim> X'; (Xs,Xs') \<in> listrel(exprel)\<rbrakk> \<Longrightarrow> FNCALL F (X#Xs) \<sim> FNCALL F (X'#Xs')"
  by (blast intro: exprel.intros listrel.intros) 


subsection\<open>Some Functions on the Free Algebra\<close>

subsubsection\<open>The Set of Variables\<close>

text\<open>A function to return the set of variables present in a message.  It will
be lifted to the initial algebra, to serve as an example of that process.
Note that the "free" refers to the free datatype rather than to the concept
of a free variable.\<close>
primrec freevars :: "freeExp \<Rightarrow> nat set" and freevars_list :: "freeExp list \<Rightarrow> nat set"
  where
  "freevars (VAR N) = {N}"
| "freevars (PLUS X Y) = freevars X \<union> freevars Y"
| "freevars (FNCALL F Xs) = freevars_list Xs"

| "freevars_list [] = {}"
| "freevars_list (X # Xs) = freevars X \<union> freevars_list Xs"

text\<open>This theorem lets us prove that the vars function respects the
equivalence relation.  It also helps us prove that Variable
  (the abstract constructor) is injective\<close>
theorem exprel_imp_eq_freevars: "U \<sim> V \<Longrightarrow> freevars U = freevars V"
proof (induct set: exprel)
  case (FNCALL Xs Xs' F)
  then show ?case
    by (induct rule: listrel.induct) auto
qed (simp_all add: Un_assoc)


subsubsection\<open>Functions for Freeness\<close>

text\<open>A discriminator function to distinguish vars, sums and function calls\<close>
primrec freediscrim :: "freeExp \<Rightarrow> int" where
  "freediscrim (VAR N) = 0"
| "freediscrim (PLUS X Y) = 1"
| "freediscrim (FNCALL F Xs) = 2"

theorem exprel_imp_eq_freediscrim:
     "U \<sim> V \<Longrightarrow> freediscrim U = freediscrim V"
  by (induct set: exprel) auto


text\<open>This function, which returns the function name, is used to
prove part of the injectivity property for FnCall.\<close>
primrec freefun :: "freeExp \<Rightarrow> nat" where
  "freefun (VAR N) = 0"
| "freefun (PLUS X Y) = 0"
| "freefun (FNCALL F Xs) = F"

theorem exprel_imp_eq_freefun:
     "U \<sim> V \<Longrightarrow> freefun U = freefun V"
  by (induct set: exprel) (simp_all add: listrel.intros)


text\<open>This function, which returns the list of function arguments, is used to
prove part of the injectivity property for FnCall.\<close>
primrec freeargs :: "freeExp \<Rightarrow> freeExp list" where
  "freeargs (VAR N) = []"
| "freeargs (PLUS X Y) = []"
| "freeargs (FNCALL F Xs) = Xs"


theorem exprel_imp_eqv_freeargs:
  assumes "U \<sim> V"
  shows "(freeargs U, freeargs V) \<in> listrel exprel"
  using assms
proof induction
  case (FNCALL Xs Xs' F)
  then show ?case
    by (simp add: listrel_iff_nth)
next
  case (SYM X Y)
  then show ?case
    by (meson equivE equiv_list_exprel symD)
next
  case (TRANS X Y Z)
  then show ?case
    by (meson equivE equiv_list_exprel transD)
qed (use listrel.simps in auto)


subsection\<open>The Initial Algebra: A Quotiented Message Type\<close>

definition "Exp = UNIV//exprel"

typedef exp = Exp
  morphisms Rep_Exp Abs_Exp
  unfolding Exp_def by (auto simp add: quotient_def)

text\<open>The abstract message constructors\<close>

definition
  Var :: "nat \<Rightarrow> exp" where
  "Var N = Abs_Exp(exprel``{VAR N})"

definition
  Plus :: "[exp,exp] \<Rightarrow> exp" where
   "Plus X Y =
       Abs_Exp (\<Union>U \<in> Rep_Exp X. \<Union>V \<in> Rep_Exp Y. exprel``{PLUS U V})"

definition
  FnCall :: "[nat, exp list] \<Rightarrow> exp" where
   "FnCall F Xs =
       Abs_Exp (\<Union>Us \<in> listset (map Rep_Exp Xs). exprel``{FNCALL F Us})"


text\<open>Reduces equality of equivalence classes to the \<^term>\<open>exprel\<close> relation:
  \<^term>\<open>(exprel``{x} = exprel``{y}) = ((x,y) \<in> exprel)\<close>\<close>
lemmas equiv_exprel_iff = eq_equiv_class_iff [OF equiv_exprel UNIV_I UNIV_I]

declare equiv_exprel_iff [simp]


text\<open>All equivalence classes belong to set of representatives\<close>
lemma exprel_in_Exp [simp]: "exprel``{U} \<in> Exp"
  by (simp add: Exp_def quotientI)

lemma inj_on_Abs_Exp: "inj_on Abs_Exp Exp"
  by (meson Abs_Exp_inject inj_onI)

text\<open>Reduces equality on abstractions to equality on representatives\<close>
declare inj_on_Abs_Exp [THEN inj_on_eq_iff, simp]

declare Abs_Exp_inverse [simp]


text\<open>Case analysis on the representation of a exp as an equivalence class.\<close>
lemma eq_Abs_Exp [case_names Abs_Exp, cases type: exp]:
     "(\<And>U. z = Abs_Exp (exprel``{U}) \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis Abs_Exp_cases Exp_def quotientE)


subsection\<open>Every list of abstract expressions can be expressed in terms of a
  list of concrete expressions\<close>

definition
  Abs_ExpList :: "freeExp list => exp list" where
  "Abs_ExpList Xs \<equiv> map (\<lambda>U. Abs_Exp(exprel``{U})) Xs"

lemma Abs_ExpList_Nil [simp]: "Abs_ExpList [] = []"
  by (simp add: Abs_ExpList_def)

lemma Abs_ExpList_Cons [simp]:
  "Abs_ExpList (X#Xs) = Abs_Exp (exprel``{X}) # Abs_ExpList Xs"
  by (simp add: Abs_ExpList_def)

lemma ExpList_rep: "\<exists>Us. z = Abs_ExpList Us"
  by (smt (verit, del_insts) Abs_ExpList_def eq_Abs_Exp ex_map_conv)


subsubsection\<open>Characteristic Equations for the Abstract Constructors\<close>

lemma Plus: "Plus (Abs_Exp(exprel``{U})) (Abs_Exp(exprel``{V})) = 
             Abs_Exp (exprel``{PLUS U V})"
proof -
  have "(\<lambda>U V. exprel``{PLUS U V}) respects2 exprel"
    by (auto simp add: congruent2_def exprel.PLUS)
  thus ?thesis
    by (simp add: Plus_def UN_equiv_class2 [OF equiv_exprel equiv_exprel])
qed

text\<open>It is not clear what to do with FnCall: it's argument is an abstraction
of an \<^typ>\<open>exp list\<close>. Is it just Nil or Cons? What seems to work best is to
regard an \<^typ>\<open>exp list\<close> as a \<^term>\<open>listrel exprel\<close> equivalence class\<close>

text\<open>This theorem is easily proved but never used. There's no obvious way
even to state the analogous result, \<open>FnCall_Cons\<close>.\<close>
lemma FnCall_Nil: "FnCall F [] = Abs_Exp (exprel``{FNCALL F []})"
  by (simp add: FnCall_def)

lemma FnCall_respects: 
     "(\<lambda>Us. exprel``{FNCALL F Us}) respects (listrel exprel)"
  by (auto simp add: congruent_def exprel.FNCALL)

lemma FnCall_sing:
     "FnCall F [Abs_Exp(exprel``{U})] = Abs_Exp (exprel``{FNCALL F [U]})"
proof -
  have "(\<lambda>U. exprel``{FNCALL F [U]}) respects exprel"
    by (auto simp add: congruent_def FNCALL_Cons listrel.intros)
  thus ?thesis
    by (simp add: FnCall_def UN_equiv_class [OF equiv_exprel])
qed

lemma listset_Rep_Exp_Abs_Exp:
     "listset (map Rep_Exp (Abs_ExpList Us)) = listrel exprel``{Us}"
  by (induct Us) (simp_all add: listrel_Cons Abs_ExpList_def)

lemma FnCall:
     "FnCall F (Abs_ExpList Us) = Abs_Exp (exprel``{FNCALL F Us})"
proof -
  have "(\<lambda>Us. exprel``{FNCALL F Us}) respects (listrel exprel)"
    by (auto simp add: congruent_def exprel.FNCALL)
  thus ?thesis
    by (simp add: FnCall_def UN_equiv_class [OF equiv_list_exprel]
                  listset_Rep_Exp_Abs_Exp)
qed


text\<open>Establishing this equation is the point of the whole exercise\<close>
theorem Plus_assoc: "Plus X (Plus Y Z) = Plus (Plus X Y) Z"
  by (cases X, cases Y, cases Z, simp add: Plus exprel.ASSOC)



subsection\<open>The Abstract Function to Return the Set of Variables\<close>

definition
  vars :: "exp \<Rightarrow> nat set" where "vars X \<equiv> (\<Union>U \<in> Rep_Exp X. freevars U)"

lemma vars_respects: "freevars respects exprel"
by (auto simp add: congruent_def exprel_imp_eq_freevars) 

text\<open>The extension of the function \<^term>\<open>vars\<close> to lists\<close>
primrec vars_list :: "exp list \<Rightarrow> nat set" where
  "vars_list []    = {}"
| "vars_list(E#Es) = vars E \<union> vars_list Es"


text\<open>Now prove the three equations for \<^term>\<open>vars\<close>\<close>

lemma vars_Variable [simp]: "vars (Var N) = {N}"
by (simp add: vars_def Var_def 
              UN_equiv_class [OF equiv_exprel vars_respects]) 
 
lemma vars_Plus [simp]: "vars (Plus X Y) = vars X \<union> vars Y"
proof -
  have "\<And>U V. \<lbrakk>X = Abs_Exp (exprel``{U}); Y = Abs_Exp (exprel``{V})\<rbrakk>
               \<Longrightarrow> vars (Plus X Y) = vars X \<union> vars Y"
    by (simp add: vars_def Plus UN_equiv_class [OF equiv_exprel vars_respects]) 
  then show ?thesis
    by (meson eq_Abs_Exp)
qed

lemma vars_FnCall [simp]: "vars (FnCall F Xs) = vars_list Xs"
proof -
  have "vars (Abs_Exp (exprel``{FNCALL F Us})) = vars_list (Abs_ExpList Us)" for Us
    by (induct Us) (auto simp: vars_def UN_equiv_class [OF equiv_exprel vars_respects])
  then show ?thesis
    by (metis ExpList_rep FnCall)
qed

lemma vars_FnCall_Nil: "vars (FnCall F Nil) = {}" 
  by simp

lemma vars_FnCall_Cons: "vars (FnCall F (X#Xs)) = vars X \<union> vars_list Xs"
  by simp


subsection\<open>Injectivity Properties of Some Constructors\<close>

lemma VAR_imp_eq: "VAR m \<sim> VAR n \<Longrightarrow> m = n"
  by (drule exprel_imp_eq_freevars, simp)

text\<open>Can also be proved using the function \<^term>\<open>vars\<close>\<close>
lemma Var_Var_eq [iff]: "(Var m = Var n) = (m = n)"
  by (auto simp add: Var_def exprel_refl dest: VAR_imp_eq)

lemma VAR_neqv_PLUS: "VAR m \<sim> PLUS X Y \<Longrightarrow> False"
  using exprel_imp_eq_freediscrim by force

theorem Var_neq_Plus [iff]: "Var N \<noteq> Plus X Y"
proof -
  have "\<And>U V. \<lbrakk>X = Abs_Exp (exprel``{U}); Y = Abs_Exp (exprel``{V})\<rbrakk> \<Longrightarrow> Var N \<noteq> Plus X Y"
    using Plus VAR_neqv_PLUS Var_def by force
  then show ?thesis
    by (meson eq_Abs_Exp)
qed

theorem Var_neq_FnCall [iff]: "Var N \<noteq> FnCall F Xs"
proof -
  have "\<And>Us. Var N \<noteq> FnCall F (Abs_ExpList Us)"
    using FnCall Var_def exprel_imp_eq_freediscrim by fastforce
  then show ?thesis
    by (metis ExpList_rep)
qed

subsection\<open>Injectivity of \<^term>\<open>FnCall\<close>\<close>

definition
  "fun" :: "exp \<Rightarrow> nat"
  where "fun X \<equiv> the_elem (\<Union>U \<in> Rep_Exp X. {freefun U})"

lemma fun_respects: "(\<lambda>U. {freefun U}) respects exprel"
  by (auto simp add: congruent_def exprel_imp_eq_freefun) 

lemma fun_FnCall [simp]: "fun (FnCall F Xs) = F"
proof -
  have "\<And>Us. fun (FnCall F (Abs_ExpList Us)) = F"
    using FnCall UN_equiv_class [OF equiv_exprel] fun_def fun_respects by fastforce
  then show ?thesis
    by (metis ExpList_rep)
qed

definition
  args :: "exp \<Rightarrow> exp list" where
  "args X = the_elem (\<Union>U \<in> Rep_Exp X. {Abs_ExpList (freeargs U)})"

text\<open>This result can probably be generalized to arbitrary equivalence
relations, but with little benefit here.\<close>
lemma Abs_ExpList_eq:
     "(y, z) \<in> listrel exprel \<Longrightarrow> Abs_ExpList (y) = Abs_ExpList (z)"
  by (induct set: listrel) simp_all

lemma args_respects: "(\<lambda>U. {Abs_ExpList (freeargs U)}) respects exprel"
  by (auto simp add: congruent_def Abs_ExpList_eq exprel_imp_eqv_freeargs) 

lemma args_FnCall [simp]: "args (FnCall F Xs) = Xs"
proof -
  have "\<And>Us. Xs = Abs_ExpList Us \<Longrightarrow> args (FnCall F Xs) = Xs"
    by (simp add: FnCall args_def UN_equiv_class [OF equiv_exprel args_respects])
  then show ?thesis
    by (metis ExpList_rep)
qed

lemma FnCall_FnCall_eq [iff]: "(FnCall F Xs = FnCall F' Xs') \<longleftrightarrow> (F=F' \<and> Xs=Xs')"
  by (metis args_FnCall fun_FnCall) 


subsection\<open>The Abstract Discriminator\<close>
text\<open>However, as \<open>FnCall_Var_neq_Var\<close> illustrates, we don't need this
function in order to prove discrimination theorems.\<close>

definition
  discrim :: "exp \<Rightarrow> int" where
  "discrim X = the_elem (\<Union>U \<in> Rep_Exp X. {freediscrim U})"

lemma discrim_respects: "(\<lambda>U. {freediscrim U}) respects exprel"
by (auto simp add: congruent_def exprel_imp_eq_freediscrim) 

text\<open>Now prove the four equations for \<^term>\<open>discrim\<close>\<close>

lemma discrim_Var [simp]: "discrim (Var N) = 0"
  by (simp add: discrim_def Var_def UN_equiv_class [OF equiv_exprel discrim_respects]) 

lemma discrim_Plus [simp]: "discrim (Plus X Y) = 1"
proof -
  have "\<And>U V. \<lbrakk>X = Abs_Exp (exprel``{U}); Y = Abs_Exp (exprel``{V})\<rbrakk> \<Longrightarrow> discrim (Plus X Y) = 1"
    by (simp add: discrim_def Plus  UN_equiv_class [OF equiv_exprel discrim_respects]) 
  then show ?thesis
    by (meson eq_Abs_Exp)
qed

lemma discrim_FnCall [simp]: "discrim (FnCall F Xs) = 2"
proof -
  have "discrim (FnCall F (Abs_ExpList Us)) = 2" for Us
    by (simp add: discrim_def FnCall UN_equiv_class [OF equiv_exprel discrim_respects]) 
  then show ?thesis
    by (metis ExpList_rep)
qed

text\<open>The structural induction rule for the abstract type\<close>
theorem exp_inducts:
  assumes V:    "\<And>nat. P1 (Var nat)"
      and P:    "\<And>exp1 exp2. \<lbrakk>P1 exp1; P1 exp2\<rbrakk> \<Longrightarrow> P1 (Plus exp1 exp2)"
      and F:    "\<And>nat list. P2 list \<Longrightarrow> P1 (FnCall nat list)"
      and Nil:  "P2 []"
      and Cons: "\<And>exp list. \<lbrakk>P1 exp; P2 list\<rbrakk> \<Longrightarrow> P2 (exp # list)"
  shows "P1 exp" and "P2 list"
proof -
  obtain U where exp: "exp = (Abs_Exp (exprel``{U}))" by (cases exp)
  obtain Us where list: "list = Abs_ExpList Us" by (metis ExpList_rep)
  have "P1 (Abs_Exp (exprel``{U}))" and "P2 (Abs_ExpList Us)"
  proof (induct U and Us rule: compat_freeExp.induct compat_freeExp_list.induct)
    case (VAR nat)
    with V show ?case by (simp add: Var_def) 
  next
    case (PLUS X Y)
    with P [of "Abs_Exp (exprel``{X})" "Abs_Exp (exprel``{Y})"]
    show ?case by (simp add: Plus) 
  next
    case (FNCALL nat list)
    with F [of "Abs_ExpList list"]
    show ?case by (simp add: FnCall) 
  next
    case Nil_freeExp
    with Nil show ?case by simp
  next
    case Cons_freeExp
    with Cons show ?case by simp
  qed
  with exp and list show "P1 exp" and "P2 list" by (simp_all only:)
qed

end
