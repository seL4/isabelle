(*  Title:      HOL/Induct/QuoNestedDataType.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2004  University of Cambridge
*)

header{*Quotienting a Free Algebra Involving Nested Recursion*}

theory QuoNestedDataType imports Main begin

subsection{*Defining the Free Algebra*}

text{*Messages with encryption and decryption as free constructors.*}
datatype
     freeExp = VAR  nat
             | PLUS  freeExp freeExp
             | FNCALL  nat "freeExp list"

text{*The equivalence relation, which makes PLUS associative.*}

text{*The first rule is the desired equation. The next three rules
make the equations applicable to subterms. The last two rules are symmetry
and transitivity.*}
inductive_set
  exprel :: "(freeExp * freeExp) set"
  and exp_rel :: "[freeExp, freeExp] => bool"  (infixl "\<sim>" 50)
  where
    "X \<sim> Y == (X,Y) \<in> exprel"
  | ASSOC: "PLUS X (PLUS Y Z) \<sim> PLUS (PLUS X Y) Z"
  | VAR: "VAR N \<sim> VAR N"
  | PLUS: "\<lbrakk>X \<sim> X'; Y \<sim> Y'\<rbrakk> \<Longrightarrow> PLUS X Y \<sim> PLUS X' Y'"
  | FNCALL: "(Xs,Xs') \<in> listrel exprel \<Longrightarrow> FNCALL F Xs \<sim> FNCALL F Xs'"
  | SYM:   "X \<sim> Y \<Longrightarrow> Y \<sim> X"
  | TRANS: "\<lbrakk>X \<sim> Y; Y \<sim> Z\<rbrakk> \<Longrightarrow> X \<sim> Z"
  monos listrel_mono


text{*Proving that it is an equivalence relation*}

lemma exprel_refl: "X \<sim> X"
  and list_exprel_refl: "(Xs,Xs) \<in> listrel(exprel)"
  by (induct X and Xs) (blast intro: exprel.intros listrel.intros)+

theorem equiv_exprel: "equiv UNIV exprel"
proof -
  have "refl exprel" by (simp add: refl_on_def exprel_refl)
  moreover have "sym exprel" by (simp add: sym_def, blast intro: exprel.SYM)
  moreover have "trans exprel" by (simp add: trans_def, blast intro: exprel.TRANS)
  ultimately show ?thesis by (simp add: equiv_def)
qed

theorem equiv_list_exprel: "equiv UNIV (listrel exprel)"
  using equiv_listrel [OF equiv_exprel] by simp


lemma FNCALL_Nil: "FNCALL F [] \<sim> FNCALL F []"
apply (rule exprel.intros) 
apply (rule listrel.intros) 
done

lemma FNCALL_Cons:
     "\<lbrakk>X \<sim> X'; (Xs,Xs') \<in> listrel(exprel)\<rbrakk>
      \<Longrightarrow> FNCALL F (X#Xs) \<sim> FNCALL F (X'#Xs')"
by (blast intro: exprel.intros listrel.intros) 



subsection{*Some Functions on the Free Algebra*}

subsubsection{*The Set of Variables*}

text{*A function to return the set of variables present in a message.  It will
be lifted to the initial algrebra, to serve as an example of that process.
Note that the "free" refers to the free datatype rather than to the concept
of a free variable.*}
primrec freevars :: "freeExp \<Rightarrow> nat set" 
  and freevars_list :: "freeExp list \<Rightarrow> nat set" where
  "freevars (VAR N) = {N}"
| "freevars (PLUS X Y) = freevars X \<union> freevars Y"
| "freevars (FNCALL F Xs) = freevars_list Xs"

| "freevars_list [] = {}"
| "freevars_list (X # Xs) = freevars X \<union> freevars_list Xs"

text{*This theorem lets us prove that the vars function respects the
equivalence relation.  It also helps us prove that Variable
  (the abstract constructor) is injective*}
theorem exprel_imp_eq_freevars: "U \<sim> V \<Longrightarrow> freevars U = freevars V"
apply (induct set: exprel) 
apply (erule_tac [4] listrel.induct) 
apply (simp_all add: Un_assoc)
done



subsubsection{*Functions for Freeness*}

text{*A discriminator function to distinguish vars, sums and function calls*}
primrec freediscrim :: "freeExp \<Rightarrow> int" where
  "freediscrim (VAR N) = 0"
| "freediscrim (PLUS X Y) = 1"
| "freediscrim (FNCALL F Xs) = 2"

theorem exprel_imp_eq_freediscrim:
     "U \<sim> V \<Longrightarrow> freediscrim U = freediscrim V"
  by (induct set: exprel) auto


text{*This function, which returns the function name, is used to
prove part of the injectivity property for FnCall.*}
primrec freefun :: "freeExp \<Rightarrow> nat" where
  "freefun (VAR N) = 0"
| "freefun (PLUS X Y) = 0"
| "freefun (FNCALL F Xs) = F"

theorem exprel_imp_eq_freefun:
     "U \<sim> V \<Longrightarrow> freefun U = freefun V"
  by (induct set: exprel) (simp_all add: listrel.intros)


text{*This function, which returns the list of function arguments, is used to
prove part of the injectivity property for FnCall.*}
primrec freeargs :: "freeExp \<Rightarrow> freeExp list" where
  "freeargs (VAR N) = []"
| "freeargs (PLUS X Y) = []"
| "freeargs (FNCALL F Xs) = Xs"

theorem exprel_imp_eqv_freeargs:
  assumes "U \<sim> V"
  shows "(freeargs U, freeargs V) \<in> listrel exprel"
proof -
  from equiv_list_exprel have sym: "sym (listrel exprel)" by (rule equivE)
  from equiv_list_exprel have trans: "trans (listrel exprel)" by (rule equivE)
  from assms show ?thesis
    apply induct
    apply (erule_tac [4] listrel.induct) 
    apply (simp_all add: listrel.intros)
    apply (blast intro: symD [OF sym])
    apply (blast intro: transD [OF trans])
    done
qed


subsection{*The Initial Algebra: A Quotiented Message Type*}

definition "Exp = UNIV//exprel"

typedef (open) exp = Exp
  morphisms Rep_Exp Abs_Exp
  unfolding Exp_def by (auto simp add: quotient_def)

text{*The abstract message constructors*}

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
       Abs_Exp (\<Union>Us \<in> listset (map Rep_Exp Xs). exprel `` {FNCALL F Us})"


text{*Reduces equality of equivalence classes to the @{term exprel} relation:
  @{term "(exprel `` {x} = exprel `` {y}) = ((x,y) \<in> exprel)"} *}
lemmas equiv_exprel_iff = eq_equiv_class_iff [OF equiv_exprel UNIV_I UNIV_I]

declare equiv_exprel_iff [simp]


text{*All equivalence classes belong to set of representatives*}
lemma [simp]: "exprel``{U} \<in> Exp"
by (auto simp add: Exp_def quotient_def intro: exprel_refl)

lemma inj_on_Abs_Exp: "inj_on Abs_Exp Exp"
apply (rule inj_on_inverseI)
apply (erule Abs_Exp_inverse)
done

text{*Reduces equality on abstractions to equality on representatives*}
declare inj_on_Abs_Exp [THEN inj_on_iff, simp]

declare Abs_Exp_inverse [simp]


text{*Case analysis on the representation of a exp as an equivalence class.*}
lemma eq_Abs_Exp [case_names Abs_Exp, cases type: exp]:
     "(!!U. z = Abs_Exp(exprel``{U}) ==> P) ==> P"
apply (rule Rep_Exp [of z, unfolded Exp_def, THEN quotientE])
apply (drule arg_cong [where f=Abs_Exp])
apply (auto simp add: Rep_Exp_inverse intro: exprel_refl)
done


subsection{*Every list of abstract expressions can be expressed in terms of a
  list of concrete expressions*}

definition
  Abs_ExpList :: "freeExp list => exp list" where
  "Abs_ExpList Xs = map (%U. Abs_Exp(exprel``{U})) Xs"

lemma Abs_ExpList_Nil [simp]: "Abs_ExpList [] == []"
by (simp add: Abs_ExpList_def)

lemma Abs_ExpList_Cons [simp]:
     "Abs_ExpList (X#Xs) == Abs_Exp (exprel``{X}) # Abs_ExpList Xs"
by (simp add: Abs_ExpList_def)

lemma ExpList_rep: "\<exists>Us. z = Abs_ExpList Us"
apply (induct z)
apply (rule_tac [2] z=a in eq_Abs_Exp)
apply (auto simp add: Abs_ExpList_def Cons_eq_map_conv intro: exprel_refl)
done

lemma eq_Abs_ExpList [case_names Abs_ExpList]:
     "(!!Us. z = Abs_ExpList Us ==> P) ==> P"
by (rule exE [OF ExpList_rep], blast) 


subsubsection{*Characteristic Equations for the Abstract Constructors*}

lemma Plus: "Plus (Abs_Exp(exprel``{U})) (Abs_Exp(exprel``{V})) = 
             Abs_Exp (exprel``{PLUS U V})"
proof -
  have "(\<lambda>U V. exprel `` {PLUS U V}) respects2 exprel"
    by (auto simp add: congruent2_def exprel.PLUS)
  thus ?thesis
    by (simp add: Plus_def UN_equiv_class2 [OF equiv_exprel equiv_exprel])
qed

text{*It is not clear what to do with FnCall: it's argument is an abstraction
of an @{typ "exp list"}. Is it just Nil or Cons? What seems to work best is to
regard an @{typ "exp list"} as a @{term "listrel exprel"} equivalence class*}

text{*This theorem is easily proved but never used. There's no obvious way
even to state the analogous result, @{text FnCall_Cons}.*}
lemma FnCall_Nil: "FnCall F [] = Abs_Exp (exprel``{FNCALL F []})"
  by (simp add: FnCall_def)

lemma FnCall_respects: 
     "(\<lambda>Us. exprel `` {FNCALL F Us}) respects (listrel exprel)"
  by (auto simp add: congruent_def exprel.FNCALL)

lemma FnCall_sing:
     "FnCall F [Abs_Exp(exprel``{U})] = Abs_Exp (exprel``{FNCALL F [U]})"
proof -
  have "(\<lambda>U. exprel `` {FNCALL F [U]}) respects exprel"
    by (auto simp add: congruent_def FNCALL_Cons listrel.intros)
  thus ?thesis
    by (simp add: FnCall_def UN_equiv_class [OF equiv_exprel])
qed

lemma listset_Rep_Exp_Abs_Exp:
     "listset (map Rep_Exp (Abs_ExpList Us)) = listrel exprel `` {Us}";
  by (induct Us) (simp_all add: listrel_Cons Abs_ExpList_def)

lemma FnCall:
     "FnCall F (Abs_ExpList Us) = Abs_Exp (exprel``{FNCALL F Us})"
proof -
  have "(\<lambda>Us. exprel `` {FNCALL F Us}) respects (listrel exprel)"
    by (auto simp add: congruent_def exprel.FNCALL)
  thus ?thesis
    by (simp add: FnCall_def UN_equiv_class [OF equiv_list_exprel]
                  listset_Rep_Exp_Abs_Exp)
qed


text{*Establishing this equation is the point of the whole exercise*}
theorem Plus_assoc: "Plus X (Plus Y Z) = Plus (Plus X Y) Z"
by (cases X, cases Y, cases Z, simp add: Plus exprel.ASSOC)



subsection{*The Abstract Function to Return the Set of Variables*}

definition
  vars :: "exp \<Rightarrow> nat set" where
  "vars X = (\<Union>U \<in> Rep_Exp X. freevars U)"

lemma vars_respects: "freevars respects exprel"
by (auto simp add: congruent_def exprel_imp_eq_freevars) 

text{*The extension of the function @{term vars} to lists*}
primrec vars_list :: "exp list \<Rightarrow> nat set" where
  "vars_list []    = {}"
| "vars_list(E#Es) = vars E \<union> vars_list Es"


text{*Now prove the three equations for @{term vars}*}

lemma vars_Variable [simp]: "vars (Var N) = {N}"
by (simp add: vars_def Var_def 
              UN_equiv_class [OF equiv_exprel vars_respects]) 
 
lemma vars_Plus [simp]: "vars (Plus X Y) = vars X \<union> vars Y"
apply (cases X, cases Y) 
apply (simp add: vars_def Plus 
                 UN_equiv_class [OF equiv_exprel vars_respects]) 
done

lemma vars_FnCall [simp]: "vars (FnCall F Xs) = vars_list Xs"
apply (cases Xs rule: eq_Abs_ExpList) 
apply (simp add: FnCall)
apply (induct_tac Us) 
apply (simp_all add: vars_def UN_equiv_class [OF equiv_exprel vars_respects])
done

lemma vars_FnCall_Nil: "vars (FnCall F Nil) = {}" 
by simp

lemma vars_FnCall_Cons: "vars (FnCall F (X#Xs)) = vars X \<union> vars_list Xs"
by simp


subsection{*Injectivity Properties of Some Constructors*}

lemma VAR_imp_eq: "VAR m \<sim> VAR n \<Longrightarrow> m = n"
by (drule exprel_imp_eq_freevars, simp)

text{*Can also be proved using the function @{term vars}*}
lemma Var_Var_eq [iff]: "(Var m = Var n) = (m = n)"
by (auto simp add: Var_def exprel_refl dest: VAR_imp_eq)

lemma VAR_neqv_PLUS: "VAR m \<sim> PLUS X Y \<Longrightarrow> False"
by (drule exprel_imp_eq_freediscrim, simp)

theorem Var_neq_Plus [iff]: "Var N \<noteq> Plus X Y"
apply (cases X, cases Y) 
apply (simp add: Var_def Plus) 
apply (blast dest: VAR_neqv_PLUS) 
done

theorem Var_neq_FnCall [iff]: "Var N \<noteq> FnCall F Xs"
apply (cases Xs rule: eq_Abs_ExpList) 
apply (auto simp add: FnCall Var_def)
apply (drule exprel_imp_eq_freediscrim, simp)
done

subsection{*Injectivity of @{term FnCall}*}

definition
  "fun" :: "exp \<Rightarrow> nat" where
  "fun X = the_elem (\<Union>U \<in> Rep_Exp X. {freefun U})"

lemma fun_respects: "(%U. {freefun U}) respects exprel"
by (auto simp add: congruent_def exprel_imp_eq_freefun) 

lemma fun_FnCall [simp]: "fun (FnCall F Xs) = F"
apply (cases Xs rule: eq_Abs_ExpList) 
apply (simp add: FnCall fun_def UN_equiv_class [OF equiv_exprel fun_respects])
done

definition
  args :: "exp \<Rightarrow> exp list" where
  "args X = the_elem (\<Union>U \<in> Rep_Exp X. {Abs_ExpList (freeargs U)})"

text{*This result can probably be generalized to arbitrary equivalence
relations, but with little benefit here.*}
lemma Abs_ExpList_eq:
     "(y, z) \<in> listrel exprel \<Longrightarrow> Abs_ExpList (y) = Abs_ExpList (z)"
  by (induct set: listrel) simp_all

lemma args_respects: "(%U. {Abs_ExpList (freeargs U)}) respects exprel"
by (auto simp add: congruent_def Abs_ExpList_eq exprel_imp_eqv_freeargs) 

lemma args_FnCall [simp]: "args (FnCall F Xs) = Xs"
apply (cases Xs rule: eq_Abs_ExpList) 
apply (simp add: FnCall args_def UN_equiv_class [OF equiv_exprel args_respects])
done


lemma FnCall_FnCall_eq [iff]:
     "(FnCall F Xs = FnCall F' Xs') = (F=F' & Xs=Xs')" 
proof
  assume "FnCall F Xs = FnCall F' Xs'"
  hence "fun (FnCall F Xs) = fun (FnCall F' Xs')" 
    and "args (FnCall F Xs) = args (FnCall F' Xs')" by auto
  thus "F=F' & Xs=Xs'" by simp
next
  assume "F=F' & Xs=Xs'" thus "FnCall F Xs = FnCall F' Xs'" by simp
qed


subsection{*The Abstract Discriminator*}
text{*However, as @{text FnCall_Var_neq_Var} illustrates, we don't need this
function in order to prove discrimination theorems.*}

definition
  discrim :: "exp \<Rightarrow> int" where
  "discrim X = the_elem (\<Union>U \<in> Rep_Exp X. {freediscrim U})"

lemma discrim_respects: "(\<lambda>U. {freediscrim U}) respects exprel"
by (auto simp add: congruent_def exprel_imp_eq_freediscrim) 

text{*Now prove the four equations for @{term discrim}*}

lemma discrim_Var [simp]: "discrim (Var N) = 0"
by (simp add: discrim_def Var_def 
              UN_equiv_class [OF equiv_exprel discrim_respects]) 

lemma discrim_Plus [simp]: "discrim (Plus X Y) = 1"
apply (cases X, cases Y) 
apply (simp add: discrim_def Plus 
                 UN_equiv_class [OF equiv_exprel discrim_respects]) 
done

lemma discrim_FnCall [simp]: "discrim (FnCall F Xs) = 2"
apply (rule_tac z=Xs in eq_Abs_ExpList) 
apply (simp add: discrim_def FnCall
                 UN_equiv_class [OF equiv_exprel discrim_respects]) 
done


text{*The structural induction rule for the abstract type*}
theorem exp_inducts:
  assumes V:    "\<And>nat. P1 (Var nat)"
      and P:    "\<And>exp1 exp2. \<lbrakk>P1 exp1; P1 exp2\<rbrakk> \<Longrightarrow> P1 (Plus exp1 exp2)"
      and F:    "\<And>nat list. P2 list \<Longrightarrow> P1 (FnCall nat list)"
      and Nil:  "P2 []"
      and Cons: "\<And>exp list. \<lbrakk>P1 exp; P2 list\<rbrakk> \<Longrightarrow> P2 (exp # list)"
  shows "P1 exp" and "P2 list"
proof -
  obtain U where exp: "exp = (Abs_Exp (exprel `` {U}))" by (cases exp)
  obtain Us where list: "list = Abs_ExpList Us" by (rule eq_Abs_ExpList)
  have "P1 (Abs_Exp (exprel `` {U}))" and "P2 (Abs_ExpList Us)"
  proof (induct U and Us)
    case (VAR nat)
    with V show ?case by (simp add: Var_def) 
  next
    case (PLUS X Y)
    with P [of "Abs_Exp (exprel `` {X})" "Abs_Exp (exprel `` {Y})"]
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
