(*  Title:      ZF/Constructible/Formula.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
*)

header {* First-Order Formulas and the Definition of the Class L *}

theory Formula imports Main begin

subsection{*Internalized formulas of FOL*}

text{*De Bruijn representation.
  Unbound variables get their denotations from an environment.*}

consts   formula :: i
datatype
  "formula" = Member ("x: nat", "y: nat")
            | Equal  ("x: nat", "y: nat")
            | Nand ("p: formula", "q: formula")
            | Forall ("p: formula")

declare formula.intros [TC]

definition
  Neg :: "i=>i" where
  "Neg(p) == Nand(p,p)"

definition
  And :: "[i,i]=>i" where
  "And(p,q) == Neg(Nand(p,q))"

definition
  Or :: "[i,i]=>i" where
  "Or(p,q) == Nand(Neg(p),Neg(q))"

definition
  Implies :: "[i,i]=>i" where
  "Implies(p,q) == Nand(p,Neg(q))"

definition
  Iff :: "[i,i]=>i" where
  "Iff(p,q) == And(Implies(p,q), Implies(q,p))"

definition
  Exists :: "i=>i" where
  "Exists(p) == Neg(Forall(Neg(p)))";

lemma Neg_type [TC]: "p \<in> formula ==> Neg(p) \<in> formula"
by (simp add: Neg_def) 

lemma And_type [TC]: "[| p \<in> formula; q \<in> formula |] ==> And(p,q) \<in> formula"
by (simp add: And_def) 

lemma Or_type [TC]: "[| p \<in> formula; q \<in> formula |] ==> Or(p,q) \<in> formula"
by (simp add: Or_def) 

lemma Implies_type [TC]:
     "[| p \<in> formula; q \<in> formula |] ==> Implies(p,q) \<in> formula"
by (simp add: Implies_def) 

lemma Iff_type [TC]:
     "[| p \<in> formula; q \<in> formula |] ==> Iff(p,q) \<in> formula"
by (simp add: Iff_def) 

lemma Exists_type [TC]: "p \<in> formula ==> Exists(p) \<in> formula"
by (simp add: Exists_def) 


consts   satisfies :: "[i,i]=>i"
primrec (*explicit lambda is required because the environment varies*)
  "satisfies(A,Member(x,y)) = 
      (\<lambda>env \<in> list(A). bool_of_o (nth(x,env) \<in> nth(y,env)))"

  "satisfies(A,Equal(x,y)) = 
      (\<lambda>env \<in> list(A). bool_of_o (nth(x,env) = nth(y,env)))"

  "satisfies(A,Nand(p,q)) =
      (\<lambda>env \<in> list(A). not ((satisfies(A,p)`env) and (satisfies(A,q)`env)))"

  "satisfies(A,Forall(p)) = 
      (\<lambda>env \<in> list(A). bool_of_o (\<forall>x\<in>A. satisfies(A,p) ` (Cons(x,env)) = 1))"


lemma "p \<in> formula ==> satisfies(A,p) \<in> list(A) -> bool"
by (induct set: formula) simp_all

abbreviation
  sats :: "[i,i,i] => o" where
  "sats(A,p,env) == satisfies(A,p)`env = 1"

lemma [simp]:
  "env \<in> list(A) 
   ==> sats(A, Member(x,y), env) <-> nth(x,env) \<in> nth(y,env)"
by simp

lemma [simp]:
  "env \<in> list(A) 
   ==> sats(A, Equal(x,y), env) <-> nth(x,env) = nth(y,env)"
by simp

lemma sats_Nand_iff [simp]:
  "env \<in> list(A) 
   ==> (sats(A, Nand(p,q), env)) <-> ~ (sats(A,p,env) & sats(A,q,env))" 
by (simp add: Bool.and_def Bool.not_def cond_def) 

lemma sats_Forall_iff [simp]:
  "env \<in> list(A) 
   ==> sats(A, Forall(p), env) <-> (\<forall>x\<in>A. sats(A, p, Cons(x,env)))"
by simp

declare satisfies.simps [simp del]; 

subsection{*Dividing line between primitive and derived connectives*}

lemma sats_Neg_iff [simp]:
  "env \<in> list(A) 
   ==> sats(A, Neg(p), env) <-> ~ sats(A,p,env)"
by (simp add: Neg_def) 

lemma sats_And_iff [simp]:
  "env \<in> list(A) 
   ==> (sats(A, And(p,q), env)) <-> sats(A,p,env) & sats(A,q,env)"
by (simp add: And_def) 

lemma sats_Or_iff [simp]:
  "env \<in> list(A) 
   ==> (sats(A, Or(p,q), env)) <-> sats(A,p,env) | sats(A,q,env)"
by (simp add: Or_def)

lemma sats_Implies_iff [simp]:
  "env \<in> list(A) 
   ==> (sats(A, Implies(p,q), env)) <-> (sats(A,p,env) --> sats(A,q,env))"
by (simp add: Implies_def, blast) 

lemma sats_Iff_iff [simp]:
  "env \<in> list(A) 
   ==> (sats(A, Iff(p,q), env)) <-> (sats(A,p,env) <-> sats(A,q,env))"
by (simp add: Iff_def, blast) 

lemma sats_Exists_iff [simp]:
  "env \<in> list(A) 
   ==> sats(A, Exists(p), env) <-> (\<exists>x\<in>A. sats(A, p, Cons(x,env)))"
by (simp add: Exists_def)


subsubsection{*Derived rules to help build up formulas*}

lemma mem_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; env \<in> list(A)|]
       ==> (x\<in>y) <-> sats(A, Member(i,j), env)" 
by (simp add: satisfies.simps)

lemma equal_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; env \<in> list(A)|]
       ==> (x=y) <-> sats(A, Equal(i,j), env)" 
by (simp add: satisfies.simps)

lemma not_iff_sats:
      "[| P <-> sats(A,p,env); env \<in> list(A)|]
       ==> (~P) <-> sats(A, Neg(p), env)"
by simp

lemma conj_iff_sats:
      "[| P <-> sats(A,p,env); Q <-> sats(A,q,env); env \<in> list(A)|]
       ==> (P & Q) <-> sats(A, And(p,q), env)"
by (simp add: sats_And_iff)

lemma disj_iff_sats:
      "[| P <-> sats(A,p,env); Q <-> sats(A,q,env); env \<in> list(A)|]
       ==> (P | Q) <-> sats(A, Or(p,q), env)"
by (simp add: sats_Or_iff)

lemma iff_iff_sats:
      "[| P <-> sats(A,p,env); Q <-> sats(A,q,env); env \<in> list(A)|]
       ==> (P <-> Q) <-> sats(A, Iff(p,q), env)"
by (simp add: sats_Forall_iff) 

lemma imp_iff_sats:
      "[| P <-> sats(A,p,env); Q <-> sats(A,q,env); env \<in> list(A)|]
       ==> (P --> Q) <-> sats(A, Implies(p,q), env)"
by (simp add: sats_Forall_iff) 

lemma ball_iff_sats:
      "[| !!x. x\<in>A ==> P(x) <-> sats(A, p, Cons(x, env)); env \<in> list(A)|]
       ==> (\<forall>x\<in>A. P(x)) <-> sats(A, Forall(p), env)"
by (simp add: sats_Forall_iff) 

lemma bex_iff_sats:
      "[| !!x. x\<in>A ==> P(x) <-> sats(A, p, Cons(x, env)); env \<in> list(A)|]
       ==> (\<exists>x\<in>A. P(x)) <-> sats(A, Exists(p), env)"
by (simp add: sats_Exists_iff) 

lemmas FOL_iff_sats = 
        mem_iff_sats equal_iff_sats not_iff_sats conj_iff_sats
        disj_iff_sats imp_iff_sats iff_iff_sats imp_iff_sats ball_iff_sats
        bex_iff_sats


subsection{*Arity of a Formula: Maximum Free de Bruijn Index*}

consts   arity :: "i=>i"
primrec
  "arity(Member(x,y)) = succ(x) \<union> succ(y)"

  "arity(Equal(x,y)) = succ(x) \<union> succ(y)"

  "arity(Nand(p,q)) = arity(p) \<union> arity(q)"

  "arity(Forall(p)) = Arith.pred(arity(p))"


lemma arity_type [TC]: "p \<in> formula ==> arity(p) \<in> nat"
by (induct_tac p, simp_all) 

lemma arity_Neg [simp]: "arity(Neg(p)) = arity(p)"
by (simp add: Neg_def) 

lemma arity_And [simp]: "arity(And(p,q)) = arity(p) \<union> arity(q)"
by (simp add: And_def) 

lemma arity_Or [simp]: "arity(Or(p,q)) = arity(p) \<union> arity(q)"
by (simp add: Or_def) 

lemma arity_Implies [simp]: "arity(Implies(p,q)) = arity(p) \<union> arity(q)"
by (simp add: Implies_def) 

lemma arity_Iff [simp]: "arity(Iff(p,q)) = arity(p) \<union> arity(q)"
by (simp add: Iff_def, blast)

lemma arity_Exists [simp]: "arity(Exists(p)) = Arith.pred(arity(p))"
by (simp add: Exists_def) 


lemma arity_sats_iff [rule_format]:
  "[| p \<in> formula; extra \<in> list(A) |]
   ==> \<forall>env \<in> list(A). 
           arity(p) \<le> length(env) --> 
           sats(A, p, env @ extra) <-> sats(A, p, env)"
apply (induct_tac p)
apply (simp_all add: Arith.pred_def nth_append Un_least_lt_iff nat_imp_quasinat
                split: split_nat_case, auto) 
done

lemma arity_sats1_iff:
  "[| arity(p) \<le> succ(length(env)); p \<in> formula; x \<in> A; env \<in> list(A); 
      extra \<in> list(A) |]
   ==> sats(A, p, Cons(x, env @ extra)) <-> sats(A, p, Cons(x, env))"
apply (insert arity_sats_iff [of p extra A "Cons(x,env)"])
apply simp 
done


subsection{*Renaming Some de Bruijn Variables*}

definition
  incr_var :: "[i,i]=>i" where
  "incr_var(x,nq) == if x<nq then x else succ(x)"

lemma incr_var_lt: "x<nq ==> incr_var(x,nq) = x"
by (simp add: incr_var_def)

lemma incr_var_le: "nq\<le>x ==> incr_var(x,nq) = succ(x)"
apply (simp add: incr_var_def) 
apply (blast dest: lt_trans1) 
done

consts   incr_bv :: "i=>i"
primrec
  "incr_bv(Member(x,y)) = 
      (\<lambda>nq \<in> nat. Member (incr_var(x,nq), incr_var(y,nq)))"

  "incr_bv(Equal(x,y)) = 
      (\<lambda>nq \<in> nat. Equal (incr_var(x,nq), incr_var(y,nq)))"

  "incr_bv(Nand(p,q)) =
      (\<lambda>nq \<in> nat. Nand (incr_bv(p)`nq, incr_bv(q)`nq))"

  "incr_bv(Forall(p)) = 
      (\<lambda>nq \<in> nat. Forall (incr_bv(p) ` succ(nq)))"


lemma [TC]: "x \<in> nat ==> incr_var(x,nq) \<in> nat"
by (simp add: incr_var_def) 

lemma incr_bv_type [TC]: "p \<in> formula ==> incr_bv(p) \<in> nat -> formula"
by (induct_tac p, simp_all) 

text{*Obviously, @{term DPow} is closed under complements and finite
intersections and unions.  Needs an inductive lemma to allow two lists of
parameters to be combined.*}

lemma sats_incr_bv_iff [rule_format]:
  "[| p \<in> formula; env \<in> list(A); x \<in> A |]
   ==> \<forall>bvs \<in> list(A). 
           sats(A, incr_bv(p) ` length(bvs), bvs @ Cons(x,env)) <-> 
           sats(A, p, bvs@env)"
apply (induct_tac p)
apply (simp_all add: incr_var_def nth_append succ_lt_iff length_type)
apply (auto simp add: diff_succ not_lt_iff_le)
done


(*the following two lemmas prevent huge case splits in arity_incr_bv_lemma*)
lemma incr_var_lemma:
     "[| x \<in> nat; y \<in> nat; nq \<le> x |]
      ==> succ(x) \<union> incr_var(y,nq) = succ(x \<union> y)"
apply (simp add: incr_var_def Ord_Un_if, auto)
  apply (blast intro: leI)
 apply (simp add: not_lt_iff_le)  
 apply (blast intro: le_anti_sym) 
apply (blast dest: lt_trans2) 
done

lemma incr_And_lemma:
     "y < x ==> y \<union> succ(x) = succ(x \<union> y)"
apply (simp add: Ord_Un_if lt_Ord lt_Ord2 succ_lt_iff) 
apply (blast dest: lt_asym) 
done

lemma arity_incr_bv_lemma [rule_format]:
  "p \<in> formula 
   ==> \<forall>n \<in> nat. arity (incr_bv(p) ` n) = 
                 (if n < arity(p) then succ(arity(p)) else arity(p))"
apply (induct_tac p) 
apply (simp_all add: imp_disj not_lt_iff_le Un_least_lt_iff lt_Un_iff le_Un_iff
                     succ_Un_distrib [symmetric] incr_var_lt incr_var_le
                     Un_commute incr_var_lemma Arith.pred_def nat_imp_quasinat
            split: split_nat_case) 
 txt{*the Forall case reduces to linear arithmetic*}
 prefer 2
 apply clarify 
 apply (blast dest: lt_trans1) 
txt{*left with the And case*}
apply safe
 apply (blast intro: incr_And_lemma lt_trans1) 
apply (subst incr_And_lemma)
 apply (blast intro: lt_trans1) 
apply (simp add: Un_commute)
done


subsection{*Renaming all but the First de Bruijn Variable*}

definition
  incr_bv1 :: "i => i" where
  "incr_bv1(p) == incr_bv(p)`1"


lemma incr_bv1_type [TC]: "p \<in> formula ==> incr_bv1(p) \<in> formula"
by (simp add: incr_bv1_def) 

(*For renaming all but the bound variable at level 0*)
lemma sats_incr_bv1_iff:
  "[| p \<in> formula; env \<in> list(A); x \<in> A; y \<in> A |]
   ==> sats(A, incr_bv1(p), Cons(x, Cons(y, env))) <-> 
       sats(A, p, Cons(x,env))"
apply (insert sats_incr_bv_iff [of p env A y "Cons(x,Nil)"])
apply (simp add: incr_bv1_def) 
done

lemma formula_add_params1 [rule_format]:
  "[| p \<in> formula; n \<in> nat; x \<in> A |]
   ==> \<forall>bvs \<in> list(A). \<forall>env \<in> list(A). 
          length(bvs) = n --> 
          sats(A, iterates(incr_bv1, n, p), Cons(x, bvs@env)) <-> 
          sats(A, p, Cons(x,env))"
apply (induct_tac n, simp, clarify) 
apply (erule list.cases)
apply (simp_all add: sats_incr_bv1_iff) 
done


lemma arity_incr_bv1_eq:
  "p \<in> formula
   ==> arity(incr_bv1(p)) =
        (if 1 < arity(p) then succ(arity(p)) else arity(p))"
apply (insert arity_incr_bv_lemma [of p 1])
apply (simp add: incr_bv1_def) 
done

lemma arity_iterates_incr_bv1_eq:
  "[| p \<in> formula; n \<in> nat |]
   ==> arity(incr_bv1^n(p)) =
         (if 1 < arity(p) then n #+ arity(p) else arity(p))"
apply (induct_tac n) 
apply (simp_all add: arity_incr_bv1_eq)
apply (simp add: not_lt_iff_le)
apply (blast intro: le_trans add_le_self2 arity_type) 
done



subsection{*Definable Powerset*}

text{*The definable powerset operation: Kunen's definition VI 1.1, page 165.*}
definition
  DPow :: "i => i" where
  "DPow(A) == {X \<in> Pow(A). 
               \<exists>env \<in> list(A). \<exists>p \<in> formula. 
                 arity(p) \<le> succ(length(env)) & 
                 X = {x\<in>A. sats(A, p, Cons(x,env))}}"

lemma DPowI:
  "[|env \<in> list(A);  p \<in> formula;  arity(p) \<le> succ(length(env))|]
   ==> {x\<in>A. sats(A, p, Cons(x,env))} \<in> DPow(A)"
by (simp add: DPow_def, blast) 

text{*With this rule we can specify @{term p} later.*}
lemma DPowI2 [rule_format]:
  "[|\<forall>x\<in>A. P(x) <-> sats(A, p, Cons(x,env));
     env \<in> list(A);  p \<in> formula;  arity(p) \<le> succ(length(env))|]
   ==> {x\<in>A. P(x)} \<in> DPow(A)"
by (simp add: DPow_def, blast) 

lemma DPowD:
  "X \<in> DPow(A) 
   ==> X <= A &
       (\<exists>env \<in> list(A). 
        \<exists>p \<in> formula. arity(p) \<le> succ(length(env)) & 
                      X = {x\<in>A. sats(A, p, Cons(x,env))})"
by (simp add: DPow_def) 

lemmas DPow_imp_subset = DPowD [THEN conjunct1]

(*Kunen's Lemma VI 1.2*)
lemma "[| p \<in> formula; env \<in> list(A); arity(p) \<le> succ(length(env)) |] 
       ==> {x\<in>A. sats(A, p, Cons(x,env))} \<in> DPow(A)"
by (blast intro: DPowI)

lemma DPow_subset_Pow: "DPow(A) <= Pow(A)"
by (simp add: DPow_def, blast)

lemma empty_in_DPow: "0 \<in> DPow(A)"
apply (simp add: DPow_def)
apply (rule_tac x=Nil in bexI) 
 apply (rule_tac x="Neg(Equal(0,0))" in bexI) 
  apply (auto simp add: Un_least_lt_iff) 
done

lemma Compl_in_DPow: "X \<in> DPow(A) ==> (A-X) \<in> DPow(A)"
apply (simp add: DPow_def, clarify, auto) 
apply (rule bexI) 
 apply (rule_tac x="Neg(p)" in bexI) 
  apply auto 
done

lemma Int_in_DPow: "[| X \<in> DPow(A); Y \<in> DPow(A) |] ==> X Int Y \<in> DPow(A)"
apply (simp add: DPow_def, auto) 
apply (rename_tac envp p envq q) 
apply (rule_tac x="envp@envq" in bexI) 
 apply (rule_tac x="And(p, iterates(incr_bv1,length(envp),q))" in bexI)
  apply typecheck
apply (rule conjI) 
(*finally check the arity!*)
 apply (simp add: arity_iterates_incr_bv1_eq length_app Un_least_lt_iff)
 apply (force intro: add_le_self le_trans) 
apply (simp add: arity_sats1_iff formula_add_params1, blast) 
done

lemma Un_in_DPow: "[| X \<in> DPow(A); Y \<in> DPow(A) |] ==> X Un Y \<in> DPow(A)"
apply (subgoal_tac "X Un Y = A - ((A-X) Int (A-Y))") 
apply (simp add: Int_in_DPow Compl_in_DPow) 
apply (simp add: DPow_def, blast) 
done

lemma singleton_in_DPow: "a \<in> A ==> {a} \<in> DPow(A)"
apply (simp add: DPow_def)
apply (rule_tac x="Cons(a,Nil)" in bexI) 
 apply (rule_tac x="Equal(0,1)" in bexI) 
  apply typecheck
apply (force simp add: succ_Un_distrib [symmetric])  
done

lemma cons_in_DPow: "[| a \<in> A; X \<in> DPow(A) |] ==> cons(a,X) \<in> DPow(A)"
apply (rule cons_eq [THEN subst]) 
apply (blast intro: singleton_in_DPow Un_in_DPow) 
done

(*Part of Lemma 1.3*)
lemma Fin_into_DPow: "X \<in> Fin(A) ==> X \<in> DPow(A)"
apply (erule Fin.induct) 
 apply (rule empty_in_DPow) 
apply (blast intro: cons_in_DPow) 
done

text{*@{term DPow} is not monotonic.  For example, let @{term A} be some
non-constructible set of natural numbers, and let @{term B} be @{term nat}.
Then @{term "A<=B"} and obviously @{term "A \<in> DPow(A)"} but @{term "A ~:
DPow(B)"}.*}

(*This may be true but the proof looks difficult, requiring relativization 
lemma DPow_insert: "DPow (cons(a,A)) = DPow(A) Un {cons(a,X) . X: DPow(A)}"
apply (rule equalityI, safe)
oops
*)

lemma Finite_Pow_subset_Pow: "Finite(A) ==> Pow(A) <= DPow(A)" 
by (blast intro: Fin_into_DPow Finite_into_Fin Fin_subset)

lemma Finite_DPow_eq_Pow: "Finite(A) ==> DPow(A) = Pow(A)"
apply (rule equalityI) 
apply (rule DPow_subset_Pow) 
apply (erule Finite_Pow_subset_Pow) 
done


subsection{*Internalized Formulas for the Ordinals*}

text{*The @{text sats} theorems below differ from the usual form in that they
include an element of absoluteness.  That is, they relate internalized
formulas to real concepts such as the subset relation, rather than to the
relativized concepts defined in theory @{text Relative}.  This lets us prove
the theorem as @{text Ords_in_DPow} without first having to instantiate the
locale @{text M_trivial}.  Note that the present theory does not even take
@{text Relative} as a parent.*}

subsubsection{*The subset relation*}

definition
  subset_fm :: "[i,i]=>i" where
  "subset_fm(x,y) == Forall(Implies(Member(0,succ(x)), Member(0,succ(y))))"

lemma subset_type [TC]: "[| x \<in> nat; y \<in> nat |] ==> subset_fm(x,y) \<in> formula"
by (simp add: subset_fm_def) 

lemma arity_subset_fm [simp]:
     "[| x \<in> nat; y \<in> nat |] ==> arity(subset_fm(x,y)) = succ(x) \<union> succ(y)"
by (simp add: subset_fm_def succ_Un_distrib [symmetric]) 

lemma sats_subset_fm [simp]:
   "[|x < length(env); y \<in> nat; env \<in> list(A); Transset(A)|]
    ==> sats(A, subset_fm(x,y), env) <-> nth(x,env) \<subseteq> nth(y,env)"
apply (frule lt_length_in_nat, assumption)  
apply (simp add: subset_fm_def Transset_def) 
apply (blast intro: nth_type) 
done

subsubsection{*Transitive sets*}

definition
  transset_fm :: "i=>i" where
  "transset_fm(x) == Forall(Implies(Member(0,succ(x)), subset_fm(0,succ(x))))"

lemma transset_type [TC]: "x \<in> nat ==> transset_fm(x) \<in> formula"
by (simp add: transset_fm_def) 

lemma arity_transset_fm [simp]:
     "x \<in> nat ==> arity(transset_fm(x)) = succ(x)"
by (simp add: transset_fm_def succ_Un_distrib [symmetric]) 

lemma sats_transset_fm [simp]:
   "[|x < length(env); env \<in> list(A); Transset(A)|]
    ==> sats(A, transset_fm(x), env) <-> Transset(nth(x,env))"
apply (frule lt_nat_in_nat, erule length_type) 
apply (simp add: transset_fm_def Transset_def) 
apply (blast intro: nth_type) 
done

subsubsection{*Ordinals*}

definition
  ordinal_fm :: "i=>i" where
  "ordinal_fm(x) == 
    And(transset_fm(x), Forall(Implies(Member(0,succ(x)), transset_fm(0))))"

lemma ordinal_type [TC]: "x \<in> nat ==> ordinal_fm(x) \<in> formula"
by (simp add: ordinal_fm_def) 

lemma arity_ordinal_fm [simp]:
     "x \<in> nat ==> arity(ordinal_fm(x)) = succ(x)"
by (simp add: ordinal_fm_def succ_Un_distrib [symmetric]) 

lemma sats_ordinal_fm:
   "[|x < length(env); env \<in> list(A); Transset(A)|]
    ==> sats(A, ordinal_fm(x), env) <-> Ord(nth(x,env))"
apply (frule lt_nat_in_nat, erule length_type) 
apply (simp add: ordinal_fm_def Ord_def Transset_def)
apply (blast intro: nth_type) 
done

text{*The subset consisting of the ordinals is definable.  Essential lemma for
@{text Ord_in_Lset}.  This result is the objective of the present subsection.*}
theorem Ords_in_DPow: "Transset(A) ==> {x \<in> A. Ord(x)} \<in> DPow(A)"
apply (simp add: DPow_def Collect_subset) 
apply (rule_tac x=Nil in bexI) 
 apply (rule_tac x="ordinal_fm(0)" in bexI) 
apply (simp_all add: sats_ordinal_fm)
done 


subsection{* Constant Lset: Levels of the Constructible Universe *}

definition
  Lset :: "i=>i" where
  "Lset(i) == transrec(i, %x f. \<Union>y\<in>x. DPow(f`y))"

definition
  L :: "i=>o" where --{*Kunen's definition VI 1.5, page 167*}
  "L(x) == \<exists>i. Ord(i) & x \<in> Lset(i)"
  
text{*NOT SUITABLE FOR REWRITING -- RECURSIVE!*}
lemma Lset: "Lset(i) = (UN j:i. DPow(Lset(j)))"
by (subst Lset_def [THEN def_transrec], simp)

lemma LsetI: "[|y\<in>x; A \<in> DPow(Lset(y))|] ==> A \<in> Lset(x)";
by (subst Lset, blast)

lemma LsetD: "A \<in> Lset(x) ==> \<exists>y\<in>x. A \<in> DPow(Lset(y))";
apply (insert Lset [of x]) 
apply (blast intro: elim: equalityE) 
done

subsubsection{* Transitivity *}

lemma elem_subset_in_DPow: "[|X \<in> A; X \<subseteq> A|] ==> X \<in> DPow(A)"
apply (simp add: Transset_def DPow_def)
apply (rule_tac x="[X]" in bexI) 
 apply (rule_tac x="Member(0,1)" in bexI) 
  apply (auto simp add: Un_least_lt_iff) 
done

lemma Transset_subset_DPow: "Transset(A) ==> A <= DPow(A)"
apply clarify  
apply (simp add: Transset_def)
apply (blast intro: elem_subset_in_DPow) 
done

lemma Transset_DPow: "Transset(A) ==> Transset(DPow(A))"
apply (simp add: Transset_def) 
apply (blast intro: elem_subset_in_DPow dest: DPowD) 
done

text{*Kunen's VI 1.6 (a)*}
lemma Transset_Lset: "Transset(Lset(i))"
apply (rule_tac a=i in eps_induct)
apply (subst Lset)
apply (blast intro!: Transset_Union_family Transset_Un Transset_DPow)
done

lemma mem_Lset_imp_subset_Lset: "a \<in> Lset(i) ==> a \<subseteq> Lset(i)"
apply (insert Transset_Lset) 
apply (simp add: Transset_def) 
done

subsubsection{* Monotonicity *}

text{*Kunen's VI 1.6 (b)*}
lemma Lset_mono [rule_format]:
     "ALL j. i<=j --> Lset(i) <= Lset(j)"
proof (induct i rule: eps_induct, intro allI impI)
  fix x j
  assume "\<forall>y\<in>x. \<forall>j. y \<subseteq> j \<longrightarrow> Lset(y) \<subseteq> Lset(j)"
     and "x \<subseteq> j"
  thus "Lset(x) \<subseteq> Lset(j)"
    by (force simp add: Lset [of x] Lset [of j]) 
qed

text{*This version lets us remove the premise @{term "Ord(i)"} sometimes.*}
lemma Lset_mono_mem [rule_format]:
     "ALL j. i:j --> Lset(i) <= Lset(j)"
proof (induct i rule: eps_induct, intro allI impI)
  fix x j
  assume "\<forall>y\<in>x. \<forall>j. y \<in> j \<longrightarrow> Lset(y) \<subseteq> Lset(j)"
     and "x \<in> j"
  thus "Lset(x) \<subseteq> Lset(j)"
    by (force simp add: Lset [of j] 
              intro!: bexI intro: elem_subset_in_DPow dest: LsetD DPowD) 
qed


text{*Useful with Reflection to bump up the ordinal*}
lemma subset_Lset_ltD: "[|A \<subseteq> Lset(i); i < j|] ==> A \<subseteq> Lset(j)"
by (blast dest: ltD [THEN Lset_mono_mem]) 

subsubsection{* 0, successor and limit equations for Lset *}

lemma Lset_0 [simp]: "Lset(0) = 0"
by (subst Lset, blast)

lemma Lset_succ_subset1: "DPow(Lset(i)) <= Lset(succ(i))"
by (subst Lset, rule succI1 [THEN RepFunI, THEN Union_upper])

lemma Lset_succ_subset2: "Lset(succ(i)) <= DPow(Lset(i))"
apply (subst Lset, rule UN_least)
apply (erule succE) 
 apply blast 
apply clarify
apply (rule elem_subset_in_DPow)
 apply (subst Lset)
 apply blast 
apply (blast intro: dest: DPowD Lset_mono_mem) 
done

lemma Lset_succ: "Lset(succ(i)) = DPow(Lset(i))"
by (intro equalityI Lset_succ_subset1 Lset_succ_subset2) 

lemma Lset_Union [simp]: "Lset(\<Union>(X)) = (\<Union>y\<in>X. Lset(y))"
apply (subst Lset)
apply (rule equalityI)
 txt{*first inclusion*}
 apply (rule UN_least)
 apply (erule UnionE)
 apply (rule subset_trans)
  apply (erule_tac [2] UN_upper, subst Lset, erule UN_upper)
txt{*opposite inclusion*}
apply (rule UN_least)
apply (subst Lset, blast)
done

subsubsection{* Lset applied to Limit ordinals *}

lemma Limit_Lset_eq:
    "Limit(i) ==> Lset(i) = (\<Union>y\<in>i. Lset(y))"
by (simp add: Lset_Union [symmetric] Limit_Union_eq)

lemma lt_LsetI: "[| a: Lset(j);  j<i |] ==> a \<in> Lset(i)"
by (blast dest: Lset_mono [OF le_imp_subset [OF leI]])

lemma Limit_LsetE:
    "[| a: Lset(i);  ~R ==> Limit(i);
        !!x. [| x<i;  a: Lset(x) |] ==> R
     |] ==> R"
apply (rule classical)
apply (rule Limit_Lset_eq [THEN equalityD1, THEN subsetD, THEN UN_E])
  prefer 2 apply assumption
 apply blast 
apply (blast intro: ltI  Limit_is_Ord)
done

subsubsection{* Basic closure properties *}

lemma zero_in_Lset: "y:x ==> 0 \<in> Lset(x)"
by (subst Lset, blast intro: empty_in_DPow)

lemma notin_Lset: "x \<notin> Lset(x)"
apply (rule_tac a=x in eps_induct)
apply (subst Lset)
apply (blast dest: DPowD)  
done


subsection{*Constructible Ordinals: Kunen's VI 1.9 (b)*}

lemma Ords_of_Lset_eq: "Ord(i) ==> {x\<in>Lset(i). Ord(x)} = i"
apply (erule trans_induct3)
  apply (simp_all add: Lset_succ Limit_Lset_eq Limit_Union_eq)
txt{*The successor case remains.*} 
apply (rule equalityI)
txt{*First inclusion*}
 apply clarify  
 apply (erule Ord_linear_lt, assumption) 
   apply (blast dest: DPow_imp_subset ltD notE [OF notin_Lset]) 
  apply blast 
 apply (blast dest: ltD)
txt{*Opposite inclusion, @{term "succ(x) \<subseteq> DPow(Lset(x)) \<inter> ON"}*}
apply auto
txt{*Key case: *}
  apply (erule subst, rule Ords_in_DPow [OF Transset_Lset]) 
 apply (blast intro: elem_subset_in_DPow dest: OrdmemD elim: equalityE) 
apply (blast intro: Ord_in_Ord) 
done


lemma Ord_subset_Lset: "Ord(i) ==> i \<subseteq> Lset(i)"
by (subst Ords_of_Lset_eq [symmetric], assumption, fast)

lemma Ord_in_Lset: "Ord(i) ==> i \<in> Lset(succ(i))"
apply (simp add: Lset_succ)
apply (subst Ords_of_Lset_eq [symmetric], assumption, 
       rule Ords_in_DPow [OF Transset_Lset]) 
done

lemma Ord_in_L: "Ord(i) ==> L(i)"
by (simp add: L_def, blast intro: Ord_in_Lset)

subsubsection{* Unions *}

lemma Union_in_Lset:
     "X \<in> Lset(i) ==> Union(X) \<in> Lset(succ(i))"
apply (insert Transset_Lset)
apply (rule LsetI [OF succI1])
apply (simp add: Transset_def DPow_def) 
apply (intro conjI, blast)
txt{*Now to create the formula @{term "\<exists>y. y \<in> X \<and> x \<in> y"} *}
apply (rule_tac x="Cons(X,Nil)" in bexI) 
 apply (rule_tac x="Exists(And(Member(0,2), Member(1,0)))" in bexI) 
  apply typecheck
apply (simp add: succ_Un_distrib [symmetric], blast) 
done

theorem Union_in_L: "L(X) ==> L(Union(X))"
by (simp add: L_def, blast dest: Union_in_Lset) 

subsubsection{* Finite sets and ordered pairs *}

lemma singleton_in_Lset: "a: Lset(i) ==> {a} \<in> Lset(succ(i))"
by (simp add: Lset_succ singleton_in_DPow) 

lemma doubleton_in_Lset:
     "[| a: Lset(i);  b: Lset(i) |] ==> {a,b} \<in> Lset(succ(i))"
by (simp add: Lset_succ empty_in_DPow cons_in_DPow) 

lemma Pair_in_Lset:
    "[| a: Lset(i);  b: Lset(i); Ord(i) |] ==> <a,b> \<in> Lset(succ(succ(i)))"
apply (unfold Pair_def)
apply (blast intro: doubleton_in_Lset) 
done

lemmas Lset_UnI1 = Un_upper1 [THEN Lset_mono [THEN subsetD]]
lemmas Lset_UnI2 = Un_upper2 [THEN Lset_mono [THEN subsetD]]

text{*Hard work is finding a single j:i such that {a,b}<=Lset(j)*}
lemma doubleton_in_LLimit:
    "[| a: Lset(i);  b: Lset(i);  Limit(i) |] ==> {a,b} \<in> Lset(i)"
apply (erule Limit_LsetE, assumption)
apply (erule Limit_LsetE, assumption)
apply (blast intro: lt_LsetI [OF doubleton_in_Lset]
                    Lset_UnI1 Lset_UnI2 Limit_has_succ Un_least_lt)
done

theorem doubleton_in_L: "[| L(a); L(b) |] ==> L({a, b})"
apply (simp add: L_def, clarify) 
apply (drule Ord2_imp_greater_Limit, assumption) 
apply (blast intro: lt_LsetI doubleton_in_LLimit Limit_is_Ord) 
done

lemma Pair_in_LLimit:
    "[| a: Lset(i);  b: Lset(i);  Limit(i) |] ==> <a,b> \<in> Lset(i)"
txt{*Infer that a, b occur at ordinals x,xa < i.*}
apply (erule Limit_LsetE, assumption)
apply (erule Limit_LsetE, assumption)
txt{*Infer that succ(succ(x Un xa)) < i *}
apply (blast intro: lt_Ord lt_LsetI [OF Pair_in_Lset]
                    Lset_UnI1 Lset_UnI2 Limit_has_succ Un_least_lt)
done



text{*The rank function for the constructible universe*}
definition
  lrank :: "i=>i" where --{*Kunen's definition VI 1.7*}
  "lrank(x) == \<mu> i. x \<in> Lset(succ(i))"

lemma L_I: "[|x \<in> Lset(i); Ord(i)|] ==> L(x)"
by (simp add: L_def, blast)

lemma L_D: "L(x) ==> \<exists>i. Ord(i) & x \<in> Lset(i)"
by (simp add: L_def)

lemma Ord_lrank [simp]: "Ord(lrank(a))"
by (simp add: lrank_def)

lemma Lset_lrank_lt [rule_format]: "Ord(i) ==> x \<in> Lset(i) --> lrank(x) < i"
apply (erule trans_induct3)
  apply simp   
 apply (simp only: lrank_def) 
 apply (blast intro: Least_le) 
apply (simp_all add: Limit_Lset_eq) 
apply (blast intro: ltI Limit_is_Ord lt_trans) 
done

text{*Kunen's VI 1.8.  The proof is much harder than the text would
suggest.  For a start, it needs the previous lemma, which is proved by
induction.*}
lemma Lset_iff_lrank_lt: "Ord(i) ==> x \<in> Lset(i) <-> L(x) & lrank(x) < i"
apply (simp add: L_def, auto) 
 apply (blast intro: Lset_lrank_lt) 
 apply (unfold lrank_def) 
apply (drule succI1 [THEN Lset_mono_mem, THEN subsetD]) 
apply (drule_tac P="\<lambda>i. x \<in> Lset(succ(i))" in LeastI, assumption) 
apply (blast intro!: le_imp_subset Lset_mono [THEN subsetD]) 
done

lemma Lset_succ_lrank_iff [simp]: "x \<in> Lset(succ(lrank(x))) <-> L(x)"
by (simp add: Lset_iff_lrank_lt)

text{*Kunen's VI 1.9 (a)*}
lemma lrank_of_Ord: "Ord(i) ==> lrank(i) = i"
apply (unfold lrank_def) 
apply (rule Least_equality) 
  apply (erule Ord_in_Lset) 
 apply assumption
apply (insert notin_Lset [of i]) 
apply (blast intro!: le_imp_subset Lset_mono [THEN subsetD]) 
done


text{*This is lrank(lrank(a)) = lrank(a) *}
declare Ord_lrank [THEN lrank_of_Ord, simp]

text{*Kunen's VI 1.10 *}
lemma Lset_in_Lset_succ: "Lset(i) \<in> Lset(succ(i))";
apply (simp add: Lset_succ DPow_def) 
apply (rule_tac x=Nil in bexI) 
 apply (rule_tac x="Equal(0,0)" in bexI) 
apply auto 
done

lemma lrank_Lset: "Ord(i) ==> lrank(Lset(i)) = i"
apply (unfold lrank_def) 
apply (rule Least_equality) 
  apply (rule Lset_in_Lset_succ) 
 apply assumption
apply clarify 
apply (subgoal_tac "Lset(succ(ia)) <= Lset(i)")
 apply (blast dest: mem_irrefl) 
apply (blast intro!: le_imp_subset Lset_mono) 
done

text{*Kunen's VI 1.11 *}
lemma Lset_subset_Vset: "Ord(i) ==> Lset(i) <= Vset(i)";
apply (erule trans_induct)
apply (subst Lset) 
apply (subst Vset) 
apply (rule UN_mono [OF subset_refl]) 
apply (rule subset_trans [OF DPow_subset_Pow]) 
apply (rule Pow_mono, blast) 
done

text{*Kunen's VI 1.12 *}
lemma Lset_subset_Vset': "i \<in> nat ==> Lset(i) = Vset(i)";
apply (erule nat_induct)
 apply (simp add: Vfrom_0) 
apply (simp add: Lset_succ Vset_succ Finite_Vset Finite_DPow_eq_Pow) 
done

text{*Every set of constructible sets is included in some @{term Lset}*} 
lemma subset_Lset:
     "(\<forall>x\<in>A. L(x)) ==> \<exists>i. Ord(i) & A \<subseteq> Lset(i)"
by (rule_tac x = "\<Union>x\<in>A. succ(lrank(x))" in exI, force)

lemma subset_LsetE:
     "[|\<forall>x\<in>A. L(x);
        !!i. [|Ord(i); A \<subseteq> Lset(i)|] ==> P|]
      ==> P"
by (blast dest: subset_Lset) 

subsubsection{*For L to satisfy the Powerset axiom *}

lemma LPow_env_typing:
    "[| y \<in> Lset(i); Ord(i); y \<subseteq> X |] 
     ==> \<exists>z \<in> Pow(X). y \<in> Lset(succ(lrank(z)))"
by (auto intro: L_I iff: Lset_succ_lrank_iff) 

lemma LPow_in_Lset:
     "[|X \<in> Lset(i); Ord(i)|] ==> \<exists>j. Ord(j) & {y \<in> Pow(X). L(y)} \<in> Lset(j)"
apply (rule_tac x="succ(\<Union>y \<in> Pow(X). succ(lrank(y)))" in exI)
apply simp 
apply (rule LsetI [OF succI1])
apply (simp add: DPow_def) 
apply (intro conjI, clarify) 
 apply (rule_tac a=x in UN_I, simp+)  
txt{*Now to create the formula @{term "y \<subseteq> X"} *}
apply (rule_tac x="Cons(X,Nil)" in bexI) 
 apply (rule_tac x="subset_fm(0,1)" in bexI) 
  apply typecheck
 apply (rule conjI) 
apply (simp add: succ_Un_distrib [symmetric]) 
apply (rule equality_iffI) 
apply (simp add: Transset_UN [OF Transset_Lset] LPow_env_typing)
apply (auto intro: L_I iff: Lset_succ_lrank_iff) 
done

theorem LPow_in_L: "L(X) ==> L({y \<in> Pow(X). L(y)})"
by (blast intro: L_I dest: L_D LPow_in_Lset)


subsection{*Eliminating @{term arity} from the Definition of @{term Lset}*}

lemma nth_zero_eq_0: "n \<in> nat ==> nth(n,[0]) = 0"
by (induct_tac n, auto)

lemma sats_app_0_iff [rule_format]:
  "[| p \<in> formula; 0 \<in> A |]
   ==> \<forall>env \<in> list(A). sats(A,p, env@[0]) <-> sats(A,p,env)"
apply (induct_tac p)
apply (simp_all del: app_Cons add: app_Cons [symmetric]
                add: nth_zero_eq_0 nth_append not_lt_iff_le nth_eq_0)
done

lemma sats_app_zeroes_iff:
  "[| p \<in> formula; 0 \<in> A; env \<in> list(A); n \<in> nat |]
   ==> sats(A,p,env @ repeat(0,n)) <-> sats(A,p,env)"
apply (induct_tac n, simp) 
apply (simp del: repeat.simps
            add: repeat_succ_app sats_app_0_iff app_assoc [symmetric]) 
done

lemma exists_bigger_env:
  "[| p \<in> formula; 0 \<in> A; env \<in> list(A) |]
   ==> \<exists>env' \<in> list(A). arity(p) \<le> succ(length(env')) & 
              (\<forall>a\<in>A. sats(A,p,Cons(a,env')) <-> sats(A,p,Cons(a,env)))"
apply (rule_tac x="env @ repeat(0,arity(p))" in bexI) 
apply (simp del: app_Cons add: app_Cons [symmetric]
            add: length_repeat sats_app_zeroes_iff, typecheck)
done


text{*A simpler version of @{term DPow}: no arity check!*}
definition
  DPow' :: "i => i" where
  "DPow'(A) == {X \<in> Pow(A). 
                \<exists>env \<in> list(A). \<exists>p \<in> formula. 
                    X = {x\<in>A. sats(A, p, Cons(x,env))}}"

lemma DPow_subset_DPow': "DPow(A) <= DPow'(A)";
by (simp add: DPow_def DPow'_def, blast)

lemma DPow'_0: "DPow'(0) = {0}"
by (auto simp add: DPow'_def)

lemma DPow'_subset_DPow: "0 \<in> A ==> DPow'(A) \<subseteq> DPow(A)"
apply (auto simp add: DPow'_def DPow_def) 
apply (frule exists_bigger_env, assumption+, force)  
done

lemma DPow_eq_DPow': "Transset(A) ==> DPow(A) = DPow'(A)"
apply (drule Transset_0_disj) 
apply (erule disjE) 
 apply (simp add: DPow'_0 Finite_DPow_eq_Pow) 
apply (rule equalityI)
 apply (rule DPow_subset_DPow') 
apply (erule DPow'_subset_DPow) 
done

text{*And thus we can relativize @{term Lset} without bothering with
      @{term arity} and @{term length}*}
lemma Lset_eq_transrec_DPow': "Lset(i) = transrec(i, %x f. \<Union>y\<in>x. DPow'(f`y))"
apply (rule_tac a=i in eps_induct)
apply (subst Lset)
apply (subst transrec)
apply (simp only: DPow_eq_DPow' [OF Transset_Lset], simp) 
done

text{*With this rule we can specify @{term p} later and don't worry about
      arities at all!*}
lemma DPow_LsetI [rule_format]:
  "[|\<forall>x\<in>Lset(i). P(x) <-> sats(Lset(i), p, Cons(x,env));
     env \<in> list(Lset(i));  p \<in> formula|]
   ==> {x\<in>Lset(i). P(x)} \<in> DPow(Lset(i))"
by (simp add: DPow_eq_DPow' [OF Transset_Lset] DPow'_def, blast) 

end
