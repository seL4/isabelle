(*  Title:      HOL/Sum_Type.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

header{*The Disjoint Sum of Two Types*}

theory Sum_Type
imports Product_Type
begin

text{*The representations of the two injections*}

constdefs
  Inl_Rep :: "['a, 'a, 'b, bool] => bool"
  "Inl_Rep == (%a. %x y p. x=a & p)"

  Inr_Rep :: "['b, 'a, 'b, bool] => bool"
  "Inr_Rep == (%b. %x y p. y=b & ~p)"


global

typedef (Sum)
  ('a, 'b) "+"          (infixr 10)
    = "{f. (? a. f = Inl_Rep(a::'a)) | (? b. f = Inr_Rep(b::'b))}"
  by auto

local


text{*abstract constants and syntax*}

constdefs
  Inl :: "'a => 'a + 'b"
   "Inl == (%a. Abs_Sum(Inl_Rep(a)))"

  Inr :: "'b => 'a + 'b"
   "Inr == (%b. Abs_Sum(Inr_Rep(b)))"

  Plus :: "['a set, 'b set] => ('a + 'b) set"        (infixr "<+>" 65)
   "A <+> B == (Inl`A) Un (Inr`B)"
    --{*disjoint sum for sets; the operator + is overloaded with wrong type!*}

  Part :: "['a set, 'b => 'a] => 'a set"
   "Part A h == A Int {x. ? z. x = h(z)}"
    --{*for selecting out the components of a mutually recursive definition*}



(** Inl_Rep and Inr_Rep: Representations of the constructors **)

(*This counts as a non-emptiness result for admitting 'a+'b as a type*)
lemma Inl_RepI: "Inl_Rep(a) : Sum"
by (auto simp add: Sum_def)

lemma Inr_RepI: "Inr_Rep(b) : Sum"
by (auto simp add: Sum_def)

lemma inj_on_Abs_Sum: "inj_on Abs_Sum Sum"
apply (rule inj_on_inverseI)
apply (erule Abs_Sum_inverse)
done

subsection{*Freeness Properties for @{term Inl} and  @{term Inr}*}

text{*Distinctness*}

lemma Inl_Rep_not_Inr_Rep: "Inl_Rep(a) ~= Inr_Rep(b)"
by (auto simp add: Inl_Rep_def Inr_Rep_def expand_fun_eq)

lemma Inl_not_Inr [iff]: "Inl(a) ~= Inr(b)"
apply (simp add: Inl_def Inr_def)
apply (rule inj_on_Abs_Sum [THEN inj_on_contraD])
apply (rule Inl_Rep_not_Inr_Rep)
apply (rule Inl_RepI)
apply (rule Inr_RepI)
done

lemmas Inr_not_Inl = Inl_not_Inr [THEN not_sym, standard, iff]

lemmas Inl_neq_Inr = Inl_not_Inr [THEN notE, standard]
lemmas Inr_neq_Inl = sym [THEN Inl_neq_Inr, standard]


text{*Injectiveness*}

lemma Inl_Rep_inject: "Inl_Rep(a) = Inl_Rep(c) ==> a=c"
by (auto simp add: Inl_Rep_def expand_fun_eq)

lemma Inr_Rep_inject: "Inr_Rep(b) = Inr_Rep(d) ==> b=d"
by (auto simp add: Inr_Rep_def expand_fun_eq)

lemma inj_Inl: "inj(Inl)"
apply (simp add: Inl_def)
apply (rule inj_onI)
apply (erule inj_on_Abs_Sum [THEN inj_onD, THEN Inl_Rep_inject])
apply (rule Inl_RepI)
apply (rule Inl_RepI)
done
lemmas Inl_inject = inj_Inl [THEN injD, standard]

lemma inj_Inr: "inj(Inr)"
apply (simp add: Inr_def)
apply (rule inj_onI)
apply (erule inj_on_Abs_Sum [THEN inj_onD, THEN Inr_Rep_inject])
apply (rule Inr_RepI)
apply (rule Inr_RepI)
done

lemmas Inr_inject = inj_Inr [THEN injD, standard]

lemma Inl_eq [iff]: "(Inl(x)=Inl(y)) = (x=y)"
by (blast dest!: Inl_inject)

lemma Inr_eq [iff]: "(Inr(x)=Inr(y)) = (x=y)"
by (blast dest!: Inr_inject)


subsection{*The Disjoint Sum of Sets*}

(** Introduction rules for the injections **)

lemma InlI [intro!]: "a : A ==> Inl(a) : A <+> B"
by (simp add: Plus_def)

lemma InrI [intro!]: "b : B ==> Inr(b) : A <+> B"
by (simp add: Plus_def)

(** Elimination rules **)

lemma PlusE [elim!]: 
    "[| u: A <+> B;   
        !!x. [| x:A;  u=Inl(x) |] ==> P;  
        !!y. [| y:B;  u=Inr(y) |] ==> P  
     |] ==> P"
by (auto simp add: Plus_def)



text{*Exhaustion rule for sums, a degenerate form of induction*}
lemma sumE: 
    "[| !!x::'a. s = Inl(x) ==> P;  !!y::'b. s = Inr(y) ==> P  
     |] ==> P"
apply (rule Abs_Sum_cases [of s]) 
apply (auto simp add: Sum_def Inl_def Inr_def)
done

lemma sum_induct: "[| !!x. P (Inl x); !!x. P (Inr x) |] ==> P x"
by (rule sumE [of x], auto)


subsection{*The @{term Part} Primitive*}

lemma Part_eqI [intro]: "[| a : A;  a=h(b) |] ==> a : Part A h"
by (auto simp add: Part_def)

lemmas PartI = Part_eqI [OF _ refl, standard]

lemma PartE [elim!]: "[| a : Part A h;  !!z. [| a : A;  a=h(z) |] ==> P |] ==> P"
by (auto simp add: Part_def)


lemma Part_subset: "Part A h <= A"
by (auto simp add: Part_def)

lemma Part_mono: "A<=B ==> Part A h <= Part B h"
by blast

lemmas basic_monos = basic_monos Part_mono

lemma PartD1: "a : Part A h ==> a : A"
by (simp add: Part_def)

lemma Part_id: "Part A (%x. x) = A"
by blast

lemma Part_Int: "Part (A Int B) h = (Part A h) Int (Part B h)"
by blast

lemma Part_Collect: "Part (A Int {x. P x}) h = (Part A h) Int {x. P x}"
by blast

ML
{*
val Inl_RepI = thm "Inl_RepI";
val Inr_RepI = thm "Inr_RepI";
val inj_on_Abs_Sum = thm "inj_on_Abs_Sum";
val Inl_Rep_not_Inr_Rep = thm "Inl_Rep_not_Inr_Rep";
val Inl_not_Inr = thm "Inl_not_Inr";
val Inr_not_Inl = thm "Inr_not_Inl";
val Inl_neq_Inr = thm "Inl_neq_Inr";
val Inr_neq_Inl = thm "Inr_neq_Inl";
val Inl_Rep_inject = thm "Inl_Rep_inject";
val Inr_Rep_inject = thm "Inr_Rep_inject";
val inj_Inl = thm "inj_Inl";
val Inl_inject = thm "Inl_inject";
val inj_Inr = thm "inj_Inr";
val Inr_inject = thm "Inr_inject";
val Inl_eq = thm "Inl_eq";
val Inr_eq = thm "Inr_eq";
val InlI = thm "InlI";
val InrI = thm "InrI";
val PlusE = thm "PlusE";
val sumE = thm "sumE";
val sum_induct = thm "sum_induct";
val Part_eqI = thm "Part_eqI";
val PartI = thm "PartI";
val PartE = thm "PartE";
val Part_subset = thm "Part_subset";
val Part_mono = thm "Part_mono";
val PartD1 = thm "PartD1";
val Part_id = thm "Part_id";
val Part_Int = thm "Part_Int";
val Part_Collect = thm "Part_Collect";

val basic_monos = thms "basic_monos";
*}


end
