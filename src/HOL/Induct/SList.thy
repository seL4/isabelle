(*  Title:      HOL/Induct/SList.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory

This theory is strictly of historical interest. It illustrates how
recursive datatypes can be constructed in higher-order logic from
first principles. Isabelle's datatype package automates a
construction of this sort.

Enriched theory of lists; mutual indirect recursive data-types.

Definition of type 'a list (strict lists) by a least fixed point

We use          list(A) == lfp(%Z. {NUMB(0)} <+> A <*> Z)
and not         list    == lfp(%Z. {NUMB(0)} <+> range(Leaf) <*> Z)

so that list can serve as a "functor" for defining other recursive types.

This enables the conservative construction of mutual recursive data-types
such as

datatype 'a m = Node 'a * ('a m) list
*)

header {* Extended List Theory (old) *}

theory SList
imports Sexp
begin

(*Hilbert_Choice is needed for the function "inv"*)

(* *********************************************************************** *)
(*                                                                         *)
(* Building up data type                                                   *)
(*                                                                         *)
(* *********************************************************************** *)


(* Defining the Concrete Constructors *)
definition
  NIL  :: "'a item" where
  "NIL = In0(Numb(0))"

definition
  CONS :: "['a item, 'a item] => 'a item" where
  "CONS M N = In1(Scons M N)"

inductive_set
  list :: "'a item set => 'a item set"
  for A :: "'a item set"
  where
    NIL_I:  "NIL: list A"
  | CONS_I: "[| a: A;  M: list A |] ==> CONS a M : list A"


definition "List = list (range Leaf)"

typedef 'a list = "List :: 'a item set"
  morphisms Rep_List Abs_List
  unfolding List_def by (blast intro: list.NIL_I)

abbreviation "Case == Datatype.Case"
abbreviation "Split == Datatype.Split"

definition
  List_case :: "['b, ['a item, 'a item]=>'b, 'a item] => 'b" where
  "List_case c d = Case(%x. c)(Split(d))"
  
definition
  List_rec  :: "['a item, 'b, ['a item, 'a item, 'b]=>'b] => 'b" where
  "List_rec M c d = wfrec (pred_sexp^+)
                           (%g. List_case c (%x y. d x y (g y))) M"


(* *********************************************************************** *)
(*                                                                         *)
(* Abstracting data type                                                   *)
(*                                                                         *)
(* *********************************************************************** *)

(*Declaring the abstract list constructors*)

no_translations
  "[x, xs]" == "x#[xs]"
  "[x]" == "x#[]"
no_notation
  Nil  ("[]") and
  Cons (infixr "#" 65)

definition
  Nil       :: "'a list"                               ("[]") where
   "Nil  = Abs_List(NIL)"

definition
  "Cons"       :: "['a, 'a list] => 'a list"           (infixr "#" 65) where
   "x#xs = Abs_List(CONS (Leaf x)(Rep_List xs))"

definition
  (* list Recursion -- the trancl is Essential; see list.ML *)
  list_rec  :: "['a list, 'b, ['a, 'a list, 'b]=>'b] => 'b" where
   "list_rec l c d =
      List_rec(Rep_List l) c (%x y r. d(inv Leaf x)(Abs_List y) r)"

definition
  list_case :: "['b, ['a, 'a list]=>'b, 'a list] => 'b" where
   "list_case a f xs = list_rec xs a (%x xs r. f x xs)"

(* list Enumeration *)
translations
  "[x, xs]" == "x#[xs]"
  "[x]"     == "x#[]"

  "case xs of [] => a | y#ys => b" == "CONST list_case(a, %y ys. b, xs)"


(* *********************************************************************** *)
(*                                                                         *)
(* Generalized Map Functionals                                             *)
(*                                                                         *)
(* *********************************************************************** *)

  
(* Generalized Map Functionals *)

definition
  Rep_map   :: "('b => 'a item) => ('b list => 'a item)" where
   "Rep_map f xs = list_rec xs  NIL(%x l r. CONS(f x) r)"

definition
  Abs_map   :: "('a item => 'b) => 'a item => 'b list" where
   "Abs_map g M  = List_rec M Nil (%N L r. g(N)#r)"


definition
  map       :: "('a=>'b) => ('a list => 'b list)" where
  "map f xs = list_rec xs [] (%x l r. f(x)#r)"

primrec take :: "['a list,nat] => 'a list" where
  take_0:  "take xs 0 = []"
| take_Suc: "take xs (Suc n) = list_case [] (%x l. x # take l n) xs"

lemma ListI: "x : list (range Leaf) ==> x : List"
by (simp add: List_def)

lemma ListD: "x : List ==> x : list (range Leaf)"
by (simp add: List_def)

lemma list_unfold: "list(A) = usum {Numb(0)} (uprod A (list(A)))"
  by (fast intro!: list.intros [unfolded NIL_def CONS_def]
           elim: list.cases [unfolded NIL_def CONS_def])

(*This justifies using list in other recursive type definitions*)
lemma list_mono: "A<=B ==> list(A) <= list(B)"
apply (rule subsetI)
apply (erule list.induct)
apply (auto intro!: list.intros)
done

(*Type checking -- list creates well-founded sets*)
lemma list_sexp: "list(sexp) <= sexp"
apply (rule subsetI)
apply (erule list.induct)
apply (unfold NIL_def CONS_def)
apply (auto intro: sexp.intros sexp_In0I sexp_In1I)
done

(* A <= sexp ==> list(A) <= sexp *)
lemmas list_subset_sexp = subset_trans [OF list_mono list_sexp] 


(*Induction for the type 'a list *)
lemma list_induct:
    "[| P(Nil);    
        !!x xs. P(xs) ==> P(x # xs) |]  ==> P(l)"
apply (unfold Nil_def Cons_def) 
apply (rule Rep_List_inverse [THEN subst])
(*types force good instantiation*)
apply (rule Rep_List [unfolded List_def, THEN list.induct], simp)
apply (erule Abs_List_inverse [unfolded List_def, THEN subst], blast) 
done


(*** Isomorphisms ***)

lemma inj_on_Abs_list: "inj_on Abs_List (list(range Leaf))"
apply (rule inj_on_inverseI)
apply (erule Abs_List_inverse [unfolded List_def])
done

(** Distinctness of constructors **)

lemma CONS_not_NIL [iff]: "CONS M N ~= NIL"
by (simp add: NIL_def CONS_def)

lemmas NIL_not_CONS [iff] = CONS_not_NIL [THEN not_sym]
lemmas CONS_neq_NIL = CONS_not_NIL [THEN notE]
lemmas NIL_neq_CONS = sym [THEN CONS_neq_NIL]

lemma Cons_not_Nil [iff]: "x # xs ~= Nil"
apply (unfold Nil_def Cons_def)
apply (rule CONS_not_NIL [THEN inj_on_Abs_list [THEN inj_on_contraD]])
apply (simp_all add: list.intros rangeI Rep_List [unfolded List_def])
done

lemmas Nil_not_Cons = Cons_not_Nil [THEN not_sym]
declare Nil_not_Cons [iff]
lemmas Cons_neq_Nil = Cons_not_Nil [THEN notE]
lemmas Nil_neq_Cons = sym [THEN Cons_neq_Nil]

(** Injectiveness of CONS and Cons **)

lemma CONS_CONS_eq [iff]: "(CONS K M)=(CONS L N) = (K=L & M=N)"
by (simp add: CONS_def)

(*For reasoning about abstract list constructors*)
declare Rep_List [THEN ListD, intro] ListI [intro]
declare list.intros [intro,simp]
declare Leaf_inject [dest!]

lemma Cons_Cons_eq [iff]: "(x#xs=y#ys) = (x=y & xs=ys)"
apply (simp add: Cons_def)
apply (subst Abs_List_inject)
apply (auto simp add: Rep_List_inject)
done

lemmas Cons_inject2 = Cons_Cons_eq [THEN iffD1, THEN conjE]

lemma CONS_D: "CONS M N: list(A) ==> M: A & N: list(A)"
  by (induct L == "CONS M N" rule: list.induct) auto

lemma sexp_CONS_D: "CONS M N: sexp ==> M: sexp & N: sexp"
apply (simp add: CONS_def In1_def)
apply (fast dest!: Scons_D)
done


(*Reasoning about constructors and their freeness*)


lemma not_CONS_self: "N: list(A) ==> !M. N ~= CONS M N"
apply (erule list.induct) apply simp_all done

lemma not_Cons_self2: "\<forall>x. l ~= x#l"
by (induct l rule: list_induct) simp_all


lemma neq_Nil_conv2: "(xs ~= []) = (\<exists>y ys. xs = y#ys)"
by (induct xs rule: list_induct) auto

(** Conversion rules for List_case: case analysis operator **)

lemma List_case_NIL [simp]: "List_case c h NIL = c"
by (simp add: List_case_def NIL_def)

lemma List_case_CONS [simp]: "List_case c h (CONS M N) = h M N"
by (simp add: List_case_def CONS_def)


(*** List_rec -- by wf recursion on pred_sexp ***)

(* The trancl(pred_sexp) is essential because pred_sexp_CONS_I1,2 would not
   hold if pred_sexp^+ were changed to pred_sexp. *)

lemma List_rec_unfold_lemma:
     "(%M. List_rec M c d) == 
      wfrec (pred_sexp^+) (%g. List_case c (%x y. d x y (g y)))"
by (simp add: List_rec_def)

lemmas List_rec_unfold = 
    def_wfrec [OF List_rec_unfold_lemma wf_pred_sexp [THEN wf_trancl]]


(** pred_sexp lemmas **)

lemma pred_sexp_CONS_I1: 
    "[| M: sexp;  N: sexp |] ==> (M, CONS M N) : pred_sexp^+"
by (simp add: CONS_def In1_def)

lemma pred_sexp_CONS_I2: 
    "[| M: sexp;  N: sexp |] ==> (N, CONS M N) : pred_sexp^+"
by (simp add: CONS_def In1_def)

lemma pred_sexp_CONS_D: 
    "(CONS M1 M2, N) : pred_sexp^+ ==>  
     (M1,N) : pred_sexp^+ & (M2,N) : pred_sexp^+"
apply (frule pred_sexp_subset_Sigma [THEN trancl_subset_Sigma, THEN subsetD])
apply (blast dest!: sexp_CONS_D intro: pred_sexp_CONS_I1 pred_sexp_CONS_I2 
                    trans_trancl [THEN transD])
done


(** Conversion rules for List_rec **)

lemma List_rec_NIL [simp]: "List_rec NIL c h = c"
apply (rule List_rec_unfold [THEN trans])
apply (simp add: List_case_NIL)
done

lemma List_rec_CONS [simp]:
     "[| M: sexp;  N: sexp |] 
      ==> List_rec (CONS M N) c h = h M N (List_rec N c h)"
apply (rule List_rec_unfold [THEN trans])
apply (simp add: pred_sexp_CONS_I2)
done


(*** list_rec -- by List_rec ***)

lemmas Rep_List_in_sexp =
    subsetD [OF range_Leaf_subset_sexp [THEN list_subset_sexp]
                Rep_List [THEN ListD]] 


lemma list_rec_Nil [simp]: "list_rec Nil c h = c"
by (simp add: list_rec_def ListI [THEN Abs_List_inverse] Nil_def)


lemma list_rec_Cons [simp]: "list_rec (a#l) c h = h a l (list_rec l c h)"
by (simp add: list_rec_def ListI [THEN Abs_List_inverse] Cons_def
              Rep_List_inverse Rep_List [THEN ListD] inj_Leaf Rep_List_in_sexp)


(*Type checking.  Useful?*)
lemma List_rec_type:
     "[| M: list(A);      
         A<=sexp;         
         c: C(NIL);       
         !!x y r. [| x: A;  y: list(A);  r: C(y) |] ==> h x y r: C(CONS x y)  
      |] ==> List_rec M c h : C(M :: 'a item)"
apply (erule list.induct, simp) 
apply (insert list_subset_sexp) 
apply (subst List_rec_CONS, blast+)
done



(** Generalized map functionals **)

lemma Rep_map_Nil [simp]: "Rep_map f Nil = NIL"
by (simp add: Rep_map_def)

lemma Rep_map_Cons [simp]: 
    "Rep_map f(x#xs) = CONS(f x)(Rep_map f xs)"
by (simp add: Rep_map_def)

lemma Rep_map_type: "(!!x. f(x): A) ==> Rep_map f xs: list(A)"
apply (simp add: Rep_map_def)
apply (rule list_induct, auto)
done

lemma Abs_map_NIL [simp]: "Abs_map g NIL = Nil"
by (simp add: Abs_map_def)

lemma Abs_map_CONS [simp]: 
    "[| M: sexp;  N: sexp |] ==> Abs_map g (CONS M N) = g(M) # Abs_map g N"
by (simp add: Abs_map_def)

(*Eases the use of primitive recursion.*)
lemma def_list_rec_NilCons:
    "[| !!xs. f(xs) = list_rec xs c h  |] 
     ==> f [] = c & f(x#xs) = h x xs (f xs)"
by simp 

lemma Abs_map_inverse:
     "[| M: list(A);  A<=sexp;  !!z. z: A ==> f(g(z)) = z |]  
      ==> Rep_map f (Abs_map g M) = M"
apply (erule list.induct, simp_all)
apply (insert list_subset_sexp) 
apply (subst Abs_map_CONS, blast)
apply blast 
apply simp 
done

(*Rep_map_inverse is obtained via Abs_Rep_map and map_ident*)

(** list_case **)

(* setting up rewrite sets *)

text{*Better to have a single theorem with a conjunctive conclusion.*}
declare def_list_rec_NilCons [OF list_case_def, simp]

(** list_case **)

lemma expand_list_case: 
 "P(list_case a f xs) = ((xs=[] --> P a ) & (!y ys. xs=y#ys --> P(f y ys)))"
by (induct xs rule: list_induct) simp_all


(**** Function definitions ****)

declare def_list_rec_NilCons [OF map_def, simp]

(** The functional "map" and the generalized functionals **)

lemma Abs_Rep_map: 
     "(!!x. f(x): sexp) ==>  
        Abs_map g (Rep_map f xs) = map (%t. g(f(t))) xs"
apply (induct xs rule: list_induct)
apply (simp_all add: Rep_map_type list_sexp [THEN subsetD])
done


(** Additional mapping lemmas **)

lemma map_ident [simp]: "map(%x. x)(xs) = xs"
by (induct xs rule: list_induct) simp_all

lemma map_compose: "map(f o g)(xs) = map f (map g xs)"
apply (simp add: o_def)
apply (induct xs rule: list_induct)
apply simp_all
done


(** take **)

lemma take_Suc1 [simp]: "take [] (Suc x) = []"
by simp

lemma take_Suc2 [simp]: "take(a#xs)(Suc x) = a#take xs x"
by simp

lemma take_Nil [simp]: "take [] n = []"
by (induct n) simp_all

lemma take_take_eq [simp]: "\<forall>n. take (take xs n) n = take xs n"
apply (induct xs rule: list_induct)
apply simp_all
apply (rule allI)
apply (induct_tac n)
apply auto
done

end
