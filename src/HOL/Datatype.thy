(*  Title:      HOL/Datatype.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Stefan Berghofer and Markus Wenzel, TU Muenchen
*)

header {* Datatype package: constructing datatypes from Cartesian Products and Disjoint Sums *}

theory Datatype
imports Product_Type Sum_Type Nat
uses
  ("Tools/Datatype/datatype.ML")
  ("Tools/inductive_realizer.ML")
  ("Tools/Datatype/datatype_realizer.ML")
begin

subsection {* Prelude: lifting over function space *}

enriched_type map_fun: map_fun
  by (simp_all add: fun_eq_iff)


subsection {* The datatype universe *}

typedef (Node)
  ('a,'b) node = "{p. EX f x k. p = (f::nat=>'b+nat, x::'a+nat) & f k = Inr 0}"
    --{*it is a subtype of @{text "(nat=>'b+nat) * ('a+nat)"}*}
  by auto

text{*Datatypes will be represented by sets of type @{text node}*}

type_synonym 'a item        = "('a, unit) node set"
type_synonym ('a, 'b) dtree = "('a, 'b) node set"

consts
  Push      :: "[('b + nat), nat => ('b + nat)] => (nat => ('b + nat))"

  Push_Node :: "[('b + nat), ('a, 'b) node] => ('a, 'b) node"
  ndepth    :: "('a, 'b) node => nat"

  Atom      :: "('a + nat) => ('a, 'b) dtree"
  Leaf      :: "'a => ('a, 'b) dtree"
  Numb      :: "nat => ('a, 'b) dtree"
  Scons     :: "[('a, 'b) dtree, ('a, 'b) dtree] => ('a, 'b) dtree"
  In0       :: "('a, 'b) dtree => ('a, 'b) dtree"
  In1       :: "('a, 'b) dtree => ('a, 'b) dtree"
  Lim       :: "('b => ('a, 'b) dtree) => ('a, 'b) dtree"

  ntrunc    :: "[nat, ('a, 'b) dtree] => ('a, 'b) dtree"

  uprod     :: "[('a, 'b) dtree set, ('a, 'b) dtree set]=> ('a, 'b) dtree set"
  usum      :: "[('a, 'b) dtree set, ('a, 'b) dtree set]=> ('a, 'b) dtree set"

  Split     :: "[[('a, 'b) dtree, ('a, 'b) dtree]=>'c, ('a, 'b) dtree] => 'c"
  Case      :: "[[('a, 'b) dtree]=>'c, [('a, 'b) dtree]=>'c, ('a, 'b) dtree] => 'c"

  dprod     :: "[(('a, 'b) dtree * ('a, 'b) dtree)set, (('a, 'b) dtree * ('a, 'b) dtree)set]
                => (('a, 'b) dtree * ('a, 'b) dtree)set"
  dsum      :: "[(('a, 'b) dtree * ('a, 'b) dtree)set, (('a, 'b) dtree * ('a, 'b) dtree)set]
                => (('a, 'b) dtree * ('a, 'b) dtree)set"


defs

  Push_Node_def:  "Push_Node == (%n x. Abs_Node (apfst (Push n) (Rep_Node x)))"

  (*crude "lists" of nats -- needed for the constructions*)
  Push_def:   "Push == (%b h. nat_case b h)"

  (** operations on S-expressions -- sets of nodes **)

  (*S-expression constructors*)
  Atom_def:   "Atom == (%x. {Abs_Node((%k. Inr 0, x))})"
  Scons_def:  "Scons M N == (Push_Node (Inr 1) ` M) Un (Push_Node (Inr (Suc 1)) ` N)"

  (*Leaf nodes, with arbitrary or nat labels*)
  Leaf_def:   "Leaf == Atom o Inl"
  Numb_def:   "Numb == Atom o Inr"

  (*Injections of the "disjoint sum"*)
  In0_def:    "In0(M) == Scons (Numb 0) M"
  In1_def:    "In1(M) == Scons (Numb 1) M"

  (*Function spaces*)
  Lim_def: "Lim f == Union {z. ? x. z = Push_Node (Inl x) ` (f x)}"

  (*the set of nodes with depth less than k*)
  ndepth_def: "ndepth(n) == (%(f,x). LEAST k. f k = Inr 0) (Rep_Node n)"
  ntrunc_def: "ntrunc k N == {n. n:N & ndepth(n)<k}"

  (*products and sums for the "universe"*)
  uprod_def:  "uprod A B == UN x:A. UN y:B. { Scons x y }"
  usum_def:   "usum A B == In0`A Un In1`B"

  (*the corresponding eliminators*)
  Split_def:  "Split c M == THE u. EX x y. M = Scons x y & u = c x y"

  Case_def:   "Case c d M == THE u.  (EX x . M = In0(x) & u = c(x))
                                  | (EX y . M = In1(y) & u = d(y))"


  (** equality for the "universe" **)

  dprod_def:  "dprod r s == UN (x,x'):r. UN (y,y'):s. {(Scons x y, Scons x' y')}"

  dsum_def:   "dsum r s == (UN (x,x'):r. {(In0(x),In0(x'))}) Un
                          (UN (y,y'):s. {(In1(y),In1(y'))})"



lemma apfst_convE: 
    "[| q = apfst f p;  !!x y. [| p = (x,y);  q = (f(x),y) |] ==> R  
     |] ==> R"
by (force simp add: apfst_def)

(** Push -- an injection, analogous to Cons on lists **)

lemma Push_inject1: "Push i f = Push j g  ==> i=j"
apply (simp add: Push_def fun_eq_iff) 
apply (drule_tac x=0 in spec, simp) 
done

lemma Push_inject2: "Push i f = Push j g  ==> f=g"
apply (auto simp add: Push_def fun_eq_iff) 
apply (drule_tac x="Suc x" in spec, simp) 
done

lemma Push_inject:
    "[| Push i f =Push j g;  [| i=j;  f=g |] ==> P |] ==> P"
by (blast dest: Push_inject1 Push_inject2) 

lemma Push_neq_K0: "Push (Inr (Suc k)) f = (%z. Inr 0) ==> P"
by (auto simp add: Push_def fun_eq_iff split: nat.split_asm)

lemmas Abs_Node_inj = Abs_Node_inject [THEN [2] rev_iffD1]


(*** Introduction rules for Node ***)

lemma Node_K0_I: "(%k. Inr 0, a) : Node"
by (simp add: Node_def)

lemma Node_Push_I: "p: Node ==> apfst (Push i) p : Node"
apply (simp add: Node_def Push_def) 
apply (fast intro!: apfst_conv nat_case_Suc [THEN trans])
done


subsection{*Freeness: Distinctness of Constructors*}

(** Scons vs Atom **)

lemma Scons_not_Atom [iff]: "Scons M N \<noteq> Atom(a)"
unfolding Atom_def Scons_def Push_Node_def One_nat_def
by (blast intro: Node_K0_I Rep_Node [THEN Node_Push_I] 
         dest!: Abs_Node_inj 
         elim!: apfst_convE sym [THEN Push_neq_K0])  

lemmas Atom_not_Scons [iff] = Scons_not_Atom [THEN not_sym]


(*** Injectiveness ***)

(** Atomic nodes **)

lemma inj_Atom: "inj(Atom)"
apply (simp add: Atom_def)
apply (blast intro!: inj_onI Node_K0_I dest!: Abs_Node_inj)
done
lemmas Atom_inject = inj_Atom [THEN injD]

lemma Atom_Atom_eq [iff]: "(Atom(a)=Atom(b)) = (a=b)"
by (blast dest!: Atom_inject)

lemma inj_Leaf: "inj(Leaf)"
apply (simp add: Leaf_def o_def)
apply (rule inj_onI)
apply (erule Atom_inject [THEN Inl_inject])
done

lemmas Leaf_inject [dest!] = inj_Leaf [THEN injD]

lemma inj_Numb: "inj(Numb)"
apply (simp add: Numb_def o_def)
apply (rule inj_onI)
apply (erule Atom_inject [THEN Inr_inject])
done

lemmas Numb_inject [dest!] = inj_Numb [THEN injD]


(** Injectiveness of Push_Node **)

lemma Push_Node_inject:
    "[| Push_Node i m =Push_Node j n;  [| i=j;  m=n |] ==> P  
     |] ==> P"
apply (simp add: Push_Node_def)
apply (erule Abs_Node_inj [THEN apfst_convE])
apply (rule Rep_Node [THEN Node_Push_I])+
apply (erule sym [THEN apfst_convE]) 
apply (blast intro: Rep_Node_inject [THEN iffD1] trans sym elim!: Push_inject)
done


(** Injectiveness of Scons **)

lemma Scons_inject_lemma1: "Scons M N <= Scons M' N' ==> M<=M'"
unfolding Scons_def One_nat_def
by (blast dest!: Push_Node_inject)

lemma Scons_inject_lemma2: "Scons M N <= Scons M' N' ==> N<=N'"
unfolding Scons_def One_nat_def
by (blast dest!: Push_Node_inject)

lemma Scons_inject1: "Scons M N = Scons M' N' ==> M=M'"
apply (erule equalityE)
apply (iprover intro: equalityI Scons_inject_lemma1)
done

lemma Scons_inject2: "Scons M N = Scons M' N' ==> N=N'"
apply (erule equalityE)
apply (iprover intro: equalityI Scons_inject_lemma2)
done

lemma Scons_inject:
    "[| Scons M N = Scons M' N';  [| M=M';  N=N' |] ==> P |] ==> P"
by (iprover dest: Scons_inject1 Scons_inject2)

lemma Scons_Scons_eq [iff]: "(Scons M N = Scons M' N') = (M=M' & N=N')"
by (blast elim!: Scons_inject)

(*** Distinctness involving Leaf and Numb ***)

(** Scons vs Leaf **)

lemma Scons_not_Leaf [iff]: "Scons M N \<noteq> Leaf(a)"
unfolding Leaf_def o_def by (rule Scons_not_Atom)

lemmas Leaf_not_Scons  [iff] = Scons_not_Leaf [THEN not_sym]

(** Scons vs Numb **)

lemma Scons_not_Numb [iff]: "Scons M N \<noteq> Numb(k)"
unfolding Numb_def o_def by (rule Scons_not_Atom)

lemmas Numb_not_Scons [iff] = Scons_not_Numb [THEN not_sym]


(** Leaf vs Numb **)

lemma Leaf_not_Numb [iff]: "Leaf(a) \<noteq> Numb(k)"
by (simp add: Leaf_def Numb_def)

lemmas Numb_not_Leaf [iff] = Leaf_not_Numb [THEN not_sym]


(*** ndepth -- the depth of a node ***)

lemma ndepth_K0: "ndepth (Abs_Node(%k. Inr 0, x)) = 0"
by (simp add: ndepth_def  Node_K0_I [THEN Abs_Node_inverse] Least_equality)

lemma ndepth_Push_Node_aux:
     "nat_case (Inr (Suc i)) f k = Inr 0 --> Suc(LEAST x. f x = Inr 0) <= k"
apply (induct_tac "k", auto)
apply (erule Least_le)
done

lemma ndepth_Push_Node: 
    "ndepth (Push_Node (Inr (Suc i)) n) = Suc(ndepth(n))"
apply (insert Rep_Node [of n, unfolded Node_def])
apply (auto simp add: ndepth_def Push_Node_def
                 Rep_Node [THEN Node_Push_I, THEN Abs_Node_inverse])
apply (rule Least_equality)
apply (auto simp add: Push_def ndepth_Push_Node_aux)
apply (erule LeastI)
done


(*** ntrunc applied to the various node sets ***)

lemma ntrunc_0 [simp]: "ntrunc 0 M = {}"
by (simp add: ntrunc_def)

lemma ntrunc_Atom [simp]: "ntrunc (Suc k) (Atom a) = Atom(a)"
by (auto simp add: Atom_def ntrunc_def ndepth_K0)

lemma ntrunc_Leaf [simp]: "ntrunc (Suc k) (Leaf a) = Leaf(a)"
unfolding Leaf_def o_def by (rule ntrunc_Atom)

lemma ntrunc_Numb [simp]: "ntrunc (Suc k) (Numb i) = Numb(i)"
unfolding Numb_def o_def by (rule ntrunc_Atom)

lemma ntrunc_Scons [simp]: 
    "ntrunc (Suc k) (Scons M N) = Scons (ntrunc k M) (ntrunc k N)"
unfolding Scons_def ntrunc_def One_nat_def
by (auto simp add: ndepth_Push_Node)



(** Injection nodes **)

lemma ntrunc_one_In0 [simp]: "ntrunc (Suc 0) (In0 M) = {}"
apply (simp add: In0_def)
apply (simp add: Scons_def)
done

lemma ntrunc_In0 [simp]: "ntrunc (Suc(Suc k)) (In0 M) = In0 (ntrunc (Suc k) M)"
by (simp add: In0_def)

lemma ntrunc_one_In1 [simp]: "ntrunc (Suc 0) (In1 M) = {}"
apply (simp add: In1_def)
apply (simp add: Scons_def)
done

lemma ntrunc_In1 [simp]: "ntrunc (Suc(Suc k)) (In1 M) = In1 (ntrunc (Suc k) M)"
by (simp add: In1_def)


subsection{*Set Constructions*}


(*** Cartesian Product ***)

lemma uprodI [intro!]: "[| M:A;  N:B |] ==> Scons M N : uprod A B"
by (simp add: uprod_def)

(*The general elimination rule*)
lemma uprodE [elim!]:
    "[| c : uprod A B;   
        !!x y. [| x:A;  y:B;  c = Scons x y |] ==> P  
     |] ==> P"
by (auto simp add: uprod_def) 


(*Elimination of a pair -- introduces no eigenvariables*)
lemma uprodE2: "[| Scons M N : uprod A B;  [| M:A;  N:B |] ==> P |] ==> P"
by (auto simp add: uprod_def)


(*** Disjoint Sum ***)

lemma usum_In0I [intro]: "M:A ==> In0(M) : usum A B"
by (simp add: usum_def)

lemma usum_In1I [intro]: "N:B ==> In1(N) : usum A B"
by (simp add: usum_def)

lemma usumE [elim!]: 
    "[| u : usum A B;   
        !!x. [| x:A;  u=In0(x) |] ==> P;  
        !!y. [| y:B;  u=In1(y) |] ==> P  
     |] ==> P"
by (auto simp add: usum_def)


(** Injection **)

lemma In0_not_In1 [iff]: "In0(M) \<noteq> In1(N)"
unfolding In0_def In1_def One_nat_def by auto

lemmas In1_not_In0 [iff] = In0_not_In1 [THEN not_sym]

lemma In0_inject: "In0(M) = In0(N) ==>  M=N"
by (simp add: In0_def)

lemma In1_inject: "In1(M) = In1(N) ==>  M=N"
by (simp add: In1_def)

lemma In0_eq [iff]: "(In0 M = In0 N) = (M=N)"
by (blast dest!: In0_inject)

lemma In1_eq [iff]: "(In1 M = In1 N) = (M=N)"
by (blast dest!: In1_inject)

lemma inj_In0: "inj In0"
by (blast intro!: inj_onI)

lemma inj_In1: "inj In1"
by (blast intro!: inj_onI)


(*** Function spaces ***)

lemma Lim_inject: "Lim f = Lim g ==> f = g"
apply (simp add: Lim_def)
apply (rule ext)
apply (blast elim!: Push_Node_inject)
done


(*** proving equality of sets and functions using ntrunc ***)

lemma ntrunc_subsetI: "ntrunc k M <= M"
by (auto simp add: ntrunc_def)

lemma ntrunc_subsetD: "(!!k. ntrunc k M <= N) ==> M<=N"
by (auto simp add: ntrunc_def)

(*A generalized form of the take-lemma*)
lemma ntrunc_equality: "(!!k. ntrunc k M = ntrunc k N) ==> M=N"
apply (rule equalityI)
apply (rule_tac [!] ntrunc_subsetD)
apply (rule_tac [!] ntrunc_subsetI [THEN [2] subset_trans], auto) 
done

lemma ntrunc_o_equality: 
    "[| !!k. (ntrunc(k) o h1) = (ntrunc(k) o h2) |] ==> h1=h2"
apply (rule ntrunc_equality [THEN ext])
apply (simp add: fun_eq_iff) 
done


(*** Monotonicity ***)

lemma uprod_mono: "[| A<=A';  B<=B' |] ==> uprod A B <= uprod A' B'"
by (simp add: uprod_def, blast)

lemma usum_mono: "[| A<=A';  B<=B' |] ==> usum A B <= usum A' B'"
by (simp add: usum_def, blast)

lemma Scons_mono: "[| M<=M';  N<=N' |] ==> Scons M N <= Scons M' N'"
by (simp add: Scons_def, blast)

lemma In0_mono: "M<=N ==> In0(M) <= In0(N)"
by (simp add: In0_def Scons_mono)

lemma In1_mono: "M<=N ==> In1(M) <= In1(N)"
by (simp add: In1_def Scons_mono)


(*** Split and Case ***)

lemma Split [simp]: "Split c (Scons M N) = c M N"
by (simp add: Split_def)

lemma Case_In0 [simp]: "Case c d (In0 M) = c(M)"
by (simp add: Case_def)

lemma Case_In1 [simp]: "Case c d (In1 N) = d(N)"
by (simp add: Case_def)



(**** UN x. B(x) rules ****)

lemma ntrunc_UN1: "ntrunc k (UN x. f(x)) = (UN x. ntrunc k (f x))"
by (simp add: ntrunc_def, blast)

lemma Scons_UN1_x: "Scons (UN x. f x) M = (UN x. Scons (f x) M)"
by (simp add: Scons_def, blast)

lemma Scons_UN1_y: "Scons M (UN x. f x) = (UN x. Scons M (f x))"
by (simp add: Scons_def, blast)

lemma In0_UN1: "In0(UN x. f(x)) = (UN x. In0(f(x)))"
by (simp add: In0_def Scons_UN1_y)

lemma In1_UN1: "In1(UN x. f(x)) = (UN x. In1(f(x)))"
by (simp add: In1_def Scons_UN1_y)


(*** Equality for Cartesian Product ***)

lemma dprodI [intro!]: 
    "[| (M,M'):r;  (N,N'):s |] ==> (Scons M N, Scons M' N') : dprod r s"
by (auto simp add: dprod_def)

(*The general elimination rule*)
lemma dprodE [elim!]: 
    "[| c : dprod r s;   
        !!x y x' y'. [| (x,x') : r;  (y,y') : s;  
                        c = (Scons x y, Scons x' y') |] ==> P  
     |] ==> P"
by (auto simp add: dprod_def)


(*** Equality for Disjoint Sum ***)

lemma dsum_In0I [intro]: "(M,M'):r ==> (In0(M), In0(M')) : dsum r s"
by (auto simp add: dsum_def)

lemma dsum_In1I [intro]: "(N,N'):s ==> (In1(N), In1(N')) : dsum r s"
by (auto simp add: dsum_def)

lemma dsumE [elim!]: 
    "[| w : dsum r s;   
        !!x x'. [| (x,x') : r;  w = (In0(x), In0(x')) |] ==> P;  
        !!y y'. [| (y,y') : s;  w = (In1(y), In1(y')) |] ==> P  
     |] ==> P"
by (auto simp add: dsum_def)


(*** Monotonicity ***)

lemma dprod_mono: "[| r<=r';  s<=s' |] ==> dprod r s <= dprod r' s'"
by blast

lemma dsum_mono: "[| r<=r';  s<=s' |] ==> dsum r s <= dsum r' s'"
by blast


(*** Bounding theorems ***)

lemma dprod_Sigma: "(dprod (A <*> B) (C <*> D)) <= (uprod A C) <*> (uprod B D)"
by blast

lemmas dprod_subset_Sigma = subset_trans [OF dprod_mono dprod_Sigma]

(*Dependent version*)
lemma dprod_subset_Sigma2:
     "(dprod (Sigma A B) (Sigma C D)) <= 
      Sigma (uprod A C) (Split (%x y. uprod (B x) (D y)))"
by auto

lemma dsum_Sigma: "(dsum (A <*> B) (C <*> D)) <= (usum A C) <*> (usum B D)"
by blast

lemmas dsum_subset_Sigma = subset_trans [OF dsum_mono dsum_Sigma]


text {* hides popular names *}
hide_type (open) node item
hide_const (open) Push Node Atom Leaf Numb Lim Split Case

use "Tools/Datatype/datatype.ML"

use "Tools/inductive_realizer.ML"
setup InductiveRealizer.setup

use "Tools/Datatype/datatype_realizer.ML"
setup Datatype_Realizer.setup

end
