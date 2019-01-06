(*  Title:      HOL/Library/Old_Datatype.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Stefan Berghofer and Markus Wenzel, TU Muenchen
*)

section \<open>Old Datatype package: constructing datatypes from Cartesian Products and Disjoint Sums\<close>

theory Old_Datatype
imports Main
begin


subsection \<open>The datatype universe\<close>

definition "Node = {p. \<exists>f x k. p = (f :: nat => 'b + nat, x ::'a + nat) \<and> f k = Inr 0}"

typedef ('a, 'b) node = "Node :: ((nat => 'b + nat) * ('a + nat)) set"
  morphisms Rep_Node Abs_Node
  unfolding Node_def by auto

text\<open>Datatypes will be represented by sets of type \<open>node\<close>\<close>

type_synonym 'a item        = "('a, unit) node set"
type_synonym ('a, 'b) dtree = "('a, 'b) node set"

definition Push :: "[('b + nat), nat => ('b + nat)] => (nat => ('b + nat))"
  (*crude "lists" of nats -- needed for the constructions*)
  where "Push == (%b h. case_nat b h)"

definition Push_Node :: "[('b + nat), ('a, 'b) node] => ('a, 'b) node"
  where "Push_Node == (%n x. Abs_Node (apfst (Push n) (Rep_Node x)))"


(** operations on S-expressions -- sets of nodes **)

(*S-expression constructors*)
definition Atom :: "('a + nat) => ('a, 'b) dtree"
  where "Atom == (%x. {Abs_Node((%k. Inr 0, x))})"
definition Scons :: "[('a, 'b) dtree, ('a, 'b) dtree] => ('a, 'b) dtree"
  where "Scons M N == (Push_Node (Inr 1) ` M) Un (Push_Node (Inr (Suc 1)) ` N)"

(*Leaf nodes, with arbitrary or nat labels*)
definition Leaf :: "'a => ('a, 'b) dtree"
  where "Leaf == Atom \<circ> Inl"
definition Numb :: "nat => ('a, 'b) dtree"
  where "Numb == Atom \<circ> Inr"

(*Injections of the "disjoint sum"*)
definition In0 :: "('a, 'b) dtree => ('a, 'b) dtree"
  where "In0(M) == Scons (Numb 0) M"
definition In1 :: "('a, 'b) dtree => ('a, 'b) dtree"
  where "In1(M) == Scons (Numb 1) M"

(*Function spaces*)
definition Lim :: "('b => ('a, 'b) dtree) => ('a, 'b) dtree"
  where "Lim f == \<Union>{z. \<exists>x. z = Push_Node (Inl x) ` (f x)}"

(*the set of nodes with depth less than k*)
definition ndepth :: "('a, 'b) node => nat"
  where "ndepth(n) == (%(f,x). LEAST k. f k = Inr 0) (Rep_Node n)"
definition ntrunc :: "[nat, ('a, 'b) dtree] => ('a, 'b) dtree"
  where "ntrunc k N == {n. n\<in>N \<and> ndepth(n)<k}"

(*products and sums for the "universe"*)
definition uprod :: "[('a, 'b) dtree set, ('a, 'b) dtree set]=> ('a, 'b) dtree set"
  where "uprod A B == UN x:A. UN y:B. { Scons x y }"
definition usum :: "[('a, 'b) dtree set, ('a, 'b) dtree set]=> ('a, 'b) dtree set"
  where "usum A B == In0`A Un In1`B"

(*the corresponding eliminators*)
definition Split :: "[[('a, 'b) dtree, ('a, 'b) dtree]=>'c, ('a, 'b) dtree] => 'c"
  where "Split c M == THE u. \<exists>x y. M = Scons x y \<and> u = c x y"

definition Case :: "[[('a, 'b) dtree]=>'c, [('a, 'b) dtree]=>'c, ('a, 'b) dtree] => 'c"
  where "Case c d M == THE u. (\<exists>x . M = In0(x) \<and> u = c(x)) \<or> (\<exists>y . M = In1(y) \<and> u = d(y))"


(** equality for the "universe" **)

definition dprod :: "[(('a, 'b) dtree * ('a, 'b) dtree)set, (('a, 'b) dtree * ('a, 'b) dtree)set]
      => (('a, 'b) dtree * ('a, 'b) dtree)set"
  where "dprod r s == UN (x,x'):r. UN (y,y'):s. {(Scons x y, Scons x' y')}"

definition dsum :: "[(('a, 'b) dtree * ('a, 'b) dtree)set, (('a, 'b) dtree * ('a, 'b) dtree)set]
      => (('a, 'b) dtree * ('a, 'b) dtree)set"
  where "dsum r s == (UN (x,x'):r. {(In0(x),In0(x'))}) Un (UN (y,y'):s. {(In1(y),In1(y'))})"


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

lemma Node_K0_I: "(\<lambda>k. Inr 0, a) \<in> Node"
by (simp add: Node_def)

lemma Node_Push_I: "p \<in> Node \<Longrightarrow> apfst (Push i) p \<in> Node"
apply (simp add: Node_def Push_def) 
apply (fast intro!: apfst_conv nat.case(2)[THEN trans])
done


subsection\<open>Freeness: Distinctness of Constructors\<close>

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

lemma Scons_Scons_eq [iff]: "(Scons M N = Scons M' N') = (M=M' \<and> N=N')"
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
     "case_nat (Inr (Suc i)) f k = Inr 0 \<longrightarrow> Suc(LEAST x. f x = Inr 0) \<le> k"
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


subsection\<open>Set Constructions\<close>


(*** Cartesian Product ***)

lemma uprodI [intro!]: "\<lbrakk>M\<in>A; N\<in>B\<rbrakk> \<Longrightarrow> Scons M N \<in> uprod A B"
by (simp add: uprod_def)

(*The general elimination rule*)
lemma uprodE [elim!]:
    "\<lbrakk>c \<in> uprod A B;   
        \<And>x y. \<lbrakk>x \<in> A; y \<in> B; c = Scons x y\<rbrakk> \<Longrightarrow> P  
     \<rbrakk> \<Longrightarrow> P"
by (auto simp add: uprod_def) 


(*Elimination of a pair -- introduces no eigenvariables*)
lemma uprodE2: "\<lbrakk>Scons M N \<in> uprod A B; \<lbrakk>M \<in> A; N \<in> B\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
by (auto simp add: uprod_def)


(*** Disjoint Sum ***)

lemma usum_In0I [intro]: "M \<in> A \<Longrightarrow> In0(M) \<in> usum A B"
by (simp add: usum_def)

lemma usum_In1I [intro]: "N \<in> B \<Longrightarrow> In1(N) \<in> usum A B"
by (simp add: usum_def)

lemma usumE [elim!]: 
    "\<lbrakk>u \<in> usum A B;   
        \<And>x. \<lbrakk>x \<in> A; u=In0(x)\<rbrakk> \<Longrightarrow> P;  
        \<And>y. \<lbrakk>y \<in> B; u=In1(y)\<rbrakk> \<Longrightarrow> P  
     \<rbrakk> \<Longrightarrow> P"
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
    "[| !!k. (ntrunc(k) \<circ> h1) = (ntrunc(k) \<circ> h2) |] ==> h1=h2"
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
    "\<lbrakk>(M,M') \<in> r; (N,N') \<in> s\<rbrakk> \<Longrightarrow> (Scons M N, Scons M' N') \<in> dprod r s"
by (auto simp add: dprod_def)

(*The general elimination rule*)
lemma dprodE [elim!]: 
    "\<lbrakk>c \<in> dprod r s;   
        \<And>x y x' y'. \<lbrakk>(x,x') \<in> r; (y,y') \<in> s;  
                        c = (Scons x y, Scons x' y')\<rbrakk> \<Longrightarrow> P  
     \<rbrakk> \<Longrightarrow> P"
by (auto simp add: dprod_def)


(*** Equality for Disjoint Sum ***)

lemma dsum_In0I [intro]: "(M,M') \<in> r \<Longrightarrow> (In0(M), In0(M')) \<in> dsum r s"
by (auto simp add: dsum_def)

lemma dsum_In1I [intro]: "(N,N') \<in> s \<Longrightarrow> (In1(N), In1(N')) \<in> dsum r s"
by (auto simp add: dsum_def)

lemma dsumE [elim!]: 
    "\<lbrakk>w \<in> dsum r s;   
        \<And>x x'. \<lbrakk> (x,x') \<in> r;  w = (In0(x), In0(x')) \<rbrakk> \<Longrightarrow> P;  
        \<And>y y'. \<lbrakk> (y,y') \<in> s;  w = (In1(y), In1(y')) \<rbrakk> \<Longrightarrow> P  
     \<rbrakk> \<Longrightarrow> P"
by (auto simp add: dsum_def)


(*** Monotonicity ***)

lemma dprod_mono: "[| r<=r';  s<=s' |] ==> dprod r s <= dprod r' s'"
by blast

lemma dsum_mono: "[| r<=r';  s<=s' |] ==> dsum r s <= dsum r' s'"
by blast


(*** Bounding theorems ***)

lemma dprod_Sigma: "(dprod (A \<times> B) (C \<times> D)) <= (uprod A C) \<times> (uprod B D)"
by blast

lemmas dprod_subset_Sigma = subset_trans [OF dprod_mono dprod_Sigma]

(*Dependent version*)
lemma dprod_subset_Sigma2:
    "(dprod (Sigma A B) (Sigma C D)) <= Sigma (uprod A C) (Split (%x y. uprod (B x) (D y)))"
by auto

lemma dsum_Sigma: "(dsum (A \<times> B) (C \<times> D)) <= (usum A C) \<times> (usum B D)"
by blast

lemmas dsum_subset_Sigma = subset_trans [OF dsum_mono dsum_Sigma]


(*** Domain theorems ***)

lemma Domain_dprod [simp]: "Domain (dprod r s) = uprod (Domain r) (Domain s)"
  by auto

lemma Domain_dsum [simp]: "Domain (dsum r s) = usum (Domain r) (Domain s)"
  by auto


text \<open>hides popular names\<close>
hide_type (open) node item
hide_const (open) Push Node Atom Leaf Numb Lim Split Case

ML_file \<open>~~/src/HOL/Tools/Old_Datatype/old_datatype.ML\<close>

end
