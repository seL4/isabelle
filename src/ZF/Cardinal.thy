(*  Title:      ZF/Cardinal.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

*)

header{*Cardinal Numbers Without the Axiom of Choice*}

theory Cardinal = OrderType + Finite + Nat + Sum:

(*** The following really belong in upair ***)

lemma eq_imp_not_mem: "a=A ==> a ~: A"
by (blast intro: elim: mem_irrefl)

constdefs

  (*least ordinal operator*)
   Least    :: "(i=>o) => i"    (binder "LEAST " 10)
     "Least(P) == THE i. Ord(i) & P(i) & (ALL j. j<i --> ~P(j))"

  eqpoll   :: "[i,i] => o"     (infixl "eqpoll" 50)
    "A eqpoll B == EX f. f: bij(A,B)"

  lepoll   :: "[i,i] => o"     (infixl "lepoll" 50)
    "A lepoll B == EX f. f: inj(A,B)"

  lesspoll :: "[i,i] => o"     (infixl "lesspoll" 50)
    "A lesspoll B == A lepoll B & ~(A eqpoll B)"

  cardinal :: "i=>i"           ("|_|")
    "|A| == LEAST i. i eqpoll A"

  Finite   :: "i=>o"
    "Finite(A) == EX n:nat. A eqpoll n"

  Card     :: "i=>o"
    "Card(i) == (i = |i|)"

syntax (xsymbols)
  "eqpoll"      :: "[i,i] => o"       (infixl "\<approx>" 50)
  "lepoll"      :: "[i,i] => o"       (infixl "\<lesssim>" 50)
  "lesspoll"    :: "[i,i] => o"       (infixl "\<prec>" 50)
  "LEAST "         :: "[pttrn, o] => i"  ("(3\<mu>_./ _)" [0, 10] 10)

(*** The Schroeder-Bernstein Theorem -- see Davey & Priestly, page 106 ***)

(** Lemma: Banach's Decomposition Theorem **)

lemma decomp_bnd_mono: "bnd_mono(X, %W. X - g``(Y - f``W))"
by (rule bnd_monoI, blast+)

lemma Banach_last_equation:
    "g: Y->X
     ==> g``(Y - f`` lfp(X, %W. X - g``(Y - f``W))) =        
	 X - lfp(X, %W. X - g``(Y - f``W))" 
apply (rule_tac P = "%u. ?v = X-u" 
       in decomp_bnd_mono [THEN lfp_unfold, THEN ssubst])
apply (simp add: double_complement  fun_is_rel [THEN image_subset])
done

lemma decomposition:
     "[| f: X->Y;  g: Y->X |] ==>    
      EX XA XB YA YB. (XA Int XB = 0) & (XA Un XB = X) &     
                      (YA Int YB = 0) & (YA Un YB = Y) &     
                      f``XA=YA & g``YB=XB"
apply (intro exI conjI)
apply (rule_tac [6] Banach_last_equation)
apply (rule_tac [5] refl)
apply (assumption | 
       rule  Diff_disjoint Diff_partition fun_is_rel image_subset lfp_subset)+
done

lemma schroeder_bernstein:
    "[| f: inj(X,Y);  g: inj(Y,X) |] ==> EX h. h: bij(X,Y)"
apply (insert decomposition [of f X Y g]) 
apply (simp add: inj_is_fun)
apply (blast intro!: restrict_bij bij_disjoint_Un intro: bij_converse_bij)
(* The instantiation of exI to "restrict(f,XA) Un converse(restrict(g,YB))"
   is forced by the context!! *)
done


(** Equipollence is an equivalence relation **)

lemma bij_imp_eqpoll: "f: bij(A,B) ==> A \<approx> B"
apply (unfold eqpoll_def)
apply (erule exI)
done

(*A eqpoll A*)
lemmas eqpoll_refl = id_bij [THEN bij_imp_eqpoll, standard, simp]

lemma eqpoll_sym: "X \<approx> Y ==> Y \<approx> X"
apply (unfold eqpoll_def)
apply (blast intro: bij_converse_bij)
done

lemma eqpoll_trans: 
    "[| X \<approx> Y;  Y \<approx> Z |] ==> X \<approx> Z"
apply (unfold eqpoll_def)
apply (blast intro: comp_bij)
done

(** Le-pollence is a partial ordering **)

lemma subset_imp_lepoll: "X<=Y ==> X \<lesssim> Y"
apply (unfold lepoll_def)
apply (rule exI)
apply (erule id_subset_inj)
done

lemmas lepoll_refl = subset_refl [THEN subset_imp_lepoll, standard, simp]

lemmas le_imp_lepoll = le_imp_subset [THEN subset_imp_lepoll, standard]

lemma eqpoll_imp_lepoll: "X \<approx> Y ==> X \<lesssim> Y"
by (unfold eqpoll_def bij_def lepoll_def, blast)

lemma lepoll_trans: "[| X \<lesssim> Y;  Y \<lesssim> Z |] ==> X \<lesssim> Z"
apply (unfold lepoll_def)
apply (blast intro: comp_inj)
done

(*Asymmetry law*)
lemma eqpollI: "[| X \<lesssim> Y;  Y \<lesssim> X |] ==> X \<approx> Y"
apply (unfold lepoll_def eqpoll_def)
apply (elim exE)
apply (rule schroeder_bernstein, assumption+)
done

lemma eqpollE:
    "[| X \<approx> Y; [| X \<lesssim> Y; Y \<lesssim> X |] ==> P |] ==> P"
by (blast intro: eqpoll_imp_lepoll eqpoll_sym) 

lemma eqpoll_iff: "X \<approx> Y <-> X \<lesssim> Y & Y \<lesssim> X"
by (blast intro: eqpollI elim!: eqpollE)

lemma lepoll_0_is_0: "A \<lesssim> 0 ==> A = 0"
apply (unfold lepoll_def inj_def)
apply (blast dest: apply_type)
done

(*0 \<lesssim> Y*)
lemmas empty_lepollI = empty_subsetI [THEN subset_imp_lepoll, standard]

lemma lepoll_0_iff: "A \<lesssim> 0 <-> A=0"
by (blast intro: lepoll_0_is_0 lepoll_refl)

lemma Un_lepoll_Un: 
    "[| A \<lesssim> B; C \<lesssim> D; B Int D = 0 |] ==> A Un C \<lesssim> B Un D"
apply (unfold lepoll_def)
apply (blast intro: inj_disjoint_Un)
done

(*A eqpoll 0 ==> A=0*)
lemmas eqpoll_0_is_0 = eqpoll_imp_lepoll [THEN lepoll_0_is_0, standard]

lemma eqpoll_0_iff: "A \<approx> 0 <-> A=0"
by (blast intro: eqpoll_0_is_0 eqpoll_refl)

lemma eqpoll_disjoint_Un: 
    "[| A \<approx> B;  C \<approx> D;  A Int C = 0;  B Int D = 0 |]   
     ==> A Un C \<approx> B Un D"
apply (unfold eqpoll_def)
apply (blast intro: bij_disjoint_Un)
done


(*** lesspoll: contributions by Krzysztof Grabczewski ***)

lemma lesspoll_not_refl: "~ (i \<prec> i)"
by (simp add: lesspoll_def) 

lemma lesspoll_irrefl [elim!]: "i \<prec> i ==> P"
by (simp add: lesspoll_def) 

lemma lesspoll_imp_lepoll: "A \<prec> B ==> A \<lesssim> B"
by (unfold lesspoll_def, blast)

lemma lepoll_well_ord: "[| A \<lesssim> B; well_ord(B,r) |] ==> EX s. well_ord(A,s)"
apply (unfold lepoll_def)
apply (blast intro: well_ord_rvimage)
done

lemma lepoll_iff_leqpoll: "A \<lesssim> B <-> A \<prec> B | A \<approx> B"
apply (unfold lesspoll_def)
apply (blast intro!: eqpollI elim!: eqpollE)
done

lemma inj_not_surj_succ: 
  "[| f : inj(A, succ(m)); f ~: surj(A, succ(m)) |] ==> EX f. f:inj(A,m)"
apply (unfold inj_def surj_def) 
apply (safe del: succE) 
apply (erule swap, rule exI) 
apply (rule_tac a = "lam z:A. if f`z=m then y else f`z" in CollectI)
txt{*the typing condition*}
 apply (best intro!: if_type [THEN lam_type] elim: apply_funtype [THEN succE])
txt{*Proving it's injective*}
apply simp
apply blast 
done

(** Variations on transitivity **)

lemma lesspoll_trans: 
      "[| X \<prec> Y; Y \<prec> Z |] ==> X \<prec> Z"
apply (unfold lesspoll_def)
apply (blast elim!: eqpollE intro: eqpollI lepoll_trans)
done

lemma lesspoll_trans1: 
      "[| X \<lesssim> Y; Y \<prec> Z |] ==> X \<prec> Z"
apply (unfold lesspoll_def)
apply (blast elim!: eqpollE intro: eqpollI lepoll_trans)
done

lemma lesspoll_trans2: 
      "[| X \<prec> Y; Y \<lesssim> Z |] ==> X \<prec> Z"
apply (unfold lesspoll_def)
apply (blast elim!: eqpollE intro: eqpollI lepoll_trans)
done


(** LEAST -- the least number operator [from HOL/Univ.ML] **)

lemma Least_equality: 
    "[| P(i);  Ord(i);  !!x. x<i ==> ~P(x) |] ==> (LEAST x. P(x)) = i"
apply (unfold Least_def) 
apply (rule the_equality, blast)
apply (elim conjE)
apply (erule Ord_linear_lt, assumption, blast+)
done

lemma LeastI: "[| P(i);  Ord(i) |] ==> P(LEAST x. P(x))"
apply (erule rev_mp)
apply (erule_tac i=i in trans_induct) 
apply (rule impI)
apply (rule classical)
apply (blast intro: Least_equality [THEN ssubst]  elim!: ltE)
done

(*Proof is almost identical to the one above!*)
lemma Least_le: "[| P(i);  Ord(i) |] ==> (LEAST x. P(x)) le i"
apply (erule rev_mp)
apply (erule_tac i=i in trans_induct) 
apply (rule impI)
apply (rule classical)
apply (subst Least_equality, assumption+)
apply (erule_tac [2] le_refl)
apply (blast elim: ltE intro: leI ltI lt_trans1)
done

(*LEAST really is the smallest*)
lemma less_LeastE: "[| P(i);  i < (LEAST x. P(x)) |] ==> Q"
apply (rule Least_le [THEN [2] lt_trans2, THEN lt_irrefl], assumption+)
apply (simp add: lt_Ord) 
done

(*Easier to apply than LeastI: conclusion has only one occurrence of P*)
lemma LeastI2:
    "[| P(i);  Ord(i);  !!j. P(j) ==> Q(j) |] ==> Q(LEAST j. P(j))"
by (blast intro: LeastI ) 

(*If there is no such P then LEAST is vacuously 0*)
lemma Least_0: 
    "[| ~ (EX i. Ord(i) & P(i)) |] ==> (LEAST x. P(x)) = 0"
apply (unfold Least_def)
apply (rule the_0, blast)
done

lemma Ord_Least: "Ord(LEAST x. P(x))"
apply (rule_tac P = "EX i. Ord(i) & P(i)" in case_split_thm)  
    (*case_tac method not available yet; needs "inductive"*)
apply safe
apply (rule Least_le [THEN ltE])
prefer 3 apply assumption+
apply (erule Least_0 [THEN ssubst])
apply (rule Ord_0)
done


(** Basic properties of cardinals **)

(*Not needed for simplification, but helpful below*)
lemma Least_cong:
     "(!!y. P(y) <-> Q(y)) ==> (LEAST x. P(x)) = (LEAST x. Q(x))"
by simp

(*Need AC to get X \<lesssim> Y ==> |X| le |Y|;  see well_ord_lepoll_imp_Card_le
  Converse also requires AC, but see well_ord_cardinal_eqE*)
lemma cardinal_cong: "X \<approx> Y ==> |X| = |Y|"
apply (unfold eqpoll_def cardinal_def)
apply (rule Least_cong)
apply (blast intro: comp_bij bij_converse_bij)
done

(*Under AC, the premise becomes trivial; one consequence is ||A|| = |A|*)
lemma well_ord_cardinal_eqpoll: 
    "well_ord(A,r) ==> |A| \<approx> A"
apply (unfold cardinal_def)
apply (rule LeastI)
apply (erule_tac [2] Ord_ordertype)
apply (erule ordermap_bij [THEN bij_converse_bij, THEN bij_imp_eqpoll])
done

(* Ord(A) ==> |A| \<approx> A *)
lemmas Ord_cardinal_eqpoll = well_ord_Memrel [THEN well_ord_cardinal_eqpoll]

lemma well_ord_cardinal_eqE:
     "[| well_ord(X,r);  well_ord(Y,s);  |X| = |Y| |] ==> X \<approx> Y"
apply (rule eqpoll_sym [THEN eqpoll_trans])
apply (erule well_ord_cardinal_eqpoll)
apply (simp (no_asm_simp) add: well_ord_cardinal_eqpoll)
done

lemma well_ord_cardinal_eqpoll_iff:
     "[| well_ord(X,r);  well_ord(Y,s) |] ==> |X| = |Y| <-> X \<approx> Y"
by (blast intro: cardinal_cong well_ord_cardinal_eqE)


(** Observations from Kunen, page 28 **)

lemma Ord_cardinal_le: "Ord(i) ==> |i| le i"
apply (unfold cardinal_def)
apply (erule eqpoll_refl [THEN Least_le])
done

lemma Card_cardinal_eq: "Card(K) ==> |K| = K"
apply (unfold Card_def)
apply (erule sym)
done

(* Could replace the  ~(j \<approx> i)  by  ~(i \<lesssim> j) *)
lemma CardI: "[| Ord(i);  !!j. j<i ==> ~(j \<approx> i) |] ==> Card(i)"
apply (unfold Card_def cardinal_def) 
apply (subst Least_equality)
apply (blast intro: eqpoll_refl )+
done

lemma Card_is_Ord: "Card(i) ==> Ord(i)"
apply (unfold Card_def cardinal_def)
apply (erule ssubst)
apply (rule Ord_Least)
done

lemma Card_cardinal_le: "Card(K) ==> K le |K|"
apply (simp (no_asm_simp) add: Card_is_Ord Card_cardinal_eq)
done

lemma Ord_cardinal [simp,intro!]: "Ord(|A|)"
apply (unfold cardinal_def)
apply (rule Ord_Least)
done

(*The cardinals are the initial ordinals*)
lemma Card_iff_initial: "Card(K) <-> Ord(K) & (ALL j. j<K --> ~ j \<approx> K)"
apply (safe intro!: CardI Card_is_Ord)
 prefer 2 apply blast
apply (unfold Card_def cardinal_def)
apply (rule less_LeastE)
apply (erule_tac [2] subst, assumption+)
done

lemma lt_Card_imp_lesspoll: "[| Card(a); i<a |] ==> i \<prec> a"
apply (unfold lesspoll_def)
apply (drule Card_iff_initial [THEN iffD1])
apply (blast intro!: leI [THEN le_imp_lepoll])
done

lemma Card_0: "Card(0)"
apply (rule Ord_0 [THEN CardI])
apply (blast elim!: ltE)
done

lemma Card_Un: "[| Card(K);  Card(L) |] ==> Card(K Un L)"
apply (rule Ord_linear_le [of K L])
apply (simp_all add: subset_Un_iff [THEN iffD1]  Card_is_Ord le_imp_subset
                     subset_Un_iff2 [THEN iffD1])
done

(*Infinite unions of cardinals?  See Devlin, Lemma 6.7, page 98*)

lemma Card_cardinal: "Card(|A|)"
apply (unfold cardinal_def)
apply (rule_tac P =  "EX i. Ord (i) & i \<approx> A" in case_split_thm)
 txt{*degenerate case*}
 prefer 2 apply (erule Least_0 [THEN ssubst], rule Card_0)
txt{*real case: A is isomorphic to some ordinal*}
apply (rule Ord_Least [THEN CardI], safe)
apply (rule less_LeastE)
prefer 2 apply assumption
apply (erule eqpoll_trans)
apply (best intro: LeastI ) 
done

(*Kunen's Lemma 10.5*)
lemma cardinal_eq_lemma: "[| |i| le j;  j le i |] ==> |j| = |i|"
apply (rule eqpollI [THEN cardinal_cong])
apply (erule le_imp_lepoll)
apply (rule lepoll_trans)
apply (erule_tac [2] le_imp_lepoll)
apply (rule eqpoll_sym [THEN eqpoll_imp_lepoll])
apply (rule Ord_cardinal_eqpoll)
apply (elim ltE Ord_succD)
done

lemma cardinal_mono: "i le j ==> |i| le |j|"
apply (rule_tac i = "|i|" and j = "|j|" in Ord_linear_le)
apply (safe intro!: Ord_cardinal le_eqI)
apply (rule cardinal_eq_lemma)
prefer 2 apply assumption
apply (erule le_trans)
apply (erule ltE)
apply (erule Ord_cardinal_le)
done

(*Since we have |succ(nat)| le |nat|, the converse of cardinal_mono fails!*)
lemma cardinal_lt_imp_lt: "[| |i| < |j|;  Ord(i);  Ord(j) |] ==> i < j"
apply (rule Ord_linear2 [of i j], assumption+)
apply (erule lt_trans2 [THEN lt_irrefl])
apply (erule cardinal_mono)
done

lemma Card_lt_imp_lt: "[| |i| < K;  Ord(i);  Card(K) |] ==> i < K"
apply (simp (no_asm_simp) add: cardinal_lt_imp_lt Card_is_Ord Card_cardinal_eq)
done

lemma Card_lt_iff: "[| Ord(i);  Card(K) |] ==> (|i| < K) <-> (i < K)"
by (blast intro: Card_lt_imp_lt Ord_cardinal_le [THEN lt_trans1])

lemma Card_le_iff: "[| Ord(i);  Card(K) |] ==> (K le |i|) <-> (K le i)"
by (simp add: Card_lt_iff Card_is_Ord Ord_cardinal not_lt_iff_le [THEN iff_sym])

(*Can use AC or finiteness to discharge first premise*)
lemma well_ord_lepoll_imp_Card_le:
     "[| well_ord(B,r);  A \<lesssim> B |] ==> |A| le |B|"
apply (rule_tac i = "|A|" and j = "|B|" in Ord_linear_le)
apply (safe intro!: Ord_cardinal le_eqI)
apply (rule eqpollI [THEN cardinal_cong], assumption)
apply (rule lepoll_trans)
apply (rule well_ord_cardinal_eqpoll [THEN eqpoll_sym, THEN eqpoll_imp_lepoll], assumption)
apply (erule le_imp_lepoll [THEN lepoll_trans])
apply (rule eqpoll_imp_lepoll)
apply (unfold lepoll_def)
apply (erule exE)
apply (rule well_ord_cardinal_eqpoll)
apply (erule well_ord_rvimage, assumption)
done


lemma lepoll_cardinal_le: "[| A \<lesssim> i; Ord(i) |] ==> |A| le i"
apply (rule le_trans)
apply (erule well_ord_Memrel [THEN well_ord_lepoll_imp_Card_le], assumption)
apply (erule Ord_cardinal_le)
done

lemma lepoll_Ord_imp_eqpoll: "[| A \<lesssim> i; Ord(i) |] ==> |A| \<approx> A"
by (blast intro: lepoll_cardinal_le well_ord_Memrel well_ord_cardinal_eqpoll dest!: lepoll_well_ord)

lemma lesspoll_imp_eqpoll: 
     "[| A \<prec> i; Ord(i) |] ==> |A| \<approx> A"
apply (unfold lesspoll_def)
apply (blast intro: lepoll_Ord_imp_eqpoll)
done


(*** The finite cardinals ***)

lemma cons_lepoll_consD: 
 "[| cons(u,A) \<lesssim> cons(v,B);  u~:A;  v~:B |] ==> A \<lesssim> B"
apply (unfold lepoll_def inj_def, safe)
apply (rule_tac x = "lam x:A. if f`x=v then f`u else f`x" in exI)
apply (rule CollectI)
(*Proving it's in the function space A->B*)
apply (rule if_type [THEN lam_type])
apply (blast dest: apply_funtype)
apply (blast elim!: mem_irrefl dest: apply_funtype)
(*Proving it's injective*)
apply (simp (no_asm_simp))
apply blast
done

lemma cons_eqpoll_consD: "[| cons(u,A) \<approx> cons(v,B);  u~:A;  v~:B |] ==> A \<approx> B"
apply (simp add: eqpoll_iff)
apply (blast intro: cons_lepoll_consD)
done

(*Lemma suggested by Mike Fourman*)
lemma succ_lepoll_succD: "succ(m) \<lesssim> succ(n) ==> m \<lesssim> n"
apply (unfold succ_def)
apply (erule cons_lepoll_consD)
apply (rule mem_not_refl)+
done

lemma nat_lepoll_imp_le [rule_format]:
     "m:nat ==> ALL n: nat. m \<lesssim> n --> m le n"
apply (induct_tac m)
apply (blast intro!: nat_0_le)
apply (rule ballI)
apply (erule_tac n = "n" in natE)
apply (simp (no_asm_simp) add: lepoll_def inj_def)
apply (blast intro!: succ_leI dest!: succ_lepoll_succD)
done

lemma nat_eqpoll_iff: "[| m:nat; n: nat |] ==> m \<approx> n <-> m = n"
apply (rule iffI)
apply (blast intro: nat_lepoll_imp_le le_anti_sym elim!: eqpollE)
apply (simp add: eqpoll_refl)
done

(*The object of all this work: every natural number is a (finite) cardinal*)
lemma nat_into_Card: 
    "n: nat ==> Card(n)"
apply (unfold Card_def cardinal_def)
apply (subst Least_equality)
apply (rule eqpoll_refl)
apply (erule nat_into_Ord) 
apply (simp (no_asm_simp) add: lt_nat_in_nat [THEN nat_eqpoll_iff])
apply (blast elim!: lt_irrefl)+
done

lemmas cardinal_0 = nat_0I [THEN nat_into_Card, THEN Card_cardinal_eq, iff]
lemmas cardinal_1 = nat_1I [THEN nat_into_Card, THEN Card_cardinal_eq, iff]


(*Part of Kunen's Lemma 10.6*)
lemma succ_lepoll_natE: "[| succ(n) \<lesssim> n;  n:nat |] ==> P"
by (rule nat_lepoll_imp_le [THEN lt_irrefl], auto)

lemma n_lesspoll_nat: "n \<in> nat ==> n \<prec> nat"
apply (unfold lesspoll_def)
apply (fast elim!: Ord_nat [THEN [2] ltI [THEN leI, THEN le_imp_lepoll]]
                   eqpoll_sym [THEN eqpoll_imp_lepoll] 
    intro: Ord_nat [THEN [2] nat_succI [THEN ltI], THEN leI, 
                 THEN le_imp_lepoll, THEN lepoll_trans, THEN succ_lepoll_natE])
done

lemma nat_lepoll_imp_ex_eqpoll_n: 
     "[| n \<in> nat;  nat \<lesssim> X |] ==> \<exists>Y. Y \<subseteq> X & n \<approx> Y"
apply (unfold lepoll_def eqpoll_def)
apply (fast del: subsetI subsetCE
            intro!: subset_SIs
            dest!: Ord_nat [THEN [2] OrdmemD, THEN [2] restrict_inj]
            elim!: restrict_bij 
                   inj_is_fun [THEN fun_is_rel, THEN image_subset])
done


(** lepoll, \<prec> and natural numbers **)

lemma lepoll_imp_lesspoll_succ: 
     "[| A \<lesssim> m; m:nat |] ==> A \<prec> succ(m)"
apply (unfold lesspoll_def)
apply (rule conjI)
apply (blast intro: subset_imp_lepoll [THEN [2] lepoll_trans])
apply (rule notI)
apply (drule eqpoll_sym [THEN eqpoll_imp_lepoll])
apply (drule lepoll_trans, assumption)
apply (erule succ_lepoll_natE, assumption)
done

lemma lesspoll_succ_imp_lepoll: 
     "[| A \<prec> succ(m); m:nat |] ==> A \<lesssim> m"
apply (unfold lesspoll_def lepoll_def eqpoll_def bij_def, clarify)
apply (blast intro!: inj_not_surj_succ)
done

lemma lesspoll_succ_iff: "m:nat ==> A \<prec> succ(m) <-> A \<lesssim> m"
by (blast intro!: lepoll_imp_lesspoll_succ lesspoll_succ_imp_lepoll)

lemma lepoll_succ_disj: "[| A \<lesssim> succ(m);  m:nat |] ==> A \<lesssim> m | A \<approx> succ(m)"
apply (rule disjCI)
apply (rule lesspoll_succ_imp_lepoll)
prefer 2 apply assumption
apply (simp (no_asm_simp) add: lesspoll_def)
done

lemma lesspoll_cardinal_lt: "[| A \<prec> i; Ord(i) |] ==> |A| < i"
apply (unfold lesspoll_def, clarify)
apply (frule lepoll_cardinal_le, assumption)
apply (blast intro: well_ord_Memrel well_ord_cardinal_eqpoll [THEN eqpoll_sym]
             dest: lepoll_well_ord  elim!: leE)
done


(*** The first infinite cardinal: Omega, or nat ***)

(*This implies Kunen's Lemma 10.6*)
lemma lt_not_lepoll: "[| n<i;  n:nat |] ==> ~ i \<lesssim> n"
apply (rule notI)
apply (rule succ_lepoll_natE [of n])
apply (rule lepoll_trans [of _ i])
apply (erule ltE)
apply (rule Ord_succ_subsetI [THEN subset_imp_lepoll], assumption+)
done

lemma Ord_nat_eqpoll_iff: "[| Ord(i);  n:nat |] ==> i \<approx> n <-> i=n"
apply (rule iffI)
 prefer 2 apply (simp add: eqpoll_refl)
apply (rule Ord_linear_lt [of i n])
apply (simp_all add: nat_into_Ord)
apply (erule lt_nat_in_nat [THEN nat_eqpoll_iff, THEN iffD1], assumption+)
apply (rule lt_not_lepoll [THEN notE], assumption+)
apply (erule eqpoll_imp_lepoll)
done

lemma Card_nat: "Card(nat)"
apply (unfold Card_def cardinal_def)
apply (subst Least_equality)
apply (rule eqpoll_refl) 
apply (rule Ord_nat) 
apply (erule ltE)
apply (simp_all add: eqpoll_iff lt_not_lepoll ltI)
done

(*Allows showing that |i| is a limit cardinal*)
lemma nat_le_cardinal: "nat le i ==> nat le |i|"
apply (rule Card_nat [THEN Card_cardinal_eq, THEN subst])
apply (erule cardinal_mono)
done


(*** Towards Cardinal Arithmetic ***)
(** Congruence laws for successor, cardinal addition and multiplication **)

(*Congruence law for  cons  under equipollence*)
lemma cons_lepoll_cong: 
    "[| A \<lesssim> B;  b ~: B |] ==> cons(a,A) \<lesssim> cons(b,B)"
apply (unfold lepoll_def, safe)
apply (rule_tac x = "lam y: cons (a,A) . if y=a then b else f`y" in exI)
apply (rule_tac d = "%z. if z:B then converse (f) `z else a" in lam_injective)
apply (safe elim!: consE') 
   apply simp_all
apply (blast intro: inj_is_fun [THEN apply_type])+ 
done

lemma cons_eqpoll_cong:
     "[| A \<approx> B;  a ~: A;  b ~: B |] ==> cons(a,A) \<approx> cons(b,B)"
by (simp add: eqpoll_iff cons_lepoll_cong)

lemma cons_lepoll_cons_iff:
     "[| a ~: A;  b ~: B |] ==> cons(a,A) \<lesssim> cons(b,B)  <->  A \<lesssim> B"
by (blast intro: cons_lepoll_cong cons_lepoll_consD)

lemma cons_eqpoll_cons_iff:
     "[| a ~: A;  b ~: B |] ==> cons(a,A) \<approx> cons(b,B)  <->  A \<approx> B"
by (blast intro: cons_eqpoll_cong cons_eqpoll_consD)

lemma singleton_eqpoll_1: "{a} \<approx> 1"
apply (unfold succ_def)
apply (blast intro!: eqpoll_refl [THEN cons_eqpoll_cong])
done

lemma cardinal_singleton: "|{a}| = 1"
apply (rule singleton_eqpoll_1 [THEN cardinal_cong, THEN trans])
apply (simp (no_asm) add: nat_into_Card [THEN Card_cardinal_eq])
done

lemma not_0_is_lepoll_1: "A ~= 0 ==> 1 \<lesssim> A"
apply (erule not_emptyE)
apply (rule_tac a = "cons (x, A-{x}) " in subst)
apply (rule_tac [2] a = "cons(0,0)" and P= "%y. y \<lesssim> cons (x, A-{x})" in subst)
prefer 3 apply (blast intro: cons_lepoll_cong subset_imp_lepoll, auto)
done

(*Congruence law for  succ  under equipollence*)
lemma succ_eqpoll_cong: "A \<approx> B ==> succ(A) \<approx> succ(B)"
apply (unfold succ_def)
apply (simp add: cons_eqpoll_cong mem_not_refl)
done

(*Congruence law for + under equipollence*)
lemma sum_eqpoll_cong: "[| A \<approx> C;  B \<approx> D |] ==> A+B \<approx> C+D"
apply (unfold eqpoll_def)
apply (blast intro!: sum_bij)
done

(*Congruence law for * under equipollence*)
lemma prod_eqpoll_cong: 
    "[| A \<approx> C;  B \<approx> D |] ==> A*B \<approx> C*D"
apply (unfold eqpoll_def)
apply (blast intro!: prod_bij)
done

lemma inj_disjoint_eqpoll: 
    "[| f: inj(A,B);  A Int B = 0 |] ==> A Un (B - range(f)) \<approx> B"
apply (unfold eqpoll_def)
apply (rule exI)
apply (rule_tac c = "%x. if x:A then f`x else x" 
            and d = "%y. if y: range (f) then converse (f) `y else y" 
       in lam_bijective)
apply (blast intro!: if_type inj_is_fun [THEN apply_type])
apply (simp (no_asm_simp) add: inj_converse_fun [THEN apply_funtype])
apply (safe elim!: UnE') 
   apply (simp_all add: inj_is_fun [THEN apply_rangeI])
apply (blast intro: inj_converse_fun [THEN apply_type])+ 
done


(*** Lemmas by Krzysztof Grabczewski.  New proofs using cons_lepoll_cons.
     Could easily generalise from succ to cons. ***)

(*If A has at most n+1 elements and a:A then A-{a} has at most n.*)
lemma Diff_sing_lepoll: 
      "[| a:A;  A \<lesssim> succ(n) |] ==> A - {a} \<lesssim> n"
apply (unfold succ_def)
apply (rule cons_lepoll_consD)
apply (rule_tac [3] mem_not_refl)
apply (erule cons_Diff [THEN ssubst], safe)
done

(*If A has at least n+1 elements then A-{a} has at least n.*)
lemma lepoll_Diff_sing: 
      "[| succ(n) \<lesssim> A |] ==> n \<lesssim> A - {a}"
apply (unfold succ_def)
apply (rule cons_lepoll_consD)
apply (rule_tac [2] mem_not_refl)
prefer 2 apply blast
apply (blast intro: subset_imp_lepoll [THEN [2] lepoll_trans])
done

lemma Diff_sing_eqpoll: "[| a:A; A \<approx> succ(n) |] ==> A - {a} \<approx> n"
by (blast intro!: eqpollI 
          elim!: eqpollE 
          intro: Diff_sing_lepoll lepoll_Diff_sing)

lemma lepoll_1_is_sing: "[| A \<lesssim> 1; a:A |] ==> A = {a}"
apply (frule Diff_sing_lepoll, assumption)
apply (drule lepoll_0_is_0)
apply (blast elim: equalityE)
done

lemma Un_lepoll_sum: "A Un B \<lesssim> A+B"
apply (unfold lepoll_def)
apply (rule_tac x = "lam x: A Un B. if x:A then Inl (x) else Inr (x) " in exI)
apply (rule_tac d = "%z. snd (z) " in lam_injective)
apply force 
apply (simp add: Inl_def Inr_def)
done

lemma well_ord_Un:
     "[| well_ord(X,R); well_ord(Y,S) |] ==> EX T. well_ord(X Un Y, T)"
by (erule well_ord_radd [THEN Un_lepoll_sum [THEN lepoll_well_ord]], 
    assumption)

(*Krzysztof Grabczewski*)
lemma disj_Un_eqpoll_sum: "A Int B = 0 ==> A Un B \<approx> A + B"
apply (unfold eqpoll_def)
apply (rule_tac x = "lam a:A Un B. if a:A then Inl (a) else Inr (a) " in exI)
apply (rule_tac d = "%z. case (%x. x, %x. x, z) " in lam_bijective)
apply auto
done


subsection {*Finite and infinite sets*}

lemma Finite_0 [simp]: "Finite(0)"
apply (unfold Finite_def)
apply (blast intro!: eqpoll_refl nat_0I)
done

lemma lepoll_nat_imp_Finite: "[| A \<lesssim> n;  n:nat |] ==> Finite(A)"
apply (unfold Finite_def)
apply (erule rev_mp)
apply (erule nat_induct)
apply (blast dest!: lepoll_0_is_0 intro!: eqpoll_refl nat_0I)
apply (blast dest!: lepoll_succ_disj)
done

lemma lesspoll_nat_is_Finite: 
     "A \<prec> nat ==> Finite(A)"
apply (unfold Finite_def)
apply (blast dest: ltD lesspoll_cardinal_lt 
                   lesspoll_imp_eqpoll [THEN eqpoll_sym])
done

lemma lepoll_Finite: 
     "[| Y \<lesssim> X;  Finite(X) |] ==> Finite(Y)"
apply (unfold Finite_def)
apply (blast elim!: eqpollE
             intro: lepoll_trans [THEN lepoll_nat_imp_Finite
                                       [unfolded Finite_def]])
done

lemmas subset_Finite = subset_imp_lepoll [THEN lepoll_Finite, standard]

lemmas Finite_Diff = Diff_subset [THEN subset_Finite, standard]

lemma Finite_cons: "Finite(x) ==> Finite(cons(y,x))"
apply (unfold Finite_def)
apply (rule_tac P =  "y:x" in case_split_thm)
apply (simp add: cons_absorb)
apply (erule bexE)
apply (rule bexI)
apply (erule_tac [2] nat_succI)
apply (simp (no_asm_simp) add: succ_def cons_eqpoll_cong mem_not_refl)
done

lemma Finite_succ: "Finite(x) ==> Finite(succ(x))"
apply (unfold succ_def)
apply (erule Finite_cons)
done

lemma Finite_cons_iff [iff]: "Finite(cons(y,x)) <-> Finite(x)"
by (blast intro: Finite_cons subset_Finite)

lemma Finite_succ_iff [iff]: "Finite(succ(x)) <-> Finite(x)"
by (simp add: succ_def)

lemma nat_le_infinite_Ord: 
      "[| Ord(i);  ~ Finite(i) |] ==> nat le i"
apply (unfold Finite_def)
apply (erule Ord_nat [THEN [2] Ord_linear2])
prefer 2 apply assumption
apply (blast intro!: eqpoll_refl elim!: ltE)
done

lemma Finite_imp_well_ord: 
    "Finite(A) ==> EX r. well_ord(A,r)"
apply (unfold Finite_def eqpoll_def)
apply (blast intro: well_ord_rvimage bij_is_inj well_ord_Memrel nat_into_Ord)
done

lemma succ_lepoll_imp_not_empty: "succ(x) \<lesssim> y ==> y \<noteq> 0"
by (fast dest!: lepoll_0_is_0)

lemma eqpoll_succ_imp_not_empty: "x \<approx> succ(n) ==> x \<noteq> 0"
by (fast elim!: eqpoll_sym [THEN eqpoll_0_is_0, THEN succ_neq_0])

lemma Finite_Fin_lemma [rule_format]:
     "n \<in> nat ==> \<forall>A. (A\<approx>n & A \<subseteq> X) --> A \<in> Fin(X)"
apply (induct_tac n)
apply (rule allI)
apply (fast intro!: Fin.emptyI dest!: eqpoll_imp_lepoll [THEN lepoll_0_is_0])
apply (rule allI)
apply (rule impI)
apply (erule conjE)
apply (rule eqpoll_succ_imp_not_empty [THEN not_emptyE], assumption)
apply (frule Diff_sing_eqpoll, assumption)
apply (erule allE)
apply (erule impE, fast)
apply (drule subsetD, assumption)
apply (drule Fin.consI, assumption)
apply (simp add: cons_Diff)
done

lemma Finite_Fin: "[| Finite(A); A \<subseteq> X |] ==> A \<in> Fin(X)"
by (unfold Finite_def, blast intro: Finite_Fin_lemma) 

lemma eqpoll_imp_Finite_iff: "A \<approx> B ==> Finite(A) <-> Finite(B)"
apply (unfold Finite_def) 
apply (blast intro: eqpoll_trans eqpoll_sym) 
done

lemma Fin_lemma [rule_format]: "n: nat ==> ALL A. A \<approx> n --> A : Fin(A)"
apply (induct_tac n)
apply (simp add: eqpoll_0_iff, clarify)
apply (subgoal_tac "EX u. u:A")
apply (erule exE)
apply (rule Diff_sing_eqpoll [THEN revcut_rl])
prefer 2 apply assumption
apply assumption
apply (rule_tac b = "A" in cons_Diff [THEN subst], assumption)
apply (rule Fin.consI, blast)
apply (blast intro: subset_consI [THEN Fin_mono, THEN subsetD])
(*Now for the lemma assumed above*)
apply (unfold eqpoll_def)
apply (blast intro: bij_converse_bij [THEN bij_is_fun, THEN apply_type])
done

lemma Finite_into_Fin: "Finite(A) ==> A : Fin(A)"
apply (unfold Finite_def)
apply (blast intro: Fin_lemma)
done

lemma Fin_into_Finite: "A : Fin(U) ==> Finite(A)"
by (fast intro!: Finite_0 Finite_cons elim: Fin_induct)

lemma Finite_Fin_iff: "Finite(A) <-> A : Fin(A)"
by (blast intro: Finite_into_Fin Fin_into_Finite)

lemma Finite_Un: "[| Finite(A); Finite(B) |] ==> Finite(A Un B)"
by (blast intro!: Fin_into_Finite Fin_UnI 
          dest!: Finite_into_Fin
          intro: Un_upper1 [THEN Fin_mono, THEN subsetD] 
                 Un_upper2 [THEN Fin_mono, THEN subsetD])

lemma Finite_Union: "[| ALL y:X. Finite(y);  Finite(X) |] ==> Finite(Union(X))"
apply (simp add: Finite_Fin_iff)
apply (rule Fin_UnionI)
apply (erule Fin_induct, simp)
apply (blast intro: Fin.consI Fin_mono [THEN [2] rev_subsetD])
done

(* Induction principle for Finite(A), by Sidi Ehmety *)
lemma Finite_induct:
"[| Finite(A); P(0);
    !! x B.   [| Finite(B); x ~: B; P(B) |] ==> P(cons(x, B)) |]
 ==> P(A)"
apply (erule Finite_into_Fin [THEN Fin_induct]) 
apply (blast intro: Fin_into_Finite)+
done

(*Sidi Ehmety.  The contrapositive says ~Finite(A) ==> ~Finite(A-{a}) *)
lemma Diff_sing_Finite: "Finite(A - {a}) ==> Finite(A)"
apply (unfold Finite_def)
apply (case_tac "a:A")
apply (subgoal_tac [2] "A-{a}=A", auto)
apply (rule_tac x = "succ (n) " in bexI)
apply (subgoal_tac "cons (a, A - {a}) = A & cons (n, n) = succ (n) ")
apply (drule_tac a = "a" and b = "n" in cons_eqpoll_cong)
apply (auto dest: mem_irrefl)
done

(*Sidi Ehmety.  And the contrapositive of this says
   [| ~Finite(A); Finite(B) |] ==> ~Finite(A-B) *)
lemma Diff_Finite [rule_format]: "Finite(B) ==> Finite(A-B) --> Finite(A)"
apply (erule Finite_induct, auto)
apply (case_tac "x:A")
 apply (subgoal_tac [2] "A-cons (x, B) = A - B")
apply (subgoal_tac "A - cons (x, B) = (A - B) - {x}")
apply (rotate_tac -1, simp)
apply (drule Diff_sing_Finite, auto)
done

lemma Finite_RepFun: "Finite(A) ==> Finite(RepFun(A,f))"
by (erule Finite_induct, simp_all)

lemma Finite_RepFun_iff_lemma [rule_format]:
     "[|Finite(x); !!x y. f(x)=f(y) ==> x=y|] 
      ==> \<forall>A. x = RepFun(A,f) --> Finite(A)" 
apply (erule Finite_induct)
 apply clarify 
 apply (case_tac "A=0", simp)
 apply (blast del: allE, clarify) 
apply (subgoal_tac "\<exists>z\<in>A. x = f(z)") 
 prefer 2 apply (blast del: allE elim: equalityE, clarify) 
apply (subgoal_tac "B = {f(u) . u \<in> A - {z}}")
 apply (blast intro: Diff_sing_Finite) 
apply (thin_tac "\<forall>A. ?P(A) --> Finite(A)") 
apply (rule equalityI) 
 apply (blast intro: elim: equalityE) 
apply (blast intro: elim: equalityCE) 
done

text{*I don't know why, but if the premise is expressed using meta-connectives
then  the simplifier cannot prove it automatically in conditional rewriting.*}
lemma Finite_RepFun_iff:
     "(\<forall>x y. f(x)=f(y) --> x=y) ==> Finite(RepFun(A,f)) <-> Finite(A)"
by (blast intro: Finite_RepFun Finite_RepFun_iff_lemma [of _ f]) 

lemma Finite_Pow: "Finite(A) ==> Finite(Pow(A))"
apply (erule Finite_induct) 
apply (simp_all add: Pow_insert Finite_Un Finite_RepFun) 
done

lemma Finite_Pow_imp_Finite: "Finite(Pow(A)) ==> Finite(A)"
apply (subgoal_tac "Finite({{x} . x \<in> A})")
 apply (simp add: Finite_RepFun_iff ) 
apply (blast intro: subset_Finite) 
done

lemma Finite_Pow_iff [iff]: "Finite(Pow(A)) <-> Finite(A)"
by (blast intro: Finite_Pow Finite_Pow_imp_Finite)



(*Krzysztof Grabczewski's proof that the converse of a finite, well-ordered
  set is well-ordered.  Proofs simplified by lcp. *)

lemma nat_wf_on_converse_Memrel: "n:nat ==> wf[n](converse(Memrel(n)))"
apply (erule nat_induct)
apply (blast intro: wf_onI)
apply (rule wf_onI)
apply (simp add: wf_on_def wf_def)
apply (rule_tac P =  "x:Z" in case_split_thm)
 txt{*x:Z case*}
 apply (drule_tac x = x in bspec, assumption)
 apply (blast elim: mem_irrefl mem_asym)
txt{*other case*} 
apply (drule_tac x = "Z" in spec, blast) 
done

lemma nat_well_ord_converse_Memrel: "n:nat ==> well_ord(n,converse(Memrel(n)))"
apply (frule Ord_nat [THEN Ord_in_Ord, THEN well_ord_Memrel])
apply (unfold well_ord_def)
apply (blast intro!: tot_ord_converse nat_wf_on_converse_Memrel)
done

lemma well_ord_converse:
     "[|well_ord(A,r);      
        well_ord(ordertype(A,r), converse(Memrel(ordertype(A, r)))) |]
      ==> well_ord(A,converse(r))"
apply (rule well_ord_Int_iff [THEN iffD1])
apply (frule ordermap_bij [THEN bij_is_inj, THEN well_ord_rvimage], assumption)
apply (simp add: rvimage_converse converse_Int converse_prod
                 ordertype_ord_iso [THEN ord_iso_rvimage_eq])
done

lemma ordertype_eq_n:
     "[| well_ord(A,r);  A \<approx> n;  n:nat |] ==> ordertype(A,r)=n"
apply (rule Ord_ordertype [THEN Ord_nat_eqpoll_iff, THEN iffD1], assumption+)
apply (rule eqpoll_trans)
 prefer 2 apply assumption
apply (unfold eqpoll_def)
apply (blast intro!: ordermap_bij [THEN bij_converse_bij])
done

lemma Finite_well_ord_converse: 
    "[| Finite(A);  well_ord(A,r) |] ==> well_ord(A,converse(r))"
apply (unfold Finite_def)
apply (rule well_ord_converse, assumption)
apply (blast dest: ordertype_eq_n intro!: nat_well_ord_converse_Memrel)
done

lemma nat_into_Finite: "n:nat ==> Finite(n)"
apply (unfold Finite_def)
apply (fast intro!: eqpoll_refl)
done

ML
{*
val Least_def = thm "Least_def";
val eqpoll_def = thm "eqpoll_def";
val lepoll_def = thm "lepoll_def";
val lesspoll_def = thm "lesspoll_def";
val cardinal_def = thm "cardinal_def";
val Finite_def = thm "Finite_def";
val Card_def = thm "Card_def";
val eq_imp_not_mem = thm "eq_imp_not_mem";
val decomp_bnd_mono = thm "decomp_bnd_mono";
val Banach_last_equation = thm "Banach_last_equation";
val decomposition = thm "decomposition";
val schroeder_bernstein = thm "schroeder_bernstein";
val bij_imp_eqpoll = thm "bij_imp_eqpoll";
val eqpoll_refl = thm "eqpoll_refl";
val eqpoll_sym = thm "eqpoll_sym";
val eqpoll_trans = thm "eqpoll_trans";
val subset_imp_lepoll = thm "subset_imp_lepoll";
val lepoll_refl = thm "lepoll_refl";
val le_imp_lepoll = thm "le_imp_lepoll";
val eqpoll_imp_lepoll = thm "eqpoll_imp_lepoll";
val lepoll_trans = thm "lepoll_trans";
val eqpollI = thm "eqpollI";
val eqpollE = thm "eqpollE";
val eqpoll_iff = thm "eqpoll_iff";
val lepoll_0_is_0 = thm "lepoll_0_is_0";
val empty_lepollI = thm "empty_lepollI";
val lepoll_0_iff = thm "lepoll_0_iff";
val Un_lepoll_Un = thm "Un_lepoll_Un";
val eqpoll_0_is_0 = thm "eqpoll_0_is_0";
val eqpoll_0_iff = thm "eqpoll_0_iff";
val eqpoll_disjoint_Un = thm "eqpoll_disjoint_Un";
val lesspoll_not_refl = thm "lesspoll_not_refl";
val lesspoll_irrefl = thm "lesspoll_irrefl";
val lesspoll_imp_lepoll = thm "lesspoll_imp_lepoll";
val lepoll_well_ord = thm "lepoll_well_ord";
val lepoll_iff_leqpoll = thm "lepoll_iff_leqpoll";
val inj_not_surj_succ = thm "inj_not_surj_succ";
val lesspoll_trans = thm "lesspoll_trans";
val lesspoll_trans1 = thm "lesspoll_trans1";
val lesspoll_trans2 = thm "lesspoll_trans2";
val Least_equality = thm "Least_equality";
val LeastI = thm "LeastI";
val Least_le = thm "Least_le";
val less_LeastE = thm "less_LeastE";
val LeastI2 = thm "LeastI2";
val Least_0 = thm "Least_0";
val Ord_Least = thm "Ord_Least";
val Least_cong = thm "Least_cong";
val cardinal_cong = thm "cardinal_cong";
val well_ord_cardinal_eqpoll = thm "well_ord_cardinal_eqpoll";
val Ord_cardinal_eqpoll = thm "Ord_cardinal_eqpoll";
val well_ord_cardinal_eqE = thm "well_ord_cardinal_eqE";
val well_ord_cardinal_eqpoll_iff = thm "well_ord_cardinal_eqpoll_iff";
val Ord_cardinal_le = thm "Ord_cardinal_le";
val Card_cardinal_eq = thm "Card_cardinal_eq";
val CardI = thm "CardI";
val Card_is_Ord = thm "Card_is_Ord";
val Card_cardinal_le = thm "Card_cardinal_le";
val Ord_cardinal = thm "Ord_cardinal";
val Card_iff_initial = thm "Card_iff_initial";
val lt_Card_imp_lesspoll = thm "lt_Card_imp_lesspoll";
val Card_0 = thm "Card_0";
val Card_Un = thm "Card_Un";
val Card_cardinal = thm "Card_cardinal";
val cardinal_mono = thm "cardinal_mono";
val cardinal_lt_imp_lt = thm "cardinal_lt_imp_lt";
val Card_lt_imp_lt = thm "Card_lt_imp_lt";
val Card_lt_iff = thm "Card_lt_iff";
val Card_le_iff = thm "Card_le_iff";
val well_ord_lepoll_imp_Card_le = thm "well_ord_lepoll_imp_Card_le";
val lepoll_cardinal_le = thm "lepoll_cardinal_le";
val lepoll_Ord_imp_eqpoll = thm "lepoll_Ord_imp_eqpoll";
val lesspoll_imp_eqpoll = thm "lesspoll_imp_eqpoll";
val cons_lepoll_consD = thm "cons_lepoll_consD";
val cons_eqpoll_consD = thm "cons_eqpoll_consD";
val succ_lepoll_succD = thm "succ_lepoll_succD";
val nat_lepoll_imp_le = thm "nat_lepoll_imp_le";
val nat_eqpoll_iff = thm "nat_eqpoll_iff";
val nat_into_Card = thm "nat_into_Card";
val cardinal_0 = thm "cardinal_0";
val cardinal_1 = thm "cardinal_1";
val succ_lepoll_natE = thm "succ_lepoll_natE";
val n_lesspoll_nat = thm "n_lesspoll_nat";
val nat_lepoll_imp_ex_eqpoll_n = thm "nat_lepoll_imp_ex_eqpoll_n";
val lepoll_imp_lesspoll_succ = thm "lepoll_imp_lesspoll_succ";
val lesspoll_succ_imp_lepoll = thm "lesspoll_succ_imp_lepoll";
val lesspoll_succ_iff = thm "lesspoll_succ_iff";
val lepoll_succ_disj = thm "lepoll_succ_disj";
val lesspoll_cardinal_lt = thm "lesspoll_cardinal_lt";
val lt_not_lepoll = thm "lt_not_lepoll";
val Ord_nat_eqpoll_iff = thm "Ord_nat_eqpoll_iff";
val Card_nat = thm "Card_nat";
val nat_le_cardinal = thm "nat_le_cardinal";
val cons_lepoll_cong = thm "cons_lepoll_cong";
val cons_eqpoll_cong = thm "cons_eqpoll_cong";
val cons_lepoll_cons_iff = thm "cons_lepoll_cons_iff";
val cons_eqpoll_cons_iff = thm "cons_eqpoll_cons_iff";
val singleton_eqpoll_1 = thm "singleton_eqpoll_1";
val cardinal_singleton = thm "cardinal_singleton";
val not_0_is_lepoll_1 = thm "not_0_is_lepoll_1";
val succ_eqpoll_cong = thm "succ_eqpoll_cong";
val sum_eqpoll_cong = thm "sum_eqpoll_cong";
val prod_eqpoll_cong = thm "prod_eqpoll_cong";
val inj_disjoint_eqpoll = thm "inj_disjoint_eqpoll";
val Diff_sing_lepoll = thm "Diff_sing_lepoll";
val lepoll_Diff_sing = thm "lepoll_Diff_sing";
val Diff_sing_eqpoll = thm "Diff_sing_eqpoll";
val lepoll_1_is_sing = thm "lepoll_1_is_sing";
val Un_lepoll_sum = thm "Un_lepoll_sum";
val well_ord_Un = thm "well_ord_Un";
val disj_Un_eqpoll_sum = thm "disj_Un_eqpoll_sum";
val Finite_0 = thm "Finite_0";
val lepoll_nat_imp_Finite = thm "lepoll_nat_imp_Finite";
val lesspoll_nat_is_Finite = thm "lesspoll_nat_is_Finite";
val lepoll_Finite = thm "lepoll_Finite";
val subset_Finite = thm "subset_Finite";
val Finite_Diff = thm "Finite_Diff";
val Finite_cons = thm "Finite_cons";
val Finite_succ = thm "Finite_succ";
val nat_le_infinite_Ord = thm "nat_le_infinite_Ord";
val Finite_imp_well_ord = thm "Finite_imp_well_ord";
val nat_wf_on_converse_Memrel = thm "nat_wf_on_converse_Memrel";
val nat_well_ord_converse_Memrel = thm "nat_well_ord_converse_Memrel";
val well_ord_converse = thm "well_ord_converse";
val ordertype_eq_n = thm "ordertype_eq_n";
val Finite_well_ord_converse = thm "Finite_well_ord_converse";
val nat_into_Finite = thm "nat_into_Finite";
*}

end
