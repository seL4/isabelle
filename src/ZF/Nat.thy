(*  Title:      ZF/Nat.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

*)

header{*The Natural numbers As a Least Fixed Point*}

theory Nat = OrdQuant + Bool + mono:

constdefs
  nat :: i
    "nat == lfp(Inf, %X. {0} Un {succ(i). i:X})"

  quasinat :: "i => o"
    "quasinat(n) == n=0 | (\<exists>m. n = succ(m))"

  (*Has an unconditional succ case, which is used in "recursor" below.*)
  nat_case :: "[i, i=>i, i]=>i"
    "nat_case(a,b,k) == THE y. k=0 & y=a | (EX x. k=succ(x) & y=b(x))"

  nat_rec :: "[i, i, [i,i]=>i]=>i"
    "nat_rec(k,a,b) ==   
          wfrec(Memrel(nat), k, %n f. nat_case(a, %m. b(m, f`m), n))"

  (*Internalized relations on the naturals*)
  
  Le :: i
    "Le == {<x,y>:nat*nat. x le y}"

  Lt :: i
    "Lt == {<x, y>:nat*nat. x < y}"
  
  Ge :: i
    "Ge == {<x,y>:nat*nat. y le x}"

  Gt :: i
    "Gt == {<x,y>:nat*nat. y < x}"

  less_than :: "i=>i"
    "less_than(n) == {i:nat.  i<n}"

  greater_than :: "i=>i"
    "greater_than(n) == {i:nat. n < i}"

lemma nat_bnd_mono: "bnd_mono(Inf, %X. {0} Un {succ(i). i:X})"
apply (rule bnd_monoI)
apply (cut_tac infinity, blast, blast) 
done

(* nat = {0} Un {succ(x). x:nat} *)
lemmas nat_unfold = nat_bnd_mono [THEN nat_def [THEN def_lfp_unfold], standard]

(** Type checking of 0 and successor **)

lemma nat_0I [iff,TC]: "0 : nat"
apply (subst nat_unfold)
apply (rule singletonI [THEN UnI1])
done

lemma nat_succI [intro!,TC]: "n : nat ==> succ(n) : nat"
apply (subst nat_unfold)
apply (erule RepFunI [THEN UnI2])
done

lemma nat_1I [iff,TC]: "1 : nat"
by (rule nat_0I [THEN nat_succI])

lemma nat_2I [iff,TC]: "2 : nat"
by (rule nat_1I [THEN nat_succI])

lemma bool_subset_nat: "bool <= nat"
by (blast elim!: boolE)

lemmas bool_into_nat = bool_subset_nat [THEN subsetD, standard]


subsection{*Injectivity Properties and Induction*}

(*Mathematical induction*)
lemma nat_induct:
    "[| n: nat;  P(0);  !!x. [| x: nat;  P(x) |] ==> P(succ(x)) |] ==> P(n)"
by (erule def_induct [OF nat_def nat_bnd_mono], blast)

(*fixed up for induct method*)
lemmas nat_induct = nat_induct [case_names 0 succ, induct set: nat]

lemma natE:
    "[| n: nat;  n=0 ==> P;  !!x. [| x: nat; n=succ(x) |] ==> P |] ==> P"
by (erule nat_unfold [THEN equalityD1, THEN subsetD, THEN UnE], auto) 

lemma nat_into_Ord [simp]: "n: nat ==> Ord(n)"
by (erule nat_induct, auto)

(* i: nat ==> 0 le i; same thing as 0<succ(i)  *)
lemmas nat_0_le = nat_into_Ord [THEN Ord_0_le, standard]

(* i: nat ==> i le i; same thing as i<succ(i)  *)
lemmas nat_le_refl = nat_into_Ord [THEN le_refl, standard]

lemma Ord_nat [iff]: "Ord(nat)"
apply (rule OrdI)
apply (erule_tac [2] nat_into_Ord [THEN Ord_is_Transset])
apply (unfold Transset_def)
apply (rule ballI)
apply (erule nat_induct, auto) 
done

lemma Limit_nat [iff]: "Limit(nat)"
apply (unfold Limit_def)
apply (safe intro!: ltI Ord_nat)
apply (erule ltD)
done

lemma succ_natD [dest!]: "succ(i): nat ==> i: nat"
by (rule Ord_trans [OF succI1], auto)

lemma nat_succ_iff [iff]: "succ(n): nat <-> n: nat"
by blast

lemma nat_le_Limit: "Limit(i) ==> nat le i"
apply (rule subset_imp_le)
apply (simp_all add: Limit_is_Ord) 
apply (rule subsetI)
apply (erule nat_induct)
 apply (erule Limit_has_0 [THEN ltD]) 
apply (blast intro: Limit_has_succ [THEN ltD] ltI Limit_is_Ord)
done

(* [| succ(i): k;  k: nat |] ==> i: k *)
lemmas succ_in_naturalD = Ord_trans [OF succI1 _ nat_into_Ord]

lemma lt_nat_in_nat: "[| m<n;  n: nat |] ==> m: nat"
apply (erule ltE)
apply (erule Ord_trans, assumption, simp) 
done

lemma le_in_nat: "[| m le n; n:nat |] ==> m:nat"
by (blast dest!: lt_nat_in_nat)


subsection{*Variations on Mathematical Induction*}

(*complete induction*)

lemmas complete_induct = Ord_induct [OF _ Ord_nat, case_names less, consumes 1]

lemmas complete_induct_rule =  
	complete_induct [rule_format, case_names less, consumes 1]


lemma nat_induct_from_lemma [rule_format]: 
    "[| n: nat;  m: nat;   
        !!x. [| x: nat;  m le x;  P(x) |] ==> P(succ(x)) |] 
     ==> m le n --> P(m) --> P(n)"
apply (erule nat_induct) 
apply (simp_all add: distrib_simps le0_iff le_succ_iff)
done

(*Induction starting from m rather than 0*)
lemma nat_induct_from: 
    "[| m le n;  m: nat;  n: nat;   
        P(m);   
        !!x. [| x: nat;  m le x;  P(x) |] ==> P(succ(x)) |]
     ==> P(n)"
apply (blast intro: nat_induct_from_lemma)
done

(*Induction suitable for subtraction and less-than*)
lemma diff_induct: 
    "[| m: nat;  n: nat;   
        !!x. x: nat ==> P(x,0);   
        !!y. y: nat ==> P(0,succ(y));   
        !!x y. [| x: nat;  y: nat;  P(x,y) |] ==> P(succ(x),succ(y)) |]
     ==> P(m,n)"
apply (erule_tac x = "m" in rev_bspec)
apply (erule nat_induct, simp) 
apply (rule ballI)
apply (rename_tac i j)
apply (erule_tac n=j in nat_induct, auto)  
done

(*fixed up for induct method*)
lemmas diff_induct = diff_induct [case_names 0 0_succ succ_succ, consumes 2]

(** Induction principle analogous to trancl_induct **)

lemma succ_lt_induct_lemma [rule_format]:
     "m: nat ==> P(m,succ(m)) --> (ALL x: nat. P(m,x) --> P(m,succ(x))) -->  
                 (ALL n:nat. m<n --> P(m,n))"
apply (erule nat_induct)
 apply (intro impI, rule nat_induct [THEN ballI])
   prefer 4 apply (intro impI, rule nat_induct [THEN ballI])
apply (auto simp add: le_iff) 
done

lemma succ_lt_induct:
    "[| m<n;  n: nat;                                    
        P(m,succ(m));                                    
        !!x. [| x: nat;  P(m,x) |] ==> P(m,succ(x)) |]
     ==> P(m,n)"
by (blast intro: succ_lt_induct_lemma lt_nat_in_nat) 

subsection{*quasinat: to allow a case-split rule for @{term nat_case}*}

text{*True if the argument is zero or any successor*}
lemma [iff]: "quasinat(0)"
by (simp add: quasinat_def)

lemma [iff]: "quasinat(succ(x))"
by (simp add: quasinat_def)

lemma nat_imp_quasinat: "n \<in> nat ==> quasinat(n)"
by (erule natE, simp_all)

lemma non_nat_case: "~ quasinat(x) ==> nat_case(a,b,x) = 0" 
by (simp add: quasinat_def nat_case_def) 

lemma nat_cases_disj: "k=0 | (\<exists>y. k = succ(y)) | ~ quasinat(k)"
txt{*The @{text case_tac} method is not yet available.*}
apply (rule_tac P = "k=0" in case_split_thm, simp) 
apply (rule_tac P = "\<exists>m. k = succ(m)" in case_split_thm, simp) 
apply simp 
apply (simp add: quasinat_def) 
done

lemma nat_cases:
     "[|k=0 ==> P;  !!y. k = succ(y) ==> P; ~ quasinat(k) ==> P|] ==> P"
by (insert nat_cases_disj [of k], blast) 

(** nat_case **)

lemma nat_case_0 [simp]: "nat_case(a,b,0) = a"
by (simp add: nat_case_def)

lemma nat_case_succ [simp]: "nat_case(a,b,succ(n)) = b(n)" 
by (simp add: nat_case_def)

lemma nat_case_type [TC]:
    "[| n: nat;  a: C(0);  !!m. m: nat ==> b(m): C(succ(m)) |] 
     ==> nat_case(a,b,n) : C(n)";
by (erule nat_induct, auto) 

lemma split_nat_case:
  "P(nat_case(a,b,k)) <-> 
   ((k=0 --> P(a)) & (\<forall>x. k=succ(x) --> P(b(x))) & (~ quasinat(k) \<longrightarrow> P(0)))"
apply (rule nat_cases [of k]) 
apply (auto simp add: non_nat_case)
done


subsection{*Recursion on the Natural Numbers*}

(** nat_rec is used to define eclose and transrec, then becomes obsolete.
    The operator rec, from arith.thy, has fewer typing conditions **)

lemma nat_rec_0: "nat_rec(0,a,b) = a"
apply (rule nat_rec_def [THEN def_wfrec, THEN trans])
 apply (rule wf_Memrel) 
apply (rule nat_case_0)
done

lemma nat_rec_succ: "m: nat ==> nat_rec(succ(m),a,b) = b(m, nat_rec(m,a,b))"
apply (rule nat_rec_def [THEN def_wfrec, THEN trans])
 apply (rule wf_Memrel) 
apply (simp add: vimage_singleton_iff)
done

(** The union of two natural numbers is a natural number -- their maximum **)

lemma Un_nat_type [TC]: "[| i: nat; j: nat |] ==> i Un j: nat"
apply (rule Un_least_lt [THEN ltD])
apply (simp_all add: lt_def) 
done

lemma Int_nat_type [TC]: "[| i: nat; j: nat |] ==> i Int j: nat"
apply (rule Int_greatest_lt [THEN ltD])
apply (simp_all add: lt_def) 
done

(*needed to simplify unions over nat*)
lemma nat_nonempty [simp]: "nat ~= 0"
by blast


ML
{*
val Le_def = thm "Le_def";
val Lt_def = thm "Lt_def";
val Ge_def = thm "Ge_def";
val Gt_def = thm "Gt_def";
val less_than_def = thm "less_than_def";
val greater_than_def = thm "greater_than_def";

val nat_bnd_mono = thm "nat_bnd_mono";
val nat_unfold = thm "nat_unfold";
val nat_0I = thm "nat_0I";
val nat_succI = thm "nat_succI";
val nat_1I = thm "nat_1I";
val nat_2I = thm "nat_2I";
val bool_subset_nat = thm "bool_subset_nat";
val bool_into_nat = thm "bool_into_nat";
val nat_induct = thm "nat_induct";
val natE = thm "natE";
val nat_into_Ord = thm "nat_into_Ord";
val nat_0_le = thm "nat_0_le";
val nat_le_refl = thm "nat_le_refl";
val Ord_nat = thm "Ord_nat";
val Limit_nat = thm "Limit_nat";
val succ_natD = thm "succ_natD";
val nat_succ_iff = thm "nat_succ_iff";
val nat_le_Limit = thm "nat_le_Limit";
val succ_in_naturalD = thm "succ_in_naturalD";
val lt_nat_in_nat = thm "lt_nat_in_nat";
val le_in_nat = thm "le_in_nat";
val complete_induct = thm "complete_induct";
val nat_induct_from = thm "nat_induct_from";
val diff_induct = thm "diff_induct";
val succ_lt_induct = thm "succ_lt_induct";
val nat_case_0 = thm "nat_case_0";
val nat_case_succ = thm "nat_case_succ";
val nat_case_type = thm "nat_case_type";
val nat_rec_0 = thm "nat_rec_0";
val nat_rec_succ = thm "nat_rec_succ";
val Un_nat_type = thm "Un_nat_type";
val Int_nat_type = thm "Int_nat_type";
val nat_nonempty = thm "nat_nonempty";
*}

end
