(*  Title:      ZF/UNITY/AllocBase.thy
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge
*)

header{*Common declarations for Chandy and Charpentier's Allocator*}

theory AllocBase imports Follows MultisetSum Guar begin

abbreviation (input)
  tokbag   :: i  (* tokbags could be multisets...or any ordered type?*)
where
  "tokbag == nat"

axiomatization
  NbT :: i and  (* Number of tokens in system *)
  Nclients :: i  (* Number of clients *)
where
  NbT_pos: "NbT \<in> nat-{0}" and
  Nclients_pos: "Nclients \<in> nat-{0}"
  
text{*This function merely sums the elements of a list*}
consts tokens :: "i =>i"
       item :: i (* Items to be merged/distributed *)
primrec 
  "tokens(Nil) = 0"
  "tokens (Cons(x,xs)) = x #+ tokens(xs)"

consts bag_of :: "i => i"
primrec
  "bag_of(Nil)    = 0"
  "bag_of(Cons(x,xs)) = {#x#} +# bag_of(xs)"


text{*Definitions needed in Client.thy.  We define a recursive predicate
using 0 and 1 to code the truth values.*}
consts all_distinct0 :: "i=>i"
primrec
  "all_distinct0(Nil) = 1"
  "all_distinct0(Cons(a, l)) =
     (if a \<in> set_of_list(l) then 0 else all_distinct0(l))"

definition
  all_distinct  :: "i=>o"  where
   "all_distinct(l) == all_distinct0(l)=1"
  
definition  
  state_of :: "i =>i" --{* coersion from anyting to state *}  where
   "state_of(s) == if s \<in> state then s else st0"

definition
  lift :: "i =>(i=>i)" --{* simplifies the expression of programs*}  where
   "lift(x) == %s. s`x"

text{* function to show that the set of variables is infinite *}
consts
  nat_list_inj :: "i=>i"
  var_inj      :: "i=>i"

primrec
  "nat_list_inj(0) = Nil"
  "nat_list_inj(succ(n)) = Cons(n, nat_list_inj(n))"

primrec
  "var_inj(Var(l)) = length(l)"

definition
  nat_var_inj  :: "i=>i"  where
  "nat_var_inj(n) == Var(nat_list_inj(n))"


subsection{*Various simple lemmas*}

lemma Nclients_NbT_gt_0 [simp]: "0 < Nclients & 0 < NbT"
apply (cut_tac Nclients_pos NbT_pos)
apply (auto intro: Ord_0_lt)
done

lemma Nclients_NbT_not_0 [simp]: "Nclients \<noteq> 0 & NbT \<noteq> 0"
by (cut_tac Nclients_pos NbT_pos, auto)

lemma Nclients_type [simp,TC]: "Nclients\<in>nat"
by (cut_tac Nclients_pos NbT_pos, auto)

lemma NbT_type [simp,TC]: "NbT\<in>nat"
by (cut_tac Nclients_pos NbT_pos, auto)

lemma INT_Nclient_iff [iff]:
     "b\<in>Inter(RepFun(Nclients, B)) <-> (\<forall>x\<in>Nclients. b\<in>B(x))"
by (force simp add: INT_iff)

lemma setsum_fun_mono [rule_format]:
     "n\<in>nat ==>  
      (\<forall>i\<in>nat. i<n --> f(i) $<= g(i)) -->  
      setsum(f, n) $<= setsum(g,n)"
apply (induct_tac "n", simp_all)
apply (subgoal_tac "Finite(x) & x\<notin>x")
 prefer 2 apply (simp add: nat_into_Finite mem_not_refl, clarify)
apply (simp (no_asm_simp) add: succ_def)
apply (subgoal_tac "\<forall>i\<in>nat. i<x--> f(i) $<= g(i) ")
 prefer 2 apply (force dest: leI) 
apply (rule zadd_zle_mono, simp_all)
done

lemma tokens_type [simp,TC]: "l\<in>list(A) ==> tokens(l)\<in>nat"
by (erule list.induct, auto)

lemma tokens_mono_aux [rule_format]:
     "xs\<in>list(A) ==> \<forall>ys\<in>list(A). <xs, ys>\<in>prefix(A)  
   --> tokens(xs) \<le> tokens(ys)"
apply (induct_tac "xs")
apply (auto dest: gen_prefix.dom_subset [THEN subsetD] simp add: prefix_def)
done

lemma tokens_mono: "<xs, ys>\<in>prefix(A) ==> tokens(xs) \<le> tokens(ys)"
apply (cut_tac prefix_type)
apply (blast intro: tokens_mono_aux)
done

lemma mono_tokens [iff]: "mono1(list(A), prefix(A), nat, Le,tokens)"
apply (unfold mono1_def)
apply (auto intro: tokens_mono simp add: Le_def)
done

lemma tokens_append [simp]: 
"[| xs\<in>list(A); ys\<in>list(A) |] ==> tokens(xs@ys) = tokens(xs) #+ tokens(ys)"
apply (induct_tac "xs", auto)
done

subsection{*The function @{term bag_of}*}

lemma bag_of_type [simp,TC]: "l\<in>list(A) ==>bag_of(l)\<in>Mult(A)"
apply (induct_tac "l")
apply (auto simp add: Mult_iff_multiset)
done

lemma bag_of_multiset:
     "l\<in>list(A) ==> multiset(bag_of(l)) & mset_of(bag_of(l))<=A"
apply (drule bag_of_type)
apply (auto simp add: Mult_iff_multiset)
done

lemma bag_of_append [simp]:
    "[| xs\<in>list(A); ys\<in>list(A)|] ==> bag_of(xs@ys) = bag_of(xs) +# bag_of(ys)"
apply (induct_tac "xs")
apply (auto simp add: bag_of_multiset munion_assoc)
done

lemma bag_of_mono_aux [rule_format]:
     "xs\<in>list(A) ==> \<forall>ys\<in>list(A). <xs, ys>\<in>prefix(A)  
      --> <bag_of(xs), bag_of(ys)>\<in>MultLe(A, r)"
apply (induct_tac "xs", simp_all, clarify) 
apply (frule_tac l = ys in bag_of_multiset)
apply (auto intro: empty_le_MultLe simp add: prefix_def)
apply (rule munion_mono)
apply (force simp add: MultLe_def Mult_iff_multiset)
apply (blast dest: gen_prefix.dom_subset [THEN subsetD])
done

lemma bag_of_mono [intro]:
     "[|  <xs, ys>\<in>prefix(A); xs\<in>list(A); ys\<in>list(A) |]
      ==> <bag_of(xs), bag_of(ys)>\<in>MultLe(A, r)"
apply (blast intro: bag_of_mono_aux)
done

lemma mono_bag_of [simp]: 
     "mono1(list(A), prefix(A), Mult(A), MultLe(A,r), bag_of)"
by (auto simp add:  mono1_def bag_of_type)


subsection{*The function @{term msetsum}*}

lemmas nat_into_Fin = eqpoll_refl [THEN [2] Fin_lemma]

lemma list_Int_length_Fin: "l \<in> list(A) ==> C Int length(l) \<in> Fin(length(l))"
apply (drule length_type)
apply (rule Fin_subset)
apply (rule Int_lower2)
apply (erule nat_into_Fin)
done



lemma mem_Int_imp_lt_length:
     "[|xs \<in> list(A); k \<in> C \<inter> length(xs)|] ==> k < length(xs)"
by (simp add: ltI)

lemma Int_succ_right:
     "A Int succ(k) = (if k : A then cons(k, A Int k) else A Int k)"
by auto


lemma bag_of_sublist_lemma:
     "[|C \<subseteq> nat; x \<in> A; xs \<in> list(A)|]   
  ==>  msetsum(\<lambda>i. {#nth(i, xs @ [x])#}, C \<inter> succ(length(xs)), A) =  
       (if length(xs) \<in> C then  
          {#x#} +# msetsum(\<lambda>x. {#nth(x, xs)#}, C \<inter> length(xs), A)  
        else msetsum(\<lambda>x. {#nth(x, xs)#}, C \<inter> length(xs), A))"
apply (simp add: subsetD nth_append lt_not_refl mem_Int_imp_lt_length cong add: msetsum_cong)
apply (simp add: Int_succ_right)
apply (simp add: lt_not_refl mem_Int_imp_lt_length cong add: msetsum_cong, clarify)
apply (subst msetsum_cons)
apply (rule_tac [3] succI1)
apply (blast intro: list_Int_length_Fin subset_succI [THEN Fin_mono, THEN subsetD])
apply (simp add: mem_not_refl)
apply (simp add: nth_type lt_not_refl)
apply (blast intro: nat_into_Ord ltI length_type)
apply (simp add: lt_not_refl mem_Int_imp_lt_length cong add: msetsum_cong)
done

lemma bag_of_sublist_lemma2:
     "l\<in>list(A) ==>  
  C <= nat ==>  
  bag_of(sublist(l, C)) =  
      msetsum(%i. {#nth(i, l)#}, C Int length(l), A)"
apply (erule list_append_induct)
apply (simp (no_asm))
apply (simp (no_asm_simp) add: sublist_append nth_append bag_of_sublist_lemma munion_commute bag_of_sublist_lemma msetsum_multiset munion_0)
done


lemma nat_Int_length_eq: "l \<in> list(A) ==> nat \<inter> length(l) = length(l)"
apply (rule Int_absorb1)
apply (rule OrdmemD, auto)
done

(*eliminating the assumption C<=nat*)
lemma bag_of_sublist:
     "l\<in>list(A) ==>  
  bag_of(sublist(l, C)) = msetsum(%i. {#nth(i, l)#}, C Int length(l), A)"
apply (subgoal_tac " bag_of (sublist (l, C Int nat)) = msetsum (%i. {#nth (i, l) #}, C Int length (l), A) ")
apply (simp add: sublist_Int_eq)
apply (simp add: bag_of_sublist_lemma2 Int_lower2 Int_assoc nat_Int_length_eq)
done

lemma bag_of_sublist_Un_Int: 
"l\<in>list(A) ==>  
  bag_of(sublist(l, B Un C)) +# bag_of(sublist(l, B Int C)) =  
      bag_of(sublist(l, B)) +# bag_of(sublist(l, C))"
apply (subgoal_tac "B Int C Int length (l) = (B Int length (l)) Int (C Int length (l))")
prefer 2 apply blast
apply (simp (no_asm_simp) add: bag_of_sublist Int_Un_distrib2 msetsum_Un_Int)
apply (rule msetsum_Un_Int)
apply (erule list_Int_length_Fin)+
 apply (simp add: ltI nth_type)
done


lemma bag_of_sublist_Un_disjoint:
     "[| l\<in>list(A); B Int C = 0  |] 
      ==> bag_of(sublist(l, B Un C)) =  
          bag_of(sublist(l, B)) +# bag_of(sublist(l, C))"
by (simp add: bag_of_sublist_Un_Int [symmetric] bag_of_multiset)


lemma bag_of_sublist_UN_disjoint [rule_format]:
     "[|Finite(I); \<forall>i\<in>I. \<forall>j\<in>I. i\<noteq>j --> A(i) \<inter> A(j) = 0;  
        l\<in>list(B) |]  
      ==> bag_of(sublist(l, \<Union>i\<in>I. A(i))) =   
          (msetsum(%i. bag_of(sublist(l, A(i))), I, B)) "
apply (simp (no_asm_simp) del: UN_simps
           add: UN_simps [symmetric] bag_of_sublist)
apply (subst  msetsum_UN_disjoint [of _ _ _ "length (l)"])
apply (drule Finite_into_Fin, assumption)
prefer 3 apply force
apply (auto intro!: Fin_IntI2 Finite_into_Fin simp add: ltI nth_type length_type nat_into_Finite)
done


lemma part_ord_Lt [simp]: "part_ord(nat, Lt)"
apply (unfold part_ord_def Lt_def irrefl_def trans_on_def)
apply (auto intro: lt_trans)
done

subsubsection{*The function @{term all_distinct}*}

lemma all_distinct_Nil [simp]: "all_distinct(Nil)"
by (unfold all_distinct_def, auto)

lemma all_distinct_Cons [simp]: 
    "all_distinct(Cons(a,l)) <->  
      (a\<in>set_of_list(l) --> False) & (a \<notin> set_of_list(l) --> all_distinct(l))"
apply (unfold all_distinct_def)
apply (auto elim: list.cases)
done

subsubsection{*The function @{term state_of}*}

lemma state_of_state: "s\<in>state ==> state_of(s)=s"
by (unfold state_of_def, auto)
declare state_of_state [simp]


lemma state_of_idem: "state_of(state_of(s))=state_of(s)"

apply (unfold state_of_def, auto)
done
declare state_of_idem [simp]


lemma state_of_type [simp,TC]: "state_of(s)\<in>state"
by (unfold state_of_def, auto)

lemma lift_apply [simp]: "lift(x, s)=s`x"
by (simp add: lift_def)


(** Used in ClientImp **)

lemma gen_Increains_state_of_eq: 
     "Increasing(A, r, %s. f(state_of(s))) = Increasing(A, r, f)"
apply (unfold Increasing_def, auto)
done

lemmas Increasing_state_ofD1 =  
      gen_Increains_state_of_eq [THEN equalityD1, THEN subsetD]
lemmas Increasing_state_ofD2 =  
      gen_Increains_state_of_eq [THEN equalityD2, THEN subsetD]

lemma Follows_state_of_eq: 
     "Follows(A, r, %s. f(state_of(s)), %s. g(state_of(s))) =   
      Follows(A, r, f, g)"
apply (unfold Follows_def Increasing_def, auto)
done

lemmas Follows_state_ofD1 =
      Follows_state_of_eq [THEN equalityD1, THEN subsetD]
lemmas Follows_state_ofD2 =
      Follows_state_of_eq [THEN equalityD2, THEN subsetD]

lemma nat_list_inj_type: "n\<in>nat ==> nat_list_inj(n)\<in>list(nat)"
by (induct_tac "n", auto)

lemma length_nat_list_inj: "n\<in>nat ==> length(nat_list_inj(n)) = n"
by (induct_tac "n", auto)

lemma var_infinite_lemma: 
  "(\<lambda>x\<in>nat. nat_var_inj(x))\<in>inj(nat, var)"
apply (unfold nat_var_inj_def)
apply (rule_tac d = var_inj in lam_injective)
apply (auto simp add: var.intros nat_list_inj_type)
apply (simp add: length_nat_list_inj)
done

lemma nat_lepoll_var: "nat lepoll var"
apply (unfold lepoll_def)
apply (rule_tac x = " (\<lambda>x\<in>nat. nat_var_inj (x))" in exI)
apply (rule var_infinite_lemma)
done

lemma var_not_Finite: "~Finite(var)"
apply (insert nat_not_Finite) 
apply (blast intro: lepoll_Finite [OF nat_lepoll_var]) 
done

lemma not_Finite_imp_exist: "~Finite(A) ==> \<exists>x. x\<in>A"
apply (subgoal_tac "A\<noteq>0")
apply (auto simp add: Finite_0)
done

lemma Inter_Diff_var_iff:
     "Finite(A) ==> b\<in>(Inter(RepFun(var-A, B))) <-> (\<forall>x\<in>var-A. b\<in>B(x))"
apply (subgoal_tac "\<exists>x. x\<in>var-A", auto)
apply (subgoal_tac "~Finite (var-A) ")
apply (drule not_Finite_imp_exist, auto)
apply (cut_tac var_not_Finite)
apply (erule swap)
apply (rule_tac B = A in Diff_Finite, auto)
done

lemma Inter_var_DiffD:
     "[| b\<in>Inter(RepFun(var-A, B)); Finite(A); x\<in>var-A |] ==> b\<in>B(x)"
by (simp add: Inter_Diff_var_iff)

(* [| Finite(A); (\<forall>x\<in>var-A. b\<in>B(x)) |] ==> b\<in>Inter(RepFun(var-A, B)) *)
lemmas Inter_var_DiffI = Inter_Diff_var_iff [THEN iffD2]

declare Inter_var_DiffI [intro!]

lemma Acts_subset_Int_Pow_simp [simp]:
     "Acts(F)<= A \<inter> Pow(state*state)  <-> Acts(F)<=A"
by (insert Acts_type [of F], auto)

lemma setsum_nsetsum_eq: 
     "[| Finite(A); \<forall>x\<in>A. g(x)\<in>nat |] 
      ==> setsum(%x. $#(g(x)), A) = $# nsetsum(%x. g(x), A)"
apply (erule Finite_induct)
apply (auto simp add: int_of_add)
done

lemma nsetsum_cong: 
     "[| A=B;  \<forall>x\<in>A. f(x)=g(x);  \<forall>x\<in>A. g(x)\<in>nat;  Finite(A) |]  
      ==> nsetsum(f, A) = nsetsum(g, B)"
apply (subgoal_tac "$# nsetsum (f, A) = $# nsetsum (g, B)", simp)
apply (simp add: setsum_nsetsum_eq [symmetric] cong: setsum_cong) 
done

end
