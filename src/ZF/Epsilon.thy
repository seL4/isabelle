(*  Title:      ZF/epsilon.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

*)

header{*Epsilon Induction and Recursion*}

theory Epsilon = Nat:

constdefs
  eclose    :: "i=>i"
    "eclose(A) == UN n:nat. nat_rec(n, A, %m r. Union(r))"

  transrec  :: "[i, [i,i]=>i] =>i"
    "transrec(a,H) == wfrec(Memrel(eclose({a})), a, H)"
 
  rank      :: "i=>i"
    "rank(a) == transrec(a, %x f. UN y:x. succ(f`y))"

  transrec2 :: "[i, i, [i,i]=>i] =>i"
    "transrec2(k, a, b) ==                     
       transrec(k, 
                %i r. if(i=0, a, 
                        if(EX j. i=succ(j),        
                           b(THE j. i=succ(j), r`(THE j. i=succ(j))),   
                           UN j<i. r`j)))"

  recursor  :: "[i, [i,i]=>i, i]=>i"
    "recursor(a,b,k) ==  transrec(k, %n f. nat_case(a, %m. b(m, f`m), n))"

  rec  :: "[i, i, [i,i]=>i]=>i"
    "rec(k,a,b) == recursor(a,b,k)"


subsection{*Basic Closure Properties*}

lemma arg_subset_eclose: "A <= eclose(A)"
apply (unfold eclose_def)
apply (rule nat_rec_0 [THEN equalityD2, THEN subset_trans])
apply (rule nat_0I [THEN UN_upper])
done

lemmas arg_into_eclose = arg_subset_eclose [THEN subsetD, standard]

lemma Transset_eclose: "Transset(eclose(A))"
apply (unfold eclose_def Transset_def)
apply (rule subsetI [THEN ballI])
apply (erule UN_E)
apply (rule nat_succI [THEN UN_I], assumption)
apply (erule nat_rec_succ [THEN ssubst])
apply (erule UnionI, assumption)
done

(* x : eclose(A) ==> x <= eclose(A) *)
lemmas eclose_subset =  
       Transset_eclose [unfolded Transset_def, THEN bspec, standard]

(* [| A : eclose(B); c : A |] ==> c : eclose(B) *)
lemmas ecloseD = eclose_subset [THEN subsetD, standard]

lemmas arg_in_eclose_sing = arg_subset_eclose [THEN singleton_subsetD]
lemmas arg_into_eclose_sing = arg_in_eclose_sing [THEN ecloseD, standard]

(* This is epsilon-induction for eclose(A); see also eclose_induct_down...
   [| a: eclose(A);  !!x. [| x: eclose(A); ALL y:x. P(y) |] ==> P(x) 
   |] ==> P(a) 
*)
lemmas eclose_induct =
     Transset_induct [OF _ Transset_eclose, induct set: eclose]


(*Epsilon induction*)
lemma eps_induct:
    "[| !!x. ALL y:x. P(y) ==> P(x) |]  ==>  P(a)"
by (rule arg_in_eclose_sing [THEN eclose_induct], blast) 


subsection{*Leastness of @{term eclose}*}

(** eclose(A) is the least transitive set including A as a subset. **)

lemma eclose_least_lemma: 
    "[| Transset(X);  A<=X;  n: nat |] ==> nat_rec(n, A, %m r. Union(r)) <= X"
apply (unfold Transset_def)
apply (erule nat_induct) 
apply (simp add: nat_rec_0)
apply (simp add: nat_rec_succ, blast)
done

lemma eclose_least: 
     "[| Transset(X);  A<=X |] ==> eclose(A) <= X"
apply (unfold eclose_def)
apply (rule eclose_least_lemma [THEN UN_least], assumption+)
done

(*COMPLETELY DIFFERENT induction principle from eclose_induct!!*)
lemma eclose_induct_down [consumes 1]:
    "[| a: eclose(b);                                            
        !!y.   [| y: b |] ==> P(y);                              
        !!y z. [| y: eclose(b);  P(y);  z: y |] ==> P(z)         
     |] ==> P(a)"
apply (rule eclose_least [THEN subsetD, THEN CollectD2, of "eclose(b)"])
  prefer 3 apply assumption
 apply (unfold Transset_def) 
 apply (blast intro: ecloseD)
apply (blast intro: arg_subset_eclose [THEN subsetD])
done

lemma Transset_eclose_eq_arg: "Transset(X) ==> eclose(X) = X"
apply (erule equalityI [OF eclose_least arg_subset_eclose])
apply (rule subset_refl)
done

text{*A transitive set either is empty or contains the empty set.*}
lemma Transset_0_lemma [rule_format]: "Transset(A) ==> x\<in>A --> 0\<in>A";
apply (simp add: Transset_def) 
apply (rule_tac a=x in eps_induct, clarify) 
apply (drule bspec, assumption) 
apply (rule_tac P = "x=0" in case_split_thm, auto)
done

lemma Transset_0_disj: "Transset(A) ==> A=0 | 0\<in>A";
by (blast dest: Transset_0_lemma)


subsection{*Epsilon Recursion*}

(*Unused...*)
lemma mem_eclose_trans: "[| A: eclose(B);  B: eclose(C) |] ==> A: eclose(C)"
by (rule eclose_least [OF Transset_eclose eclose_subset, THEN subsetD], 
    assumption+)

(*Variant of the previous lemma in a useable form for the sequel*)
lemma mem_eclose_sing_trans:
     "[| A: eclose({B});  B: eclose({C}) |] ==> A: eclose({C})"
by (rule eclose_least [OF Transset_eclose singleton_subsetI, THEN subsetD], 
    assumption+)

lemma under_Memrel: "[| Transset(i);  j:i |] ==> Memrel(i)-``{j} = j"
by (unfold Transset_def, blast)

lemma lt_Memrel: "j < i ==> Memrel(i) -`` {j} = j"
by (simp add: lt_def Ord_def under_Memrel) 

(* j : eclose(A) ==> Memrel(eclose(A)) -`` j = j *)
lemmas under_Memrel_eclose = Transset_eclose [THEN under_Memrel, standard]

lemmas wfrec_ssubst = wf_Memrel [THEN wfrec, THEN ssubst]

lemma wfrec_eclose_eq:
    "[| k:eclose({j});  j:eclose({i}) |] ==>  
     wfrec(Memrel(eclose({i})), k, H) = wfrec(Memrel(eclose({j})), k, H)"
apply (erule eclose_induct)
apply (rule wfrec_ssubst)
apply (rule wfrec_ssubst)
apply (simp add: under_Memrel_eclose mem_eclose_sing_trans [of _ j i])
done

lemma wfrec_eclose_eq2: 
    "k: i ==> wfrec(Memrel(eclose({i})),k,H) = wfrec(Memrel(eclose({k})),k,H)"
apply (rule arg_in_eclose_sing [THEN wfrec_eclose_eq])
apply (erule arg_into_eclose_sing)
done

lemma transrec: "transrec(a,H) = H(a, lam x:a. transrec(x,H))"
apply (unfold transrec_def)
apply (rule wfrec_ssubst)
apply (simp add: wfrec_eclose_eq2 arg_in_eclose_sing under_Memrel_eclose)
done

(*Avoids explosions in proofs; resolve it with a meta-level definition.*)
lemma def_transrec:
    "[| !!x. f(x)==transrec(x,H) |] ==> f(a) = H(a, lam x:a. f(x))"
apply simp
apply (rule transrec)
done

lemma transrec_type:
    "[| !!x u. [| x:eclose({a});  u: Pi(x,B) |] ==> H(x,u) : B(x) |]
     ==> transrec(a,H) : B(a)"
apply (rule_tac i = "a" in arg_in_eclose_sing [THEN eclose_induct])
apply (subst transrec)
apply (simp add: lam_type) 
done

lemma eclose_sing_Ord: "Ord(i) ==> eclose({i}) <= succ(i)"
apply (erule Ord_is_Transset [THEN Transset_succ, THEN eclose_least])
apply (rule succI1 [THEN singleton_subsetI])
done

lemma succ_subset_eclose_sing: "succ(i) <= eclose({i})"
apply (insert arg_subset_eclose [of "{i}"], simp) 
apply (frule eclose_subset, blast) 
done

lemma eclose_sing_Ord_eq: "Ord(i) ==> eclose({i}) = succ(i)"
apply (rule equalityI)
apply (erule eclose_sing_Ord)  
apply (rule succ_subset_eclose_sing) 
done

lemma Ord_transrec_type:
  assumes jini: "j: i"
      and ordi: "Ord(i)"
      and minor: " !!x u. [| x: i;  u: Pi(x,B) |] ==> H(x,u) : B(x)"
  shows "transrec(j,H) : B(j)"
apply (rule transrec_type)
apply (insert jini ordi)
apply (blast intro!: minor
             intro: Ord_trans 
             dest: Ord_in_Ord [THEN eclose_sing_Ord, THEN subsetD])
done

subsection{*Rank*}

(*NOT SUITABLE FOR REWRITING -- RECURSIVE!*)
lemma rank: "rank(a) = (UN y:a. succ(rank(y)))"
by (subst rank_def [THEN def_transrec], simp)

lemma Ord_rank [simp]: "Ord(rank(a))"
apply (rule_tac a="a" in eps_induct) 
apply (subst rank)
apply (rule Ord_succ [THEN Ord_UN])
apply (erule bspec, assumption)
done

lemma rank_of_Ord: "Ord(i) ==> rank(i) = i"
apply (erule trans_induct)
apply (subst rank)
apply (simp add: Ord_equality)
done

lemma rank_lt: "a:b ==> rank(a) < rank(b)"
apply (rule_tac a1 = "b" in rank [THEN ssubst])
apply (erule UN_I [THEN ltI])
apply (rule_tac [2] Ord_UN, auto)
done

lemma eclose_rank_lt: "a: eclose(b) ==> rank(a) < rank(b)"
apply (erule eclose_induct_down)
apply (erule rank_lt)
apply (erule rank_lt [THEN lt_trans], assumption)
done

lemma rank_mono: "a<=b ==> rank(a) le rank(b)"
apply (rule subset_imp_le)
apply (subst rank)
apply (subst rank, auto)
done

lemma rank_Pow: "rank(Pow(a)) = succ(rank(a))"
apply (rule rank [THEN trans])
apply (rule le_anti_sym)
apply (rule_tac [2] UN_upper_le)
apply (rule UN_least_le)
apply (auto intro: rank_mono simp add: Ord_UN)
done

lemma rank_0 [simp]: "rank(0) = 0"
by (rule rank [THEN trans], blast)

lemma rank_succ [simp]: "rank(succ(x)) = succ(rank(x))"
apply (rule rank [THEN trans])
apply (rule equalityI [OF UN_least succI1 [THEN UN_upper]])
apply (erule succE, blast)
apply (erule rank_lt [THEN leI, THEN succ_leI, THEN le_imp_subset])
done

lemma rank_Union: "rank(Union(A)) = (UN x:A. rank(x))"
apply (rule equalityI)
apply (rule_tac [2] rank_mono [THEN le_imp_subset, THEN UN_least])
apply (erule_tac [2] Union_upper)
apply (subst rank)
apply (rule UN_least)
apply (erule UnionE)
apply (rule subset_trans)
apply (erule_tac [2] RepFunI [THEN Union_upper])
apply (erule rank_lt [THEN succ_leI, THEN le_imp_subset])
done

lemma rank_eclose: "rank(eclose(a)) = rank(a)"
apply (rule le_anti_sym)
apply (rule_tac [2] arg_subset_eclose [THEN rank_mono])
apply (rule_tac a1 = "eclose (a) " in rank [THEN ssubst])
apply (rule Ord_rank [THEN UN_least_le])
apply (erule eclose_rank_lt [THEN succ_leI])
done

lemma rank_pair1: "rank(a) < rank(<a,b>)"
apply (unfold Pair_def)
apply (rule consI1 [THEN rank_lt, THEN lt_trans])
apply (rule consI1 [THEN consI2, THEN rank_lt])
done

lemma rank_pair2: "rank(b) < rank(<a,b>)"
apply (unfold Pair_def)
apply (rule consI1 [THEN consI2, THEN rank_lt, THEN lt_trans])
apply (rule consI1 [THEN consI2, THEN rank_lt])
done

(*Not clear how to remove the P(a) condition, since the "then" part
  must refer to "a"*)
lemma the_equality_if:
     "P(a) ==> (THE x. P(x)) = (if (EX!x. P(x)) then a else 0)"
by (simp add: the_0 the_equality2)

(*The first premise not only fixs i but ensures f~=0.
  The second premise is now essential.  Consider otherwise the relation 
  r = {<0,0>,<0,1>,<0,2>,...}.  Then f`0 = Union(f``{0}) = Union(nat) = nat,
  whose rank equals that of r.*)
lemma rank_apply: "[|i : domain(f); function(f)|] ==> rank(f`i) < rank(f)"
apply clarify  
apply (simp add: function_apply_equality) 
apply (blast intro: lt_trans rank_lt rank_pair2)
done


subsection{*Corollaries of Leastness*}

lemma mem_eclose_subset: "A:B ==> eclose(A)<=eclose(B)"
apply (rule Transset_eclose [THEN eclose_least])
apply (erule arg_into_eclose [THEN eclose_subset])
done

lemma eclose_mono: "A<=B ==> eclose(A) <= eclose(B)"
apply (rule Transset_eclose [THEN eclose_least])
apply (erule subset_trans)
apply (rule arg_subset_eclose)
done

(** Idempotence of eclose **)

lemma eclose_idem: "eclose(eclose(A)) = eclose(A)"
apply (rule equalityI)
apply (rule eclose_least [OF Transset_eclose subset_refl])
apply (rule arg_subset_eclose)
done

(** Transfinite recursion for definitions based on the 
    three cases of ordinals **)

lemma transrec2_0 [simp]: "transrec2(0,a,b) = a"
by (rule transrec2_def [THEN def_transrec, THEN trans], simp)

lemma transrec2_succ [simp]: "transrec2(succ(i),a,b) = b(i, transrec2(i,a,b))"
apply (rule transrec2_def [THEN def_transrec, THEN trans])
apply (simp add: the_equality if_P)
done

lemma transrec2_Limit:
     "Limit(i) ==> transrec2(i,a,b) = (UN j<i. transrec2(j,a,b))"
apply (rule transrec2_def [THEN def_transrec, THEN trans])
apply (auto simp add: OUnion_def) 
done

lemma def_transrec2:
     "(!!x. f(x)==transrec2(x,a,b))
      ==> f(0) = a & 
          f(succ(i)) = b(i, f(i)) & 
          (Limit(K) --> f(K) = (UN j<K. f(j)))"
by (simp add: transrec2_Limit)


(** recursor -- better than nat_rec; the succ case has no type requirement! **)

(*NOT suitable for rewriting*)
lemmas recursor_lemma = recursor_def [THEN def_transrec, THEN trans]

lemma recursor_0: "recursor(a,b,0) = a"
by (rule nat_case_0 [THEN recursor_lemma])

lemma recursor_succ: "recursor(a,b,succ(m)) = b(m, recursor(a,b,m))"
by (rule recursor_lemma, simp)


(** rec: old version for compatibility **)

lemma rec_0 [simp]: "rec(0,a,b) = a"
apply (unfold rec_def)
apply (rule recursor_0)
done

lemma rec_succ [simp]: "rec(succ(m),a,b) = b(m, rec(m,a,b))"
apply (unfold rec_def)
apply (rule recursor_succ)
done

lemma rec_type:
    "[| n: nat;   
        a: C(0);   
        !!m z. [| m: nat;  z: C(m) |] ==> b(m,z): C(succ(m)) |]
     ==> rec(n,a,b) : C(n)"
by (erule nat_induct, auto)

ML
{*
val arg_subset_eclose = thm "arg_subset_eclose";
val arg_into_eclose = thm "arg_into_eclose";
val Transset_eclose = thm "Transset_eclose";
val eclose_subset = thm "eclose_subset";
val ecloseD = thm "ecloseD";
val arg_in_eclose_sing = thm "arg_in_eclose_sing";
val arg_into_eclose_sing = thm "arg_into_eclose_sing";
val eclose_induct = thm "eclose_induct";
val eps_induct = thm "eps_induct";
val eclose_least = thm "eclose_least";
val eclose_induct_down = thm "eclose_induct_down";
val Transset_eclose_eq_arg = thm "Transset_eclose_eq_arg";
val mem_eclose_trans = thm "mem_eclose_trans";
val mem_eclose_sing_trans = thm "mem_eclose_sing_trans";
val under_Memrel = thm "under_Memrel";
val under_Memrel_eclose = thm "under_Memrel_eclose";
val wfrec_ssubst = thm "wfrec_ssubst";
val wfrec_eclose_eq = thm "wfrec_eclose_eq";
val wfrec_eclose_eq2 = thm "wfrec_eclose_eq2";
val transrec = thm "transrec";
val def_transrec = thm "def_transrec";
val transrec_type = thm "transrec_type";
val eclose_sing_Ord = thm "eclose_sing_Ord";
val Ord_transrec_type = thm "Ord_transrec_type";
val rank = thm "rank";
val Ord_rank = thm "Ord_rank";
val rank_of_Ord = thm "rank_of_Ord";
val rank_lt = thm "rank_lt";
val eclose_rank_lt = thm "eclose_rank_lt";
val rank_mono = thm "rank_mono";
val rank_Pow = thm "rank_Pow";
val rank_0 = thm "rank_0";
val rank_succ = thm "rank_succ";
val rank_Union = thm "rank_Union";
val rank_eclose = thm "rank_eclose";
val rank_pair1 = thm "rank_pair1";
val rank_pair2 = thm "rank_pair2";
val the_equality_if = thm "the_equality_if";
val rank_apply = thm "rank_apply";
val mem_eclose_subset = thm "mem_eclose_subset";
val eclose_mono = thm "eclose_mono";
val eclose_idem = thm "eclose_idem";
val transrec2_0 = thm "transrec2_0";
val transrec2_succ = thm "transrec2_succ";
val transrec2_Limit = thm "transrec2_Limit";
val recursor_0 = thm "recursor_0";
val recursor_succ = thm "recursor_succ";
val rec_0 = thm "rec_0";
val rec_succ = thm "rec_succ";
val rec_type = thm "rec_type";
*}

end
