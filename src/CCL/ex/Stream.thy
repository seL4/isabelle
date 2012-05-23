(*  Title:      CCL/ex/Stream.thy
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

header {* Programs defined over streams *}

theory Stream
imports List
begin

definition iter1 :: "[i=>i,i]=>i"
  where "iter1(f,a) == letrec iter x be x$iter(f(x)) in iter(a)"

definition iter2 :: "[i=>i,i]=>i"
  where "iter2(f,a) == letrec iter x be x$map(f,iter(x)) in iter(a)"

(*
Proving properties about infinite lists using coinduction:
    Lists(A)  is the set of all finite and infinite lists of elements of A.
    ILists(A) is the set of infinite lists of elements of A.
*)


subsection {* Map of composition is composition of maps *}

lemma map_comp:
  assumes 1: "l:Lists(A)"
  shows "map(f \<circ> g,l) = map(f,map(g,l))"
  apply (tactic {* eq_coinduct3_tac @{context}
    "{p. EX x y. p=<x,y> & (EX l:Lists (A) .x=map (f \<circ> g,l) & y=map (f,map (g,l)))}" 1 *})
   apply (blast intro: 1)
  apply safe
  apply (drule ListsXH [THEN iffD1])
  apply (tactic "EQgen_tac @{context} [] 1")
   apply fastforce
  done

(*** Mapping the identity function leaves a list unchanged ***)

lemma map_id:
  assumes 1: "l:Lists(A)"
  shows "map(%x. x,l) = l"
  apply (tactic {* eq_coinduct3_tac @{context}
    "{p. EX x y. p=<x,y> & (EX l:Lists (A) .x=map (%x. x,l) & y=l) }" 1 *})
  apply (blast intro: 1)
  apply safe
  apply (drule ListsXH [THEN iffD1])
  apply (tactic "EQgen_tac @{context} [] 1")
  apply blast
  done


subsection {* Mapping distributes over append *}

lemma map_append:
  assumes "l:Lists(A)"
    and "m:Lists(A)"
  shows "map(f,l@m) = map(f,l) @ map(f,m)"
  apply (tactic {* eq_coinduct3_tac @{context}
    "{p. EX x y. p=<x,y> & (EX l:Lists (A). EX m:Lists (A). x=map (f,l@m) & y=map (f,l) @ map (f,m))}" 1 *})
  apply (blast intro: assms)
  apply safe
  apply (drule ListsXH [THEN iffD1])
  apply (tactic "EQgen_tac @{context} [] 1")
  apply (drule ListsXH [THEN iffD1])
  apply (tactic "EQgen_tac @{context} [] 1")
  apply blast
  done


subsection {* Append is associative *}

lemma append_assoc:
  assumes "k:Lists(A)"
    and "l:Lists(A)"
    and "m:Lists(A)"
  shows "k @ l @ m = (k @ l) @ m"
  apply (tactic {* eq_coinduct3_tac @{context}
    "{p. EX x y. p=<x,y> & (EX k:Lists (A). EX l:Lists (A). EX m:Lists (A). x=k @ l @ m & y= (k @ l) @ m) }" 1*})
  apply (blast intro: assms)
  apply safe
  apply (drule ListsXH [THEN iffD1])
  apply (tactic "EQgen_tac @{context} [] 1")
   prefer 2
   apply blast
  apply (tactic {* DEPTH_SOLVE (etac (XH_to_E @{thm ListsXH}) 1
    THEN EQgen_tac @{context} [] 1) *})
  done


subsection {* Appending anything to an infinite list doesn't alter it *}

lemma ilist_append:
  assumes "l:ILists(A)"
  shows "l @ m = l"
  apply (tactic {* eq_coinduct3_tac @{context}
    "{p. EX x y. p=<x,y> & (EX l:ILists (A) .EX m. x=l@m & y=l)}" 1 *})
  apply (blast intro: assms)
  apply safe
  apply (drule IListsXH [THEN iffD1])
  apply (tactic "EQgen_tac @{context} [] 1")
  apply blast
  done

(*** The equivalance of two versions of an iteration function       ***)
(*                                                                    *)
(*        fun iter1(f,a) = a$iter1(f,f(a))                            *)
(*        fun iter2(f,a) = a$map(f,iter2(f,a))                        *)

lemma iter1B: "iter1(f,a) = a$iter1(f,f(a))"
  apply (unfold iter1_def)
  apply (rule letrecB [THEN trans])
  apply simp
  done

lemma iter2B: "iter2(f,a) = a $ map(f,iter2(f,a))"
  apply (unfold iter2_def)
  apply (rule letrecB [THEN trans])
  apply (rule refl)
  done

lemma iter2Blemma:
  "n:Nat ==>  
    map(f) ^ n ` iter2(f,a) = (f ^ n ` a) $ (map(f) ^ n ` map(f,iter2(f,a)))"
  apply (rule_tac P = "%x. ?lhs (x) = ?rhs" in iter2B [THEN ssubst])
  apply (simp add: nmapBcons)
  done

lemma iter1_iter2_eq: "iter1(f,a) = iter2(f,a)"
  apply (tactic {* eq_coinduct3_tac @{context}
    "{p. EX x y. p=<x,y> & (EX n:Nat. x=iter1 (f,f^n`a) & y=map (f) ^n`iter2 (f,a))}" 1*})
  apply (fast intro!: napplyBzero [symmetric] napplyBzero [symmetric, THEN arg_cong])
  apply (tactic {* EQgen_tac @{context} [@{thm iter1B}, @{thm iter2Blemma}] 1 *})
  apply (subst napply_f, assumption)
  apply (rule_tac f1 = f in napplyBsucc [THEN subst])
  apply blast
  done

end
