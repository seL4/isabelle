header {* Mostly Isar-style Reasoning for Binary Tree Operations *}
theory BinaryTree_Map = BinaryTree:

text {* We prove correctness of map operations
 implemented using binary search trees from BinaryTree.

 This document is GPL.

 Author: Viktor Kuncak, MIT CSAIL, November 2003 *}


(*============================================================*)
section {* Map implementation and an abstraction function *}
(*============================================================*)

types 
  'a tarray = "(index * 'a) Tree"

constdefs
  valid_tmap :: "'a tarray => bool"
  "valid_tmap t == sortedTree fst t"

declare valid_tmap_def [simp]

constdefs
  mapOf :: "'a tarray => index => 'a option"
  -- {* the abstraction function from trees to maps *}
  "mapOf t i == 
   (case (tlookup fst i t) of
     None => None
   | Some ia => Some (snd ia))"

(*============================================================*)
section {* Auxiliary Properties of our Implementation *}
(*============================================================*)

lemma mapOf_lookup1: "tlookup fst i t = None ==> mapOf t i = None"
by (simp add: mapOf_def)

lemma mapOf_lookup2: "tlookup fst i t = Some (j,a) ==> mapOf t i = Some a"
by (simp add: mapOf_def)

lemma assumes h: "mapOf t i = None"
      shows mapOf_lookup3: "tlookup fst i t = None"
proof (cases "tlookup fst i t")
case None from this show ?thesis by assumption
next case (Some ia) note tsome = this
  from this have o1: "tlookup fst i t = Some (fst ia, snd ia)" by simp
  have "mapOf t i = Some (snd ia)"
  by (insert mapOf_lookup2 [of i t "fst ia" "snd ia"], simp add: o1)
  from this have "mapOf t i ~= None" by simp
  from this h show ?thesis by simp -- {* contradiction *}
qed

lemma assumes v: "valid_tmap t"
      assumes h: "mapOf t i = Some a"
      shows mapOf_lookup4: "tlookup fst i t = Some (i,a)"
proof (cases "tlookup fst i t")
case None 
  from this mapOf_lookup1 have "mapOf t i = None" by auto
  from this h show ?thesis by simp -- {* contradiction *}
next case (Some ia) note tsome = this
  have tlookup_some_inst: "sortedTree fst t & (tlookup fst i t = Some ia) --> 
        ia : setOf t & fst ia = i" by (simp add: tlookup_some)
  from tlookup_some_inst tsome v have "ia : setOf t" by simp
  from tsome have "mapOf t i = Some (snd ia)" by (simp add: mapOf_def)
  from this h have o1: "snd ia = a" by simp
  from tlookup_some_inst tsome v have o2: "fst ia = i" by simp
  from o1 o2 have "ia = (i,a)" by auto
  from this tsome show "tlookup fst i t = Some (i, a)" by simp
qed

subsection {* Lemmas @{text mapset_none} and @{text mapset_some} establish 
              a relation between the set and map abstraction of the tree *}

lemma assumes v: "valid_tmap t"
      shows mapset_none: "(mapOf t i = None) = (ALL a. (i,a) ~: setOf t)"
proof
  -- {* ==> *}
  assume mapNone: "mapOf t i = None"
  from v mapNone mapOf_lookup3 have lnone: "tlookup fst i t = None" by auto
  show "ALL a. (i,a) ~: setOf t"
  proof
    fix a
    show "(i,a) ~: setOf t"
    proof
      assume iain: "(i,a) : setOf t"
      have tlookup_none_inst: 
      "sortedTree fst t & (tlookup fst i t = None) --> (ALL x:setOf t. fst x ~= i)"
      by (insert tlookup_none [of "fst" "t" "i"], assumption)
      from v lnone tlookup_none_inst have "ALL x : setOf t. fst x ~= i" by simp
      from this iain have "fst (i,a) ~= i" by fastsimp
      from this show False by simp
    qed
  qed
  -- {* <== *}
  next assume h: "ALL a. (i,a) ~: setOf t"
  show "mapOf t i = None"
  proof (cases "mapOf t i")
  case None show ?thesis by assumption
  next case (Some a) note mapsome = this
    from v mapsome have o1: "tlookup fst i t = Some (i,a)" by (simp add: mapOf_lookup4)
    (* moving mapOf_lookup4 to assumption does not work, although it uses
       no == !! *)
    from tlookup_some have tlookup_some_inst:
    "sortedTree fst t & tlookup fst i t = Some (i,a) --> 
     (i,a) : setOf t & fst (i,a) = i"
    by (insert tlookup_some [of fst t i "(i,a)"], assumption)   
    from v o1 this have "(i,a) : setOf t" by simp
    from this h show ?thesis by auto -- {* contradiction *}
  qed
qed

lemma assumes v: "valid_tmap t"
      shows mapset_some: "(mapOf t i = Some a) = ((i,a) : setOf t)"
proof
  -- {* ==> *}
  assume mapsome: "mapOf t i = Some a"
  from v mapsome have o1: "tlookup fst i t = Some (i,a)" by (simp add: mapOf_lookup4)
  from tlookup_some have tlookup_some_inst:
  "sortedTree fst t & tlookup fst i t = Some (i,a) --> 
   (i,a) : setOf t & fst (i,a) = i"
  by (insert tlookup_some [of fst t i "(i,a)"], assumption)   
  from v o1 this show "(i,a) : setOf t" by simp
  -- {* <== *}
  next assume iain: "(i,a) : setOf t"
  from v iain tlookup_finds have "tlookup fst (fst (i,a)) t = Some (i,a)" by fastsimp
  from this have "tlookup fst i t = Some (i,a)" by simp
  from this show "mapOf t i = Some a" by (simp add: mapOf_def)
qed

(*============================================================*)
section {* Empty Map *}
(*============================================================*)

lemma mnew_spec_valid: "valid_tmap Tip"
by (simp add: mapOf_def)

lemma mtip_spec_empty: "mapOf Tip k = None"
by (simp add: mapOf_def)


(*============================================================*)
section {* Map Update Operation *}
(*============================================================*)

constdefs
  mupdate :: "index => 'a => 'a tarray => 'a tarray"
  "mupdate i a t == binsert fst (i,a) t"

lemma assumes v: "valid_tmap t"
      shows mupdate_map: "mapOf (mupdate i a t) = (mapOf t)(i |-> a)"
proof
  fix i2
  let ?tr = "binsert fst (i,a) t"
  have upres: "mupdate i a t = ?tr" by (simp add: mupdate_def)
  from v binsert_set 
  have setSpec: "setOf ?tr = setOf t - eqs fst (i,a) Un {(i,a)}" by fastsimp
  from v binsert_sorted have vr: "valid_tmap ?tr" by fastsimp
  show "mapOf (mupdate i a t) i2 = ((mapOf t)(i |-> a)) i2"
  proof (cases "i = i2")
  case True note i2ei = this
    from i2ei have rhs_res: "((mapOf t)(i |-> a)) i2 = Some a" by simp
    have lhs_res: "mapOf (mupdate i a t) i = Some a"
    proof -
      have will_find: "tlookup fst i ?tr = Some (i,a)"
      proof -
        from setSpec have kvin: "(i,a) : setOf ?tr" by simp
        have binsert_sorted_inst: "sortedTree fst t --> 
                                 sortedTree fst ?tr"
        by (insert binsert_sorted [of "fst" "t" "(i,a)"], assumption)
        from v binsert_sorted_inst have rs: "sortedTree fst ?tr" by simp
        have tlookup_finds_inst: "sortedTree fst ?tr & (i,a) : setOf ?tr --> 
                                  tlookup fst i ?tr = Some (i,a)"
        by (insert tlookup_finds [of "fst" "?tr" "(i,a)"], simp)
        from rs kvin tlookup_finds_inst show ?thesis by simp
      qed
      from upres will_find show ?thesis by (simp add: mapOf_def)
    qed
    from lhs_res rhs_res i2ei show ?thesis by simp
  next case False note i2nei = this
    from i2nei have rhs_res: "((mapOf t)(i |-> a)) i2 = mapOf t i2" by auto
    have lhs_res: "mapOf (mupdate i a t) i2 = mapOf t i2"
    proof (cases "mapOf t i2")
    case None from this have mapNone: "mapOf t i2 = None" by simp
      from v mapNone mapset_none have i2nin: "ALL a. (i2,a) ~: setOf t" by fastsimp
      have noneIn: "ALL b. (i2,b) ~: setOf ?tr"
      proof 
        fix b 
        from v binsert_set 
        have "setOf ?tr = setOf t - eqs fst (i,a) Un {(i,a)}"
        by fastsimp
        from this i2nei i2nin show "(i2,b) ~: setOf ?tr" by fastsimp
      qed
      have mapset_none_inst: 
      "valid_tmap ?tr --> (mapOf ?tr i2 = None) = (ALL a. (i2, a) ~: setOf ?tr)" 
      by (insert mapset_none [of "?tr" i2], simp)
      from vr noneIn mapset_none_inst have "mapOf ?tr i2 = None" by fastsimp
      from this upres mapNone show ?thesis by simp
    next case (Some z) from this have mapSome: "mapOf t i2 = Some z" by simp
      from v mapSome mapset_some have "(i2,z) : setOf t" by fastsimp
      from this setSpec i2nei have "(i2,z) : setOf ?tr" by (simp add: eqs_def)
      from this vr mapset_some have "mapOf ?tr i2 = Some z" by fastsimp
      from this upres mapSome show ?thesis by simp
    qed
    from lhs_res rhs_res show ?thesis by simp
  qed
qed

lemma assumes v: "valid_tmap t"
      shows mupdate_valid: "valid_tmap (mupdate i a t)"
proof -
  let ?tr = "binsert fst (i,a) t"
  have upres: "mupdate i a t = ?tr" by (simp add: mupdate_def)
  from v binsert_sorted have vr: "valid_tmap ?tr" by fastsimp
  from vr upres show ?thesis by simp
qed

(*============================================================*)
section {* Map Remove Operation *}
(*============================================================*)

constdefs
  mremove :: "index => 'a tarray => 'a tarray"
  "mremove i t == remove fst (i, arbitrary) t"

lemma assumes v: "valid_tmap t"
      shows mremove_valid: "valid_tmap (mremove i t)"
proof (simp add: mremove_def)
  from v remove_sort 
  show "sortedTree fst (remove fst (i,arbitrary) t)" by fastsimp
qed

lemma assumes v: "valid_tmap t"
      shows mremove_map: "mapOf (mremove i t) i = None"
proof (simp add: mremove_def)
  let ?tr = "remove fst (i,arbitrary) t"
  show "mapOf ?tr i = None"
  proof -
    from v remove_spec 
    have remSet: "setOf ?tr = setOf t - eqs fst (i,arbitrary)"
    by fastsimp
    have noneIn: "ALL a. (i,a) ~: setOf ?tr"
    proof 
      fix a
      from remSet show "(i,a) ~: setOf ?tr" by (simp add: eqs_def)
    qed
    from v remove_sort have vr: "valid_tmap ?tr" by fastsimp
    have mapset_none_inst: "valid_tmap ?tr ==>
    (mapOf ?tr i = None) = (ALL a. (i,a) ~: setOf ?tr)"
    by (insert mapset_none [of "?tr" "i"], simp)
    from vr this have "(mapOf ?tr i = None) = (ALL a. (i,a) ~: setOf ?tr)" by fastsimp
    from this noneIn show "mapOf ?tr i = None" by simp    
  qed
qed

end
