(*  Title:      HOL/Induct/LList.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory

Shares NIL, CONS, List_case with List.thy

Still needs flatten function -- hard because it need
bounds on the amount of lookahead required.

Could try (but would it work for the gfp analogue of term?)
  LListD_Fun_def "LListD_Fun(A) == (%Z. diag({Numb(0)}) <++> diag(A) <**> Z)"

A nice but complex example would be [ML for the Working Programmer, page 176]
  from(1) = enumerate (Lmap (Lmap(pack), makeqq(from(1),from(1))))

Previous definition of llistD_Fun was explicit:
  llistD_Fun_def
   "llistD_Fun(r) ==    
       {(LNil,LNil)}  Un        
       (UN x. (split(%l1 l2.(LCons(x,l1),LCons(x,l2))))`r)"
*)

header {*Definition of type llist by a greatest fixed point*}

theory LList = Main + SList:

consts

  llist  :: "'a item set => 'a item set"
  LListD :: "('a item * 'a item)set => ('a item * 'a item)set"


coinductive "llist(A)"
  intros
    NIL_I:  "NIL \<in> llist(A)"
    CONS_I:         "[| a \<in> A;  M \<in> llist(A) |] ==> CONS a M \<in> llist(A)"

coinductive "LListD(r)"
  intros
    NIL_I:  "(NIL, NIL) \<in> LListD(r)"
    CONS_I:         "[| (a,b) \<in> r;  (M,N) \<in> LListD(r) |] 
                     ==> (CONS a M, CONS b N) \<in> LListD(r)"


typedef (LList)
  'a llist = "llist(range Leaf) :: 'a item set"
  by (blast intro: llist.NIL_I)

constdefs
  list_Fun   :: "['a item set, 'a item set] => 'a item set"
    --{*Now used exclusively for abbreviating the coinduction rule*}
     "list_Fun A X == {z. z = NIL | (\<exists>M a. z = CONS a M & a \<in> A & M \<in> X)}"

  LListD_Fun :: 
      "[('a item * 'a item)set, ('a item * 'a item)set] => 
       ('a item * 'a item)set"
    "LListD_Fun r X ==   
       {z. z = (NIL, NIL) |   
           (\<exists>M N a b. z = (CONS a M, CONS b N) & (a, b) \<in> r & (M, N) \<in> X)}"

  LNil :: "'a llist"
     --{*abstract constructor*}
    "LNil == Abs_LList NIL"

  LCons :: "['a, 'a llist] => 'a llist"
     --{*abstract constructor*}
    "LCons x xs == Abs_LList(CONS (Leaf x) (Rep_LList xs))"

  llist_case :: "['b, ['a, 'a llist]=>'b, 'a llist] => 'b"
    "llist_case c d l == 
       List_case c (%x y. d (inv Leaf x) (Abs_LList y)) (Rep_LList l)"

  LList_corec_fun :: "[nat, 'a=> ('b item * 'a) option, 'a] => 'b item"
    "LList_corec_fun k f == 
     nat_rec (%x. {})                         
             (%j r x. case f x of None    => NIL
                                | Some(z,w) => CONS z (r w)) 
             k"

  LList_corec     :: "['a, 'a => ('b item * 'a) option] => 'b item"
    "LList_corec a f == \<Union>k. LList_corec_fun k f a"

  llist_corec     :: "['a, 'a => ('b * 'a) option] => 'b llist"
    "llist_corec a f == 
       Abs_LList(LList_corec a 
                 (%z. case f z of None      => None
                                | Some(v,w) => Some(Leaf(v), w)))"

  llistD_Fun :: "('a llist * 'a llist)set => ('a llist * 'a llist)set"
    "llistD_Fun(r) ==    
        prod_fun Abs_LList Abs_LList `         
                LListD_Fun (diag(range Leaf))   
                            (prod_fun Rep_LList Rep_LList ` r)"



text{* The case syntax for type @{text "'a llist"} *}
translations
  "case p of LNil => a | LCons x l => b" == "llist_case a (%x l. b) p"


subsubsection{* Sample function definitions.  Item-based ones start with @{text L} *}

constdefs
  Lmap       :: "('a item => 'b item) => ('a item => 'b item)"
    "Lmap f M == LList_corec M (List_case None (%x M'. Some((f(x), M'))))"

  lmap       :: "('a=>'b) => ('a llist => 'b llist)"
    "lmap f l == llist_corec l (%z. case z of LNil => None 
                                           | LCons y z => Some(f(y), z))"

  iterates   :: "['a => 'a, 'a] => 'a llist"
    "iterates f a == llist_corec a (%x. Some((x, f(x))))"     

  Lconst     :: "'a item => 'a item"
    "Lconst(M) == lfp(%N. CONS M N)"

  Lappend    :: "['a item, 'a item] => 'a item"
   "Lappend M N == LList_corec (M,N)                                         
     (split(List_case (List_case None (%N1 N2. Some((N1, (NIL,N2))))) 
                      (%M1 M2 N. Some((M1, (M2,N))))))"

  lappend    :: "['a llist, 'a llist] => 'a llist"
    "lappend l n == llist_corec (l,n)                                         
       (split(llist_case (llist_case None (%n1 n2. Some((n1, (LNil,n2))))) 
                         (%l1 l2 n. Some((l1, (l2,n))))))"


text{*Append generates its result by applying f, where
    f((NIL,NIL))          = None
    f((NIL, CONS N1 N2))  = Some((N1, (NIL,N2))
    f((CONS M1 M2, N))    = Some((M1, (M2,N))
*}

text{*
SHOULD @{text LListD_Fun_CONS_I}, etc., be equations (for rewriting)?
*}

lemmas UN1_I = UNIV_I [THEN UN_I, standard]

subsubsection{* Simplification *}

declare option.split [split]

text{*This justifies using llist in other recursive type definitions*}
lemma llist_mono: "A<=B ==> llist(A) <= llist(B)"
apply (unfold llist.defs )
apply (rule gfp_mono)
apply (assumption | rule basic_monos)+
done


lemma llist_unfold: "llist(A) = usum {Numb(0)} (uprod A (llist A))"
  by (fast intro!: llist.intros [unfolded NIL_def CONS_def]
           elim: llist.cases [unfolded NIL_def CONS_def])


subsection{* Type checking by coinduction *}

text {*
  {\dots} using @{text list_Fun} THE COINDUCTIVE DEFINITION PACKAGE
  COULD DO THIS!
*}

lemma llist_coinduct: 
    "[| M \<in> X;  X <= list_Fun A (X Un llist(A)) |] ==>  M \<in> llist(A)"
apply (unfold list_Fun_def)
apply (erule llist.coinduct)
apply (erule subsetD [THEN CollectD], assumption)
done

lemma list_Fun_NIL_I [iff]: "NIL \<in> list_Fun A X"
by (unfold list_Fun_def NIL_def, fast)

lemma list_Fun_CONS_I [intro!,simp]: 
    "[| M \<in> A;  N \<in> X |] ==> CONS M N \<in> list_Fun A X"
apply (unfold list_Fun_def CONS_def, fast)
done


text{*Utilise the ``strong'' part, i.e. @{text "gfp(f)"}*}
lemma list_Fun_llist_I: "M \<in> llist(A) ==> M \<in> list_Fun A (X Un llist(A))"
apply (unfold llist.defs list_Fun_def)
apply (rule gfp_fun_UnI2) 
apply (rule monoI, blast) 
apply assumption
done

subsection{* @{text LList_corec} satisfies the desired recurion equation *}

text{*A continuity result?*}
lemma CONS_UN1: "CONS M (\<Union>x. f(x)) = (\<Union>x. CONS M (f x))"
apply (unfold CONS_def)
apply (simp add: In1_UN1 Scons_UN1_y)
done

lemma CONS_mono: "[| M<=M';  N<=N' |] ==> CONS M N <= CONS M' N'"
apply (unfold CONS_def)
apply (assumption | rule In1_mono Scons_mono)+
done

declare LList_corec_fun_def [THEN def_nat_rec_0, simp]
        LList_corec_fun_def [THEN def_nat_rec_Suc, simp]

subsubsection{* The directions of the equality are proved separately *}

lemma LList_corec_subset1: 
    "LList_corec a f <=  
     (case f a of None => NIL | Some(z,w) => CONS z (LList_corec w f))"
apply (unfold LList_corec_def)
apply (rule UN_least)
apply (case_tac "k")
apply (simp_all (no_asm_simp))
apply (rule allI impI subset_refl [THEN CONS_mono] UNIV_I [THEN UN_upper])+
done

lemma LList_corec_subset2: 
    "(case f a of None => NIL | Some(z,w) => CONS z (LList_corec w f)) <=  
     LList_corec a f"
apply (unfold LList_corec_def)
apply (simp add: CONS_UN1, safe) 
apply (rule_tac a="Suc(?k)" in UN_I, simp, simp)+ 
done

text{*the recursion equation for @{text LList_corec} -- NOT SUITABLE FOR REWRITING!*}
lemma LList_corec:
     "LList_corec a f =   
      (case f a of None => NIL | Some(z,w) => CONS z (LList_corec w f))"
by (rule equalityI LList_corec_subset1 LList_corec_subset2)+

text{*definitional version of same*}
lemma def_LList_corec: 
     "[| !!x. h(x) == LList_corec x f |]      
      ==> h(a) = (case f a of None => NIL | Some(z,w) => CONS z (h w))"
by (simp add: LList_corec)

text{*A typical use of co-induction to show membership in the @{text gfp}. 
  Bisimulation is @{text "range(%x. LList_corec x f)"} *}
lemma LList_corec_type: "LList_corec a f \<in> llist UNIV"
apply (rule_tac X = "range (%x. LList_corec x ?g) " in llist_coinduct)
apply (rule rangeI, safe)
apply (subst LList_corec, simp)
done


subsection{* @{text llist} equality as a @{text gfp}; the bisimulation principle *}

text{*This theorem is actually used, unlike the many similar ones in ZF*}
lemma LListD_unfold: "LListD r = dsum (diag {Numb 0}) (dprod r (LListD r))"
  by (fast intro!: LListD.intros [unfolded NIL_def CONS_def]
           elim: LListD.cases [unfolded NIL_def CONS_def])

lemma LListD_implies_ntrunc_equality [rule_format]:
     "\<forall>M N. (M,N) \<in> LListD(diag A) --> ntrunc k M = ntrunc k N"
apply (induct_tac "k" rule: nat_less_induct)
apply (safe del: equalityI)
apply (erule LListD.cases)
apply (safe del: equalityI)
apply (case_tac "n", simp)
apply (rename_tac "n'")
apply (case_tac "n'")
apply (simp_all add: CONS_def less_Suc_eq)
done

text{*The domain of the @{text LListD} relation*}
lemma Domain_LListD: 
    "Domain (LListD(diag A)) <= llist(A)"
apply (unfold llist.defs NIL_def CONS_def)
apply (rule gfp_upperbound)
txt{*avoids unfolding @{text LListD} on the rhs*}
apply (rule_tac P = "%x. Domain x <= ?B" in LListD_unfold [THEN ssubst], simp)
apply blast 
done

text{*This inclusion justifies the use of coinduction to show @{text "M = N"}*}
lemma LListD_subset_diag: "LListD(diag A) <= diag(llist(A))"
apply (rule subsetI)
apply (rule_tac p = "x" in PairE, safe)
apply (rule diag_eqI)
apply (rule LListD_implies_ntrunc_equality [THEN ntrunc_equality], assumption)
apply (erule DomainI [THEN Domain_LListD [THEN subsetD]])
done


subsubsection{* Coinduction, using @{text LListD_Fun} *}

text {* THE COINDUCTIVE DEFINITION PACKAGE COULD DO THIS! *}

lemma LListD_Fun_mono: "A<=B ==> LListD_Fun r A <= LListD_Fun r B"
apply (unfold LListD_Fun_def)
apply (assumption | rule basic_monos)+
done

lemma LListD_coinduct: 
    "[| M \<in> X;  X <= LListD_Fun r (X Un LListD(r)) |] ==>  M \<in> LListD(r)"
apply (unfold LListD_Fun_def)
apply (erule LListD.coinduct)
apply (erule subsetD [THEN CollectD], assumption)
done

lemma LListD_Fun_NIL_I: "(NIL,NIL) \<in> LListD_Fun r s"
by (unfold LListD_Fun_def NIL_def, fast)

lemma LListD_Fun_CONS_I: 
     "[| x\<in>A;  (M,N):s |] ==> (CONS x M, CONS x N) \<in> LListD_Fun (diag A) s"
apply (unfold LListD_Fun_def CONS_def, blast)
done

text{*Utilise the "strong" part, i.e. @{text "gfp(f)"}*}
lemma LListD_Fun_LListD_I:
     "M \<in> LListD(r) ==> M \<in> LListD_Fun r (X Un LListD(r))"
apply (unfold LListD.defs LListD_Fun_def)
apply (rule gfp_fun_UnI2) 
apply (rule monoI, blast) 
apply assumption
done


text{*This converse inclusion helps to strengthen @{text LList_equalityI}*}
lemma diag_subset_LListD: "diag(llist(A)) <= LListD(diag A)"
apply (rule subsetI)
apply (erule LListD_coinduct)
apply (rule subsetI)
apply (erule diagE)
apply (erule ssubst)
apply (erule llist.cases)
apply (simp_all add: diagI LListD_Fun_NIL_I LListD_Fun_CONS_I)
done

lemma LListD_eq_diag: "LListD(diag A) = diag(llist(A))"
apply (rule equalityI LListD_subset_diag diag_subset_LListD)+
done

lemma LListD_Fun_diag_I: "M \<in> llist(A) ==> (M,M) \<in> LListD_Fun (diag A) (X Un diag(llist(A)))"
apply (rule LListD_eq_diag [THEN subst])
apply (rule LListD_Fun_LListD_I)
apply (simp add: LListD_eq_diag diagI)
done


subsubsection{* To show two LLists are equal, exhibit a bisimulation! 
      [also admits true equality]
   Replace @{text A} by some particular set, like @{text "{x. True}"}??? *}
lemma LList_equalityI:
     "[| (M,N) \<in> r;  r <= LListD_Fun (diag A) (r Un diag(llist(A))) |] 
      ==>  M=N"
apply (rule LListD_subset_diag [THEN subsetD, THEN diagE])
apply (erule LListD_coinduct)
apply (simp add: LListD_eq_diag, safe)
done


subsection{* Finality of @{text "llist(A)"}: Uniqueness of functions defined by corecursion *}

text{*We must remove @{text Pair_eq} because it may turn an instance of reflexivity
  @{text "(h1 b, h2 b) = (h1 ?x17, h2 ?x17)"} into a conjunction! 
  (or strengthen the Solver?) 
*}
declare Pair_eq [simp del]

text{*abstract proof using a bisimulation*}
lemma LList_corec_unique:
 "[| !!x. h1(x) = (case f x of None => NIL | Some(z,w) => CONS z (h1 w));   
     !!x. h2(x) = (case f x of None => NIL | Some(z,w) => CONS z (h2 w)) |] 
  ==> h1=h2"
apply (rule ext)
txt{*next step avoids an unknown (and flexflex pair) in simplification*}
apply (rule_tac A = "UNIV" and r = "range(%u. (h1 u, h2 u))" 
       in LList_equalityI)
apply (rule rangeI, safe)
apply (simp add: LListD_Fun_NIL_I UNIV_I [THEN LListD_Fun_CONS_I])
done

lemma equals_LList_corec:
 "[| !!x. h(x) = (case f x of None => NIL | Some(z,w) => CONS z (h w)) |]  
  ==> h = (%x. LList_corec x f)"
by (simp add: LList_corec_unique LList_corec) 


subsubsection{*Obsolete proof of @{text LList_corec_unique}: 
               complete induction, not coinduction *}

lemma ntrunc_one_CONS [simp]: "ntrunc (Suc 0) (CONS M N) = {}"
by (simp add: CONS_def ntrunc_one_In1)

lemma ntrunc_CONS [simp]: 
    "ntrunc (Suc(Suc(k))) (CONS M N) = CONS (ntrunc k M) (ntrunc k N)"
by (simp add: CONS_def)


lemma
 assumes prem1:
          "!!x. h1 x = (case f x of None => NIL | Some(z,w) => CONS z (h1 w))"
     and prem2:
          "!!x. h2 x = (case f x of None => NIL | Some(z,w) => CONS z (h2 w))"
 shows "h1=h2"
apply (rule ntrunc_equality [THEN ext])
apply (rule_tac x = "x" in spec)
apply (induct_tac "k" rule: nat_less_induct)
apply (rename_tac "n")
apply (rule allI)
apply (subst prem1)
apply (subst prem2, simp)
apply (intro strip) 
apply (case_tac "n") 
apply (rename_tac [2] "m")
apply (case_tac [2] "m")
apply simp_all
done


subsection{*Lconst: defined directly by @{text lfp} *}

text{*But it could be defined by corecursion.*}

lemma Lconst_fun_mono: "mono(CONS(M))"
apply (rule monoI subset_refl CONS_mono)+
apply assumption 
done

text{* @{text "Lconst(M) = CONS M (Lconst M)"} *}
lemmas Lconst = Lconst_fun_mono [THEN Lconst_def [THEN def_lfp_unfold]]

text{*A typical use of co-induction to show membership in the gfp.
  The containing set is simply the singleton @{text "{Lconst(M)}"}. *}
lemma Lconst_type: "M\<in>A ==> Lconst(M): llist(A)"
apply (rule singletonI [THEN llist_coinduct], safe)
apply (rule_tac P = "%u. u \<in> ?A" in Lconst [THEN ssubst])
apply (assumption | rule list_Fun_CONS_I singletonI UnI1)+
done

lemma Lconst_eq_LList_corec: "Lconst(M) = LList_corec M (%x. Some(x,x))"
apply (rule equals_LList_corec [THEN fun_cong], simp)
apply (rule Lconst)
done

text{*Thus we could have used gfp in the definition of Lconst*}
lemma gfp_Lconst_eq_LList_corec: "gfp(%N. CONS M N) = LList_corec M (%x. Some(x,x))"
apply (rule equals_LList_corec [THEN fun_cong], simp)
apply (rule Lconst_fun_mono [THEN gfp_unfold])
done


subsection{* Isomorphisms *}

lemma inj_Rep_LList: "inj Rep_LList"
apply (rule inj_on_inverseI)
apply (rule Rep_LList_inverse)
done


lemma LListI: "x \<in> llist (range Leaf) ==> x \<in> LList"
by (unfold LList_def, simp)

lemma LListD: "x \<in> LList ==> x \<in> llist (range Leaf)"
by (unfold LList_def, simp)


subsubsection{* Distinctness of constructors *}

lemma LCons_not_LNil [iff]: "~ LCons x xs = LNil"
apply (unfold LNil_def LCons_def)
apply (subst Abs_LList_inject)
apply (rule llist.intros CONS_not_NIL rangeI LListI Rep_LList [THEN LListD])+
done

lemmas LNil_not_LCons [iff] = LCons_not_LNil [THEN not_sym, standard]


subsubsection{* llist constructors *}

lemma Rep_LList_LNil: "Rep_LList LNil = NIL"
apply (unfold LNil_def)
apply (rule llist.NIL_I [THEN LListI, THEN Abs_LList_inverse])
done

lemma Rep_LList_LCons: "Rep_LList(LCons x l) = CONS (Leaf x) (Rep_LList l)"
apply (unfold LCons_def)
apply (rule llist.CONS_I [THEN LListI, THEN Abs_LList_inverse] 
            rangeI Rep_LList [THEN LListD])+
done

subsubsection{* Injectiveness of @{text CONS} and @{text LCons} *}

lemma CONS_CONS_eq2: "(CONS M N=CONS M' N') = (M=M' & N=N')"
apply (unfold CONS_def)
apply (fast elim!: Scons_inject)
done

lemmas CONS_inject = CONS_CONS_eq [THEN iffD1, THEN conjE, standard]


text{*For reasoning about abstract llist constructors*}

declare Rep_LList [THEN LListD, intro] LListI [intro]
declare llist.intros [intro]

lemma LCons_LCons_eq [iff]: "(LCons x xs=LCons y ys) = (x=y & xs=ys)"
apply (unfold LCons_def)
apply (subst Abs_LList_inject)
apply (auto simp add: Rep_LList_inject)
done

lemma CONS_D2: "CONS M N \<in> llist(A) ==> M \<in> A & N \<in> llist(A)"
apply (erule llist.cases)
apply (erule CONS_neq_NIL, fast)
done


subsection{* Reasoning about @{text "llist(A)"} *}

text{*A special case of @{text list_equality} for functions over lazy lists*}
lemma LList_fun_equalityI:
 "[| M \<in> llist(A); g(NIL): llist(A);                              
     f(NIL)=g(NIL);                                              
     !!x l. [| x\<in>A;  l \<in> llist(A) |] ==>                          
            (f(CONS x l),g(CONS x l)) \<in>                          
                LListD_Fun (diag A) ((%u.(f(u),g(u)))`llist(A) Un   
                                    diag(llist(A)))              
  |] ==> f(M) = g(M)"
apply (rule LList_equalityI)
apply (erule imageI)
apply (rule image_subsetI)
apply (erule_tac aa=x in llist.cases)
apply (erule ssubst, erule ssubst, erule LListD_Fun_diag_I, blast) 
done


subsection{* The functional @{text Lmap} *}

lemma Lmap_NIL [simp]: "Lmap f NIL = NIL"
by (rule Lmap_def [THEN def_LList_corec, THEN trans], simp)

lemma Lmap_CONS [simp]: "Lmap f (CONS M N) = CONS (f M) (Lmap f N)"
by (rule Lmap_def [THEN def_LList_corec, THEN trans], simp)



text{*Another type-checking proof by coinduction*}
lemma Lmap_type:
     "[| M \<in> llist(A);  !!x. x\<in>A ==> f(x):B |] ==> Lmap f M \<in> llist(B)"
apply (erule imageI [THEN llist_coinduct], safe)
apply (erule llist.cases, simp_all)
done

text{*This type checking rule synthesises a sufficiently large set for @{text f}*}
lemma Lmap_type2: "M \<in> llist(A) ==> Lmap f M \<in> llist(f`A)"
apply (erule Lmap_type)
apply (erule imageI)
done

subsubsection{* Two easy results about @{text Lmap} *}

lemma Lmap_compose: "M \<in> llist(A) ==> Lmap (f o g) M = Lmap f (Lmap g M)"
apply (unfold o_def)
apply (drule imageI)
apply (erule LList_equalityI, safe)
apply (erule llist.cases, simp_all)
apply (rule LListD_Fun_NIL_I imageI UnI1 rangeI [THEN LListD_Fun_CONS_I])+
apply assumption  
done

lemma Lmap_ident: "M \<in> llist(A) ==> Lmap (%x. x) M = M"
apply (drule imageI)
apply (erule LList_equalityI, safe)
apply (erule llist.cases, simp_all)
apply (rule LListD_Fun_NIL_I imageI UnI1 rangeI [THEN LListD_Fun_CONS_I])+
apply assumption 
done


subsection{* @{text Lappend} -- its two arguments cause some complications! *}

lemma Lappend_NIL_NIL [simp]: "Lappend NIL NIL = NIL"
apply (unfold Lappend_def)
apply (rule LList_corec [THEN trans], simp)
done

lemma Lappend_NIL_CONS [simp]: 
    "Lappend NIL (CONS N N') = CONS N (Lappend NIL N')"
apply (unfold Lappend_def)
apply (rule LList_corec [THEN trans], simp)
done

lemma Lappend_CONS [simp]: 
    "Lappend (CONS M M') N = CONS M (Lappend M' N)"
apply (unfold Lappend_def)
apply (rule LList_corec [THEN trans], simp)
done

declare llist.intros [simp] LListD_Fun_CONS_I [simp] 
        range_eqI [simp] image_eqI [simp]


lemma Lappend_NIL [simp]: "M \<in> llist(A) ==> Lappend NIL M = M"
by (erule LList_fun_equalityI, simp_all)

lemma Lappend_NIL2: "M \<in> llist(A) ==> Lappend M NIL = M"
by (erule LList_fun_equalityI, simp_all)


subsubsection{* Alternative type-checking proofs for @{text Lappend} *}

text{*weak co-induction: bisimulation and case analysis on both variables*}
lemma Lappend_type: "[| M \<in> llist(A); N \<in> llist(A) |] ==> Lappend M N \<in> llist(A)"
apply (rule_tac X = "\<Union>u\<in>llist (A) . \<Union>v \<in> llist (A) . {Lappend u v}" in llist_coinduct)
apply fast
apply safe
apply (erule_tac aa = "u" in llist.cases)
apply (erule_tac aa = "v" in llist.cases, simp_all)
apply blast
done

text{*strong co-induction: bisimulation and case analysis on one variable*}
lemma Lappend_type': "[| M \<in> llist(A); N \<in> llist(A) |] ==> Lappend M N \<in> llist(A)"
apply (rule_tac X = " (%u. Lappend u N) `llist (A) " in llist_coinduct)
apply (erule imageI)
apply (rule image_subsetI)
apply (erule_tac aa = "x" in llist.cases)
apply (simp add: list_Fun_llist_I, simp)
done

subsection{* Lazy lists as the type @{text "'a llist"} -- strongly typed versions of above *}

subsubsection{* @{text llist_case}: case analysis for @{text "'a llist"} *}

declare LListI [THEN Abs_LList_inverse, simp]
declare Rep_LList_inverse [simp]
declare Rep_LList [THEN LListD, simp]
declare rangeI [simp] inj_Leaf [simp] 

lemma llist_case_LNil [simp]: "llist_case c d LNil = c"
by (unfold llist_case_def LNil_def, simp)

lemma llist_case_LCons [simp]: 
    "llist_case c d (LCons M N) = d M N"
apply (unfold llist_case_def LCons_def, simp)
done

text{*Elimination is case analysis, not induction.*}
lemma llistE: "[| l=LNil ==> P;  !!x l'. l=LCons x l' ==> P |] ==> P"
apply (rule Rep_LList [THEN LListD, THEN llist.cases])
 apply (simp add: Rep_LList_LNil [symmetric] Rep_LList_inject)
 apply blast 
apply (erule LListI [THEN Rep_LList_cases], clarify)
apply (simp add: Rep_LList_LCons [symmetric] Rep_LList_inject, blast) 
done

subsubsection{* @{text llist_corec}: corecursion for @{text "'a llist"} *}

text{*Lemma for the proof of @{text llist_corec}*}
lemma LList_corec_type2:
     "LList_corec a  
           (%z. case f z of None => None | Some(v,w) => Some(Leaf(v),w)) 
       \<in> llist(range Leaf)"
apply (rule_tac X = "range (%x. LList_corec x ?g) " in llist_coinduct)
apply (rule rangeI, safe)
apply (subst LList_corec, force)
done

lemma llist_corec: 
    "llist_corec a f =   
     (case f a of None => LNil | Some(z,w) => LCons z (llist_corec w f))"
apply (unfold llist_corec_def LNil_def LCons_def)
apply (subst LList_corec)
apply (case_tac "f a")
apply (simp add: LList_corec_type2)
apply (force simp add: LList_corec_type2)
done

text{*definitional version of same*}
lemma def_llist_corec: 
     "[| !!x. h(x) == llist_corec x f |] ==>      
      h(a) = (case f a of None => LNil | Some(z,w) => LCons z (h w))"
by (simp add: llist_corec)

subsection{* Proofs about type @{text "'a llist"} functions *}

subsection{* Deriving @{text llist_equalityI} -- @{text llist} equality is a bisimulation *}

lemma LListD_Fun_subset_Times_llist: 
    "r <= (llist A) <*> (llist A) ==>  
            LListD_Fun (diag A) r <= (llist A) <*> (llist A)"
apply (unfold LListD_Fun_def)
apply (subst llist_unfold)
apply (simp add: NIL_def CONS_def, fast)
done

lemma subset_Times_llist:
     "prod_fun Rep_LList Rep_LList ` r <=  
     (llist(range Leaf)) <*> (llist(range Leaf))"
by (blast intro: Rep_LList [THEN LListD])

lemma prod_fun_lemma:
     "r <= (llist(range Leaf)) <*> (llist(range Leaf)) 
      ==> prod_fun (Rep_LList o Abs_LList) (Rep_LList o Abs_LList) ` r <= r"
apply safe
apply (erule subsetD [THEN SigmaE2], assumption)
apply (simp add: LListI [THEN Abs_LList_inverse])
done

lemma prod_fun_range_eq_diag:
     "prod_fun Rep_LList  Rep_LList ` range(%x. (x, x)) =  
      diag(llist(range Leaf))"
apply (rule equalityI, blast) 
apply (fast elim: LListI [THEN Abs_LList_inverse, THEN subst])
done

text{*Used with @{text lfilter}*}
lemma llistD_Fun_mono: 
    "A<=B ==> llistD_Fun A <= llistD_Fun B"
apply (unfold llistD_Fun_def prod_fun_def, auto)
apply (rule image_eqI)
 prefer 2 apply (blast intro: rev_subsetD [OF _ LListD_Fun_mono], force)
done

subsubsection{* To show two llists are equal, exhibit a bisimulation! 
      [also admits true equality] *}
lemma llist_equalityI: 
    "[| (l1,l2) \<in> r;  r <= llistD_Fun(r Un range(%x.(x,x))) |] ==> l1=l2"
apply (unfold llistD_Fun_def)
apply (rule Rep_LList_inject [THEN iffD1])
apply (rule_tac r = "prod_fun Rep_LList Rep_LList `r" and A = "range (Leaf) " in LList_equalityI)
apply (erule prod_fun_imageI)
apply (erule image_mono [THEN subset_trans])
apply (rule image_compose [THEN subst])
apply (rule prod_fun_compose [THEN subst])
apply (subst image_Un)
apply (subst prod_fun_range_eq_diag)
apply (rule LListD_Fun_subset_Times_llist [THEN prod_fun_lemma])
apply (rule subset_Times_llist [THEN Un_least])
apply (rule diag_subset_Times)
done

subsubsection{* Rules to prove the 2nd premise of @{text llist_equalityI} *}
lemma llistD_Fun_LNil_I [simp]: "(LNil,LNil) \<in> llistD_Fun(r)"
apply (unfold llistD_Fun_def LNil_def)
apply (rule LListD_Fun_NIL_I [THEN prod_fun_imageI])
done

lemma llistD_Fun_LCons_I [simp]: 
    "(l1,l2):r ==> (LCons x l1, LCons x l2) \<in> llistD_Fun(r)"
apply (unfold llistD_Fun_def LCons_def)
apply (rule rangeI [THEN LListD_Fun_CONS_I, THEN prod_fun_imageI])
apply (erule prod_fun_imageI)
done

text{*Utilise the "strong" part, i.e. @{text "gfp(f)"}*}
lemma llistD_Fun_range_I: "(l,l) \<in> llistD_Fun(r Un range(%x.(x,x)))"
apply (unfold llistD_Fun_def)
apply (rule Rep_LList_inverse [THEN subst])
apply (rule prod_fun_imageI)
apply (subst image_Un)
apply (subst prod_fun_range_eq_diag)
apply (rule Rep_LList [THEN LListD, THEN LListD_Fun_diag_I])
done

text{*A special case of @{text list_equality} for functions over lazy lists*}
lemma llist_fun_equalityI:
     "[| f(LNil)=g(LNil);                                                 
         !!x l. (f(LCons x l),g(LCons x l)) 
                \<in> llistD_Fun(range(%u. (f(u),g(u))) Un range(%v. (v,v)))    
      |] ==> f(l) = (g(l :: 'a llist) :: 'b llist)"
apply (rule_tac r = "range (%u. (f (u),g (u))) " in llist_equalityI)
apply (rule rangeI, clarify) 
apply (rule_tac l = "u" in llistE)
apply (simp_all add: llistD_Fun_range_I) 
done


subsection{* The functional @{text lmap} *}

lemma lmap_LNil [simp]: "lmap f LNil = LNil"
by (rule lmap_def [THEN def_llist_corec, THEN trans], simp)

lemma lmap_LCons [simp]: "lmap f (LCons M N) = LCons (f M) (lmap f N)"
by (rule lmap_def [THEN def_llist_corec, THEN trans], simp)


subsubsection{* Two easy results about @{text lmap} *}

lemma lmap_compose [simp]: "lmap (f o g) l = lmap f (lmap g l)"
by (rule_tac l = "l" in llist_fun_equalityI, simp_all)

lemma lmap_ident [simp]: "lmap (%x. x) l = l"
by (rule_tac l = "l" in llist_fun_equalityI, simp_all)


subsection{* iterates -- @{text llist_fun_equalityI} cannot be used! *}

lemma iterates: "iterates f x = LCons x (iterates f (f x))"
by (rule iterates_def [THEN def_llist_corec, THEN trans], simp)

lemma lmap_iterates [simp]: "lmap f (iterates f x) = iterates f (f x)"
apply (rule_tac r = "range (%u. (lmap f (iterates f u),iterates f (f u))) " in llist_equalityI)
apply (rule rangeI, safe)
apply (rule_tac x1 = "f (u) " in iterates [THEN ssubst])
apply (rule_tac x1 = "u" in iterates [THEN ssubst], simp)
done

lemma iterates_lmap: "iterates f x = LCons x (lmap f (iterates f x))"
apply (subst lmap_iterates)
apply (rule iterates)
done

subsection{* A rather complex proof about iterates -- cf Andy Pitts *}

subsubsection{* Two lemmas about @{text "natrec n x (%m. g)"}, which is essentially
  @{text "(g^n)(x)"} *}

lemma fun_power_lmap: "nat_rec (LCons b l) (%m. lmap(f)) n =       
     LCons (nat_rec b (%m. f) n) (nat_rec l (%m. lmap(f)) n)"
apply (induct_tac "n", simp_all)
done

lemma fun_power_Suc: "nat_rec (g x) (%m. g) n = nat_rec x (%m. g) (Suc n)"
by (induct_tac "n", simp_all)

lemmas Pair_cong = refl [THEN cong, THEN cong, of concl: Pair]


text{*The bisimulation consists of @{text "{(lmap(f)^n (h(u)), lmap(f)^n (iterates(f,u)))}"}
  for all @{text u} and all @{text "n::nat"}.*}
lemma iterates_equality:
     "(!!x. h(x) = LCons x (lmap f (h x))) ==> h = iterates(f)"
apply (rule ext)
apply (rule_tac 
       r = "\<Union>u. range (%n. (nat_rec (h u) (%m y. lmap f y) n, 
                             nat_rec (iterates f u) (%m y. lmap f y) n))" 
       in llist_equalityI)
apply (rule UN1_I range_eqI Pair_cong nat_rec_0 [symmetric])+
apply clarify
apply (subst iterates, atomize)
apply (drule_tac x=u in spec) 
apply (erule ssubst) 
apply (subst fun_power_lmap)
apply (subst fun_power_lmap)
apply (rule llistD_Fun_LCons_I)
apply (rule lmap_iterates [THEN subst])
apply (subst fun_power_Suc)
apply (subst fun_power_Suc, blast)
done


subsection{* @{text lappend} -- its two arguments cause some complications! *}

lemma lappend_LNil_LNil [simp]: "lappend LNil LNil = LNil"
apply (unfold lappend_def)
apply (rule llist_corec [THEN trans], simp)
done

lemma lappend_LNil_LCons [simp]: 
    "lappend LNil (LCons l l') = LCons l (lappend LNil l')"
apply (unfold lappend_def)
apply (rule llist_corec [THEN trans], simp)
done

lemma lappend_LCons [simp]: 
    "lappend (LCons l l') N = LCons l (lappend l' N)"
apply (unfold lappend_def)
apply (rule llist_corec [THEN trans], simp)
done

lemma lappend_LNil [simp]: "lappend LNil l = l"
by (rule_tac l = "l" in llist_fun_equalityI, simp_all)

lemma lappend_LNil2 [simp]: "lappend l LNil = l"
by (rule_tac l = "l" in llist_fun_equalityI, simp_all)


text{*The infinite first argument blocks the second*}
lemma lappend_iterates [simp]: "lappend (iterates f x) N = iterates f x"
apply (rule_tac r = "range (%u. (lappend (iterates f u) N,iterates f u))" 
       in llist_equalityI)
apply (rule rangeI, safe)
apply (subst iterates, simp)
done

subsubsection{* Two proofs that @{text lmap} distributes over lappend *}

text{*Long proof requiring case analysis on both both arguments*}
lemma lmap_lappend_distrib:
     "lmap f (lappend l n) = lappend (lmap f l) (lmap f n)"
apply (rule_tac r = "\<Union>n. range (%l. (lmap f (lappend l n),
                                      lappend (lmap f l) (lmap f n)))" 
       in llist_equalityI)
apply (rule UN1_I)
apply (rule rangeI, safe)
apply (rule_tac l = "l" in llistE)
apply (rule_tac l = "n" in llistE, simp_all)
apply (blast intro: llistD_Fun_LCons_I) 
done

text{*Shorter proof of theorem above using @{text llist_equalityI} as strong coinduction*}
lemma lmap_lappend_distrib':
     "lmap f (lappend l n) = lappend (lmap f l) (lmap f n)"
apply (rule_tac l = "l" in llist_fun_equalityI, simp)
apply simp
done

text{*Without strong coinduction, three case analyses might be needed*}
lemma lappend_assoc': "lappend (lappend l1 l2) l3 = lappend l1 (lappend l2 l3)"
apply (rule_tac l = "l1" in llist_fun_equalityI, simp)
apply simp
done

end
