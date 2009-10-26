(*  Title:      HOL/Library/Coinductive_Lists.thy
    Author:     Lawrence C Paulson and Makarius
*)

header {* Potentially infinite lists as greatest fixed-point *}

theory Coinductive_List
imports List Main
begin

subsection {* List constructors over the datatype universe *}

definition "NIL = Datatype.In0 (Datatype.Numb 0)"
definition "CONS M N = Datatype.In1 (Datatype.Scons M N)"

lemma CONS_not_NIL [iff]: "CONS M N \<noteq> NIL"
  and NIL_not_CONS [iff]: "NIL \<noteq> CONS M N"
  and CONS_inject [iff]: "(CONS K M) = (CONS L N) = (K = L \<and> M = N)"
  by (simp_all add: NIL_def CONS_def)

lemma CONS_mono: "M \<subseteq> M' \<Longrightarrow> N \<subseteq> N' \<Longrightarrow> CONS M N \<subseteq> CONS M' N'"
  by (simp add: CONS_def In1_mono Scons_mono)

lemma CONS_UN1: "CONS M (\<Union>x. f x) = (\<Union>x. CONS M (f x))"
    -- {* A continuity result? *}
  by (simp add: CONS_def In1_UN1 Scons_UN1_y)

definition "List_case c h = Datatype.Case (\<lambda>_. c) (Datatype.Split h)"

lemma List_case_NIL [simp]: "List_case c h NIL = c"
  and List_case_CONS [simp]: "List_case c h (CONS M N) = h M N"
  by (simp_all add: List_case_def NIL_def CONS_def)


subsection {* Corecursive lists *}

coinductive_set LList for A
where NIL [intro]:  "NIL \<in> LList A"
  | CONS [intro]: "a \<in> A \<Longrightarrow> M \<in> LList A \<Longrightarrow> CONS a M \<in> LList A"

lemma LList_mono:
  assumes subset: "A \<subseteq> B"
  shows "LList A \<subseteq> LList B"
    -- {* This justifies using @{text LList} in other recursive type definitions. *}
proof
  fix x
  assume "x \<in> LList A"
  then show "x \<in> LList B"
  proof coinduct
    case LList
    then show ?case using subset
      by cases blast+
  qed
qed

consts
  LList_corec_aux :: "nat \<Rightarrow> ('a \<Rightarrow> ('b Datatype.item \<times> 'a) option) \<Rightarrow>
    'a \<Rightarrow> 'b Datatype.item"
primrec
  "LList_corec_aux 0 f x = {}"
  "LList_corec_aux (Suc k) f x =
    (case f x of
      None \<Rightarrow> NIL
    | Some (z, w) \<Rightarrow> CONS z (LList_corec_aux k f w))"

definition "LList_corec a f = (\<Union>k. LList_corec_aux k f a)"

text {*
  Note: the subsequent recursion equation for @{text LList_corec} may
  be used with the Simplifier, provided it operates in a non-strict
  fashion for case expressions (i.e.\ the usual @{text case}
  congruence rule needs to be present).
*}

lemma LList_corec:
  "LList_corec a f =
    (case f a of None \<Rightarrow> NIL | Some (z, w) \<Rightarrow> CONS z (LList_corec w f))"
  (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    apply (unfold LList_corec_def)
    apply (rule UN_least)
    apply (case_tac k)
     apply (simp_all (no_asm_simp) split: option.splits)
    apply (rule allI impI subset_refl [THEN CONS_mono] UNIV_I [THEN UN_upper])+
    done
  show "?rhs \<subseteq> ?lhs"
    apply (simp add: LList_corec_def split: option.splits)
    apply (simp add: CONS_UN1)
    apply safe
     apply (rule_tac a = "Suc ?k" in UN_I, simp, simp)+
    done
qed

lemma LList_corec_type: "LList_corec a f \<in> LList UNIV"
proof -
  have "\<exists>x. LList_corec a f = LList_corec x f" by blast
  then show ?thesis
  proof coinduct
    case (LList L)
    then obtain x where L: "L = LList_corec x f" by blast
    show ?case
    proof (cases "f x")
      case None
      then have "LList_corec x f = NIL"
        by (simp add: LList_corec)
      with L have ?NIL by simp
      then show ?thesis ..
    next
      case (Some p)
      then have "LList_corec x f = CONS (fst p) (LList_corec (snd p) f)"
        by (simp add: LList_corec split: prod.split)
      with L have ?CONS by auto
      then show ?thesis ..
    qed
  qed
qed


subsection {* Abstract type definition *}

typedef 'a llist = "LList (range Datatype.Leaf) :: 'a Datatype.item set"
proof
  show "NIL \<in> ?llist" ..
qed

lemma NIL_type: "NIL \<in> llist"
  unfolding llist_def by (rule LList.NIL)

lemma CONS_type: "a \<in> range Datatype.Leaf \<Longrightarrow>
    M \<in> llist \<Longrightarrow> CONS a M \<in> llist"
  unfolding llist_def by (rule LList.CONS)

lemma llistI: "x \<in> LList (range Datatype.Leaf) \<Longrightarrow> x \<in> llist"
  by (simp add: llist_def)

lemma llistD: "x \<in> llist \<Longrightarrow> x \<in> LList (range Datatype.Leaf)"
  by (simp add: llist_def)

lemma Rep_llist_UNIV: "Rep_llist x \<in> LList UNIV"
proof -
  have "Rep_llist x \<in> llist" by (rule Rep_llist)
  then have "Rep_llist x \<in> LList (range Datatype.Leaf)"
    by (simp add: llist_def)
  also have "\<dots> \<subseteq> LList UNIV" by (rule LList_mono) simp
  finally show ?thesis .
qed

definition "LNil = Abs_llist NIL"
definition "LCons x xs = Abs_llist (CONS (Datatype.Leaf x) (Rep_llist xs))"

code_datatype LNil LCons

lemma LCons_not_LNil [iff]: "LCons x xs \<noteq> LNil"
  apply (simp add: LNil_def LCons_def)
  apply (subst Abs_llist_inject)
    apply (auto intro: NIL_type CONS_type Rep_llist)
  done

lemma LNil_not_LCons [iff]: "LNil \<noteq> LCons x xs"
  by (rule LCons_not_LNil [symmetric])

lemma LCons_inject [iff]: "(LCons x xs = LCons y ys) = (x = y \<and> xs = ys)"
  apply (simp add: LCons_def)
  apply (subst Abs_llist_inject)
    apply (auto simp add: Rep_llist_inject intro: CONS_type Rep_llist)
  done

lemma Rep_llist_LNil: "Rep_llist LNil = NIL"
  by (simp add: LNil_def add: Abs_llist_inverse NIL_type)

lemma Rep_llist_LCons: "Rep_llist (LCons x l) =
    CONS (Datatype.Leaf x) (Rep_llist l)"
  by (simp add: LCons_def Abs_llist_inverse CONS_type Rep_llist)

lemma llist_cases [cases type: llist]:
  obtains
    (LNil) "l = LNil"
  | (LCons) x l' where "l = LCons x l'"
proof (cases l)
  case (Abs_llist L)
  from `L \<in> llist` have "L \<in> LList (range Datatype.Leaf)" by (rule llistD)
  then show ?thesis
  proof cases
    case NIL
    with Abs_llist have "l = LNil" by (simp add: LNil_def)
    with LNil show ?thesis .
  next
    case (CONS a K)
    then have "K \<in> llist" by (blast intro: llistI)
    then obtain l' where "K = Rep_llist l'" by cases
    with CONS and Abs_llist obtain x where "l = LCons x l'"
      by (auto simp add: LCons_def Abs_llist_inject)
    with LCons show ?thesis .
  qed
qed


definition
  [code del]: "llist_case c d l =
    List_case c (\<lambda>x y. d (inv Datatype.Leaf x) (Abs_llist y)) (Rep_llist l)"


syntax  (* FIXME? *)
  LNil :: logic
  LCons :: logic
translations
  "case p of LNil \<Rightarrow> a | LCons x l \<Rightarrow> b" \<rightleftharpoons> "CONST llist_case a (\<lambda>x l. b) p"

lemma llist_case_LNil [simp, code]: "llist_case c d LNil = c"
  by (simp add: llist_case_def LNil_def
    NIL_type Abs_llist_inverse)

lemma llist_case_LCons [simp, code]: "llist_case c d (LCons M N) = d M N"
  by (simp add: llist_case_def LCons_def
    CONS_type Abs_llist_inverse Rep_llist Rep_llist_inverse inj_Leaf)

lemma llist_case_cert:
  assumes "CASE \<equiv> llist_case c d"
  shows "(CASE LNil \<equiv> c) &&& (CASE (LCons M N) \<equiv> d M N)"
  using assms by simp_all

setup {*
  Code.add_case @{thm llist_case_cert}
*}

definition
  [code del]: "llist_corec a f =
    Abs_llist (LList_corec a
      (\<lambda>z.
        case f z of None \<Rightarrow> None
        | Some (v, w) \<Rightarrow> Some (Datatype.Leaf v, w)))"

lemma LList_corec_type2:
  "LList_corec a
    (\<lambda>z. case f z of None \<Rightarrow> None
      | Some (v, w) \<Rightarrow> Some (Datatype.Leaf v, w)) \<in> llist"
  (is "?corec a \<in> _")
proof (unfold llist_def)
  let "LList_corec a ?g" = "?corec a"
  have "\<exists>x. ?corec a = ?corec x" by blast
  then show "?corec a \<in> LList (range Datatype.Leaf)"
  proof coinduct
    case (LList L)
    then obtain x where L: "L = ?corec x" by blast
    show ?case
    proof (cases "f x")
      case None
      then have "?corec x = NIL"
        by (simp add: LList_corec)
      with L have ?NIL by simp
      then show ?thesis ..
    next
      case (Some p)
      then have "?corec x =
          CONS (Datatype.Leaf (fst p)) (?corec (snd p))"
        by (simp add: LList_corec split: prod.split)
      with L have ?CONS by auto
      then show ?thesis ..
    qed
  qed
qed

lemma llist_corec [code, nitpick_simp]:
  "llist_corec a f =
    (case f a of None \<Rightarrow> LNil | Some (z, w) \<Rightarrow> LCons z (llist_corec w f))"
proof (cases "f a")
  case None
  then show ?thesis
    by (simp add: llist_corec_def LList_corec LNil_def)
next
  case (Some p)

  let "?corec a" = "llist_corec a f"
  let "?rep_corec a" =
    "LList_corec a
      (\<lambda>z. case f z of None \<Rightarrow> None
        | Some (v, w) \<Rightarrow> Some (Datatype.Leaf v, w))"

  have "?corec a = Abs_llist (?rep_corec a)"
    by (simp only: llist_corec_def)
  also from Some have "?rep_corec a =
      CONS (Datatype.Leaf (fst p)) (?rep_corec (snd p))"
    by (simp add: LList_corec split: prod.split)
  also have "?rep_corec (snd p) = Rep_llist (?corec (snd p))"
    by (simp only: llist_corec_def Abs_llist_inverse LList_corec_type2)
  finally have "?corec a = LCons (fst p) (?corec (snd p))"
    by (simp only: LCons_def)
  with Some show ?thesis by (simp split: prod.split)
qed


subsection {* Equality as greatest fixed-point -- the bisimulation principle *}

coinductive_set EqLList for r
where EqNIL: "(NIL, NIL) \<in> EqLList r"
  | EqCONS: "(a, b) \<in> r \<Longrightarrow> (M, N) \<in> EqLList r \<Longrightarrow>
      (CONS a M, CONS b N) \<in> EqLList r"

lemma EqLList_unfold:
    "EqLList r = dsum (Id_on {Datatype.Numb 0}) (dprod r (EqLList r))"
  by (fast intro!: EqLList.intros [unfolded NIL_def CONS_def]
           elim: EqLList.cases [unfolded NIL_def CONS_def])

lemma EqLList_implies_ntrunc_equality:
    "(M, N) \<in> EqLList (Id_on A) \<Longrightarrow> ntrunc k M = ntrunc k N"
  apply (induct k arbitrary: M N rule: nat_less_induct)
  apply (erule EqLList.cases)
   apply (safe del: equalityI)
  apply (case_tac n)
   apply simp
  apply (rename_tac n')
  apply (case_tac n')
   apply (simp_all add: CONS_def less_Suc_eq)
  done

lemma Domain_EqLList: "Domain (EqLList (Id_on A)) \<subseteq> LList A"
  apply (rule subsetI)
  apply (erule LList.coinduct)
  apply (subst (asm) EqLList_unfold)
  apply (auto simp add: NIL_def CONS_def)
  done

lemma EqLList_Id_on: "EqLList (Id_on A) = Id_on (LList A)"
  (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    apply (rule subsetI)
    apply (rule_tac p = x in PairE)
    apply clarify
    apply (rule Id_on_eqI)
     apply (rule EqLList_implies_ntrunc_equality [THEN ntrunc_equality],
       assumption)
    apply (erule DomainI [THEN Domain_EqLList [THEN subsetD]])
    done
  {
    fix M N assume "(M, N) \<in> Id_on (LList A)"
    then have "(M, N) \<in> EqLList (Id_on A)"
    proof coinduct
      case (EqLList M N)
      then obtain L where L: "L \<in> LList A" and MN: "M = L" "N = L" by blast
      from L show ?case
      proof cases
        case NIL with MN have ?EqNIL by simp
        then show ?thesis ..
      next
        case CONS with MN have ?EqCONS by (simp add: Id_onI)
        then show ?thesis ..
      qed
    qed
  }
  then show "?rhs \<subseteq> ?lhs" by auto
qed

lemma EqLList_Id_on_iff [iff]: "(p \<in> EqLList (Id_on A)) = (p \<in> Id_on (LList A))"
  by (simp only: EqLList_Id_on)


text {*
  To show two LLists are equal, exhibit a bisimulation!  (Also admits
  true equality.)
*}

lemma LList_equalityI
  [consumes 1, case_names EqLList, case_conclusion EqLList EqNIL EqCONS]:
  assumes r: "(M, N) \<in> r"
    and step: "\<And>M N. (M, N) \<in> r \<Longrightarrow>
      M = NIL \<and> N = NIL \<or>
        (\<exists>a b M' N'.
          M = CONS a M' \<and> N = CONS b N' \<and> (a, b) \<in> Id_on A \<and>
            ((M', N') \<in> r \<or> (M', N') \<in> EqLList (Id_on A)))"
  shows "M = N"
proof -
  from r have "(M, N) \<in> EqLList (Id_on A)"
  proof coinduct
    case EqLList
    then show ?case by (rule step)
  qed
  then show ?thesis by auto
qed

lemma LList_fun_equalityI
  [consumes 1, case_names NIL_type NIL CONS, case_conclusion CONS EqNIL EqCONS]:
  assumes M: "M \<in> LList A"
    and fun_NIL: "g NIL \<in> LList A"  "f NIL = g NIL"
    and fun_CONS: "\<And>x l. x \<in> A \<Longrightarrow> l \<in> LList A \<Longrightarrow>
            (f (CONS x l), g (CONS x l)) = (NIL, NIL) \<or>
            (\<exists>M N a b.
              (f (CONS x l), g (CONS x l)) = (CONS a M, CONS b N) \<and>
                (a, b) \<in> Id_on A \<and>
                (M, N) \<in> {(f u, g u) | u. u \<in> LList A} \<union> Id_on (LList A))"
      (is "\<And>x l. _ \<Longrightarrow> _ \<Longrightarrow> ?fun_CONS x l")
  shows "f M = g M"
proof -
  let ?bisim = "{(f L, g L) | L. L \<in> LList A}"
  have "(f M, g M) \<in> ?bisim" using M by blast
  then show ?thesis
  proof (coinduct taking: A rule: LList_equalityI)
    case (EqLList M N)
    then obtain L where MN: "M = f L" "N = g L" and L: "L \<in> LList A" by blast
    from L show ?case
    proof (cases L)
      case NIL
      with fun_NIL and MN have "(M, N) \<in> Id_on (LList A)" by auto
      then have "(M, N) \<in> EqLList (Id_on A)" ..
      then show ?thesis by cases simp_all
    next
      case (CONS a K)
      from fun_CONS and `a \<in> A` `K \<in> LList A`
      have "?fun_CONS a K" (is "?NIL \<or> ?CONS") .
      then show ?thesis
      proof
        assume ?NIL
        with MN CONS have "(M, N) \<in> Id_on (LList A)" by auto
        then have "(M, N) \<in> EqLList (Id_on A)" ..
        then show ?thesis by cases simp_all
      next
        assume ?CONS
        with CONS obtain a b M' N' where
            fg: "(f L, g L) = (CONS a M', CONS b N')"
          and ab: "(a, b) \<in> Id_on A"
          and M'N': "(M', N') \<in> ?bisim \<union> Id_on (LList A)"
          by blast
        from M'N' show ?thesis
        proof
          assume "(M', N') \<in> ?bisim"
          with MN fg ab show ?thesis by simp
        next
          assume "(M', N') \<in> Id_on (LList A)"
          then have "(M', N') \<in> EqLList (Id_on A)" ..
          with MN fg ab show ?thesis by simp
        qed
      qed
    qed
  qed
qed

text {*
  Finality of @{text "llist A"}: Uniqueness of functions defined by corecursion.
*}

lemma equals_LList_corec:
  assumes h: "\<And>x. h x =
    (case f x of None \<Rightarrow> NIL | Some (z, w) \<Rightarrow> CONS z (h w))"
  shows "h x = (\<lambda>x. LList_corec x f) x"
proof -
  def h' \<equiv> "\<lambda>x. LList_corec x f"
  then have h': "\<And>x. h' x =
      (case f x of None \<Rightarrow> NIL | Some (z, w) \<Rightarrow> CONS z (h' w))"
    unfolding h'_def by (simp add: LList_corec)
  have "(h x, h' x) \<in> {(h u, h' u) | u. True}" by blast
  then show "h x = h' x"
  proof (coinduct taking: UNIV rule: LList_equalityI)
    case (EqLList M N)
    then obtain x where MN: "M = h x" "N = h' x" by blast
    show ?case
    proof (cases "f x")
      case None
      with h h' MN have ?EqNIL by simp
      then show ?thesis ..
    next
      case (Some p)
      with h h' MN have "M = CONS (fst p) (h (snd p))"
        and "N = CONS (fst p) (h' (snd p))"
        by (simp_all split: prod.split)
      then have ?EqCONS by (auto iff: Id_on_iff)
      then show ?thesis ..
    qed
  qed
qed


lemma llist_equalityI
  [consumes 1, case_names Eqllist, case_conclusion Eqllist EqLNil EqLCons]:
  assumes r: "(l1, l2) \<in> r"
    and step: "\<And>q. q \<in> r \<Longrightarrow>
      q = (LNil, LNil) \<or>
        (\<exists>l1 l2 a b.
          q = (LCons a l1, LCons b l2) \<and> a = b \<and>
            ((l1, l2) \<in> r \<or> l1 = l2))"
      (is "\<And>q. _ \<Longrightarrow> ?EqLNil q \<or> ?EqLCons q")
  shows "l1 = l2"
proof -
  def M \<equiv> "Rep_llist l1" and N \<equiv> "Rep_llist l2"
  with r have "(M, N) \<in> {(Rep_llist l1, Rep_llist l2) | l1 l2. (l1, l2) \<in> r}"
    by blast
  then have "M = N"
  proof (coinduct taking: UNIV rule: LList_equalityI)
    case (EqLList M N)
    then obtain l1 l2 where
        MN: "M = Rep_llist l1" "N = Rep_llist l2" and r: "(l1, l2) \<in> r"
      by auto
    from step [OF r] show ?case
    proof
      assume "?EqLNil (l1, l2)"
      with MN have ?EqNIL by (simp add: Rep_llist_LNil)
      then show ?thesis ..
    next
      assume "?EqLCons (l1, l2)"
      with MN have ?EqCONS
        by (force simp add: Rep_llist_LCons EqLList_Id_on intro: Rep_llist_UNIV)
      then show ?thesis ..
    qed
  qed
  then show ?thesis by (simp add: M_def N_def Rep_llist_inject)
qed

lemma llist_fun_equalityI
  [case_names LNil LCons, case_conclusion LCons EqLNil EqLCons]:
  assumes fun_LNil: "f LNil = g LNil"
    and fun_LCons: "\<And>x l.
      (f (LCons x l), g (LCons x l)) = (LNil, LNil) \<or>
        (\<exists>l1 l2 a b.
          (f (LCons x l), g (LCons x l)) = (LCons a l1, LCons b l2) \<and>
            a = b \<and> ((l1, l2) \<in> {(f u, g u) | u. True} \<or> l1 = l2))"
      (is "\<And>x l. ?fun_LCons x l")
  shows "f l = g l"
proof -
  have "(f l, g l) \<in> {(f l, g l) | l. True}" by blast
  then show ?thesis
  proof (coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain l where q: "q = (f l, g l)" by blast
    show ?case
    proof (cases l)
      case LNil
      with fun_LNil and q have "q = (g LNil, g LNil)" by simp
      then show ?thesis by (cases "g LNil") simp_all
    next
      case (LCons x l')
      with `?fun_LCons x l'` q LCons show ?thesis by blast
    qed
  qed
qed


subsection {* Derived operations -- both on the set and abstract type *}

subsubsection {* @{text Lconst} *}

definition "Lconst M \<equiv> lfp (\<lambda>N. CONS M N)"

lemma Lconst_fun_mono: "mono (CONS M)"
  by (simp add: monoI CONS_mono)

lemma Lconst: "Lconst M = CONS M (Lconst M)"
  by (rule Lconst_def [THEN def_lfp_unfold]) (rule Lconst_fun_mono)

lemma Lconst_type:
  assumes "M \<in> A"
  shows "Lconst M \<in> LList A"
proof -
  have "Lconst M \<in> {Lconst (id M)}" by simp
  then show ?thesis
  proof coinduct
    case (LList N)
    then have "N = Lconst M" by simp
    also have "\<dots> = CONS M (Lconst M)" by (rule Lconst)
    finally have ?CONS using `M \<in> A` by simp
    then show ?case ..
  qed
qed

lemma Lconst_eq_LList_corec: "Lconst M = LList_corec M (\<lambda>x. Some (x, x))"
  apply (rule equals_LList_corec)
  apply simp
  apply (rule Lconst)
  done

lemma gfp_Lconst_eq_LList_corec:
    "gfp (\<lambda>N. CONS M N) = LList_corec M (\<lambda>x. Some(x, x))"
  apply (rule equals_LList_corec)
  apply simp
  apply (rule Lconst_fun_mono [THEN gfp_unfold])
  done


subsubsection {* @{text Lmap} and @{text lmap} *}

definition
  "Lmap f M = LList_corec M (List_case None (\<lambda>x M'. Some (f x, M')))"
definition
  "lmap f l = llist_corec l
    (\<lambda>z.
      case z of LNil \<Rightarrow> None
      | LCons y z \<Rightarrow> Some (f y, z))"

lemma Lmap_NIL [simp]: "Lmap f NIL = NIL"
  and Lmap_CONS [simp]: "Lmap f (CONS M N) = CONS (f M) (Lmap f N)"
  by (simp_all add: Lmap_def LList_corec)

lemma Lmap_type:
  assumes M: "M \<in> LList A"
    and f: "\<And>x. x \<in> A \<Longrightarrow> f x \<in> B"
  shows "Lmap f M \<in> LList B"
proof -
  from M have "Lmap f M \<in> {Lmap f N | N. N \<in> LList A}" by blast
  then show ?thesis
  proof coinduct
    case (LList L)
    then obtain N where L: "L = Lmap f N" and N: "N \<in> LList A" by blast
    from N show ?case
    proof cases
      case NIL
      with L have ?NIL by simp
      then show ?thesis ..
    next
      case (CONS K a)
      with f L have ?CONS by auto
      then show ?thesis ..
    qed
  qed
qed

lemma Lmap_compose:
  assumes M: "M \<in> LList A"
  shows "Lmap (f o g) M = Lmap f (Lmap g M)"  (is "?lhs M = ?rhs M")
proof -
  have "(?lhs M, ?rhs M) \<in> {(?lhs N, ?rhs N) | N. N \<in> LList A}"
    using M by blast
  then show ?thesis
  proof (coinduct taking: "range (\<lambda>N. N)" rule: LList_equalityI)
    case (EqLList L M)
    then obtain N where LM: "L = ?lhs N" "M = ?rhs N" and N: "N \<in> LList A" by blast
    from N show ?case
    proof cases
      case NIL
      with LM have ?EqNIL by simp
      then show ?thesis ..
    next
      case CONS
      with LM have ?EqCONS by auto
      then show ?thesis ..
    qed
  qed
qed

lemma Lmap_ident:
  assumes M: "M \<in> LList A"
  shows "Lmap (\<lambda>x. x) M = M"  (is "?lmap M = _")
proof -
  have "(?lmap M, M) \<in> {(?lmap N, N) | N. N \<in> LList A}" using M by blast
  then show ?thesis
  proof (coinduct taking: "range (\<lambda>N. N)" rule: LList_equalityI)
    case (EqLList L M)
    then obtain N where LM: "L = ?lmap N" "M = N" and N: "N \<in> LList A" by blast
    from N show ?case
    proof cases
      case NIL
      with LM have ?EqNIL by simp
      then show ?thesis ..
    next
      case CONS
      with LM have ?EqCONS by auto
      then show ?thesis ..
    qed
  qed
qed

lemma lmap_LNil [simp, nitpick_simp]: "lmap f LNil = LNil"
  and lmap_LCons [simp, nitpick_simp]:
  "lmap f (LCons M N) = LCons (f M) (lmap f N)"
  by (simp_all add: lmap_def llist_corec)

lemma lmap_compose [simp]: "lmap (f o g) l = lmap f (lmap g l)"
  by (coinduct l rule: llist_fun_equalityI) auto

lemma lmap_ident [simp]: "lmap (\<lambda>x. x) l = l"
  by (coinduct l rule: llist_fun_equalityI) auto



subsubsection {* @{text Lappend} *}

definition
  "Lappend M N = LList_corec (M, N)
    (split (List_case
        (List_case None (\<lambda>N1 N2. Some (N1, (NIL, N2))))
        (\<lambda>M1 M2 N. Some (M1, (M2, N)))))"
definition
  "lappend l n = llist_corec (l, n)
    (split (llist_case
        (llist_case None (\<lambda>n1 n2. Some (n1, (LNil, n2))))
        (\<lambda>l1 l2 n. Some (l1, (l2, n)))))"

lemma Lappend_NIL_NIL [simp]:
    "Lappend NIL NIL = NIL"
  and Lappend_NIL_CONS [simp]:
    "Lappend NIL (CONS N N') = CONS N (Lappend NIL N')"
  and Lappend_CONS [simp]:
    "Lappend (CONS M M') N = CONS M (Lappend M' N)"
  by (simp_all add: Lappend_def LList_corec)

lemma Lappend_NIL [simp]: "M \<in> LList A \<Longrightarrow> Lappend NIL M = M"
  by (erule LList_fun_equalityI) auto

lemma Lappend_NIL2: "M \<in> LList A \<Longrightarrow> Lappend M NIL = M"
  by (erule LList_fun_equalityI) auto

lemma Lappend_type:
  assumes M: "M \<in> LList A" and N: "N \<in> LList A"
  shows "Lappend M N \<in> LList A"
proof -
  have "Lappend M N \<in> {Lappend u v | u v. u \<in> LList A \<and> v \<in> LList A}"
    using M N by blast
  then show ?thesis
  proof coinduct
    case (LList L)
    then obtain M N where L: "L = Lappend M N"
        and M: "M \<in> LList A" and N: "N \<in> LList A"
      by blast
    from M show ?case
    proof cases
      case NIL
      from N show ?thesis
      proof cases
        case NIL
        with L and `M = NIL` have ?NIL by simp
        then show ?thesis ..
      next
        case CONS
        with L and `M = NIL` have ?CONS by simp
        then show ?thesis ..
      qed
    next
      case CONS
      with L N have ?CONS by auto
      then show ?thesis ..
    qed
  qed
qed

lemma lappend_LNil_LNil [simp, nitpick_simp]: "lappend LNil LNil = LNil"
  and lappend_LNil_LCons [simp, nitpick_simp]: "lappend LNil (LCons l l') = LCons l (lappend LNil l')"
  and lappend_LCons [simp, nitpick_simp]: "lappend (LCons l l') m = LCons l (lappend l' m)"
  by (simp_all add: lappend_def llist_corec)

lemma lappend_LNil1 [simp]: "lappend LNil l = l"
  by (coinduct l rule: llist_fun_equalityI) auto

lemma lappend_LNil2 [simp]: "lappend l LNil = l"
  by (coinduct l rule: llist_fun_equalityI) auto

lemma lappend_assoc: "lappend (lappend l1 l2) l3 = lappend l1 (lappend l2 l3)"
  by (coinduct l1 rule: llist_fun_equalityI) auto

lemma lmap_lappend_distrib: "lmap f (lappend l n) = lappend (lmap f l) (lmap f n)"
  by (coinduct l rule: llist_fun_equalityI) auto


subsection{* iterates *}

text {* @{text llist_fun_equalityI} cannot be used here! *}

definition
  iterates :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a llist" where
  "iterates f a = llist_corec a (\<lambda>x. Some (x, f x))"

lemma iterates [nitpick_simp]: "iterates f x = LCons x (iterates f (f x))"
  apply (unfold iterates_def)
  apply (subst llist_corec)
  apply simp
  done

lemma lmap_iterates: "lmap f (iterates f x) = iterates f (f x)"
proof -
  have "(lmap f (iterates f x), iterates f (f x)) \<in>
    {(lmap f (iterates f u), iterates f (f u)) | u. True}" by blast
  then show ?thesis
  proof (coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain x where q: "q = (lmap f (iterates f x), iterates f (f x))"
      by blast
    also have "iterates f (f x) = LCons (f x) (iterates f (f (f x)))"
      by (subst iterates) rule
    also have "iterates f x = LCons x (iterates f (f x))"
      by (subst iterates) rule
    finally have ?EqLCons by auto
    then show ?case ..
  qed
qed

lemma iterates_lmap: "iterates f x = LCons x (lmap f (iterates f x))"
  by (subst lmap_iterates) (rule iterates)


subsection{* A rather complex proof about iterates -- cf.\ Andy Pitts *}

lemma funpow_lmap:
  fixes f :: "'a \<Rightarrow> 'a"
  shows "(lmap f ^^ n) (LCons b l) = LCons ((f ^^ n) b) ((lmap f ^^ n) l)"
  by (induct n) simp_all


lemma iterates_equality:
  assumes h: "\<And>x. h x = LCons x (lmap f (h x))"
  shows "h = iterates f"
proof
  fix x
  have "(h x, iterates f x) \<in>
      {((lmap f ^^ n) (h u), (lmap f ^^ n) (iterates f u)) | u n. True}"
  proof -
    have "(h x, iterates f x) = ((lmap f ^^ 0) (h x), (lmap f ^^ 0) (iterates f x))"
      by simp
    then show ?thesis by blast
  qed
  then show "h x = iterates f x"
  proof (coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain u n where "q = ((lmap f ^^ n) (h u), (lmap f ^^ n) (iterates f u))"
        (is "_ = (?q1, ?q2)")
      by auto
    also have "?q1 = LCons ((f ^^ n) u) ((lmap f ^^ Suc n) (h u))"
    proof -
      have "?q1 = (lmap f ^^ n) (LCons u (lmap f (h u)))"
        by (subst h) rule
      also have "\<dots> = LCons ((f ^^ n) u) ((lmap f ^^ n) (lmap f (h u)))"
        by (rule funpow_lmap)
      also have "(lmap f ^^ n) (lmap f (h u)) = (lmap f ^^ Suc n) (h u)"
        by (simp add: funpow_swap1)
      finally show ?thesis .
    qed
    also have "?q2 = LCons ((f ^^ n) u) ((lmap f ^^ Suc n) (iterates f u))"
    proof -
      have "?q2 = (lmap f ^^ n) (LCons u (iterates f (f u)))"
        by (subst iterates) rule
      also have "\<dots> = LCons ((f ^^ n) u) ((lmap f ^^ n) (iterates f (f u)))"
        by (rule funpow_lmap)
      also have "(lmap f ^^ n) (iterates f (f u)) = (lmap f ^^ Suc n) (iterates f u)"
        by (simp add: lmap_iterates funpow_swap1)
      finally show ?thesis .
    qed
    finally have ?EqLCons by (auto simp del: funpow.simps)
    then show ?case ..
  qed
qed

lemma lappend_iterates: "lappend (iterates f x) l = iterates f x"
proof -
  have "(lappend (iterates f x) l, iterates f x) \<in>
    {(lappend (iterates f u) l, iterates f u) | u. True}" by blast
  then show ?thesis
  proof (coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain x where "q = (lappend (iterates f x) l, iterates f x)" by blast
    also have "iterates f x = LCons x (iterates f (f x))" by (rule iterates)
    finally have ?EqLCons by auto
    then show ?case ..
  qed
qed

setup {*
  Nitpick.register_codatatype @{typ "'a llist"} @{const_name llist_case}
    (map dest_Const [@{term LNil}, @{term LCons}])
*}

end
