(*  Title:      HOL/HOLCF/IOA/meta_theory/Seq.thy
    Author:     Olaf Müller
*)

header {* Partial, Finite and Infinite Sequences (lazy lists), modeled as domain *}

theory Seq
imports "../../HOLCF"
begin

default_sort pcpo

domain (unsafe) 'a seq = nil  ("nil") | cons (HD :: 'a) (lazy TL :: "'a seq")  (infixr "##" 65)

(*
   sfilter       :: "('a -> tr) -> 'a seq -> 'a seq"
   smap          :: "('a -> 'b) -> 'a seq -> 'b seq"
   sforall       :: "('a -> tr) => 'a seq => bool"
   sforall2      :: "('a -> tr) -> 'a seq -> tr"
   slast         :: "'a seq     -> 'a"
   sconc         :: "'a seq     -> 'a seq -> 'a seq"
   sdropwhile    :: "('a -> tr)  -> 'a seq -> 'a seq"
   stakewhile    :: "('a -> tr)  -> 'a seq -> 'a seq"
   szip          :: "'a seq      -> 'b seq -> ('a*'b) seq"
   sflat        :: "('a seq) seq  -> 'a seq"

   sfinite       :: "'a seq set"
   Partial       :: "'a seq => bool"
   Infinite      :: "'a seq => bool"

   nproj        :: "nat => 'a seq => 'a"
   sproj        :: "nat => 'a seq => 'a seq"
*)

inductive
  Finite :: "'a seq => bool"
  where
    sfinite_0:  "Finite nil"
  | sfinite_n:  "[| Finite tr; a~=UU |] ==> Finite (a##tr)"

declare Finite.intros [simp]

definition
  Partial :: "'a seq => bool"
where
  "Partial x  == (seq_finite x) & ~(Finite x)"

definition
  Infinite :: "'a seq => bool"
where
  "Infinite x == ~(seq_finite x)"


subsection {* recursive equations of operators *}

subsubsection {* smap *}

fixrec
  smap :: "('a -> 'b) -> 'a seq -> 'b seq"
where
  smap_nil: "smap$f$nil=nil"
| smap_cons: "[|x~=UU|] ==> smap$f$(x##xs)= (f$x)##smap$f$xs"

lemma smap_UU [simp]: "smap$f$UU=UU"
by fixrec_simp

subsubsection {* sfilter *}

fixrec
   sfilter :: "('a -> tr) -> 'a seq -> 'a seq"
where
  sfilter_nil: "sfilter$P$nil=nil"
| sfilter_cons:
    "x~=UU ==> sfilter$P$(x##xs)=
              (If P$x then x##(sfilter$P$xs) else sfilter$P$xs)"

lemma sfilter_UU [simp]: "sfilter$P$UU=UU"
by fixrec_simp

subsubsection {* sforall2 *}

fixrec
  sforall2 :: "('a -> tr) -> 'a seq -> tr"
where
  sforall2_nil: "sforall2$P$nil=TT"
| sforall2_cons:
    "x~=UU ==> sforall2$P$(x##xs)= ((P$x) andalso sforall2$P$xs)"

lemma sforall2_UU [simp]: "sforall2$P$UU=UU"
by fixrec_simp

definition
  sforall_def: "sforall P t == (sforall2$P$t ~=FF)"

subsubsection {* stakewhile *}

fixrec
  stakewhile :: "('a -> tr)  -> 'a seq -> 'a seq"
where
  stakewhile_nil: "stakewhile$P$nil=nil"
| stakewhile_cons:
    "x~=UU ==> stakewhile$P$(x##xs) =
              (If P$x then x##(stakewhile$P$xs) else nil)"

lemma stakewhile_UU [simp]: "stakewhile$P$UU=UU"
by fixrec_simp

subsubsection {* sdropwhile *}

fixrec
  sdropwhile :: "('a -> tr) -> 'a seq -> 'a seq"
where
  sdropwhile_nil: "sdropwhile$P$nil=nil"
| sdropwhile_cons:
    "x~=UU ==> sdropwhile$P$(x##xs) =
              (If P$x then sdropwhile$P$xs else x##xs)"

lemma sdropwhile_UU [simp]: "sdropwhile$P$UU=UU"
by fixrec_simp

subsubsection {* slast *}

fixrec
  slast :: "'a seq -> 'a"
where
  slast_nil: "slast$nil=UU"
| slast_cons:
    "x~=UU ==> slast$(x##xs)= (If is_nil$xs then x else slast$xs)"

lemma slast_UU [simp]: "slast$UU=UU"
by fixrec_simp

subsubsection {* sconc *}

fixrec
  sconc :: "'a seq -> 'a seq -> 'a seq"
where
  sconc_nil: "sconc$nil$y = y"
| sconc_cons':
    "x~=UU ==> sconc$(x##xs)$y = x##(sconc$xs$y)"

abbreviation
  sconc_syn :: "'a seq => 'a seq => 'a seq"  (infixr "@@" 65) where
  "xs @@ ys == sconc $ xs $ ys"

lemma sconc_UU [simp]: "UU @@ y=UU"
by fixrec_simp

lemma sconc_cons [simp]: "(x##xs) @@ y=x##(xs @@ y)"
apply (cases "x=UU")
apply simp_all
done

declare sconc_cons' [simp del]

subsubsection {* sflat *}

fixrec
  sflat :: "('a seq) seq -> 'a seq"
where
  sflat_nil: "sflat$nil=nil"
| sflat_cons': "x~=UU ==> sflat$(x##xs)= x@@(sflat$xs)"

lemma sflat_UU [simp]: "sflat$UU=UU"
by fixrec_simp

lemma sflat_cons [simp]: "sflat$(x##xs)= x@@(sflat$xs)"
by (cases "x=UU", simp_all)

declare sflat_cons' [simp del]

subsubsection {* szip *}

fixrec
  szip :: "'a seq -> 'b seq -> ('a*'b) seq"
where
  szip_nil: "szip$nil$y=nil"
| szip_cons_nil: "x~=UU ==> szip$(x##xs)$nil=UU"
| szip_cons:
    "[| x~=UU; y~=UU|] ==> szip$(x##xs)$(y##ys) = (x,y)##szip$xs$ys"

lemma szip_UU1 [simp]: "szip$UU$y=UU"
by fixrec_simp

lemma szip_UU2 [simp]: "x~=nil ==> szip$x$UU=UU"
by (cases x, simp_all, fixrec_simp)


subsection "scons, nil"

lemma scons_inject_eq:
 "[|x~=UU;y~=UU|]==> (x##xs=y##ys) = (x=y & xs=ys)"
by simp

lemma nil_less_is_nil: "nil<<x ==> nil=x"
apply (cases x)
apply simp
apply simp
apply simp
done

subsection "sfilter, sforall, sconc"

lemma if_and_sconc [simp]: "(if b then tr1 else tr2) @@ tr
        = (if b then tr1 @@ tr else tr2 @@ tr)"
by simp


lemma sfiltersconc: "sfilter$P$(x @@ y) = (sfilter$P$x @@ sfilter$P$y)"
apply (induct x)
(* adm *)
apply simp
(* base cases *)
apply simp
apply simp
(* main case *)
apply (rule_tac p="P$a" in trE)
apply simp
apply simp
apply simp
done

lemma sforallPstakewhileP: "sforall P (stakewhile$P$x)"
apply (simp add: sforall_def)
apply (induct x)
(* adm *)
apply simp
(* base cases *)
apply simp
apply simp
(* main case *)
apply (rule_tac p="P$a" in trE)
apply simp
apply simp
apply simp
done

lemma forallPsfilterP: "sforall P (sfilter$P$x)"
apply (simp add: sforall_def)
apply (induct x)
(* adm *)
apply simp
(* base cases *)
apply simp
apply simp
(* main case *)
apply (rule_tac p="P$a" in trE)
apply simp
apply simp
apply simp
done


subsection "Finite"

(* ----------------------------------------------------  *)
(* Proofs of rewrite rules for Finite:                  *)
(* 1. Finite(nil),   (by definition)                    *)
(* 2. ~Finite(UU),                                      *)
(* 3. a~=UU==> Finite(a##x)=Finite(x)                  *)
(* ----------------------------------------------------  *)

lemma Finite_UU_a: "Finite x --> x~=UU"
apply (rule impI)
apply (erule Finite.induct)
 apply simp
apply simp
done

lemma Finite_UU [simp]: "~(Finite UU)"
apply (cut_tac x="UU" in Finite_UU_a)
apply fast
done

lemma Finite_cons_a: "Finite x --> a~=UU --> x=a##xs --> Finite xs"
apply (intro strip)
apply (erule Finite.cases)
apply fastforce
apply simp
done

lemma Finite_cons: "a~=UU ==>(Finite (a##x)) = (Finite x)"
apply (rule iffI)
apply (erule (1) Finite_cons_a [rule_format])
apply fast
apply simp
done

lemma Finite_upward: "\<lbrakk>Finite x; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> Finite y"
apply (induct arbitrary: y set: Finite)
apply (case_tac y, simp, simp, simp)
apply (case_tac y, simp, simp)
apply simp
done

lemma adm_Finite [simp]: "adm Finite"
by (rule adm_upward, rule Finite_upward)


subsection "induction"


(*--------------------------------   *)
(* Extensions to Induction Theorems  *)
(*--------------------------------   *)


lemma seq_finite_ind_lemma:
  assumes "(!!n. P(seq_take n$s))"
  shows "seq_finite(s) -->P(s)"
apply (unfold seq.finite_def)
apply (intro strip)
apply (erule exE)
apply (erule subst)
apply (rule assms)
done


lemma seq_finite_ind: "!!P.[|P(UU);P(nil);
   !! x s1.[|x~=UU;P(s1)|] ==> P(x##s1)
   |] ==> seq_finite(s) --> P(s)"
apply (rule seq_finite_ind_lemma)
apply (erule seq.finite_induct)
 apply assumption
apply simp
done

end
