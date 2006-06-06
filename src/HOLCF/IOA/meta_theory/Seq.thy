(*  Title:      HOLCF/IOA/meta_theory/Seq.thy
    ID:         $Id$
    Author:     Olaf Müller
*)

header {* Partial, Finite and Infinite Sequences (lazy lists), modeled as domain *}

theory Seq
imports HOLCF
begin

domain 'a seq = nil | "##" (HD :: 'a) (lazy TL :: "'a seq")  (infixr 65)

consts
   sfilter       :: "('a -> tr) -> 'a seq -> 'a seq"
   smap          :: "('a -> 'b) -> 'a seq -> 'b seq"
   sforall       :: "('a -> tr) => 'a seq => bool"
   sforall2      :: "('a -> tr) -> 'a seq -> tr"
   slast         :: "'a seq     -> 'a"
   sconc         :: "'a seq     -> 'a seq -> 'a seq"
   sdropwhile    ::"('a -> tr)  -> 'a seq -> 'a seq"
   stakewhile    ::"('a -> tr)  -> 'a seq -> 'a seq"
   szip          ::"'a seq      -> 'b seq -> ('a*'b) seq"
   sflat        :: "('a seq) seq  -> 'a seq"

   sfinite       :: "'a seq set"
   Partial       ::"'a seq => bool"
   Infinite      ::"'a seq => bool"

   nproj        :: "nat => 'a seq => 'a"
   sproj        :: "nat => 'a seq => 'a seq"

syntax
   "@@"         :: "'a seq => 'a seq => 'a seq" (infixr 65)
   "Finite"     :: "'a seq => bool"

translations
   "xs @@ ys" == "sconc $ xs $ ys"
   "Finite x" == "x:sfinite"
   "~(Finite x)" =="x~:sfinite"

defs

(* f not possible at lhs, as "pattern matching" only for % x arguments,
   f cannot be written at rhs in front, as fix_eq3 does not apply later *)
smap_def:
  "smap == (fix$(LAM h f tr. case tr of
      nil   => nil
    | x##xs => f$x ## h$f$xs))"

sfilter_def:
  "sfilter == (fix$(LAM h P t. case t of
           nil => nil
         | x##xs => If P$x
                    then x##(h$P$xs)
                    else     h$P$xs
                    fi))"
sforall_def:
  "sforall P t == (sforall2$P$t ~=FF)"


sforall2_def:
  "sforall2 == (fix$(LAM h P t. case t of
           nil => TT
         | x##xs => P$x andalso h$P$xs))"

sconc_def:
  "sconc == (fix$(LAM h t1 t2. case t1 of
               nil       => t2
             | x##xs => x##(h$xs$t2)))"

slast_def:
  "slast == (fix$(LAM h t. case t of
           nil => UU
         | x##xs => (If is_nil$xs
                          then x
                         else h$xs fi)))"

stakewhile_def:
  "stakewhile == (fix$(LAM h P t. case t of
           nil => nil
         | x##xs => If P$x
                    then x##(h$P$xs)
                    else nil
                    fi))"
sdropwhile_def:
  "sdropwhile == (fix$(LAM h P t. case t of
           nil => nil
         | x##xs => If P$x
                    then h$P$xs
                    else t
                    fi))"
sflat_def:
  "sflat == (fix$(LAM h t. case t of
           nil => nil
         | x##xs => x @@ (h$xs)))"

szip_def:
  "szip == (fix$(LAM h t1 t2. case t1 of
               nil   => nil
             | x##xs => (case t2 of
                          nil => UU
                        | y##ys => <x,y>##(h$xs$ys))))"

Partial_def:
  "Partial x  == (seq_finite x) & ~(Finite x)"

Infinite_def:
  "Infinite x == ~(seq_finite x)"


inductive "sfinite"
   intros
    sfinite_0:  "nil:sfinite"
    sfinite_n:  "[|tr:sfinite;a~=UU|] ==> (a##tr) : sfinite"

declare sfinite.intros [simp]
declare seq.rews [simp]


subsection {* recursive equations of operators *}

subsubsection {* smap *}

lemma smap_unfold:
  "smap = (LAM f tr. case tr of nil  => nil | x##xs => f$x ## smap$f$xs)"
by (subst fix_eq2 [OF smap_def], simp)

lemma smap_nil [simp]: "smap$f$nil=nil"
by (subst smap_unfold, simp)

lemma smap_UU [simp]: "smap$f$UU=UU"
by (subst smap_unfold, simp)

lemma smap_cons [simp]: "[|x~=UU|] ==> smap$f$(x##xs)= (f$x)##smap$f$xs"
apply (rule trans)
apply (subst smap_unfold)
apply simp
apply (rule refl)
done

subsubsection {* sfilter *}

lemma sfilter_unfold:
  "sfilter = (LAM P tr. case tr of
           nil   => nil
         | x##xs => If P$x then x##(sfilter$P$xs) else sfilter$P$xs fi)"
by (subst fix_eq2 [OF sfilter_def], simp)

lemma sfilter_nil [simp]: "sfilter$P$nil=nil"
by (subst sfilter_unfold, simp)

lemma sfilter_UU [simp]: "sfilter$P$UU=UU"
by (subst sfilter_unfold, simp)

lemma sfilter_cons [simp]:
"x~=UU ==> sfilter$P$(x##xs)=
              (If P$x then x##(sfilter$P$xs) else sfilter$P$xs fi)"
apply (rule trans)
apply (subst sfilter_unfold)
apply simp
apply (rule refl)
done

subsubsection {* sforall2 *}

lemma sforall2_unfold:
   "sforall2 = (LAM P tr. case tr of
                           nil   => TT
                         | x##xs => (P$x andalso sforall2$P$xs))"
by (subst fix_eq2 [OF sforall2_def], simp)

lemma sforall2_nil [simp]: "sforall2$P$nil=TT"
by (subst sforall2_unfold, simp)

lemma sforall2_UU [simp]: "sforall2$P$UU=UU"
by (subst sforall2_unfold, simp)

lemma sforall2_cons [simp]:
"x~=UU ==> sforall2$P$(x##xs)= ((P$x) andalso sforall2$P$xs)"
apply (rule trans)
apply (subst sforall2_unfold)
apply simp
apply (rule refl)
done


subsubsection {* stakewhile *}

lemma stakewhile_unfold:
  "stakewhile = (LAM P tr. case tr of
     nil   => nil
   | x##xs => (If P$x then x##(stakewhile$P$xs) else nil fi))"
by (subst fix_eq2 [OF stakewhile_def], simp)

lemma stakewhile_nil [simp]: "stakewhile$P$nil=nil"
apply (subst stakewhile_unfold)
apply simp
done

lemma stakewhile_UU [simp]: "stakewhile$P$UU=UU"
apply (subst stakewhile_unfold)
apply simp
done

lemma stakewhile_cons [simp]:
"x~=UU ==> stakewhile$P$(x##xs) =
              (If P$x then x##(stakewhile$P$xs) else nil fi)"
apply (rule trans)
apply (subst stakewhile_unfold)
apply simp
apply (rule refl)
done

subsubsection {* sdropwhile *}

lemma sdropwhile_unfold:
   "sdropwhile = (LAM P tr. case tr of
                           nil   => nil
                         | x##xs => (If P$x then sdropwhile$P$xs else tr fi))"
by (subst fix_eq2 [OF sdropwhile_def], simp)

lemma sdropwhile_nil [simp]: "sdropwhile$P$nil=nil"
apply (subst sdropwhile_unfold)
apply simp
done

lemma sdropwhile_UU [simp]: "sdropwhile$P$UU=UU"
apply (subst sdropwhile_unfold)
apply simp
done

lemma sdropwhile_cons [simp]:
"x~=UU ==> sdropwhile$P$(x##xs) =
              (If P$x then sdropwhile$P$xs else x##xs fi)"
apply (rule trans)
apply (subst sdropwhile_unfold)
apply simp
apply (rule refl)
done


subsubsection {* slast *}

lemma slast_unfold:
   "slast = (LAM tr. case tr of
                           nil   => UU
                         | x##xs => (If is_nil$xs then x else slast$xs fi))"
by (subst fix_eq2 [OF slast_def], simp)

lemma slast_nil [simp]: "slast$nil=UU"
apply (subst slast_unfold)
apply simp
done

lemma slast_UU [simp]: "slast$UU=UU"
apply (subst slast_unfold)
apply simp
done

lemma slast_cons [simp]:
"x~=UU ==> slast$(x##xs)= (If is_nil$xs then x else slast$xs fi)"
apply (rule trans)
apply (subst slast_unfold)
apply simp
apply (rule refl)
done


subsubsection {* sconc *}

lemma sconc_unfold:
   "sconc = (LAM t1 t2. case t1 of
                           nil   => t2
                         | x##xs => x ## (xs @@ t2))"
by (subst fix_eq2 [OF sconc_def], simp)

lemma sconc_nil [simp]: "nil @@ y = y"
apply (subst sconc_unfold)
apply simp
done

lemma sconc_UU [simp]: "UU @@ y=UU"
apply (subst sconc_unfold)
apply simp
done

lemma sconc_cons [simp]: "(x##xs) @@ y=x##(xs @@ y)"
apply (rule trans)
apply (subst sconc_unfold)
apply simp
apply (case_tac "x=UU")
apply simp_all
done


subsubsection {* sflat *}

lemma sflat_unfold:
   "sflat = (LAM tr. case tr of
                           nil   => nil
                         | x##xs => x @@ sflat$xs)"
by (subst fix_eq2 [OF sflat_def], simp)

lemma sflat_nil [simp]: "sflat$nil=nil"
apply (subst sflat_unfold)
apply simp
done

lemma sflat_UU [simp]: "sflat$UU=UU"
apply (subst sflat_unfold)
apply simp
done

lemma sflat_cons [simp]: "sflat$(x##xs)= x@@(sflat$xs)"
apply (rule trans)
apply (subst sflat_unfold)
apply simp
apply (case_tac "x=UU")
apply simp_all
done


subsubsection {* szip *}

lemma szip_unfold:
   "szip = (LAM t1 t2. case t1 of
                nil   => nil
              | x##xs => (case t2 of
                           nil => UU
                         | y##ys => <x,y>##(szip$xs$ys)))"
by (subst fix_eq2 [OF szip_def], simp)

lemma szip_nil [simp]: "szip$nil$y=nil"
apply (subst szip_unfold)
apply simp
done

lemma szip_UU1 [simp]: "szip$UU$y=UU"
apply (subst szip_unfold)
apply simp
done

lemma szip_UU2 [simp]: "x~=nil ==> szip$x$UU=UU"
apply (subst szip_unfold)
apply simp
apply (rule_tac x="x" in seq.casedist)
apply simp_all
done

lemma szip_cons_nil [simp]: "x~=UU ==> szip$(x##xs)$nil=UU"
apply (rule trans)
apply (subst szip_unfold)
apply simp_all
done

lemma szip_cons [simp]:
"[| x~=UU; y~=UU|] ==> szip$(x##xs)$(y##ys) = <x,y>##szip$xs$ys"
apply (rule trans)
apply (subst szip_unfold)
apply simp_all
done


subsection "scons, nil"

lemma scons_inject_eq:
 "[|x~=UU;y~=UU|]==> (x##xs=y##ys) = (x=y & xs=ys)"
by (simp add: seq.injects)

lemma nil_less_is_nil: "nil<<x ==> nil=x"
apply (rule_tac x="x" in seq.casedist)
apply simp
apply simp
apply simp
done

subsection "sfilter, sforall, sconc"

lemma if_and_sconc [simp]: "(if b then tr1 else tr2) @@ tr
        = (if b then tr1 @@ tr else tr2 @@ tr)"
by simp


lemma sfiltersconc: "sfilter$P$(x @@ y) = (sfilter$P$x @@ sfilter$P$y)"
apply (rule_tac x="x" in seq.ind)
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
apply (rule_tac x="x" in seq.ind)
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
apply (rule_tac x="x" in seq.ind)
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
apply (erule sfinite.induct)
 apply simp
apply simp
done

lemma Finite_UU [simp]: "~(Finite UU)"
apply (cut_tac x="UU" in Finite_UU_a)
apply fast
done

lemma Finite_cons_a: "Finite x --> a~=UU --> x=a##xs --> Finite xs"
apply (intro strip)
apply (erule sfinite.elims)
apply fastsimp
apply (simp add: seq.injects)
done

lemma Finite_cons: "a~=UU ==>(Finite (a##x)) = (Finite x)"
apply (rule iffI)
apply (erule (1) Finite_cons_a [rule_format])
apply fast
apply simp
done


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
apply (rule prems)
done


lemma seq_finite_ind: "!!P.[|P(UU);P(nil);
   !! x s1.[|x~=UU;P(s1)|] ==> P(x##s1)
   |] ==> seq_finite(s) --> P(s)"
apply (rule seq_finite_ind_lemma)
apply (erule seq.finite_ind)
 apply assumption
apply simp
done

end
