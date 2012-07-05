(*  Title:      HOL/HOLCF/IOA/meta_theory/Sequence.thy
    Author:     Olaf Müller

Sequences over flat domains with lifted elements.
*)

theory Sequence
imports Seq
begin

default_sort type

type_synonym 'a Seq = "'a lift seq"

consts

  Consq            ::"'a            => 'a Seq -> 'a Seq"
  Filter           ::"('a => bool)  => 'a Seq -> 'a Seq"
  Map              ::"('a => 'b)    => 'a Seq -> 'b Seq"
  Forall           ::"('a => bool)  => 'a Seq => bool"
  Last             ::"'a Seq        -> 'a lift"
  Dropwhile        ::"('a => bool)  => 'a Seq -> 'a Seq"
  Takewhile        ::"('a => bool)  => 'a Seq -> 'a Seq"
  Zip              ::"'a Seq        -> 'b Seq -> ('a * 'b) Seq"
  Flat             ::"('a Seq) seq   -> 'a Seq"

  Filter2          ::"('a => bool)  => 'a Seq -> 'a Seq"

abbreviation
  Consq_syn  ("(_/>>_)"  [66,65] 65) where
  "a>>s == Consq a$s"

notation (xsymbols)
  Consq_syn  ("(_\<leadsto>_)"  [66,65] 65)


(* list Enumeration *)
syntax
  "_totlist"      :: "args => 'a Seq"              ("[(_)!]")
  "_partlist"     :: "args => 'a Seq"              ("[(_)?]")
translations
  "[x, xs!]"     == "x>>[xs!]"
  "[x!]"         == "x>>nil"
  "[x, xs?]"     == "x>>[xs?]"
  "[x?]"         == "x>>CONST bottom"

defs

Consq_def:     "Consq a == LAM s. Def a ## s"

Filter_def:    "Filter P == sfilter$(flift2 P)"

Map_def:       "Map f  == smap$(flift2 f)"

Forall_def:    "Forall P == sforall (flift2 P)"

Last_def:      "Last == slast"

Dropwhile_def: "Dropwhile P == sdropwhile$(flift2 P)"

Takewhile_def: "Takewhile P == stakewhile$(flift2 P)"

Flat_def:      "Flat == sflat"

Zip_def:
  "Zip == (fix$(LAM h t1 t2. case t1 of
               nil   => nil
             | x##xs => (case t2 of
                          nil => UU
                        | y##ys => (case x of
                                      UU  => UU
                                    | Def a => (case y of
                                                  UU => UU
                                                | Def b => Def (a,b)##(h$xs$ys))))))"

Filter2_def:    "Filter2 P == (fix$(LAM h t. case t of
            nil => nil
          | x##xs => (case x of UU => UU | Def y => (if P y
                     then x##(h$xs)
                     else     h$xs))))"

declare andalso_and [simp]
declare andalso_or [simp]

subsection "recursive equations of operators"

subsubsection "Map"

lemma Map_UU: "Map f$UU =UU"
by (simp add: Map_def)

lemma Map_nil: "Map f$nil =nil"
by (simp add: Map_def)

lemma Map_cons: "Map f$(x>>xs)=(f x) >> Map f$xs"
by (simp add: Map_def Consq_def flift2_def)


subsubsection {* Filter *}

lemma Filter_UU: "Filter P$UU =UU"
by (simp add: Filter_def)

lemma Filter_nil: "Filter P$nil =nil"
by (simp add: Filter_def)

lemma Filter_cons:
  "Filter P$(x>>xs)= (if P x then x>>(Filter P$xs) else Filter P$xs)"
by (simp add: Filter_def Consq_def flift2_def If_and_if)


subsubsection {* Forall *}

lemma Forall_UU: "Forall P UU"
by (simp add: Forall_def sforall_def)

lemma Forall_nil: "Forall P nil"
by (simp add: Forall_def sforall_def)

lemma Forall_cons: "Forall P (x>>xs)= (P x & Forall P xs)"
by (simp add: Forall_def sforall_def Consq_def flift2_def)


subsubsection {* Conc *}

lemma Conc_cons: "(x>>xs) @@ y = x>>(xs @@y)"
by (simp add: Consq_def)


subsubsection {* Takewhile *}

lemma Takewhile_UU: "Takewhile P$UU =UU"
by (simp add: Takewhile_def)

lemma Takewhile_nil: "Takewhile P$nil =nil"
by (simp add: Takewhile_def)

lemma Takewhile_cons:
  "Takewhile P$(x>>xs)= (if P x then x>>(Takewhile P$xs) else nil)"
by (simp add: Takewhile_def Consq_def flift2_def If_and_if)


subsubsection {* DropWhile *}

lemma Dropwhile_UU: "Dropwhile P$UU =UU"
by (simp add: Dropwhile_def)

lemma Dropwhile_nil: "Dropwhile P$nil =nil"
by (simp add: Dropwhile_def)

lemma Dropwhile_cons:
  "Dropwhile P$(x>>xs)= (if P x then Dropwhile P$xs else x>>xs)"
by (simp add: Dropwhile_def Consq_def flift2_def If_and_if)


subsubsection {* Last *}

lemma Last_UU: "Last$UU =UU"
by (simp add: Last_def)

lemma Last_nil: "Last$nil =UU"
by (simp add: Last_def)

lemma Last_cons: "Last$(x>>xs)= (if xs=nil then Def x else Last$xs)"
apply (simp add: Last_def Consq_def)
apply (cases xs)
apply simp_all
done


subsubsection {* Flat *}

lemma Flat_UU: "Flat$UU =UU"
by (simp add: Flat_def)

lemma Flat_nil: "Flat$nil =nil"
by (simp add: Flat_def)

lemma Flat_cons: "Flat$(x##xs)= x @@ (Flat$xs)"
by (simp add: Flat_def Consq_def)


subsubsection {* Zip *}

lemma Zip_unfold:
"Zip = (LAM t1 t2. case t1 of
                nil   => nil
              | x##xs => (case t2 of
                           nil => UU
                         | y##ys => (case x of
                                       UU  => UU
                                     | Def a => (case y of
                                                   UU => UU
                                                 | Def b => Def (a,b)##(Zip$xs$ys)))))"
apply (rule trans)
apply (rule fix_eq2)
apply (rule Zip_def)
apply (rule beta_cfun)
apply simp
done

lemma Zip_UU1: "Zip$UU$y =UU"
apply (subst Zip_unfold)
apply simp
done

lemma Zip_UU2: "x~=nil ==> Zip$x$UU =UU"
apply (subst Zip_unfold)
apply simp
apply (cases x)
apply simp_all
done

lemma Zip_nil: "Zip$nil$y =nil"
apply (subst Zip_unfold)
apply simp
done

lemma Zip_cons_nil: "Zip$(x>>xs)$nil= UU"
apply (subst Zip_unfold)
apply (simp add: Consq_def)
done

lemma Zip_cons: "Zip$(x>>xs)$(y>>ys)= (x,y) >> Zip$xs$ys"
apply (rule trans)
apply (subst Zip_unfold)
apply simp
apply (simp add: Consq_def)
done

lemmas [simp del] =
  sfilter_UU sfilter_nil sfilter_cons
  smap_UU smap_nil smap_cons
  sforall2_UU sforall2_nil sforall2_cons
  slast_UU slast_nil slast_cons
  stakewhile_UU  stakewhile_nil  stakewhile_cons
  sdropwhile_UU  sdropwhile_nil  sdropwhile_cons
  sflat_UU sflat_nil sflat_cons
  szip_UU1 szip_UU2 szip_nil szip_cons_nil szip_cons

lemmas [simp] =
  Filter_UU Filter_nil Filter_cons
  Map_UU Map_nil Map_cons
  Forall_UU Forall_nil Forall_cons
  Last_UU Last_nil Last_cons
  Conc_cons
  Takewhile_UU Takewhile_nil Takewhile_cons
  Dropwhile_UU Dropwhile_nil Dropwhile_cons
  Zip_UU1 Zip_UU2 Zip_nil Zip_cons_nil Zip_cons



section "Cons"

lemma Consq_def2: "a>>s = (Def a)##s"
apply (simp add: Consq_def)
done

lemma Seq_exhaust: "x = UU | x = nil | (? a s. x = a >> s)"
apply (simp add: Consq_def2)
apply (cut_tac seq.nchotomy)
apply (fast dest: not_Undef_is_Def [THEN iffD1])
done


lemma Seq_cases:
"!!P. [| x = UU ==> P; x = nil ==> P; !!a s. x = a >> s  ==> P |] ==> P"
apply (cut_tac x="x" in Seq_exhaust)
apply (erule disjE)
apply simp
apply (erule disjE)
apply simp
apply (erule exE)+
apply simp
done

(*
fun Seq_case_tac s i = rule_tac x",s)] Seq_cases i
          THEN hyp_subst_tac i THEN hyp_subst_tac (i+1) THEN hyp_subst_tac (i+2);
*)
(* on a>>s only simp_tac, as full_simp_tac is uncomplete and often causes errors *)
(*
fun Seq_case_simp_tac s i = Seq_case_tac s i THEN Asm_simp_tac (i+2)
                                             THEN Asm_full_simp_tac (i+1)
                                             THEN Asm_full_simp_tac i;
*)

lemma Cons_not_UU: "a>>s ~= UU"
apply (subst Consq_def2)
apply simp
done


lemma Cons_not_less_UU: "~(a>>x) << UU"
apply (rule notI)
apply (drule below_antisym)
apply simp
apply (simp add: Cons_not_UU)
done

lemma Cons_not_less_nil: "~a>>s << nil"
apply (simp add: Consq_def2)
done

lemma Cons_not_nil: "a>>s ~= nil"
apply (simp add: Consq_def2)
done

lemma Cons_not_nil2: "nil ~= a>>s"
apply (simp add: Consq_def2)
done

lemma Cons_inject_eq: "(a>>s = b>>t) = (a = b & s = t)"
apply (simp only: Consq_def2)
apply (simp add: scons_inject_eq)
done

lemma Cons_inject_less_eq: "(a>>s<<b>>t) = (a = b & s<<t)"
apply (simp add: Consq_def2)
done

lemma seq_take_Cons: "seq_take (Suc n)$(a>>x) = a>> (seq_take n$x)"
apply (simp add: Consq_def)
done

lemmas [simp] =
  Cons_not_nil2 Cons_inject_eq Cons_inject_less_eq seq_take_Cons
  Cons_not_UU Cons_not_less_UU Cons_not_less_nil Cons_not_nil


subsection "induction"

lemma Seq_induct:
"!! P. [| adm P; P UU; P nil; !! a s. P s ==> P (a>>s)|] ==> P x"
apply (erule (2) seq.induct)
apply defined
apply (simp add: Consq_def)
done

lemma Seq_FinitePartial_ind:
"!! P.[|P UU;P nil; !! a s. P s ==> P(a>>s) |]
                ==> seq_finite x --> P x"
apply (erule (1) seq_finite_ind)
apply defined
apply (simp add: Consq_def)
done

lemma Seq_Finite_ind:
"!! P.[| Finite x; P nil; !! a s. [| Finite s; P s|] ==> P (a>>s) |] ==> P x"
apply (erule (1) Finite.induct)
apply defined
apply (simp add: Consq_def)
done


(* rws are definitions to be unfolded for admissibility check *)
(*
fun Seq_induct_tac s rws i = rule_tac x",s)] Seq_induct i
                         THEN (REPEAT_DETERM (CHANGED (Asm_simp_tac (i+1))))
                         THEN simp add: rws) i;

fun Seq_Finite_induct_tac i = erule Seq_Finite_ind i
                              THEN (REPEAT_DETERM (CHANGED (Asm_simp_tac i)));

fun pair_tac s = rule_tac p",s)] PairE
                          THEN' hyp_subst_tac THEN' Simp_tac;
*)
(* induction on a sequence of pairs with pairsplitting and simplification *)
(*
fun pair_induct_tac s rws i =
           rule_tac x",s)] Seq_induct i
           THEN pair_tac "a" (i+3)
           THEN (REPEAT_DETERM (CHANGED (Simp_tac (i+1))))
           THEN simp add: rws) i;
*)


(* ------------------------------------------------------------------------------------ *)

subsection "HD,TL"

lemma HD_Cons [simp]: "HD$(x>>y) = Def x"
apply (simp add: Consq_def)
done

lemma TL_Cons [simp]: "TL$(x>>y) = y"
apply (simp add: Consq_def)
done

(* ------------------------------------------------------------------------------------ *)

subsection "Finite, Partial, Infinite"

lemma Finite_Cons [simp]: "Finite (a>>xs) = Finite xs"
apply (simp add: Consq_def2 Finite_cons)
done

lemma FiniteConc_1: "Finite (x::'a Seq) ==> Finite y --> Finite (x@@y)"
apply (erule Seq_Finite_ind, simp_all)
done

lemma FiniteConc_2:
"Finite (z::'a Seq) ==> !x y. z= x@@y --> (Finite x & Finite y)"
apply (erule Seq_Finite_ind)
(* nil*)
apply (intro strip)
apply (rule_tac x="x" in Seq_cases, simp_all)
(* cons *)
apply (intro strip)
apply (rule_tac x="x" in Seq_cases, simp_all)
apply (rule_tac x="y" in Seq_cases, simp_all)
done

lemma FiniteConc [simp]: "Finite(x@@y) = (Finite (x::'a Seq) & Finite y)"
apply (rule iffI)
apply (erule FiniteConc_2 [rule_format])
apply (rule refl)
apply (rule FiniteConc_1 [rule_format])
apply auto
done


lemma FiniteMap1: "Finite s ==> Finite (Map f$s)"
apply (erule Seq_Finite_ind, simp_all)
done

lemma FiniteMap2: "Finite s ==> ! t. (s = Map f$t) --> Finite t"
apply (erule Seq_Finite_ind)
apply (intro strip)
apply (rule_tac x="t" in Seq_cases, simp_all)
(* main case *)
apply auto
apply (rule_tac x="t" in Seq_cases, simp_all)
done

lemma Map2Finite: "Finite (Map f$s) = Finite s"
apply auto
apply (erule FiniteMap2 [rule_format])
apply (rule refl)
apply (erule FiniteMap1)
done


lemma FiniteFilter: "Finite s ==> Finite (Filter P$s)"
apply (erule Seq_Finite_ind, simp_all)
done


(* ----------------------------------------------------------------------------------- *)

subsection "Conc"

lemma Conc_cong: "!! x::'a Seq. Finite x ==> ((x @@ y) = (x @@ z)) = (y = z)"
apply (erule Seq_Finite_ind, simp_all)
done

lemma Conc_assoc: "(x @@ y) @@ z = (x::'a Seq) @@ y @@ z"
apply (rule_tac x="x" in Seq_induct, simp_all)
done

lemma nilConc [simp]: "s@@ nil = s"
apply (induct s)
apply simp
apply simp
apply simp
apply simp
done


(* should be same as nil_is_Conc2 when all nils are turned to right side !! *)
lemma nil_is_Conc: "(nil = x @@ y) = ((x::'a Seq)= nil & y = nil)"
apply (rule_tac x="x" in Seq_cases)
apply auto
done

lemma nil_is_Conc2: "(x @@ y = nil) = ((x::'a Seq)= nil & y = nil)"
apply (rule_tac x="x" in Seq_cases)
apply auto
done


(* ------------------------------------------------------------------------------------ *)

subsection "Last"

lemma Finite_Last1: "Finite s ==> s~=nil --> Last$s~=UU"
apply (erule Seq_Finite_ind, simp_all)
done

lemma Finite_Last2: "Finite s ==> Last$s=UU --> s=nil"
apply (erule Seq_Finite_ind, simp_all)
apply fast
done


(* ------------------------------------------------------------------------------------ *)


subsection "Filter, Conc"


lemma FilterPQ: "Filter P$(Filter Q$s) = Filter (%x. P x & Q x)$s"
apply (rule_tac x="s" in Seq_induct, simp_all)
done

lemma FilterConc: "Filter P$(x @@ y) = (Filter P$x @@ Filter P$y)"
apply (simp add: Filter_def sfiltersconc)
done

(* ------------------------------------------------------------------------------------ *)

subsection "Map"

lemma MapMap: "Map f$(Map g$s) = Map (f o g)$s"
apply (rule_tac x="s" in Seq_induct, simp_all)
done

lemma MapConc: "Map f$(x@@y) = (Map f$x) @@ (Map f$y)"
apply (rule_tac x="x" in Seq_induct, simp_all)
done

lemma MapFilter: "Filter P$(Map f$x) = Map f$(Filter (P o f)$x)"
apply (rule_tac x="x" in Seq_induct, simp_all)
done

lemma nilMap: "nil = (Map f$s) --> s= nil"
apply (rule_tac x="s" in Seq_cases, simp_all)
done


lemma ForallMap: "Forall P (Map f$s) = Forall (P o f) s"
apply (rule_tac x="s" in Seq_induct)
apply (simp add: Forall_def sforall_def)
apply simp_all
done




(* ------------------------------------------------------------------------------------ *)

subsection "Forall"


lemma ForallPForallQ1: "Forall P ys & (! x. P x --> Q x)
         --> Forall Q ys"
apply (rule_tac x="ys" in Seq_induct)
apply (simp add: Forall_def sforall_def)
apply simp_all
done

lemmas ForallPForallQ =
  ForallPForallQ1 [THEN mp, OF conjI, OF _ allI, OF _ impI]

lemma Forall_Conc_impl: "(Forall P x & Forall P y) --> Forall P (x @@ y)"
apply (rule_tac x="x" in Seq_induct)
apply (simp add: Forall_def sforall_def)
apply simp_all
done

lemma Forall_Conc [simp]:
  "Finite x ==> Forall P (x @@ y) = (Forall P x & Forall P y)"
apply (erule Seq_Finite_ind, simp_all)
done

lemma ForallTL1: "Forall P s  --> Forall P (TL$s)"
apply (rule_tac x="s" in Seq_induct)
apply (simp add: Forall_def sforall_def)
apply simp_all
done

lemmas ForallTL = ForallTL1 [THEN mp]

lemma ForallDropwhile1: "Forall P s  --> Forall P (Dropwhile Q$s)"
apply (rule_tac x="s" in Seq_induct)
apply (simp add: Forall_def sforall_def)
apply simp_all
done

lemmas ForallDropwhile = ForallDropwhile1 [THEN mp]


(* only admissible in t, not if done in s *)

lemma Forall_prefix: "! s. Forall P s --> t<<s --> Forall P t"
apply (rule_tac x="t" in Seq_induct)
apply (simp add: Forall_def sforall_def)
apply simp_all
apply (intro strip)
apply (rule_tac x="sa" in Seq_cases)
apply simp
apply auto
done

lemmas Forall_prefixclosed = Forall_prefix [rule_format]

lemma Forall_postfixclosed:
  "[| Finite h; Forall P s; s= h @@ t |] ==> Forall P t"
apply auto
done


lemma ForallPFilterQR1:
  "((! x. P x --> (Q x = R x)) & Forall P tr) --> Filter Q$tr = Filter R$tr"
apply (rule_tac x="tr" in Seq_induct)
apply (simp add: Forall_def sforall_def)
apply simp_all
done

lemmas ForallPFilterQR = ForallPFilterQR1 [THEN mp, OF conjI, OF allI]


(* ------------------------------------------------------------------------------------- *)

subsection "Forall, Filter"


lemma ForallPFilterP: "Forall P (Filter P$x)"
apply (simp add: Filter_def Forall_def forallPsfilterP)
done

(* holds also in other direction, then equal to forallPfilterP *)
lemma ForallPFilterPid1: "Forall P x --> Filter P$x = x"
apply (rule_tac x="x" in Seq_induct)
apply (simp add: Forall_def sforall_def Filter_def)
apply simp_all
done

lemmas ForallPFilterPid = ForallPFilterPid1 [THEN mp]


(* holds also in other direction *)
lemma ForallnPFilterPnil1: "!! ys . Finite ys ==>
   Forall (%x. ~P x) ys --> Filter P$ys = nil "
apply (erule Seq_Finite_ind, simp_all)
done

lemmas ForallnPFilterPnil = ForallnPFilterPnil1 [THEN mp]


(* holds also in other direction *)
lemma ForallnPFilterPUU1: "~Finite ys & Forall (%x. ~P x) ys
                  --> Filter P$ys = UU "
apply (rule_tac x="ys" in Seq_induct)
apply (simp add: Forall_def sforall_def)
apply simp_all
done

lemmas ForallnPFilterPUU = ForallnPFilterPUU1 [THEN mp, OF conjI]


(* inverse of ForallnPFilterPnil *)

lemma FilternPnilForallP [rule_format]: "Filter P$ys = nil -->
   (Forall (%x. ~P x) ys & Finite ys)"
apply (rule_tac x="ys" in Seq_induct)
(* adm *)
apply (simp add: Forall_def sforall_def)
(* base cases *)
apply simp
apply simp
(* main case *)
apply simp
done


(* inverse of ForallnPFilterPUU *)

lemma FilternPUUForallP:
  assumes "Filter P$ys = UU"
  shows "Forall (%x. ~P x) ys  & ~Finite ys"
proof
  show "Forall (%x. ~P x) ys"
  proof (rule classical)
    assume "\<not> ?thesis"
    then have "Filter P$ys ~= UU"
      apply (rule rev_mp)
      apply (induct ys rule: Seq_induct)
      apply (simp add: Forall_def sforall_def)
      apply simp_all
      done
    with assms show ?thesis by contradiction
  qed
  show "~ Finite ys"
  proof
    assume "Finite ys"
    then have "Filter P$ys ~= UU"
      by (rule Seq_Finite_ind) simp_all
    with assms show False by contradiction
  qed
qed


lemma ForallQFilterPnil:
  "!! Q P.[| Forall Q ys; Finite ys; !!x. Q x ==> ~P x|]
    ==> Filter P$ys = nil"
apply (erule ForallnPFilterPnil)
apply (erule ForallPForallQ)
apply auto
done

lemma ForallQFilterPUU:
 "!! Q P. [| ~Finite ys; Forall Q ys;  !!x. Q x ==> ~P x|]
    ==> Filter P$ys = UU "
apply (erule ForallnPFilterPUU)
apply (erule ForallPForallQ)
apply auto
done



(* ------------------------------------------------------------------------------------- *)

subsection "Takewhile, Forall, Filter"


lemma ForallPTakewhileP [simp]: "Forall P (Takewhile P$x)"
apply (simp add: Forall_def Takewhile_def sforallPstakewhileP)
done


lemma ForallPTakewhileQ [simp]:
"!! P. [| !!x. Q x==> P x |] ==> Forall P (Takewhile Q$x)"
apply (rule ForallPForallQ)
apply (rule ForallPTakewhileP)
apply auto
done


lemma FilterPTakewhileQnil [simp]:
  "!! Q P.[| Finite (Takewhile Q$ys); !!x. Q x ==> ~P x |]
   ==> Filter P$(Takewhile Q$ys) = nil"
apply (erule ForallnPFilterPnil)
apply (rule ForallPForallQ)
apply (rule ForallPTakewhileP)
apply auto
done

lemma FilterPTakewhileQid [simp]:
 "!! Q P. [| !!x. Q x ==> P x |] ==>
            Filter P$(Takewhile Q$ys) = (Takewhile Q$ys)"
apply (rule ForallPFilterPid)
apply (rule ForallPForallQ)
apply (rule ForallPTakewhileP)
apply auto
done


lemma Takewhile_idempotent: "Takewhile P$(Takewhile P$s) = Takewhile P$s"
apply (rule_tac x="s" in Seq_induct)
apply (simp add: Forall_def sforall_def)
apply simp_all
done

lemma ForallPTakewhileQnP [simp]:
 "Forall P s --> Takewhile (%x. Q x | (~P x))$s = Takewhile Q$s"
apply (rule_tac x="s" in Seq_induct)
apply (simp add: Forall_def sforall_def)
apply simp_all
done

lemma ForallPDropwhileQnP [simp]:
 "Forall P s --> Dropwhile (%x. Q x | (~P x))$s = Dropwhile Q$s"
apply (rule_tac x="s" in Seq_induct)
apply (simp add: Forall_def sforall_def)
apply simp_all
done


lemma TakewhileConc1:
 "Forall P s --> Takewhile P$(s @@ t) = s @@ (Takewhile P$t)"
apply (rule_tac x="s" in Seq_induct)
apply (simp add: Forall_def sforall_def)
apply simp_all
done

lemmas TakewhileConc = TakewhileConc1 [THEN mp]

lemma DropwhileConc1:
 "Finite s ==> Forall P s --> Dropwhile P$(s @@ t) = Dropwhile P$t"
apply (erule Seq_Finite_ind, simp_all)
done

lemmas DropwhileConc = DropwhileConc1 [THEN mp]



(* ----------------------------------------------------------------------------------- *)

subsection "coinductive characterizations of Filter"


lemma divide_Seq_lemma:
 "HD$(Filter P$y) = Def x
    --> y = ((Takewhile (%x. ~P x)$y) @@ (x >> TL$(Dropwhile (%a.~P a)$y))) 
             & Finite (Takewhile (%x. ~ P x)$y)  & P x"

(* FIX: pay attention: is only admissible with chain-finite package to be added to
        adm test and Finite f x admissibility *)
apply (rule_tac x="y" in Seq_induct)
apply (simp add: adm_subst [OF _ adm_Finite])
apply simp
apply simp
apply (case_tac "P a")
 apply simp
 apply blast
(* ~ P a *)
apply simp
done

lemma divide_Seq: "(x>>xs) << Filter P$y 
   ==> y = ((Takewhile (%a. ~ P a)$y) @@ (x >> TL$(Dropwhile (%a.~P a)$y)))
      & Finite (Takewhile (%a. ~ P a)$y)  & P x"
apply (rule divide_Seq_lemma [THEN mp])
apply (drule_tac f="HD" and x="x>>xs" in  monofun_cfun_arg)
apply simp
done


lemma nForall_HDFilter:
 "~Forall P y --> (? x. HD$(Filter (%a. ~P a)$y) = Def x)"
unfolding not_Undef_is_Def [symmetric]
apply (induct y rule: Seq_induct)
apply (simp add: Forall_def sforall_def)
apply simp_all
done


lemma divide_Seq2: "~Forall P y
  ==> ? x. y= (Takewhile P$y @@ (x >> TL$(Dropwhile P$y))) &
      Finite (Takewhile P$y) & (~ P x)"
apply (drule nForall_HDFilter [THEN mp])
apply safe
apply (rule_tac x="x" in exI)
apply (cut_tac P1="%x. ~ P x" in divide_Seq_lemma [THEN mp])
apply auto
done


lemma divide_Seq3: "~Forall P y
  ==> ? x bs rs. y= (bs @@ (x>>rs)) & Finite bs & Forall P bs & (~ P x)"
apply (drule divide_Seq2)
(*Auto_tac no longer proves it*)
apply fastforce
done

lemmas [simp] = FilterPQ FilterConc Conc_cong


(* ------------------------------------------------------------------------------------- *)


subsection "take_lemma"

lemma seq_take_lemma: "(!n. seq_take n$x = seq_take n$x') = (x = x')"
apply (rule iffI)
apply (rule seq.take_lemma)
apply auto
done

lemma take_reduction1:
"  ! n. ((! k. k < n --> seq_take k$y1 = seq_take k$y2)
    --> seq_take n$(x @@ (t>>y1)) =  seq_take n$(x @@ (t>>y2)))"
apply (rule_tac x="x" in Seq_induct)
apply simp_all
apply (intro strip)
apply (case_tac "n")
apply auto
apply (case_tac "n")
apply auto
done


lemma take_reduction:
 "!! n.[| x=y; s=t; !! k. k<n ==> seq_take k$y1 = seq_take k$y2|]
  ==> seq_take n$(x @@ (s>>y1)) =  seq_take n$(y @@ (t>>y2))"
apply (auto intro!: take_reduction1 [rule_format])
done

(* ------------------------------------------------------------------
          take-lemma and take_reduction for << instead of =
   ------------------------------------------------------------------ *)

lemma take_reduction_less1:
"  ! n. ((! k. k < n --> seq_take k$y1 << seq_take k$y2)
    --> seq_take n$(x @@ (t>>y1)) <<  seq_take n$(x @@ (t>>y2)))"
apply (rule_tac x="x" in Seq_induct)
apply simp_all
apply (intro strip)
apply (case_tac "n")
apply auto
apply (case_tac "n")
apply auto
done


lemma take_reduction_less:
 "!! n.[| x=y; s=t;!! k. k<n ==> seq_take k$y1 << seq_take k$y2|]
  ==> seq_take n$(x @@ (s>>y1)) <<  seq_take n$(y @@ (t>>y2))"
apply (auto intro!: take_reduction_less1 [rule_format])
done

lemma take_lemma_less1:
  assumes "!! n. seq_take n$s1 << seq_take n$s2"
  shows "s1<<s2"
apply (rule_tac t="s1" in seq.reach [THEN subst])
apply (rule_tac t="s2" in seq.reach [THEN subst])
apply (rule lub_mono)
apply (rule seq.chain_take [THEN ch2ch_Rep_cfunL])
apply (rule seq.chain_take [THEN ch2ch_Rep_cfunL])
apply (rule assms)
done


lemma take_lemma_less: "(!n. seq_take n$x << seq_take n$x') = (x << x')"
apply (rule iffI)
apply (rule take_lemma_less1)
apply auto
apply (erule monofun_cfun_arg)
done

(* ------------------------------------------------------------------
          take-lemma proof principles
   ------------------------------------------------------------------ *)

lemma take_lemma_principle1:
 "!! Q. [|!! s. [| Forall Q s; A s |] ==> (f s) = (g s) ;
            !! s1 s2 y. [| Forall Q s1; Finite s1; ~ Q y; A (s1 @@ y>>s2)|]
                          ==> (f (s1 @@ y>>s2)) = (g (s1 @@ y>>s2)) |]
               ==> A x --> (f x)=(g x)"
apply (case_tac "Forall Q x")
apply (auto dest!: divide_Seq3)
done

lemma take_lemma_principle2:
  "!! Q. [|!! s. [| Forall Q s; A s |] ==> (f s) = (g s) ;
           !! s1 s2 y. [| Forall Q s1; Finite s1; ~ Q y; A (s1 @@ y>>s2)|]
                          ==> ! n. seq_take n$(f (s1 @@ y>>s2))
                                 = seq_take n$(g (s1 @@ y>>s2)) |]
               ==> A x --> (f x)=(g x)"
apply (case_tac "Forall Q x")
apply (auto dest!: divide_Seq3)
apply (rule seq.take_lemma)
apply auto
done


(* Note: in the following proofs the ordering of proof steps is very
         important, as otherwise either (Forall Q s1) would be in the IH as
         assumption (then rule useless) or it is not possible to strengthen
         the IH apply doing a forall closure of the sequence t (then rule also useless).
         This is also the reason why the induction rule (nat_less_induct or nat_induct) has to
         to be imbuilt into the rule, as induction has to be done early and the take lemma
         has to be used in the trivial direction afterwards for the (Forall Q x) case.  *)

lemma take_lemma_induct:
"!! Q. [|!! s. [| Forall Q s; A s |] ==> (f s) = (g s) ;
         !! s1 s2 y n. [| ! t. A t --> seq_take n$(f t) = seq_take n$(g t);
                          Forall Q s1; Finite s1; ~ Q y; A (s1 @@ y>>s2) |]
                          ==>   seq_take (Suc n)$(f (s1 @@ y>>s2))
                              = seq_take (Suc n)$(g (s1 @@ y>>s2)) |]
               ==> A x --> (f x)=(g x)"
apply (rule impI)
apply (rule seq.take_lemma)
apply (rule mp)
prefer 2 apply assumption
apply (rule_tac x="x" in spec)
apply (rule nat.induct)
apply simp
apply (rule allI)
apply (case_tac "Forall Q xa")
apply (force intro!: seq_take_lemma [THEN iffD2, THEN spec])
apply (auto dest!: divide_Seq3)
done


lemma take_lemma_less_induct:
"!! Q. [|!! s. [| Forall Q s; A s |] ==> (f s) = (g s) ;
        !! s1 s2 y n. [| ! t m. m < n --> A t --> seq_take m$(f t) = seq_take m$(g t);
                          Forall Q s1; Finite s1; ~ Q y; A (s1 @@ y>>s2) |]
                          ==>   seq_take n$(f (s1 @@ y>>s2))
                              = seq_take n$(g (s1 @@ y>>s2)) |]
               ==> A x --> (f x)=(g x)"
apply (rule impI)
apply (rule seq.take_lemma)
apply (rule mp)
prefer 2 apply assumption
apply (rule_tac x="x" in spec)
apply (rule nat_less_induct)
apply (rule allI)
apply (case_tac "Forall Q xa")
apply (force intro!: seq_take_lemma [THEN iffD2, THEN spec])
apply (auto dest!: divide_Seq3)
done



lemma take_lemma_in_eq_out:
"!! Q. [| A UU  ==> (f UU) = (g UU) ;
          A nil ==> (f nil) = (g nil) ;
          !! s y n. [| ! t. A t --> seq_take n$(f t) = seq_take n$(g t);
                     A (y>>s) |]
                     ==>   seq_take (Suc n)$(f (y>>s))
                         = seq_take (Suc n)$(g (y>>s)) |]
               ==> A x --> (f x)=(g x)"
apply (rule impI)
apply (rule seq.take_lemma)
apply (rule mp)
prefer 2 apply assumption
apply (rule_tac x="x" in spec)
apply (rule nat.induct)
apply simp
apply (rule allI)
apply (rule_tac x="xa" in Seq_cases)
apply simp_all
done


(* ------------------------------------------------------------------------------------ *)

subsection "alternative take_lemma proofs"


(* --------------------------------------------------------------- *)
(*              Alternative Proof of FilterPQ                      *)
(* --------------------------------------------------------------- *)

declare FilterPQ [simp del]


(* In general: How to do this case without the same adm problems
   as for the entire proof ? *)
lemma Filter_lemma1: "Forall (%x.~(P x & Q x)) s
          --> Filter P$(Filter Q$s) =
              Filter (%x. P x & Q x)$s"

apply (rule_tac x="s" in Seq_induct)
apply (simp add: Forall_def sforall_def)
apply simp_all
done

lemma Filter_lemma2: "Finite s ==>
          (Forall (%x. (~P x) | (~ Q x)) s
          --> Filter P$(Filter Q$s) = nil)"
apply (erule Seq_Finite_ind, simp_all)
done

lemma Filter_lemma3: "Finite s ==>
          Forall (%x. (~P x) | (~ Q x)) s
          --> Filter (%x. P x & Q x)$s = nil"
apply (erule Seq_Finite_ind, simp_all)
done


lemma FilterPQ_takelemma: "Filter P$(Filter Q$s) = Filter (%x. P x & Q x)$s"
apply (rule_tac A1="%x. True" and
                 Q1="%x.~(P x & Q x)" and x1="s" in
                 take_lemma_induct [THEN mp])
(* better support for A = %x. True *)
apply (simp add: Filter_lemma1)
apply (simp add: Filter_lemma2 Filter_lemma3)
apply simp
done

declare FilterPQ [simp]


(* --------------------------------------------------------------- *)
(*              Alternative Proof of MapConc                       *)
(* --------------------------------------------------------------- *)



lemma MapConc_takelemma: "Map f$(x@@y) = (Map f$x) @@ (Map f$y)"
apply (rule_tac A1="%x. True" and x1="x" in
    take_lemma_in_eq_out [THEN mp])
apply auto
done


ML {*

fun Seq_case_tac ctxt s i =
  res_inst_tac ctxt [(("x", 0), s)] @{thm Seq_cases} i
  THEN hyp_subst_tac i THEN hyp_subst_tac (i+1) THEN hyp_subst_tac (i+2);

(* on a>>s only simp_tac, as full_simp_tac is uncomplete and often causes errors *)
fun Seq_case_simp_tac ctxt s i =
  let val ss = simpset_of ctxt in
    Seq_case_tac ctxt s i
    THEN asm_simp_tac ss (i+2)
    THEN asm_full_simp_tac ss (i+1)
    THEN asm_full_simp_tac ss i
  end;

(* rws are definitions to be unfolded for admissibility check *)
fun Seq_induct_tac ctxt s rws i =
  let val ss = simpset_of ctxt in
    res_inst_tac ctxt [(("x", 0), s)] @{thm Seq_induct} i
    THEN (REPEAT_DETERM (CHANGED (asm_simp_tac ss (i+1))))
    THEN simp_tac (ss addsimps rws) i
  end;

fun Seq_Finite_induct_tac ctxt i =
  etac @{thm Seq_Finite_ind} i
  THEN (REPEAT_DETERM (CHANGED (asm_simp_tac (simpset_of ctxt) i)));

fun pair_tac ctxt s =
  res_inst_tac ctxt [(("p", 0), s)] @{thm PairE}
  THEN' hyp_subst_tac THEN' asm_full_simp_tac (simpset_of ctxt);

(* induction on a sequence of pairs with pairsplitting and simplification *)
fun pair_induct_tac ctxt s rws i =
  let val ss = simpset_of ctxt in
    res_inst_tac ctxt [(("x", 0), s)] @{thm Seq_induct} i
    THEN pair_tac ctxt "a" (i+3)
    THEN (REPEAT_DETERM (CHANGED (simp_tac ss (i+1))))
    THEN simp_tac (ss addsimps rws) i
  end;

*}

end
