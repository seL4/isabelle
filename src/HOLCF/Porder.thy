(*  Title:      HOLCF/Porder.thy
    ID:         $Id$
    Author:     Franz Regensburger

Definition of class porder (partial order).
Conservative extension of theory Porder0 by constant definitions.
*)

header {* Partial orders *}

theory Porder
imports Main
begin

subsection {* Type class for partial orders *}

	-- {* introduce a (syntactic) class for the constant @{text "<<"} *}
axclass sq_ord < type

	-- {* characteristic constant @{text "<<"} for po *}
consts
  "<<"          :: "['a,'a::sq_ord] => bool"        (infixl 55)

syntax (xsymbols)
  "op <<"       :: "['a,'a::sq_ord] => bool"        (infixl "\<sqsubseteq>" 55)

axclass po < sq_ord
        -- {* class axioms: *}
refl_less [iff]: "x << x"        
antisym_less:    "[|x << y; y << x |] ==> x = y"    
trans_less:      "[|x << y; y << z |] ==> x << z"

text {* minimal fixes least element *}

lemma minimal2UU[OF allI] : "!x::'a::po. uu<<x ==> uu=(THE u.!y. u<<y)"
by (blast intro: theI2 antisym_less)

text {* the reverse law of anti-symmetry of @{term "op <<"} *}

lemma antisym_less_inverse: "(x::'a::po)=y ==> x << y & y << x"
apply blast
done

lemma box_less: "[| (a::'a::po) << b; c << a; b << d|] ==> c << d"
apply (erule trans_less)
apply (erule trans_less)
apply assumption
done

lemma po_eq_conv: "((x::'a::po)=y) = (x << y & y << x)"
apply (fast elim!: antisym_less_inverse intro!: antisym_less)
done

subsection {* Chains and least upper bounds *}

consts  
        "<|"    ::      "['a set,'a::po] => bool"       (infixl 55)
        "<<|"   ::      "['a set,'a::po] => bool"       (infixl 55)
        lub     ::      "'a set => 'a::po"
        tord ::      "'a::po set => bool"
        chain ::     "(nat=>'a::po) => bool"
        max_in_chain :: "[nat,nat=>'a::po]=>bool"
        finite_chain :: "(nat=>'a::po)=>bool"

syntax
  "@LUB"	:: "('b => 'a) => 'a"	(binder "LUB " 10)

translations
  "LUB x. t"	== "lub(range(%x. t))"

syntax (xsymbols)
  "LUB "	:: "[idts, 'a] => 'a"		("(3\<Squnion>_./ _)"[0,10] 10)

defs

-- {* class definitions *}
is_ub_def:       "S  <| x == ! y. y:S --> y<<x"
is_lub_def:      "S <<| x == S <| x & (!u. S <| u  --> x << u)"

-- {* Arbitrary chains are total orders *}
tord_def:     "tord S == !x y. x:S & y:S --> (x<<y | y<<x)"

-- {* Here we use countable chains and I prefer to code them as functions! *}
chain_def:        "chain F == !i. F i << F (Suc i)"

-- {* finite chains, needed for monotony of continouous functions *}
max_in_chain_def: "max_in_chain i C == ! j. i <= j --> C(i) = C(j)" 
finite_chain_def: "finite_chain C == chain(C) & (? i. max_in_chain i C)"

lub_def:          "lub S == (THE x. S <<| x)"

text {* lubs are unique *}

lemma unique_lub: 
        "[| S <<| x ; S <<| y |] ==> x=y"
apply (unfold is_lub_def is_ub_def)
apply (blast intro: antisym_less)
done

text {* chains are monotone functions *}

lemma chain_mono [rule_format]: "chain F ==> x<y --> F x<<F y"
apply (unfold chain_def)
apply (induct_tac "y")
apply auto
prefer 2 apply (blast intro: trans_less)
apply (blast elim!: less_SucE)
done

lemma chain_mono3: "[| chain F; x <= y |] ==> F x << F y"
apply (drule le_imp_less_or_eq)
apply (blast intro: chain_mono)
done

text {* The range of a chain is a totally ordered *}

lemma chain_tord: "chain(F) ==> tord(range(F))"
apply (unfold tord_def)
apply safe
apply (rule nat_less_cases)
apply (fast intro: chain_mono)+
done

text {* technical lemmas about @{term lub} and @{term is_lub} *}

lemmas lub = lub_def [THEN meta_eq_to_obj_eq, standard]

lemma lubI[OF exI]: "EX x. M <<| x ==> M <<| lub(M)"
apply (unfold lub_def)
apply (rule theI')
apply (erule ex_ex1I)
apply (erule unique_lub)
apply assumption
done

lemma thelubI: "M <<| l ==> lub(M) = l"
apply (rule unique_lub)
apply (rule lubI)
apply assumption
apply assumption
done

lemma lub_singleton [simp]: "lub{x} = x"
apply (simp (no_asm) add: thelubI is_lub_def is_ub_def)
done

text {* access to some definition as inference rule *}

lemma is_lubD1: "S <<| x ==> S <| x"
apply (unfold is_lub_def)
apply auto
done

lemma is_lub_lub: "[| S <<| x; S <| u |] ==> x << u"
apply (unfold is_lub_def)
apply auto
done

lemma is_lubI:
        "[| S <| x; !!u. S <| u ==> x << u |] ==> S <<| x"
apply (unfold is_lub_def)
apply blast
done

lemma chainE: "chain F ==> F(i) << F(Suc(i))"
apply (unfold chain_def)
apply auto
done

lemma chainI: "(!!i. F i << F(Suc i)) ==> chain F"
apply (unfold chain_def)
apply blast
done

lemma chain_shift: "chain Y ==> chain (%i. Y (i + j))"
apply (rule chainI)
apply simp
apply (erule chainE)
done

text {* technical lemmas about (least) upper bounds of chains *}

lemma ub_rangeD: "range S <| x  ==> S(i) << x"
apply (unfold is_ub_def)
apply blast
done

lemma ub_rangeI: "(!!i. S i << x) ==> range S <| x"
apply (unfold is_ub_def)
apply blast
done

lemmas is_ub_lub = is_lubD1 [THEN ub_rangeD, standard]
  -- {* @{thm is_ub_lub} *} (* range(?S1) <<| ?x1 ==> ?S1(?x) << ?x1 *)

lemma is_ub_range_shift:
  "chain S \<Longrightarrow> range (\<lambda>i. S (i + j)) <| x = range S <| x"
apply (rule iffI)
apply (rule ub_rangeI)
apply (rule_tac y="S (i + j)" in trans_less)
apply (erule chain_mono3)
apply (rule le_add1)
apply (erule ub_rangeD)
apply (rule ub_rangeI)
apply (erule ub_rangeD)
done

lemma is_lub_range_shift:
  "chain S \<Longrightarrow> range (\<lambda>i. S (i + j)) <<| x = range S <<| x"
by (simp add: is_lub_def is_ub_range_shift)

text {* results about finite chains *}

lemma lub_finch1: 
        "[| chain C; max_in_chain i C|] ==> range C <<| C i"
apply (unfold max_in_chain_def)
apply (rule is_lubI)
apply (rule ub_rangeI)
apply (rule_tac m = "i" in nat_less_cases)
apply (rule antisym_less_inverse [THEN conjunct2])
apply (erule disjI1 [THEN less_or_eq_imp_le, THEN rev_mp])
apply (erule spec)
apply (rule antisym_less_inverse [THEN conjunct2])
apply (erule disjI2 [THEN less_or_eq_imp_le, THEN rev_mp])
apply (erule spec)
apply (erule chain_mono)
apply assumption
apply (erule ub_rangeD)
done

lemma lub_finch2: 
        "finite_chain(C) ==> range(C) <<| C(LEAST i. max_in_chain i C)"
apply (unfold finite_chain_def)
apply (rule lub_finch1)
prefer 2 apply (best intro: LeastI)
apply blast
done

lemma bin_chain: "x<<y ==> chain (%i. if i=0 then x else y)"
apply (rule chainI)
apply (induct_tac "i")
apply auto
done

lemma bin_chainmax: 
        "x<<y ==> max_in_chain (Suc 0) (%i. if (i=0) then x else y)"
apply (unfold max_in_chain_def le_def)
apply (rule allI)
apply (induct_tac "j")
apply auto
done

lemma lub_bin_chain: "x << y ==> range(%i::nat. if (i=0) then x else y) <<| y"
apply (rule_tac s = "if (Suc 0) = 0 then x else y" in subst , rule_tac [2] lub_finch1)
apply (erule_tac [2] bin_chain)
apply (erule_tac [2] bin_chainmax)
apply (simp (no_asm))
done

text {* the maximal element in a chain is its lub *}

lemma lub_chain_maxelem: "[| Y i = c;  ALL i. Y i<<c |] ==> lub(range Y) = c"
apply (blast dest: ub_rangeD intro: thelubI is_lubI ub_rangeI)
done

text {* the lub of a constant chain is the constant *}

lemma chain_const: "chain (\<lambda>i. c)"
by (simp add: chainI)

lemma lub_const: "range(%x. c) <<| c"
apply (blast dest: ub_rangeD intro: is_lubI ub_rangeI)
done

lemmas thelub_const = lub_const [THEN thelubI, standard]

end 
