(*  Title:      HOL/HOL.thy
    ID:         $Id$
    Author:     Tobias Nipkow, Markus Wenzel, and Larry Paulson
*)

header {* The basis of Higher-Order Logic *}

theory HOL
imports CPure
files ("cladata.ML") ("blastdata.ML") ("simpdata.ML") ("antisym_setup.ML")
begin

subsection {* Primitive logic *}

subsubsection {* Core syntax *}

classes type
defaultsort type

global

typedecl bool

arities
  bool :: type
  fun :: (type, type) type

judgment
  Trueprop      :: "bool => prop"                   ("(_)" 5)

consts
  Not           :: "bool => bool"                   ("~ _" [40] 40)
  True          :: bool
  False         :: bool
  If            :: "[bool, 'a, 'a] => 'a"           ("(if (_)/ then (_)/ else (_))" 10)
  arbitrary     :: 'a

  The           :: "('a => bool) => 'a"
  All           :: "('a => bool) => bool"           (binder "ALL " 10)
  Ex            :: "('a => bool) => bool"           (binder "EX " 10)
  Ex1           :: "('a => bool) => bool"           (binder "EX! " 10)
  Let           :: "['a, 'a => 'b] => 'b"

  "="           :: "['a, 'a] => bool"               (infixl 50)
  &             :: "[bool, bool] => bool"           (infixr 35)
  "|"           :: "[bool, bool] => bool"           (infixr 30)
  -->           :: "[bool, bool] => bool"           (infixr 25)

local


subsubsection {* Additional concrete syntax *}

nonterminals
  letbinds  letbind
  case_syn  cases_syn

syntax
  "_not_equal"  :: "['a, 'a] => bool"                    (infixl "~=" 50)
  "_The"        :: "[pttrn, bool] => 'a"                 ("(3THE _./ _)" [0, 10] 10)

  "_bind"       :: "[pttrn, 'a] => letbind"              ("(2_ =/ _)" 10)
  ""            :: "letbind => letbinds"                 ("_")
  "_binds"      :: "[letbind, letbinds] => letbinds"     ("_;/ _")
  "_Let"        :: "[letbinds, 'a] => 'a"                ("(let (_)/ in (_))" 10)

  "_case_syntax":: "['a, cases_syn] => 'b"               ("(case _ of/ _)" 10)
  "_case1"      :: "['a, 'b] => case_syn"                ("(2_ =>/ _)" 10)
  ""            :: "case_syn => cases_syn"               ("_")
  "_case2"      :: "[case_syn, cases_syn] => cases_syn"  ("_/ | _")

translations
  "x ~= y"                == "~ (x = y)"
  "THE x. P"              == "The (%x. P)"
  "_Let (_binds b bs) e"  == "_Let b (_Let bs e)"
  "let x = a in e"        == "Let a (%x. e)"

print_translation {*
(* To avoid eta-contraction of body: *)
[("The", fn [Abs abs] =>
     let val (x,t) = atomic_abs_tr' abs
     in Syntax.const "_The" $ x $ t end)]
*}

syntax (output)
  "="           :: "['a, 'a] => bool"                    (infix 50)
  "_not_equal"  :: "['a, 'a] => bool"                    (infix "~=" 50)

syntax (xsymbols)
  Not           :: "bool => bool"                        ("\<not> _" [40] 40)
  "op &"        :: "[bool, bool] => bool"                (infixr "\<and>" 35)
  "op |"        :: "[bool, bool] => bool"                (infixr "\<or>" 30)
  "op -->"      :: "[bool, bool] => bool"                (infixr "\<longrightarrow>" 25)
  "_not_equal"  :: "['a, 'a] => bool"                    (infix "\<noteq>" 50)
  "ALL "        :: "[idts, bool] => bool"                ("(3\<forall>_./ _)" [0, 10] 10)
  "EX "         :: "[idts, bool] => bool"                ("(3\<exists>_./ _)" [0, 10] 10)
  "EX! "        :: "[idts, bool] => bool"                ("(3\<exists>!_./ _)" [0, 10] 10)
  "_case1"      :: "['a, 'b] => case_syn"                ("(2_ \<Rightarrow>/ _)" 10)
(*"_case2"      :: "[case_syn, cases_syn] => cases_syn"  ("_/ \<orelse> _")*)

syntax (xsymbols output)
  "_not_equal"  :: "['a, 'a] => bool"                    (infix "\<noteq>" 50)

syntax (HTML output)
  "_not_equal"  :: "['a, 'a] => bool"                    (infix "\<noteq>" 50)
  Not           :: "bool => bool"                        ("\<not> _" [40] 40)
  "op &"        :: "[bool, bool] => bool"                (infixr "\<and>" 35)
  "op |"        :: "[bool, bool] => bool"                (infixr "\<or>" 30)
  "_not_equal"  :: "['a, 'a] => bool"                    (infix "\<noteq>" 50)
  "ALL "        :: "[idts, bool] => bool"                ("(3\<forall>_./ _)" [0, 10] 10)
  "EX "         :: "[idts, bool] => bool"                ("(3\<exists>_./ _)" [0, 10] 10)
  "EX! "        :: "[idts, bool] => bool"                ("(3\<exists>!_./ _)" [0, 10] 10)

syntax (HOL)
  "ALL "        :: "[idts, bool] => bool"                ("(3! _./ _)" [0, 10] 10)
  "EX "         :: "[idts, bool] => bool"                ("(3? _./ _)" [0, 10] 10)
  "EX! "        :: "[idts, bool] => bool"                ("(3?! _./ _)" [0, 10] 10)


subsubsection {* Axioms and basic definitions *}

axioms
  eq_reflection:  "(x=y) ==> (x==y)"

  refl:           "t = (t::'a)"

  ext:            "(!!x::'a. (f x ::'b) = g x) ==> (%x. f x) = (%x. g x)"
    -- {*Extensionality is built into the meta-logic, and this rule expresses
         a related property.  It is an eta-expanded version of the traditional
         rule, and similar to the ABS rule of HOL*}

  the_eq_trivial: "(THE x. x = a) = (a::'a)"

  impI:           "(P ==> Q) ==> P-->Q"
  mp:             "[| P-->Q;  P |] ==> Q"


text{*Thanks to Stephan Merz*}
theorem subst:
  assumes eq: "s = t" and p: "P(s)"
  shows "P(t::'a)"
proof -
  from eq have meta: "s \<equiv> t"
    by (rule eq_reflection)
  from p show ?thesis
    by (unfold meta)
qed

defs
  True_def:     "True      == ((%x::bool. x) = (%x. x))"
  All_def:      "All(P)    == (P = (%x. True))"
  Ex_def:       "Ex(P)     == !Q. (!x. P x --> Q) --> Q"
  False_def:    "False     == (!P. P)"
  not_def:      "~ P       == P-->False"
  and_def:      "P & Q     == !R. (P-->Q-->R) --> R"
  or_def:       "P | Q     == !R. (P-->R) --> (Q-->R) --> R"
  Ex1_def:      "Ex1(P)    == ? x. P(x) & (! y. P(y) --> y=x)"

axioms
  iff:          "(P-->Q) --> (Q-->P) --> (P=Q)"
  True_or_False:  "(P=True) | (P=False)"

defs
  Let_def:      "Let s f == f(s)"
  if_def:       "If P x y == THE z::'a. (P=True --> z=x) & (P=False --> z=y)"

finalconsts
  "op ="
  "op -->"
  The
  arbitrary

subsubsection {* Generic algebraic operations *}

axclass zero < type
axclass one < type
axclass plus < type
axclass minus < type
axclass times < type
axclass inverse < type

global

consts
  "0"           :: "'a::zero"                       ("0")
  "1"           :: "'a::one"                        ("1")
  "+"           :: "['a::plus, 'a]  => 'a"          (infixl 65)
  -             :: "['a::minus, 'a] => 'a"          (infixl 65)
  uminus        :: "['a::minus] => 'a"              ("- _" [81] 80)
  *             :: "['a::times, 'a] => 'a"          (infixl 70)

syntax
  "_index1"  :: index    ("\<^sub>1")
translations
  (index) "\<^sub>1" => (index) "\<^bsub>\<struct>\<^esub>"

local

typed_print_translation {*
  let
    fun tr' c = (c, fn show_sorts => fn T => fn ts =>
      if T = dummyT orelse not (! show_types) andalso can Term.dest_Type T then raise Match
      else Syntax.const Syntax.constrainC $ Syntax.const c $ Syntax.term_of_typ show_sorts T);
  in [tr' "0", tr' "1"] end;
*} -- {* show types that are presumably too general *}


consts
  abs           :: "'a::minus => 'a"
  inverse       :: "'a::inverse => 'a"
  divide        :: "['a::inverse, 'a] => 'a"        (infixl "'/" 70)

syntax (xsymbols)
  abs :: "'a::minus => 'a"    ("\<bar>_\<bar>")
syntax (HTML output)
  abs :: "'a::minus => 'a"    ("\<bar>_\<bar>")


subsection {*Equality*}

lemma sym: "s=t ==> t=s"
apply (erule subst)
apply (rule refl)
done

(*calling "standard" reduces maxidx to 0*)
lemmas ssubst = sym [THEN subst, standard]

lemma trans: "[| r=s; s=t |] ==> r=t"
apply (erule subst , assumption)
done

lemma def_imp_eq:  assumes meq: "A == B" shows "A = B"
apply (unfold meq)
apply (rule refl)
done

(*Useful with eresolve_tac for proving equalties from known equalities.
        a = b
        |   |
        c = d   *)
lemma box_equals: "[| a=b;  a=c;  b=d |] ==> c=d"
apply (rule trans)
apply (rule trans)
apply (rule sym)
apply assumption+
done


subsection {*Congruence rules for application*}

(*similar to AP_THM in Gordon's HOL*)
lemma fun_cong: "(f::'a=>'b) = g ==> f(x)=g(x)"
apply (erule subst)
apply (rule refl)
done

(*similar to AP_TERM in Gordon's HOL and FOL's subst_context*)
lemma arg_cong: "x=y ==> f(x)=f(y)"
apply (erule subst)
apply (rule refl)
done

lemma cong: "[| f = g; (x::'a) = y |] ==> f(x) = g(y)"
apply (erule subst)+
apply (rule refl)
done


subsection {*Equality of booleans -- iff*}

lemma iffI: assumes prems: "P ==> Q" "Q ==> P" shows "P=Q"
apply (rules intro: iff [THEN mp, THEN mp] impI prems)
done

lemma iffD2: "[| P=Q; Q |] ==> P"
apply (erule ssubst)
apply assumption
done

lemma rev_iffD2: "[| Q; P=Q |] ==> P"
apply (erule iffD2)
apply assumption
done

lemmas iffD1 = sym [THEN iffD2, standard]
lemmas rev_iffD1 = sym [THEN [2] rev_iffD2, standard]

lemma iffE:
  assumes major: "P=Q"
      and minor: "[| P --> Q; Q --> P |] ==> R"
  shows "R"
by (rules intro: minor impI major [THEN iffD2] major [THEN iffD1])


subsection {*True*}

lemma TrueI: "True"
apply (unfold True_def)
apply (rule refl)
done

lemma eqTrueI: "P ==> P=True"
by (rules intro: iffI TrueI)

lemma eqTrueE: "P=True ==> P"
apply (erule iffD2)
apply (rule TrueI)
done


subsection {*Universal quantifier*}

lemma allI: assumes p: "!!x::'a. P(x)" shows "ALL x. P(x)"
apply (unfold All_def)
apply (rules intro: ext eqTrueI p)
done

lemma spec: "ALL x::'a. P(x) ==> P(x)"
apply (unfold All_def)
apply (rule eqTrueE)
apply (erule fun_cong)
done

lemma allE:
  assumes major: "ALL x. P(x)"
      and minor: "P(x) ==> R"
  shows "R"
by (rules intro: minor major [THEN spec])

lemma all_dupE:
  assumes major: "ALL x. P(x)"
      and minor: "[| P(x); ALL x. P(x) |] ==> R"
  shows "R"
by (rules intro: minor major major [THEN spec])


subsection {*False*}
(*Depends upon spec; it is impossible to do propositional logic before quantifiers!*)

lemma FalseE: "False ==> P"
apply (unfold False_def)
apply (erule spec)
done

lemma False_neq_True: "False=True ==> P"
by (erule eqTrueE [THEN FalseE])


subsection {*Negation*}

lemma notI:
  assumes p: "P ==> False"
  shows "~P"
apply (unfold not_def)
apply (rules intro: impI p)
done

lemma False_not_True: "False ~= True"
apply (rule notI)
apply (erule False_neq_True)
done

lemma True_not_False: "True ~= False"
apply (rule notI)
apply (drule sym)
apply (erule False_neq_True)
done

lemma notE: "[| ~P;  P |] ==> R"
apply (unfold not_def)
apply (erule mp [THEN FalseE])
apply assumption
done

(* Alternative ~ introduction rule: [| P ==> ~ Pa; P ==> Pa |] ==> ~ P *)
lemmas notI2 = notE [THEN notI, standard]


subsection {*Implication*}

lemma impE:
  assumes "P-->Q" "P" "Q ==> R"
  shows "R"
by (rules intro: prems mp)

(* Reduces Q to P-->Q, allowing substitution in P. *)
lemma rev_mp: "[| P;  P --> Q |] ==> Q"
by (rules intro: mp)

lemma contrapos_nn:
  assumes major: "~Q"
      and minor: "P==>Q"
  shows "~P"
by (rules intro: notI minor major [THEN notE])

(*not used at all, but we already have the other 3 combinations *)
lemma contrapos_pn:
  assumes major: "Q"
      and minor: "P ==> ~Q"
  shows "~P"
by (rules intro: notI minor major notE)

lemma not_sym: "t ~= s ==> s ~= t"
apply (erule contrapos_nn)
apply (erule sym)
done

(*still used in HOLCF*)
lemma rev_contrapos:
  assumes pq: "P ==> Q"
      and nq: "~Q"
  shows "~P"
apply (rule nq [THEN contrapos_nn])
apply (erule pq)
done

subsection {*Existential quantifier*}

lemma exI: "P x ==> EX x::'a. P x"
apply (unfold Ex_def)
apply (rules intro: allI allE impI mp)
done

lemma exE:
  assumes major: "EX x::'a. P(x)"
      and minor: "!!x. P(x) ==> Q"
  shows "Q"
apply (rule major [unfolded Ex_def, THEN spec, THEN mp])
apply (rules intro: impI [THEN allI] minor)
done


subsection {*Conjunction*}

lemma conjI: "[| P; Q |] ==> P&Q"
apply (unfold and_def)
apply (rules intro: impI [THEN allI] mp)
done

lemma conjunct1: "[| P & Q |] ==> P"
apply (unfold and_def)
apply (rules intro: impI dest: spec mp)
done

lemma conjunct2: "[| P & Q |] ==> Q"
apply (unfold and_def)
apply (rules intro: impI dest: spec mp)
done

lemma conjE:
  assumes major: "P&Q"
      and minor: "[| P; Q |] ==> R"
  shows "R"
apply (rule minor)
apply (rule major [THEN conjunct1])
apply (rule major [THEN conjunct2])
done

lemma context_conjI:
  assumes prems: "P" "P ==> Q" shows "P & Q"
by (rules intro: conjI prems)


subsection {*Disjunction*}

lemma disjI1: "P ==> P|Q"
apply (unfold or_def)
apply (rules intro: allI impI mp)
done

lemma disjI2: "Q ==> P|Q"
apply (unfold or_def)
apply (rules intro: allI impI mp)
done

lemma disjE:
  assumes major: "P|Q"
      and minorP: "P ==> R"
      and minorQ: "Q ==> R"
  shows "R"
by (rules intro: minorP minorQ impI
                 major [unfolded or_def, THEN spec, THEN mp, THEN mp])


subsection {*Classical logic*}


lemma classical:
  assumes prem: "~P ==> P"
  shows "P"
apply (rule True_or_False [THEN disjE, THEN eqTrueE])
apply assumption
apply (rule notI [THEN prem, THEN eqTrueI])
apply (erule subst)
apply assumption
done

lemmas ccontr = FalseE [THEN classical, standard]

(*notE with premises exchanged; it discharges ~R so that it can be used to
  make elimination rules*)
lemma rev_notE:
  assumes premp: "P"
      and premnot: "~R ==> ~P"
  shows "R"
apply (rule ccontr)
apply (erule notE [OF premnot premp])
done

(*Double negation law*)
lemma notnotD: "~~P ==> P"
apply (rule classical)
apply (erule notE)
apply assumption
done

lemma contrapos_pp:
  assumes p1: "Q"
      and p2: "~P ==> ~Q"
  shows "P"
by (rules intro: classical p1 p2 notE)


subsection {*Unique existence*}

lemma ex1I:
  assumes prems: "P a" "!!x. P(x) ==> x=a"
  shows "EX! x. P(x)"
by (unfold Ex1_def, rules intro: prems exI conjI allI impI)

text{*Sometimes easier to use: the premises have no shared variables.  Safe!*}
lemma ex_ex1I:
  assumes ex_prem: "EX x. P(x)"
      and eq: "!!x y. [| P(x); P(y) |] ==> x=y"
  shows "EX! x. P(x)"
by (rules intro: ex_prem [THEN exE] ex1I eq)

lemma ex1E:
  assumes major: "EX! x. P(x)"
      and minor: "!!x. [| P(x);  ALL y. P(y) --> y=x |] ==> R"
  shows "R"
apply (rule major [unfolded Ex1_def, THEN exE])
apply (erule conjE)
apply (rules intro: minor)
done

lemma ex1_implies_ex: "EX! x. P x ==> EX x. P x"
apply (erule ex1E)
apply (rule exI)
apply assumption
done


subsection {*THE: definite description operator*}

lemma the_equality:
  assumes prema: "P a"
      and premx: "!!x. P x ==> x=a"
  shows "(THE x. P x) = a"
apply (rule trans [OF _ the_eq_trivial])
apply (rule_tac f = "The" in arg_cong)
apply (rule ext)
apply (rule iffI)
 apply (erule premx)
apply (erule ssubst, rule prema)
done

lemma theI:
  assumes "P a" and "!!x. P x ==> x=a"
  shows "P (THE x. P x)"
by (rules intro: prems the_equality [THEN ssubst])

lemma theI': "EX! x. P x ==> P (THE x. P x)"
apply (erule ex1E)
apply (erule theI)
apply (erule allE)
apply (erule mp)
apply assumption
done

(*Easier to apply than theI: only one occurrence of P*)
lemma theI2:
  assumes "P a" "!!x. P x ==> x=a" "!!x. P x ==> Q x"
  shows "Q (THE x. P x)"
by (rules intro: prems theI)

lemma the1_equality: "[| EX!x. P x; P a |] ==> (THE x. P x) = a"
apply (rule the_equality)
apply  assumption
apply (erule ex1E)
apply (erule all_dupE)
apply (drule mp)
apply  assumption
apply (erule ssubst)
apply (erule allE)
apply (erule mp)
apply assumption
done

lemma the_sym_eq_trivial: "(THE y. x=y) = x"
apply (rule the_equality)
apply (rule refl)
apply (erule sym)
done


subsection {*Classical intro rules for disjunction and existential quantifiers*}

lemma disjCI:
  assumes "~Q ==> P" shows "P|Q"
apply (rule classical)
apply (rules intro: prems disjI1 disjI2 notI elim: notE)
done

lemma excluded_middle: "~P | P"
by (rules intro: disjCI)

text{*case distinction as a natural deduction rule. Note that @{term "~P"}
   is the second case, not the first.*}
lemma case_split_thm:
  assumes prem1: "P ==> Q"
      and prem2: "~P ==> Q"
  shows "Q"
apply (rule excluded_middle [THEN disjE])
apply (erule prem2)
apply (erule prem1)
done

(*Classical implies (-->) elimination. *)
lemma impCE:
  assumes major: "P-->Q"
      and minor: "~P ==> R" "Q ==> R"
  shows "R"
apply (rule excluded_middle [of P, THEN disjE])
apply (rules intro: minor major [THEN mp])+
done

(*This version of --> elimination works on Q before P.  It works best for
  those cases in which P holds "almost everywhere".  Can't install as
  default: would break old proofs.*)
lemma impCE':
  assumes major: "P-->Q"
      and minor: "Q ==> R" "~P ==> R"
  shows "R"
apply (rule excluded_middle [of P, THEN disjE])
apply (rules intro: minor major [THEN mp])+
done

(*Classical <-> elimination. *)
lemma iffCE:
  assumes major: "P=Q"
      and minor: "[| P; Q |] ==> R"  "[| ~P; ~Q |] ==> R"
  shows "R"
apply (rule major [THEN iffE])
apply (rules intro: minor elim: impCE notE)
done

lemma exCI:
  assumes "ALL x. ~P(x) ==> P(a)"
  shows "EX x. P(x)"
apply (rule ccontr)
apply (rules intro: prems exI allI notI notE [of "\<exists>x. P x"])
done



subsection {* Theory and package setup *}

ML
{*
val plusI = thm "plusI"
val minusI = thm "minusI"
val timesI = thm "timesI"
val eq_reflection = thm "eq_reflection"
val refl = thm "refl"
val subst = thm "subst"
val ext = thm "ext"
val impI = thm "impI"
val mp = thm "mp"
val True_def = thm "True_def"
val All_def = thm "All_def"
val Ex_def = thm "Ex_def"
val False_def = thm "False_def"
val not_def = thm "not_def"
val and_def = thm "and_def"
val or_def = thm "or_def"
val Ex1_def = thm "Ex1_def"
val iff = thm "iff"
val True_or_False = thm "True_or_False"
val Let_def = thm "Let_def"
val if_def = thm "if_def"
val sym = thm "sym"
val ssubst = thm "ssubst"
val trans = thm "trans"
val def_imp_eq = thm "def_imp_eq"
val box_equals = thm "box_equals"
val fun_cong = thm "fun_cong"
val arg_cong = thm "arg_cong"
val cong = thm "cong"
val iffI = thm "iffI"
val iffD2 = thm "iffD2"
val rev_iffD2 = thm "rev_iffD2"
val iffD1 = thm "iffD1"
val rev_iffD1 = thm "rev_iffD1"
val iffE = thm "iffE"
val TrueI = thm "TrueI"
val eqTrueI = thm "eqTrueI"
val eqTrueE = thm "eqTrueE"
val allI = thm "allI"
val spec = thm "spec"
val allE = thm "allE"
val all_dupE = thm "all_dupE"
val FalseE = thm "FalseE"
val False_neq_True = thm "False_neq_True"
val notI = thm "notI"
val False_not_True = thm "False_not_True"
val True_not_False = thm "True_not_False"
val notE = thm "notE"
val notI2 = thm "notI2"
val impE = thm "impE"
val rev_mp = thm "rev_mp"
val contrapos_nn = thm "contrapos_nn"
val contrapos_pn = thm "contrapos_pn"
val not_sym = thm "not_sym"
val rev_contrapos = thm "rev_contrapos"
val exI = thm "exI"
val exE = thm "exE"
val conjI = thm "conjI"
val conjunct1 = thm "conjunct1"
val conjunct2 = thm "conjunct2"
val conjE = thm "conjE"
val context_conjI = thm "context_conjI"
val disjI1 = thm "disjI1"
val disjI2 = thm "disjI2"
val disjE = thm "disjE"
val classical = thm "classical"
val ccontr = thm "ccontr"
val rev_notE = thm "rev_notE"
val notnotD = thm "notnotD"
val contrapos_pp = thm "contrapos_pp"
val ex1I = thm "ex1I"
val ex_ex1I = thm "ex_ex1I"
val ex1E = thm "ex1E"
val ex1_implies_ex = thm "ex1_implies_ex"
val the_equality = thm "the_equality"
val theI = thm "theI"
val theI' = thm "theI'"
val theI2 = thm "theI2"
val the1_equality = thm "the1_equality"
val the_sym_eq_trivial = thm "the_sym_eq_trivial"
val disjCI = thm "disjCI"
val excluded_middle = thm "excluded_middle"
val case_split_thm = thm "case_split_thm"
val impCE = thm "impCE"
val impCE = thm "impCE"
val iffCE = thm "iffCE"
val exCI = thm "exCI"

(* combination of (spec RS spec RS ...(j times) ... spec RS mp) *)
local
  fun wrong_prem (Const ("All", _) $ (Abs (_, _, t))) = wrong_prem t
  |   wrong_prem (Bound _) = true
  |   wrong_prem _ = false
  val filter_right = filter (fn t => not (wrong_prem (HOLogic.dest_Trueprop (hd (Thm.prems_of t)))))
in
  fun smp i = funpow i (fn m => filter_right ([spec] RL m)) ([mp])
  fun smp_tac j = EVERY'[dresolve_tac (smp j), atac]
end


fun strip_tac i = REPEAT(resolve_tac [impI,allI] i)

(*Obsolete form of disjunctive case analysis*)
fun excluded_middle_tac sP =
    res_inst_tac [("Q",sP)] (excluded_middle RS disjE)

fun case_tac a = res_inst_tac [("P",a)] case_split_thm
*}

theorems case_split = case_split_thm [case_names True False]


subsubsection {* Intuitionistic Reasoning *}

lemma impE':
  assumes 1: "P --> Q"
    and 2: "Q ==> R"
    and 3: "P --> Q ==> P"
  shows R
proof -
  from 3 and 1 have P .
  with 1 have Q by (rule impE)
  with 2 show R .
qed

lemma allE':
  assumes 1: "ALL x. P x"
    and 2: "P x ==> ALL x. P x ==> Q"
  shows Q
proof -
  from 1 have "P x" by (rule spec)
  from this and 1 show Q by (rule 2)
qed

lemma notE':
  assumes 1: "~ P"
    and 2: "~ P ==> P"
  shows R
proof -
  from 2 and 1 have P .
  with 1 show R by (rule notE)
qed

lemmas [CPure.elim!] = disjE iffE FalseE conjE exE
  and [CPure.intro!] = iffI conjI impI TrueI notI allI refl
  and [CPure.elim 2] = allE notE' impE'
  and [CPure.intro] = exI disjI2 disjI1

lemmas [trans] = trans
  and [sym] = sym not_sym
  and [CPure.elim?] = iffD1 iffD2 impE


subsubsection {* Atomizing meta-level connectives *}

lemma atomize_all [atomize]: "(!!x. P x) == Trueprop (ALL x. P x)"
proof
  assume "!!x. P x"
  show "ALL x. P x" by (rule allI)
next
  assume "ALL x. P x"
  thus "!!x. P x" by (rule allE)
qed

lemma atomize_imp [atomize]: "(A ==> B) == Trueprop (A --> B)"
proof
  assume r: "A ==> B"
  show "A --> B" by (rule impI) (rule r)
next
  assume "A --> B" and A
  thus B by (rule mp)
qed

lemma atomize_not: "(A ==> False) == Trueprop (~A)"
proof
  assume r: "A ==> False"
  show "~A" by (rule notI) (rule r)
next
  assume "~A" and A
  thus False by (rule notE)
qed

lemma atomize_eq [atomize]: "(x == y) == Trueprop (x = y)"
proof
  assume "x == y"
  show "x = y" by (unfold prems) (rule refl)
next
  assume "x = y"
  thus "x == y" by (rule eq_reflection)
qed

lemma atomize_conj [atomize]:
  "(!!C. (A ==> B ==> PROP C) ==> PROP C) == Trueprop (A & B)"
proof
  assume "!!C. (A ==> B ==> PROP C) ==> PROP C"
  show "A & B" by (rule conjI)
next
  fix C
  assume "A & B"
  assume "A ==> B ==> PROP C"
  thus "PROP C"
  proof this
    show A by (rule conjunct1)
    show B by (rule conjunct2)
  qed
qed

lemmas [symmetric, rulify] = atomize_all atomize_imp


subsubsection {* Classical Reasoner setup *}

use "cladata.ML"
setup hypsubst_setup

ML_setup {*
  Context.>> (ContextRules.addSWrapper (fn tac => hyp_subst_tac' ORELSE' tac));
*}

setup Classical.setup
setup clasetup

lemmas [intro?] = ext
  and [elim?] = ex1_implies_ex

use "blastdata.ML"
setup Blast.setup


subsubsection {* Simplifier setup *}

lemma meta_eq_to_obj_eq: "x == y ==> x = y"
proof -
  assume r: "x == y"
  show "x = y" by (unfold r) (rule refl)
qed

lemma eta_contract_eq: "(%s. f s) = f" ..

lemma simp_thms:
  shows not_not: "(~ ~ P) = P"
  and Not_eq_iff: "((~P) = (~Q)) = (P = Q)"
  and
    "(P ~= Q) = (P = (~Q))"
    "(P | ~P) = True"    "(~P | P) = True"
    "(x = x) = True"
    "(~True) = False"  "(~False) = True"
    "(~P) ~= P"  "P ~= (~P)"
    "(True=P) = P"  "(P=True) = P"  "(False=P) = (~P)"  "(P=False) = (~P)"
    "(True --> P) = P"  "(False --> P) = True"
    "(P --> True) = True"  "(P --> P) = True"
    "(P --> False) = (~P)"  "(P --> ~P) = (~P)"
    "(P & True) = P"  "(True & P) = P"
    "(P & False) = False"  "(False & P) = False"
    "(P & P) = P"  "(P & (P & Q)) = (P & Q)"
    "(P & ~P) = False"    "(~P & P) = False"
    "(P | True) = True"  "(True | P) = True"
    "(P | False) = P"  "(False | P) = P"
    "(P | P) = P"  "(P | (P | Q)) = (P | Q)" and
    "(ALL x. P) = P"  "(EX x. P) = P"  "EX x. x=t"  "EX x. t=x"
    -- {* needed for the one-point-rule quantifier simplification procs *}
    -- {* essential for termination!! *} and
    "!!P. (EX x. x=t & P(x)) = P(t)"
    "!!P. (EX x. t=x & P(x)) = P(t)"
    "!!P. (ALL x. x=t --> P(x)) = P(t)"
    "!!P. (ALL x. t=x --> P(x)) = P(t)"
  by (blast, blast, blast, blast, blast, rules+)

lemma imp_cong: "(P = P') ==> (P' ==> (Q = Q')) ==> ((P --> Q) = (P' --> Q'))"
  by rules

lemma ex_simps:
  "!!P Q. (EX x. P x & Q)   = ((EX x. P x) & Q)"
  "!!P Q. (EX x. P & Q x)   = (P & (EX x. Q x))"
  "!!P Q. (EX x. P x | Q)   = ((EX x. P x) | Q)"
  "!!P Q. (EX x. P | Q x)   = (P | (EX x. Q x))"
  "!!P Q. (EX x. P x --> Q) = ((ALL x. P x) --> Q)"
  "!!P Q. (EX x. P --> Q x) = (P --> (EX x. Q x))"
  -- {* Miniscoping: pushing in existential quantifiers. *}
  by (rules | blast)+

lemma all_simps:
  "!!P Q. (ALL x. P x & Q)   = ((ALL x. P x) & Q)"
  "!!P Q. (ALL x. P & Q x)   = (P & (ALL x. Q x))"
  "!!P Q. (ALL x. P x | Q)   = ((ALL x. P x) | Q)"
  "!!P Q. (ALL x. P | Q x)   = (P | (ALL x. Q x))"
  "!!P Q. (ALL x. P x --> Q) = ((EX x. P x) --> Q)"
  "!!P Q. (ALL x. P --> Q x) = (P --> (ALL x. Q x))"
  -- {* Miniscoping: pushing in universal quantifiers. *}
  by (rules | blast)+

lemma disj_absorb: "(A | A) = A"
  by blast

lemma disj_left_absorb: "(A | (A | B)) = (A | B)"
  by blast

lemma conj_absorb: "(A & A) = A"
  by blast

lemma conj_left_absorb: "(A & (A & B)) = (A & B)"
  by blast

lemma eq_ac:
  shows eq_commute: "(a=b) = (b=a)"
    and eq_left_commute: "(P=(Q=R)) = (Q=(P=R))"
    and eq_assoc: "((P=Q)=R) = (P=(Q=R))" by (rules, blast+)
lemma neq_commute: "(a~=b) = (b~=a)" by rules

lemma conj_comms:
  shows conj_commute: "(P&Q) = (Q&P)"
    and conj_left_commute: "(P&(Q&R)) = (Q&(P&R))" by rules+
lemma conj_assoc: "((P&Q)&R) = (P&(Q&R))" by rules

lemma disj_comms:
  shows disj_commute: "(P|Q) = (Q|P)"
    and disj_left_commute: "(P|(Q|R)) = (Q|(P|R))" by rules+
lemma disj_assoc: "((P|Q)|R) = (P|(Q|R))" by rules

lemma conj_disj_distribL: "(P&(Q|R)) = (P&Q | P&R)" by rules
lemma conj_disj_distribR: "((P|Q)&R) = (P&R | Q&R)" by rules

lemma disj_conj_distribL: "(P|(Q&R)) = ((P|Q) & (P|R))" by rules
lemma disj_conj_distribR: "((P&Q)|R) = ((P|R) & (Q|R))" by rules

lemma imp_conjR: "(P --> (Q&R)) = ((P-->Q) & (P-->R))" by rules
lemma imp_conjL: "((P&Q) -->R)  = (P --> (Q --> R))" by rules
lemma imp_disjL: "((P|Q) --> R) = ((P-->R)&(Q-->R))" by rules

text {* These two are specialized, but @{text imp_disj_not1} is useful in @{text "Auth/Yahalom"}. *}
lemma imp_disj_not1: "(P --> Q | R) = (~Q --> P --> R)" by blast
lemma imp_disj_not2: "(P --> Q | R) = (~R --> P --> Q)" by blast

lemma imp_disj1: "((P-->Q)|R) = (P--> Q|R)" by blast
lemma imp_disj2: "(Q|(P-->R)) = (P--> Q|R)" by blast

lemma de_Morgan_disj: "(~(P | Q)) = (~P & ~Q)" by rules
lemma de_Morgan_conj: "(~(P & Q)) = (~P | ~Q)" by blast
lemma not_imp: "(~(P --> Q)) = (P & ~Q)" by blast
lemma not_iff: "(P~=Q) = (P = (~Q))" by blast
lemma disj_not1: "(~P | Q) = (P --> Q)" by blast
lemma disj_not2: "(P | ~Q) = (Q --> P)"  -- {* changes orientation :-( *}
  by blast
lemma imp_conv_disj: "(P --> Q) = ((~P) | Q)" by blast

lemma iff_conv_conj_imp: "(P = Q) = ((P --> Q) & (Q --> P))" by rules


lemma cases_simp: "((P --> Q) & (~P --> Q)) = Q"
  -- {* Avoids duplication of subgoals after @{text split_if}, when the true and false *}
  -- {* cases boil down to the same thing. *}
  by blast

lemma not_all: "(~ (! x. P(x))) = (? x.~P(x))" by blast
lemma imp_all: "((! x. P x) --> Q) = (? x. P x --> Q)" by blast
lemma not_ex: "(~ (? x. P(x))) = (! x.~P(x))" by rules
lemma imp_ex: "((? x. P x) --> Q) = (! x. P x --> Q)" by rules

lemma ex_disj_distrib: "(? x. P(x) | Q(x)) = ((? x. P(x)) | (? x. Q(x)))" by rules
lemma all_conj_distrib: "(!x. P(x) & Q(x)) = ((! x. P(x)) & (! x. Q(x)))" by rules

text {*
  \medskip The @{text "&"} congruence rule: not included by default!
  May slow rewrite proofs down by as much as 50\% *}

lemma conj_cong:
    "(P = P') ==> (P' ==> (Q = Q')) ==> ((P & Q) = (P' & Q'))"
  by rules

lemma rev_conj_cong:
    "(Q = Q') ==> (Q' ==> (P = P')) ==> ((P & Q) = (P' & Q'))"
  by rules

text {* The @{text "|"} congruence rule: not included by default! *}

lemma disj_cong:
    "(P = P') ==> (~P' ==> (Q = Q')) ==> ((P | Q) = (P' | Q'))"
  by blast

lemma eq_sym_conv: "(x = y) = (y = x)"
  by rules


text {* \medskip if-then-else rules *}

lemma if_True: "(if True then x else y) = x"
  by (unfold if_def) blast

lemma if_False: "(if False then x else y) = y"
  by (unfold if_def) blast

lemma if_P: "P ==> (if P then x else y) = x"
  by (unfold if_def) blast

lemma if_not_P: "~P ==> (if P then x else y) = y"
  by (unfold if_def) blast

lemma split_if: "P (if Q then x else y) = ((Q --> P(x)) & (~Q --> P(y)))"
  apply (rule case_split [of Q])
   apply (subst if_P)
    prefer 3 apply (subst if_not_P, blast+)
  done

lemma split_if_asm: "P (if Q then x else y) = (~((Q & ~P x) | (~Q & ~P y)))"
by (subst split_if, blast)

lemmas if_splits = split_if split_if_asm

lemma if_def2: "(if Q then x else y) = ((Q --> x) & (~ Q --> y))"
  by (rule split_if)

lemma if_cancel: "(if c then x else x) = x"
by (subst split_if, blast)

lemma if_eq_cancel: "(if x = y then y else x) = x"
by (subst split_if, blast)

lemma if_bool_eq_conj: "(if P then Q else R) = ((P-->Q) & (~P-->R))"
  -- {* This form is useful for expanding @{text if}s on the RIGHT of the @{text "==>"} symbol. *}
  by (rule split_if)

lemma if_bool_eq_disj: "(if P then Q else R) = ((P&Q) | (~P&R))"
  -- {* And this form is useful for expanding @{text if}s on the LEFT. *}
  apply (subst split_if, blast)
  done

lemma Eq_TrueI: "P ==> P == True" by (unfold atomize_eq) rules
lemma Eq_FalseI: "~P ==> P == False" by (unfold atomize_eq) rules

text {* \medskip let rules for simproc *}

lemma Let_folded: "f x \<equiv> g x \<Longrightarrow>  Let x f \<equiv> Let x g"
  by (unfold Let_def)

lemma Let_unfold: "f x \<equiv> g \<Longrightarrow>  Let x f \<equiv> g"
  by (unfold Let_def)

subsubsection {* Actual Installation of the Simplifier *}

use "simpdata.ML"
setup Simplifier.setup
setup "Simplifier.method_setup Splitter.split_modifiers" setup simpsetup
setup Splitter.setup setup Clasimp.setup

declare disj_absorb [simp] conj_absorb [simp]

lemma ex1_eq[iff]: "EX! x. x = t" "EX! x. t = x"
by blast+

theorem choice_eq: "(ALL x. EX! y. P x y) = (EX! f. ALL x. P x (f x))"
  apply (rule iffI)
  apply (rule_tac a = "%x. THE y. P x y" in ex1I)
  apply (fast dest!: theI')
  apply (fast intro: ext the1_equality [symmetric])
  apply (erule ex1E)
  apply (rule allI)
  apply (rule ex1I)
  apply (erule spec)
  apply (erule_tac x = "%z. if z = x then y else f z" in allE)
  apply (erule impE)
  apply (rule allI)
  apply (rule_tac P = "xa = x" in case_split_thm)
  apply (drule_tac [3] x = x in fun_cong, simp_all)
  done

text{*Needs only HOL-lemmas:*}
lemma mk_left_commute:
  assumes a: "\<And>x y z. f (f x y) z = f x (f y z)" and
          c: "\<And>x y. f x y = f y x"
  shows "f x (f y z) = f y (f x z)"
by(rule trans[OF trans[OF c a] arg_cong[OF c, of "f y"]])


subsubsection {* Generic cases and induction *}

constdefs
  induct_forall :: "('a => bool) => bool"
  "induct_forall P == \<forall>x. P x"
  induct_implies :: "bool => bool => bool"
  "induct_implies A B == A --> B"
  induct_equal :: "'a => 'a => bool"
  "induct_equal x y == x = y"
  induct_conj :: "bool => bool => bool"
  "induct_conj A B == A & B"

lemma induct_forall_eq: "(!!x. P x) == Trueprop (induct_forall (\<lambda>x. P x))"
  by (simp only: atomize_all induct_forall_def)

lemma induct_implies_eq: "(A ==> B) == Trueprop (induct_implies A B)"
  by (simp only: atomize_imp induct_implies_def)

lemma induct_equal_eq: "(x == y) == Trueprop (induct_equal x y)"
  by (simp only: atomize_eq induct_equal_def)

lemma induct_forall_conj: "induct_forall (\<lambda>x. induct_conj (A x) (B x)) =
    induct_conj (induct_forall A) (induct_forall B)"
  by (unfold induct_forall_def induct_conj_def) rules

lemma induct_implies_conj: "induct_implies C (induct_conj A B) =
    induct_conj (induct_implies C A) (induct_implies C B)"
  by (unfold induct_implies_def induct_conj_def) rules

lemma induct_conj_curry: "(induct_conj A B ==> PROP C) == (A ==> B ==> PROP C)"
proof
  assume r: "induct_conj A B ==> PROP C" and A B
  show "PROP C" by (rule r) (simp! add: induct_conj_def)
next
  assume r: "A ==> B ==> PROP C" and "induct_conj A B"
  show "PROP C" by (rule r) (simp! add: induct_conj_def)+
qed

lemma induct_impliesI: "(A ==> B) ==> induct_implies A B"
  by (simp add: induct_implies_def)

lemmas induct_atomize = atomize_conj induct_forall_eq induct_implies_eq induct_equal_eq
lemmas induct_rulify1 [symmetric, standard] = induct_forall_eq induct_implies_eq induct_equal_eq
lemmas induct_rulify2 = induct_forall_def induct_implies_def induct_equal_def induct_conj_def
lemmas induct_conj = induct_forall_conj induct_implies_conj induct_conj_curry

hide const induct_forall induct_implies induct_equal induct_conj


text {* Method setup. *}

ML {*
  structure InductMethod = InductMethodFun
  (struct
    val dest_concls = HOLogic.dest_concls
    val cases_default = thm "case_split"
    val local_impI = thm "induct_impliesI"
    val conjI = thm "conjI"
    val atomize = thms "induct_atomize"
    val rulify1 = thms "induct_rulify1"
    val rulify2 = thms "induct_rulify2"
    val localize = [Thm.symmetric (thm "induct_implies_def")]
  end);
*}

setup InductMethod.setup


subsection {* Order signatures and orders *}

axclass
  ord < type

syntax
  "op <"        :: "['a::ord, 'a] => bool"             ("op <")
  "op <="       :: "['a::ord, 'a] => bool"             ("op <=")

global

consts
  "op <"        :: "['a::ord, 'a] => bool"             ("(_/ < _)"  [50, 51] 50)
  "op <="       :: "['a::ord, 'a] => bool"             ("(_/ <= _)" [50, 51] 50)

local

syntax (xsymbols)
  "op <="       :: "['a::ord, 'a] => bool"             ("op \<le>")
  "op <="       :: "['a::ord, 'a] => bool"             ("(_/ \<le> _)"  [50, 51] 50)

syntax (HTML output)
  "op <="       :: "['a::ord, 'a] => bool"             ("op \<le>")
  "op <="       :: "['a::ord, 'a] => bool"             ("(_/ \<le> _)"  [50, 51] 50)

text{* Syntactic sugar: *}

consts
  "_gt" :: "'a::ord => 'a => bool"             (infixl ">" 50)
  "_ge" :: "'a::ord => 'a => bool"             (infixl ">=" 50)
translations
  "x > y"  => "y < x"
  "x >= y" => "y <= x"

syntax (xsymbols)
  "_ge"       :: "'a::ord => 'a => bool"             (infixl "\<ge>" 50)

syntax (HTML output)
  "_ge"       :: "['a::ord, 'a] => bool"             (infixl "\<ge>" 50)


subsubsection {* Monotonicity *}

locale mono =
  fixes f
  assumes mono: "A <= B ==> f A <= f B"

lemmas monoI [intro?] = mono.intro
  and monoD [dest?] = mono.mono

constdefs
  min :: "['a::ord, 'a] => 'a"
  "min a b == (if a <= b then a else b)"
  max :: "['a::ord, 'a] => 'a"
  "max a b == (if a <= b then b else a)"

lemma min_leastL: "(!!x. least <= x) ==> min least x = least"
  by (simp add: min_def)

lemma min_of_mono:
    "ALL x y. (f x <= f y) = (x <= y) ==> min (f m) (f n) = f (min m n)"
  by (simp add: min_def)

lemma max_leastL: "(!!x. least <= x) ==> max least x = x"
  by (simp add: max_def)

lemma max_of_mono:
    "ALL x y. (f x <= f y) = (x <= y) ==> max (f m) (f n) = f (max m n)"
  by (simp add: max_def)


subsubsection "Orders"

axclass order < ord
  order_refl [iff]: "x <= x"
  order_trans: "x <= y ==> y <= z ==> x <= z"
  order_antisym: "x <= y ==> y <= x ==> x = y"
  order_less_le: "(x < y) = (x <= y & x ~= y)"


text {* Reflexivity. *}

lemma order_eq_refl: "!!x::'a::order. x = y ==> x <= y"
    -- {* This form is useful with the classical reasoner. *}
  apply (erule ssubst)
  apply (rule order_refl)
  done

lemma order_less_irrefl [iff]: "~ x < (x::'a::order)"
  by (simp add: order_less_le)

lemma order_le_less: "((x::'a::order) <= y) = (x < y | x = y)"
    -- {* NOT suitable for iff, since it can cause PROOF FAILED. *}
  apply (simp add: order_less_le, blast)
  done

lemmas order_le_imp_less_or_eq = order_le_less [THEN iffD1, standard]

lemma order_less_imp_le: "!!x::'a::order. x < y ==> x <= y"
  by (simp add: order_less_le)


text {* Asymmetry. *}

lemma order_less_not_sym: "(x::'a::order) < y ==> ~ (y < x)"
  by (simp add: order_less_le order_antisym)

lemma order_less_asym: "x < (y::'a::order) ==> (~P ==> y < x) ==> P"
  apply (drule order_less_not_sym)
  apply (erule contrapos_np, simp)
  done

lemma order_eq_iff: "!!x::'a::order. (x = y) = (x \<le> y & y \<le> x)"
by (blast intro: order_antisym)

lemma order_antisym_conv: "(y::'a::order) <= x ==> (x <= y) = (x = y)"
by(blast intro:order_antisym)

text {* Transitivity. *}

lemma order_less_trans: "!!x::'a::order. [| x < y; y < z |] ==> x < z"
  apply (simp add: order_less_le)
  apply (blast intro: order_trans order_antisym)
  done

lemma order_le_less_trans: "!!x::'a::order. [| x <= y; y < z |] ==> x < z"
  apply (simp add: order_less_le)
  apply (blast intro: order_trans order_antisym)
  done

lemma order_less_le_trans: "!!x::'a::order. [| x < y; y <= z |] ==> x < z"
  apply (simp add: order_less_le)
  apply (blast intro: order_trans order_antisym)
  done


text {* Useful for simplification, but too risky to include by default. *}

lemma order_less_imp_not_less: "(x::'a::order) < y ==>  (~ y < x) = True"
  by (blast elim: order_less_asym)

lemma order_less_imp_triv: "(x::'a::order) < y ==>  (y < x --> P) = True"
  by (blast elim: order_less_asym)

lemma order_less_imp_not_eq: "(x::'a::order) < y ==>  (x = y) = False"
  by auto

lemma order_less_imp_not_eq2: "(x::'a::order) < y ==>  (y = x) = False"
  by auto


text {* Other operators. *}

lemma min_leastR: "(!!x::'a::order. least <= x) ==> min x least = least"
  apply (simp add: min_def)
  apply (blast intro: order_antisym)
  done

lemma max_leastR: "(!!x::'a::order. least <= x) ==> max x least = x"
  apply (simp add: max_def)
  apply (blast intro: order_antisym)
  done


subsubsection {* Least value operator *}

constdefs
  Least :: "('a::ord => bool) => 'a"               (binder "LEAST " 10)
  "Least P == THE x. P x & (ALL y. P y --> x <= y)"
    -- {* We can no longer use LeastM because the latter requires Hilbert-AC. *}

lemma LeastI2:
  "[| P (x::'a::order);
      !!y. P y ==> x <= y;
      !!x. [| P x; ALL y. P y --> x \<le> y |] ==> Q x |]
   ==> Q (Least P)"
  apply (unfold Least_def)
  apply (rule theI2)
    apply (blast intro: order_antisym)+
  done

lemma Least_equality:
    "[| P (k::'a::order); !!x. P x ==> k <= x |] ==> (LEAST x. P x) = k"
  apply (simp add: Least_def)
  apply (rule the_equality)
  apply (auto intro!: order_antisym)
  done


subsubsection "Linear / total orders"

axclass linorder < order
  linorder_linear: "x <= y | y <= x"

lemma linorder_less_linear: "!!x::'a::linorder. x<y | x=y | y<x"
  apply (simp add: order_less_le)
  apply (insert linorder_linear, blast)
  done

lemma linorder_le_less_linear: "!!x::'a::linorder. x\<le>y | y<x"
  by (simp add: order_le_less linorder_less_linear)

lemma linorder_le_cases [case_names le ge]:
    "((x::'a::linorder) \<le> y ==> P) ==> (y \<le> x ==> P) ==> P"
  by (insert linorder_linear, blast)

lemma linorder_cases [case_names less equal greater]:
    "((x::'a::linorder) < y ==> P) ==> (x = y ==> P) ==> (y < x ==> P) ==> P"
  by (insert linorder_less_linear, blast)

lemma linorder_not_less: "!!x::'a::linorder. (~ x < y) = (y <= x)"
  apply (simp add: order_less_le)
  apply (insert linorder_linear)
  apply (blast intro: order_antisym)
  done

lemma linorder_not_le: "!!x::'a::linorder. (~ x <= y) = (y < x)"
  apply (simp add: order_less_le)
  apply (insert linorder_linear)
  apply (blast intro: order_antisym)
  done

lemma linorder_neq_iff: "!!x::'a::linorder. (x ~= y) = (x<y | y<x)"
by (cut_tac x = x and y = y in linorder_less_linear, auto)

lemma linorder_neqE: "x ~= (y::'a::linorder) ==> (x < y ==> R) ==> (y < x ==> R) ==> R"
by (simp add: linorder_neq_iff, blast)

lemma linorder_antisym_conv1: "~ (x::'a::linorder) < y ==> (x <= y) = (x = y)"
by(blast intro:order_antisym dest:linorder_not_less[THEN iffD1])

lemma linorder_antisym_conv2: "(x::'a::linorder) <= y ==> (~ x < y) = (x = y)"
by(blast intro:order_antisym dest:linorder_not_less[THEN iffD1])

lemma linorder_antisym_conv3: "~ (y::'a::linorder) < x ==> (~ x < y) = (x = y)"
by(blast intro:order_antisym dest:linorder_not_less[THEN iffD1])

use "antisym_setup.ML";
setup antisym_setup

subsubsection "Min and max on (linear) orders"

lemma min_same [simp]: "min (x::'a::order) x = x"
  by (simp add: min_def)

lemma max_same [simp]: "max (x::'a::order) x = x"
  by (simp add: max_def)

lemma le_max_iff_disj: "!!z::'a::linorder. (z <= max x y) = (z <= x | z <= y)"
  apply (simp add: max_def)
  apply (insert linorder_linear)
  apply (blast intro: order_trans)
  done

lemma le_maxI1: "(x::'a::linorder) <= max x y"
  by (simp add: le_max_iff_disj)

lemma le_maxI2: "(y::'a::linorder) <= max x y"
    -- {* CANNOT use with @{text "[intro!]"} because blast will give PROOF FAILED. *}
  by (simp add: le_max_iff_disj)

lemma less_max_iff_disj: "!!z::'a::linorder. (z < max x y) = (z < x | z < y)"
  apply (simp add: max_def order_le_less)
  apply (insert linorder_less_linear)
  apply (blast intro: order_less_trans)
  done

lemma max_le_iff_conj [simp]:
    "!!z::'a::linorder. (max x y <= z) = (x <= z & y <= z)"
  apply (simp add: max_def)
  apply (insert linorder_linear)
  apply (blast intro: order_trans)
  done

lemma max_less_iff_conj [simp]:
    "!!z::'a::linorder. (max x y < z) = (x < z & y < z)"
  apply (simp add: order_le_less max_def)
  apply (insert linorder_less_linear)
  apply (blast intro: order_less_trans)
  done

lemma le_min_iff_conj [simp]:
    "!!z::'a::linorder. (z <= min x y) = (z <= x & z <= y)"
    -- {* @{text "[iff]"} screws up a @{text blast} in MiniML *}
  apply (simp add: min_def)
  apply (insert linorder_linear)
  apply (blast intro: order_trans)
  done

lemma min_less_iff_conj [simp]:
    "!!z::'a::linorder. (z < min x y) = (z < x & z < y)"
  apply (simp add: order_le_less min_def)
  apply (insert linorder_less_linear)
  apply (blast intro: order_less_trans)
  done

lemma min_le_iff_disj: "!!z::'a::linorder. (min x y <= z) = (x <= z | y <= z)"
  apply (simp add: min_def)
  apply (insert linorder_linear)
  apply (blast intro: order_trans)
  done

lemma min_less_iff_disj: "!!z::'a::linorder. (min x y < z) = (x < z | y < z)"
  apply (simp add: min_def order_le_less)
  apply (insert linorder_less_linear)
  apply (blast intro: order_less_trans)
  done

lemma max_assoc: "!!x::'a::linorder. max (max x y) z = max x (max y z)"
apply(simp add:max_def)
apply(rule conjI)
apply(blast intro:order_trans)
apply(simp add:linorder_not_le)
apply(blast dest: order_less_trans order_le_less_trans)
done

lemma max_commute: "!!x::'a::linorder. max x y = max y x"
apply(simp add:max_def)
apply(simp add:linorder_not_le)
apply(blast dest: order_less_trans)
done

lemmas max_ac = max_assoc max_commute
                mk_left_commute[of max,OF max_assoc max_commute]

lemma min_assoc: "!!x::'a::linorder. min (min x y) z = min x (min y z)"
apply(simp add:min_def)
apply(rule conjI)
apply(blast intro:order_trans)
apply(simp add:linorder_not_le)
apply(blast dest: order_less_trans order_le_less_trans)
done

lemma min_commute: "!!x::'a::linorder. min x y = min y x"
apply(simp add:min_def)
apply(simp add:linorder_not_le)
apply(blast dest: order_less_trans)
done

lemmas min_ac = min_assoc min_commute
                mk_left_commute[of min,OF min_assoc min_commute]

lemma split_min:
    "P (min (i::'a::linorder) j) = ((i <= j --> P(i)) & (~ i <= j --> P(j)))"
  by (simp add: min_def)

lemma split_max:
    "P (max (i::'a::linorder) j) = ((i <= j --> P(j)) & (~ i <= j --> P(i)))"
  by (simp add: max_def)


subsubsection {* Transitivity rules for calculational reasoning *}


lemma order_neq_le_trans: "a ~= b ==> (a::'a::order) <= b ==> a < b"
  by (simp add: order_less_le)

lemma order_le_neq_trans: "(a::'a::order) <= b ==> a ~= b ==> a < b"
  by (simp add: order_less_le)

lemma order_less_asym': "(a::'a::order) < b ==> b < a ==> P"
  by (rule order_less_asym)


subsubsection {* Setup of transitivity reasoner as Solver *}

lemma less_imp_neq: "[| (x::'a::order) < y |] ==> x ~= y"
  by (erule contrapos_pn, erule subst, rule order_less_irrefl)

lemma eq_neq_eq_imp_neq: "[| x = a ; a ~= b; b = y |] ==> x ~= y"
  by (erule subst, erule ssubst, assumption)

ML_setup {*

(* The setting up of Quasi_Tac serves as a demo.  Since there is no
   class for quasi orders, the tactics Quasi_Tac.trans_tac and
   Quasi_Tac.quasi_tac are not of much use. *)

fun decomp_gen sort sign (Trueprop $ t) =
  let fun of_sort t = Sign.of_sort sign (type_of t, sort)
  fun dec (Const ("Not", _) $ t) = (
	  case dec t of
	    None => None
	  | Some (t1, rel, t2) => Some (t1, "~" ^ rel, t2))
	| dec (Const ("op =",  _) $ t1 $ t2) =
	    if of_sort t1
	    then Some (t1, "=", t2)
	    else None
	| dec (Const ("op <=",  _) $ t1 $ t2) =
	    if of_sort t1
	    then Some (t1, "<=", t2)
	    else None
	| dec (Const ("op <",  _) $ t1 $ t2) =
	    if of_sort t1
	    then Some (t1, "<", t2)
	    else None
	| dec _ = None
  in dec t end;

structure Quasi_Tac = Quasi_Tac_Fun (
  struct
    val le_trans = thm "order_trans";
    val le_refl = thm "order_refl";
    val eqD1 = thm "order_eq_refl";
    val eqD2 = thm "sym" RS thm "order_eq_refl";
    val less_reflE = thm "order_less_irrefl" RS thm "notE";
    val less_imp_le = thm "order_less_imp_le";
    val le_neq_trans = thm "order_le_neq_trans";
    val neq_le_trans = thm "order_neq_le_trans";
    val less_imp_neq = thm "less_imp_neq";
    val decomp_trans = decomp_gen ["HOL.order"];
    val decomp_quasi = decomp_gen ["HOL.order"];

  end);  (* struct *)

structure Order_Tac = Order_Tac_Fun (
  struct
    val less_reflE = thm "order_less_irrefl" RS thm "notE";
    val le_refl = thm "order_refl";
    val less_imp_le = thm "order_less_imp_le";
    val not_lessI = thm "linorder_not_less" RS thm "iffD2";
    val not_leI = thm "linorder_not_le" RS thm "iffD2";
    val not_lessD = thm "linorder_not_less" RS thm "iffD1";
    val not_leD = thm "linorder_not_le" RS thm "iffD1";
    val eqI = thm "order_antisym";
    val eqD1 = thm "order_eq_refl";
    val eqD2 = thm "sym" RS thm "order_eq_refl";
    val less_trans = thm "order_less_trans";
    val less_le_trans = thm "order_less_le_trans";
    val le_less_trans = thm "order_le_less_trans";
    val le_trans = thm "order_trans";
    val le_neq_trans = thm "order_le_neq_trans";
    val neq_le_trans = thm "order_neq_le_trans";
    val less_imp_neq = thm "less_imp_neq";
    val eq_neq_eq_imp_neq = thm "eq_neq_eq_imp_neq";
    val decomp_part = decomp_gen ["HOL.order"];
    val decomp_lin = decomp_gen ["HOL.linorder"];

  end);  (* struct *)

simpset_ref() := simpset ()
    addSolver (mk_solver "Trans_linear" (fn _ => Order_Tac.linear_tac))
    addSolver (mk_solver "Trans_partial" (fn _ => Order_Tac.partial_tac));
  (* Adding the transitivity reasoners also as safe solvers showed a slight
     speed up, but the reasoning strength appears to be not higher (at least
     no breaking of additional proofs in the entire HOL distribution, as
     of 5 March 2004, was observed). *)
*}

(* Optional setup of methods *)

(*
method_setup trans_partial =
  {* Method.no_args (Method.SIMPLE_METHOD' HEADGOAL (Order_Tac.partial_tac)) *}
  {* transitivity reasoner for partial orders *}	
method_setup trans_linear =
  {* Method.no_args (Method.SIMPLE_METHOD' HEADGOAL (Order_Tac.linear_tac)) *}
  {* transitivity reasoner for linear orders *}
*)

(*
declare order.order_refl [simp del] order_less_irrefl [simp del]

can currently not be removed, abel_cancel relies on it.
*)

subsubsection "Bounded quantifiers"

syntax
  "_lessAll" :: "[idt, 'a, bool] => bool"   ("(3ALL _<_./ _)"  [0, 0, 10] 10)
  "_lessEx"  :: "[idt, 'a, bool] => bool"   ("(3EX _<_./ _)"  [0, 0, 10] 10)
  "_leAll"   :: "[idt, 'a, bool] => bool"   ("(3ALL _<=_./ _)" [0, 0, 10] 10)
  "_leEx"    :: "[idt, 'a, bool] => bool"   ("(3EX _<=_./ _)" [0, 0, 10] 10)

  "_gtAll" :: "[idt, 'a, bool] => bool"   ("(3ALL _>_./ _)"  [0, 0, 10] 10)
  "_gtEx"  :: "[idt, 'a, bool] => bool"   ("(3EX _>_./ _)"  [0, 0, 10] 10)
  "_geAll"   :: "[idt, 'a, bool] => bool"   ("(3ALL _>=_./ _)" [0, 0, 10] 10)
  "_geEx"    :: "[idt, 'a, bool] => bool"   ("(3EX _>=_./ _)" [0, 0, 10] 10)

syntax (xsymbols)
  "_lessAll" :: "[idt, 'a, bool] => bool"   ("(3\<forall>_<_./ _)"  [0, 0, 10] 10)
  "_lessEx"  :: "[idt, 'a, bool] => bool"   ("(3\<exists>_<_./ _)"  [0, 0, 10] 10)
  "_leAll"   :: "[idt, 'a, bool] => bool"   ("(3\<forall>_\<le>_./ _)" [0, 0, 10] 10)
  "_leEx"    :: "[idt, 'a, bool] => bool"   ("(3\<exists>_\<le>_./ _)" [0, 0, 10] 10)

  "_gtAll" :: "[idt, 'a, bool] => bool"   ("(3\<forall>_>_./ _)"  [0, 0, 10] 10)
  "_gtEx"  :: "[idt, 'a, bool] => bool"   ("(3\<exists>_>_./ _)"  [0, 0, 10] 10)
  "_geAll"   :: "[idt, 'a, bool] => bool"   ("(3\<forall>_\<ge>_./ _)" [0, 0, 10] 10)
  "_geEx"    :: "[idt, 'a, bool] => bool"   ("(3\<exists>_\<ge>_./ _)" [0, 0, 10] 10)

syntax (HOL)
  "_lessAll" :: "[idt, 'a, bool] => bool"   ("(3! _<_./ _)"  [0, 0, 10] 10)
  "_lessEx"  :: "[idt, 'a, bool] => bool"   ("(3? _<_./ _)"  [0, 0, 10] 10)
  "_leAll"   :: "[idt, 'a, bool] => bool"   ("(3! _<=_./ _)" [0, 0, 10] 10)
  "_leEx"    :: "[idt, 'a, bool] => bool"   ("(3? _<=_./ _)" [0, 0, 10] 10)

syntax (HTML output)
  "_lessAll" :: "[idt, 'a, bool] => bool"   ("(3\<forall>_<_./ _)"  [0, 0, 10] 10)
  "_lessEx"  :: "[idt, 'a, bool] => bool"   ("(3\<exists>_<_./ _)"  [0, 0, 10] 10)
  "_leAll"   :: "[idt, 'a, bool] => bool"   ("(3\<forall>_\<le>_./ _)" [0, 0, 10] 10)
  "_leEx"    :: "[idt, 'a, bool] => bool"   ("(3\<exists>_\<le>_./ _)" [0, 0, 10] 10)

  "_gtAll" :: "[idt, 'a, bool] => bool"   ("(3\<forall>_>_./ _)"  [0, 0, 10] 10)
  "_gtEx"  :: "[idt, 'a, bool] => bool"   ("(3\<exists>_>_./ _)"  [0, 0, 10] 10)
  "_geAll"   :: "[idt, 'a, bool] => bool"   ("(3\<forall>_\<ge>_./ _)" [0, 0, 10] 10)
  "_geEx"    :: "[idt, 'a, bool] => bool"   ("(3\<exists>_\<ge>_./ _)" [0, 0, 10] 10)

translations
 "ALL x<y. P"   =>  "ALL x. x < y --> P"
 "EX x<y. P"    =>  "EX x. x < y  & P"
 "ALL x<=y. P"  =>  "ALL x. x <= y --> P"
 "EX x<=y. P"   =>  "EX x. x <= y & P"
 "ALL x>y. P"   =>  "ALL x. x > y --> P"
 "EX x>y. P"    =>  "EX x. x > y  & P"
 "ALL x>=y. P"  =>  "ALL x. x >= y --> P"
 "EX x>=y. P"   =>  "EX x. x >= y & P"

print_translation {*
let
  fun mk v v' q n P =
    if v=v' andalso not(v  mem (map fst (Term.add_frees([],n))))
    then Syntax.const q $ Syntax.mark_bound v' $ n $ P else raise Match;
  fun all_tr' [Const ("_bound",_) $ Free (v,_),
               Const("op -->",_) $ (Const ("op <",_) $ (Const ("_bound",_) $ Free (v',_)) $ n ) $ P] =
    mk v v' "_lessAll" n P

  | all_tr' [Const ("_bound",_) $ Free (v,_),
               Const("op -->",_) $ (Const ("op <=",_) $ (Const ("_bound",_) $ Free (v',_)) $ n ) $ P] =
    mk v v' "_leAll" n P

  | all_tr' [Const ("_bound",_) $ Free (v,_),
               Const("op -->",_) $ (Const ("op <",_) $ n $ (Const ("_bound",_) $ Free (v',_))) $ P] =
    mk v v' "_gtAll" n P

  | all_tr' [Const ("_bound",_) $ Free (v,_),
               Const("op -->",_) $ (Const ("op <=",_) $ n $ (Const ("_bound",_) $ Free (v',_))) $ P] =
    mk v v' "_geAll" n P;

  fun ex_tr' [Const ("_bound",_) $ Free (v,_),
               Const("op &",_) $ (Const ("op <",_) $ (Const ("_bound",_) $ Free (v',_)) $ n ) $ P] =
    mk v v' "_lessEx" n P

  | ex_tr' [Const ("_bound",_) $ Free (v,_),
               Const("op &",_) $ (Const ("op <=",_) $ (Const ("_bound",_) $ Free (v',_)) $ n ) $ P] =
    mk v v' "_leEx" n P

  | ex_tr' [Const ("_bound",_) $ Free (v,_),
               Const("op &",_) $ (Const ("op <",_) $ n $ (Const ("_bound",_) $ Free (v',_))) $ P] =
    mk v v' "_gtEx" n P

  | ex_tr' [Const ("_bound",_) $ Free (v,_),
               Const("op &",_) $ (Const ("op <=",_) $ n $ (Const ("_bound",_) $ Free (v',_))) $ P] =
    mk v v' "_geEx" n P
in
[("ALL ", all_tr'), ("EX ", ex_tr')]
end
*}

end

