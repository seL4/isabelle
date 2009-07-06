(*
    File:        TLA/Intensional.thy
    ID:          $Id$
    Author:      Stephan Merz
    Copyright:   1998 University of Munich
*)

header {* A framework for "intensional" (possible-world based) logics
  on top of HOL, with lifting of constants and functions *}

theory Intensional
imports Main
begin

axclass
  world < type

(** abstract syntax **)

types
  ('w,'a) expr = "'w => 'a"               (* intention: 'w::world, 'a::type *)
  'w form = "('w, bool) expr"

consts
  Valid    :: "('w::world) form => bool"
  const    :: "'a => ('w::world, 'a) expr"
  lift     :: "['a => 'b, ('w::world, 'a) expr] => ('w,'b) expr"
  lift2    :: "['a => 'b => 'c, ('w::world,'a) expr, ('w,'b) expr] => ('w,'c) expr"
  lift3    :: "['a => 'b => 'c => 'd, ('w::world,'a) expr, ('w,'b) expr, ('w,'c) expr] => ('w,'d) expr"

  (* "Rigid" quantification (logic level) *)
  RAll     :: "('a => ('w::world) form) => 'w form"       (binder "Rall " 10)
  REx      :: "('a => ('w::world) form) => 'w form"       (binder "Rex " 10)
  REx1     :: "('a => ('w::world) form) => 'w form"       (binder "Rex! " 10)

(** concrete syntax **)

nonterminals
  lift
  liftargs

syntax
  ""            :: "id => lift"                          ("_")
  ""            :: "longid => lift"                      ("_")
  ""            :: "var => lift"                         ("_")
  "_applC"      :: "[lift, cargs] => lift"               ("(1_/ _)" [1000, 1000] 999)
  ""            :: "lift => lift"                        ("'(_')")
  "_lambda"     :: "[idts, 'a] => lift"                  ("(3%_./ _)" [0, 3] 3)
  "_constrain"  :: "[lift, type] => lift"                ("(_::_)" [4, 0] 3)
  ""            :: "lift => liftargs"                    ("_")
  "_liftargs"   :: "[lift, liftargs] => liftargs"        ("_,/ _")
  "_Valid"      :: "lift => bool"                        ("(|- _)" 5)
  "_holdsAt"    :: "['a, lift] => bool"                  ("(_ |= _)" [100,10] 10)

  (* Syntax for lifted expressions outside the scope of |- or |= *)
  "LIFT"        :: "lift => 'a"                          ("LIFT _")

  (* generic syntax for lifted constants and functions *)
  "_const"      :: "'a => lift"                          ("(#_)" [1000] 999)
  "_lift"       :: "['a, lift] => lift"                  ("(_<_>)" [1000] 999)
  "_lift2"      :: "['a, lift, lift] => lift"            ("(_<_,/ _>)" [1000] 999)
  "_lift3"      :: "['a, lift, lift, lift] => lift"      ("(_<_,/ _,/ _>)" [1000] 999)

  (* concrete syntax for common infix functions: reuse same symbol *)
  "_liftEqu"    :: "[lift, lift] => lift"                ("(_ =/ _)" [50,51] 50)
  "_liftNeq"    :: "[lift, lift] => lift"                ("(_ ~=/ _)" [50,51] 50)
  "_liftNot"    :: "lift => lift"                        ("(~ _)" [40] 40)
  "_liftAnd"    :: "[lift, lift] => lift"                ("(_ &/ _)" [36,35] 35)
  "_liftOr"     :: "[lift, lift] => lift"                ("(_ |/ _)" [31,30] 30)
  "_liftImp"    :: "[lift, lift] => lift"                ("(_ -->/ _)" [26,25] 25)
  "_liftIf"     :: "[lift, lift, lift] => lift"          ("(if (_)/ then (_)/ else (_))" 10)
  "_liftPlus"   :: "[lift, lift] => lift"                ("(_ +/ _)" [66,65] 65)
  "_liftMinus"  :: "[lift, lift] => lift"                ("(_ -/ _)" [66,65] 65)
  "_liftTimes"  :: "[lift, lift] => lift"                ("(_ */ _)" [71,70] 70)
  "_liftDiv"    :: "[lift, lift] => lift"                ("(_ div _)" [71,70] 70)
  "_liftMod"    :: "[lift, lift] => lift"                ("(_ mod _)" [71,70] 70)
  "_liftLess"   :: "[lift, lift] => lift"                ("(_/ < _)"  [50, 51] 50)
  "_liftLeq"    :: "[lift, lift] => lift"                ("(_/ <= _)" [50, 51] 50)
  "_liftMem"    :: "[lift, lift] => lift"                ("(_/ : _)" [50, 51] 50)
  "_liftNotMem" :: "[lift, lift] => lift"                ("(_/ ~: _)" [50, 51] 50)
  "_liftFinset" :: "liftargs => lift"                    ("{(_)}")
  (** TODO: syntax for lifted collection / comprehension **)
  "_liftPair"   :: "[lift,liftargs] => lift"                   ("(1'(_,/ _'))")
  (* infix syntax for list operations *)
  "_liftCons" :: "[lift, lift] => lift"                  ("(_ #/ _)" [65,66] 65)
  "_liftApp"  :: "[lift, lift] => lift"                  ("(_ @/ _)" [65,66] 65)
  "_liftList" :: "liftargs => lift"                      ("[(_)]")

  (* Rigid quantification (syntax level) *)
  "_ARAll"  :: "[idts, lift] => lift"                    ("(3! _./ _)" [0, 10] 10)
  "_AREx"   :: "[idts, lift] => lift"                    ("(3? _./ _)" [0, 10] 10)
  "_AREx1"  :: "[idts, lift] => lift"                    ("(3?! _./ _)" [0, 10] 10)
  "_RAll" :: "[idts, lift] => lift"                      ("(3ALL _./ _)" [0, 10] 10)
  "_REx"  :: "[idts, lift] => lift"                      ("(3EX _./ _)" [0, 10] 10)
  "_REx1" :: "[idts, lift] => lift"                      ("(3EX! _./ _)" [0, 10] 10)

translations
  "_const"        == "const"
  "_lift"         == "lift"
  "_lift2"        == "lift2"
  "_lift3"        == "lift3"
  "_Valid"        == "Valid"
  "_RAll x A"     == "Rall x. A"
  "_REx x  A"     == "Rex x. A"
  "_REx1 x  A"    == "Rex! x. A"
  "_ARAll"        => "_RAll"
  "_AREx"         => "_REx"
  "_AREx1"        => "_REx1"

  "w |= A"        => "A w"
  "LIFT A"        => "A::_=>_"

  "_liftEqu"      == "_lift2 (op =)"
  "_liftNeq u v"  == "_liftNot (_liftEqu u v)"
  "_liftNot"      == "_lift Not"
  "_liftAnd"      == "_lift2 (op &)"
  "_liftOr"       == "_lift2 (op | )"
  "_liftImp"      == "_lift2 (op -->)"
  "_liftIf"       == "_lift3 If"
  "_liftPlus"     == "_lift2 (op +)"
  "_liftMinus"    == "_lift2 (op -)"
  "_liftTimes"    == "_lift2 (op *)"
  "_liftDiv"      == "_lift2 (op div)"
  "_liftMod"      == "_lift2 (op mod)"
  "_liftLess"     == "_lift2 (op <)"
  "_liftLeq"      == "_lift2 (op <=)"
  "_liftMem"      == "_lift2 (op :)"
  "_liftNotMem x xs"   == "_liftNot (_liftMem x xs)"
  "_liftFinset (_liftargs x xs)"  == "_lift2 CONST insert x (_liftFinset xs)"
  "_liftFinset x" == "_lift2 CONST insert x (_const {})"
  "_liftPair x (_liftargs y z)"       == "_liftPair x (_liftPair y z)"
  "_liftPair"     == "_lift2 Pair"
  "_liftCons"     == "lift2 Cons"
  "_liftApp"      == "lift2 (op @)"
  "_liftList (_liftargs x xs)"  == "_liftCons x (_liftList xs)"
  "_liftList x"   == "_liftCons x (_const [])"



  "w |= ~A"       <= "_liftNot A w"
  "w |= A & B"    <= "_liftAnd A B w"
  "w |= A | B"    <= "_liftOr A B w"
  "w |= A --> B"  <= "_liftImp A B w"
  "w |= u = v"    <= "_liftEqu u v w"
  "w |= ALL x. A"   <= "_RAll x A w"
  "w |= EX x. A"   <= "_REx x A w"
  "w |= EX! x. A"  <= "_REx1 x A w"

syntax (xsymbols)
  "_Valid"      :: "lift => bool"                        ("(\<turnstile> _)" 5)
  "_holdsAt"    :: "['a, lift] => bool"                  ("(_ \<Turnstile> _)" [100,10] 10)
  "_liftNeq"    :: "[lift, lift] => lift"                (infixl "\<noteq>" 50)
  "_liftNot"    :: "lift => lift"                        ("\<not> _" [40] 40)
  "_liftAnd"    :: "[lift, lift] => lift"                (infixr "\<and>" 35)
  "_liftOr"     :: "[lift, lift] => lift"                (infixr "\<or>" 30)
  "_liftImp"    :: "[lift, lift] => lift"                (infixr "\<longrightarrow>" 25)
  "_RAll"       :: "[idts, lift] => lift"                ("(3\<forall>_./ _)" [0, 10] 10)
  "_REx"        :: "[idts, lift] => lift"                ("(3\<exists>_./ _)" [0, 10] 10)
  "_REx1"       :: "[idts, lift] => lift"                ("(3\<exists>!_./ _)" [0, 10] 10)
  "_liftLeq"    :: "[lift, lift] => lift"                ("(_/ \<le> _)" [50, 51] 50)
  "_liftMem"    :: "[lift, lift] => lift"                ("(_/ \<in> _)" [50, 51] 50)
  "_liftNotMem" :: "[lift, lift] => lift"                ("(_/ \<notin> _)" [50, 51] 50)

syntax (HTML output)
  "_liftNeq"    :: "[lift, lift] => lift"                (infixl "\<noteq>" 50)
  "_liftNot"    :: "lift => lift"                        ("\<not> _" [40] 40)
  "_liftAnd"    :: "[lift, lift] => lift"                (infixr "\<and>" 35)
  "_liftOr"     :: "[lift, lift] => lift"                (infixr "\<or>" 30)
  "_RAll"       :: "[idts, lift] => lift"                ("(3\<forall>_./ _)" [0, 10] 10)
  "_REx"        :: "[idts, lift] => lift"                ("(3\<exists>_./ _)" [0, 10] 10)
  "_REx1"       :: "[idts, lift] => lift"                ("(3\<exists>!_./ _)" [0, 10] 10)
  "_liftLeq"    :: "[lift, lift] => lift"                ("(_/ \<le> _)" [50, 51] 50)
  "_liftMem"    :: "[lift, lift] => lift"                ("(_/ \<in> _)" [50, 51] 50)
  "_liftNotMem" :: "[lift, lift] => lift"                ("(_/ \<notin> _)" [50, 51] 50)

axioms
  Valid_def:   "|- A    ==  ALL w. w |= A"

  unl_con:     "LIFT #c w  ==  c"
  unl_lift:    "lift f x w == f (x w)"
  unl_lift2:   "LIFT f<x, y> w == f (x w) (y w)"
  unl_lift3:   "LIFT f<x, y, z> w == f (x w) (y w) (z w)"

  unl_Rall:    "w |= ALL x. A x  ==  ALL x. (w |= A x)"
  unl_Rex:     "w |= EX x. A x   ==  EX x. (w |= A x)"
  unl_Rex1:    "w |= EX! x. A x  ==  EX! x. (w |= A x)"


subsection {* Lemmas and tactics for "intensional" logics. *}

lemmas intensional_rews [simp] =
  unl_con unl_lift unl_lift2 unl_lift3 unl_Rall unl_Rex unl_Rex1

lemma inteq_reflection: "|- x=y  ==>  (x==y)"
  apply (unfold Valid_def unl_lift2)
  apply (rule eq_reflection)
  apply (rule ext)
  apply (erule spec)
  done

lemma intI [intro!]: "(!!w. w |= A) ==> |- A"
  apply (unfold Valid_def)
  apply (rule allI)
  apply (erule meta_spec)
  done

lemma intD [dest]: "|- A ==> w |= A"
  apply (unfold Valid_def)
  apply (erule spec)
  done

(** Lift usual HOL simplifications to "intensional" level. **)

lemma int_simps:
  "|- (x=x) = #True"
  "|- (~#True) = #False"  "|- (~#False) = #True"  "|- (~~ P) = P"
  "|- ((~P) = P) = #False"  "|- (P = (~P)) = #False"
  "|- (P ~= Q) = (P = (~Q))"
  "|- (#True=P) = P"  "|- (P=#True) = P"
  "|- (#True --> P) = P"  "|- (#False --> P) = #True"
  "|- (P --> #True) = #True"  "|- (P --> P) = #True"
  "|- (P --> #False) = (~P)"  "|- (P --> ~P) = (~P)"
  "|- (P & #True) = P"  "|- (#True & P) = P"
  "|- (P & #False) = #False"  "|- (#False & P) = #False"
  "|- (P & P) = P"  "|- (P & ~P) = #False"  "|- (~P & P) = #False"
  "|- (P | #True) = #True"  "|- (#True | P) = #True"
  "|- (P | #False) = P"  "|- (#False | P) = P"
  "|- (P | P) = P"  "|- (P | ~P) = #True"  "|- (~P | P) = #True"
  "|- (! x. P) = P"  "|- (? x. P) = P"
  "|- (~Q --> ~P) = (P --> Q)"
  "|- (P|Q --> R) = ((P-->R)&(Q-->R))"
  apply (unfold Valid_def intensional_rews)
  apply blast+
  done

declare int_simps [THEN inteq_reflection, simp]

lemma TrueW [simp]: "|- #True"
  by (simp add: Valid_def unl_con)



(* ======== Functions to "unlift" intensional implications into HOL rules ====== *)

ML {*
(* Basic unlifting introduces a parameter "w" and applies basic rewrites, e.g.
   |- F = G    becomes   F w = G w
   |- F --> G  becomes   F w --> G w
*)

fun int_unlift th =
  rewrite_rule @{thms intensional_rews} (th RS @{thm intD} handle THM _ => th);

(* Turn  |- F = G  into meta-level rewrite rule  F == G *)
fun int_rewrite th =
  zero_var_indexes (rewrite_rule @{thms intensional_rews} (th RS @{thm inteq_reflection}))

(* flattening turns "-->" into "==>" and eliminates conjunctions in the
   antecedent. For example,

         P & Q --> (R | S --> T)    becomes   [| P; Q; R | S |] ==> T

   Flattening can be useful with "intensional" lemmas (after unlifting).
   Naive resolution with mp and conjI may run away because of higher-order
   unification, therefore the code is a little awkward.
*)
fun flatten t =
  let
    (* analogous to RS, but using matching instead of resolution *)
    fun matchres tha i thb =
      case Seq.chop 2 (Thm.biresolution true [(false,tha)] i thb) of
          ([th],_) => th
        | ([],_)   => raise THM("matchres: no match", i, [tha,thb])
        |      _   => raise THM("matchres: multiple unifiers", i, [tha,thb])

    (* match tha with some premise of thb *)
    fun matchsome tha thb =
      let fun hmatch 0 = raise THM("matchsome: no match", 0, [tha,thb])
            | hmatch n = matchres tha n thb handle THM _ => hmatch (n-1)
      in hmatch (nprems_of thb) end

    fun hflatten t =
        case (concl_of t) of
          Const _ $ (Const ("op -->", _) $ _ $ _) => hflatten (t RS mp)
        | _ => (hflatten (matchsome conjI t)) handle THM _ => zero_var_indexes t
  in
    hflatten t
  end

fun int_use th =
    case (concl_of th) of
      Const _ $ (Const ("Intensional.Valid", _) $ _) =>
              (flatten (int_unlift th) handle THM _ => th)
    | _ => th
*}

attribute_setup int_unlift = {* Scan.succeed (Thm.rule_attribute (K int_unlift)) *} ""
attribute_setup int_rewrite = {* Scan.succeed (Thm.rule_attribute (K int_rewrite)) *} ""
attribute_setup flatten = {* Scan.succeed (Thm.rule_attribute (K flatten)) *} ""
attribute_setup int_use = {* Scan.succeed (Thm.rule_attribute (K int_use)) *} ""

lemma Not_Rall: "|- (~(! x. F x)) = (? x. ~F x)"
  by (simp add: Valid_def)

lemma Not_Rex: "|- (~ (? x. F x)) = (! x. ~ F x)"
  by (simp add: Valid_def)

end
