(* 
    File:	 TLA/Intensional.thy
    Author:      Stephan Merz
    Copyright:   1998 University of Munich

    Theory Name: Intensional
    Logic Image: HOL

Define a framework for "intensional" (possible-world based) logics
on top of HOL, with lifting of constants and functions.
*)

Intensional  =  Main +

axclass
  world < type

(** abstract syntax **)

types
  ('w,'a) expr = 'w => 'a               (* intention: 'w::world, 'a::type *)
  'w form = ('w, bool) expr

consts
  Valid    :: ('w::world) form => bool
  const    :: 'a => ('w::world, 'a) expr
  lift     :: ['a => 'b, ('w::world, 'a) expr] => ('w,'b) expr
  lift2    :: ['a => 'b => 'c, ('w::world,'a) expr, ('w,'b) expr] => ('w,'c) expr
  lift3    :: ['a => 'b => 'c => 'd, ('w::world,'a) expr, ('w,'b) expr, ('w,'c) expr] => ('w,'d) expr

  (* "Rigid" quantification (logic level) *)
  RAll     :: "('a => ('w::world) form) => 'w form"       (binder "Rall " 10)
  REx      :: "('a => ('w::world) form) => 'w form"       (binder "Rex " 10)
  REx1     :: "('a => ('w::world) form) => 'w form"       (binder "Rex! " 10)

(** concrete syntax **)

nonterminals
  lift
  liftargs

syntax
  ""            :: id => lift                          ("_")
  ""            :: longid => lift                      ("_")
  ""            :: var => lift                         ("_")
  "_applC"      :: [lift, cargs] => lift               ("(1_/ _)" [1000, 1000] 999)
  ""            :: lift => lift                        ("'(_')")
  "_lambda"     :: [idts, 'a] => lift                  ("(3%_./ _)" [0, 3] 3)
  "_constrain"  :: [lift, type] => lift                ("(_::_)" [4, 0] 3)
  ""            :: lift => liftargs                    ("_")
  "_liftargs"   :: [lift, liftargs] => liftargs        ("_,/ _")
  "_Valid"      :: lift => bool                        ("(|- _)" 5)
  "_holdsAt"    :: ['a, lift] => bool                  ("(_ |= _)" [100,10] 10)

  (* Syntax for lifted expressions outside the scope of |- or |= *)
  "LIFT"        :: lift => 'a                          ("LIFT _")

  (* generic syntax for lifted constants and functions *)
  "_const"      :: 'a => lift                          ("(#_)" [1000] 999)
  "_lift"       :: ['a, lift] => lift                  ("(_<_>)" [1000] 999)
  "_lift2"      :: ['a, lift, lift] => lift            ("(_<_,/ _>)" [1000] 999)
  "_lift3"      :: ['a, lift, lift, lift] => lift      ("(_<_,/ _,/ _>)" [1000] 999)

  (* concrete syntax for common infix functions: reuse same symbol *)
  "_liftEqu"    :: [lift, lift] => lift                ("(_ =/ _)" [50,51] 50)
  "_liftNeq"    :: [lift, lift] => lift                ("(_ ~=/ _)" [50,51] 50)
  "_liftNot"    :: lift => lift                        ("(~ _)" [40] 40)
  "_liftAnd"    :: [lift, lift] => lift                ("(_ &/ _)" [36,35] 35)
  "_liftOr"     :: [lift, lift] => lift                ("(_ |/ _)" [31,30] 30)
  "_liftImp"    :: [lift, lift] => lift                ("(_ -->/ _)" [26,25] 25)
  "_liftIf"     :: [lift, lift, lift] => lift          ("(if (_)/ then (_)/ else (_))" 10)
  "_liftPlus"   :: [lift, lift] => lift                ("(_ +/ _)" [66,65] 65)
  "_liftMinus"  :: [lift, lift] => lift                ("(_ -/ _)" [66,65] 65)
  "_liftTimes"  :: [lift, lift] => lift                ("(_ */ _)" [71,70] 70)
  "_liftDiv"    :: [lift, lift] => lift                ("(_ div _)" [71,70] 70)
  "_liftMod"    :: [lift, lift] => lift                ("(_ mod _)" [71,70] 70)
  "_liftLess"   :: [lift, lift] => lift                ("(_/ < _)"  [50, 51] 50)
  "_liftLeq"    :: [lift, lift] => lift                ("(_/ <= _)" [50, 51] 50)
  "_liftMem"    :: [lift, lift] => lift                ("(_/ : _)" [50, 51] 50)
  "_liftNotMem" :: [lift, lift] => lift                ("(_/ ~: _)" [50, 51] 50)
  "_liftFinset" :: liftargs => lift                    ("{(_)}")
  (** TODO: syntax for lifted collection / comprehension **)
  "_liftPair"   :: [lift,liftargs] => lift                   ("(1'(_,/ _'))")
  (* infix syntax for list operations *)
  "_liftCons" :: [lift, lift] => lift                  ("(_ #/ _)" [65,66] 65)
  "_liftApp"  :: [lift, lift] => lift                  ("(_ @/ _)" [65,66] 65)
  "_liftList" :: liftargs => lift                      ("[(_)]")

  (* Rigid quantification (syntax level) *)
  "_ARAll"  :: [idts, lift] => lift                    ("(3! _./ _)" [0, 10] 10)
  "_AREx"   :: [idts, lift] => lift                    ("(3? _./ _)" [0, 10] 10)
  "_AREx1"  :: [idts, lift] => lift                    ("(3?! _./ _)" [0, 10] 10)
  "_RAll" :: [idts, lift] => lift                      ("(3ALL _./ _)" [0, 10] 10)
  "_REx"  :: [idts, lift] => lift                      ("(3EX _./ _)" [0, 10] 10)
  "_REx1" :: [idts, lift] => lift                      ("(3EX! _./ _)" [0, 10] 10)

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
  "_liftFinset (_liftargs x xs)"  == "_lift2 insert x (_liftFinset xs)"
  "_liftFinset x" == "_lift2 insert x (_const {})"
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
  "_Valid"      :: lift => bool                        ("(\\<turnstile> _)" 5)
  "_holdsAt"    :: ['a, lift] => bool                  ("(_ \\<Turnstile> _)" [100,10] 10)
  "_liftNeq"    :: [lift, lift] => lift                (infixl "\\<noteq>" 50)
  "_liftNot"    :: lift => lift                        ("\\<not> _" [40] 40)
  "_liftAnd"    :: [lift, lift] => lift                (infixr "\\<and>" 35)
  "_liftOr"     :: [lift, lift] => lift                (infixr "\\<or>" 30)
  "_liftImp"    :: [lift, lift] => lift                (infixr "\\<longrightarrow>" 25)
  "_RAll"       :: [idts, lift] => lift                ("(3\\<forall>_./ _)" [0, 10] 10)
  "_REx"        :: [idts, lift] => lift                ("(3\\<exists>_./ _)" [0, 10] 10)
  "_REx1"       :: [idts, lift] => lift                ("(3\\<exists>!_./ _)" [0, 10] 10)
  "_liftLeq"    :: [lift, lift] => lift                ("(_/ \\<le> _)" [50, 51] 50)
  "_liftMem"    :: [lift, lift] => lift                ("(_/ \\<in> _)" [50, 51] 50)
  "_liftNotMem" :: [lift, lift] => lift                ("(_/ \\<notin> _)" [50, 51] 50)

syntax (HTML output)
  "_liftNot"    :: lift => lift                        ("\\<not> _" [40] 40)

rules
  Valid_def   "|- A    ==  ALL w. w |= A"

  unl_con     "LIFT #c w  ==  c" 
  unl_lift    "LIFT f<x> w == f (x w)"
  unl_lift2   "LIFT f<x, y> w == f (x w) (y w)"
  unl_lift3   "LIFT f<x, y, z> w == f (x w) (y w) (z w)"

  unl_Rall    "w |= ALL x. A x  ==  ALL x. (w |= A x)" 
  unl_Rex     "w |= EX x. A x   ==  EX x. (w |= A x)"
  unl_Rex1    "w |= EX! x. A x  ==  EX! x. (w |= A x)"
end
