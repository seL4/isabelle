(*  Title:      HOL/HOL.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1993  University of Cambridge

Higher-Order Logic
*)

HOL = CPure +

classes
  term < logic

axclass
  plus < term

axclass
  minus < term

axclass
  times < term

default
  term

types
  bool

arities
  fun :: (term, term) term
  bool :: term


consts

  (* Constants *)

  Trueprop      :: bool => prop                     ("(_)" 5)
  not           :: bool => bool                     ("~ _" [40] 40)
  True, False   :: bool
  If            :: [bool, 'a, 'a] => 'a   ("(if (_)/ then (_)/ else (_))" 10)
  Inv           :: ('a => 'b) => ('b => 'a)

  (* Binders *)

  Eps           :: ('a => bool) => 'a
  All           :: ('a => bool) => bool             (binder "! " 10)
  Ex            :: ('a => bool) => bool             (binder "? " 10)
  Ex1           :: ('a => bool) => bool             (binder "?! " 10)
  Let           :: ['a, 'a => 'b] => 'b

  (* Infixes *)

  o             :: ['b => 'c, 'a => 'b, 'a] => 'c   (infixl 55)
  "="           :: ['a, 'a] => bool                 (infixl 50)
  "&"           :: [bool, bool] => bool             (infixr 35)
  "|"           :: [bool, bool] => bool             (infixr 30)
  "-->"         :: [bool, bool] => bool             (infixr 25)

  (* Overloaded Constants *)

  "+"           :: ['a::plus, 'a] => 'a             (infixl 65)
  "-"           :: ['a::minus, 'a] => 'a            (infixl 65)
  "*"           :: ['a::times, 'a] => 'a            (infixl 70)


types
  letbinds  letbind
  case_syn  cases_syn

syntax

  "~="          :: ['a, 'a] => bool                 (infixl 50)

  "@Eps"        :: [pttrn,bool] => 'a               ("(3@ _./ _)" 10)

  (* Alternative Quantifiers *)

  "*All"        :: [idts, bool] => bool             ("(3ALL _./ _)" 10)
  "*Ex"         :: [idts, bool] => bool             ("(3EX _./ _)" 10)
  "*Ex1"        :: [idts, bool] => bool             ("(3EX! _./ _)" 10)

  (* Let expressions *)

  "_bind"       :: [pttrn, 'a] => letbind           ("(2_ =/ _)" 10)
  ""            :: letbind => letbinds              ("_")
  "_binds"      :: [letbind, letbinds] => letbinds  ("_;/ _")
  "_Let"        :: [letbinds, 'a] => 'a             ("(let (_)/ in (_))" 10)

  (* Case expressions *)

  "@case"       :: ['a, cases_syn] => 'b            ("(case _ of/ _)" 10)
  "@case1"      :: ['a, 'b] => case_syn             ("(2_ =>/ _)" 10)
  ""            :: case_syn => cases_syn            ("_")
  "@case2"      :: [case_syn, cases_syn] => cases_syn   ("_/ | _")

translations
  "x ~= y"      == "~ (x = y)"
  "@ x.b"       == "Eps(%x.b)"
  "ALL xs. P"   => "! xs. P"
  "EX xs. P"    => "? xs. P"
  "EX! xs. P"   => "?! xs. P"
  "_Let (_binds b bs) e"  == "_Let b (_Let bs e)"
  "let x = a in e"        == "Let a (%x. e)"

rules

  eq_reflection "(x=y) ==> (x==y)"

  (* Basic Rules *)

  refl          "t = (t::'a)"
  subst         "[| s = t; P(s) |] ==> P(t::'a)"
  ext           "(!!x::'a. (f(x)::'b) = g(x)) ==> (%x.f(x)) = (%x.g(x))"
  selectI       "P(x::'a) ==> P(@x.P(x))"

  impI          "(P ==> Q) ==> P-->Q"
  mp            "[| P-->Q;  P |] ==> Q"

defs

  True_def      "True      == ((%x::bool.x)=(%x.x))"
  All_def       "All(P)    == (P = (%x.True))"
  Ex_def        "Ex(P)     == P(@x.P(x))"
  False_def     "False     == (!P.P)"
  not_def       "~ P       == P-->False"
  and_def       "P & Q     == !R. (P-->Q-->R) --> R"
  or_def        "P | Q     == !R. (P-->R) --> (Q-->R) --> R"
  Ex1_def       "Ex1(P)    == ? x. P(x) & (! y. P(y) --> y=x)"

rules
  (* Axioms *)

  iff           "(P-->Q) --> (Q-->P) --> (P=Q)"
  True_or_False "(P=True) | (P=False)"

defs
  (* Misc Definitions *)

  Let_def       "Let s f == f(s)"
  Inv_def       "Inv(f::'a=>'b)  == (% y. @x. f(x)=y)"
  o_def         "(f::'b=>'c) o g == (%(x::'a). f(g(x)))"
  if_def        "If P x y == @z::'a. (P=True --> z=x) & (P=False --> z=y)"

(* start 8bit 1 *)
types
('a, 'b) "л"          (infixr 5)

syntax
  "Ъ"		:: "['a::{}, 'a] => prop"       ("(_ Ъ/ _)"         [3, 2] 2)
  "кл"		:: "[prop, prop] => prop"	("(_ кл/ _)"        [2, 1] 1)
  "Gbigimpl"	:: "[asms, prop] => prop"	("((3Л _ М) кл/ _)" [0, 1] 1)
  "Gall"	:: "('a => prop) => prop"	(binder "Д"                0)

  "Glam"         :: "[idts, 'a::logic] => 'b::logic"  ("(3і_./ _)" 10)
  "Ы"           :: "['a, 'a] => bool"                 (infixl 50)
  "Gnot"        :: "bool => bool"                     ("ї _" [40] 40)
  "GEps"        :: "[pttrn, bool] => 'a"               ("(3®_./ _)" 10)
  "GAll"        :: "[idts, bool] => bool"             ("(3В_./ _)" 10)
  "GEx"         :: "[idts, bool] => bool"             ("(3Г_./ _)" 10)
  "GEx1"        :: "[idts, bool] => bool"             ("(3Г!_./ _)" 10)
  "А"           :: "[bool, bool] => bool"             (infixr 35)
  "Б"           :: "[bool, bool] => bool"             (infixr 30)
  "зи"          :: "[bool, bool] => bool"             (infixr 25)

translations
(type)  "x л y"	== (type) "x => y" 

(*  "іx.t"	=> "%x.t" *)

  "x Ы y"	== "x ~= y"
  "ї y"		== "~y"
  "®x.P"	== "@x.P"
  "Вx.P"	== "! x. P"
  "Гx.P"	== "? x. P"
  "Г!x.P"	== "?! x. P"
  "x А y"	== "x & y"
  "x Б y"	== "x | y"
  "x зи y"	== "x --> y"
(* end 8bit 1 *)

end

ML

(** Choice between the HOL and Isabelle style of quantifiers **)

val HOL_quantifiers = ref true;

fun alt_ast_tr' (name, alt_name) =
  let
    fun ast_tr' (*name*) args =
      if ! HOL_quantifiers then raise Match
      else Syntax.mk_appl (Syntax.Constant alt_name) args;
  in
    (name, ast_tr')
  end;


val print_ast_translation =
  map alt_ast_tr' [("! ", "*All"), ("? ", "*Ex"), ("?! ", "*Ex1")];

(* start 8bit 2 *)
local open Ast;
fun bigimpl_ast_tr (*"Gbigimpl"*) [asms, concl] =
      fold_ast_p "кл" (unfold_ast "_asms" asms, concl)
  | bigimpl_ast_tr (*"Gbigimpl"*) asts = raise_ast "bigimpl_ast_tr" asts;
fun impl_ast_tr' (*"кл"*) asts =
  (case unfold_ast_p "кл" (Appl (Constant "кл" :: asts)) of
    (asms as _ :: _ :: _, concl)
      => Appl [Constant "Gbigimpl", fold_ast "_asms" asms, concl]
  | _ => raise Match);

in
val parse_ast_translation = ("Gbigimpl", bigimpl_ast_tr)::
				("Glam",    fn asts => Appl (Constant "_abs" :: asts))::
				parse_ast_translation;

val print_ast_translation = ("кл", impl_ast_tr')::
				("_lambda", fn asts => Appl (Constant "Glam" :: asts)) ::	
				print_ast_translation;

end;

local open Syntax in
val thy = thy 
|> add_trrules_i 
[mk_appl (Constant "Ъ" ) [Variable "P", Variable "Q"] <-> 
 mk_appl (Constant "==") [Variable "P", Variable "Q"],
 mk_appl (Constant "кл" ) [Variable "P", Variable "Q"] <-> 
 mk_appl (Constant "==>") [Variable "P", Variable "Q"],
 (Constant "Д" ) <->  (Constant "!!")]
end;
(* end 8bit 2 *)



