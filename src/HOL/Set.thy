(*  Title:      HOL/Set.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1993  University of Cambridge
*)

Set = Ord +

types
  'a set

arities
  set :: (term) term

instance
  set :: (term) {ord, minus}

consts
  "{}"          :: 'a set                           ("{}")
  insert        :: ['a, 'a set] => 'a set
  Collect       :: ('a => bool) => 'a set               (*comprehension*)
  Compl         :: ('a set) => 'a set                   (*complement*)
  Int           :: ['a set, 'a set] => 'a set       (infixl 70)
  Un            :: ['a set, 'a set] => 'a set       (infixl 65)
  UNION, INTER  :: ['a set, 'a => 'b set] => 'b set     (*general*)
  UNION1        :: ['a => 'b set] => 'b set         (binder "UN " 10)
  INTER1        :: ['a => 'b set] => 'b set         (binder "INT " 10)
  Union, Inter  :: (('a set)set) => 'a set              (*of a set*)
  Pow           :: 'a set => 'a set set                 (*powerset*)
  range         :: ('a => 'b) => 'b set                 (*of function*)
  Ball, Bex     :: ['a set, 'a => bool] => bool         (*bounded quantifiers*)
  inj, surj     :: ('a => 'b) => bool                   (*inj/surjective*)
  inj_onto      :: ['a => 'b, 'a set] => bool
  "``"          :: ['a => 'b, 'a set] => ('b set)   (infixl 90)
  ":"           :: ['a, 'a set] => bool             (infixl 50) (*membership*)


syntax

  UNIV         :: 'a set

  "~:"          :: ['a, 'a set] => bool             (infixl 50)

  "@Finset"     :: args => 'a set                   ("{(_)}")

  "@Coll"       :: [pttrn, bool] => 'a set          ("(1{_./ _})")
  "@SetCompr"   :: ['a, idts, bool] => 'a set       ("(1{_ |/_./ _})")

  (* Big Intersection / Union *)

  "@INTER"      :: [pttrn, 'a set, 'b set] => 'b set  ("(3INT _:_./ _)" 10)
  "@UNION"      :: [pttrn, 'a set, 'b set] => 'b set  ("(3UN _:_./ _)" 10)

  (* Bounded Quantifiers *)

  "@Ball"       :: [pttrn, 'a set, bool] => bool      ("(3! _:_./ _)" 10)
  "@Bex"        :: [pttrn, 'a set, bool] => bool      ("(3? _:_./ _)" 10)
  "*Ball"       :: [pttrn, 'a set, bool] => bool      ("(3ALL _:_./ _)" 10)
  "*Bex"        :: [pttrn, 'a set, bool] => bool      ("(3EX _:_./ _)" 10)

translations
  "UNIV"        == "Compl {}"
  "x ~: y"      == "~ (x : y)"
  "{x, xs}"     == "insert x {xs}"
  "{x}"         == "insert x {}"
  "{x. P}"      == "Collect (%x. P)"
  "INT x:A. B"  == "INTER A (%x. B)"
  "UN x:A. B"   == "UNION A (%x. B)"
  "! x:A. P"    == "Ball A (%x. P)"
  "? x:A. P"    == "Bex A (%x. P)"
  "ALL x:A. P"  => "Ball A (%x. P)"
  "EX x:A. P"   => "Bex A (%x. P)"


rules

  (* Isomorphisms between Predicates and Sets *)

  mem_Collect_eq    "(a : {x.P(x)}) = P(a)"
  Collect_mem_eq    "{x.x:A} = A"


defs
  Ball_def      "Ball A P       == ! x. x:A --> P(x)"
  Bex_def       "Bex A P        == ? x. x:A & P(x)"
  subset_def    "A <= B         == ! x:A. x:B"
  Compl_def     "Compl(A)       == {x. ~x:A}"
  Un_def        "A Un B         == {x.x:A | x:B}"
  Int_def       "A Int B        == {x.x:A & x:B}"
  set_diff_def  "A - B          == {x. x:A & ~x:B}"
  INTER_def     "INTER A B      == {y. ! x:A. y: B(x)}"
  UNION_def     "UNION A B      == {y. ? x:A. y: B(x)}"
  INTER1_def    "INTER1(B)      == INTER {x.True} B"
  UNION1_def    "UNION1(B)      == UNION {x.True} B"
  Inter_def     "Inter(S)       == (INT x:S. x)"
  Union_def     "Union(S)       == (UN x:S. x)"
  Pow_def       "Pow(A)         == {B. B <= A}"
  empty_def     "{}             == {x. False}"
  insert_def    "insert a B     == {x.x=a} Un B"
  range_def     "range(f)       == {y. ? x. y=f(x)}"
  image_def     "f``A           == {y. ? x:A. y=f(x)}"
  inj_def       "inj(f)         == ! x y. f(x)=f(y) --> x=y"
  inj_onto_def  "inj_onto f A   == ! x:A. ! y:A. f(x)=f(y) --> x=y"
  surj_def      "surj(f)        == ! y. ? x. y=f(x)"

(* start 8bit 1 *)
syntax
  "Ð"		:: "['a set, 'a set] => 'a set"       (infixl 70)
  "Ñ"		:: "['a set, 'a set] => 'a set"       (infixl 65)
  "Î"		:: "['a, 'a set] => bool"             (infixl 50)
  "ñ"		:: "['a, 'a set] => bool"             (infixl 50)
  GUnion	:: "(('a set)set) => 'a set"          ("Ó_" [90] 90)
  GInter	:: "(('a set)set) => 'a set"          ("Ò_" [90] 90)
  GUNION1       :: "['a => 'b set] => 'b set"         (binder "Ó " 10)
  GINTER1       :: "['a => 'b set] => 'b set"         (binder "Ò " 10)
  GINTER	:: "[pttrn, 'a set, 'b set] => 'b set"  ("(3Ò _Î_./ _)" 10)
  GUNION	:: "[pttrn, 'a set, 'b set] => 'b set"  ("(3Ó _Î_./ _)" 10)
  GBall		:: "[pttrn, 'a set, bool] => bool"      ("(3Â _Î_./ _)" 10)
  GBex		:: "[pttrn, 'a set, bool] => bool"      ("(3Ã _Î_./ _)" 10)

translations
  "x ñ y"      == "¿(x : y)"
  "x Î y"      == "(x : y)"
  "x Ð y"      == "x Int y"
  "x Ñ y"      == "x Un  y"
  "ÒX"        == "Inter X" 
  "ÓX"        == "Union X"
  "Òx.A"      == "INT x.A"
  "Óx.A"      == "UN x.A"
  "ÒxÎA. B"   == "INT x:A. B"
  "ÓxÎA. B"   == "UN x:A. B"
  "ÂxÎA. P"    == "! x:A. P"
  "ÃxÎA. P"    == "? x:A. P"
(* end 8bit 1 *)

end

ML

local

(* Translates between { e | x1..xn. P} and {u. ? x1..xn. u=e & P}      *)
(* {y. ? x1..xn. y = e & P} is only translated if [0..n] subset bvs(e) *)

val ex_tr = snd(mk_binder_tr("? ","Ex"));

fun nvars(Const("_idts",_) $ _ $ idts) = nvars(idts)+1
  | nvars(_) = 1;

fun setcompr_tr[e,idts,b] =
  let val eq = Syntax.const("op =") $ Bound(nvars(idts)) $ e
      val P = Syntax.const("op &") $ eq $ b
      val exP = ex_tr [idts,P]
  in Syntax.const("Collect") $ Abs("",dummyT,exP) end;

val ex_tr' = snd(mk_binder_tr' ("Ex","DUMMY"));

fun setcompr_tr'[Abs(_,_,P)] =
  let fun ok(Const("Ex",_)$Abs(_,_,P),n) = ok(P,n+1)
        | ok(Const("op &",_) $ (Const("op =",_) $ Bound(m) $ e) $ _, n) =
            if n>0 andalso m=n andalso
              ((0 upto (n-1)) subset add_loose_bnos(e,0,[]))
            then () else raise Match

      fun tr'(_ $ abs) =
        let val _ $ idts $ (_ $ (_ $ _ $ e) $ Q) = ex_tr'[abs]
        in Syntax.const("@SetCompr") $ e $ idts $ Q end
  in ok(P,0); tr'(P) end;

in

val parse_translation = [("@SetCompr", setcompr_tr)];
val print_translation = [("Collect", setcompr_tr')];
val print_ast_translation =
  map HOL.alt_ast_tr' [("@Ball", "*Ball"), ("@Bex", "*Bex")];

end;

