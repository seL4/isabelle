(*  Title:      HOL/Set.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1993  University of Cambridge
*)

Set = Ord +


(** Core syntax **)

global

types
  'a set

arities
  set :: (term) term

instance
  set :: (term) {ord, minus}

syntax
  "op :"        :: ['a, 'a set] => bool             ("op :")

consts
  "{}"          :: 'a set                           ("{}")
  UNIV          :: 'a set
  insert        :: ['a, 'a set] => 'a set
  Collect       :: ('a => bool) => 'a set               (*comprehension*)
  Int           :: ['a set, 'a set] => 'a set       (infixl 70)
  Un            :: ['a set, 'a set] => 'a set       (infixl 65)
  UNION, INTER  :: ['a set, 'a => 'b set] => 'b set     (*general*)
  Union, Inter  :: (('a set) set) => 'a set             (*of a set*)
  Pow           :: 'a set => 'a set set                 (*powerset*)
  range         :: ('a => 'b) => 'b set                 (*of function*)
  Ball, Bex     :: ['a set, 'a => bool] => bool         (*bounded quantifiers*)
  "image"       :: ['a => 'b, 'a set] => ('b set)   (infixr "``" 90)
  (*membership*)
  "op :"        :: ['a, 'a set] => bool             ("(_/ : _)" [50, 51] 50)


(** Additional concrete syntax **)

syntax

  (* Infix syntax for non-membership *)

  "op ~:"       :: ['a, 'a set] => bool               ("op ~:")
  "op ~:"       :: ['a, 'a set] => bool               ("(_/ ~: _)" [50, 51] 50)


  "@Finset"     :: args => 'a set                     ("{(_)}")
  "@Coll"       :: [pttrn, bool] => 'a set            ("(1{_./ _})")
  "@SetCompr"   :: ['a, idts, bool] => 'a set         ("(1{_ |/_./ _})")

  (* Big Intersection / Union *)

  "@INTER1"     :: [pttrns, 'b set] => 'b set         ("(3INT _./ _)" 10)
  "@UNION1"     :: [pttrns, 'b set] => 'b set         ("(3UN _./ _)" 10)
  "@INTER"      :: [pttrn, 'a set, 'b set] => 'b set  ("(3INT _:_./ _)" 10)
  "@UNION"      :: [pttrn, 'a set, 'b set] => 'b set  ("(3UN _:_./ _)" 10)

  (* Bounded Quantifiers *)
  "_Ball"       :: [pttrn, 'a set, bool] => bool      ("(3ALL _:_./ _)" [0, 0, 10] 10)
  "_Bex"        :: [pttrn, 'a set, bool] => bool      ("(3EX _:_./ _)" [0, 0, 10] 10)

syntax (HOL)
  "_Ball"       :: [pttrn, 'a set, bool] => bool      ("(3! _:_./ _)" [0, 0, 10] 10)
  "_Bex"        :: [pttrn, 'a set, bool] => bool      ("(3? _:_./ _)" [0, 0, 10] 10)

translations
  "range f"     == "f``UNIV"
  "x ~: y"      == "~ (x : y)"
  "{x, xs}"     == "insert x {xs}"
  "{x}"         == "insert x {}"
  "{x. P}"      == "Collect (%x. P)"
  "UN x y. B"   == "UN x. UN y. B"
  "UN x. B"     == "UNION UNIV (%x. B)"
  "INT x y. B"  == "INT x. INT y. B"
  "INT x. B"    == "INTER UNIV (%x. B)"
  "UN x:A. B"   == "UNION A (%x. B)"
  "INT x:A. B"  == "INTER A (%x. B)"
  "ALL x:A. P"  == "Ball A (%x. P)"
  "EX x:A. P"   == "Bex A (%x. P)"

syntax ("" output)
  "_setle"      :: ['a set, 'a set] => bool           ("op <=")
  "_setle"      :: ['a set, 'a set] => bool           ("(_/ <= _)" [50, 51] 50)
  "_setless"    :: ['a set, 'a set] => bool           ("op <")
  "_setless"    :: ['a set, 'a set] => bool           ("(_/ < _)" [50, 51] 50)

syntax (symbols)
  "_setle"      :: ['a set, 'a set] => bool           ("op \\<subseteq>")
  "_setle"      :: ['a set, 'a set] => bool           ("(_/ \\<subseteq> _)" [50, 51] 50)
  "_setless"    :: ['a set, 'a set] => bool           ("op \\<subset>")
  "_setless"    :: ['a set, 'a set] => bool           ("(_/ \\<subset> _)" [50, 51] 50)
  "op Int"      :: ['a set, 'a set] => 'a set         (infixl "\\<inter>" 70)
  "op Un"       :: ['a set, 'a set] => 'a set         (infixl "\\<union>" 65)
  "op :"        :: ['a, 'a set] => bool               ("op \\<in>")
  "op :"        :: ['a, 'a set] => bool               ("(_/ \\<in> _)" [50, 51] 50)
  "op ~:"       :: ['a, 'a set] => bool               ("op \\<notin>")
  "op ~:"       :: ['a, 'a set] => bool               ("(_/ \\<notin> _)" [50, 51] 50)
  "@UNION1"     :: [pttrns, 'b set] => 'b set         ("(3\\<Union>_./ _)" 10)
  "@INTER1"     :: [pttrns, 'b set] => 'b set         ("(3\\<Inter>_./ _)" 10)
  "@UNION"      :: [pttrn, 'a set, 'b set] => 'b set  ("(3\\<Union>_\\<in>_./ _)" 10)
  "@INTER"      :: [pttrn, 'a set, 'b set] => 'b set  ("(3\\<Inter>_\\<in>_./ _)" 10)
  Union         :: (('a set) set) => 'a set           ("\\<Union>_" [90] 90)
  Inter         :: (('a set) set) => 'a set           ("\\<Inter>_" [90] 90)
  "_Ball"       :: [pttrn, 'a set, bool] => bool      ("(3\\<forall>_\\<in>_./ _)" [0, 0, 10] 10)
  "_Bex"        :: [pttrn, 'a set, bool] => bool      ("(3\\<exists>_\\<in>_./ _)" [0, 0, 10] 10)

translations
  "op \\<subseteq>" => "op <= :: [_ set, _ set] => bool"
  "op \\<subset>" => "op <  :: [_ set, _ set] => bool"



(** Rules and definitions **)

local

rules

  (* Isomorphisms between Predicates and Sets *)

  mem_Collect_eq    "(a : {x. P(x)}) = P(a)"
  Collect_mem_eq    "{x. x:A} = A"


defs
  Ball_def      "Ball A P       == ! x. x:A --> P(x)"
  Bex_def       "Bex A P        == ? x. x:A & P(x)"
  subset_def    "A <= B         == ! x:A. x:B"
  psubset_def   "A < B          == (A::'a set) <= B & ~ A=B"
  Compl_def     "- A            == {x. ~x:A}"
  Un_def        "A Un B         == {x. x:A | x:B}"
  Int_def       "A Int B        == {x. x:A & x:B}"
  set_diff_def  "A - B          == {x. x:A & ~x:B}"
  INTER_def     "INTER A B      == {y. ! x:A. y: B(x)}"
  UNION_def     "UNION A B      == {y. ? x:A. y: B(x)}"
  Inter_def     "Inter S        == (INT x:S. x)"
  Union_def     "Union S        == (UN x:S. x)"
  Pow_def       "Pow A          == {B. B <= A}"
  empty_def     "{}             == {x. False}"
  UNIV_def      "UNIV           == {x. True}"
  insert_def    "insert a B     == {x. x=a} Un B"
  image_def     "f``A           == {y. ? x:A. y=f(x)}"


end


ML

local

(* Set inclusion *)

fun le_tr' _ (*op <=*) (Type ("fun", (Type ("set", _) :: _))) ts =
      list_comb (Syntax.const "_setle", ts)
  | le_tr' _ (*op <=*) _ _ = raise Match;

fun less_tr' _ (*op <*) (Type ("fun", (Type ("set", _) :: _))) ts =
      list_comb (Syntax.const "_setless", ts)
  | less_tr' _ (*op <*) _ _ = raise Match;


(* Translates between { e | x1..xn. P} and {u. ? x1..xn. u=e & P}      *)
(* {y. ? x1..xn. y = e & P} is only translated if [0..n] subset bvs(e) *)

val ex_tr = snd(mk_binder_tr("EX ","Ex"));

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
val typed_print_translation = [("op <=", le_tr'), ("op <", less_tr')];


end;
