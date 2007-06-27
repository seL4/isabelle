(* ========================================================================= *)
(* FIRST ORDER LOGIC LITERALS                                                *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Literal :> Literal =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* A type for storing first order logic literals.                            *)
(* ------------------------------------------------------------------------- *)

type polarity = bool;

type literal = polarity * Atom.atom;

(* ------------------------------------------------------------------------- *)
(* Constructors and destructors.                                             *)
(* ------------------------------------------------------------------------- *)

fun polarity ((pol,_) : literal) = pol;

fun atom ((_,atm) : literal) = atm;

fun name lit = Atom.name (atom lit);

fun arguments lit = Atom.arguments (atom lit);

fun arity lit = Atom.arity (atom lit);

fun positive lit = polarity lit;

fun negative lit = not (polarity lit);

fun negate (pol,atm) : literal = (not pol, atm)

fun relation lit = Atom.relation (atom lit);

fun functions lit = Atom.functions (atom lit);

fun functionNames lit = Atom.functionNames (atom lit);

(* Binary relations *)

fun mkBinop rel (pol,a,b) : literal = (pol, Atom.mkBinop rel (a,b));

fun destBinop rel ((pol,atm) : literal) =
    case Atom.destBinop rel atm of (a,b) => (pol,a,b);

fun isBinop rel = can (destBinop rel);

(* Formulas *)

fun toFormula (true,atm) = Formula.Atom atm
  | toFormula (false,atm) = Formula.Not (Formula.Atom atm);

fun fromFormula (Formula.Atom atm) = (true,atm)
  | fromFormula (Formula.Not (Formula.Atom atm)) = (false,atm)
  | fromFormula _ = raise Error "Literal.fromFormula";

(* ------------------------------------------------------------------------- *)
(* The size of a literal in symbols.                                         *)
(* ------------------------------------------------------------------------- *)

fun symbols ((_,atm) : literal) = Atom.symbols atm;

(* ------------------------------------------------------------------------- *)
(* A total comparison function for literals.                                 *)
(* ------------------------------------------------------------------------- *)

fun compare ((pol1,atm1),(pol2,atm2)) =
    case boolCompare (pol1,pol2) of
      LESS => GREATER
    | EQUAL => Atom.compare (atm1,atm2)
    | GREATER => LESS;

(* ------------------------------------------------------------------------- *)
(* Subterms.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun subterm lit path = Atom.subterm (atom lit) path;

fun subterms lit = Atom.subterms (atom lit);

fun replace (lit as (pol,atm)) path_tm =
    let
      val atm' = Atom.replace atm path_tm
    in
      if Sharing.pointerEqual (atm,atm') then lit else (pol,atm')
    end;

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

fun freeIn v lit = Atom.freeIn v (atom lit);

fun freeVars lit = Atom.freeVars (atom lit);

(* ------------------------------------------------------------------------- *)
(* Substitutions.                                                            *)
(* ------------------------------------------------------------------------- *)

fun subst sub (lit as (pol,atm)) : literal =
    let
      val atm' = Atom.subst sub atm
    in
      if Sharing.pointerEqual (atm',atm) then lit else (pol,atm')
    end;

(* ------------------------------------------------------------------------- *)
(* Matching.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun match sub ((pol1,atm1) : literal) (pol2,atm2) =
    let
      val _ = pol1 = pol2 orelse raise Error "Literal.match"
    in
      Atom.match sub atm1 atm2
    end;

(* ------------------------------------------------------------------------- *)
(* Unification.                                                              *)
(* ------------------------------------------------------------------------- *)

fun unify sub ((pol1,atm1) : literal) (pol2,atm2) =
    let
      val _ = pol1 = pol2 orelse raise Error "Literal.unify"
    in
      Atom.unify sub atm1 atm2
    end;

(* ------------------------------------------------------------------------- *)
(* The equality relation.                                                    *)
(* ------------------------------------------------------------------------- *)

fun mkEq l_r : literal = (true, Atom.mkEq l_r);

fun destEq ((true,atm) : literal) = Atom.destEq atm
  | destEq (false,_) = raise Error "Literal.destEq";

val isEq = can destEq;

fun mkNeq l_r : literal = (false, Atom.mkEq l_r);

fun destNeq ((false,atm) : literal) = Atom.destEq atm
  | destNeq (true,_) = raise Error "Literal.destNeq";

val isNeq = can destNeq;

fun mkRefl tm = (true, Atom.mkRefl tm);

fun destRefl (true,atm) = Atom.destRefl atm
  | destRefl (false,_) = raise Error "Literal.destRefl";

val isRefl = can destRefl;

fun mkIrrefl tm = (false, Atom.mkRefl tm);

fun destIrrefl (true,_) = raise Error "Literal.destIrrefl"
  | destIrrefl (false,atm) = Atom.destRefl atm;

val isIrrefl = can destIrrefl;

fun sym (pol,atm) : literal = (pol, Atom.sym atm);

fun lhs ((_,atm) : literal) = Atom.lhs atm;

fun rhs ((_,atm) : literal) = Atom.rhs atm;

(* ------------------------------------------------------------------------- *)
(* Special support for terms with type annotations.                          *)
(* ------------------------------------------------------------------------- *)

fun typedSymbols ((_,atm) : literal) = Atom.typedSymbols atm;

fun nonVarTypedSubterms ((_,atm) : literal) = Atom.nonVarTypedSubterms atm;

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty-printing.                                              *)
(* ------------------------------------------------------------------------- *)

val pp = Parser.ppMap toFormula Formula.pp;

val toString = Parser.toString pp;

fun fromString s = fromFormula (Formula.fromString s);

val parse = Parser.parseQuotation Term.toString fromString;

end

structure LiteralOrdered =
struct type t = Literal.literal val compare = Literal.compare end

structure LiteralSet =
struct

  local
    structure S = ElementSet (LiteralOrdered);
  in
    open S;
  end;

  fun negateMember lit set = member (Literal.negate lit) set;

  val negate =
      let
        fun f (lit,set) = add set (Literal.negate lit)
      in
        foldl f empty
      end;

  val relations =
      let
        fun f (lit,set) = NameAritySet.add set (Literal.relation lit)
      in
        foldl f NameAritySet.empty
      end;

  val functions =
      let
        fun f (lit,set) = NameAritySet.union set (Literal.functions lit)
      in
        foldl f NameAritySet.empty
      end;

  val freeVars =
      let
        fun f (lit,set) = NameSet.union set (Literal.freeVars lit)
      in
        foldl f NameSet.empty
      end;

  val symbols =
      let
        fun f (lit,z) = Literal.symbols lit + z
      in
        foldl f 0
      end;

  val typedSymbols =
      let
        fun f (lit,z) = Literal.typedSymbols lit + z
      in
        foldl f 0
      end;

  fun subst sub lits =
      let
        fun substLit (lit,(eq,lits')) =
            let
              val lit' = Literal.subst sub lit
              val eq = eq andalso Sharing.pointerEqual (lit,lit')
            in
              (eq, add lits' lit')
            end
              
        val (eq,lits') = foldl substLit (true,empty) lits
      in
        if eq then lits else lits'
      end;

  val pp =
      Parser.ppMap
        toList
        (Parser.ppBracket "{" "}" (Parser.ppSequence "," Literal.pp));

end

structure LiteralMap = KeyMap (LiteralOrdered);
