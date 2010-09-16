(* ========================================================================= *)
(* FIRST ORDER LOGIC ATOMS                                                   *)
(* Copyright (c) 2001 Joe Hurd, distributed under the BSD License            *)
(* ========================================================================= *)

structure Atom :> Atom =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* A type for storing first order logic atoms.                               *)
(* ------------------------------------------------------------------------- *)

type relationName = Name.name;

type relation = relationName * int;

type atom = relationName * Term.term list;

(* ------------------------------------------------------------------------- *)
(* Constructors and destructors.                                             *)
(* ------------------------------------------------------------------------- *)

fun name ((rel,_) : atom) = rel;

fun arguments ((_,args) : atom) = args;

fun arity atm = length (arguments atm);

fun relation atm = (name atm, arity atm);

val functions =
    let
      fun f (tm,acc) = NameAritySet.union (Term.functions tm) acc
    in
      fn atm => List.foldl f NameAritySet.empty (arguments atm)
    end;

val functionNames =
    let
      fun f (tm,acc) = NameSet.union (Term.functionNames tm) acc
    in
      fn atm => List.foldl f NameSet.empty (arguments atm)
    end;

(* Binary relations *)

fun mkBinop p (a,b) : atom = (p,[a,b]);

fun destBinop p (x,[a,b]) =
    if Name.equal x p then (a,b) else raise Error "Atom.destBinop: wrong binop"
  | destBinop _ _ = raise Error "Atom.destBinop: not a binop";

fun isBinop p = can (destBinop p);

(* ------------------------------------------------------------------------- *)
(* The size of an atom in symbols.                                           *)
(* ------------------------------------------------------------------------- *)

fun symbols atm =
    List.foldl (fn (tm,z) => Term.symbols tm + z) 1 (arguments atm);

(* ------------------------------------------------------------------------- *)
(* A total comparison function for atoms.                                    *)
(* ------------------------------------------------------------------------- *)

fun compare ((p1,tms1),(p2,tms2)) =
    case Name.compare (p1,p2) of
      LESS => LESS
    | EQUAL => lexCompare Term.compare (tms1,tms2)
    | GREATER => GREATER;

fun equal atm1 atm2 = compare (atm1,atm2) = EQUAL;

(* ------------------------------------------------------------------------- *)
(* Subterms.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun subterm _ [] = raise Bug "Atom.subterm: empty path"
  | subterm ((_,tms) : atom) (h :: t) =
    if h >= length tms then raise Error "Atom.subterm: bad path"
    else Term.subterm (List.nth (tms,h)) t;

fun subterms ((_,tms) : atom) =
    let
      fun f ((n,tm),l) = map (fn (p,s) => (n :: p, s)) (Term.subterms tm) @ l
    in
      List.foldl f [] (enumerate tms)
    end;

fun replace _ ([],_) = raise Bug "Atom.replace: empty path"
  | replace (atm as (rel,tms)) (h :: t, res) : atom =
    if h >= length tms then raise Error "Atom.replace: bad path"
    else
      let
        val tm = List.nth (tms,h)
        val tm' = Term.replace tm (t,res)
      in
        if Portable.pointerEqual (tm,tm') then atm
        else (rel, updateNth (h,tm') tms)
      end;

fun find pred =
    let
      fun f (i,tm) =
          case Term.find pred tm of
            SOME path => SOME (i :: path)
          | NONE => NONE
    in
      fn (_,tms) : atom => first f (enumerate tms)
    end;

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

fun freeIn v atm = List.exists (Term.freeIn v) (arguments atm);

val freeVars =
    let
      fun f (tm,acc) = NameSet.union (Term.freeVars tm) acc
    in
      fn atm => List.foldl f NameSet.empty (arguments atm)
    end;

(* ------------------------------------------------------------------------- *)
(* Substitutions.                                                            *)
(* ------------------------------------------------------------------------- *)

fun subst sub (atm as (p,tms)) : atom =
    let
      val tms' = Sharing.map (Subst.subst sub) tms
    in
      if Portable.pointerEqual (tms',tms) then atm else (p,tms')
    end;

(* ------------------------------------------------------------------------- *)
(* Matching.                                                                 *)
(* ------------------------------------------------------------------------- *)

local
  fun matchArg ((tm1,tm2),sub) = Subst.match sub tm1 tm2;
in
  fun match sub (p1,tms1) (p2,tms2) =
      let
        val _ = (Name.equal p1 p2 andalso length tms1 = length tms2) orelse
                raise Error "Atom.match"
      in
        List.foldl matchArg sub (zip tms1 tms2)
      end;
end;

(* ------------------------------------------------------------------------- *)
(* Unification.                                                              *)
(* ------------------------------------------------------------------------- *)

local
  fun unifyArg ((tm1,tm2),sub) = Subst.unify sub tm1 tm2;
in
  fun unify sub (p1,tms1) (p2,tms2) =
      let
        val _ = (Name.equal p1 p2 andalso length tms1 = length tms2) orelse
                raise Error "Atom.unify"
      in
        List.foldl unifyArg sub (zip tms1 tms2)
      end;
end;

(* ------------------------------------------------------------------------- *)
(* The equality relation.                                                    *)
(* ------------------------------------------------------------------------- *)

val eqRelationName = Name.fromString "=";

val eqRelationArity = 2;

val eqRelation = (eqRelationName,eqRelationArity);

val mkEq = mkBinop eqRelationName;

fun destEq x = destBinop eqRelationName x;

fun isEq x = isBinop eqRelationName x;

fun mkRefl tm = mkEq (tm,tm);

fun destRefl atm =
    let
      val (l,r) = destEq atm
      val _ = Term.equal l r orelse raise Error "Atom.destRefl"
    in
      l
    end;

fun isRefl x = can destRefl x;

fun sym atm =
    let
      val (l,r) = destEq atm
      val _ = not (Term.equal l r) orelse raise Error "Atom.sym: refl"
    in
      mkEq (r,l)
    end;

fun lhs atm = fst (destEq atm);

fun rhs atm = snd (destEq atm);

(* ------------------------------------------------------------------------- *)
(* Special support for terms with type annotations.                          *)
(* ------------------------------------------------------------------------- *)

fun typedSymbols ((_,tms) : atom) =
    List.foldl (fn (tm,z) => Term.typedSymbols tm + z) 1 tms;

fun nonVarTypedSubterms (_,tms) =
    let
      fun addArg ((n,arg),acc) =
          let
            fun addTm ((path,tm),acc) = (n :: path, tm) :: acc
          in
            List.foldl addTm acc (Term.nonVarTypedSubterms arg)
          end
    in
      List.foldl addArg [] (enumerate tms)
    end;

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty printing.                                              *)
(* ------------------------------------------------------------------------- *)

val pp = Print.ppMap Term.Fn Term.pp;

val toString = Print.toString pp;

fun fromString s = Term.destFn (Term.fromString s);

val parse = Parse.parseQuotation Term.toString fromString;

end

structure AtomOrdered =
struct type t = Atom.atom val compare = Atom.compare end

structure AtomMap = KeyMap (AtomOrdered);

structure AtomSet = ElementSet (AtomMap);
