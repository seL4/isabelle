(* ========================================================================= *)
(* FIRST ORDER LOGIC FORMULAS                                                *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Formula :> Formula =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* A type of first order logic formulas.                                     *)
(* ------------------------------------------------------------------------- *)

datatype formula =
    True
  | False
  | Atom of Atom.atom
  | Not of formula
  | And of formula * formula
  | Or of formula * formula
  | Imp of formula * formula
  | Iff of formula * formula
  | Forall of Term.var * formula
  | Exists of Term.var * formula;

(* ------------------------------------------------------------------------- *)
(* Constructors and destructors.                                             *)
(* ------------------------------------------------------------------------- *)

(* Booleans *)

fun mkBoolean true = True
  | mkBoolean false = False;

fun destBoolean True = true
  | destBoolean False = false
  | destBoolean _ = raise Error "destBoolean";

val isBoolean = can destBoolean;

(* Functions *)

local
  fun funcs fs [] = fs
    | funcs fs (True :: fms) = funcs fs fms
    | funcs fs (False :: fms) = funcs fs fms
    | funcs fs (Atom atm :: fms) =
      funcs (NameAritySet.union (Atom.functions atm) fs) fms
    | funcs fs (Not p :: fms) = funcs fs (p :: fms)
    | funcs fs (And (p,q) :: fms) = funcs fs (p :: q :: fms)
    | funcs fs (Or (p,q) :: fms) = funcs fs (p :: q :: fms)
    | funcs fs (Imp (p,q) :: fms) = funcs fs (p :: q :: fms)
    | funcs fs (Iff (p,q) :: fms) = funcs fs (p :: q :: fms)
    | funcs fs (Forall (_,p) :: fms) = funcs fs (p :: fms)
    | funcs fs (Exists (_,p) :: fms) = funcs fs (p :: fms);
in
  fun functions fm = funcs NameAritySet.empty [fm];
end;

local
  fun funcs fs [] = fs
    | funcs fs (True :: fms) = funcs fs fms
    | funcs fs (False :: fms) = funcs fs fms
    | funcs fs (Atom atm :: fms) =
      funcs (NameSet.union (Atom.functionNames atm) fs) fms
    | funcs fs (Not p :: fms) = funcs fs (p :: fms)
    | funcs fs (And (p,q) :: fms) = funcs fs (p :: q :: fms)
    | funcs fs (Or (p,q) :: fms) = funcs fs (p :: q :: fms)
    | funcs fs (Imp (p,q) :: fms) = funcs fs (p :: q :: fms)
    | funcs fs (Iff (p,q) :: fms) = funcs fs (p :: q :: fms)
    | funcs fs (Forall (_,p) :: fms) = funcs fs (p :: fms)
    | funcs fs (Exists (_,p) :: fms) = funcs fs (p :: fms);
in
  fun functionNames fm = funcs NameSet.empty [fm];
end;

(* Relations *)

local
  fun rels fs [] = fs
    | rels fs (True :: fms) = rels fs fms
    | rels fs (False :: fms) = rels fs fms
    | rels fs (Atom atm :: fms) =
      rels (NameAritySet.add fs (Atom.relation atm)) fms
    | rels fs (Not p :: fms) = rels fs (p :: fms)
    | rels fs (And (p,q) :: fms) = rels fs (p :: q :: fms)
    | rels fs (Or (p,q) :: fms) = rels fs (p :: q :: fms)
    | rels fs (Imp (p,q) :: fms) = rels fs (p :: q :: fms)
    | rels fs (Iff (p,q) :: fms) = rels fs (p :: q :: fms)
    | rels fs (Forall (_,p) :: fms) = rels fs (p :: fms)
    | rels fs (Exists (_,p) :: fms) = rels fs (p :: fms);
in
  fun relations fm = rels NameAritySet.empty [fm];
end;

local
  fun rels fs [] = fs
    | rels fs (True :: fms) = rels fs fms
    | rels fs (False :: fms) = rels fs fms
    | rels fs (Atom atm :: fms) = rels (NameSet.add fs (Atom.name atm)) fms
    | rels fs (Not p :: fms) = rels fs (p :: fms)
    | rels fs (And (p,q) :: fms) = rels fs (p :: q :: fms)
    | rels fs (Or (p,q) :: fms) = rels fs (p :: q :: fms)
    | rels fs (Imp (p,q) :: fms) = rels fs (p :: q :: fms)
    | rels fs (Iff (p,q) :: fms) = rels fs (p :: q :: fms)
    | rels fs (Forall (_,p) :: fms) = rels fs (p :: fms)
    | rels fs (Exists (_,p) :: fms) = rels fs (p :: fms);
in
  fun relationNames fm = rels NameSet.empty [fm];
end;

(* Atoms *)

fun destAtom (Atom atm) = atm
  | destAtom _ = raise Error "Formula.destAtom";

val isAtom = can destAtom;

(* Negations *)

fun destNeg (Not p) = p
  | destNeg _ = raise Error "Formula.destNeg";

val isNeg = can destNeg;

val stripNeg =
    let
      fun strip n (Not fm) = strip (n + 1) fm
        | strip n fm = (n,fm)
    in
      strip 0
    end;

(* Conjunctions *)

fun listMkConj fms =
    case rev fms of [] => True | fm :: fms => foldl And fm fms;

local
  fun strip cs (And (p,q)) = strip (p :: cs) q
    | strip cs fm = rev (fm :: cs);
in
  fun stripConj True = []
    | stripConj fm = strip [] fm;
end;

val flattenConj =
    let
      fun flat acc [] = acc
        | flat acc (And (p,q) :: fms) = flat acc (q :: p :: fms)
        | flat acc (True :: fms) = flat acc fms
        | flat acc (fm :: fms) = flat (fm :: acc) fms
    in
      fn fm => flat [] [fm]
    end;

(* Disjunctions *)

fun listMkDisj fms =
    case rev fms of [] => False | fm :: fms => foldl Or fm fms;

local
  fun strip cs (Or (p,q)) = strip (p :: cs) q
    | strip cs fm = rev (fm :: cs);
in
  fun stripDisj False = []
    | stripDisj fm = strip [] fm;
end;

val flattenDisj =
    let
      fun flat acc [] = acc
        | flat acc (Or (p,q) :: fms) = flat acc (q :: p :: fms)
        | flat acc (False :: fms) = flat acc fms
        | flat acc (fm :: fms) = flat (fm :: acc) fms
    in
      fn fm => flat [] [fm]
    end;

(* Equivalences *)

fun listMkEquiv fms =
    case rev fms of [] => True | fm :: fms => foldl Iff fm fms;

local
  fun strip cs (Iff (p,q)) = strip (p :: cs) q
    | strip cs fm = rev (fm :: cs);
in
  fun stripEquiv True = []
    | stripEquiv fm = strip [] fm;
end;

val flattenEquiv =
    let
      fun flat acc [] = acc
        | flat acc (Iff (p,q) :: fms) = flat acc (q :: p :: fms)
        | flat acc (True :: fms) = flat acc fms
        | flat acc (fm :: fms) = flat (fm :: acc) fms
    in
      fn fm => flat [] [fm]
    end;

(* Universal quantifiers *)

fun destForall (Forall v_f) = v_f
  | destForall _ = raise Error "destForall";

val isForall = can destForall;

fun listMkForall ([],body) = body
  | listMkForall (v :: vs, body) = Forall (v, listMkForall (vs,body));

local
  fun strip vs (Forall (v,b)) = strip (v :: vs) b
    | strip vs tm = (rev vs, tm);
in
  val stripForall = strip [];
end;

(* Existential quantifiers *)

fun destExists (Exists v_f) = v_f
  | destExists _ = raise Error "destExists";

val isExists = can destExists;

fun listMkExists ([],body) = body
  | listMkExists (v :: vs, body) = Exists (v, listMkExists (vs,body));

local
  fun strip vs (Exists (v,b)) = strip (v :: vs) b
    | strip vs tm = (rev vs, tm);
in
  val stripExists = strip [];
end;

(* ------------------------------------------------------------------------- *)
(* The size of a formula in symbols.                                         *)
(* ------------------------------------------------------------------------- *)

local
  fun sz n [] = n
    | sz n (True :: fms) = sz (n + 1) fms
    | sz n (False :: fms) = sz (n + 1) fms
    | sz n (Atom atm :: fms) = sz (n + Atom.symbols atm) fms
    | sz n (Not p :: fms) = sz (n + 1) (p :: fms)
    | sz n (And (p,q) :: fms) = sz (n + 1) (p :: q :: fms)
    | sz n (Or (p,q) :: fms) = sz (n + 1) (p :: q :: fms)
    | sz n (Imp (p,q) :: fms) = sz (n + 1) (p :: q :: fms)
    | sz n (Iff (p,q) :: fms) = sz (n + 1) (p :: q :: fms)
    | sz n (Forall (_,p) :: fms) = sz (n + 1) (p :: fms)
    | sz n (Exists (_,p) :: fms) = sz (n + 1) (p :: fms);
in
  fun symbols fm = sz 0 [fm];
end;

(* ------------------------------------------------------------------------- *)
(* A total comparison function for formulas.                                 *)
(* ------------------------------------------------------------------------- *)

local
  fun cmp [] = EQUAL
    | cmp ((True,True) :: l) = cmp l
    | cmp ((True,_) :: _) = LESS
    | cmp ((_,True) :: _) = GREATER
    | cmp ((False,False) :: l) = cmp l
    | cmp ((False,_) :: _) = LESS
    | cmp ((_,False) :: _) = GREATER
    | cmp ((Atom atm1, Atom atm2) :: l) =
      (case Atom.compare (atm1,atm2) of
         LESS => LESS
       | EQUAL => cmp l
       | GREATER => GREATER)
    | cmp ((Atom _, _) :: _) = LESS
    | cmp ((_, Atom _) :: _) = GREATER
    | cmp ((Not p1, Not p2) :: l) = cmp ((p1,p2) :: l)
    | cmp ((Not _, _) :: _) = LESS
    | cmp ((_, Not _) :: _) = GREATER
    | cmp ((And (p1,q1), And (p2,q2)) :: l) = cmp ((p1,p2) :: (q1,q2) :: l)
    | cmp ((And _, _) :: _) = LESS
    | cmp ((_, And _) :: _) = GREATER
    | cmp ((Or (p1,q1), Or (p2,q2)) :: l) = cmp ((p1,p2) :: (q1,q2) :: l)
    | cmp ((Or _, _) :: _) = LESS
    | cmp ((_, Or _) :: _) = GREATER
    | cmp ((Imp (p1,q1), Imp (p2,q2)) :: l) = cmp ((p1,p2) :: (q1,q2) :: l)
    | cmp ((Imp _, _) :: _) = LESS
    | cmp ((_, Imp _) :: _) = GREATER
    | cmp ((Iff (p1,q1), Iff (p2,q2)) :: l) = cmp ((p1,p2) :: (q1,q2) :: l)
    | cmp ((Iff _, _) :: _) = LESS
    | cmp ((_, Iff _) :: _) = GREATER
    | cmp ((Forall (v1,p1), Forall (v2,p2)) :: l) =
      (case Name.compare (v1,v2) of
         LESS => LESS
       | EQUAL => cmp ((p1,p2) :: l)
       | GREATER => GREATER)
    | cmp ((Forall _, Exists _) :: _) = LESS
    | cmp ((Exists _, Forall _) :: _) = GREATER
    | cmp ((Exists (v1,p1), Exists (v2,p2)) :: l) =
      (case Name.compare (v1,v2) of
         LESS => LESS
       | EQUAL => cmp ((p1,p2) :: l)
       | GREATER => GREATER);
in
  fun compare fm1_fm2 = cmp [fm1_fm2];
end;

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

fun freeIn v =
    let
      fun f [] = false
        | f (True :: fms) = f fms
        | f (False :: fms) = f fms
        | f (Atom atm :: fms) = Atom.freeIn v atm orelse f fms
        | f (Not p :: fms) = f (p :: fms)
        | f (And (p,q) :: fms) = f (p :: q :: fms)
        | f (Or (p,q) :: fms) = f (p :: q :: fms)
        | f (Imp (p,q) :: fms) = f (p :: q :: fms)
        | f (Iff (p,q) :: fms) = f (p :: q :: fms)
        | f (Forall (w,p) :: fms) = if v = w then f fms else f (p :: fms)
        | f (Exists (w,p) :: fms) = if v = w then f fms else f (p :: fms)
    in
      fn fm => f [fm]
    end;

local
  fun fv vs [] = vs
    | fv vs ((_,True) :: fms) = fv vs fms
    | fv vs ((_,False) :: fms) = fv vs fms
    | fv vs ((bv, Atom atm) :: fms) =
      fv (NameSet.union vs (NameSet.difference (Atom.freeVars atm) bv)) fms
    | fv vs ((bv, Not p) :: fms) = fv vs ((bv,p) :: fms)
    | fv vs ((bv, And (p,q)) :: fms) = fv vs ((bv,p) :: (bv,q) :: fms)
    | fv vs ((bv, Or (p,q)) :: fms) = fv vs ((bv,p) :: (bv,q) :: fms)
    | fv vs ((bv, Imp (p,q)) :: fms) = fv vs ((bv,p) :: (bv,q) :: fms)
    | fv vs ((bv, Iff (p,q)) :: fms) = fv vs ((bv,p) :: (bv,q) :: fms)
    | fv vs ((bv, Forall (v,p)) :: fms) = fv vs ((NameSet.add bv v, p) :: fms)
    | fv vs ((bv, Exists (v,p)) :: fms) = fv vs ((NameSet.add bv v, p) :: fms);
in
  fun freeVars fm = fv NameSet.empty [(NameSet.empty,fm)];
end;

fun specialize fm = snd (stripForall fm);

fun generalize fm = listMkForall (NameSet.toList (freeVars fm), fm);

(* ------------------------------------------------------------------------- *)
(* Substitutions.                                                            *)
(* ------------------------------------------------------------------------- *)

local
  fun substCheck sub fm = if Subst.null sub then fm else substFm sub fm

  and substFm sub fm =
      case fm of
        True => fm
      | False => fm
      | Atom (p,tms) =>
        let
          val tms' = Sharing.map (Subst.subst sub) tms
        in
          if Sharing.pointerEqual (tms,tms') then fm else Atom (p,tms')
        end
      | Not p =>
        let
          val p' = substFm sub p
        in
          if Sharing.pointerEqual (p,p') then fm else Not p'
        end
      | And (p,q) => substConn sub fm And p q
      | Or (p,q) => substConn sub fm Or p q
      | Imp (p,q) => substConn sub fm Imp p q
      | Iff (p,q) => substConn sub fm Iff p q
      | Forall (v,p) => substQuant sub fm Forall v p
      | Exists (v,p) => substQuant sub fm Exists v p

  and substConn sub fm conn p q =
      let
        val p' = substFm sub p
        and q' = substFm sub q
      in
        if Sharing.pointerEqual (p,p') andalso
           Sharing.pointerEqual (q,q')
        then fm
        else conn (p',q')
      end

  and substQuant sub fm quant v p =
      let
        val v' =
            let
              fun f (w,s) =
                  if w = v then s
                  else
                    case Subst.peek sub w of
                      NONE => NameSet.add s w
                    | SOME tm => NameSet.union s (Term.freeVars tm)
                  
              val vars = freeVars p
              val vars = NameSet.foldl f NameSet.empty vars
            in
              Term.variantPrime vars v
            end

        val sub =
            if v = v' then Subst.remove sub (NameSet.singleton v)
            else Subst.insert sub (v, Term.Var v')

        val p' = substCheck sub p
      in
        if v = v' andalso Sharing.pointerEqual (p,p') then fm
        else quant (v',p')
      end;
in
  val subst = substCheck;
end;

(* ------------------------------------------------------------------------- *)
(* The equality relation.                                                    *)
(* ------------------------------------------------------------------------- *)

fun mkEq a_b = Atom (Atom.mkEq a_b);

fun destEq fm = Atom.destEq (destAtom fm);

val isEq = can destEq;

fun mkNeq a_b = Not (mkEq a_b);

fun destNeq (Not fm) = destEq fm
  | destNeq _ = raise Error "Formula.destNeq";

val isNeq = can destNeq;

fun mkRefl tm = Atom (Atom.mkRefl tm);

fun destRefl fm = Atom.destRefl (destAtom fm);

val isRefl = can destRefl;

fun sym fm = Atom (Atom.sym (destAtom fm));

fun lhs fm = fst (destEq fm);

fun rhs fm = snd (destEq fm);

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty-printing.                                              *)
(* ------------------------------------------------------------------------- *)

type quotation = formula Parser.quotation

val truthSymbol = "T"
and falsitySymbol = "F"
and conjunctionSymbol = "/\\"
and disjunctionSymbol = "\\/"
and implicationSymbol = "==>"
and equivalenceSymbol = "<=>"
and universalSymbol = "!"
and existentialSymbol = "?";

local
  fun demote True = Term.Fn (truthSymbol,[])
    | demote False = Term.Fn (falsitySymbol,[])
    | demote (Atom (p,tms)) = Term.Fn (p,tms)
    | demote (Not p) = Term.Fn (!Term.negation, [demote p])
    | demote (And (p,q)) = Term.Fn (conjunctionSymbol, [demote p, demote q])
    | demote (Or (p,q)) = Term.Fn (disjunctionSymbol, [demote p, demote q])
    | demote (Imp (p,q)) = Term.Fn (implicationSymbol, [demote p, demote q])
    | demote (Iff (p,q)) = Term.Fn (equivalenceSymbol, [demote p, demote q])
    | demote (Forall (v,b)) = Term.Fn (universalSymbol, [Term.Var v, demote b])
    | demote (Exists (v,b)) =
      Term.Fn (existentialSymbol, [Term.Var v, demote b]);
in
  fun pp ppstrm fm = Term.pp ppstrm (demote fm);
end;

val toString = Parser.toString pp;

local
  fun isQuant [Term.Var _, _] = true
    | isQuant _ = false;

  fun promote (Term.Var v) = Atom (v,[])
    | promote (Term.Fn (f,tms)) =
      if f = truthSymbol andalso null tms then
        True
      else if f = falsitySymbol andalso null tms then
        False
      else if f = !Term.negation andalso length tms = 1 then
        Not (promote (hd tms))
      else if f = conjunctionSymbol andalso length tms = 2 then
        And (promote (hd tms), promote (List.nth (tms,1)))
      else if f = disjunctionSymbol andalso length tms = 2 then
        Or (promote (hd tms), promote (List.nth (tms,1)))
      else if f = implicationSymbol andalso length tms = 2 then
        Imp (promote (hd tms), promote (List.nth (tms,1)))
      else if f = equivalenceSymbol andalso length tms = 2 then
        Iff (promote (hd tms), promote (List.nth (tms,1)))
      else if f = universalSymbol andalso isQuant tms then
        Forall (Term.destVar (hd tms), promote (List.nth (tms,1)))
      else if f = existentialSymbol andalso isQuant tms then
        Exists (Term.destVar (hd tms), promote (List.nth (tms,1)))
      else
        Atom (f,tms);
in
  fun fromString s = promote (Term.fromString s);
end;

val parse = Parser.parseQuotation toString fromString;

end
