(* ========================================================================= *)
(* FIRST ORDER LOGIC FORMULAS                                                *)
(* Copyright (c) 2001 Joe Hurd, distributed under the BSD License            *)
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

fun isTrue fm =
    case fm of
      True => true
    | _ => false;

fun isFalse fm =
    case fm of
      False => true
    | _ => false;

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
    case List.rev fms of [] => True | fm :: fms => List.foldl And fm fms;

local
  fun strip cs (And (p,q)) = strip (p :: cs) q
    | strip cs fm = List.rev (fm :: cs);
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
    case List.rev fms of [] => False | fm :: fms => List.foldl Or fm fms;

local
  fun strip cs (Or (p,q)) = strip (p :: cs) q
    | strip cs fm = List.rev (fm :: cs);
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
    case List.rev fms of [] => True | fm :: fms => List.foldl Iff fm fms;

local
  fun strip cs (Iff (p,q)) = strip (p :: cs) q
    | strip cs fm = List.rev (fm :: cs);
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

fun setMkForall (vs,body) = NameSet.foldr Forall body vs;

local
  fun strip vs (Forall (v,b)) = strip (v :: vs) b
    | strip vs tm = (List.rev vs, tm);
in
  val stripForall = strip [];
end;

(* Existential quantifiers *)

fun destExists (Exists v_f) = v_f
  | destExists _ = raise Error "destExists";

val isExists = can destExists;

fun listMkExists ([],body) = body
  | listMkExists (v :: vs, body) = Exists (v, listMkExists (vs,body));

fun setMkExists (vs,body) = NameSet.foldr Exists body vs;

local
  fun strip vs (Exists (v,b)) = strip (v :: vs) b
    | strip vs tm = (List.rev vs, tm);
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
    | cmp (f1_f2 :: fs) =
      if Portable.pointerEqual f1_f2 then cmp fs
      else
        case f1_f2 of
          (True,True) => cmp fs
        | (True,_) => LESS
        | (_,True) => GREATER
        | (False,False) => cmp fs
        | (False,_) => LESS
        | (_,False) => GREATER
        | (Atom atm1, Atom atm2) =>
          (case Atom.compare (atm1,atm2) of
             LESS => LESS
           | EQUAL => cmp fs
           | GREATER => GREATER)
        | (Atom _, _) => LESS
        | (_, Atom _) => GREATER
        | (Not p1, Not p2) => cmp ((p1,p2) :: fs)
        | (Not _, _) => LESS
        | (_, Not _) => GREATER
        | (And (p1,q1), And (p2,q2)) => cmp ((p1,p2) :: (q1,q2) :: fs)
        | (And _, _) => LESS
        | (_, And _) => GREATER
        | (Or (p1,q1), Or (p2,q2)) => cmp ((p1,p2) :: (q1,q2) :: fs)
        | (Or _, _) => LESS
        | (_, Or _) => GREATER
        | (Imp (p1,q1), Imp (p2,q2)) => cmp ((p1,p2) :: (q1,q2) :: fs)
        | (Imp _, _) => LESS
        | (_, Imp _) => GREATER
        | (Iff (p1,q1), Iff (p2,q2)) => cmp ((p1,p2) :: (q1,q2) :: fs)
        | (Iff _, _) => LESS
        | (_, Iff _) => GREATER
        | (Forall (v1,p1), Forall (v2,p2)) =>
          (case Name.compare (v1,v2) of
             LESS => LESS
           | EQUAL => cmp ((p1,p2) :: fs)
           | GREATER => GREATER)
        | (Forall _, Exists _) => LESS
        | (Exists _, Forall _) => GREATER
        | (Exists (v1,p1), Exists (v2,p2)) =>
          (case Name.compare (v1,v2) of
             LESS => LESS
           | EQUAL => cmp ((p1,p2) :: fs)
           | GREATER => GREATER);
in
  fun compare fm1_fm2 = cmp [fm1_fm2];
end;

fun equal fm1 fm2 = compare (fm1,fm2) = EQUAL;

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
        | f (Forall (w,p) :: fms) =
          if Name.equal v w then f fms else f (p :: fms)
        | f (Exists (w,p) :: fms) =
          if Name.equal v w then f fms else f (p :: fms)
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

  fun add (fm,vs) = fv vs [(NameSet.empty,fm)];
in
  fun freeVars fm = add (fm,NameSet.empty);

  fun freeVarsList fms = List.foldl add NameSet.empty fms;
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
          if Portable.pointerEqual (tms,tms') then fm else Atom (p,tms')
        end
      | Not p =>
        let
          val p' = substFm sub p
        in
          if Portable.pointerEqual (p,p') then fm else Not p'
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
        if Portable.pointerEqual (p,p') andalso
           Portable.pointerEqual (q,q')
        then fm
        else conn (p',q')
      end

  and substQuant sub fm quant v p =
      let
        val v' =
            let
              fun f (w,s) =
                  if Name.equal w v then s
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
            if Name.equal v v' then Subst.remove sub (NameSet.singleton v)
            else Subst.insert sub (v, Term.Var v')

        val p' = substCheck sub p
      in
        if Name.equal v v' andalso Portable.pointerEqual (p,p') then fm
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

type quotation = formula Parse.quotation;

val truthName = Name.fromString "T"
and falsityName = Name.fromString "F"
and conjunctionName = Name.fromString "/\\"
and disjunctionName = Name.fromString "\\/"
and implicationName = Name.fromString "==>"
and equivalenceName = Name.fromString "<=>"
and universalName = Name.fromString "!"
and existentialName = Name.fromString "?";

local
  fun demote True = Term.Fn (truthName,[])
    | demote False = Term.Fn (falsityName,[])
    | demote (Atom (p,tms)) = Term.Fn (p,tms)
    | demote (Not p) =
      let
        val ref s = Term.negation
      in
        Term.Fn (Name.fromString s, [demote p])
      end
    | demote (And (p,q)) = Term.Fn (conjunctionName, [demote p, demote q])
    | demote (Or (p,q)) = Term.Fn (disjunctionName, [demote p, demote q])
    | demote (Imp (p,q)) = Term.Fn (implicationName, [demote p, demote q])
    | demote (Iff (p,q)) = Term.Fn (equivalenceName, [demote p, demote q])
    | demote (Forall (v,b)) = Term.Fn (universalName, [Term.Var v, demote b])
    | demote (Exists (v,b)) =
      Term.Fn (existentialName, [Term.Var v, demote b]);
in
  fun pp fm = Term.pp (demote fm);
end;

val toString = Print.toString pp;

local
  fun isQuant [Term.Var _, _] = true
    | isQuant _ = false;

  fun promote (Term.Var v) = Atom (v,[])
    | promote (Term.Fn (f,tms)) =
      if Name.equal f truthName andalso List.null tms then
        True
      else if Name.equal f falsityName andalso List.null tms then
        False
      else if Name.toString f = !Term.negation andalso length tms = 1 then
        Not (promote (hd tms))
      else if Name.equal f conjunctionName andalso length tms = 2 then
        And (promote (hd tms), promote (List.nth (tms,1)))
      else if Name.equal f disjunctionName andalso length tms = 2 then
        Or (promote (hd tms), promote (List.nth (tms,1)))
      else if Name.equal f implicationName andalso length tms = 2 then
        Imp (promote (hd tms), promote (List.nth (tms,1)))
      else if Name.equal f equivalenceName andalso length tms = 2 then
        Iff (promote (hd tms), promote (List.nth (tms,1)))
      else if Name.equal f universalName andalso isQuant tms then
        Forall (Term.destVar (hd tms), promote (List.nth (tms,1)))
      else if Name.equal f existentialName andalso isQuant tms then
        Exists (Term.destVar (hd tms), promote (List.nth (tms,1)))
      else
        Atom (f,tms);
in
  fun fromString s = promote (Term.fromString s);
end;

val parse = Parse.parseQuotation toString fromString;

(* ------------------------------------------------------------------------- *)
(* Splitting goals.                                                          *)
(* ------------------------------------------------------------------------- *)

local
  fun add_asms asms goal =
      if List.null asms then goal else Imp (listMkConj (List.rev asms), goal);

  fun add_var_asms asms v goal = add_asms asms (Forall (v,goal));

  fun split asms pol fm =
      case (pol,fm) of
        (* Positive splittables *)
        (true,True) => []
      | (true, Not f) => split asms false f
      | (true, And (f1,f2)) => split asms true f1 @ split (f1 :: asms) true f2
      | (true, Or (f1,f2)) => split (Not f1 :: asms) true f2
      | (true, Imp (f1,f2)) => split (f1 :: asms) true f2
      | (true, Iff (f1,f2)) =>
        split (f1 :: asms) true f2 @ split (f2 :: asms) true f1
      | (true, Forall (v,f)) => List.map (add_var_asms asms v) (split [] true f)
        (* Negative splittables *)
      | (false,False) => []
      | (false, Not f) => split asms true f
      | (false, And (f1,f2)) => split (f1 :: asms) false f2
      | (false, Or (f1,f2)) =>
        split asms false f1 @ split (Not f1 :: asms) false f2
      | (false, Imp (f1,f2)) => split asms true f1 @ split (f1 :: asms) false f2
      | (false, Iff (f1,f2)) =>
        split (f1 :: asms) false f2 @ split (f2 :: asms) false f1
      | (false, Exists (v,f)) => List.map (add_var_asms asms v) (split [] false f)
        (* Unsplittables *)
      | _ => [add_asms asms (if pol then fm else Not fm)];
in
  fun splitGoal fm = split [] true fm;
end;

(*MetisTrace3
val splitGoal = fn fm =>
    let
      val result = splitGoal fm
      val () = Print.trace pp "Formula.splitGoal: fm" fm
      val () = Print.trace (Print.ppList pp) "Formula.splitGoal: result" result
    in
      result
    end;
*)

end

structure FormulaOrdered =
struct type t = Formula.formula val compare = Formula.compare end

structure FormulaMap = KeyMap (FormulaOrdered);

structure FormulaSet = ElementSet (FormulaMap);
