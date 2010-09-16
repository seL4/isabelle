(* ========================================================================= *)
(* FIRST ORDER LOGIC SUBSTITUTIONS                                           *)
(* Copyright (c) 2002 Joe Hurd, distributed under the BSD License            *)
(* ========================================================================= *)

structure Subst :> Subst =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* A type of first order logic substitutions.                                *)
(* ------------------------------------------------------------------------- *)

datatype subst = Subst of Term.term NameMap.map;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val empty = Subst (NameMap.new ());

fun null (Subst m) = NameMap.null m;

fun size (Subst m) = NameMap.size m;

fun peek (Subst m) v = NameMap.peek m v;

fun insert (Subst m) v_tm = Subst (NameMap.insert m v_tm);

fun singleton v_tm = insert empty v_tm;

fun toList (Subst m) = NameMap.toList m;

fun fromList l = Subst (NameMap.fromList l);

fun foldl f b (Subst m) = NameMap.foldl f b m;

fun foldr f b (Subst m) = NameMap.foldr f b m;

fun pp sub =
    Print.ppBracket "<[" "]>"
      (Print.ppOpList "," (Print.ppOp2 " |->" Name.pp Term.pp))
      (toList sub);

val toString = Print.toString pp;

(* ------------------------------------------------------------------------- *)
(* Normalizing removes identity substitutions.                               *)
(* ------------------------------------------------------------------------- *)

local
  fun isNotId (v,tm) = not (Term.equalVar v tm);
in
  fun normalize (sub as Subst m) =
      let
        val m' = NameMap.filter isNotId m
      in
        if NameMap.size m = NameMap.size m' then sub else Subst m'
      end;
end;

(* ------------------------------------------------------------------------- *)
(* Applying a substitution to a first order logic term.                      *)
(* ------------------------------------------------------------------------- *)

fun subst sub =
    let
      fun tmSub (tm as Term.Var v) =
          (case peek sub v of
             SOME tm' => if Portable.pointerEqual (tm,tm') then tm else tm'
           | NONE => tm)
        | tmSub (tm as Term.Fn (f,args)) =
          let
            val args' = Sharing.map tmSub args
          in
            if Portable.pointerEqual (args,args') then tm
            else Term.Fn (f,args')
          end
    in
      fn tm => if null sub then tm else tmSub tm
    end;

(* ------------------------------------------------------------------------- *)
(* Restricting a substitution to a given set of variables.                   *)
(* ------------------------------------------------------------------------- *)

fun restrict (sub as Subst m) varSet =
    let
      fun isRestrictedVar (v,_) = NameSet.member v varSet

      val m' = NameMap.filter isRestrictedVar m
    in
      if NameMap.size m = NameMap.size m' then sub else Subst m'
    end;

fun remove (sub as Subst m) varSet =
    let
      fun isRestrictedVar (v,_) = not (NameSet.member v varSet)

      val m' = NameMap.filter isRestrictedVar m
    in
      if NameMap.size m = NameMap.size m' then sub else Subst m'
    end;

(* ------------------------------------------------------------------------- *)
(* Composing two substitutions so that the following identity holds:         *)
(*                                                                           *)
(* subst (compose sub1 sub2) tm = subst sub2 (subst sub1 tm)                 *)
(* ------------------------------------------------------------------------- *)

fun compose (sub1 as Subst m1) sub2 =
    let
      fun f (v,tm,s) = insert s (v, subst sub2 tm)
    in
      if null sub2 then sub1 else NameMap.foldl f sub2 m1
    end;

(* ------------------------------------------------------------------------- *)
(* Creating the union of two compatible substitutions.                       *)
(* ------------------------------------------------------------------------- *)

local
  fun compatible ((_,tm1),(_,tm2)) =
      if Term.equal tm1 tm2 then SOME tm1
      else raise Error "Subst.union: incompatible";
in
  fun union (s1 as Subst m1) (s2 as Subst m2) =
      if NameMap.null m1 then s2
      else if NameMap.null m2 then s1
      else Subst (NameMap.union compatible m1 m2);
end;

(* ------------------------------------------------------------------------- *)
(* Substitutions can be inverted iff they are renaming substitutions.        *)
(* ------------------------------------------------------------------------- *)

local
  fun inv (v, Term.Var w, s) =
      if NameMap.inDomain w s then raise Error "Subst.invert: non-injective"
      else NameMap.insert s (w, Term.Var v)
    | inv (_, Term.Fn _, _) = raise Error "Subst.invert: non-variable";
in
  fun invert (Subst m) = Subst (NameMap.foldl inv (NameMap.new ()) m);
end;

val isRenaming = can invert;

(* ------------------------------------------------------------------------- *)
(* Creating a substitution to freshen variables.                             *)
(* ------------------------------------------------------------------------- *)

val freshVars =
    let
      fun add (v,m) = insert m (v, Term.newVar ())
    in
      NameSet.foldl add empty
    end;

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

val redexes =
    let
      fun add (v,_,s) = NameSet.add s v
    in
      foldl add NameSet.empty
    end;

val residueFreeVars =
    let
      fun add (_,t,s) = NameSet.union s (Term.freeVars t)
    in
      foldl add NameSet.empty
    end;

val freeVars =
    let
      fun add (v,t,s) = NameSet.union (NameSet.add s v) (Term.freeVars t)
    in
      foldl add NameSet.empty
    end;

(* ------------------------------------------------------------------------- *)
(* Functions.                                                                *)
(* ------------------------------------------------------------------------- *)

val functions =
    let
      fun add (_,t,s) = NameAritySet.union s (Term.functions t)
    in
      foldl add NameAritySet.empty
    end;

(* ------------------------------------------------------------------------- *)
(* Matching for first order logic terms.                                     *)
(* ------------------------------------------------------------------------- *)

local
  fun matchList sub [] = sub
    | matchList sub ((Term.Var v, tm) :: rest) =
      let
        val sub =
            case peek sub v of
              NONE => insert sub (v,tm)
            | SOME tm' =>
              if Term.equal tm tm' then sub
              else raise Error "Subst.match: incompatible matches"
      in
        matchList sub rest
      end
    | matchList sub ((Term.Fn (f1,args1), Term.Fn (f2,args2)) :: rest) =
      if Name.equal f1 f2 andalso length args1 = length args2 then
        matchList sub (zip args1 args2 @ rest)
      else raise Error "Subst.match: different structure"
    | matchList _ _ = raise Error "Subst.match: functions can't match vars";
in
  fun match sub tm1 tm2 = matchList sub [(tm1,tm2)];
end;

(* ------------------------------------------------------------------------- *)
(* Unification for first order logic terms.                                  *)
(* ------------------------------------------------------------------------- *)

local
  fun solve sub [] = sub
    | solve sub ((tm1_tm2 as (tm1,tm2)) :: rest) =
      if Portable.pointerEqual tm1_tm2 then solve sub rest
      else solve' sub (subst sub tm1) (subst sub tm2) rest

  and solve' sub (Term.Var v) tm rest =
      if Term.equalVar v tm then solve sub rest
      else if Term.freeIn v tm then raise Error "Subst.unify: occurs check"
      else
        (case peek sub v of
           NONE => solve (compose sub (singleton (v,tm))) rest
         | SOME tm' => solve' sub tm' tm rest)
    | solve' sub tm1 (tm2 as Term.Var _) rest = solve' sub tm2 tm1 rest
    | solve' sub (Term.Fn (f1,args1)) (Term.Fn (f2,args2)) rest =
      if Name.equal f1 f2 andalso length args1 = length args2 then
        solve sub (zip args1 args2 @ rest)
      else
        raise Error "Subst.unify: different structure";
in
  fun unify sub tm1 tm2 = solve sub [(tm1,tm2)];
end;

end
