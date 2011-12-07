(* ========================================================================= *)
(* NAME/ARITY PAIRS                                                          *)
(* Copyright (c) 2004 Joe Hurd, distributed under the BSD License            *)
(* ========================================================================= *)

structure NameArity :> NameArity =
struct

(* ------------------------------------------------------------------------- *)
(* A type of name/arity pairs.                                               *)
(* ------------------------------------------------------------------------- *)

type nameArity = Name.name * int;

fun name ((n,_) : nameArity) = n;

fun arity ((_,i) : nameArity) = i;

(* ------------------------------------------------------------------------- *)
(* Testing for different arities.                                            *)
(* ------------------------------------------------------------------------- *)

fun nary i n_i = arity n_i = i;

val nullary = nary 0
and unary = nary 1
and binary = nary 2
and ternary = nary 3;

(* ------------------------------------------------------------------------- *)
(* A total ordering.                                                         *)
(* ------------------------------------------------------------------------- *)

fun compare ((n1,i1),(n2,i2)) =
    case Name.compare (n1,n2) of
      LESS => LESS
    | EQUAL => Int.compare (i1,i2)
    | GREATER => GREATER;

fun equal (n1,i1) (n2,i2) = i1 = i2 andalso Name.equal n1 n2;

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty printing.                                              *)
(* ------------------------------------------------------------------------- *)

fun pp (n,i) =
    Print.inconsistentBlock 0
      [Name.pp n,
       Print.ppString "/",
       Print.ppInt i];

end

structure NameArityOrdered =
struct type t = NameArity.nameArity val compare = NameArity.compare end

structure NameArityMap =
struct

local
  structure S = KeyMap (NameArityOrdered);
in
  open S;
end;

fun compose m1 m2 =
    let
      fun pk ((_,a),n) = peek m2 (n,a)
    in
      mapPartial pk m1
    end;

end

structure NameAritySet =
struct

local
  structure S = ElementSet (NameArityMap);
in
  open S;
end;

val allNullary = all NameArity.nullary;

val pp =
    Print.ppMap
      toList
      (Print.ppBracket "{" "}" (Print.ppOpList "," NameArity.pp));


end
