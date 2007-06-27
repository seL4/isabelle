(* ========================================================================= *)
(* FIRST ORDER LOGIC TERMS                                                   *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Term =
sig

(* ------------------------------------------------------------------------- *)
(* A type of first order logic terms.                                        *)
(* ------------------------------------------------------------------------- *)

type var = Name.name

type functionName = Name.name

type function = functionName * int

type const = functionName

datatype term =
    Var of var
  | Fn of functionName * term list

(* ------------------------------------------------------------------------- *)
(* Constructors and destructors.                                             *)
(* ------------------------------------------------------------------------- *)

(* Variables *)

val destVar : term -> var

val isVar : term -> bool

val equalVar : var -> term -> bool

(* Functions *)

val destFn : term -> functionName * term list

val isFn : term -> bool

val fnName : term -> functionName

val fnArguments : term -> term list

val fnArity : term -> int

val fnFunction : term -> function

val functions : term -> NameAritySet.set

val functionNames : term -> NameSet.set

(* Constants *)

val mkConst : const -> term

val destConst : term -> const

val isConst : term -> bool

(* Binary functions *)

val mkBinop : functionName -> term * term -> term

val destBinop : functionName -> term -> term * term

val isBinop : functionName -> term -> bool

(* ------------------------------------------------------------------------- *)
(* The size of a term in symbols.                                            *)
(* ------------------------------------------------------------------------- *)

val symbols : term -> int

(* ------------------------------------------------------------------------- *)
(* A total comparison function for terms.                                    *)
(* ------------------------------------------------------------------------- *)

val compare : term * term -> order

(* ------------------------------------------------------------------------- *)
(* Subterms.                                                                 *)
(* ------------------------------------------------------------------------- *)

type path = int list

val subterm : term -> path -> term

val subterms : term -> (path * term) list

val replace : term -> path * term -> term

val find : (term -> bool) -> term -> path option

val ppPath : path Parser.pp

val pathToString : path -> string

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

val freeIn : var -> term -> bool

val freeVars : term -> NameSet.set

(* ------------------------------------------------------------------------- *)
(* Fresh variables.                                                          *)
(* ------------------------------------------------------------------------- *)

val newVar : unit -> term

val newVars : int -> term list

val variantPrime : NameSet.set -> var -> var

val variantNum : NameSet.set -> var -> var

(* ------------------------------------------------------------------------- *)
(* Special support for terms with type annotations.                          *)
(* ------------------------------------------------------------------------- *)

val isTypedVar : term -> bool

val typedSymbols : term -> int

val nonVarTypedSubterms : term -> (path * term) list

(* ------------------------------------------------------------------------- *)
(* Special support for terms with an explicit function application operator. *)
(* ------------------------------------------------------------------------- *)

val mkComb : term * term -> term

val destComb : term -> term * term

val isComb : term -> bool

val listMkComb : term * term list -> term

val stripComb : term -> term * term list

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty printing.                                              *)
(* ------------------------------------------------------------------------- *)

(* Infix symbols *)

val infixes : Parser.infixities ref

(* The negation symbol *)

val negation : Name.name ref

(* Binder symbols *)

val binders : Name.name list ref

(* Bracket symbols *)

val brackets : (Name.name * Name.name) list ref

(* Pretty printing *)

val pp : term Parser.pp

val toString : term -> string

(* Parsing *)

val fromString : string -> term

val parse : term Parser.quotation -> term

end
