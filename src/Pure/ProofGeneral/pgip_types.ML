(*  Title:      Pure/ProofGeneral/pgip_types.ML
    Author:     David Aspinall

Some PGIP types and conversions.
*)

signature PGIPTYPES =
sig
  val attr: string -> string -> XML.attributes
  val opt_attr: string -> string option -> XML.attributes
  val get_attr: XML.attributes -> string -> string           (* raises PGIP *)

  datatype pgiptype =
      Pgipnull | Pgipbool | Pgipint of int option * int option | Pgipnat | Pgipreal
    | Pgipstring | Pgipconst of string | Pgipchoice of pgipdtype list

  and pgipdtype = Pgipdtype of string option * pgiptype  (* type with opt. description *)

  exception PGIP of string

  val pgiptype_to_xml   : pgiptype -> XML.tree
end

structure PgipTypes : PGIPTYPES =
struct

exception PGIP of string

(** XML utils **)

fun get_attr attrs name =
  (case Properties.get attrs name of
    SOME value => value
  | NONE => raise PGIP ("Missing attribute: " ^ quote name));

fun attr x y = [(x,y)] : XML.attributes

fun opt_attr _ NONE = []
  | opt_attr name (SOME value) = attr name value;


(* PGIP datatypes.

   This is a reflection of the type structure of PGIP configuration,
   which is meant for setting up user dialogs and preference settings.
   These are configured declaratively in XML, using a syntax for types
   and values which is like a (vastly cut down) form of XML Schema
   Datatypes.

   The prover needs to interpret the strings representing the typed
   values, at least for the types it expects from the dialogs it
   configures.  Here we go further and construct a type-safe
   encapsulation of these values, which would be useful for more
   advanced cases (e.g. generating and processing forms).
*)


datatype pgiptype =
         Pgipnull                            (* unit type: unique element is empty string *)
       | Pgipbool                            (* booleans: "true" or "false" *)
       | Pgipint of int option * int option  (* ranged integers, should be XSD canonical *)
       | Pgipnat                             (* naturals: non-negative integers (convenience) *)
       | Pgipreal                            (* floating-point numbers *)
       | Pgipstring                          (* non-empty strings *)
       | Pgipconst of string                 (* singleton type *)
       | Pgipchoice of pgipdtype list        (* union type *)

(* Compared with the PGIP schema, we push descriptions of types inside choices. *)

and pgipdtype = Pgipdtype of string option * pgiptype

datatype pgipuval =
    Pgvalnull | Pgvalbool of bool | Pgvalint of int | Pgvalnat of int | Pgvalreal of real
  | Pgvalstring of string | Pgvalconst of string

type pgipval = pgiptype * pgipuval      (* type-safe values *)

fun pgipdtype_to_xml (desco,ty) =
    let
        val desc_attr = opt_attr "descr" desco

        val elt = case ty of
                      Pgipnull => "pgipnull"
                    | Pgipbool => "pgipbool"
                    | Pgipint _ => "pgipint"
                    | Pgipnat => "pgipint"
                    | Pgipreal => "pgipint"  (*sic!*)  (*required for PG 4.0 and 3.7.x*)
                    | Pgipstring => "pgipstring"
                    | Pgipconst _ => "pgipconst"
                    | Pgipchoice _ => "pgipchoice"

        fun range_attr r v = attr r (Markup.print_int v)

        val attrs = case ty of
                        Pgipint (SOME min,SOME max) => (range_attr "min" min)@(range_attr "max" max)
                      | Pgipint (SOME min,NONE) => (range_attr "min" min)
                      | Pgipint (NONE,SOME max) => (range_attr "max" max)
                      | Pgipnat => (range_attr "min" 0)
                      | Pgipconst nm => attr "name" nm
                      | _ => []

        fun destpgipdtype (Pgipdtype x) = x

        val typargs = case ty of
                          Pgipchoice ds => map destpgipdtype ds
                        | _ => []
    in
        XML.Elem ((elt, desc_attr @ attrs), map pgipdtype_to_xml typargs)
    end

val pgiptype_to_xml = pgipdtype_to_xml o pair NONE

end

