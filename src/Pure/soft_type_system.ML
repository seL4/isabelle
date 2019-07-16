(*  Title:      Pure/soft_type_system.ML
    Author:     Alexander Krauss
    Author:     Makarius

Support for a soft-type system within the Isabelle logical framework.
*)

signature SOFT_TYPE_SYSTEM =
sig
  type operations =
    {augment: term -> Proof.context -> Proof.context,
     implicit_vars: Proof.context -> term -> (string * typ) list,
     purge: theory -> term -> term}
  val setup: operations -> theory -> theory
  val augment: term -> Proof.context -> Proof.context
  val implicit_vars: Proof.context -> term -> (string * typ) list
  val global_purge: theory -> term -> term
  val purge: Proof.context -> term -> term
end;

structure Soft_Type_System: SOFT_TYPE_SYSTEM =
struct

(* operations *)

type operations =
  {
    (*extend the proof context by additional information present in the
      given term, e.g. assumptions about variables*)
    augment: term -> Proof.context -> Proof.context,

    (*variables from the term that are implicitly introduced into the
      context via this statement*)
    implicit_vars: Proof.context -> term -> (string * typ) list,

    (*purge soft type annotations encoded in a term*)
    purge: theory -> term -> term
  };

val no_operations: operations =
 {augment = K I,
  implicit_vars = K (K []),
  purge = K I};


(* theory data *)

structure Data = Theory_Data
(
  type T = (operations * stamp) option;
  val empty = NONE;
  val extend = I;
  fun merge (data as SOME (_, s), SOME (_, s')) =
        if s = s' then data
        else error "Cannot merge theories with different soft-type systems"
    | merge data = merge_options data;
);

fun setup operations =
  Data.map (fn data =>
    (case data of
      NONE => SOME (operations, stamp ())
    | SOME _ => error "Duplicate setup of soft-type system"));


(* get operations *)

fun global_operations thy =
  (case Data.get thy of SOME (ops, _) => ops | NONE => no_operations);

val operations = global_operations o Proof_Context.theory_of;

fun augment t ctxt = #augment (operations ctxt) t ctxt;
fun implicit_vars ctxt t = #implicit_vars (operations ctxt) ctxt t;

fun global_purge thy t = #purge (global_operations thy) thy t;
val purge = global_purge o Proof_Context.theory_of;

end;
