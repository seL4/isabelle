(*  Title:      HOL/Tools/Lifting/lifting_info.ML
    Author:     Ondrej Kuncar

Context data for the lifting package.
*)

signature LIFTING_INFO =
sig
  type quotmaps = {rel_quot_thm: thm}
  val lookup_quotmaps: Proof.context -> string -> quotmaps option
  val lookup_quotmaps_global: theory -> string -> quotmaps option
  val print_quotmaps: Proof.context -> unit

  type quotients = {quot_thm: thm}
  val transform_quotients: morphism -> quotients -> quotients
  val lookup_quotients: Proof.context -> string -> quotients option
  val lookup_quotients_global: theory -> string -> quotients option
  val update_quotients: string -> quotients -> Context.generic -> Context.generic
  val dest_quotients: Proof.context -> quotients list
  val print_quotients: Proof.context -> unit

  val get_invariant_commute_rules: Proof.context -> thm list

  val setup: theory -> theory
end;

structure Lifting_Info: LIFTING_INFO =
struct

open Lifting_Util

(** data containers **)

(* info about Quotient map theorems *)
type quotmaps = {rel_quot_thm: thm}

structure Quotmaps = Generic_Data
(
  type T = quotmaps Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data = Symtab.merge (K true) data
)

val lookup_quotmaps = Symtab.lookup o Quotmaps.get o Context.Proof
val lookup_quotmaps_global = Symtab.lookup o Quotmaps.get o Context.Theory

(* FIXME export proper internal update operation!? *)

fun add_quot_map rel_quot_thm ctxt = 
  let
    val rel_quot_thm_concl = (Logic.strip_imp_concl o prop_of) rel_quot_thm
    val (_, abs, _, _) = (dest_Quotient o HOLogic.dest_Trueprop) rel_quot_thm_concl
    val relatorT_name = (fst o dest_Type o fst o dest_funT o fastype_of) abs
    val minfo = {rel_quot_thm = rel_quot_thm}
  in
    Quotmaps.map (Symtab.update (relatorT_name, minfo)) ctxt
  end    

val quotmaps_attribute_setup =
  Attrib.setup @{binding quot_map} (Scan.succeed (Thm.declaration_attribute add_quot_map))
    "declaration of the Quotient map theorem"

fun print_quotmaps ctxt =
  let
    fun prt_map (ty_name, {rel_quot_thm}) =
      Pretty.block (separate (Pretty.brk 2)
         [Pretty.str "type:", 
          Pretty.str ty_name,
          Pretty.str "quot. theorem:", 
          Syntax.pretty_term ctxt (prop_of rel_quot_thm)])
  in
    map prt_map (Symtab.dest (Quotmaps.get (Context.Proof ctxt)))
    |> Pretty.big_list "maps for type constructors:"
    |> Pretty.writeln
  end

(* info about quotient types *)
type quotients = {quot_thm: thm}

structure Quotients = Generic_Data
(
  type T = quotients Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data = Symtab.merge (K true) data
)

fun transform_quotients phi {quot_thm} =
  {quot_thm = Morphism.thm phi quot_thm}

val lookup_quotients = Symtab.lookup o Quotients.get o Context.Proof
val lookup_quotients_global = Symtab.lookup o Quotients.get o Context.Theory

fun update_quotients str qinfo = Quotients.map (Symtab.update (str, qinfo))

fun dest_quotients ctxt =  (* FIXME slightly expensive way to retrieve data *)
  map snd (Symtab.dest (Quotients.get (Context.Proof ctxt)))

fun print_quotients ctxt =
  let
    fun prt_quot (qty_name, {quot_thm}) =
      Pretty.block (separate (Pretty.brk 2)
       [Pretty.str "type:", 
        Pretty.str qty_name,
        Pretty.str "quot. thm:",
        Syntax.pretty_term ctxt (prop_of quot_thm)])
  in
    map prt_quot (Symtab.dest (Quotients.get (Context.Proof ctxt)))
    |> Pretty.big_list "quotients:"
    |> Pretty.writeln
  end

structure Invariant_Commute = Named_Thms
(
  val name = @{binding invariant_commute}
  val description = "theorems that a relator of an invariant is an invariant of the corresponding predicate"
)

fun get_invariant_commute_rules ctxt = map safe_mk_meta_eq (Invariant_Commute.get ctxt)

(* theory setup *)

val setup =
  quotmaps_attribute_setup
  #> Invariant_Commute.setup

(* outer syntax commands *)

val _ =
  Outer_Syntax.improper_command @{command_spec "print_quotmaps"} "print quotient map functions"
    (Scan.succeed (Toplevel.keep (print_quotmaps o Toplevel.context_of)))

val _ =
  Outer_Syntax.improper_command @{command_spec "print_quotients"} "print quotients"
    (Scan.succeed (Toplevel.keep (print_quotients o Toplevel.context_of)))

end;