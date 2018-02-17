(*  Title:      HOL/Tools/Quotient/quotient_info.ML
    Author:     Cezary Kaliszyk and Christian Urban

Context data for the quotient package.
*)

signature QUOTIENT_INFO =
sig
  type quotmaps = {relmap: string, quot_thm: thm}
  val lookup_quotmaps: Proof.context -> string -> quotmaps option
  val lookup_quotmaps_global: theory -> string -> quotmaps option
  val update_quotmaps: string * quotmaps -> Context.generic -> Context.generic
  val print_quotmaps: Proof.context -> unit

  type abs_rep = {abs : term, rep : term}
  val transform_abs_rep: morphism -> abs_rep -> abs_rep
  val lookup_abs_rep: Proof.context -> string -> abs_rep option
  val lookup_abs_rep_global: theory -> string -> abs_rep option
  val update_abs_rep: string * abs_rep -> Context.generic -> Context.generic
  val print_abs_rep: Proof.context -> unit

  type quotients = {qtyp: typ, rtyp: typ, equiv_rel: term, equiv_thm: thm, quot_thm: thm}
  val transform_quotients: morphism -> quotients -> quotients
  val lookup_quotients: Proof.context -> string -> quotients option
  val lookup_quotients_global: theory -> string -> quotients option
  val update_quotients: string * quotients -> Context.generic -> Context.generic
  val dest_quotients: Proof.context -> quotients list
  val print_quotients: Proof.context -> unit

  type quotconsts = {qconst: term, rconst: term, def: thm}
  val transform_quotconsts: morphism -> quotconsts -> quotconsts
  val lookup_quotconsts_global: theory -> term -> quotconsts option
  val update_quotconsts: string * quotconsts -> Context.generic -> Context.generic
  val dest_quotconsts: Proof.context -> quotconsts list
  val dest_quotconsts_global: theory -> quotconsts list
  val print_quotconsts: Proof.context -> unit
end

structure Quotient_Info: QUOTIENT_INFO =
struct

(** data containers **)

(*info about map- and rel-functions for a type*)
type quotmaps = {relmap: string, quot_thm: thm}
fun transform_quotmaps phi : quotmaps -> quotmaps =
  fn {relmap, quot_thm} => {relmap = relmap, quot_thm = Morphism.thm phi quot_thm}

(*info about abs/rep terms*)
type abs_rep = {abs : term, rep : term}
fun transform_abs_rep phi : abs_rep -> abs_rep =
  fn {abs, rep} => {abs = Morphism.term phi abs, rep = Morphism.term phi rep}

(*info about quotient types*)
type quotients = {qtyp: typ, rtyp: typ, equiv_rel: term, equiv_thm: thm, quot_thm: thm}
fun transform_quotients phi : quotients -> quotients =
  fn {qtyp, rtyp, equiv_rel, equiv_thm, quot_thm} =>
    {qtyp = Morphism.typ phi qtyp,
     rtyp = Morphism.typ phi rtyp,
     equiv_rel = Morphism.term phi equiv_rel,
     equiv_thm = Morphism.thm phi equiv_thm,
     quot_thm = Morphism.thm phi quot_thm}

(*info about quotient constants*)
(*We need to be able to lookup instances of lifted constants,
  for example given "nat fset" we need to find "'a fset";
  but overloaded constants share the same name.*)
type quotconsts = {qconst: term, rconst: term, def: thm}
fun eq_quotconsts (x: quotconsts, y: quotconsts) = #qconst x = #qconst y
fun transform_quotconsts phi : quotconsts -> quotconsts =
  fn {qconst, rconst, def} =>
    {qconst = Morphism.term phi qconst,
     rconst = Morphism.term phi rconst,
     def = Morphism.thm phi def}

structure Data = Generic_Data
(
  type T =
    quotmaps Symtab.table *
    abs_rep Symtab.table *
    quotients Symtab.table *
    quotconsts list Symtab.table
  val empty: T = (Symtab.empty, Symtab.empty, Symtab.empty, Symtab.empty)
  val extend = I
  fun merge
   ((quotmaps1, abs_rep1, quotients1, quotconsts1),
    (quotmaps2, abs_rep2, quotients2, quotconsts2)) : T =
   (Symtab.merge (K true) (quotmaps1, quotmaps2),
    Symtab.merge (K true) (abs_rep1, abs_rep2),
    Symtab.merge (K true) (quotients1, quotients2),
    Symtab.merge_list eq_quotconsts (quotconsts1, quotconsts2))
)

val get_quotmaps = #1 o Data.get
val get_abs_rep = #2 o Data.get
val get_quotients = #3 o Data.get
val get_quotconsts = #4 o Data.get

val map_quotmaps = Data.map o @{apply 4(1)}
val map_abs_rep = Data.map o @{apply 4(2)}
val map_quotients = Data.map o @{apply 4(3)}
val map_quotconsts = Data.map o @{apply 4(4)}


(* quotmaps *)

fun lookup_quotmaps_generic context name =
  Symtab.lookup (get_quotmaps context) name
  |> Option.map (transform_quotmaps (Morphism.transfer_morphism (Context.theory_of context)))

val lookup_quotmaps = lookup_quotmaps_generic o Context.Proof
val lookup_quotmaps_global = lookup_quotmaps_generic o Context.Theory

val update_quotmaps =
  map_quotmaps o Symtab.update o apsnd (transform_quotmaps Morphism.trim_context_morphism)

val _ =
  Theory.setup
   (Attrib.setup @{binding mapQ3}
      ((Args.type_name {proper = true, strict = true} --| Scan.lift @{keyword "="}) --
        (Scan.lift @{keyword "("} |--
          Args.const {proper = true, strict = true} --| Scan.lift @{keyword ","} --
          Attrib.thm --| Scan.lift @{keyword ")"}) >>
        (fn (tyname, (relmap, quot_thm)) =>
          Thm.declaration_attribute
            (K (update_quotmaps (tyname, {relmap = relmap, quot_thm = quot_thm})))))
      "declaration of map information")

fun print_quotmaps ctxt =
  let
    fun prt_map (ty_name, {relmap, quot_thm}) =
      Pretty.block (separate (Pretty.brk 2)
         [Pretty.str "type:",
          Pretty.str ty_name,
          Pretty.str "relation map:",
          Pretty.str relmap,
          Pretty.str "quot. theorem:",
          Syntax.pretty_term ctxt (Thm.prop_of quot_thm)])
  in
    map prt_map (Symtab.dest (get_quotmaps (Context.Proof ctxt)))
    |> Pretty.big_list "maps for type constructors:"
    |> Pretty.writeln
  end


(* abs_rep *)

val lookup_abs_rep = Symtab.lookup o get_abs_rep o Context.Proof
val lookup_abs_rep_global = Symtab.lookup o get_abs_rep o Context.Theory

val update_abs_rep =
  map_abs_rep o Symtab.update o apsnd (transform_abs_rep Morphism.trim_context_morphism)

fun print_abs_rep ctxt =
  let
    fun prt_abs_rep (s, {abs, rep}) =
      Pretty.block (separate (Pretty.brk 2)
       [Pretty.str "type constructor:",
        Pretty.str s,
        Pretty.str "abs term:",
        Syntax.pretty_term ctxt abs,
        Pretty.str "rep term:",
        Syntax.pretty_term ctxt rep])
  in
    map prt_abs_rep (Symtab.dest (get_abs_rep (Context.Proof ctxt)))
    |> Pretty.big_list "abs/rep terms:"
    |> Pretty.writeln
  end


(* quotients *)

fun lookup_quotients_generic context name =
  Symtab.lookup (get_quotients context) name
  |> Option.map (transform_quotients (Morphism.transfer_morphism (Context.theory_of context)))

val lookup_quotients = lookup_quotients_generic o Context.Proof
val lookup_quotients_global = lookup_quotients_generic o Context.Theory

val update_quotients =
  map_quotients o Symtab.update o apsnd (transform_quotients Morphism.trim_context_morphism)

fun dest_quotients ctxt =
  map snd (Symtab.dest (get_quotients (Context.Proof ctxt)))

fun print_quotients ctxt =
  let
    fun prt_quot {qtyp, rtyp, equiv_rel, equiv_thm, quot_thm} =
      Pretty.block (separate (Pretty.brk 2)
       [Pretty.str "quotient type:",
        Syntax.pretty_typ ctxt qtyp,
        Pretty.str "raw type:",
        Syntax.pretty_typ ctxt rtyp,
        Pretty.str "relation:",
        Syntax.pretty_term ctxt equiv_rel,
        Pretty.str "equiv. thm:",
        Syntax.pretty_term ctxt (Thm.prop_of equiv_thm),
        Pretty.str "quot. thm:",
        Syntax.pretty_term ctxt (Thm.prop_of quot_thm)])
  in
    map (prt_quot o snd) (Symtab.dest (get_quotients (Context.Proof ctxt)))
    |> Pretty.big_list "quotients:"
    |> Pretty.writeln
  end


(* quotconsts *)

val update_quotconsts =
  map_quotconsts o Symtab.cons_list o apsnd (transform_quotconsts Morphism.trim_context_morphism)

fun dest_quotconsts_generic context =
  maps #2 (Symtab.dest (get_quotconsts context))
  |> map (transform_quotconsts (Morphism.transfer_morphism (Context.theory_of context)))

val dest_quotconsts = dest_quotconsts_generic o Context.Proof
val dest_quotconsts_global = dest_quotconsts_generic o Context.Theory

fun lookup_quotconsts_global thy t =
  let
    val (name, qty) = dest_Const t
  in
    Symtab.lookup_list (get_quotconsts (Context.Theory thy)) name
    |> find_first (fn {qconst, ...} =>
        let val (name', qty') = dest_Const qconst
        in name = name' andalso Sign.typ_instance thy (qty, qty') end)
    |> Option.map (transform_quotconsts (Morphism.transfer_morphism thy))
  end

fun print_quotconsts ctxt =
  let
    fun prt_qconst {qconst, rconst, def} =
      Pretty.block (separate (Pretty.brk 1)
       [Syntax.pretty_term ctxt qconst,
        Pretty.str ":=",
        Syntax.pretty_term ctxt rconst,
        Pretty.str "as",
        Syntax.pretty_term ctxt (Thm.prop_of def)])
  in
    map prt_qconst (dest_quotconsts ctxt)
    |> Pretty.big_list "quotient constants:"
    |> Pretty.writeln
  end


(* outer syntax commands *)

val _ =
  Outer_Syntax.command @{command_keyword print_quotmapsQ3} "print quotient map functions"
    (Scan.succeed (Toplevel.keep (print_quotmaps o Toplevel.context_of)))

val _ =
  Outer_Syntax.command @{command_keyword print_quotientsQ3} "print quotients"
    (Scan.succeed (Toplevel.keep (print_quotients o Toplevel.context_of)))

val _ =
  Outer_Syntax.command @{command_keyword print_quotconsts} "print quotient constants"
    (Scan.succeed (Toplevel.keep (print_quotconsts o Toplevel.context_of)))

end
