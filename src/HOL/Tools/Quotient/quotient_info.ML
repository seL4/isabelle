(*  Title:      HOL/Tools/Quotient/quotient_info.ML
    Author:     Cezary Kaliszyk and Christian Urban

Context data for the quotient package.
*)

signature QUOTIENT_INFO =
sig
  type quotmaps = {relmap: string, quot_thm: thm}
  val lookup_quotmaps: Proof.context -> string -> quotmaps option
  val lookup_quotmaps_global: theory -> string -> quotmaps option
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
  val dest_quotconsts_global: theory -> quotconsts list
  val dest_quotconsts: Proof.context -> quotconsts list
  val print_quotconsts: Proof.context -> unit
end;

structure Quotient_Info: QUOTIENT_INFO =
struct

(** data containers **)

(*info about map- and rel-functions for a type*)
type quotmaps = {relmap: string, quot_thm: thm}

(*info about abs/rep terms*)
type abs_rep = {abs : term, rep : term}
fun transform_abs_rep phi {abs, rep} : abs_rep =
  {abs = Morphism.term phi abs, rep = Morphism.term phi rep}

(*info about quotient types*)
type quotients = {qtyp: typ, rtyp: typ, equiv_rel: term, equiv_thm: thm, quot_thm: thm}
fun transform_quotients phi {qtyp, rtyp, equiv_rel, equiv_thm, quot_thm} : quotients =
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
fun transform_quotconsts phi {qconst, rconst, def} : quotconsts =
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

val lookup_quotmaps = Symtab.lookup o get_quotmaps o Context.Proof
val lookup_quotmaps_global = Symtab.lookup o get_quotmaps o Context.Theory

(* FIXME export proper internal update operation!? *)

val _ =
  Theory.setup
   (Attrib.setup @{binding mapQ3}
      ((Args.type_name {proper = true, strict = true} --| Scan.lift @{keyword "="}) --
        (Scan.lift @{keyword "("} |--
          Args.const {proper = true, strict = true} --| Scan.lift @{keyword ","} --
          Attrib.thm --| Scan.lift @{keyword ")"}) >>
        (fn (tyname, (relname, qthm)) =>
          let val minfo = {relmap = relname, quot_thm = qthm}
          in Thm.declaration_attribute (fn _ => map_quotmaps (Symtab.update (tyname, minfo))) end))
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
          Syntax.pretty_term ctxt (prop_of quot_thm)])
  in
    map prt_map (Symtab.dest (get_quotmaps (Context.Proof ctxt)))
    |> Pretty.big_list "maps for type constructors:"
    |> Pretty.writeln
  end


(* abs_rep *)

val lookup_abs_rep = Symtab.lookup o get_abs_rep o Context.Proof
val lookup_abs_rep_global = Symtab.lookup o get_abs_rep o Context.Theory

val update_abs_rep = map_abs_rep o Symtab.update

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

val lookup_quotients = Symtab.lookup o get_quotients o Context.Proof
val lookup_quotients_global = Symtab.lookup o get_quotients o Context.Theory

val update_quotients = map_quotients o Symtab.update

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
        Syntax.pretty_term ctxt (prop_of equiv_thm),
        Pretty.str "quot. thm:",
        Syntax.pretty_term ctxt (prop_of quot_thm)])
  in
    map (prt_quot o snd) (Symtab.dest (get_quotients (Context.Proof ctxt)))
    |> Pretty.big_list "quotients:"
    |> Pretty.writeln
  end


(* quotconsts *)

val update_quotconsts = map_quotconsts o Symtab.cons_list

fun dest_quotconsts ctxt =
  maps snd (Symtab.dest (get_quotconsts (Context.Proof ctxt)))

fun dest_quotconsts_global thy =
  maps snd (Symtab.dest (get_quotconsts (Context.Theory thy)))

fun lookup_quotconsts_global thy t =
  let
    val (name, qty) = dest_Const t
    fun matches (x: quotconsts) =
      let val (name', qty') = dest_Const (#qconst x);
      in name = name' andalso Sign.typ_instance thy (qty, qty') end
  in
    (case Symtab.lookup (get_quotconsts (Context.Theory thy)) name of
      NONE => NONE
    | SOME l => find_first matches l)
  end

fun print_quotconsts ctxt =
  let
    fun prt_qconst {qconst, rconst, def} =
      Pretty.block (separate (Pretty.brk 1)
       [Syntax.pretty_term ctxt qconst,
        Pretty.str ":=",
        Syntax.pretty_term ctxt rconst,
        Pretty.str "as",
        Syntax.pretty_term ctxt (prop_of def)])
  in
    map prt_qconst (maps snd (Symtab.dest (get_quotconsts (Context.Proof ctxt))))
    |> Pretty.big_list "quotient constants:"
    |> Pretty.writeln
  end


(* outer syntax commands *)

val _ =
  Outer_Syntax.command @{command_spec "print_quotmapsQ3"} "print quotient map functions"
    (Scan.succeed (Toplevel.keep (print_quotmaps o Toplevel.context_of)))

val _ =
  Outer_Syntax.command @{command_spec "print_quotientsQ3"} "print quotients"
    (Scan.succeed (Toplevel.keep (print_quotients o Toplevel.context_of)))

val _ =
  Outer_Syntax.command @{command_spec "print_quotconsts"} "print quotient constants"
    (Scan.succeed (Toplevel.keep (print_quotconsts o Toplevel.context_of)))

end;
