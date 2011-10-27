(*  Title:      HOL/Tools/Quotient/quotient_info.ML
    Author:     Cezary Kaliszyk and Christian Urban

Data slots for the quotient package.
*)

(* FIXME odd names/signatures of data access operations *)

signature QUOTIENT_INFO =
sig

  type maps_info = {mapfun: string, relmap: string}
  val maps_lookup: theory -> string -> maps_info option
  val maps_update_thy: string -> maps_info -> theory -> theory
  val maps_update: string -> maps_info -> Proof.context -> Proof.context
  val print_mapsinfo: Proof.context -> unit

  type quotdata_info = {qtyp: typ, rtyp: typ, equiv_rel: term, equiv_thm: thm}
  val transform_quotdata: morphism -> quotdata_info -> quotdata_info
  val quotdata_lookup: theory -> string -> quotdata_info option
  val quotdata_update_thy: string -> quotdata_info -> theory -> theory
  val quotdata_update_gen: string -> quotdata_info -> Context.generic -> Context.generic
  val quotdata_dest: Proof.context -> quotdata_info list
  val print_quotinfo: Proof.context -> unit

  type qconsts_info = {qconst: term, rconst: term, def: thm}
  val transform_qconsts: morphism -> qconsts_info -> qconsts_info
  val qconsts_lookup: theory -> term -> qconsts_info option
  val qconsts_update_thy: string -> qconsts_info -> theory -> theory
  val qconsts_update_gen: string -> qconsts_info -> Context.generic -> Context.generic
  val qconsts_dest: Proof.context -> qconsts_info list
  val print_qconstinfo: Proof.context -> unit

  val equiv_rules_get: Proof.context -> thm list
  val equiv_rules_add: attribute
  val rsp_rules_get: Proof.context -> thm list
  val rsp_rules_add: attribute
  val prs_rules_get: Proof.context -> thm list
  val prs_rules_add: attribute
  val id_simps_get: Proof.context -> thm list
  val quotient_rules_get: Proof.context -> thm list
  val quotient_rules_add: attribute
  val setup: theory -> theory
end;

structure Quotient_Info: QUOTIENT_INFO =
struct

(** data containers **)

(* FIXME just one data slot (record) per program unit *)

(* info about map- and rel-functions for a type *)
type maps_info = {mapfun: string, relmap: string}

structure MapsData = Theory_Data
(
  type T = maps_info Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data = Symtab.merge (K true) data
)

fun maps_lookup thy s = Symtab.lookup (MapsData.get thy) s

fun maps_update_thy k minfo = MapsData.map (Symtab.update (k, minfo))
fun maps_update k minfo = Proof_Context.background_theory (maps_update_thy k minfo)  (* FIXME *)

fun maps_attribute_aux s minfo = Thm.declaration_attribute
  (fn _ => Context.mapping (maps_update_thy s minfo) (maps_update s minfo))

(* attribute to be used in declare statements *)
fun maps_attribute (ctxt, (tystr, (mapstr, relstr))) =
  let
    val thy = Proof_Context.theory_of ctxt
    val tyname = Sign.intern_type thy tystr
    val mapname = Sign.intern_const thy mapstr
    val relname = Sign.intern_const thy relstr

    fun sanity_check s = (Const (s, dummyT) |> Syntax.check_term ctxt; ())
    val _ = List.app sanity_check [mapname, relname]
  in
    maps_attribute_aux tyname {mapfun = mapname, relmap = relname}
  end

val maps_attr_parser =
  Args.context -- Scan.lift
    ((Args.name --| Parse.$$$ "=") --
      (Parse.$$$ "(" |-- Args.name --| Parse.$$$ "," --
        Args.name --| Parse.$$$ ")"))

fun print_mapsinfo ctxt =
  let
    fun prt_map (ty_name, {mapfun, relmap}) =
      Pretty.block (separate (Pretty.brk 2)
        (map Pretty.str
         ["type:", ty_name,
          "map:", mapfun,
          "relation map:", relmap]))
  in
    MapsData.get (Proof_Context.theory_of ctxt)
    |> Symtab.dest
    |> map (prt_map)
    |> Pretty.big_list "maps for type constructors:"
    |> Pretty.writeln
  end


(* info about quotient types *)
type quotdata_info = {qtyp: typ, rtyp: typ, equiv_rel: term, equiv_thm: thm}

structure QuotData = Theory_Data
(
  type T = quotdata_info Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data = Symtab.merge (K true) data
)

fun transform_quotdata phi {qtyp, rtyp, equiv_rel, equiv_thm} =
  {qtyp = Morphism.typ phi qtyp,
   rtyp = Morphism.typ phi rtyp,
   equiv_rel = Morphism.term phi equiv_rel,
   equiv_thm = Morphism.thm phi equiv_thm}

fun quotdata_lookup thy str = Symtab.lookup (QuotData.get thy) str

fun quotdata_update_thy str qinfo = QuotData.map (Symtab.update (str, qinfo))
fun quotdata_update_gen str qinfo = Context.mapping (quotdata_update_thy str qinfo) I

fun quotdata_dest lthy =
  map snd (Symtab.dest (QuotData.get (Proof_Context.theory_of lthy)))

fun print_quotinfo ctxt =
  let
    fun prt_quot {qtyp, rtyp, equiv_rel, equiv_thm} =
      Pretty.block (separate (Pretty.brk 2)
       [Pretty.str "quotient type:",
        Syntax.pretty_typ ctxt qtyp,
        Pretty.str "raw type:",
        Syntax.pretty_typ ctxt rtyp,
        Pretty.str "relation:",
        Syntax.pretty_term ctxt equiv_rel,
        Pretty.str "equiv. thm:",
        Syntax.pretty_term ctxt (prop_of equiv_thm)])
  in
    QuotData.get (Proof_Context.theory_of ctxt)
    |> Symtab.dest
    |> map (prt_quot o snd)
    |> Pretty.big_list "quotients:"
    |> Pretty.writeln
  end


(* info about quotient constants *)
type qconsts_info = {qconst: term, rconst: term, def: thm}

fun qconsts_info_eq (x : qconsts_info, y : qconsts_info) = #qconst x = #qconst y

(* We need to be able to lookup instances of lifted constants,
   for example given "nat fset" we need to find "'a fset";
   but overloaded constants share the same name *)
structure QConstsData = Theory_Data
(
  type T = qconsts_info list Symtab.table
  val empty = Symtab.empty
  val extend = I
  val merge = Symtab.merge_list qconsts_info_eq
)

fun transform_qconsts phi {qconst, rconst, def} =
  {qconst = Morphism.term phi qconst,
   rconst = Morphism.term phi rconst,
   def = Morphism.thm phi def}

fun qconsts_update_thy name qcinfo = QConstsData.map (Symtab.cons_list (name, qcinfo))
fun qconsts_update_gen name qcinfo = Context.mapping (qconsts_update_thy name qcinfo) I

fun qconsts_dest lthy =
  flat (map snd (Symtab.dest (QConstsData.get (Proof_Context.theory_of lthy))))

fun qconsts_lookup thy t =
  let
    val (name, qty) = dest_Const t
    fun matches (x: qconsts_info) =
      let
        val (name', qty') = dest_Const (#qconst x);
      in
        name = name' andalso Sign.typ_instance thy (qty, qty')
      end
  in
    (case Symtab.lookup (QConstsData.get thy) name of
      NONE => NONE
    | SOME l => find_first matches l)
  end

fun print_qconstinfo ctxt =
  let
    fun prt_qconst {qconst, rconst, def} =
      Pretty.block (separate (Pretty.brk 1)
       [Syntax.pretty_term ctxt qconst,
        Pretty.str ":=",
        Syntax.pretty_term ctxt rconst,
        Pretty.str "as",
        Syntax.pretty_term ctxt (prop_of def)])
  in
    QConstsData.get (Proof_Context.theory_of ctxt)
    |> Symtab.dest
    |> map snd
    |> flat
    |> map prt_qconst
    |> Pretty.big_list "quotient constants:"
    |> Pretty.writeln
  end

(* equivalence relation theorems *)
structure EquivRules = Named_Thms
(
  val name = "quot_equiv"
  val description = "equivalence relation theorems"
)

val equiv_rules_get = EquivRules.get
val equiv_rules_add = EquivRules.add

(* respectfulness theorems *)
structure RspRules = Named_Thms
(
  val name = "quot_respect"
  val description = "respectfulness theorems"
)

val rsp_rules_get = RspRules.get
val rsp_rules_add = RspRules.add

(* preservation theorems *)
structure PrsRules = Named_Thms
(
  val name = "quot_preserve"
  val description = "preservation theorems"
)

val prs_rules_get = PrsRules.get
val prs_rules_add = PrsRules.add

(* id simplification theorems *)
structure IdSimps = Named_Thms
(
  val name = "id_simps"
  val description = "identity simp rules for maps"
)

val id_simps_get = IdSimps.get

(* quotient theorems *)
structure QuotientRules = Named_Thms
(
  val name = "quot_thm"
  val description = "quotient theorems"
)

val quotient_rules_get = QuotientRules.get
val quotient_rules_add = QuotientRules.add


(* theory setup *)

val setup =
  Attrib.setup @{binding "map"} (maps_attr_parser >> maps_attribute)
    "declaration of map information" #>
  EquivRules.setup #>
  RspRules.setup #>
  PrsRules.setup #>
  IdSimps.setup #>
  QuotientRules.setup


(* outer syntax commands *)

val _ =
  Outer_Syntax.improper_command "print_quotmaps" "print quotient map functions" Keyword.diag
    (Scan.succeed (Toplevel.keep (print_mapsinfo o Toplevel.context_of)))

val _ =
  Outer_Syntax.improper_command "print_quotients" "print quotients" Keyword.diag
    (Scan.succeed (Toplevel.keep (print_quotinfo o Toplevel.context_of)))

val _ =
  Outer_Syntax.improper_command "print_quotconsts" "print quotient constants" Keyword.diag
    (Scan.succeed (Toplevel.keep (print_qconstinfo o Toplevel.context_of)))


end; (* structure *)
