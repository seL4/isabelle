(*  Title:      HOL/Tools/Quotient/quotient_info.ML
    Author:     Cezary Kaliszyk and Christian Urban

Context data for the quotient package.
*)

signature QUOTIENT_INFO =
sig
  type quotmaps = {mapfun: string, relmap: string}
  val lookup_quotmaps: Proof.context -> string -> quotmaps option
  val print_quotmaps: Proof.context -> unit

  type quotients = {qtyp: typ, rtyp: typ, equiv_rel: term, equiv_thm: thm}
  val transform_quotients: morphism -> quotients -> quotients
  val lookup_quotients: Proof.context -> string -> quotients option
  val update_quotients: string -> quotients -> Context.generic -> Context.generic
  val dest_quotients: Proof.context -> quotients list
  val print_quotients: Proof.context -> unit

  type quotconsts = {qconst: term, rconst: term, def: thm}
  val transform_quotconsts: morphism -> quotconsts -> quotconsts
  val lookup_quotconsts: Proof.context -> term -> quotconsts option
  val update_quotconsts: string -> quotconsts -> Context.generic -> Context.generic
  val dest_quotconsts: Proof.context -> quotconsts list
  val print_quotconsts: Proof.context -> unit

  val equiv_rules: Proof.context -> thm list
  val equiv_rules_add: attribute
  val rsp_rules: Proof.context -> thm list
  val rsp_rules_add: attribute
  val prs_rules: Proof.context -> thm list
  val prs_rules_add: attribute
  val id_simps: Proof.context -> thm list
  val quotient_rules: Proof.context -> thm list
  val quotient_rules_add: attribute
  val setup: theory -> theory
end;

structure Quotient_Info: QUOTIENT_INFO =
struct

(** data containers **)

(* FIXME just one data slot (record) per program unit *)

(* info about map- and rel-functions for a type *)
type quotmaps = {mapfun: string, relmap: string}

structure Quotmaps = Generic_Data
(
  type T = quotmaps Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data = Symtab.merge (K true) data
)

val lookup_quotmaps = Symtab.lookup o Quotmaps.get o Context.Proof

(* FIXME export proper internal update operation!? *)

val quotmaps_attribute_setup =
  Attrib.setup @{binding map}
    ((Args.type_name false --| Scan.lift (Parse.$$$ "=")) --  (* FIXME Args.type_name true (requires "set" type) *)
      (Scan.lift (Parse.$$$ "(") |-- Args.const_proper true --| Scan.lift (Parse.$$$ ",") --
        Args.const_proper true --| Scan.lift (Parse.$$$ ")")) >>
      (fn (tyname, (mapname, relname)) =>
        let val minfo = {mapfun = mapname, relmap = relname}
        in Thm.declaration_attribute (fn _ => Quotmaps.map (Symtab.update (tyname, minfo))) end))
    "declaration of map information"

fun print_quotmaps ctxt =
  let
    fun prt_map (ty_name, {mapfun, relmap}) =
      Pretty.block (separate (Pretty.brk 2)
        (map Pretty.str
         ["type:", ty_name,
          "map:", mapfun,
          "relation map:", relmap]))
  in
    map prt_map (Symtab.dest (Quotmaps.get (Context.Proof ctxt)))
    |> Pretty.big_list "maps for type constructors:"
    |> Pretty.writeln
  end


(* info about quotient types *)
type quotients = {qtyp: typ, rtyp: typ, equiv_rel: term, equiv_thm: thm}

structure Quotients = Generic_Data
(
  type T = quotients Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data = Symtab.merge (K true) data
)

fun transform_quotients phi {qtyp, rtyp, equiv_rel, equiv_thm} =
  {qtyp = Morphism.typ phi qtyp,
   rtyp = Morphism.typ phi rtyp,
   equiv_rel = Morphism.term phi equiv_rel,
   equiv_thm = Morphism.thm phi equiv_thm}

val lookup_quotients = Symtab.lookup o Quotients.get o Context.Proof

fun update_quotients str qinfo = Quotients.map (Symtab.update (str, qinfo))

fun dest_quotients ctxt =  (* FIXME slightly expensive way to retrieve data *)
  map snd (Symtab.dest (Quotients.get (Context.Proof ctxt)))

fun print_quotients ctxt =
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
    map (prt_quot o snd) (Symtab.dest (Quotients.get (Context.Proof ctxt)))
    |> Pretty.big_list "quotients:"
    |> Pretty.writeln
  end


(* info about quotient constants *)
type quotconsts = {qconst: term, rconst: term, def: thm}

fun eq_quotconsts (x : quotconsts, y : quotconsts) = #qconst x = #qconst y

(* We need to be able to lookup instances of lifted constants,
   for example given "nat fset" we need to find "'a fset";
   but overloaded constants share the same name *)
structure Quotconsts = Generic_Data
(
  type T = quotconsts list Symtab.table
  val empty = Symtab.empty
  val extend = I
  val merge = Symtab.merge_list eq_quotconsts
)

fun transform_quotconsts phi {qconst, rconst, def} =
  {qconst = Morphism.term phi qconst,
   rconst = Morphism.term phi rconst,
   def = Morphism.thm phi def}

fun update_quotconsts name qcinfo = Quotconsts.map (Symtab.cons_list (name, qcinfo))

fun dest_quotconsts ctxt =
  flat (map snd (Symtab.dest (Quotconsts.get (Context.Proof ctxt))))

fun lookup_quotconsts ctxt t =
  let
    val thy = Proof_Context.theory_of ctxt

    val (name, qty) = dest_Const t
    fun matches (x: quotconsts) =
      let val (name', qty') = dest_Const (#qconst x);
      in name = name' andalso Sign.typ_instance thy (qty, qty') end
  in
    (case Symtab.lookup (Quotconsts.get (Context.Proof ctxt)) name of
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
    map prt_qconst (maps snd (Symtab.dest (Quotconsts.get (Context.Proof ctxt))))
    |> Pretty.big_list "quotient constants:"
    |> Pretty.writeln
  end

(* equivalence relation theorems *)
structure Equiv_Rules = Named_Thms
(
  val name = "quot_equiv"
  val description = "equivalence relation theorems"
)

val equiv_rules = Equiv_Rules.get
val equiv_rules_add = Equiv_Rules.add

(* respectfulness theorems *)
structure Rsp_Rules = Named_Thms
(
  val name = "quot_respect"
  val description = "respectfulness theorems"
)

val rsp_rules = Rsp_Rules.get
val rsp_rules_add = Rsp_Rules.add

(* preservation theorems *)
structure Prs_Rules = Named_Thms
(
  val name = "quot_preserve"
  val description = "preservation theorems"
)

val prs_rules = Prs_Rules.get
val prs_rules_add = Prs_Rules.add

(* id simplification theorems *)
structure Id_Simps = Named_Thms
(
  val name = "id_simps"
  val description = "identity simp rules for maps"
)

val id_simps = Id_Simps.get

(* quotient theorems *)
structure Quotient_Rules = Named_Thms
(
  val name = "quot_thm"
  val description = "quotient theorems"
)

val quotient_rules = Quotient_Rules.get
val quotient_rules_add = Quotient_Rules.add


(* theory setup *)

val setup =
  quotmaps_attribute_setup #>
  Equiv_Rules.setup #>
  Rsp_Rules.setup #>
  Prs_Rules.setup #>
  Id_Simps.setup #>
  Quotient_Rules.setup


(* outer syntax commands *)

val _ =
  Outer_Syntax.improper_command "print_quotmaps" "print quotient map functions" Keyword.diag
    (Scan.succeed (Toplevel.keep (print_quotmaps o Toplevel.context_of)))

val _ =
  Outer_Syntax.improper_command "print_quotients" "print quotients" Keyword.diag
    (Scan.succeed (Toplevel.keep (print_quotients o Toplevel.context_of)))

val _ =
  Outer_Syntax.improper_command "print_quotconsts" "print quotient constants" Keyword.diag
    (Scan.succeed (Toplevel.keep (print_quotconsts o Toplevel.context_of)))

end;
