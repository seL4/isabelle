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
  val update_abs_rep: string -> abs_rep -> Context.generic -> Context.generic
  val print_abs_rep: Proof.context -> unit
  
  type quotients = {qtyp: typ, rtyp: typ, equiv_rel: term, equiv_thm: thm, quot_thm: thm}
  val transform_quotients: morphism -> quotients -> quotients
  val lookup_quotients: Proof.context -> string -> quotients option
  val lookup_quotients_global: theory -> string -> quotients option
  val update_quotients: string -> quotients -> Context.generic -> Context.generic
  val dest_quotients: Proof.context -> quotients list
  val print_quotients: Proof.context -> unit

  type quotconsts = {qconst: term, rconst: term, def: thm}
  val transform_quotconsts: morphism -> quotconsts -> quotconsts
  val lookup_quotconsts_global: theory -> term -> quotconsts option
  val update_quotconsts: string -> quotconsts -> Context.generic -> Context.generic
  val dest_quotconsts_global: theory -> quotconsts list
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
type quotmaps = {relmap: string, quot_thm: thm}

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

val quotmaps_attribute_setup =
  Attrib.setup @{binding mapQ3}
    ((Args.type_name true --| Scan.lift @{keyword "="}) --
      (Scan.lift @{keyword "("} |-- Args.const_proper true --| Scan.lift @{keyword ","} --
        Attrib.thm --| Scan.lift @{keyword ")"}) >>
      (fn (tyname, (relname, qthm)) =>
        let val minfo = {relmap = relname, quot_thm = qthm}
        in Thm.declaration_attribute (fn _ => Quotmaps.map (Symtab.update (tyname, minfo))) end))
    "declaration of map information"

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
    map prt_map (Symtab.dest (Quotmaps.get (Context.Proof ctxt)))
    |> Pretty.big_list "maps for type constructors:"
    |> Pretty.writeln
  end

(* info about abs/rep terms *)
type abs_rep = {abs : term, rep : term}

structure Abs_Rep = Generic_Data
(
  type T = abs_rep Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data = Symtab.merge (K true) data
)

fun transform_abs_rep phi {abs, rep} = {abs = Morphism.term phi abs, rep = Morphism.term phi rep}

val lookup_abs_rep = Symtab.lookup o Abs_Rep.get o Context.Proof
val lookup_abs_rep_global = Symtab.lookup o Abs_Rep.get o Context.Theory

fun update_abs_rep str data = Abs_Rep.map (Symtab.update (str, data))

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
    map prt_abs_rep (Symtab.dest (Abs_Rep.get (Context.Proof ctxt)))
    |> Pretty.big_list "abs/rep terms:"
    |> Pretty.writeln
  end

(* info about quotient types *)
type quotients = {qtyp: typ, rtyp: typ, equiv_rel: term, equiv_thm: thm, quot_thm: thm}

structure Quotients = Generic_Data
(
  type T = quotients Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data = Symtab.merge (K true) data
)

fun transform_quotients phi {qtyp, rtyp, equiv_rel, equiv_thm, quot_thm} =
  {qtyp = Morphism.typ phi qtyp,
   rtyp = Morphism.typ phi rtyp,
   equiv_rel = Morphism.term phi equiv_rel,
   equiv_thm = Morphism.thm phi equiv_thm,
   quot_thm = Morphism.thm phi quot_thm}

val lookup_quotients = Symtab.lookup o Quotients.get o Context.Proof
val lookup_quotients_global = Symtab.lookup o Quotients.get o Context.Theory

fun update_quotients str qinfo = Quotients.map (Symtab.update (str, qinfo))

fun dest_quotients ctxt =  (* FIXME slightly expensive way to retrieve data *)
  map snd (Symtab.dest (Quotients.get (Context.Proof ctxt)))

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

fun dest_quotconsts_global thy =
  flat (map snd (Symtab.dest (Quotconsts.get (Context.Theory thy))))



fun lookup_quotconsts_global thy t =
  let
    val (name, qty) = dest_Const t
    fun matches (x: quotconsts) =
      let val (name', qty') = dest_Const (#qconst x);
      in name = name' andalso Sign.typ_instance thy (qty, qty') end
  in
    (case Symtab.lookup (Quotconsts.get (Context.Theory thy)) name of
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
  val name = @{binding quot_equiv}
  val description = "equivalence relation theorems"
)

val equiv_rules = Equiv_Rules.get
val equiv_rules_add = Equiv_Rules.add

(* respectfulness theorems *)
structure Rsp_Rules = Named_Thms
(
  val name = @{binding quot_respect}
  val description = "respectfulness theorems"
)

val rsp_rules = Rsp_Rules.get
val rsp_rules_add = Rsp_Rules.add

(* preservation theorems *)
structure Prs_Rules = Named_Thms
(
  val name = @{binding quot_preserve}
  val description = "preservation theorems"
)

val prs_rules = Prs_Rules.get
val prs_rules_add = Prs_Rules.add

(* id simplification theorems *)
structure Id_Simps = Named_Thms
(
  val name = @{binding id_simps}
  val description = "identity simp rules for maps"
)

val id_simps = Id_Simps.get

(* quotient theorems *)
structure Quotient_Rules = Named_Thms
(
  val name = @{binding quot_thm}
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
  Outer_Syntax.improper_command @{command_spec "print_quotmapsQ3"} "print quotient map functions"
    (Scan.succeed (Toplevel.keep (print_quotmaps o Toplevel.context_of)))

val _ =
  Outer_Syntax.improper_command @{command_spec "print_quotientsQ3"} "print quotients"
    (Scan.succeed (Toplevel.keep (print_quotients o Toplevel.context_of)))

val _ =
  Outer_Syntax.improper_command @{command_spec "print_quotconsts"} "print quotient constants"
    (Scan.succeed (Toplevel.keep (print_quotconsts o Toplevel.context_of)))

end;
