(*  Title:      HOL/Import/import_data.ML
    Author:     Cezary Kaliszyk, University of Innsbruck
    Author:     Alexander Krauss, QAware GmbH

Importer data.
*)

signature IMPORT_DATA =
sig
  val get_const_map : theory -> string -> string option
  val get_typ_map : theory -> string -> string option
  val get_const_def : theory -> string -> thm option
  val get_typ_def : theory -> string -> thm option
  val add_const_map : string -> string -> theory -> theory
  val add_const_map_cmd : string -> string -> theory -> theory
  val add_typ_map : string -> string -> theory -> theory
  val add_typ_map_cmd : string -> string -> theory -> theory
  val add_const_def : string -> thm -> string option -> theory -> theory
  val add_typ_def : string -> string -> string -> thm -> theory -> theory
end

structure Import_Data: IMPORT_DATA =
struct

structure Data = Theory_Data
(
  type T =
   {const_map: string Symtab.table, ty_map: string Symtab.table,
    const_def: thm Symtab.table, ty_def: thm Symtab.table}
  val empty =
   {const_map = Symtab.empty, ty_map = Symtab.empty,
    const_def = Symtab.empty, ty_def = Symtab.empty}
  fun merge
   ({const_map = cm1, ty_map = tm1, const_def = cd1, ty_def = td1},
    {const_map = cm2, ty_map = tm2, const_def = cd2, ty_def = td2}) : T =
    {const_map = Symtab.merge (K true) (cm1, cm2), ty_map = Symtab.merge (K true) (tm1, tm2),
     const_def = Symtab.merge (K true) (cd1, cd2), ty_def = Symtab.merge (K true) (td1, td2)}
)

val get_const_map = Symtab.lookup o #const_map o Data.get
val get_typ_map = Symtab.lookup o #ty_map o Data.get
val get_const_def = Symtab.lookup o #const_def o Data.get
val get_typ_def = Symtab.lookup o #ty_def o Data.get

fun add_const_map c d =
  Data.map (fn {const_map, ty_map, const_def, ty_def} =>
    {const_map = Symtab.update (c, d) const_map, ty_map = ty_map,
     const_def = const_def, ty_def = ty_def})

fun add_const_map_cmd c s thy =
  let
    val ctxt = Proof_Context.init_global thy
    val d = dest_Const_name (Proof_Context.read_const {proper = true, strict = false} ctxt s)
  in add_const_map c d thy end

fun add_typ_map c d =
  Data.map (fn {const_map, ty_map, const_def, ty_def} =>
    {const_map = const_map, ty_map = (Symtab.update (c, d) ty_map),
     const_def = const_def, ty_def = ty_def})

fun add_typ_map_cmd c s thy =
  let
    val ctxt = Proof_Context.init_global thy
    val d = dest_Type_name (Proof_Context.read_type_name {proper = true, strict = false} ctxt s)
  in add_typ_map c d thy end

fun add_const_def c th name_opt thy =
  let
    val th' = Thm.legacy_freezeT th
    val name =
      (case name_opt of
        NONE => dest_Const_name (#1 (HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of th'))))
      | SOME name => name)
  in
    thy
    |> add_const_map c name
    |> Data.map (fn {const_map, ty_map, const_def, ty_def} =>
      {const_map = const_map, ty_map = ty_map,
       const_def = (Symtab.update (c, th') const_def), ty_def = ty_def})
  end

fun add_typ_def type_name abs_name rep_name th thy =
  let
    val th' = Thm.legacy_freezeT th
    val ((_, rep), abs) =
      Thm.prop_of th'
      |> HOLogic.dest_Trueprop
      |> dest_comb |> #1
      |> dest_comb |>> dest_comb
    val A = domain_type (fastype_of rep)
  in
    thy
    |> add_typ_map type_name (dest_Type_name A)
    |> add_const_map abs_name (dest_Const_name abs)
    |> add_const_map rep_name (dest_Const_name rep)
    |> Data.map (fn {const_map, ty_map, const_def, ty_def} =>
      {const_map = const_map, ty_map = ty_map,
       const_def = const_def, ty_def = (Symtab.update (type_name, th') ty_def)})
  end

val _ =
  Theory.setup (Attrib.setup \<^binding>\<open>import_const\<close>
    (Scan.lift Parse.name --
      Scan.option (Scan.lift \<^keyword>\<open>:\<close> |-- Args.const {proper = true, strict = false}) >>
      (fn (s1, s2) => Thm.declaration_attribute
        (fn th => Context.mapping (add_const_def s1 th s2) I)))
    "declare a theorem as an equality that maps the given constant")

val _ =
  Theory.setup (Attrib.setup \<^binding>\<open>import_type\<close>
    (Scan.lift (Parse.name -- Parse.name -- Parse.name) >>
      (fn ((tyname, absname), repname) => Thm.declaration_attribute
        (fn th => Context.mapping (add_typ_def tyname absname repname th) I)))
    "declare a type_definition theorem as a map for an imported type with abs and rep")

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>import_type_map\<close>
    "map external type name to existing Isabelle/HOL type name"
    ((Parse.name --| \<^keyword>\<open>:\<close>) -- Parse.type_const >>
      (fn (c, d) => Toplevel.theory (add_typ_map_cmd c d)))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>import_const_map\<close>
    "map external const name to existing Isabelle/HOL const name"
    ((Parse.name --| \<^keyword>\<open>:\<close>) -- Parse.const >>
      (fn (c, d) => Toplevel.theory (add_const_map_cmd c d)))

(*Initial type and constant maps, for types and constants that are not
  defined, which means their definitions do not appear in the proof dump.*)
val _ =
  Theory.setup
   (add_typ_map "bool" \<^type_name>\<open>bool\<close> #>
    add_typ_map "fun" \<^type_name>\<open>fun\<close> #>
    add_typ_map "ind" \<^type_name>\<open>ind\<close> #>
    add_const_map "=" \<^const_name>\<open>HOL.eq\<close> #>
    add_const_map "@" \<^const_name>\<open>Eps\<close>)

end
