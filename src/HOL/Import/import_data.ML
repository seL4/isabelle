(*  Title:      HOL/Import/import_data.ML
    Author:     Cezary Kaliszyk, University of Innsbruck
    Author:     Alexander Krauss, QAware GmbH

Importer data.
*)

signature IMPORT_DATA =
sig
  val get_const_map : string -> theory -> string option
  val get_typ_map : string -> theory -> string option
  val get_const_def : string -> theory -> thm option
  val get_typ_def : string -> theory -> thm option

  val add_const_map : string -> string -> theory -> theory
  val add_typ_map : string -> string -> theory -> theory
  val add_const_def : string -> thm -> string option -> theory -> theory
  val add_typ_def : string -> string -> string -> thm -> theory -> theory
end

structure Import_Data: IMPORT_DATA =
struct

structure Data = Theory_Data
(
  type T = {const_map: string Symtab.table, ty_map: string Symtab.table,
            const_def: thm Symtab.table, ty_def: thm Symtab.table}
  val empty = {const_map = Symtab.empty, ty_map = Symtab.empty,
               const_def = Symtab.empty, ty_def = Symtab.empty}
  val extend = I
  fun merge
   ({const_map = cm1, ty_map = tm1, const_def = cd1, ty_def = td1},
    {const_map = cm2, ty_map = tm2, const_def = cd2, ty_def = td2}) : T =
    {const_map = Symtab.merge (K true) (cm1, cm2), ty_map = Symtab.merge (K true) (tm1, tm2),
     const_def = Symtab.merge (K true) (cd1, cd2), ty_def = Symtab.merge (K true) (td1, td2)
    }
)

fun get_const_map s thy = Symtab.lookup (#const_map (Data.get thy)) s

fun get_typ_map s thy = Symtab.lookup (#ty_map (Data.get thy)) s

fun get_const_def s thy = Symtab.lookup (#const_def (Data.get thy)) s

fun get_typ_def s thy = Symtab.lookup (#ty_def (Data.get thy)) s

fun add_const_map s1 s2 thy =
  Data.map (fn {const_map, ty_map, const_def, ty_def} =>
    {const_map = (Symtab.update (s1, s2) const_map), ty_map = ty_map,
     const_def = const_def, ty_def = ty_def}) thy

fun add_typ_map s1 s2 thy =
  Data.map (fn {const_map, ty_map, const_def, ty_def} =>
    {const_map = const_map, ty_map = (Symtab.update (s1, s2) ty_map),
     const_def = const_def, ty_def = ty_def}) thy

fun add_const_def s th name_opt thy =
  let
    val th = Thm.legacy_freezeT th
    val name = case name_opt of
         NONE => (fst o dest_Const o fst o HOLogic.dest_eq o
           HOLogic.dest_Trueprop o prop_of) th
       | SOME n => n
    val thy' = add_const_map s name thy
  in
    Data.map (fn {const_map, ty_map, const_def, ty_def} =>
      {const_map = const_map, ty_map = ty_map,
       const_def = (Symtab.update (s, th) const_def), ty_def = ty_def}) thy'
  end

fun add_typ_def tyname absname repname th thy =
  let
    val th = Thm.legacy_freezeT th
    val (l, _) = dest_comb (HOLogic.dest_Trueprop (prop_of th))
    val (l, abst) = dest_comb l
    val (_, rept) = dest_comb l
    val (absn, _) = dest_Const abst
    val (repn, _) = dest_Const rept
    val nty = domain_type (fastype_of rept)
    val ntyn = fst (dest_Type nty)
    val thy2 = add_typ_map tyname ntyn thy
    val thy3 = add_const_map absname absn thy2
    val thy4 = add_const_map repname repn thy3
  in
    Data.map (fn {const_map, ty_map, const_def, ty_def} =>
      {const_map = const_map, ty_map = ty_map,
       const_def = const_def, ty_def = (Symtab.update (tyname, th) ty_def)}) thy4
  end

val parser = Parse.name -- Scan.option (Parse.$$$ ":" |-- Parse.xname)
fun add_const_attr (s1, s2) = Thm.declaration_attribute
  (fn th => Context.mapping (add_const_def s1 th s2) (fn x => x))
val _ = Context.>> (Context.map_theory
  (Attrib.setup (Binding.name "import_const") (Scan.lift parser >> add_const_attr)
  "Declare a theorem as an equality that maps the given constant"))

val parser = Parse.name -- (Parse.name -- Parse.name)
fun add_typ_attr (tyname, (absname, repname)) = Thm.declaration_attribute
  (fn th => Context.mapping (add_typ_def tyname absname repname th) (fn x => x))
val _ = Context.>> (Context.map_theory
  (Attrib.setup (Binding.name "import_type") (Scan.lift parser >> add_typ_attr)
  "Declare a type_definion theorem as a map for an imported type abs rep"))

val type_map = (Parse.name --| Parse.$$$ ":" -- Parse.xname) >>
  (fn (ty_name1, ty_name2) => add_typ_map ty_name1 ty_name2)
val _ = Outer_Syntax.command @{command_spec "import_type_map"}
  "Map external type name to existing Isabelle/HOL type name"
  (type_map >> Toplevel.theory)

val const_map = (Parse.name --| Parse.$$$ ":" -- Parse.xname) >>
  (fn (cname1, cname2) => add_const_map cname1 cname2)
val _ = Outer_Syntax.command @{command_spec "import_const_map"}
  "Map external const name to existing Isabelle/HOL const name"
  (const_map >> Toplevel.theory)

(* Initial type and constant maps, for types and constants that are not
   defined, which means their definitions do not appear in the proof dump *)
val _ = Context.>> (Context.map_theory (
  add_typ_map "bool" @{type_name bool} o
  add_typ_map "fun" @{type_name fun} o
  add_typ_map "ind" @{type_name ind} o
  add_const_map "=" @{const_name HOL.eq} o
  add_const_map "@" @{const_name "Eps"}))

end
