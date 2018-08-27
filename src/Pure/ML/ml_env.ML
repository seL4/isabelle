(*  Title:      Pure/ML/ml_env.ML
    Author:     Makarius

Toplevel environment for Standard ML and Isabelle/ML within the
implicit context.
*)

signature ML_ENV =
sig
  val Isabelle: string
  val SML: string
  val is_standard: string -> bool
  val make_standard: bool -> string
  val ML_environment_raw: Config.raw
  val ML_environment: string Config.T
  val ML_read_global_raw: Config.raw
  val ML_read_global: bool Config.T
  val ML_write_global_raw: Config.raw
  val ML_write_global: bool Config.T
  val inherit: Context.generic -> Context.generic -> Context.generic
  val setup: string -> theory -> theory
  val context_env: Context.generic -> string option -> string
  val default_env: string option -> string
  val get_breakpoint: Context.generic -> serial -> (bool Unsynchronized.ref * Position.T) option
  val add_breakpoints: (serial * (bool Unsynchronized.ref * Thread_Position.T)) list -> unit
  val forget_structure: string -> Context.generic -> Context.generic
  val bootstrap_name_space: Context.generic -> Context.generic
  val add_name_space: string -> ML_Name_Space.T -> Context.generic -> Context.generic
  val make_name_space: {read: string option, write: string option} -> ML_Name_Space.T
  val context: ML_Compiler0.context
  val name_space: ML_Name_Space.T
  val check_functor: string -> unit
end

structure ML_Env: ML_ENV =
struct

(* named environments *)

val Isabelle = "Isabelle";
val SML = "SML";

fun is_standard env = env <> Isabelle;
fun make_standard sml = if sml then SML else Isabelle;

val ML_environment_raw = Config.declare ("ML_environment", \<^here>) (fn _ => Config.String Isabelle);
val ML_environment = Config.string ML_environment_raw;


(* global read/write *)

val ML_read_global_raw = Config.declare ("ML_read_global", \<^here>) (fn _ => Config.Bool true);
val ML_write_global_raw = Config.declare ("ML_write_global", \<^here>) (fn _ => Config.Bool true);

val ML_read_global = Config.bool ML_read_global_raw;
val ML_write_global = Config.bool ML_write_global_raw;

fun read_global context = Config.get_generic context ML_read_global;
fun write_global context = Config.get_generic context ML_write_global;


(* name space tables *)

type tables =
  PolyML.NameSpace.Values.value Symtab.table *
  PolyML.NameSpace.TypeConstrs.typeConstr Symtab.table *
  PolyML.NameSpace.Infixes.fixity Symtab.table *
  PolyML.NameSpace.Structures.structureVal Symtab.table *
  PolyML.NameSpace.Signatures.signatureVal Symtab.table *
  PolyML.NameSpace.Functors.functorVal Symtab.table;

val empty_tables: tables =
  (Symtab.empty, Symtab.empty, Symtab.empty, Symtab.empty, Symtab.empty, Symtab.empty);

fun merge_tables
  ((val1, type1, fixity1, structure1, signature1, functor1),
   (val2, type2, fixity2, structure2, signature2, functor2)) : tables =
  (Symtab.merge (K true) (val1, val2),
   Symtab.merge (K true) (type1, type2),
   Symtab.merge (K true) (fixity1, fixity2),
   Symtab.merge (K true) (structure1, structure2),
   Symtab.merge (K true) (signature1, signature2),
   Symtab.merge (K true) (functor1, functor2));

val sml_tables: tables =
  (Symtab.make ML_Name_Space.sml_val,
   Symtab.make ML_Name_Space.sml_type,
   Symtab.make ML_Name_Space.sml_fixity,
   Symtab.make ML_Name_Space.sml_structure,
   Symtab.make ML_Name_Space.sml_signature,
   Symtab.make ML_Name_Space.sml_functor);


(* context data *)

type data =
 {envs: tables Name_Space.table,
  breakpoints: (bool Unsynchronized.ref * Position.T) Inttab.table};

fun make_data (envs, breakpoints) : data = {envs = envs, breakpoints = breakpoints};

structure Data = Generic_Data
(
  type T = data
  val empty = make_data (Name_Space.empty_table "ML_environment", Inttab.empty);
  fun extend (data : T) = make_data (#envs data, #breakpoints data);
  fun merge (data : T * T) =
    make_data ((apply2 #envs data) |> Name_Space.join_tables (K merge_tables),
      Inttab.merge (K true) (apply2 #breakpoints data));
);

val inherit = Data.put o Data.get;

fun setup env_name thy =
  thy |> (Context.theory_map o Data.map) (fn {envs, breakpoints} =>
    let
      val thy' = Sign.map_naming (K Name_Space.global_naming) thy;
      val tables = if env_name = Isabelle then empty_tables else sml_tables;
      val (_, envs') = envs
        |> Name_Space.define (Context.Theory thy') true (Binding.name env_name, tables);
    in make_data (envs', breakpoints) end);

val get_env = Name_Space.get o #envs o Data.get;

fun update_env env_name f context = context |> Data.map (fn {envs, breakpoints} =>
  let
    val _ = Name_Space.get envs env_name;
    val envs' = Name_Space.map_table_entry env_name f envs;
  in make_data (envs', breakpoints) end);

fun forget_structure name context =
  (if write_global context then ML_Name_Space.forget_structure name else ();
    context |> update_env Isabelle (fn tables =>
      (#1 tables, #2 tables, #3 tables, Symtab.delete_safe name (#4 tables), #5 tables, #6 tables)));


(* environment name *)

fun check_env opt_context name =
  (case opt_context of
    NONE =>
      if name = Isabelle then name
      else error ("Bad ML environment name " ^ quote name ^ " -- no context")
  | SOME context => if name = Isabelle then name else (get_env context name; name));

fun context_env context opt_name =
  check_env (SOME context) (the_default (Config.get_generic context ML_environment) opt_name);

fun default_env opt_name =
  let val opt_context = Context.get_generic_context () in
    check_env opt_context
      (case opt_name of
        SOME name => name
      | NONE => (case opt_context of NONE => Isabelle | SOME context => context_env context NONE))
  end;


(* name space *)

val bootstrap_name_space =
  update_env Isabelle (fn (tables: tables) =>
    let
      fun update entries (x, y) = member (op =) entries x ? Symtab.update (x, y);
      val bootstrap_val = update ML_Name_Space.bootstrap_values;
      val bootstrap_structure = update ML_Name_Space.bootstrap_structures;
      val bootstrap_signature = update ML_Name_Space.bootstrap_signatures;

      val (val1, type1, fixity1, structure1, signature1, functor1) = sml_tables;
      val val2 = val1
        |> fold bootstrap_val (#allVal ML_Name_Space.global ())
        |> Symtab.fold bootstrap_val (#1 tables);
      val structure2 = structure1
        |> fold bootstrap_structure (#allStruct ML_Name_Space.global ())
        |> Symtab.fold bootstrap_structure (#4 tables);
      val signature2 = signature1
        |> fold bootstrap_signature (#allSig ML_Name_Space.global ())
        |> Symtab.fold bootstrap_signature (#5 tables);
    in (val2, type1, fixity1, structure2, signature2, functor1) end);

fun add_name_space env (space: ML_Name_Space.T) =
  update_env env (fn (val1, type1, fixity1, structure1, signature1, functor1) =>
    let
      val val2 = fold Symtab.update (#allVal space ()) val1;
      val type2 = fold Symtab.update (#allType space ()) type1;
      val fixity2 = fold Symtab.update (#allFix space ()) fixity1;
      val structure2 = fold Symtab.update (#allStruct space ()) structure1;
      val signature2 = fold Symtab.update (#allSig space ()) signature1;
      val functor2 = fold Symtab.update (#allFunct space ()) functor1;
    in (val2, type2, fixity2, structure2, signature2, functor2) end);

fun make_name_space {read, write} : ML_Name_Space.T =
  let
    val read_env = default_env read;
    val write_env = default_env write;

    fun lookup_env sel1 context name = Symtab.lookup (sel1 (get_env context read_env)) name;
    fun dest_env sel1 context = Symtab.dest (sel1 (get_env context read_env));
    fun enter_env ap1 entry = update_env write_env (ap1 (Symtab.update entry));

    fun lookup sel1 sel2 name =
      if read_env = Isabelle then
        (case Context.get_generic_context () of
          NONE => sel2 ML_Name_Space.global name
        | SOME context =>
            (case lookup_env sel1 context name of
              NONE => if read_global context then sel2 ML_Name_Space.global name else NONE
            | some => some))
      else lookup_env sel1 (Context.the_generic_context ()) name;

    fun all sel1 sel2 () =
      sort_distinct (string_ord o apply2 #1)
        (if read_env = Isabelle then
          (case Context.get_generic_context () of
            NONE => sel2 ML_Name_Space.global ()
          | SOME context =>
              dest_env sel1 context @
              (if read_global context then sel2 ML_Name_Space.global () else []))
         else dest_env sel1 (Context.the_generic_context ()));

    fun enter ap1 sel2 entry =
      if write_env = Isabelle then
        (case Context.get_generic_context () of
          NONE => sel2 ML_Name_Space.global entry
        | SOME context =>
            (if write_global context then sel2 ML_Name_Space.global entry else ();
             Context.>> (enter_env ap1 entry)))
      else Context.>> (enter_env ap1 entry);
  in
   {lookupVal    = lookup #1 #lookupVal,
    lookupType   = lookup #2 #lookupType,
    lookupFix    = lookup #3 #lookupFix,
    lookupStruct = lookup #4 #lookupStruct,
    lookupSig    = lookup #5 #lookupSig,
    lookupFunct  = lookup #6 #lookupFunct,
    enterVal     = enter (fn h => fn (a, b, c, d, e, f) => (h a, b, c, d, e, f)) #enterVal,
    enterType    = enter (fn h => fn (a, b, c, d, e, f) => (a, h b, c, d, e, f)) #enterType,
    enterFix     = enter (fn h => fn (a, b, c, d, e, f) => (a, b, h c, d, e, f)) #enterFix,
    enterStruct  = enter (fn h => fn (a, b, c, d, e, f) => (a, b, c, h d, e, f)) #enterStruct,
    enterSig     = enter (fn h => fn (a, b, c, d, e, f) => (a, b, c, d, h e, f)) #enterSig,
    enterFunct   = enter (fn h => fn (a, b, c, d, e, f) => (a, b, c, d, e, h f)) #enterFunct,
    allVal       = all #1 #allVal,
    allType      = all #2 #allType,
    allFix       = all #3 #allFix,
    allStruct    = all #4 #allStruct,
    allSig       = all #5 #allSig,
    allFunct     = all #6 #allFunct}
  end;

val context: ML_Compiler0.context =
 {name_space = make_name_space {read = NONE, write = NONE},
  print_depth = NONE,
  here = Position.here oo Position.line_file,
  print = writeln,
  error = error};

val name_space = #name_space context;

val is_functor = is_some o #lookupFunct name_space;

fun check_functor name =
  if not (is_functor "Table") (*mask dummy version of name_space*) orelse is_functor name then ()
  else error ("Unknown ML functor: " ^ quote name);


(* breakpoints *)

val get_breakpoint = Inttab.lookup o #breakpoints o Data.get;

fun add_breakpoints more_breakpoints =
  if is_some (Context.get_generic_context ()) then
    Context.>>
      (Data.map (fn {envs, breakpoints} =>
        let val breakpoints' =
          fold (Inttab.update_new o (apsnd o apsnd) Position.make) more_breakpoints breakpoints;
        in make_data (envs, breakpoints') end))
  else ();

end;

Theory.setup (ML_Env.setup ML_Env.Isabelle #> ML_Env.setup ML_Env.SML);
