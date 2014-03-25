(*  Title:      Pure/ML/ml_env.ML
    Author:     Makarius

Toplevel environment for Standard ML and Isabelle/ML within the
implicit context.
*)

signature ML_ENV =
sig
  val inherit: Context.generic -> Context.generic -> Context.generic
  val SML_name_space: ML_Name_Space.T
  val name_space: ML_Name_Space.T
  val local_context: use_context
  val check_functor: string -> unit
end

structure ML_Env: ML_ENV =
struct

(* context data *)

type tables =
  ML_Name_Space.valueVal Symtab.table *
  ML_Name_Space.typeVal Symtab.table *
  ML_Name_Space.fixityVal Symtab.table *
  ML_Name_Space.structureVal Symtab.table *
  ML_Name_Space.signatureVal Symtab.table *
  ML_Name_Space.functorVal Symtab.table;

fun merge_tables
  ((val1, type1, fixity1, structure1, signature1, functor1),
   (val2, type2, fixity2, structure2, signature2, functor2)) : tables =
  (Symtab.merge (K true) (val1, val2),
   Symtab.merge (K true) (type1, type2),
   Symtab.merge (K true) (fixity1, fixity2),
   Symtab.merge (K true) (structure1, structure2),
   Symtab.merge (K true) (signature1, signature2),
   Symtab.merge (K true) (functor1, functor2));

type data = {bootstrap: bool, tables: tables, sml_tables: tables};

fun make_data (bootstrap, tables, sml_tables) : data =
  {bootstrap = bootstrap, tables = tables, sml_tables = sml_tables};

structure Env = Generic_Data
(
  type T = data
  val empty =
    make_data (true,
      (Symtab.empty, Symtab.empty, Symtab.empty, Symtab.empty, Symtab.empty, Symtab.empty),
      (Symtab.make ML_Name_Space.initial_val,
       Symtab.make ML_Name_Space.initial_type,
       Symtab.make ML_Name_Space.initial_fixity,
       Symtab.make ML_Name_Space.initial_structure,
       Symtab.make ML_Name_Space.initial_signature,
       Symtab.make ML_Name_Space.initial_functor));
  fun extend (data : T) = make_data (false, #tables data, #sml_tables data);
  fun merge (data : T * T) =
    make_data (false,
      merge_tables (pairself #tables data),
      merge_tables (pairself #sml_tables data));
);

val inherit = Env.put o Env.get;


(* SML name space *)

val SML_name_space: ML_Name_Space.T =
  let
    fun lookup which name =
      Context.the_thread_data ()
      |> (fn context => Symtab.lookup (which (#sml_tables (Env.get context))) name);

    fun all which () =
      Context.the_thread_data ()
      |> (fn context => Symtab.dest (which (#sml_tables (Env.get context))))
      |> sort_distinct (string_ord o pairself #1);

    fun enter which entry =
      Context.>> (Env.map (fn {bootstrap, tables, sml_tables} =>
        let val sml_tables' = which (Symtab.update entry) sml_tables
        in make_data (bootstrap, tables, sml_tables') end));
  in
   {lookupVal    = lookup #1,
    lookupType   = lookup #2,
    lookupFix    = lookup #3,
    lookupStruct = lookup #4,
    lookupSig    = lookup #5,
    lookupFunct  = lookup #6,
    enterVal     = enter (fn h => fn (a, b, c, d, e, f) => (h a, b, c, d, e, f)),
    enterType    = enter (fn h => fn (a, b, c, d, e, f) => (a, h b, c, d, e, f)),
    enterFix     = enter (fn h => fn (a, b, c, d, e, f) => (a, b, h c, d, e, f)),
    enterStruct  = enter (fn h => fn (a, b, c, d, e, f) => (a, b, c, h d, e, f)),
    enterSig     = enter (fn h => fn (a, b, c, d, e, f) => (a, b, c, d, h e, f)),
    enterFunct   = enter (fn h => fn (a, b, c, d, e, f) => (a, b, c, d, e, h f)),
    allVal       = all #1,
    allType      = all #2,
    allFix       = all #3,
    allStruct    = all #4,
    allSig       = all #5,
    allFunct     = all #6}
  end;


(* Isabelle/ML name space *)

val name_space: ML_Name_Space.T =
  let
    fun lookup sel1 sel2 name =
      Context.thread_data ()
      |> (fn NONE => NONE | SOME context => Symtab.lookup (sel1 (#tables (Env.get context))) name)
      |> (fn NONE => sel2 ML_Name_Space.global name | some => some);

    fun all sel1 sel2 () =
      Context.thread_data ()
      |> (fn NONE => [] | SOME context => Symtab.dest (sel1 (#tables (Env.get context))))
      |> append (sel2 ML_Name_Space.global ())
      |> sort_distinct (string_ord o pairself #1);

    fun enter ap1 sel2 entry =
      if is_some (Context.thread_data ()) then
        Context.>> (Env.map (fn {bootstrap, tables, sml_tables} =>
          let
            val _ = if bootstrap then sel2 ML_Name_Space.global entry else ();
            val tables' = ap1 (Symtab.update entry) tables;
          in make_data (bootstrap, tables', sml_tables) end))
      else sel2 ML_Name_Space.global entry;
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

val local_context: use_context =
 {tune_source = ML_Parse.fix_ints,
  name_space = name_space,
  str_of_pos = Position.here oo Position.line_file,
  print = writeln,
  error = error};

val is_functor = is_some o #lookupFunct name_space;

fun check_functor name =
  if not (is_functor "Table") (*mask dummy version of name_space*) orelse is_functor name then ()
  else error ("Unknown ML functor: " ^ quote name);

end;

