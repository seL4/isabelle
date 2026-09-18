(*  Title:      HOL/Tools/SMT/alethe/rare_rewrites/cvc5_rare.ML
    Author:     Mathias Fleury, University of Freiburg
    Author:     Hanna Lachnitt, Stanford University

Declaration of the rare rules used for the reconstruction
*)

signature CVC5_RARE =
sig
  val rare_lookup: Context.generic -> string -> thm list option
  val rare_rule: Context.generic -> string -> thm list
  val rare_add: string * string -> Context.generic -> Context.generic
  val rare_rm: string -> Context.generic -> Context.generic
  val all_rare_rules: Context.generic -> (string * string) list
end;


structure CVC5_Rare: CVC5_RARE =
struct

type rare = string Symtab.table

val empty_rare = Symtab.empty

fun merge_rare tables = Symtab.merge (op =) tables

structure Data = Generic_Data
(
  type T = rare
  val empty = empty_rare
  val merge = merge_rare
)

fun rare_lookup ctxt name =
  let
    val rules = Data.get ctxt
  in
    case (Symtab.lookup rules name) of
      SOME a => SOME (Named_Theorems.get (Context.proof_of ctxt) a)
    | NONE => NONE
  end

fun rare_rule ctxt = rare_lookup ctxt #> the
val all_rare_rules = Data.get #> Symtab.dest

fun rare_add name_thy context =
  Data.map (Symtab.update name_thy) context

fun rare_rm name context =
  Data.map (Symtab.delete name) context


fun rare_check_and_add (short, long) context =
  let
    val _ = Named_Theorems.get (Context.proof_of context) long
  in
    rare_add (short, long) context
  end

val _ = Outer_Syntax.command \<^command_keyword>\<open>cvc5_rare\<close>
         "Declare a string of a named_theorems as a rare rule"
    (Parse.string >> (fn long => fn lthy =>
  let
    val short = Long_Name.base_name long
  in
    Toplevel.theory (Context.theory_map (rare_check_and_add ((short, long)))) lthy
  end))

end;
