(*  Title:      HOL/Tools/recdef_package.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Wrapper module for Konrad Slind's TFL package.
*)

signature RECDEF_PACKAGE =
sig
  val quiet_mode: bool ref
  val print_recdefs: theory -> unit
  val get_recdef: theory -> string -> {rules: thm list, induct: thm, tcs: term list}
  val add_recdef: xstring -> string -> ((bstring * string) * Args.src list) list
    -> simpset option -> (xstring * Args.src list) list
    -> theory -> theory * {rules: thm list, induct: thm, tcs: term list}
  val add_recdef_i: xstring -> term -> ((bstring * term) * theory attribute list) list
    -> simpset option -> (thm * theory attribute list) list
    -> theory -> theory * {rules: thm list, induct: thm, tcs: term list}
  val setup: (theory -> theory) list
end;

structure RecdefPackage: RECDEF_PACKAGE =
struct

val quiet_mode = Tfl.quiet_mode;
val message = Tfl.message;



(** theory data **)

(* data kind 'HOL/recdef' *)

type recdef_info = {rules: thm list, induct: thm, tcs: term list};

structure RecdefArgs =
struct
  val name = "HOL/recdef";
  type T = recdef_info Symtab.table;

  val empty = Symtab.empty;
  val prep_ext = I;
  val merge: T * T -> T = Symtab.merge (K true);

  fun print sg tab =
    Pretty.writeln (Pretty.strs ("recdefs:" ::
      map (Sign.cond_extern sg Sign.constK o fst) (Symtab.dest tab)));
end;

structure RecdefData = TheoryDataFun(RecdefArgs);
val print_recdefs = RecdefData.print;


(* get and put data *)

fun get_recdef thy name =
  (case Symtab.lookup (RecdefData.get thy, name) of
    Some info => info
  | None => error ("Unknown recursive function " ^ quote name));

fun put_recdef name info thy =
  let
    val tab = Symtab.update_new ((name, info), RecdefData.get thy)
      handle Symtab.DUP _ => error ("Duplicate recursive function definition " ^ quote name);
  in RecdefData.put tab thy end;



(** add_recdef(_i) **)

fun gen_add_recdef tfl_def prep_att prep_ss app_thms raw_name R eq_srcs raw_ss raw_congs thy =
  let
    val name = Sign.intern_const (Theory.sign_of thy) raw_name;
    val bname = Sign.base_name name;

    val _ = Theory.requires thy "Recdef" "recursive function definitions";
    val _ = message ("Defining recursive function " ^ quote name ^ " ...");

    val ((eq_names, eqs), raw_eq_atts) = apfst split_list (split_list eq_srcs);
    val eq_atts = map (map (prep_att thy)) raw_eq_atts;
    val ss = (case raw_ss of None => Simplifier.simpset_of thy | Some x => prep_ss x);
    val (thy1, congs) = thy |> app_thms raw_congs;
    val (thy2, pats) = tfl_def thy1 name R eqs;
    val (result as {rules, induct, tcs}) = Tfl.simplify_defn (ss, congs) (thy2, (name, pats));
    val thy3 =
      thy2
      |> Theory.add_path bname
      |> PureThy.add_thmss [(("rules", rules), [])]
      |> PureThy.add_thms ((("induct", induct), []) :: ((eq_names ~~ rules) ~~ eq_atts))
      |> put_recdef name result
      |> Theory.parent_path;
  in (thy3, result) end;

val add_recdef = gen_add_recdef Tfl.define Attrib.global_attribute I IsarThy.apply_theorems;
val add_recdef_x = gen_add_recdef Tfl.define Attrib.global_attribute
  (Simplifier.simpset_of o ThyInfo.get_theory) IsarThy.apply_theorems;
val add_recdef_i = gen_add_recdef Tfl.define_i (K I) I IsarThy.apply_theorems_i;


(** package setup **)

(* setup theory *)

val setup = [RecdefData.init];


(* outer syntax *)

local open OuterParse in

val recdef_decl =
  name -- term -- Scan.repeat1 (opt_thm_name ":" -- term) --
  Scan.optional ($$$ "(" |-- $$$ "congs" |-- !!! (xthms1 --| $$$ ")")) [] --
  Scan.option ($$$ "(" |-- $$$ "simpset" |-- !!! (name --| $$$ ")"))
  >> (fn ((((f, R), eqs), congs), ss) => #1 o add_recdef_x f R (map triple_swap eqs) ss congs);

val recdefP =
  OuterSyntax.command "recdef" "define general recursive functions (TFL)"
    (recdef_decl >> Toplevel.theory);

val _ = OuterSyntax.add_keywords ["congs", "simpset"];
val _ = OuterSyntax.add_parsers [recdefP];

end;


end;
