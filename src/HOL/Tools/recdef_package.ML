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
  val add_recdef: xstring -> string -> string list -> simpset option
    -> (xstring * Args.src list) list -> theory
    -> theory * {rules: thm list, induct: thm, tcs: term list}
  val add_recdef_i: xstring -> term -> term list -> simpset option
    -> (thm * theory attribute list) list
    -> theory -> theory * {rules: thm list, induct: thm, tcs: term list}
  val defer_recdef: xstring -> string list -> (xstring * Args.src list) list
    -> theory -> theory * {induct_rules: thm}
  val defer_recdef_i: xstring -> term list -> (thm * theory attribute list) list
    -> theory -> theory * {induct_rules: thm}
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
  val copy = I;
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

fun requires_recdef thy = Theory.requires thy "Recdef" "recursive functions";

fun gen_add_recdef tfl_fn prep_ss app_thms raw_name R eqs raw_ss raw_congs thy =
  let
    val name = Sign.intern_const (Theory.sign_of thy) raw_name;
    val bname = Sign.base_name name;

    val _ = requires_recdef thy;
    val _ = message ("Defining recursive function " ^ quote name ^ " ...");

    val ss = (case raw_ss of None => Simplifier.simpset_of thy | Some x => prep_ss x);
    val (thy1, congs) = thy |> app_thms raw_congs;
    val (thy2, pats) = tfl_fn thy1 name R eqs;
    val (result as {rules, induct, tcs}) = Tfl.simplify_defn (ss, congs) (thy2, (name, pats));
    val thy3 =
      thy2
      |> Theory.add_path bname
      |> PureThy.add_thmss [(("rules", rules), [])]
      |> PureThy.add_thms [(("induct", induct), [])]
      |> put_recdef name result
      |> Theory.parent_path;
  in (thy3, result) end;

val add_recdef = gen_add_recdef Tfl.define I IsarThy.apply_theorems;
val add_recdef_x = gen_add_recdef Tfl.define (Simplifier.simpset_of o ThyInfo.get_theory)
  IsarThy.apply_theorems;
val add_recdef_i = gen_add_recdef Tfl.define_i I IsarThy.apply_theorems_i;



(** defer_recdef(_i) **)

fun gen_defer_recdef tfl_fn app_thms raw_name eqs raw_congs thy =
  let
    val name = Sign.intern_const (Theory.sign_of thy) raw_name;
    val bname = Sign.base_name name;

    val _ = requires_recdef thy;
    val _ = message ("Deferred recursive function " ^ quote name ^ " ...");

    val (thy1, congs) = thy |> app_thms raw_congs;
    val (thy2, induct_rules) = tfl_fn thy1 name congs eqs;
    val thy3 =
      thy2
      |> Theory.add_path bname
      |> PureThy.add_thms [(("induct_rules", induct_rules), [])]
      |> Theory.parent_path;
  in (thy3, {induct_rules = induct_rules}) end;

val defer_recdef = gen_defer_recdef Tfl.defer IsarThy.apply_theorems;
val defer_recdef_i = gen_defer_recdef Tfl.defer_i IsarThy.apply_theorems_i;



(** package setup **)

(* setup theory *)

val setup = [RecdefData.init];


(* outer syntax *)

local structure P = OuterParse and K = OuterSyntax.Keyword in

val recdef_decl =
  P.name -- P.term -- Scan.repeat1 P.term --
  Scan.optional (P.$$$ "(" |-- P.$$$ "congs" |-- P.!!! (P.xthms1 --| P.$$$ ")")) [] --
  Scan.option (P.$$$ "(" |-- P.$$$ "simpset" |-- P.!!! (P.name --| P.$$$ ")"))
  >> (fn ((((f, R), eqs), congs), ss) => #1 o add_recdef_x f R eqs ss congs);

val recdefP =
  OuterSyntax.command "recdef" "define general recursive functions (TFL)" K.thy_decl
    (recdef_decl >> Toplevel.theory);


val defer_recdef_decl =
  P.name -- Scan.repeat1 P.term --
  Scan.optional (P.$$$ "(" |-- P.$$$ "congs" |-- P.!!! (P.xthms1 --| P.$$$ ")")) []
  >> (fn ((f, eqs), congs) => #1 o defer_recdef f eqs congs);

val defer_recdefP =
  OuterSyntax.command "defer_recdef" "defer general recursive functions (TFL)" K.thy_decl
    (defer_recdef_decl >> Toplevel.theory);

val _ = OuterSyntax.add_keywords ["congs", "simpset"];
val _ = OuterSyntax.add_parsers [recdefP, defer_recdefP];

end;


end;
