(*  Title:      HOL/Tools/recdef_package.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Wrapper module for Konrad Slind's TFL package.
*)

signature RECDEF_PACKAGE =
sig
  val quiet_mode: bool ref
  val print_recdefs: theory -> unit
  val get_recdef: theory -> string
    -> {simps: thm list, rules: thm list list, induct: thm, tcs: term list} option
  val add_recdef: xstring -> string -> ((bstring * string) * Args.src list) list
    -> simpset option -> (xstring * Args.src list) list -> theory
    -> theory * {simps: thm list, rules: thm list list, induct: thm, tcs: term list}
  val add_recdef_i: xstring -> term -> ((bstring * term) * theory attribute list) list
    -> simpset option -> (thm * theory attribute list) list
    -> theory -> theory * {simps: thm list, rules: thm list list, induct: thm, tcs: term list}
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

type recdef_info = {simps: thm list, rules: thm list list, induct: thm, tcs: term list};

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
      map #1 (Sign.cond_extern_table sg Sign.constK tab)));
end;

structure RecdefData = TheoryDataFun(RecdefArgs);
val print_recdefs = RecdefData.print;


(* get and put data *)

fun get_recdef thy name = Symtab.lookup (RecdefData.get thy, name);

fun put_recdef name info thy =
  let
    val tab = Symtab.update_new ((name, info), RecdefData.get thy)
      handle Symtab.DUP _ => error ("Duplicate recursive function definition " ^ quote name);
  in RecdefData.put tab thy end;



(** add_recdef(_i) **)

fun requires_recdef thy = Theory.requires thy "Recdef" "recursive functions";

fun gen_add_recdef tfl_fn prep_att app_thms raw_name R eq_srcs opt_ss raw_congs thy =
  let
    val name = Sign.intern_const (Theory.sign_of thy) raw_name;
    val bname = Sign.base_name name;

    val _ = requires_recdef thy;
    val _ = message ("Defining recursive function " ^ quote name ^ " ...");

    val ((eq_names, eqs), raw_eq_atts) = apfst split_list (split_list eq_srcs);
    val eq_atts = map (map (prep_att thy)) raw_eq_atts;
    val ss = if_none opt_ss (Simplifier.simpset_of thy);
    val (thy, congs) = thy |> app_thms raw_congs;

    val (thy, {rules = rules_idx, induct, tcs}) = tfl_fn thy name R (ss, congs) eqs;
    val rules = map (map #1) (Library.partition_eq Library.eq_snd rules_idx);
    val simp_att = if null tcs then [Simplifier.simp_add_global] else [];

    val case_numbers = map Library.string_of_int (1 upto Thm.nprems_of induct);
    val (thy, (simps' :: rules', [induct'])) =
      thy
      |> Theory.add_path bname
      |> PureThy.add_thmss ((("simps", flat rules), simp_att) :: ((eq_names ~~ rules) ~~ eq_atts))
      |>>> PureThy.add_thms [(("induct", induct), [RuleCases.case_names case_numbers])];
    val result = {simps = simps', rules = rules', induct = induct', tcs = tcs};
    val thy =
      thy
      |> put_recdef name result
      |> Theory.parent_path;
  in (thy, result) end;

val add_recdef = gen_add_recdef Tfl.define Attrib.global_attribute IsarThy.apply_theorems;
val add_recdef_x = gen_add_recdef Tfl.define Attrib.global_attribute IsarThy.apply_theorems;
val add_recdef_i = gen_add_recdef Tfl.define_i (K I) IsarThy.apply_theorems_i;



(** defer_recdef(_i) **)

fun gen_defer_recdef tfl_fn app_thms raw_name eqs raw_congs thy =
  let
    val name = Sign.intern_const (Theory.sign_of thy) raw_name;
    val bname = Sign.base_name name;

    val _ = requires_recdef thy;
    val _ = message ("Deferred recursive function " ^ quote name ^ " ...");

    val (thy1, congs) = thy |> app_thms raw_congs;
    val (thy2, induct_rules) = tfl_fn thy1 name congs eqs;
    val (thy3, [induct_rules']) =
      thy2
      |> Theory.add_path bname
      |> PureThy.add_thms [(("induct_rules", induct_rules), [])]
      |>> Theory.parent_path;
  in (thy3, {induct_rules = induct_rules'}) end;

val defer_recdef = gen_defer_recdef Tfl.defer IsarThy.apply_theorems;
val defer_recdef_i = gen_defer_recdef Tfl.defer_i IsarThy.apply_theorems_i;



(** package setup **)

(* setup theory *)

val setup = [RecdefData.init];


(* outer syntax *)

local structure P = OuterParse and K = OuterSyntax.Keyword in

val recdef_decl =
  P.name -- P.term -- Scan.repeat1 (P.opt_thm_name ":" -- P.prop --| P.marg_comment) --
  Scan.optional (P.$$$ "congs" |-- P.!!! P.xthms1) []
  >> (fn (((f, R), eqs), congs) => #1 o add_recdef_x f R (map P.triple_swap eqs) None congs);

val recdefP =
  OuterSyntax.command "recdef" "define general recursive functions (TFL)" K.thy_decl
    (recdef_decl >> Toplevel.theory);


val defer_recdef_decl =
  P.name -- Scan.repeat1 P.prop --
  Scan.optional (P.$$$ "(" |-- P.$$$ "congs" |-- P.!!! (P.xthms1 --| P.$$$ ")")) []
  >> (fn ((f, eqs), congs) => #1 o defer_recdef f eqs congs);

val defer_recdefP =
  OuterSyntax.command "defer_recdef" "defer general recursive functions (TFL)" K.thy_decl
    (defer_recdef_decl >> Toplevel.theory);

val _ = OuterSyntax.add_keywords ["congs", "simpset"];
val _ = OuterSyntax.add_parsers [recdefP, defer_recdefP];

end;


end;
