(*  Title:      Pure/pure_thy.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Init 'theorems' data.  The Pure theories.
*)

signature PURE_THY =
sig
  val put_thms: (bstring * thm) list -> theory -> theory        (*DESTRUCTIVE*)
  val put_thmss: (bstring * thm list) list -> theory -> theory  (*DESTRUCTIVE*)
  val store_thm: (bstring * thm) -> thm                         (*DESTRUCTIVE*)
  val get_thm: theory -> xstring -> thm
  val get_thms: theory -> xstring -> thm list
  val proto_pure: theory
  val pure: theory
  val cpure: theory
end;

structure PureThy: PURE_THY =
struct


(** init theorems data **)

(* data kind theorems *)

val theorems = "theorems";

exception Theorems of
  {space: NameSpace.T, thms_tab: thm list Symtab.table} ref;


(* methods *)

local

val empty =
  Theorems (ref {space = NameSpace.empty, thms_tab = Symtab.null});

fun ext (Theorems (ref {space, ...})) =
  Theorems (ref {space = space, thms_tab = Symtab.null});

fun merge (Theorems (ref {space = space1, ...}), Theorems (ref {space = space2, ...})) =
  Theorems (ref {space = NameSpace.merge (space1, space2), thms_tab = Symtab.null});

fun print (Theorems (ref {space, thms_tab})) =
  let
    val prt_thm = Pretty.quote o pretty_thm;
    fun prt_thms (name, [th]) =
          Pretty.block [Pretty.str (name ^ ":"), Pretty.brk 1, (prt_thm th)]
      | prt_thms (name, ths) = Pretty.big_list (name ^ ":") (map prt_thm ths);

    fun extrn name =
      if ! long_names then name else NameSpace.extern space name;
    val thmss = sort_wrt fst (map (apfst extrn) (Symtab.dest thms_tab));
  in
    Pretty.writeln (Pretty.strs ("theorem name space:" :: map quote (NameSpace.dest space)));
    Pretty.writeln (Pretty.big_list "theorems:" (map prt_thms thmss))
  end;

in

val theorems_methods = (empty, ext, merge, print);

end;


(* get data record *)

fun get_theorems sg =
  (case Sign.get_data sg theorems of
    Theorems r => r
  | _ => sys_error "get_theorems");


(* retrieve theorems *)

fun lookup_thms theory full_name =
  let
    val tab_of = #thms_tab o ! o get_theorems o sign_of;
    fun lookup [] = raise Match
      | lookup (thy :: thys) =
          (case Symtab.lookup (tab_of thy, full_name) of
            Some thms => thms
          | None => lookup (Theory.parents_of thy) handle Match => lookup thys)
  in
    lookup [theory] handle Match
      => raise THEORY ("No theorems " ^ quote full_name ^ " stored in theory", [theory])
  end;

fun get_thms thy name =
  let
    val ref {space, ...} = get_theorems (sign_of thy);
    val full_name = NameSpace.intern space name;
  in lookup_thms thy full_name end;

fun get_thm thy name =
  (case get_thms thy name of
    [thm] => thm
  | _ => raise THEORY ("Singleton theorem list expected " ^ quote name, [thy]));


(* store theorems *)                    (*DESTRUCTIVE*)

fun err_dup name =
  error ("Duplicate theorems " ^ quote name);

fun warn_overwrite name =
  warning ("Replaced old copy of theorems " ^ quote name);

fun warn_same name =
  warning ("Theorem database already contains a copy of " ^ quote name);


fun enter_thms sg single (raw_name, thms) =
  let
    val len = length thms;
    val name = Sign.full_name sg raw_name;
    val names =
      if single then replicate len name
      else map (fn i => name ^ "_" ^ string_of_int i) (0 upto (len - 1));
    val named_thms = ListPair.map Thm.name_thm (names, thms);

    val eq_thms = ListPair.all Thm.eq_thm;
    val r as ref {space, thms_tab = tab} = get_theorems sg;
  in
    (case Symtab.lookup (tab, name) of
      None =>
        if NameSpace.declared space name then err_dup name else ()
    | Some thms' =>
        if length thms' = len andalso eq_thms (thms', named_thms) then
          warn_same name
        else warn_overwrite name);

    r :=
     {space = NameSpace.extend ([name], space),
      thms_tab = Symtab.update ((name, named_thms), tab)};

    named_thms
  end;

fun do_enter_thms sg single name_thms =
  (enter_thms sg single name_thms; ());


fun put_thmss thmss thy =
  (seq (do_enter_thms (sign_of thy) false) thmss; thy);

fun put_thms thms thy =
  (seq (do_enter_thms (sign_of thy) true) (map (apsnd (fn th => [th])) thms); thy);

fun store_thm (name, thm) =
  let val [named_thm] = enter_thms (Thm.sign_of_thm thm) true (name, [thm])
  in named_thm end;



(** the Pure theories **)

val proto_pure =
  Theory.pre_pure
  |> Theory.init_data theorems theorems_methods
  |> Theory.add_types
   (("fun", 2, NoSyn) ::
    ("prop", 0, NoSyn) ::
    ("itself", 1, NoSyn) ::
    Syntax.pure_types)
  |> Theory.add_classes_i [(logicC, [])]
  |> Theory.add_defsort_i logicS
  |> Theory.add_arities_i
   [("fun", [logicS, logicS], logicS),
    ("prop", [], logicS),
    ("itself", [logicS], logicS)]
  |> Theory.add_syntax Syntax.pure_syntax
  |> Theory.add_modesyntax ("symbols", true) Syntax.pure_sym_syntax
  |> Theory.add_trfuns Syntax.pure_trfuns
  |> Theory.add_trfunsT Syntax.pure_trfunsT
  |> Theory.add_syntax
   [("==>", "[prop, prop] => prop", Delimfix "op ==>")]
  |> Theory.add_consts
   [("==", "['a::{}, 'a] => prop", InfixrName ("==", 2)),
    ("=?=", "['a::{}, 'a] => prop", InfixrName ("=?=", 2)),
    ("==>", "[prop, prop] => prop", Mixfix ("(_/ ==> _)", [2, 1], 1)),
    ("all", "('a => prop) => prop", Binder ("!!", 0, 0)),
    ("TYPE", "'a itself", NoSyn)]
  |> Theory.add_defs [("flexpair_def", "(t =?= u) == (t == u::'a::{})")]
  |> Theory.add_name "ProtoPure";

val pure = proto_pure
  |> Theory.add_syntax Syntax.pure_appl_syntax
  |> Theory.add_name "Pure";

val cpure = proto_pure
  |> Theory.add_syntax Syntax.pure_applC_syntax
  |> Theory.add_name "CPure";


end;



(** theory structures **)

structure ProtoPure =
struct
  val thy = PureThy.proto_pure;
  val flexpair_def = get_axiom thy "flexpair_def";
end;

structure Pure = struct val thy = PureThy.pure end;
structure CPure = struct val thy = PureThy.cpure end;
