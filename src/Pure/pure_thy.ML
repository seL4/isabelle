(*  Title:      Pure/pure_thy.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Init 'theorems' data.  The Pure theories.
*)

signature BASIC_PURE_THY =
sig
  val get_thm: theory -> xstring -> thm
  val get_thms: theory -> xstring -> thm list
  val thms_of: theory -> (string * thm) list
end

signature PURE_THY =
sig
  include BASIC_PURE_THY
  val thms_containing: theory -> string list -> (string * thm) list
  val store_thms: (bstring * thm) list -> theory -> theory
  val store_thmss: (bstring * thm list) list -> theory -> theory
  val smart_store_thm: (bstring * thm) -> thm
  val add_store_axioms: (bstring * string) list -> theory -> theory
  val add_store_axioms_i: (bstring * term) list -> theory -> theory
  val add_store_defs: (bstring * string) list -> theory -> theory
  val add_store_defs_i: (bstring * term) list -> theory -> theory
  val proto_pure: theory
  val pure: theory
  val cpure: theory
end;

structure PureThy: PURE_THY =
struct


(*** init theorems data ***)

(** data kind theorems **)

val theoremsK = "theorems";

exception Theorems of
 {space: NameSpace.T,
  thms_tab: thm list Symtab.table,
  const_idx: int * (int * thm) list Symtab.table} ref;


(* methods *)

local

fun mk_empty _ =
  Theorems (ref {space = NameSpace.empty,
    thms_tab = Symtab.null, const_idx = (0, Symtab.null)});

fun print (Theorems (ref {space, thms_tab, const_idx = _})) =
  let
    val prt_thm = Pretty.quote o Display.pretty_thm;
    fun prt_thms (name, [th]) =
          Pretty.block [Pretty.str (name ^ ":"), Pretty.brk 1, prt_thm th]
      | prt_thms (name, ths) = Pretty.big_list (name ^ ":") (map prt_thm ths);

    fun extrn name =
      if ! long_names then name else NameSpace.extern space name;
    val thmss = sort_wrt fst (map (apfst extrn) (Symtab.dest thms_tab));
  in
    Pretty.writeln (Pretty.strs ("theorem name space:" :: map quote (NameSpace.dest space)));
    Pretty.writeln (Pretty.big_list "theorems:" (map prt_thms thmss))
  end;

in

val theorems_data: string * (object * (object -> object) *
  (object * object -> object) * (object -> unit)) =
    (theoremsK, (mk_empty (), mk_empty, mk_empty, print));

end;


(* get data record *)

fun get_theorems_sg sg =
  (case Sign.get_data sg theoremsK of
    Theorems r => r
  | _ => sys_error "get_theorems_sg");

val get_theorems = get_theorems_sg o sign_of;



(** retrieve theorems **)

fun local_thms thy name =
  let
    val ref {space, thms_tab, ...} = get_theorems thy;
    val full_name = NameSpace.intern space name;
  in Symtab.lookup (thms_tab, full_name) end;

fun all_local_thms [] _ = None
  | all_local_thms (thy :: thys) name =
      (case local_thms thy name of
        None => all_local_thms thys name
      | some => some);


(* get_thm(s) *)

fun get_thms thy name =
  (case all_local_thms (thy :: Theory.ancestors_of thy) name of
    None => raise THEORY ("Theorems " ^ quote name ^ " not stored in theory", [thy])
  | Some thms => thms);

fun get_thm thy name =
  (case get_thms thy name of
    [thm] => thm
  | _ => raise THEORY ("Singleton list of theorems expected " ^ quote name, [thy]));


(* thms_of *)

fun attach_name thm = (Thm.name_of_thm thm, thm);

fun thms_of thy =
  let val ref {thms_tab, ...} = get_theorems thy in
    map attach_name (flat (map snd (Symtab.dest thms_tab)))
  end;



(** theorems indexed by constants **)

(* make index *)

val ignore = ["Trueprop", "all", "==>", "=="];

fun add_const_idx ((next, table), thm) =
  let
    val {hyps, prop, ...} = Thm.rep_thm thm;
    val consts =
      foldr add_term_consts (hyps, add_term_consts (prop, [])) \\ ignore;

    fun add (tab, c) =
      Symtab.update ((c, (next, thm) :: Symtab.lookup_multi (tab, c)), tab);
  in (next + 1, foldl add (table, consts)) end;

fun make_const_idx thm_tab =
  foldl (foldl add_const_idx) ((0, Symtab.null), map snd (Symtab.dest thm_tab));


(* lookup index *)

(*search locally*)
fun containing [] thy = thms_of thy
  | containing consts thy =
      let
        fun int ([], _) = []
          | int (_, []) = []
          | int (xxs as ((x as (i:int, _)) :: xs), yys as ((y as (j, _)) :: ys)) =
              if i = j then x :: int (xs, ys)
              else if i > j then int (xs, yys)
              else int (xxs, ys);

        fun ints [xs] = xs
          | ints xss = if exists null xss then [] else foldl int (hd xss, tl xss);

        val ref {const_idx = (_, ctab), ...} = get_theorems thy;
        val ithmss = map (fn c => Symtab.lookup_multi (ctab, c)) consts;
      in
        map (attach_name o snd) (ints ithmss)
      end;

(*search globally*)
fun thms_containing thy consts =
  flat (map (containing (consts \\ ignore)) (thy :: Theory.ancestors_of thy));



(** store theorems **)                    (*DESTRUCTIVE*)

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

    val r as ref {space, thms_tab, const_idx} = get_theorems_sg sg;

    val overwrite =
      (case Symtab.lookup (thms_tab, name) of
        None => false
      | Some thms' =>
          if length thms' = len andalso eq_thms (thms', named_thms) then
            (warn_same name; false)
          else (warn_overwrite name; true));

    val space' = NameSpace.extend ([name], space);
    val thms_tab' = Symtab.update ((name, named_thms), thms_tab);
    val const_idx' =
      if overwrite then make_const_idx thms_tab'
      else foldl add_const_idx (const_idx, named_thms);
  in
    r := {space = space', thms_tab = thms_tab', const_idx = const_idx'};
    named_thms
  end;

fun do_enter_thms sg single thms = (enter_thms sg single thms; ());


fun store_thmss thmss thy =
  (seq (do_enter_thms (sign_of thy) false) thmss; thy);

fun store_thms thms thy =
  (seq (do_enter_thms (sign_of thy) true) (map (apsnd (fn th => [th])) thms); thy);

fun smart_store_thm (name, thm) =
  let val [named_thm] = enter_thms (Thm.sign_of_thm thm) true (name, [thm])
  in named_thm end;


(* store axioms as theorems *)

fun add_store add named_axs thy =
  let
    val thy' = add named_axs thy;
    val named_thms = map (fn (name, _) => (name, get_axiom thy' name)) named_axs;
  in store_thms named_thms thy' end;

val add_store_axioms = add_store Theory.add_axioms;
val add_store_axioms_i = add_store Theory.add_axioms_i;
val add_store_defs = add_store Theory.add_defs;
val add_store_defs_i = add_store Theory.add_defs_i;



(** the Pure theories **)

val proto_pure =
  Theory.pre_pure
  |> Theory.init_data [theorems_data]
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
  |> Theory.add_path "ProtoPure"
  |> add_store_defs [("flexpair_def", "(t =?= u) == (t == u::'a::{})")]
  |> Theory.add_name "ProtoPure";

val pure =
  Theory.prep_ext_merge [proto_pure]
  |> Theory.add_syntax Syntax.pure_appl_syntax
  |> Theory.add_path "Pure"
  |> Theory.add_name "Pure";

val cpure =
  Theory.prep_ext_merge [proto_pure]
  |> Theory.add_syntax Syntax.pure_applC_syntax
  |> Theory.add_path "CPure"
  |> Theory.add_name "CPure";


end;


structure BasicPureThy: BASIC_PURE_THY = PureThy;
open BasicPureThy;



(** theory structures **)

structure ProtoPure =
struct
  val thy = PureThy.proto_pure;
  val flexpair_def = get_axiom thy "flexpair_def";
end;

structure Pure = struct val thy = PureThy.pure end;
structure CPure = struct val thy = PureThy.cpure end;
