(*  Title:      Pure/pure_thy.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

The Pure theories.
*)

signature BASIC_PURE_THY =
sig
  val get_thm: theory -> xstring -> thm
  val get_thms: theory -> xstring -> thm list
  val thms_of: theory -> (string * thm) list
end;

signature PURE_THY =
sig
  include BASIC_PURE_THY
  val thms_closure: theory -> xstring -> tthm list option
  val get_tthm: theory -> xstring -> tthm
  val get_tthms: theory -> xstring -> tthm list
  val thms_containing: theory -> string list -> (string * thm) list
  val smart_store_thm: (bstring * thm) -> thm
  val add_tthms: ((bstring * tthm) * theory attribute list) list -> theory -> theory
  val add_tthmss: ((bstring * tthm list) * theory attribute list) list -> theory -> theory
  val add_axioms: ((bstring * string) * theory attribute list) list -> theory -> theory
  val add_axioms_i: ((bstring * term) * theory attribute list) list -> theory -> theory
  val add_axioms_x: ((bstring * string) * tag list) list -> theory -> theory
  val add_axiomss: ((bstring * string list) * theory attribute list) list -> theory -> theory
  val add_axiomss_i: ((bstring * term list) * theory attribute list) list -> theory -> theory
  val add_defs: ((bstring * string) * theory attribute list) list -> theory -> theory
  val add_defs_i: ((bstring * term) * theory attribute list) list -> theory -> theory
  val add_defs_x: ((bstring * string) * tag list) list -> theory -> theory
  val add_defss: ((bstring * string list) * theory attribute list) list -> theory -> theory
  val add_defss_i: ((bstring * term list) * theory attribute list) list -> theory -> theory
  val add_typedecls: (bstring * string list * mixfix) list -> theory -> theory
  val proto_pure: theory
  val pure: theory
  val cpure: theory
end;

structure PureThy: PURE_THY =
struct


(*** theorem database ***)

(** data kind 'Pure/theorems' **)

val theoremsK = "Pure/theorems";

exception Theorems of
 {space: NameSpace.T,
  thms_tab: tthm list Symtab.table,
  const_idx: int * (int * tthm) list Symtab.table} ref;


(* methods *)

local
  fun mk_empty _ =
    Theorems (ref {space = NameSpace.empty,
      thms_tab = Symtab.empty, const_idx = (0, Symtab.empty)});

  fun print sg (Theorems (ref {space, thms_tab, const_idx = _})) =
    let
      val prt_thm = Attribute.pretty_tthm o apfst (Thm.transfer_sg sg);
      fun prt_thms (name, [th]) =
            Pretty.block [Pretty.str (name ^ ":"), Pretty.brk 1, prt_thm th]
        | prt_thms (name, ths) = Pretty.big_list (name ^ ":") (map prt_thm ths);

      fun extrn name =
        if ! long_names then name else NameSpace.extern space name;
      val thmss = sort_wrt fst (map (apfst extrn) (Symtab.dest thms_tab));
    in
      Pretty.writeln (Display.pretty_name_space ("theorem name space", space));
      Pretty.writeln (Pretty.big_list "theorems:" (map prt_thms thmss))
    end;
in
  val theorems_setup = Theory.init_data [(theoremsK, (mk_empty (), mk_empty, mk_empty, print))];
end;


(* get data record *)

fun get_theorems_sg sg =
  (case Sign.get_data sg theoremsK of
    Theorems r => r
  | _ => type_error theoremsK);

val get_theorems = get_theorems_sg o Theory.sign_of;



(** retrieve theorems **)

(* thms_closure *)

(*note: we avoid life references to the theory, so users may safely
  keep thms_closure without too much space consumption*)

fun thms_closure_aux thy =
  let val ref {space, thms_tab, ...} = get_theorems thy
  in fn name => Symtab.lookup (thms_tab, NameSpace.intern space name) end;

fun thms_closure thy =
  let val closures = map thms_closure_aux (thy :: Theory.ancestors_of thy)
  in fn name => get_first (fn f => f name) closures end;


(* get_thms etc. *)

fun lookup_thms name thy = thms_closure_aux thy name;

fun get_tthms thy name =
  (case get_first (lookup_thms name) (thy :: Theory.ancestors_of thy) of
    None => raise THEORY ("Unknown theorem(s) " ^ quote name, [thy])
  | Some thms => thms);

fun get_tthm thy name =
  (case get_tthms thy name of
    [thm] => thm
  | _ => raise THEORY ("Single theorem expected " ^ quote name, [thy]));

fun get_thms thy = map Attribute.thm_of o get_tthms thy;
fun get_thm thy = Attribute.thm_of o get_tthm thy;


(* thms_of *)

fun attach_name (thm, _) = (Thm.name_of_thm thm, thm);

fun thms_of thy =
  let val ref {thms_tab, ...} = get_theorems thy in
    map attach_name (flat (map snd (Symtab.dest thms_tab)))
  end;



(** theorems indexed by constants **)

(* make index *)

val ignore = ["Trueprop", "all", "==>", "=="];

fun add_const_idx ((next, table), tthm as (thm, _)) =
  let
    val {hyps, prop, ...} = Thm.rep_thm thm;
    val consts =
      foldr add_term_consts (hyps, add_term_consts (prop, [])) \\ ignore;

    fun add (tab, c) =
      Symtab.update ((c, (next, tthm) :: Symtab.lookup_multi (tab, c)), tab);
  in (next + 1, foldl add (table, consts)) end;

fun make_const_idx thm_tab =
  foldl (foldl add_const_idx) ((0, Symtab.empty), map snd (Symtab.dest thm_tab));


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

(* naming *)

fun gen_names len name =
  map (fn i => name ^ "_" ^ string_of_int i) (1 upto len);

fun name_single name x = [(name, x)];
fun name_multi name xs = gen_names (length xs) name ~~ xs;


(* enter_tthmx *)

fun warn_overwrite name =
  warning ("Replaced old copy of theorems " ^ quote name);

fun warn_same name =
  warning ("Theorem database already contains a copy of " ^ quote name);  

fun enter_tthmx sg app_name (bname, tthmx) =
  let
    val name = Sign.full_name sg bname;
    fun name_tthm (nm, (thm, tgs)) = (Thm.name_thm (nm, thm), tgs);
    val named_tthms = map name_tthm (app_name name tthmx);

    fun eq_tthm ((th1, _), (th2, _)) = Thm.eq_thm (th1, th2);

    val r as ref {space, thms_tab, const_idx} = get_theorems_sg sg;

    val overwrite =
      (case Symtab.lookup (thms_tab, name) of
        None => false
      | Some tthms' =>
          if length tthms' = length named_tthms andalso forall2 eq_tthm (tthms', named_tthms) then
            (warn_same name; false)
          else (warn_overwrite name; true));

    val space' = NameSpace.extend (space, [name]);
    val thms_tab' = Symtab.update ((name, named_tthms), thms_tab);
    val const_idx' =
      if overwrite then make_const_idx thms_tab'
      else foldl add_const_idx (const_idx, named_tthms);
  in
    r := {space = space', thms_tab = thms_tab', const_idx = const_idx'};
    named_tthms
  end;


(* add_tthms(s) *)

fun add_tthmx app_name app_att ((bname, tthmx), atts) thy =
  let val (thy', tthmx') = app_att ((thy, tthmx), atts)
  in enter_tthmx (Theory.sign_of thy') app_name (bname, tthmx'); thy' end;

val add_tthms = Theory.apply o map (add_tthmx name_single Attribute.apply);
val add_tthmss = Theory.apply o map (add_tthmx name_multi Attribute.applys);


(* smart_store_thm *)

fun smart_store_thm (name, thm) =
  let val [(thm', _)] = enter_tthmx (Thm.sign_of_thm thm) name_single (name, Attribute.tthm_of thm)
  in thm' end;


(* store axioms as theorems *)

local
  fun add_ax app_name add ((name, axs), atts) thy =
    let
      val named_axs = app_name name axs;
      val thy' = add named_axs thy;
      val tthms = map (Attribute.tthm_of o Thm.get_axiom thy' o fst) named_axs;
    in add_tthmss [((name, tthms), atts)] thy' end;

  fun add_axs app_name add = Theory.apply o map (add_ax app_name add);
in
  val add_axioms    = add_axs name_single Theory.add_axioms;
  val add_axioms_i  = add_axs name_single Theory.add_axioms_i;
  val add_axiomss   = add_axs name_multi Theory.add_axioms;
  val add_axiomss_i = add_axs name_multi Theory.add_axioms_i;
  val add_defs      = add_axs name_single Theory.add_defs;
  val add_defs_i    = add_axs name_single Theory.add_defs_i;
  val add_defss     = add_axs name_multi Theory.add_defs;
  val add_defss_i   = add_axs name_multi Theory.add_defs_i;
end;

fun add_axioms_x axms thy = add_axioms (map (apsnd (map (Attribute.global_attr thy))) axms) thy;
fun add_defs_x defs thy = add_defs (map (apsnd (map (Attribute.global_attr thy))) defs) thy;



(*** add logical types ***)

fun add_typedecls decls thy =
  let
    val full = Sign.full_name (Theory.sign_of thy);

    fun type_of (raw_name, vs, mx) =
      if null (duplicates vs) then (raw_name, length vs, mx)
      else error ("Duplicate parameters in type declaration: " ^ quote raw_name);

    fun arity_of (raw_name, len, mx) =
      (full (Syntax.type_name raw_name mx), replicate len logicS, logicS);

    val types = map type_of decls;
    val arities = map arity_of types;
  in
    thy
    |> Theory.add_types types
    |> Theory.add_arities_i arities
  end;



(*** the Pure theories ***)

val proto_pure =
  Theory.pre_pure
  |> Theory.apply [Attribute.setup, theorems_setup]
  |> Theory.add_types
   [("fun", 2, NoSyn),
    ("prop", 0, NoSyn),
    ("itself", 1, NoSyn),
    ("dummy", 0, NoSyn)]
  |> Theory.add_classes_i [(logicC, [])]
  |> Theory.add_defsort_i logicS
  |> Theory.add_arities_i
   [("fun", [logicS, logicS], logicS),
    ("prop", [], logicS),
    ("itself", [logicS], logicS)]
  |> Theory.add_nonterminals Syntax.pure_nonterms
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
    ("Goal", "prop => prop", Mixfix ("GOAL _", [999], 1000)),
    ("TYPE", "'a itself", NoSyn)]
  |> Theory.add_path "ProtoPure"
  |> (add_defs o map Attribute.none)
   [("flexpair_def", "(t =?= u) == (t == u::'a::{})"),
    ("Goal_def", "GOAL (PROP A) == PROP A")]
  |> Theory.add_name "ProtoPure";

val pure =
  Theory.prep_ext_merge [proto_pure]
  |> Theory.add_path "Pure"
  |> Theory.add_syntax Syntax.pure_appl_syntax
  |> Theory.add_name "Pure";

val cpure =
  Theory.prep_ext_merge [proto_pure]
  |> Theory.add_path "CPure"
  |> Theory.add_syntax Syntax.pure_applC_syntax
  |> Theory.add_name "CPure";


end;


structure BasicPureThy: BASIC_PURE_THY = PureThy;
open BasicPureThy;



(** theory structures **)

structure ProtoPure =
struct
  val thy = PureThy.proto_pure;
  val flexpair_def = get_axiom thy "flexpair_def";
  val Goal_def = get_axiom thy "Goal_def";
end;

structure Pure = struct val thy = PureThy.pure end;
structure CPure = struct val thy = PureThy.cpure end;
