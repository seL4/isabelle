(*  Title:      Pure/pure_thy.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Theorem database, derived theory operations, and the ProtoPure theory.
*)

signature BASIC_PURE_THY =
sig
  val print_theorems: theory -> unit
  val print_theory: theory -> unit
  val get_thm: theory -> xstring -> thm
  val get_thms: theory -> xstring -> thm list
  val get_thmss: theory -> xstring list -> thm list
  val thms_of: theory -> (string * thm) list
  structure ProtoPure:
    sig
      val thy: theory
      val flexpair_def: thm
      val Goal_def: thm
    end
end;

signature PURE_THY =
sig
  include BASIC_PURE_THY
  val cond_extern_thm_sg: Sign.sg -> string -> xstring
  val thms_containing: theory -> string list -> (string * thm) list
  val store_thm: (bstring * thm) * theory attribute list -> theory -> theory * thm
  val smart_store_thms: (bstring * thm list) -> thm list
  val forall_elim_var: int -> thm -> thm
  val forall_elim_vars: int -> thm -> thm
  val add_thms: ((bstring * thm) * theory attribute list) list -> theory -> theory
  val add_thmss: ((bstring * thm list) * theory attribute list) list -> theory -> theory
  val have_thmss: bstring -> theory attribute list ->
    (thm list * theory attribute list) list -> theory -> theory * thm list
  val add_axioms: ((bstring * string) * theory attribute list) list -> theory -> theory
  val add_axioms_i: ((bstring * term) * theory attribute list) list -> theory -> theory
  val add_axiomss: ((bstring * string list) * theory attribute list) list -> theory -> theory
  val add_axiomss_i: ((bstring * term list) * theory attribute list) list -> theory -> theory
  val add_defs: ((bstring * string) * theory attribute list) list -> theory -> theory
  val add_defs_i: ((bstring * term) * theory attribute list) list -> theory -> theory
  val add_defss: ((bstring * string list) * theory attribute list) list -> theory -> theory
  val add_defss_i: ((bstring * term list) * theory attribute list) list -> theory -> theory
  val get_name: theory -> string
  val put_name: string -> theory -> theory
  val global_path: theory -> theory
  val local_path: theory -> theory
  val begin_theory: string -> theory list -> theory
  val end_theory: theory -> theory
  val checkpoint: theory -> theory
  val add_typedecls: (bstring * string list * mixfix) list -> theory -> theory
  val dummy_patternN: string
end;

structure PureThy: PURE_THY =
struct


(*** theorem database ***)

(** data kind 'Pure/theorems' **)

structure TheoremsDataArgs =
struct
  val name = "Pure/theorems";

  type T =
    {space: NameSpace.T,
      thms_tab: thm list Symtab.table,
      const_idx: int * (int * thm) list Symtab.table} ref;

  fun mk_empty _ =
    ref {space = NameSpace.empty, thms_tab = Symtab.empty, const_idx = (0, Symtab.empty)} : T;

  val empty = mk_empty ();
  fun copy (ref x) = ref x;
  val prep_ext = mk_empty;
  val merge = mk_empty;

  fun print sg (ref {space, thms_tab, const_idx = _}) =
    let
      val prt_thm = Display.pretty_thm o Thm.transfer_sg sg;
      fun prt_thms (name, [th]) =
            Pretty.block [Pretty.str (name ^ ":"), Pretty.brk 1, prt_thm th]
        | prt_thms (name, ths) = Pretty.big_list (name ^ ":") (map prt_thm ths);

      val thmss = NameSpace.cond_extern_table space thms_tab;
    in
      Pretty.writeln (Display.pretty_name_space ("theorem name space", space));
      Pretty.writeln (Pretty.big_list "theorems:" (map prt_thms thmss))
    end;
end;

structure TheoremsData = TheoryDataFun(TheoremsDataArgs);
val get_theorems_sg = TheoremsData.get_sg;
val get_theorems = TheoremsData.get;

val cond_extern_thm_sg = NameSpace.cond_extern o #space o ! o get_theorems_sg;


(* print theory *)

val print_theorems = TheoremsData.print;
fun print_theory thy =
  (Display.print_theory thy; print_theorems thy);



(** retrieve theorems **)

(* get_thms etc. *)

fun lookup_thms name thy =
  let val ref {space, thms_tab, ...} = get_theorems thy
  in Symtab.lookup (thms_tab, NameSpace.intern space name) end;

fun get_thms thy name =
  (case get_first (lookup_thms name) (thy :: Theory.ancestors_of thy) of
    None => raise THEORY ("Unknown theorem(s) " ^ quote name, [thy])
  | Some thms => thms);

fun get_thm thy name =
  (case get_thms thy name of
    [thm] => thm
  | _ => raise THEORY ("Single theorem expected " ^ quote name, [thy]));

fun get_thmss thy names = flat (map (get_thms thy) names);


(* thms_of *)

fun attach_name thm = (Thm.name_of_thm thm, thm);

fun thms_of thy =
  let val ref {thms_tab, ...} = get_theorems thy in
    map attach_name (flat (map snd (Symtab.dest thms_tab)))
  end;



(** theorems indexed by constants **)

(* make index *)

fun add_const_idx ((next, table), thm) =
  let
    val {hyps, prop, ...} = Thm.rep_thm thm;
    val consts =
      foldr add_term_consts (hyps, add_term_consts (prop, []));

    fun add (tab, c) =
      Symtab.update ((c, (next, thm) :: Symtab.lookup_multi (tab, c)), tab);
  in (next + 1, foldl add (table, consts)) end;

fun make_const_idx thm_tab =
  Symtab.foldl (fn (x, (_, ths)) => foldl add_const_idx (x, ths)) ((0, Symtab.empty), thm_tab);


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
      in map (attach_name o snd) (ints ithmss) end;

(*search globally*)
fun thms_containing thy consts =
  (case filter (is_none o Sign.const_type (Theory.sign_of thy)) consts of
    [] => flat (map (containing consts) (thy :: Theory.ancestors_of thy))
  | cs => raise THEORY ("thms_containing: undeclared consts " ^ commas_quote cs, [thy]));



(** store theorems **)                    (*DESTRUCTIVE*)

(* naming *)

fun gen_names len name =
  map (fn i => name ^ "_" ^ string_of_int i) (1 upto len);

fun name_single name x = [(name, x)];
fun name_multi name xs = gen_names (length xs) name ~~ xs;


(* enter_thmx *)

fun warn_overwrite name = warning ("Replaced old copy of theorems " ^ quote name);
fun warn_same name = warning ("Theorem database already contains a copy of " ^ quote name);

fun enter_thmx _ app_name ("", thmx) = map #2 (app_name "" thmx)
  | enter_thmx sg app_name (bname, thmx) =
      let
        val name = Sign.full_name sg bname;
        val named_thms = map Thm.name_thm (app_name name thmx);

        val r as ref {space, thms_tab, const_idx} = get_theorems_sg sg;

        val overwrite =
          (case Symtab.lookup (thms_tab, name) of
            None => false
          | Some thms' =>
              if Library.equal_lists Thm.eq_thm (thms', named_thms) then (warn_same name; false)
              else (warn_overwrite name; true));

        val space' = NameSpace.extend (space, [name]);
        val thms_tab' = Symtab.update ((name, named_thms), thms_tab);
        val const_idx' =
          if overwrite then make_const_idx thms_tab'
          else foldl add_const_idx (const_idx, named_thms);
      in r := {space = space', thms_tab = thms_tab', const_idx = const_idx'}; named_thms end;


(* add_thms(s) *)

fun add_thmx app_name app_att ((bname, thmx), atts) thy =
  let
    val (thy', thmx') = app_att ((thy, thmx), atts);
    val thms'' = enter_thmx (Theory.sign_of thy') app_name (bname, thmx');
  in (thy', thms'') end;

fun add_thmxs name app = Library.apply o map (fst oo add_thmx name app);

val add_thms = add_thmxs name_single Thm.apply_attributes;
val add_thmss = add_thmxs name_multi Thm.applys_attributes;


(* have_thmss *)

fun have_thmss bname more_atts ths_atts thy =
  let
    fun app (x, (ths, atts)) = Thm.applys_attributes ((x, ths), atts);
    val (thy', thmss') =
      foldl_map app (thy, map (fn (ths, atts) => (ths, atts @ more_atts)) ths_atts);
    val thms' = flat thmss';
    val thms'' = enter_thmx (Theory.sign_of thy') name_multi (bname, thms');
  in (thy', thms'') end;


(* store_thm *)

fun store_thm th_atts thy =
  let val (thy', [th']) = add_thmx name_single Thm.apply_attributes th_atts thy
  in (thy', th') end;


(* smart_store_thms *)

fun smart_store_thms (name, []) = error ("Cannot store empty list of theorems: " ^ quote name)
  | smart_store_thms (name, [thm]) = enter_thmx (Thm.sign_of_thm thm) name_single (name, thm)
  | smart_store_thms (name, thms) =
      let
        val merge_sg = Sign.merge_refs o apsnd (Sign.self_ref o Thm.sign_of_thm);
        val sg_ref = foldl merge_sg (Sign.self_ref (Thm.sign_of_thm (hd thms)), tl thms);
      in enter_thmx (Sign.deref sg_ref) name_multi (name, thms) end;


(* forall_elim_vars (belongs to drule.ML) *)

(*Replace outermost quantified variable by Var of given index.
    Could clash with Vars already present.*)
fun forall_elim_var i th =
    let val {prop,sign,...} = rep_thm th
    in case prop of
          Const("all",_) $ Abs(a,T,_) =>
              forall_elim (cterm_of sign (Var((a,i), T)))  th
        | _ => raise THM("forall_elim_var", i, [th])
    end;

(*Repeat forall_elim_var until all outer quantifiers are removed*)
fun forall_elim_vars i th =
    forall_elim_vars i (forall_elim_var i th)
        handle THM _ => th;


(* store axioms as theorems *)

local
  fun get_axs thy named_axs =
    map (forall_elim_vars 0 o Thm.get_axiom thy o fst) named_axs;

  fun add_single add ((name, ax), atts) thy =
    let
      val named_ax = name_single name ax;
      val thy' = add named_ax thy;
      val thm = hd (get_axs thy' named_ax);
    in add_thms [((name, thm), atts)] thy' end;

  fun add_multi add ((name, axs), atts) thy =
    let
      val named_axs = name_multi name axs;
      val thy' = add named_axs thy;
      val thms = get_axs thy' named_axs;
    in add_thmss [((name, thms), atts)] thy' end;

  fun add_singles add = Library.apply o map (add_single add);
  fun add_multis add = Library.apply o map (add_multi add);
in
  val add_axioms    = add_singles Theory.add_axioms;
  val add_axioms_i  = add_singles Theory.add_axioms_i;
  val add_axiomss   = add_multis Theory.add_axioms;
  val add_axiomss_i = add_multis Theory.add_axioms_i;
  val add_defs      = add_singles Theory.add_defs;
  val add_defs_i    = add_singles Theory.add_defs_i;
  val add_defss     = add_multis Theory.add_defs;
  val add_defss_i   = add_multis Theory.add_defs_i;
end;



(*** derived theory operations ***)

(** theory management **)

(* data kind 'Pure/theory_management' *)

structure TheoryManagementDataArgs =
struct
  val name = "Pure/theory_management";
  type T = {name: string, version: int};

  val empty = {name = "", version = 0};
  val copy = I;
  val prep_ext  = I;
  fun merge _ = empty;
  fun print _ _ = ();
end;

structure TheoryManagementData = TheoryDataFun(TheoryManagementDataArgs);
val get_info = TheoryManagementData.get;
val put_info = TheoryManagementData.put;


(* get / put name *)

val get_name = #name o get_info;
fun put_name name = put_info {name = name, version = 0};


(* control prefixing of theory name *)

val global_path = Theory.root_path;

fun local_path thy =
  thy |> Theory.root_path |> Theory.add_path (get_name thy);


(* begin / end theory *)

fun begin_theory name thys =
  Theory.prep_ext_merge thys
  |> put_name name
  |> local_path;

fun end_theory thy = Theory.add_name (get_name thy) thy;

fun checkpoint thy =
  if is_draft thy then
    let val {name, version} = get_info thy in
      thy
      |> Theory.add_name (name ^ ":" ^ string_of_int version)
      |> put_info {name = name, version = version + 1}
    end
  else thy;



(** add logical types **)

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



(*** the ProtoPure theory ***)

val dummy_patternN = "dummy_pattern";

val proto_pure =
  Theory.pre_pure
  |> Library.apply [TheoremsData.init, TheoryManagementData.init]
  |> put_name "ProtoPure"
  |> global_path
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
  |> Theory.add_modesyntax (Symbol.symbolsN, true) Syntax.pure_sym_syntax
  |> Theory.add_modesyntax (Symbol.xsymbolsN, true) Syntax.pure_xsym_syntax
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
    ("TYPE", "'a itself", NoSyn),
    (dummy_patternN, "'a", Delimfix "'_")]
  |> Theory.add_modesyntax ("", false)
    [("Goal", "prop => prop", Mixfix ("_", [0], 1000))]
  |> local_path
  |> (add_defs o map Thm.no_attributes)
   [("flexpair_def", "(t =?= u) == (t == u::'a::{})"),
    ("Goal_def", "GOAL (PROP A) == PROP A")]
  |> end_theory;

structure ProtoPure =
struct
  val thy = proto_pure;
  val flexpair_def = get_axiom thy "flexpair_def";
  val Goal_def = get_axiom thy "Goal_def";
end;


end;


structure BasicPureThy: BASIC_PURE_THY = PureThy;
open BasicPureThy;
