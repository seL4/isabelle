(*  Title:      Pure/pure_thy.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Theorem storage.  The ProtoPure theory.
*)

signature BASIC_PURE_THY =
sig
  datatype interval = FromTo of int * int | From of int | Single of int
  datatype thmref = Name of string | NameSelection of string * interval list
  val print_theorems: theory -> unit
  val print_theory: theory -> unit
  val get_thm: theory -> thmref -> thm
  val get_thms: theory -> thmref -> thm list
  val get_thmss: theory -> thmref list -> thm list
  structure ProtoPure:
    sig
      val thy: theory
      val Goal_def: thm
    end
end;

signature PURE_THY =
sig
  include BASIC_PURE_THY
  val string_of_thmref: thmref -> string
  val print_theorems_diff: theory -> theory -> unit
  val get_thm_closure: theory -> thmref -> thm
  val get_thms_closure: theory -> thmref -> thm list
  val single_thm: string -> thm list -> thm
  val name_of_thmref: thmref -> string
  val map_name_of_thmref: (string -> string) -> thmref -> thmref
  val select_thm: thmref -> thm list -> thm list
  val selections: string * thm list -> (thmref * thm) list
  val theorems_of: theory -> thm list NameSpace.table
  val theorem_space: theory -> NameSpace.T
  val fact_index_of: theory -> FactIndex.T
  val valid_thms: theory -> thmref * thm list -> bool
  val thms_containing: theory -> FactIndex.spec -> (string * thm list) list
  val thms_containing_consts: theory -> string list -> (string * thm) list
  val thms_of: theory -> (string * thm) list
  val all_thms_of: theory -> (string * thm) list
  val hide_thms: bool -> string list -> theory -> theory
  val store_thm: (bstring * thm) * theory attribute list -> theory -> theory * thm
  val smart_store_thms: (bstring * thm list) -> thm list
  val smart_store_thms_open: (bstring * thm list) -> thm list
  val forall_elim_var: int -> thm -> thm
  val forall_elim_vars: int -> thm -> thm
  val add_thms: ((bstring * thm) * theory attribute list) list -> theory -> theory * thm list
  val add_thmss: ((bstring * thm list) * theory attribute list) list -> theory
    -> theory * thm list list
  val note_thmss: theory attribute -> ((bstring * theory attribute list) *
    (thmref * theory attribute list) list) list ->
    theory -> theory * (bstring * thm list) list
  val note_thmss_i: theory attribute -> ((bstring * theory attribute list) *
    (thm list * theory attribute list) list) list ->
    theory -> theory * (bstring * thm list) list
  val add_axioms: ((bstring * string) * theory attribute list) list ->
    theory -> theory * thm list
  val add_axioms_i: ((bstring * term) * theory attribute list) list ->
    theory -> theory * thm list
  val add_axiomss: ((bstring * string list) * theory attribute list) list ->
    theory -> theory * thm list list
  val add_axiomss_i: ((bstring * term list) * theory attribute list) list ->
    theory -> theory * thm list list
  val add_defs: bool -> ((bstring * string) * theory attribute list) list ->
    theory -> theory * thm list
  val add_defs_i: bool -> ((bstring * term) * theory attribute list) list ->
    theory -> theory * thm list
  val add_defss: bool -> ((bstring * string list) * theory attribute list) list ->
    theory -> theory * thm list list
  val add_defss_i: bool -> ((bstring * term list) * theory attribute list) list ->
    theory -> theory * thm list list
  val generic_setup: string -> theory -> theory
  val add_oracle: bstring * string * string -> theory -> theory
end;

structure PureThy: PURE_THY =
struct


(*** theorem database ***)

(** dataype theorems **)

fun pretty_theorems_diff thy prev_thms (space, thms) =
  let
    val prt_thm = Display.pretty_thm_sg thy;
    fun prt_thms (name, [th]) =
          Pretty.block [Pretty.str (name ^ ":"), Pretty.brk 1, prt_thm th]
      | prt_thms (name, ths) = Pretty.big_list (name ^ ":") (map prt_thm ths);

    val diff_thmss = Symtab.fold (fn fact =>
      if not (Symtab.member eq_thms prev_thms fact) then cons fact else I) thms [];
    val thmss = diff_thmss |> map (apfst (NameSpace.extern space)) |> Library.sort_wrt #1;
  in Pretty.big_list "theorems:" (map prt_thms thmss) end;

fun pretty_theorems thy = pretty_theorems_diff thy Symtab.empty;

structure TheoremsData = TheoryDataFun
(struct
  val name = "Pure/theorems";
  type T =
   {theorems: thm list NameSpace.table,
    index: FactIndex.T} ref;

  fun mk_empty _ =
    ref {theorems = NameSpace.empty_table, index = FactIndex.empty}: T;

  val empty = mk_empty ();
  fun copy (ref x) = ref x;
  val extend = mk_empty;
  fun merge _ = mk_empty;
  fun print thy (ref {theorems, index}) = Pretty.writeln (pretty_theorems thy theorems);
end);

val get_theorems_ref = TheoremsData.get;
val get_theorems = ! o get_theorems_ref;
val theorems_of = #theorems o get_theorems;
val theorem_space = #1 o theorems_of;
val fact_index_of = #index o get_theorems;


(* print theory *)

val print_theorems = TheoremsData.print;

fun print_theorems_diff prev_thy thy =
  Pretty.writeln (pretty_theorems_diff thy
    (#2 (theorems_of prev_thy)) (#theorems (get_theorems thy)));

fun print_theory thy =
  Display.pretty_full_theory thy @
    [pretty_theorems thy (#theorems (get_theorems thy))]
  |> Pretty.chunks |> Pretty.writeln;



(** retrieve theorems **)

fun the_thms _ (SOME thms) = thms
  | the_thms name NONE = error ("Unknown theorem(s) " ^ quote name);

fun single_thm _ [thm] = thm
  | single_thm name _ = error ("Single theorem expected " ^ quote name);


(* datatype interval *)

datatype interval =
  FromTo of int * int |
  From of int |
  Single of int;

fun interval _ (FromTo (i, j)) = i upto j
  | interval n (From i) = i upto n
  | interval _ (Single i) = [i];

fun string_of_interval (FromTo (i, j)) = string_of_int i ^ "-" ^ string_of_int j
  | string_of_interval (From i) = string_of_int i ^ "-"
  | string_of_interval (Single i) = string_of_int i;


(* datatype thmref *)

datatype thmref =
  Name of string |
  NameSelection of string * interval list;

fun name_of_thmref (Name name) = name
  | name_of_thmref (NameSelection (name, _)) = name;

fun map_name_of_thmref f (Name name) = Name (f name)
  | map_name_of_thmref f (NameSelection (name, is)) = NameSelection (f name, is);

fun string_of_thmref (Name name) = name
  | string_of_thmref (NameSelection (name, is)) =
      name ^ enclose "(" ")" (commas (map string_of_interval is));


(* select_thm *)

fun select_thm (Name _) thms = thms
  | select_thm (NameSelection (name, is)) thms =
      let
        val n = length thms;
        fun select i =
          if i < 1 orelse i > n then
            error ("Bad subscript " ^ string_of_int i ^ " for " ^
              quote name ^ " (length " ^ string_of_int n ^ ")")
          else List.nth (thms, i - 1);
      in map select (List.concat (map (interval n) is)) end;


(* selections *)

fun selections (name, [thm]) = [(Name name, thm)]
  | selections (name, thms) = (1 upto length thms, thms) |> ListPair.map (fn (i, thm) =>
      (NameSelection (name, [Single i]), thm));


(* get_thm(s)_closure -- statically scoped versions *)

(*beware of proper order of evaluation!*)

fun lookup_thms thy =
  let
    val thy_ref = Theory.self_ref thy;
    val (space, thms) = #theorems (get_theorems thy);
  in
    fn name =>
      Option.map (map (Thm.transfer (Theory.deref thy_ref)))     (*dynamic identity*)
      (Symtab.lookup thms (NameSpace.intern space name)) (*static content*)
  end;

fun get_thms_closure thy =
  let val closures = map lookup_thms (thy :: Theory.ancestors_of thy) in
    fn thmref =>
      let val name = name_of_thmref thmref
      in select_thm thmref (the_thms name (get_first (fn f => f name) closures)) end
  end;

fun get_thm_closure thy =
  let val get = get_thms_closure thy
  in fn thmref => single_thm (name_of_thmref thmref) (get thmref) end;


(* get_thms etc. *)

fun get_thms theory thmref =
  let val name = name_of_thmref thmref in
    get_first (fn thy => lookup_thms thy name) (theory :: Theory.ancestors_of theory)
    |> the_thms name |> select_thm thmref |> map (Thm.transfer theory)
  end;

fun get_thmss thy thmrefs = List.concat (map (get_thms thy) thmrefs);
fun get_thm thy thmref = single_thm (name_of_thmref thmref) (get_thms thy thmref);


(* thms_containing etc. *)

fun valid_thms thy (thmref, ths) =
  (case try (transform_error (get_thms thy)) thmref of
    NONE => false
  | SOME ths' => Thm.eq_thms (ths, ths'));

fun thms_containing theory spec =
  (theory :: Theory.ancestors_of theory)
  |> map (fn thy =>
      FactIndex.find (fact_index_of thy) spec
      |> List.filter (fn (name, ths) => valid_thms theory (Name name, ths))
      |> gen_distinct (eq_fst (op =)))
  |> List.concat;

fun thms_containing_consts thy consts =
  thms_containing thy (consts, []) |> map #2 |> List.concat
  |> map (fn th => (Thm.name_of_thm th, th));


(* thms_of etc. *)

fun thms_of thy =
  let val thms = #2 (theorems_of thy)
  in map (fn th => (Thm.name_of_thm th, th)) (List.concat (map snd (Symtab.dest thms))) end;

fun all_thms_of thy = List.concat (map thms_of (thy :: Theory.ancestors_of thy));



(** store theorems **)                    (*DESTRUCTIVE*)

(* hiding -- affects current theory node only *)

fun hide_thms fully names thy =
  let
    val r as ref {theorems = (space, thms), index} = get_theorems_ref thy;
    val space' = fold (NameSpace.hide fully) names space;
  in r := {theorems = (space', thms), index = index}; thy end;


(* naming *)

fun gen_names j len name =
  map (fn i => name ^ "_" ^ string_of_int i) (j + 1 upto j + len);

fun name_multi name xs = gen_names 0 (length xs) name ~~ xs;

fun name_thm pre (name, thm) =
  if Thm.name_of_thm thm <> "" andalso pre then thm else Thm.name_thm (name, thm);

fun name_thms pre name [x] = [name_thm pre (name, x)]
  | name_thms pre name xs = map (name_thm pre) (name_multi name xs);

fun name_thmss name xs =
  (case filter_out (null o fst) xs of
    [([x], z)] => [([name_thm true (name, x)], z)]
  | _ => snd (foldl_map (fn (i, (ys, z)) =>
    (i + length ys, (map (name_thm true) (gen_names i (length ys) name ~~ ys), z))) (0, xs)));


(* enter_thms *)

fun warn_overwrite name = warning ("Replaced old copy of theorems " ^ quote name);
fun warn_same name = warning ("Theorem database already contains a copy of " ^ quote name);

fun enter_thms _ _ app_att ("", thms) thy = app_att (thy, thms)
  | enter_thms pre_name post_name app_att (bname, thms) thy =
      let
        val name = Sign.full_name thy bname;
        val (thy', thms') = apsnd (post_name name) (app_att (thy, pre_name name thms));
        val r as ref {theorems = (space, theorems), index} = get_theorems_ref thy';
        val space' = Sign.declare_name thy' name space;
        val theorems' = Symtab.update (name, thms') theorems;
        val index' = FactIndex.add (K false) (name, thms') index;
      in
        (case Symtab.lookup theorems name of
          NONE => ()
        | SOME thms'' =>
            if Thm.eq_thms (thms', thms'') then warn_same name
            else warn_overwrite name);
        r := {theorems = (space', theorems'), index = index'};
        (thy', thms')
      end;


(* add_thms(s) *)

fun add_thms_atts pre_name ((bname, thms), atts) =
  enter_thms pre_name (name_thms false)
    (Thm.applys_attributes o rpair atts) (bname, thms);

fun gen_add_thmss pre_name args theory =
  foldl_map (fn (thy, arg) => add_thms_atts pre_name arg thy) (theory, args);

fun gen_add_thms pre_name args =
  apsnd (map hd) o gen_add_thmss pre_name (map (apfst (apsnd single)) args);

val add_thmss = gen_add_thmss (name_thms true);
val add_thms = gen_add_thms (name_thms true);


(* note_thmss(_i) *)

local

fun gen_note_thss get kind_att (thy, ((bname, more_atts), ths_atts)) =
  let
    fun app (x, (ths, atts)) = Thm.applys_attributes ((x, ths), atts);
    val (thy', thms) = thy |> enter_thms
      name_thmss (name_thms false) (apsnd List.concat o foldl_map app)
      (bname, map (fn (ths, atts) => (get thy ths, atts @ more_atts @ [kind_att])) ths_atts);
  in (thy', (bname, thms)) end;

fun gen_note_thmss get kind_att args thy =
  foldl_map (gen_note_thss get kind_att) (thy, args);

in

val note_thmss = gen_note_thmss get_thms;
val note_thmss_i = gen_note_thmss (K I);

end;


(* store_thm *)

fun store_thm ((bname, thm), atts) thy =
  let val (thy', [th']) = add_thms_atts (name_thms true) ((bname, [thm]), atts) thy
  in (thy', th') end;


(* smart_store_thms(_open) *)

local

fun smart_store _ (name, []) =
      error ("Cannot store empty list of theorems: " ^ quote name)
  | smart_store name_thm (name, [thm]) =
      #2 (enter_thms (name_thm true) (name_thm false) I (name, [thm]) (Thm.theory_of_thm thm))
  | smart_store name_thm (name, thms) =
      let
        fun merge (thy, th) = Theory.merge (thy, Thm.theory_of_thm th);
        val thy = Library.foldl merge (Thm.theory_of_thm (hd thms), tl thms);
      in #2 (enter_thms (name_thm true) (name_thm false) I (name, thms) thy) end;

in

val smart_store_thms = smart_store name_thms;
val smart_store_thms_open = smart_store (K (K I));

end;


(* forall_elim_var(s) -- belongs to drule.ML *)

fun forall_elim_vars_aux strip_vars i th =
  let
    val {thy, tpairs, prop, ...} = Thm.rep_thm th;
    val add_used = Term.fold_aterms
      (fn Var ((x, j), _) => if i = j then curry (op ins_string) x else I | _ => I);
    val used = fold (fn (t, u) => add_used t o add_used u) tpairs (add_used prop []);
    val vars = strip_vars prop;
    val cvars = (Term.variantlist (map #1 vars, used), vars)
      |> ListPair.map (fn (x, (_, T)) => Thm.cterm_of thy (Var ((x, i), T)));
  in fold Thm.forall_elim cvars th end;

val forall_elim_vars = forall_elim_vars_aux Term.strip_all_vars;

fun forall_elim_var i th = forall_elim_vars_aux
  (fn Const ("all", _) $ Abs (a, T, _) => [(a, T)]
  | _ => raise THM ("forall_elim_vars", i, [th])) i th;


(* store axioms as theorems *)

local
  fun get_ax thy (name, _) = Thm.get_axiom_i thy (Sign.full_name thy name);
  fun get_axs thy named_axs = map (forall_elim_vars 0 o get_ax thy) named_axs;

  fun add_single add (thy, ((name, ax), atts)) =
    let
      val named_ax = [(name, ax)];
      val thy' = add named_ax thy;
      val thm = hd (get_axs thy' named_ax);
    in apsnd hd (gen_add_thms (K I) [((name, thm), atts)] thy') end;

  fun add_multi add (thy, ((name, axs), atts)) =
    let
      val named_axs = name_multi name axs;
      val thy' = add named_axs thy;
      val thms = get_axs thy' named_axs;
    in apsnd hd (gen_add_thmss (K I) [((name, thms), atts)] thy') end;

  fun add_singles add args thy = foldl_map (add_single add) (thy, args);
  fun add_multis add args thy = foldl_map (add_multi add) (thy, args);
in
  val add_axioms    = add_singles Theory.add_axioms;
  val add_axioms_i  = add_singles Theory.add_axioms_i;
  val add_axiomss   = add_multis Theory.add_axioms;
  val add_axiomss_i = add_multis Theory.add_axioms_i;
  val add_defs      = add_singles o Theory.add_defs;
  val add_defs_i    = add_singles o Theory.add_defs_i;
  val add_defss     = add_multis o Theory.add_defs;
  val add_defss_i   = add_multis o Theory.add_defs_i;
end;



(*** ML setup ***)

(* generic_setup *)

val generic_setup =
  Context.use_let "val setup: (theory -> theory) list" "Library.apply setup";


(* add_oracle *)

fun add_oracle (name, T, oracle) =
  let val txt =
    "local\n\
    \  type T = " ^ T ^ ";\n\
    \  val oracle: theory -> T -> term = " ^ oracle ^ ";\n\
    \  val name = " ^ quote name ^ ";\n\
    \  exception Arg of T;\n\
    \  val _ = Context.>> (Theory.add_oracle (name, fn (thy, Arg x) => oracle thy x));\n\
    \  val thy = Context.the_context ();\n\
    \  val invoke_" ^ name ^ " = Thm.invoke_oracle_i thy (Sign.full_name thy name);\n\
    \in\n\
    \  fun " ^ name ^ " thy x = invoke_" ^ name ^ " (thy, Arg x);\n\
    \end;\n";
  in Context.use_mltext_theory txt false end;



(*** the ProtoPure theory ***)

val aT = TFree ("'a", []);
val A = Free ("A", propT);

val proto_pure =
  Context.pre_pure_thy
  |> Compress.init_data
  |> Sign.init_data
  |> Theory.init_data
  |> Proofterm.init_data
  |> TheoremsData.init
  |> Theory.add_types
   [("fun", 2, NoSyn),
    ("prop", 0, NoSyn),
    ("itself", 1, NoSyn),
    ("dummy", 0, NoSyn)]
  |> Theory.add_nonterminals Syntax.pure_nonterms
  |> Theory.add_syntax Syntax.pure_syntax
  |> Theory.add_syntax Syntax.pure_appl_syntax
  |> Theory.add_modesyntax (Symbol.xsymbolsN, true) Syntax.pure_xsym_syntax
  |> Theory.add_syntax
   [("==>", "prop => prop => prop", Delimfix "op ==>"),
    (Term.dummy_patternN, "aprop", Delimfix "'_")]
  |> Theory.add_consts
   [("==", "'a => 'a => prop", InfixrName ("==", 2)),
    ("==>", "prop => prop => prop", Mixfix ("(_/ ==> _)", [2, 1], 1)),
    ("all", "('a => prop) => prop", Binder ("!!", 0, 0)),
    ("Goal", "prop => prop", NoSyn),
    ("TYPE", "'a itself", NoSyn),
    (Term.dummy_patternN, "'a", Delimfix "'_")]
  |> Theory.add_finals_i false
    [Const ("==", [aT, aT] ---> propT),
     Const ("==>", [propT, propT] ---> propT),
     Const ("all", (aT --> propT) --> propT),
     Const ("TYPE", a_itselfT),
     Const (Term.dummy_patternN, aT)]
  |> Theory.add_modesyntax ("", false)
    (Syntax.pure_syntax_output @ Syntax.pure_appl_syntax)
  |> Theory.add_trfuns Syntax.pure_trfuns
  |> Theory.add_trfunsT Syntax.pure_trfunsT
  |> Sign.local_path
  |> (#1 oo (add_defs_i false o map Thm.no_attributes))
   [("Goal_def", Logic.mk_equals (Logic.mk_goal A, A))]
  |> (#1 o add_thmss [(("nothing", []), [])])
  |> Theory.add_axioms_i Proofterm.equality_axms
  |> Theory.end_theory;

structure ProtoPure =
struct
  val thy = proto_pure;
  val Goal_def = get_axiom thy "Goal_def";
end;

end;

structure BasicPureThy: BASIC_PURE_THY = PureThy;
open BasicPureThy;
