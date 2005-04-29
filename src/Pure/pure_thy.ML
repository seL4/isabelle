(*  Title:      Pure/pure_thy.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
                contributions by Rafal Kolanski, NICTA

Theorem database, derived theory operations, and the ProtoPure theory.
*)

signature BASIC_PURE_THY =
sig
  type thmref
  val print_theorems: theory -> unit
  val print_theory: theory -> unit
  val get_thm: theory -> thmref -> thm
  val get_thms: theory -> thmref -> thm list
  val get_thmss: theory -> thmref list -> thm list
  val thms_of: theory -> (string * thm) list
  val thms_with_names_of: theory -> (string * thm list) list
  structure ProtoPure:
    sig
      val thy: theory
      val Goal_def: thm
    end
end;

signature PURE_THY =
sig
  include BASIC_PURE_THY
  datatype interval = FromTo of int * int | From of int | Single of int
  val get_thm_closure: theory -> thmref -> thm
  val get_thms_closure: theory -> thmref -> thm list
  val single_thm: string -> thm list -> thm
  val select_thm: thmref -> thm list -> thm list
  val cond_extern_thm_sg: Sign.sg -> string -> xstring
  val thms_containing: theory -> string list * string list -> (string * thm list) list
  val find_theorems: Sign.sg -> (string * thm list) list -> string list -> (string * thm list) list 
  val thms_containing_consts: theory -> string list -> (string * thm) list
  val find_matching_thms: (thm -> thm list) * (term -> term)
        -> theory -> term -> (string * thm) list
  val find_intros: theory -> term -> (string * thm) list
  val find_intros_goal : theory -> thm -> int -> (string * thm) list
  val find_elims : theory -> term -> (string * thm) list
  val hide_thms: bool -> string list -> theory -> theory
  val store_thm: (bstring * thm) * theory attribute list -> theory -> theory * thm
  val smart_store_thms: (bstring * thm list) -> thm list
  val smart_store_thms_open: (bstring * thm list) -> thm list
  val forall_elim_var: int -> thm -> thm
  val forall_elim_vars: int -> thm -> thm
  val add_thms: ((bstring * thm) * theory attribute list) list -> theory -> theory * thm list
  val add_thmss: ((bstring * thm list) * theory attribute list) list -> theory
    -> theory * thm list list
  val note_thmss:
    theory attribute -> ((bstring * theory attribute list) *
    (thmref * theory attribute list) list) list -> theory ->
    theory * (bstring * thm list) list
  val note_thmss_i:
    theory attribute -> ((bstring * theory attribute list) *
    (thm list * theory attribute list) list) list -> theory ->
    theory * (bstring * thm list) list
  val note_thmss_accesses:
    (string -> string list) ->
    theory attribute -> ((bstring * theory attribute list) *
    (thmref * theory attribute list) list) list -> theory ->
    theory * (bstring * thm list) list
  val note_thmss_accesses_i:
    (string -> string list) ->
    theory attribute -> ((bstring * theory attribute list) *
    (thm list * theory attribute list) list) list -> theory ->
    theory * (bstring * thm list) list
  val add_axioms: ((bstring * string) * theory attribute list) list -> theory -> theory * thm list
  val add_axioms_i: ((bstring * term) * theory attribute list) list -> theory -> theory * thm list
  val add_axiomss: ((bstring * string list) * theory attribute list) list -> theory
    -> theory * thm list list
  val add_axiomss_i: ((bstring * term list) * theory attribute list) list -> theory
    -> theory * thm list list
  val add_defs: bool -> ((bstring * string) * theory attribute list) list
    -> theory -> theory * thm list
  val add_defs_i: bool -> ((bstring * term) * theory attribute list) list
    -> theory -> theory * thm list
  val add_defss: bool -> ((bstring * string list) * theory attribute list) list
    -> theory -> theory * thm list list
  val add_defss_i: bool -> ((bstring * term list) * theory attribute list) list
    -> theory -> theory * thm list list
  val get_name: theory -> string
  val put_name: string -> theory -> theory
  val global_path: theory -> theory
  val local_path: theory -> theory
  val begin_theory: string -> theory list -> theory
  val end_theory: theory -> theory
  val checkpoint: theory -> theory
  val add_typedecls: (bstring * string list * mixfix) list -> theory -> theory
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
      index: FactIndex.T} ref;

  fun mk_empty _ =
    ref {space = NameSpace.empty, thms_tab = Symtab.empty, index = FactIndex.empty}: T;

  val empty = mk_empty ();
  fun copy (ref x) = ref x;
  val prep_ext = mk_empty;
  val merge = mk_empty;

  fun pretty sg (ref {space, thms_tab, index = _}) =
    let
      val prt_thm = Display.pretty_thm_sg sg;
      fun prt_thms (name, [th]) =
            Pretty.block [Pretty.str (name ^ ":"), Pretty.brk 1, prt_thm th]
        | prt_thms (name, ths) = Pretty.big_list (name ^ ":") (map prt_thm ths);

      val thmss = NameSpace.cond_extern_table space thms_tab;
    in Pretty.big_list "theorems:" (map prt_thms thmss) end;

  fun print sg data = Pretty.writeln (pretty sg data);
end;

structure TheoremsData = TheoryDataFun(TheoremsDataArgs);
val get_theorems_sg = TheoremsData.get_sg;
val get_theorems = TheoremsData.get;

val cond_extern_thm_sg = NameSpace.cond_extern o #space o ! o get_theorems_sg;


(* print theory *)

val print_theorems = TheoremsData.print;

fun print_theory thy =
  Display.pretty_full_theory thy @
  [TheoremsDataArgs.pretty (Theory.sign_of thy) (get_theorems thy)]
  |> Pretty.chunks |> Pretty.writeln;



(** retrieve theorems **)

fun the_thms _ (SOME thms) = thms
  | the_thms name NONE = error ("Unknown theorem(s) " ^ quote name);

fun single_thm _ [thm] = thm
  | single_thm name _ = error ("Single theorem expected " ^ quote name);


(* selections *)

datatype interval =
  FromTo of int * int |
  From of int |
  Single of int;

type thmref = xstring * interval list option;

local

fun interval _ (FromTo (i, j)) = i upto j
  | interval n (From i) = i upto n
  | interval _ (Single i) = [i];

fun select name thms n i =
  if i < 1 orelse i > n then
    error ("Bad subscript " ^ string_of_int i ^ " for " ^
      quote name ^ " (length " ^ string_of_int n ^ ")")
  else List.nth (thms, i - 1);

in

fun select_thm (_, NONE) thms = thms
  | select_thm (name, SOME is) thms =
      let val n = length thms
      in map (select name thms n) (List.concat (map (interval n) is)) end;

end;


(* get_thm(s)_closure -- statically scoped versions *)

(*beware of proper order of evaluation!*)

fun lookup_thms thy =
  let
    val sg_ref = Sign.self_ref (Theory.sign_of thy);
    val ref {space, thms_tab, ...} = get_theorems thy;
  in
    fn name =>
      Option.map (map (Thm.transfer_sg (Sign.deref sg_ref)))        (*semi-dynamic identity*)
      (Symtab.lookup (thms_tab, NameSpace.intern space name))   (*static content*)
  end;

fun get_thms_closure thy =
  let val closures = map lookup_thms (thy :: Theory.ancestors_of thy)
  in fn namei as (name, _) => select_thm namei
    (the_thms name (get_first (fn f => f name) closures))
  end;

fun get_thm_closure thy =
  let val get = get_thms_closure thy
  in fn namei as (name, _) => single_thm name (get namei) end;


(* get_thm etc. *)

fun get_thms theory (namei as (name, _)) =
  get_first (fn thy => lookup_thms thy name) (theory :: Theory.ancestors_of theory)
  |> the_thms name |> select_thm namei |> map (Thm.transfer theory);

fun get_thmss thy names = List.concat (map (get_thms thy) names);
fun get_thm thy (namei as (name, _)) = single_thm name (get_thms thy namei);


(* thms_of *)

fun thms_of thy =
  let val ref {thms_tab, ...} = get_theorems thy in
    map (fn th => (Thm.name_of_thm th, th)) (List.concat (map snd (Symtab.dest thms_tab)))
  end;

(* thms_with_names_of - theorems in this theory and their names *)
fun thms_with_names_of thy = 
  TheoremsData.get thy |> ! |> #index |> FactIndex.find ([],[]);
  (* looking for nothing in a FactIndex finds everything, i.e. all theorems *)

(* thms_containing *)

fun thms_containing thy idx =
  let
    fun valid (name, ths) =
      (case try (transform_error (get_thms thy)) (name, NONE) of
        NONE => false
      | SOME ths' => Library.equal_lists Thm.eq_thm (ths, ths'));
  in
    (thy :: Theory.ancestors_of thy)
    |> map (gen_distinct eq_fst o List.filter valid o FactIndex.find idx o #index o ! o get_theorems)
    |> List.concat
  end;

fun thms_containing_consts thy consts =
  thms_containing thy (consts, []) |> map #2 |> List.concat
  |> map (fn th => (Thm.name_of_thm th, th))

(* find_theorems - finding theorems by matching on a series of subterms  *)

(* Takes a string pattern, such as "(_::nat) + (_ + _)" and converts it into
    a term with all free variables made schematic *)
fun str_pattern_to_term sg str_pattern =
  let
    (* pattern as term with dummies as Consts *)
    val term_pattern = read_cterm sg (str_pattern, TypeInfer.logicT) 
                       |> Thm.term_of; 
    (* with dummies as Vars *)
    val v_pattern = #2 (Term.replace_dummy_patterns (1,term_pattern));
  in
    (* with schematic vars *)
    #1 (Type.varify (v_pattern, []))
  end;

(* find all thms such that for each returned thm, all given 
    propositions are subterms of it *)
fun thms_matching_patterns tsign (pat::pats) thms = 
    let 
        fun match_single pattern thm = 
            Pattern.matches_subterm tsign (pat, Thm.prop_of thm);
    in
        thms_matching_patterns tsign pats
            (List.filter (match_single pat) thms)
    end
  | thms_matching_patterns _ _ thms = thms; 

(* facts are pairs of theorem name and a list of its thms *)
fun find_theorems sg facts str_patterns =
  let
    val typesg = Sign.tsig_of sg;
    
    (* the patterns we will be looking for *)
    val patterns = map (str_pattern_to_term sg) str_patterns;

    (* we are interested in theorems which have one or more thms for which
       all patterns are subterms *)
    fun matches (_, thms) = 
        (not o null o (thms_matching_patterns typesg patterns)) thms
  in
    List.filter matches facts
  end;

(* intro/elim theorems *)

(* intro: given a goal state, find a suitable intro rule for some subgoal *)
(* elim: given a theorem thm,
         find a theorem whose major premise eliminates the conclusion of thm *)

fun top_const t = (case head_of t of Const (c, _) => SOME c | _ => NONE);

(* This is a hack to remove the Trueprop constant that most logics use *)
fun rem_top (_ $ t) = t
  | rem_top _ = Bound 0 (* does not match anything *)

(*returns all those named_thms whose subterm extracted by extract can be
  instantiated to obj; the list is sorted according to the number of premises
  and the size of the required substitution.*)
fun select_match(c,obj, signobj, named_thms, (extract_thms,extract_term)) =
  let val tsig = Sign.tsig_of signobj
      fun matches prop =
        let val pat = extract_term prop
        in case head_of pat of
             Const(d,_) => c=d andalso Pattern.matches tsig (pat,obj)
           | _ => false
        end

      fun substsize prop =
            let val pat = extract_term prop
                val (_,subst) = Pattern.match tsig (pat,obj)
            in Vartab.foldl (op + o apsnd (size_of_term o snd o snd)) (0, subst)
            end

      fun thm_ord ((p0,s0,_),(p1,s1,_)) =
            prod_ord (int_ord o pairself (fn 0 => 0 | x => 1)) int_ord ((p0,s0),(p1,s1));

      fun select((p as (_,thm))::named_thms, sels) =
            let
              fun sel(thm::thms,sels) =     
                    let val {prop, ...} = rep_thm thm
                    in if matches prop
                       then (nprems_of thm,substsize prop,p)::sels
                       else sel(thms,sels)
                    end
                | sel([],sels) = sels
             val {sign, ...} = rep_thm thm
           in select(named_thms,if Sign.subsig(sign, signobj)
                                then sel(extract_thms thm,sels)
                                else sels)
           end
        | select([],sels) = sels

  in map (fn (_,_,t) => t) (sort thm_ord (select(named_thms, []))) end;

fun find_matching_thms extract thy prop =
  (case top_const prop of NONE => []
   | SOME c => let val thms = thms_containing_consts thy [c]
               in select_match(c,prop,Theory.sign_of thy,thms,extract) end)

val find_intros =
  find_matching_thms (single, rem_top o Logic.strip_imp_concl)

fun find_intros_goal thy st i =
  find_intros thy (rem_top(Logic.concl_of_goal (prop_of st) i));

val find_elims = find_matching_thms
  (fn thm => if Thm.no_prems thm then [] else [thm],
   rem_top o hd o Logic.strip_imp_prems)


(** store theorems **)                    (*DESTRUCTIVE*)

(* hiding -- affects current theory node only! *)

fun hide_thms fully names thy =
  let
    val r as ref {space, thms_tab, index} = get_theorems thy;
    val space' = NameSpace.hide fully (space, names);
  in r := {space = space', thms_tab = thms_tab, index = index}; thy end;


(* naming *)

fun gen_names j len name =
  map (fn i => name ^ "_" ^ string_of_int i) (j+1 upto j+len);

fun name_multi name xs = gen_names 0 (length xs) name ~~ xs;

fun name_thm pre (p as (_, thm)) =
  if Thm.name_of_thm thm <> "" andalso pre then thm else Thm.name_thm p;

fun name_thms pre name [x] = [name_thm pre (name, x)]
  | name_thms pre name xs = map (name_thm pre) (name_multi name xs);

fun name_thmss name xs = (case filter_out (null o fst) xs of
    [([x], z)] => [([name_thm true (name, x)], z)]
  | _ => snd (foldl_map (fn (i, (ys, z)) => (i + length ys,
  (map (name_thm true) (gen_names i (length ys) name ~~ ys), z))) (0, xs)));


(* enter_thms *)

fun warn_overwrite name = warning ("Replaced old copy of theorems " ^ quote name);
fun warn_same name = warning ("Theorem database already contains a copy of " ^ quote name);

fun gen_enter_thms _ _ _ _ _ app_att thy ("", thms) = app_att (thy, thms)
  | gen_enter_thms full acc sg pre_name post_name app_att thy (bname, thms) =
      let
        val name = full sg bname;
        val (thy', thms') = app_att (thy, pre_name name thms);
        val named_thms = post_name name thms';

        val r as ref {space, thms_tab, index} = get_theorems_sg sg;
        val space' = NameSpace.extend' acc (space, [name]);
        val thms_tab' = Symtab.update ((name, named_thms), thms_tab);
        val index' = FactIndex.add (K false) (index, (name, named_thms));
      in
        (case Symtab.lookup (thms_tab, name) of
          NONE => ()
        | SOME thms' =>
            if Library.equal_lists Thm.eq_thm (thms', named_thms) then warn_same name
            else warn_overwrite name);
        r := {space = space', thms_tab = thms_tab', index = index'};
        (thy', named_thms)
      end;

fun enter_thms sg = gen_enter_thms Sign.full_name NameSpace.accesses sg;

(* add_thms(s) *)

fun add_thms_atts pre_name ((bname, thms), atts) thy =
  enter_thms (Theory.sign_of thy) pre_name (name_thms false)
    (Thm.applys_attributes o rpair atts) thy (bname, thms);

fun gen_add_thmss pre_name args theory =
  foldl_map (fn (thy, arg) => add_thms_atts pre_name arg thy) (theory, args);

fun gen_add_thms pre_name args =
  apsnd (map hd) o gen_add_thmss pre_name (map (apfst (apsnd single)) args);

val add_thmss = gen_add_thmss (name_thms true);
val add_thms = gen_add_thms (name_thms true);


(* note_thmss(_i) *)

local

fun gen_note_thss enter get kind_att (thy, ((bname, more_atts), ths_atts)) =
  let
    fun app (x, (ths, atts)) = Thm.applys_attributes ((x, ths), atts);
    val (thy', thms) = enter (Theory.sign_of thy)
      name_thmss (name_thms false) (apsnd List.concat o foldl_map app) thy
      (bname, map (fn (ths, atts) => (get thy ths, atts @ more_atts @ [kind_att])) ths_atts);
  in (thy', (bname, thms)) end;

fun gen_note_thmss enter get kind_att args thy =
  foldl_map (gen_note_thss enter get kind_att) (thy, args);

in

(* if path is set, only permit unqualified names *)

val note_thmss = gen_note_thmss enter_thms get_thms;
val note_thmss_i = gen_note_thmss enter_thms (K I);

(* always permit qualified names,
   clients may specify non-standard access policy *)

fun note_thmss_accesses acc =
  gen_note_thmss (gen_enter_thms Sign.full_name' acc) get_thms;
fun note_thmss_accesses_i acc =
  gen_note_thmss (gen_enter_thms Sign.full_name' acc) (K I);

end;


(* store_thm *)

fun store_thm ((bname, thm), atts) thy =
  let val (thy', [th']) = add_thms_atts (name_thms true) ((bname, [thm]), atts) thy
  in (thy', th') end;


(* smart_store_thms *)

fun gen_smart_store_thms _ (name, []) =
      error ("Cannot store empty list of theorems: " ^ quote name)
  | gen_smart_store_thms name_thm (name, [thm]) =
      snd (enter_thms (Thm.sign_of_thm thm) (name_thm true) (name_thm false)
        I () (name, [thm]))
  | gen_smart_store_thms name_thm (name, thms) =
      let
        val merge_sg = Sign.merge_refs o apsnd (Sign.self_ref o Thm.sign_of_thm);
        val sg_ref = Library.foldl merge_sg (Sign.self_ref (Thm.sign_of_thm (hd thms)), tl thms);
      in snd (enter_thms (Sign.deref sg_ref) (name_thm true) (name_thm false)
        I () (name, thms))
      end;

val smart_store_thms = gen_smart_store_thms name_thms;
val smart_store_thms_open = gen_smart_store_thms (K (K I));


(* forall_elim_vars (belongs to drule.ML) *)

(*Replace outermost quantified variable by Var of given index.*)
fun forall_elim_var i th =
    let val {prop,sign,...} = rep_thm th
    in case prop of
        Const ("all", _) $ Abs (a, T, _) =>
          let val used = map (fst o fst)
            (List.filter (equal i o snd o fst) (Term.add_vars ([], prop)))
          in forall_elim (cterm_of sign (Var ((variant used a, i), T))) th end
      | _ => raise THM ("forall_elim_var", i, [th])
    end;

(*Repeat forall_elim_var until all outer quantifiers are removed*)
fun forall_elim_vars i th =
    forall_elim_vars i (forall_elim_var i th)
        handle THM _ => th;


(* store axioms as theorems *)

local
  fun get_axs thy named_axs =
    map (forall_elim_vars 0 o Thm.get_axiom thy o fst) named_axs;

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

fun end_theory thy =
  thy
  |> Theory.add_name (get_name thy);

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
  in thy |> Theory.add_types (map type_of decls) end;



(*** the ProtoPure theory ***)


(*It might make sense to restrict the polymorphism of the constant "==" to
  sort logic, instead of the universal sort, {}.  Unfortunately, this change
  causes HOL/Import/shuffler.ML to fail.*)

val proto_pure =
  Theory.pre_pure
  |> Library.apply [TheoremsData.init, TheoryManagementData.init, Proofterm.init]
  |> put_name "ProtoPure"
  |> global_path
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
   [("==>", "[prop, prop] => prop", Delimfix "op ==>"),
    (Term.dummy_patternN, "aprop", Delimfix "'_")]
  |> Theory.add_consts
   [("==", "['a, 'a] => prop", InfixrName ("==", 2)),
    ("==>", "[prop, prop] => prop", Mixfix ("(_/ ==> _)", [2, 1], 1)),
    ("all", "('a => prop) => prop", Binder ("!!", 0, 0)),
    ("Goal", "prop => prop", NoSyn),
    ("TYPE", "'a itself", NoSyn),
    (Term.dummy_patternN, "'a", Delimfix "'_")]
  |> Theory.add_finals_i false
    [Const("==", [TFree ("'a", []), TFree ("'a", [])] ---> propT),
     Const("==>", [propT, propT] ---> propT),
     Const("all", (TFree("'a", []) --> propT) --> propT),
     Const("TYPE", a_itselfT)]
  |> Theory.add_modesyntax ("", false)
    (Syntax.pure_syntax_output @ Syntax.pure_appl_syntax)
  |> Theory.add_trfuns Syntax.pure_trfuns
  |> Theory.add_trfunsT Syntax.pure_trfunsT
  |> local_path
  |> (#1 oo (add_defs_i false o map Thm.no_attributes))
   [("Goal_def", let val A = Free ("A", propT) in Logic.mk_equals (Logic.mk_goal A, A) end)]
  |> (#1 o add_thmss [(("nothing", []), [])])
  |> Theory.add_axioms_i Proofterm.equality_axms
  |> end_theory;

structure ProtoPure =
struct
  val thy = proto_pure;
  val Goal_def = get_axiom thy "Goal_def";
end;


end;


structure BasicPureThy: BASIC_PURE_THY = PureThy;
open BasicPureThy;

