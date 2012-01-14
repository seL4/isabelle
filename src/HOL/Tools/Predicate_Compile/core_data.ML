(*  Title:      HOL/Tools/Predicate_Compile/core_data.ML
    Author:     Lukas Bulwahn, TU Muenchen

Data of the predicate compiler core.
*)

signature CORE_DATA =
sig
  type mode = Predicate_Compile_Aux.mode
  type compilation = Predicate_Compile_Aux.compilation
  type compilation_funs = Predicate_Compile_Aux.compilation_funs
  
  datatype predfun_data = PredfunData of {
    definition : thm,
    intro : thm,
    elim : thm,
    neg_intro : thm option
  };

  datatype pred_data = PredData of {
    intros : (string option * thm) list,
    elim : thm option,
    preprocessed : bool,
    function_names : (compilation * (mode * string) list) list,
    predfun_data : (mode * predfun_data) list,
    needs_random : mode list
  };

  structure PredData : THEORY_DATA
  
  (* queries *)
  val defined_functions : compilation -> Proof.context -> string -> bool
  val is_registered : Proof.context -> string -> bool
  val function_name_of : compilation -> Proof.context -> string -> mode -> string
  val the_elim_of : Proof.context -> string -> thm
  val has_elim : Proof.context -> string -> bool
  
  val needs_random : Proof.context -> string -> mode -> bool
  
  val predfun_intro_of : Proof.context -> string -> mode -> thm
  val predfun_neg_intro_of : Proof.context -> string -> mode -> thm option
  val predfun_elim_of : Proof.context -> string -> mode -> thm
  val predfun_definition_of : Proof.context -> string -> mode -> thm
  
  val all_preds_of : Proof.context -> string list
  val modes_of: compilation -> Proof.context -> string -> mode list
  val all_modes_of : compilation -> Proof.context -> (string * mode list) list
  val all_random_modes_of : Proof.context -> (string * mode list) list
  val intros_of : Proof.context -> string -> thm list
  val names_of : Proof.context -> string -> string option list

  val intros_graph_of : Proof.context -> thm list Graph.T
  
  (* updaters *)
  
  val register_predicate : (string * thm list * thm) -> theory -> theory
  val register_intros : string * thm list -> theory -> theory

  (* FIXME: naming of function is strange *)
  val defined_function_of : compilation -> string -> theory -> theory
  val add_intro : string option * thm -> theory -> theory
  val set_elim : thm -> theory -> theory
  val set_function_name : compilation -> string -> mode -> string -> theory -> theory
  val add_predfun_data : string -> mode -> thm * ((thm * thm) * thm option) -> theory -> theory
  val set_needs_random : string -> mode list -> theory -> theory
  (* sophisticated updaters *)
  val extend_intro_graph : string list -> theory -> theory
  val preprocess_intros : string -> theory -> theory
  
  (* alternative function definitions *)
  val register_alternative_function : string -> mode -> string -> theory -> theory
  val alternative_compilation_of_global : theory -> string -> mode ->
    (compilation_funs -> typ -> term) option
  val alternative_compilation_of : Proof.context -> string -> mode ->
    (compilation_funs -> typ -> term) option
  val functional_compilation : string -> mode -> compilation_funs -> typ -> term
  val force_modes_and_functions : string -> (mode * (string * bool)) list -> theory -> theory
  val force_modes_and_compilations : string ->
    (mode * ((compilation_funs -> typ -> term) * bool)) list -> theory -> theory

end;

structure Core_Data : CORE_DATA =
struct

open Predicate_Compile_Aux;

(* book-keeping *)

datatype predfun_data = PredfunData of {
  definition : thm,
  intro : thm,
  elim : thm,
  neg_intro : thm option
};

fun rep_predfun_data (PredfunData data) = data;

fun mk_predfun_data (definition, ((intro, elim), neg_intro)) =
  PredfunData {definition = definition, intro = intro, elim = elim, neg_intro = neg_intro}

datatype pred_data = PredData of {
  intros : (string option * thm) list,
  elim : thm option,
  preprocessed : bool,
  function_names : (compilation * (mode * string) list) list,
  predfun_data : (mode * predfun_data) list,
  needs_random : mode list
};

fun rep_pred_data (PredData data) = data;

fun mk_pred_data (((intros, elim), preprocessed), (function_names, (predfun_data, needs_random))) =
  PredData {intros = intros, elim = elim, preprocessed = preprocessed,
    function_names = function_names, predfun_data = predfun_data, needs_random = needs_random}

fun map_pred_data f (PredData {intros, elim, preprocessed, function_names, predfun_data, needs_random}) =
  mk_pred_data (f (((intros, elim), preprocessed), (function_names, (predfun_data, needs_random))))

fun eq_option eq (NONE, NONE) = true
  | eq_option eq (SOME x, SOME y) = eq (x, y)
  | eq_option eq _ = false

fun eq_pred_data (PredData d1, PredData d2) = 
  eq_list (eq_pair (op =) Thm.eq_thm) (#intros d1, #intros d2) andalso
  eq_option Thm.eq_thm (#elim d1, #elim d2)

structure PredData = Theory_Data
(
  type T = pred_data Graph.T;
  val empty = Graph.empty;
  val extend = I;
  val merge = Graph.merge eq_pred_data;
);

(* queries *)

fun lookup_pred_data ctxt name =
  Option.map rep_pred_data (try (Graph.get_node (PredData.get (Proof_Context.theory_of ctxt))) name)

fun the_pred_data ctxt name = case lookup_pred_data ctxt name
 of NONE => error ("No such predicate " ^ quote name)  
  | SOME data => data;

val is_registered = is_some oo lookup_pred_data

val all_preds_of = Graph.keys o PredData.get o Proof_Context.theory_of

val intros_of = map snd o #intros oo the_pred_data

val names_of = map fst o #intros oo the_pred_data

fun the_elim_of ctxt name = case #elim (the_pred_data ctxt name)
 of NONE => error ("No elimination rule for predicate " ^ quote name)
  | SOME thm => thm
  
val has_elim = is_some o #elim oo the_pred_data

fun function_names_of compilation ctxt name =
  case AList.lookup (op =) (#function_names (the_pred_data ctxt name)) compilation of
    NONE => error ("No " ^ string_of_compilation compilation
      ^ " functions defined for predicate " ^ quote name)
  | SOME fun_names => fun_names

fun function_name_of compilation ctxt name mode =
  case AList.lookup eq_mode
    (function_names_of compilation ctxt name) mode of
    NONE => error ("No " ^ string_of_compilation compilation
      ^ " function defined for mode " ^ string_of_mode mode ^ " of predicate " ^ quote name)
  | SOME function_name => function_name

fun modes_of compilation ctxt name = map fst (function_names_of compilation ctxt name)

fun all_modes_of compilation ctxt =
  map_filter (fn name => Option.map (pair name) (try (modes_of compilation ctxt) name))
    (all_preds_of ctxt)

val all_random_modes_of = all_modes_of Random

fun defined_functions compilation ctxt name = case lookup_pred_data ctxt name of
    NONE => false
  | SOME data => AList.defined (op =) (#function_names data) compilation

fun needs_random ctxt s m =
  member (op =) (#needs_random (the_pred_data ctxt s)) m

fun lookup_predfun_data ctxt name mode =
  Option.map rep_predfun_data
    (AList.lookup eq_mode (#predfun_data (the_pred_data ctxt name)) mode)

fun the_predfun_data ctxt name mode =
  case lookup_predfun_data ctxt name mode of
    NONE => error ("No function defined for mode " ^ string_of_mode mode ^
      " of predicate " ^ name)
  | SOME data => data;

val predfun_definition_of = #definition ooo the_predfun_data

val predfun_intro_of = #intro ooo the_predfun_data

val predfun_elim_of = #elim ooo the_predfun_data

val predfun_neg_intro_of = #neg_intro ooo the_predfun_data

val intros_graph_of =
  Graph.map (K (map snd o #intros o rep_pred_data)) o PredData.get o Proof_Context.theory_of

fun prove_casesrule ctxt (pred, (pre_cases_rule, nparams)) cases_rule =
  let
    val thy = Proof_Context.theory_of ctxt
    val nargs = length (binder_types (fastype_of pred))
    fun PEEK f dependent_tactic st = dependent_tactic (f st) st
    fun meta_eq_of th = th RS @{thm eq_reflection}
    val tuple_rew_rules = map meta_eq_of [@{thm fst_conv}, @{thm snd_conv}, @{thm Pair_eq}]
    fun instantiate i n {context = ctxt, params = p, prems = prems,
      asms = a, concl = cl, schematics = s}  =
      let
        fun term_pair_of (ix, (ty,t)) = (Var (ix,ty), t)
        fun inst_of_matches tts = fold (Pattern.match thy) tts (Vartab.empty, Vartab.empty)
          |> snd |> Vartab.dest |> map (pairself (cterm_of thy) o term_pair_of)
        val (cases, (eqs, prems)) = apsnd (chop (nargs - nparams)) (chop n prems)
        val case_th = Raw_Simplifier.simplify true
          (@{thm Predicate.eq_is_eq} :: map meta_eq_of eqs) (nth cases (i - 1))
        val prems' = maps (dest_conjunct_prem o Raw_Simplifier.simplify true tuple_rew_rules) prems
        val pats = map (swap o HOLogic.dest_eq o HOLogic.dest_Trueprop) (take nargs (prems_of case_th))
        val case_th' = Thm.instantiate ([], inst_of_matches pats) case_th
          OF (replicate nargs @{thm refl})
        val thesis =
          Thm.instantiate ([], inst_of_matches (prems_of case_th' ~~ map prop_of prems')) case_th'
            OF prems'
      in
        (rtac thesis 1)
      end
    val tac =
      etac pre_cases_rule 1
      THEN
      (PEEK nprems_of
        (fn n =>
          ALLGOALS (fn i =>
            Simplifier.rewrite_goal_tac [@{thm split_paired_all}] i
            THEN (SUBPROOF (instantiate i n) ctxt i))))
  in
    Goal.prove ctxt (Term.add_free_names cases_rule []) [] cases_rule (fn _ => tac)
  end

(* updaters *)

(* fetching introduction rules or registering introduction rules *)

val no_compilation = ([], ([], []))

fun fetch_pred_data ctxt name =
  case try (Inductive.the_inductive ctxt) name of
    SOME (info as (_, result)) => 
      let
        fun is_intro_of intro =
          let
            val (const, _) = strip_comb (HOLogic.dest_Trueprop (concl_of intro))
          in (fst (dest_Const const) = name) end;
        val thy = Proof_Context.theory_of ctxt
        val intros = map (preprocess_intro thy) (filter is_intro_of (#intrs result))
        val index = find_index (fn s => s = name) (#names (fst info))
        val pre_elim = nth (#elims result) index
        val pred = nth (#preds result) index
        val elim_t = mk_casesrule ctxt pred intros
        val nparams = length (Inductive.params_of (#raw_induct result))
        val elim = prove_casesrule ctxt (pred, (pre_elim, nparams)) elim_t
      in
        mk_pred_data (((map (pair NONE) intros, SOME elim), true), no_compilation)
      end
  | NONE => error ("No such predicate: " ^ quote name)

fun add_predfun_data name mode data =
  let
    val add = (apsnd o apsnd o apfst) (cons (mode, mk_predfun_data data))
  in PredData.map (Graph.map_node name (map_pred_data add)) end

fun is_inductive_predicate ctxt name =
  is_some (try (Inductive.the_inductive ctxt) name)

fun depending_preds_of ctxt (key, value) =
  let
    val intros = map (Thm.prop_of o snd) ((#intros o rep_pred_data) value)
  in
    fold Term.add_const_names intros []
      |> (fn cs =>
        if member (op =) cs @{const_name "HOL.eq"} then
          insert (op =) @{const_name Predicate.eq} cs
        else cs)
      |> filter (fn c => (not (c = key)) andalso
        (is_inductive_predicate ctxt c orelse is_registered ctxt c))
  end;

fun add_intro (opt_case_name, thm) thy =
  let
    val (name, T) = dest_Const (fst (strip_intro_concl thm))
    fun cons_intro gr =
     case try (Graph.get_node gr) name of
       SOME pred_data => Graph.map_node name (map_pred_data
         (apfst (apfst (apfst (fn intros => intros @ [(opt_case_name, thm)]))))) gr
     | NONE => Graph.new_node (name, mk_pred_data ((([(opt_case_name, thm)], NONE), false), no_compilation)) gr
  in PredData.map cons_intro thy end

fun set_elim thm =
  let
    val (name, _) = dest_Const (fst 
      (strip_comb (HOLogic.dest_Trueprop (hd (prems_of thm)))))
  in PredData.map (Graph.map_node name (map_pred_data (apfst (apfst (apsnd (K (SOME thm))))))) end

fun register_predicate (constname, intros, elim) thy =
  let
    val named_intros = map (pair NONE) intros
  in
    if not (member (op =) (Graph.keys (PredData.get thy)) constname) then
      PredData.map
        (Graph.new_node (constname,
          mk_pred_data (((named_intros, SOME elim), false), no_compilation))) thy
    else thy
  end

fun register_intros (constname, pre_intros) thy =
  let
    val T = Sign.the_const_type thy constname
    fun constname_of_intro intr = fst (dest_Const (fst (strip_intro_concl intr)))
    val _ = if not (forall (fn intr => constname_of_intro intr = constname) pre_intros) then
      error ("register_intros: Introduction rules of different constants are used\n" ^
        "expected rules for " ^ constname ^ ", but received rules for " ^
          commas (map constname_of_intro pre_intros))
      else ()
    val pred = Const (constname, T)
    val pre_elim = 
      (Drule.export_without_context o Skip_Proof.make_thm thy)
      (mk_casesrule (Proof_Context.init_global thy) pred pre_intros)
  in register_predicate (constname, pre_intros, pre_elim) thy end

fun defined_function_of compilation pred =
  let
    val set = (apsnd o apfst) (cons (compilation, []))
  in
    PredData.map (Graph.map_node pred (map_pred_data set))
  end

fun set_function_name compilation pred mode name =
  let
    val set = (apsnd o apfst)
      (AList.map_default (op =) (compilation, [(mode, name)]) (cons (mode, name)))
  in
    PredData.map (Graph.map_node pred (map_pred_data set))
  end

fun set_needs_random name modes =
  let
    val set = (apsnd o apsnd o apsnd) (K modes)
  in
    PredData.map (Graph.map_node name (map_pred_data set))
  end  

fun extend' value_of edges_of key (G, visited) =
  let
    val (G', v) = case try (Graph.get_node G) key of
        SOME v => (G, v)
      | NONE => (Graph.new_node (key, value_of key) G, value_of key)
    val (G'', visited') = fold (extend' value_of edges_of)
      (subtract (op =) visited (edges_of (key, v)))
      (G', key :: visited)
  in
    (fold (Graph.add_edge o (pair key)) (edges_of (key, v)) G'', visited')
  end;

fun extend value_of edges_of key G = fst (extend' value_of edges_of key (G, [])) 

fun extend_intro_graph names thy =
  let
    val ctxt = Proof_Context.init_global thy
  in
    PredData.map (fold (extend (fetch_pred_data ctxt) (depending_preds_of ctxt)) names) thy
  end

fun preprocess_intros name thy =
  PredData.map (Graph.map_node name (map_pred_data (apfst (fn (rules, preprocessed) =>
    if preprocessed then (rules, preprocessed)
    else
      let
        val (named_intros, SOME elim) = rules
        val named_intros' = map (apsnd (preprocess_intro thy)) named_intros
        val pred = Const (name, Sign.the_const_type thy name)
        val ctxt = Proof_Context.init_global thy
        val elim_t = mk_casesrule ctxt pred (map snd named_intros')
        val nparams = (case try (Inductive.the_inductive ctxt) name of
            SOME (_, result) => length (Inductive.params_of (#raw_induct result))
          | NONE => 0)
        val elim' = prove_casesrule ctxt (pred, (elim, 0)) elim_t
      in
        ((named_intros', SOME elim'), true)
      end))))
    thy  

(* registration of alternative function names *)

structure Alt_Compilations_Data = Theory_Data
(
  type T = (mode * (compilation_funs -> typ -> term)) list Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data : T = Symtab.merge (K true) data;
);

fun alternative_compilation_of_global thy pred_name mode =
  AList.lookup eq_mode (Symtab.lookup_list (Alt_Compilations_Data.get thy) pred_name) mode

fun alternative_compilation_of ctxt pred_name mode =
  AList.lookup eq_mode
    (Symtab.lookup_list (Alt_Compilations_Data.get (Proof_Context.theory_of ctxt)) pred_name) mode

fun force_modes_and_compilations pred_name compilations =
  let
    (* thm refl is a dummy thm *)
    val modes = map fst compilations
    val (needs_random, non_random_modes) = pairself (map fst)
      (List.partition (fn (m, (fun_name, random)) => random) compilations)
    val non_random_dummys = map (rpair "dummy") non_random_modes
    val all_dummys = map (rpair "dummy") modes
    val dummy_function_names = map (rpair all_dummys) Predicate_Compile_Aux.random_compilations
      @ map (rpair non_random_dummys) Predicate_Compile_Aux.non_random_compilations
    val alt_compilations = map (apsnd fst) compilations
  in
    PredData.map (Graph.new_node
      (pred_name, mk_pred_data ((([], SOME @{thm refl}), true), (dummy_function_names, ([], needs_random)))))
    #> Alt_Compilations_Data.map (Symtab.insert (K false) (pred_name, alt_compilations))
  end

fun functional_compilation fun_name mode compfuns T =
  let
    val (inpTs, outpTs) = split_map_modeT (fn _ => fn T => (SOME T, NONE))
      mode (binder_types T)
    val bs = map (pair "x") inpTs
    val bounds = map Bound (rev (0 upto (length bs) - 1))
    val f = Const (fun_name, inpTs ---> HOLogic.mk_tupleT outpTs)
  in fold_rev Term.abs bs (mk_single compfuns (list_comb (f, bounds))) end

fun register_alternative_function pred_name mode fun_name =
  Alt_Compilations_Data.map (Symtab.insert_list (eq_pair eq_mode (K false))
    (pred_name, (mode, functional_compilation fun_name mode)))

fun force_modes_and_functions pred_name fun_names =
  force_modes_and_compilations pred_name
    (map (fn (mode, (fun_name, random)) => (mode, (functional_compilation fun_name mode, random)))
    fun_names)

end;