(* Author: Lukas Bulwahn, TU Muenchen

(Prototype of) A compiler from predicates specified by intro/elim rules
to equations.
*)

signature PREDICATE_COMPILE_CORE =
sig
  val setup: theory -> theory
  val code_pred: Predicate_Compile_Aux.options -> string -> Proof.context -> Proof.state
  val code_pred_cmd: Predicate_Compile_Aux.options -> string -> Proof.context -> Proof.state
  type smode = (int * int list option) list
  type mode = smode option list * smode
  datatype tmode = Mode of mode * smode * tmode option list;
  (*val add_equations_of: bool -> string list -> theory -> theory *)
  val register_predicate : (thm list * thm * int) -> theory -> theory
  val register_intros : thm list -> theory -> theory
  val is_registered : theory -> string -> bool
 (* val fetch_pred_data : theory -> string -> (thm list * thm * int)  *)
  val predfun_intro_of: theory -> string -> mode -> thm
  val predfun_elim_of: theory -> string -> mode -> thm
  val strip_intro_concl: int -> term -> term * (term list * term list)
  val predfun_name_of: theory -> string -> mode -> string
  val all_preds_of : theory -> string list
  val modes_of: theory -> string -> mode list
  val sizelim_modes_of: theory -> string -> mode list
  val sizelim_function_name_of : theory -> string -> mode -> string
  val generator_modes_of: theory -> string -> mode list
  val generator_name_of : theory -> string -> mode -> string
  val string_of_mode : mode -> string
  val intros_of: theory -> string -> thm list
  val nparams_of: theory -> string -> int
  val add_intro: thm -> theory -> theory
  val set_elim: thm -> theory -> theory
  val set_nparams : string -> int -> theory -> theory
  val print_stored_rules: theory -> unit
  val print_all_modes: theory -> unit
  val do_proofs: bool Unsynchronized.ref
  val mk_casesrule : Proof.context -> int -> thm list -> term
  val analyze_compr: theory -> term -> term
  val eval_ref: (unit -> term Predicate.pred) option Unsynchronized.ref
  val add_equations : Predicate_Compile_Aux.options -> string list -> theory -> theory
  val code_pred_intros_attrib : attribute
  (* used by Quickcheck_Generator *) 
  (*val funT_of : mode -> typ -> typ
  val mk_if_pred : term -> term
  val mk_Eval : term * term -> term*)
  val mk_tupleT : typ list -> typ
(*  val mk_predT :  typ -> typ *)
  (* temporary for testing of the compilation *)
  datatype indprem = Prem of term list * term | Negprem of term list * term | Sidecond of term |
    GeneratorPrem of term list * term | Generator of (string * typ);
 (* val prepare_intrs: theory -> string list ->
    (string * typ) list * int * string list * string list * (string * mode list) list *
    (string * (term list * indprem list) list) list * (string * (int option list * int)) list*)
  datatype compilation_funs = CompilationFuns of {
    mk_predT : typ -> typ,
    dest_predT : typ -> typ,
    mk_bot : typ -> term,
    mk_single : term -> term,
    mk_bind : term * term -> term,
    mk_sup : term * term -> term,
    mk_if : term -> term,
    mk_not : term -> term,
    mk_map : typ -> typ -> term -> term -> term,
    lift_pred : term -> term
  };  
  type moded_clause = term list * (indprem * tmode) list
  type 'a pred_mode_table = (string * (mode * 'a) list) list
  val infer_modes : Predicate_Compile_Aux.options -> theory -> (string * mode list) list
    -> (string * mode list) list
    -> string list
    -> (string * (term list * indprem list) list) list
    -> (moded_clause list) pred_mode_table
  val infer_modes_with_generator : Predicate_Compile_Aux.options -> theory -> (string * mode list) list
    -> (string * mode list) list
    -> string list
    -> (string * (term list * indprem list) list) list
    -> (moded_clause list) pred_mode_table  
  (*val compile_preds : theory -> compilation_funs -> string list -> string list
    -> (string * typ) list -> (moded_clause list) pred_mode_table -> term pred_mode_table
  val rpred_create_definitions :(string * typ) list -> string * mode list
    -> theory -> theory 
  val split_smode : int list -> term list -> (term list * term list) *)
  val print_moded_clauses :
    theory -> (moded_clause list) pred_mode_table -> unit
  val print_compiled_terms : theory -> term pred_mode_table -> unit
  (*val rpred_prove_preds : theory -> term pred_mode_table -> thm pred_mode_table*)
  val pred_compfuns : compilation_funs
  val rpred_compfuns : compilation_funs
  val dest_funT : typ -> typ * typ
 (* val depending_preds_of : theory -> thm list -> string list *)
  val add_quickcheck_equations : Predicate_Compile_Aux.options -> string list -> theory -> theory
  val add_sizelim_equations : Predicate_Compile_Aux.options -> string list -> theory -> theory
  val is_inductive_predicate : theory -> string -> bool
  val terms_vs : term list -> string list
  val subsets : int -> int -> int list list
  val check_mode_clause : bool -> theory -> string list ->
    (string * mode list) list -> (string * mode list) list -> mode -> (term list * indprem list)
      -> (term list * (indprem * tmode) list) option
  val string_of_moded_prem : theory -> (indprem * tmode) -> string
  val all_modes_of : theory -> (string * mode list) list
  val all_generator_modes_of : theory -> (string * mode list) list
  val preprocess_intro : theory -> thm -> thm
  val is_constrt : theory -> term -> bool
  val is_predT : typ -> bool
  val guess_nparams : typ -> int
  val cprods_subset : 'a list list -> 'a list list
  val dest_prem : theory -> term list ->  term -> indprem
end;

structure Predicate_Compile_Core : PREDICATE_COMPILE_CORE =
struct

open Predicate_Compile_Aux;
(** auxiliary **)

(* debug stuff *)

fun tracing s = (if ! Toplevel.debug then Output.tracing s else ());

fun print_tac s = Seq.single;
fun print_tac' options s = 
  if show_proof_trace options then Tactical.print_tac s else Seq.single;

fun debug_tac msg = Seq.single; (* (fn st => (Output.tracing msg; Seq.single st)); *)

val do_proofs = Unsynchronized.ref true;

datatype assertion = Max_number_of_subgoals of int
fun assert_tac (Max_number_of_subgoals i) st =
  if (nprems_of st <= i) then Seq.single st
  else error ("assert_tac: Numbers of subgoals mismatch at goal state :"
    ^ "\n" ^ Pretty.string_of (Pretty.chunks
      (Goal_Display.pretty_goals_without_context (! Goal_Display.goals_limit) st)));

(* reference to preprocessing of InductiveSet package *)

val ind_set_codegen_preproc = (fn thy => I) (*Inductive_Set.codegen_preproc;*)

(** fundamentals **)

(* syntactic operations *)

fun mk_eq (x, xs) =
  let fun mk_eqs _ [] = []
        | mk_eqs a (b::cs) =
            HOLogic.mk_eq (Free (a, fastype_of b), b) :: mk_eqs a cs
  in mk_eqs x xs end;

fun mk_tupleT [] = HOLogic.unitT
  | mk_tupleT Ts = foldr1 HOLogic.mk_prodT Ts;

fun dest_tupleT (Type (@{type_name Product_Type.unit}, [])) = []
  | dest_tupleT (Type (@{type_name "*"}, [T1, T2])) = T1 :: (dest_tupleT T2)
  | dest_tupleT t = [t]

fun mk_tuple [] = HOLogic.unit
  | mk_tuple ts = foldr1 HOLogic.mk_prod ts;

fun dest_tuple (Const (@{const_name Product_Type.Unity}, _)) = []
  | dest_tuple (Const (@{const_name Pair}, _) $ t1 $ t2) = t1 :: (dest_tuple t2)
  | dest_tuple t = [t]

fun mk_scomp (t, u) =
  let
    val T = fastype_of t
    val U = fastype_of u
    val [A] = binder_types T
    val D = body_type U 
  in 
    Const (@{const_name "scomp"}, T --> U --> A --> D) $ t $ u
  end;

fun dest_funT (Type ("fun",[S, T])) = (S, T)
  | dest_funT T = raise TYPE ("dest_funT", [T], [])
 
fun mk_fun_comp (t, u) =
  let
    val (_, B) = dest_funT (fastype_of t)
    val (C, A) = dest_funT (fastype_of u)
  in
    Const(@{const_name "Fun.comp"}, (A --> B) --> (C --> A) --> C --> B) $ t $ u
  end;

fun dest_randomT (Type ("fun", [@{typ Random.seed},
  Type ("*", [Type ("*", [T, @{typ "unit => Code_Evaluation.term"}]) ,@{typ Random.seed}])])) = T
  | dest_randomT T = raise TYPE ("dest_randomT", [T], [])

(* destruction of intro rules *)

(* FIXME: look for other place where this functionality was used before *)
fun strip_intro_concl nparams intro = let
  val _ $ u = Logic.strip_imp_concl intro
  val (pred, all_args) = strip_comb u
  val (params, args) = chop nparams all_args
in (pred, (params, args)) end

(** data structures **)

(* new datatype for modes: *)
(*
datatype instantiation = Input | Output
type arg_mode = Tuple of instantiation list | Atom of instantiation | HigherOrderMode of mode
type mode = arg_mode list
type tmode = Mode of mode * 
*)
type smode = (int * int list option) list
type mode = smode option list * smode;
datatype tmode = Mode of mode * smode * tmode option list;

fun gen_split_smode (mk_tuple, strip_tuple) smode ts =
  let
    fun split_tuple' _ _ [] = ([], [])
    | split_tuple' is i (t::ts) =
      (if i mem is then apfst else apsnd) (cons t)
        (split_tuple' is (i+1) ts)
    fun split_tuple is t = split_tuple' is 1 (strip_tuple t)
    fun split_smode' _ _ [] = ([], [])
      | split_smode' smode i (t::ts) =
        (if i mem (map fst smode) then
          case (the (AList.lookup (op =) smode i)) of
            NONE => apfst (cons t)
            | SOME is =>
              let
                val (ts1, ts2) = split_tuple is t
                fun cons_tuple ts = if null ts then I else cons (mk_tuple ts)
                in (apfst (cons_tuple ts1)) o (apsnd (cons_tuple ts2)) end
          else apsnd (cons t))
        (split_smode' smode (i+1) ts)
  in split_smode' smode 1 ts end

val split_smode = gen_split_smode (HOLogic.mk_tuple, HOLogic.strip_tuple)   
val split_smodeT = gen_split_smode (HOLogic.mk_tupleT, HOLogic.strip_tupleT)

fun gen_split_mode split_smode (iss, is) ts =
  let
    val (t1, t2) = chop (length iss) ts 
  in (t1, split_smode is t2) end

val split_mode = gen_split_mode split_smode
val split_modeT = gen_split_mode split_smodeT

fun string_of_smode js =
    commas (map
      (fn (i, is) =>
        string_of_int i ^ (case is of NONE => ""
    | SOME is => "p" ^ enclose "[" "]" (commas (map string_of_int is)))) js)

fun string_of_mode (iss, is) = space_implode " -> " (map
  (fn NONE => "X"
    | SOME js => enclose "[" "]" (string_of_smode js))
       (iss @ [SOME is]));

fun string_of_tmode (Mode (predmode, termmode, param_modes)) =
  "predmode: " ^ (string_of_mode predmode) ^ 
  (if null param_modes then "" else
    "; " ^ "params: " ^ commas (map (the_default "NONE" o Option.map string_of_tmode) param_modes))

datatype indprem = Prem of term list * term | Negprem of term list * term | Sidecond of term |
  GeneratorPrem of term list * term | Generator of (string * typ);

type moded_clause = term list * (indprem * tmode) list
type 'a pred_mode_table = (string * (mode * 'a) list) list

datatype predfun_data = PredfunData of {
  name : string,
  definition : thm,
  intro : thm,
  elim : thm
};

fun rep_predfun_data (PredfunData data) = data;
fun mk_predfun_data (name, definition, intro, elim) =
  PredfunData {name = name, definition = definition, intro = intro, elim = elim}

datatype function_data = FunctionData of {
  name : string,
  equation : thm option (* is not used at all? *)
};

fun rep_function_data (FunctionData data) = data;
fun mk_function_data (name, equation) =
  FunctionData {name = name, equation = equation}

datatype pred_data = PredData of {
  intros : thm list,
  elim : thm option,
  nparams : int,
  functions : (mode * predfun_data) list,
  generators : (mode * function_data) list,
  sizelim_functions : (mode * function_data) list 
};

fun rep_pred_data (PredData data) = data;
fun mk_pred_data ((intros, elim, nparams), (functions, generators, sizelim_functions)) =
  PredData {intros = intros, elim = elim, nparams = nparams,
    functions = functions, generators = generators, sizelim_functions = sizelim_functions}
fun map_pred_data f (PredData {intros, elim, nparams, functions, generators, sizelim_functions}) =
  mk_pred_data (f ((intros, elim, nparams), (functions, generators, sizelim_functions)))
  
fun eq_option eq (NONE, NONE) = true
  | eq_option eq (SOME x, SOME y) = eq (x, y)
  | eq_option eq _ = false
  
fun eq_pred_data (PredData d1, PredData d2) = 
  eq_list (Thm.eq_thm) (#intros d1, #intros d2) andalso
  eq_option (Thm.eq_thm) (#elim d1, #elim d2) andalso
  #nparams d1 = #nparams d2
  
structure PredData = TheoryDataFun
(
  type T = pred_data Graph.T;
  val empty = Graph.empty;
  val copy = I;
  val extend = I;
  fun merge _ = Graph.merge eq_pred_data;
);

(* queries *)

fun lookup_pred_data thy name =
  Option.map rep_pred_data (try (Graph.get_node (PredData.get thy)) name)

fun the_pred_data thy name = case lookup_pred_data thy name
 of NONE => error ("No such predicate " ^ quote name)  
  | SOME data => data;

val is_registered = is_some oo lookup_pred_data 

val all_preds_of = Graph.keys o PredData.get

fun intros_of thy = map (Thm.transfer thy) o #intros o the_pred_data thy

fun the_elim_of thy name = case #elim (the_pred_data thy name)
 of NONE => error ("No elimination rule for predicate " ^ quote name)
  | SOME thm => Thm.transfer thy thm 
  
val has_elim = is_some o #elim oo the_pred_data;

val nparams_of = #nparams oo the_pred_data

val modes_of = (map fst) o #functions oo the_pred_data

val sizelim_modes_of = (map fst) o #sizelim_functions oo the_pred_data

val rpred_modes_of = (map fst) o #generators oo the_pred_data
  
fun all_modes_of thy = map (fn name => (name, modes_of thy name)) (all_preds_of thy) 

val is_compiled = not o null o #functions oo the_pred_data

fun lookup_predfun_data thy name mode =
  Option.map rep_predfun_data (AList.lookup (op =)
  (#functions (the_pred_data thy name)) mode)

fun the_predfun_data thy name mode = case lookup_predfun_data thy name mode
  of NONE => error ("No function defined for mode " ^ string_of_mode mode ^ " of predicate " ^ name)
   | SOME data => data;

val predfun_name_of = #name ooo the_predfun_data

val predfun_definition_of = #definition ooo the_predfun_data

val predfun_intro_of = #intro ooo the_predfun_data

val predfun_elim_of = #elim ooo the_predfun_data

fun lookup_generator_data thy name mode = 
  Option.map rep_function_data (AList.lookup (op =)
  (#generators (the_pred_data thy name)) mode)
  
fun the_generator_data thy name mode = case lookup_generator_data thy name mode
  of NONE => error ("No generator defined for mode " ^ string_of_mode mode ^ " of predicate " ^ name)
   | SOME data => data

val generator_name_of = #name ooo the_generator_data

val generator_modes_of = (map fst) o #generators oo the_pred_data

fun all_generator_modes_of thy =
  map (fn name => (name, generator_modes_of thy name)) (all_preds_of thy) 

fun lookup_sizelim_function_data thy name mode =
  Option.map rep_function_data (AList.lookup (op =)
  (#sizelim_functions (the_pred_data thy name)) mode)

fun the_sizelim_function_data thy name mode = case lookup_sizelim_function_data thy name mode
  of NONE => error ("No size-limited function defined for mode " ^ string_of_mode mode
    ^ " of predicate " ^ name)
   | SOME data => data

val sizelim_function_name_of = #name ooo the_sizelim_function_data

(*val generator_modes_of = (map fst) o #generators oo the_pred_data*)
     
(* diagnostic display functions *)

fun print_modes modes =
  tracing ("Inferred modes:\n" ^
    cat_lines (map (fn (s, ms) => s ^ ": " ^ commas (map
      string_of_mode ms)) modes));

fun print_pred_mode_table string_of_entry thy pred_mode_table =
  let
    fun print_mode pred (mode, entry) =  "mode : " ^ (string_of_mode mode)
      ^ (string_of_entry pred mode entry)  
    fun print_pred (pred, modes) =
      "predicate " ^ pred ^ ": " ^ cat_lines (map (print_mode pred) modes)
    val _ = tracing (cat_lines (map print_pred pred_mode_table))
  in () end;

fun string_of_prem thy (Prem (ts, p)) =
    (Syntax.string_of_term_global thy (list_comb (p, ts))) ^ "(premise)"
  | string_of_prem thy (Negprem (ts, p)) =
    (Syntax.string_of_term_global thy (HOLogic.mk_not (list_comb (p, ts)))) ^ "(negative premise)"
  | string_of_prem thy (Sidecond t) =
    (Syntax.string_of_term_global thy t) ^ "(sidecondition)"
  | string_of_prem thy _ = error "string_of_prem: unexpected input"

fun string_of_moded_prem thy (Prem (ts, p), tmode) =
    (Syntax.string_of_term_global thy (list_comb (p, ts))) ^
    "(" ^ (string_of_tmode tmode) ^ ")"
  | string_of_moded_prem thy (GeneratorPrem (ts, p), Mode (predmode, is, _)) =
    (Syntax.string_of_term_global thy (list_comb (p, ts))) ^
    "(generator_mode: " ^ (string_of_mode predmode) ^ ")"
  | string_of_moded_prem thy (Generator (v, T), _) =
    "Generator for " ^ v ^ " of Type " ^ (Syntax.string_of_typ_global thy T)
  | string_of_moded_prem thy (Negprem (ts, p), Mode (_, is, _)) =
    (Syntax.string_of_term_global thy (list_comb (p, ts))) ^
    "(negative mode: " ^ string_of_smode is ^ ")"
  | string_of_moded_prem thy (Sidecond t, Mode (_, is, _)) =
    (Syntax.string_of_term_global thy t) ^
    "(sidecond mode: " ^ string_of_smode is ^ ")"    
  | string_of_moded_prem _ _ = error "string_of_moded_prem: unimplemented"

fun print_moded_clauses thy =
  let
    fun string_of_clause pred mode clauses =
      cat_lines (map (fn (ts, prems) => (space_implode " --> "
        (map (string_of_moded_prem thy) prems)) ^ " --> " ^ pred ^ " "
        ^ (space_implode " " (map (Syntax.string_of_term_global thy) ts))) clauses)
  in print_pred_mode_table string_of_clause thy end;

fun string_of_clause thy pred (ts, prems) =
  (space_implode " --> "
  (map (string_of_prem thy) prems)) ^ " --> " ^ pred ^ " "
   ^ (space_implode " " (map (Syntax.string_of_term_global thy) ts))

fun print_compiled_terms thy =
  print_pred_mode_table (fn _ => fn _ => Syntax.string_of_term_global thy) thy
    
fun print_stored_rules thy =
  let
    val preds = (Graph.keys o PredData.get) thy
    fun print pred () = let
      val _ = writeln ("predicate: " ^ pred)
      val _ = writeln ("number of parameters: " ^ string_of_int (nparams_of thy pred))
      val _ = writeln ("introrules: ")
      val _ = fold (fn thm => fn u => writeln (Display.string_of_thm_global thy thm))
        (rev (intros_of thy pred)) ()
    in
      if (has_elim thy pred) then
        writeln ("elimrule: " ^ Display.string_of_thm_global thy (the_elim_of thy pred))
      else
        writeln ("no elimrule defined")
    end
  in
    fold print preds ()
  end;

fun print_all_modes thy =
  let
    val _ = writeln ("Inferred modes:")
    fun print (pred, modes) u =
      let
        val _ = writeln ("predicate: " ^ pred)
        val _ = writeln ("modes: " ^ (commas (map string_of_mode modes)))
      in u end  
  in
    fold print (all_modes_of thy) ()
  end

(* validity checks *)

fun check_expected_modes (options : Predicate_Compile_Aux.options) modes =
  case expected_modes options of
    SOME (s, ms) => (case AList.lookup (op =) modes s of
      SOME modes =>
        if not (eq_set (map (map (rpair NONE)) ms, map snd modes)) then
          error ("expected modes were not inferred:"
            ^ "infered modes for " ^ s ^ ": " ^ commas (map (string_of_smode o snd) modes))
        else ()
      | NONE => ())
  | NONE => ()

(* importing introduction rules *)   

fun unify_consts thy cs intr_ts =
  (let
     val add_term_consts_2 = fold_aterms (fn Const c => insert (op =) c | _ => I);
     fun varify (t, (i, ts)) =
       let val t' = map_types (Logic.incr_tvar (i + 1)) (#2 (Type.varify [] t))
       in (maxidx_of_term t', t'::ts) end;
     val (i, cs') = foldr varify (~1, []) cs;
     val (i', intr_ts') = foldr varify (i, []) intr_ts;
     val rec_consts = fold add_term_consts_2 cs' [];
     val intr_consts = fold add_term_consts_2 intr_ts' [];
     fun unify (cname, cT) =
       let val consts = map snd (List.filter (fn c => fst c = cname) intr_consts)
       in fold (Sign.typ_unify thy) ((replicate (length consts) cT) ~~ consts) end;
     val (env, _) = fold unify rec_consts (Vartab.empty, i');
     val subst = map_types (Envir.norm_type env)
   in (map subst cs', map subst intr_ts')
   end) handle Type.TUNIFY =>
     (warning "Occurrences of recursive constant have non-unifiable types"; (cs, intr_ts));

fun import_intros _ [] ctxt = ([], ctxt)
  | import_intros nparams (th :: ths) ctxt =
    let
      val ((_, [th']), ctxt') = Variable.import false [th] ctxt
      val thy = ProofContext.theory_of ctxt'
      val (pred, (params, args)) = strip_intro_concl nparams (prop_of th')
      val ho_args = filter (is_predT o fastype_of) args
      fun instantiate_typ th =
        let
          val (pred', _) = strip_intro_concl 0 (prop_of th)
          val _ = if not (fst (dest_Const pred) = fst (dest_Const pred')) then
            error "Trying to instantiate another predicate" else ()
          val subst = Sign.typ_match thy
            (fastype_of pred', fastype_of pred) Vartab.empty
          val subst' = map (fn (indexname, (s, T)) => ((indexname, s), T))
            (Vartab.dest subst)
        in Thm.certify_instantiate (subst', []) th end;
      fun instantiate_ho_args th =
        let
          val (_, (params', args')) = strip_intro_concl nparams (prop_of th)
          val ho_args' = map dest_Var (filter (is_predT o fastype_of) args')
        in Thm.certify_instantiate ([], map dest_Var params' ~~ params) th end
      val ((_, ths'), ctxt1) =
        Variable.import false (map (instantiate_typ #> instantiate_ho_args) ths) ctxt'
    in
      (th' :: ths', ctxt1)
    end

(* generation of case rules from user-given introduction rules *)

fun mk_casesrule ctxt nparams introrules =
  let
    val (intros_th, ctxt1) = import_intros nparams introrules ctxt
    val intros = map prop_of intros_th
    val (pred, (params, args)) = strip_intro_concl nparams (hd intros)
    val ([propname], ctxt2) = Variable.variant_fixes ["thesis"] ctxt1
    val prop = HOLogic.mk_Trueprop (Free (propname, HOLogic.boolT))
    val (argnames, ctxt3) = Variable.variant_fixes
      (map (fn i => "a" ^ string_of_int i) (1 upto (length args))) ctxt2
    val argvs = map2 (curry Free) argnames (map fastype_of args)
    fun mk_case intro =
      let
        val (_, (_, args)) = strip_intro_concl nparams intro
        val prems = Logic.strip_imp_prems intro
        val eqprems = map (HOLogic.mk_Trueprop o HOLogic.mk_eq) (argvs ~~ args)
        val frees = (fold o fold_aterms)
          (fn t as Free _ =>
              if member (op aconv) params t then I else insert (op aconv) t
           | _ => I) (args @ prems) []
      in fold Logic.all frees (Logic.list_implies (eqprems @ prems, prop)) end
    val assm = HOLogic.mk_Trueprop (list_comb (pred, params @ argvs))
    val cases = map mk_case intros
  in Logic.list_implies (assm :: cases, prop) end;

(** preprocessing rules **)  

fun imp_prems_conv cv ct =
  case Thm.term_of ct of
    Const ("==>", _) $ _ $ _ => Conv.combination_conv (Conv.arg_conv cv) (imp_prems_conv cv) ct
  | _ => Conv.all_conv ct

fun Trueprop_conv cv ct =
  case Thm.term_of ct of
    Const ("Trueprop", _) $ _ => Conv.arg_conv cv ct  
  | _ => error "Trueprop_conv"

fun preprocess_intro thy rule =
  Conv.fconv_rule
    (imp_prems_conv
      (Trueprop_conv (Conv.try_conv (Conv.rewr_conv (Thm.symmetric @{thm Predicate.eq_is_eq})))))
    (Thm.transfer thy rule)

fun preprocess_elim thy nparams elimrule =
  let
    fun replace_eqs (Const ("Trueprop", _) $ (Const ("op =", T) $ lhs $ rhs)) =
       HOLogic.mk_Trueprop (Const (@{const_name Predicate.eq}, T) $ lhs $ rhs)
     | replace_eqs t = t
    val ctxt = ProofContext.init thy
    val ((_, [elimrule]), ctxt') = Variable.import false [elimrule] ctxt
    val prems = Thm.prems_of elimrule
    val nargs = length (snd (strip_comb (HOLogic.dest_Trueprop (hd prems)))) - nparams
    fun preprocess_case t =
      let
       val params = Logic.strip_params t
       val (assums1, assums2) = chop nargs (Logic.strip_assums_hyp t)
       val assums_hyp' = assums1 @ (map replace_eqs assums2)
      in
       list_all (params, Logic.list_implies (assums_hyp', Logic.strip_assums_concl t))
      end
    val cases' = map preprocess_case (tl prems)
    val elimrule' = Logic.list_implies ((hd prems) :: cases', Thm.concl_of elimrule)
    val bigeq = (Thm.symmetric (Conv.implies_concl_conv
      (MetaSimplifier.rewrite true [@{thm Predicate.eq_is_eq}])
        (cterm_of thy elimrule')))
    val tac = (fn _ => setmp quick_and_dirty true (SkipProof.cheat_tac thy))    
    val eq = Goal.prove ctxt' [] [] (Logic.mk_equals ((Thm.prop_of elimrule), elimrule')) tac
  in
    Thm.equal_elim eq elimrule |> singleton (Variable.export ctxt' ctxt)
  end;

(* special case: predicate with no introduction rule *)
fun noclause thy predname elim = let
  val T = (Logic.unvarifyT o Sign.the_const_type thy) predname
  val Ts = binder_types T
  val names = Name.variant_list []
        (map (fn i => "x" ^ (string_of_int i)) (1 upto (length Ts)))
  val vs = map2 (curry Free) names Ts
  val clausehd = HOLogic.mk_Trueprop (list_comb (Const (predname, T), vs))
  val intro_t = Logic.mk_implies (@{prop False}, clausehd)
  val P = HOLogic.mk_Trueprop (Free ("P", HOLogic.boolT))
  val elim_t = Logic.list_implies ([clausehd, Logic.mk_implies (@{prop False}, P)], P)
  val intro = Goal.prove (ProofContext.init thy) names [] intro_t
        (fn {...} => etac @{thm FalseE} 1)
  val elim = Goal.prove (ProofContext.init thy) ("P" :: names) [] elim_t
        (fn {...} => etac elim 1) 
in
  ([intro], elim)
end

fun expand_tuples_elim th = th

fun fetch_pred_data thy name =
  case try (Inductive.the_inductive (ProofContext.init thy)) name of
    SOME (info as (_, result)) => 
      let
        fun is_intro_of intro =
          let
            val (const, _) = strip_comb (HOLogic.dest_Trueprop (concl_of intro))
          in (fst (dest_Const const) = name) end;      
        val intros = ind_set_codegen_preproc thy
          (map (expand_tuples thy #> preprocess_intro thy) (filter is_intro_of (#intrs result)))
        val pre_elim = nth (#elims result) (find_index (fn s => s = name) (#names (fst info)))
        val nparams = length (Inductive.params_of (#raw_induct result))
        (*val elim = singleton (ind_set_codegen_preproc thy) (preprocess_elim thy nparams 
          (expand_tuples_elim pre_elim))*)
        val elim =
          (Drule.standard o (setmp quick_and_dirty true (SkipProof.make_thm thy)))
          (mk_casesrule (ProofContext.init thy) nparams intros)
        val (intros, elim) = if null intros then noclause thy name elim else (intros, elim)
      in
        mk_pred_data ((intros, SOME elim, nparams), ([], [], []))
      end                                                                    
  | NONE => error ("No such predicate: " ^ quote name)

(* updaters *)

fun apfst3 f (x, y, z) =  (f x, y, z)
fun apsnd3 f (x, y, z) =  (x, f y, z)
fun aptrd3 f (x, y, z) =  (x, y, f z)

fun add_predfun name mode data =
  let
    val add = (apsnd o apfst3 o cons) (mode, mk_predfun_data data)
  in PredData.map (Graph.map_node name (map_pred_data add)) end

fun is_inductive_predicate thy name =
  is_some (try (Inductive.the_inductive (ProofContext.init thy)) name)

fun depending_preds_of thy (key, value) =
  let
    val intros = (#intros o rep_pred_data) value
  in
    fold Term.add_const_names (map Thm.prop_of intros) []
      |> filter (fn c => (not (c = key)) andalso (is_inductive_predicate thy c orelse is_registered thy c))
  end;


(* code dependency graph *)
(*
fun dependencies_of thy name =
  let
    val (intros, elim, nparams) = fetch_pred_data thy name 
    val data = mk_pred_data ((intros, SOME elim, nparams), ([], [], []))
    val keys = depending_preds_of thy intros
  in
    (data, keys)
  end;
*)
(* guessing number of parameters *)
fun find_indexes pred xs =
  let
    fun find is n [] = is
      | find is n (x :: xs) = find (if pred x then (n :: is) else is) (n + 1) xs;
  in rev (find [] 0 xs) end;

fun guess_nparams T =
  let
    val argTs = binder_types T
    val nparams = fold (curry Int.max)
      (map (fn x => x + 1) (find_indexes is_predT argTs)) 0
  in nparams end;

fun add_intro thm thy = let
   val (name, T) = dest_Const (fst (strip_intro_concl 0 (prop_of thm)))
   fun cons_intro gr =
     case try (Graph.get_node gr) name of
       SOME pred_data => Graph.map_node name (map_pred_data
         (apfst (fn (intros, elim, nparams) => (thm::intros, elim, nparams)))) gr
     | NONE =>
       let
         val nparams = the_default (guess_nparams T)  (try (#nparams o rep_pred_data o (fetch_pred_data thy)) name)
       in Graph.new_node (name, mk_pred_data (([thm], NONE, nparams), ([], [], []))) gr end;
  in PredData.map cons_intro thy end

fun set_elim thm = let
    val (name, _) = dest_Const (fst 
      (strip_comb (HOLogic.dest_Trueprop (hd (prems_of thm)))))
    fun set (intros, _, nparams) = (intros, SOME thm, nparams)  
  in PredData.map (Graph.map_node name (map_pred_data (apfst set))) end

fun set_nparams name nparams = let
    fun set (intros, elim, _ ) = (intros, elim, nparams) 
  in PredData.map (Graph.map_node name (map_pred_data (apfst set))) end
    
fun register_predicate (pre_intros, pre_elim, nparams) thy =
  let
    val (name, _) = dest_Const (fst (strip_intro_concl nparams (prop_of (hd pre_intros))))
    (* preprocessing *)
    val intros = ind_set_codegen_preproc thy (map (preprocess_intro thy) pre_intros)
    val elim = singleton (ind_set_codegen_preproc thy) (preprocess_elim thy nparams pre_elim)
  in
    if not (member (op =) (Graph.keys (PredData.get thy)) name) then
      PredData.map
        (Graph.new_node (name, mk_pred_data ((intros, SOME elim, nparams), ([], [], [])))) thy
    else thy
  end

fun register_intros pre_intros thy =
  let
    val (c, T) = dest_Const (fst (strip_intro_concl 0 (prop_of (hd pre_intros))))
    fun constname_of_intro intr = fst (dest_Const (fst (strip_intro_concl 0 (prop_of intr))))
    val _ = if not (forall (fn intr => constname_of_intro intr = c) pre_intros) then
      error "register_intros: Introduction rules of different constants are used" else ()
    val nparams = guess_nparams T
    val pre_elim = 
      (Drule.standard o (setmp quick_and_dirty true (SkipProof.make_thm thy)))
      (mk_casesrule (ProofContext.init thy) nparams pre_intros)
  in register_predicate (pre_intros, pre_elim, nparams) thy end

fun set_generator_name pred mode name = 
  let
    val set = (apsnd o apsnd3 o cons) (mode, mk_function_data (name, NONE))
  in
    PredData.map (Graph.map_node pred (map_pred_data set))
  end

fun set_sizelim_function_name pred mode name = 
  let
    val set = (apsnd o aptrd3 o cons) (mode, mk_function_data (name, NONE))
  in
    PredData.map (Graph.map_node pred (map_pred_data set))
  end

(** data structures for generic compilation for different monads **)

(* maybe rename functions more generic:
  mk_predT -> mk_monadT; dest_predT -> dest_monadT
  mk_single -> mk_return (?)
*)
datatype compilation_funs = CompilationFuns of {
  mk_predT : typ -> typ,
  dest_predT : typ -> typ,
  mk_bot : typ -> term,
  mk_single : term -> term,
  mk_bind : term * term -> term,
  mk_sup : term * term -> term,
  mk_if : term -> term,
  mk_not : term -> term,
(*  funT_of : mode -> typ -> typ, *)
(*  mk_fun_of : theory -> (string * typ) -> mode -> term, *) 
  mk_map : typ -> typ -> term -> term -> term,
  lift_pred : term -> term
};

fun mk_predT (CompilationFuns funs) = #mk_predT funs
fun dest_predT (CompilationFuns funs) = #dest_predT funs
fun mk_bot (CompilationFuns funs) = #mk_bot funs
fun mk_single (CompilationFuns funs) = #mk_single funs
fun mk_bind (CompilationFuns funs) = #mk_bind funs
fun mk_sup (CompilationFuns funs) = #mk_sup funs
fun mk_if (CompilationFuns funs) = #mk_if funs
fun mk_not (CompilationFuns funs) = #mk_not funs
(*fun funT_of (CompilationFuns funs) = #funT_of funs*)
(*fun mk_fun_of (CompilationFuns funs) = #mk_fun_of funs*)
fun mk_map (CompilationFuns funs) = #mk_map funs
fun lift_pred (CompilationFuns funs) = #lift_pred funs

fun funT_of compfuns (iss, is) T =
  let
    val Ts = binder_types T
    val (paramTs, (inargTs, outargTs)) = split_modeT (iss, is) Ts
    val paramTs' = map2 (fn NONE => I | SOME is => funT_of compfuns ([], is)) iss paramTs
  in
    (paramTs' @ inargTs) ---> (mk_predT compfuns (mk_tupleT outargTs))
  end;

fun mk_fun_of compfuns thy (name, T) mode = 
  Const (predfun_name_of thy name mode, funT_of compfuns mode T)


structure PredicateCompFuns =
struct

fun mk_predT T = Type (@{type_name "Predicate.pred"}, [T])

fun dest_predT (Type (@{type_name "Predicate.pred"}, [T])) = T
  | dest_predT T = raise TYPE ("dest_predT", [T], []);

fun mk_bot T = Const (@{const_name Orderings.bot}, mk_predT T);

fun mk_single t =
  let val T = fastype_of t
  in Const(@{const_name Predicate.single}, T --> mk_predT T) $ t end;

fun mk_bind (x, f) =
  let val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (@{const_name Predicate.bind}, fastype_of x --> T --> U) $ x $ f
  end;

val mk_sup = HOLogic.mk_binop @{const_name sup};

fun mk_if cond = Const (@{const_name Predicate.if_pred},
  HOLogic.boolT --> mk_predT HOLogic.unitT) $ cond;

fun mk_not t = let val T = mk_predT HOLogic.unitT
  in Const (@{const_name Predicate.not_pred}, T --> T) $ t end

fun mk_Enum f =
  let val T as Type ("fun", [T', _]) = fastype_of f
  in
    Const (@{const_name Predicate.Pred}, T --> mk_predT T') $ f    
  end;

fun mk_Eval (f, x) =
  let
    val T = fastype_of x
  in
    Const (@{const_name Predicate.eval}, mk_predT T --> T --> HOLogic.boolT) $ f $ x
  end;

fun mk_map T1 T2 tf tp = Const (@{const_name Predicate.map},
  (T1 --> T2) --> mk_predT T1 --> mk_predT T2) $ tf $ tp;

val lift_pred = I

val compfuns = CompilationFuns {mk_predT = mk_predT, dest_predT = dest_predT, mk_bot = mk_bot,
  mk_single = mk_single, mk_bind = mk_bind, mk_sup = mk_sup, mk_if = mk_if, mk_not = mk_not,
  mk_map = mk_map, lift_pred = lift_pred};

end;

structure RPredCompFuns =
struct

fun mk_rpredT T =
  @{typ "Random.seed"} --> HOLogic.mk_prodT (PredicateCompFuns.mk_predT T, @{typ "Random.seed"})

fun dest_rpredT (Type ("fun", [_,
  Type (@{type_name "*"}, [Type (@{type_name "Predicate.pred"}, [T]), _])])) = T
  | dest_rpredT T = raise TYPE ("dest_rpredT", [T], []); 

fun mk_bot T = Const(@{const_name RPred.bot}, mk_rpredT T)

fun mk_single t =
  let
    val T = fastype_of t
  in
    Const (@{const_name RPred.return}, T --> mk_rpredT T) $ t
  end;

fun mk_bind (x, f) =
  let
    val T as (Type ("fun", [_, U])) = fastype_of f
  in
    Const (@{const_name RPred.bind}, fastype_of x --> T --> U) $ x $ f
  end

val mk_sup = HOLogic.mk_binop @{const_name RPred.supp}

fun mk_if cond = Const (@{const_name RPred.if_rpred},
  HOLogic.boolT --> mk_rpredT HOLogic.unitT) $ cond;

fun mk_not t = error "Negation is not defined for RPred"

fun mk_map t = error "FIXME" (*FIXME*)

fun lift_pred t =
  let
    val T = PredicateCompFuns.dest_predT (fastype_of t)
    val lift_predT = PredicateCompFuns.mk_predT T --> mk_rpredT T 
  in
    Const (@{const_name "RPred.lift_pred"}, lift_predT) $ t  
  end;

val compfuns = CompilationFuns {mk_predT = mk_rpredT, dest_predT = dest_rpredT, mk_bot = mk_bot,
    mk_single = mk_single, mk_bind = mk_bind, mk_sup = mk_sup, mk_if = mk_if, mk_not = mk_not,
    mk_map = mk_map, lift_pred = lift_pred};

end;
(* for external use with interactive mode *)
val pred_compfuns = PredicateCompFuns.compfuns
val rpred_compfuns = RPredCompFuns.compfuns;

fun lift_random random =
  let
    val T = dest_randomT (fastype_of random)
  in
    Const (@{const_name lift_random}, (@{typ Random.seed} -->
      HOLogic.mk_prodT (HOLogic.mk_prodT (T, @{typ "unit => term"}), @{typ Random.seed})) --> 
      RPredCompFuns.mk_rpredT T) $ random
  end;

fun sizelim_funT_of compfuns (iss, is) T =
  let
    val Ts = binder_types T
    val (paramTs, (inargTs, outargTs)) = split_modeT (iss, is) Ts
    val paramTs' = map2 (fn SOME is => sizelim_funT_of PredicateCompFuns.compfuns ([], is) | NONE => I) iss paramTs 
  in
    (paramTs' @ inargTs @ [@{typ bool}, @{typ "code_numeral"}]) ---> (mk_predT compfuns (mk_tupleT outargTs))
  end;  

fun mk_sizelim_fun_of compfuns thy (name, T) mode =
  Const (sizelim_function_name_of thy name mode, sizelim_funT_of compfuns mode T)
  
fun mk_generator_of compfuns thy (name, T) mode = 
  Const (generator_name_of thy name mode, sizelim_funT_of compfuns mode T)

(* Mode analysis *)

(*** check if a term contains only constructor functions ***)
fun is_constrt thy =
  let
    val cnstrs = flat (maps
      (map (fn (_, (Tname, _, cs)) => map (apsnd (rpair Tname o length)) cs) o #descr o snd)
      (Symtab.dest (Datatype.get_all thy)));
    fun check t = (case strip_comb t of
        (Free _, []) => true
      | (Const (s, T), ts) => (case (AList.lookup (op =) cnstrs s, body_type T) of
            (SOME (i, Tname), Type (Tname', _)) => length ts = i andalso Tname = Tname' andalso forall check ts
          | _ => false)
      | _ => false)
  in check end;

(*** check if a type is an equality type (i.e. doesn't contain fun)
  FIXME this is only an approximation ***)
fun is_eqT (Type (s, Ts)) = s <> "fun" andalso forall is_eqT Ts
  | is_eqT _ = true;

fun term_vs tm = fold_aterms (fn Free (x, T) => cons x | _ => I) tm [];
val terms_vs = distinct (op =) o maps term_vs;

(** collect all Frees in a term (with duplicates!) **)
fun term_vTs tm =
  fold_aterms (fn Free xT => cons xT | _ => I) tm [];

(*FIXME this function should not be named merge... make it local instead*)
fun merge xs [] = xs
  | merge [] ys = ys
  | merge (x::xs) (y::ys) = if length x >= length y then x::merge xs (y::ys)
      else y::merge (x::xs) ys;

fun subsets i j = if i <= j then
       let val is = subsets (i+1) j
       in merge (map (fn ks => i::ks) is) is end
     else [[]];
     
(* FIXME: should be in library - cprod = map_prod I *)
fun cprod ([], ys) = []
  | cprod (x :: xs, ys) = map (pair x) ys @ cprod (xs, ys);

fun cprods xss = foldr (map op :: o cprod) [[]] xss;

fun cprods_subset [] = [[]]
  | cprods_subset (xs :: xss) =
  let
    val yss = (cprods_subset xss)
  in maps (fn ys => map (fn x => cons x ys) xs) yss @ yss end
  
(*TODO: cleanup function and put together with modes_of_term *)
(*
fun modes_of_param default modes t = let
    val (vs, t') = strip_abs t
    val b = length vs
    fun mk_modes name args = Option.map (maps (fn (m as (iss, is)) =>
        let
          val (args1, args2) =
            if length args < length iss then
              error ("Too few arguments for inductive predicate " ^ name)
            else chop (length iss) args;
          val k = length args2;
          val perm = map (fn i => (find_index_eq (Bound (b - i)) args2) + 1)
            (1 upto b)  
          val partial_mode = (1 upto k) \\ perm
        in
          if not (partial_mode subset is) then [] else
          let
            val is' = 
            (fold_index (fn (i, j) => if j mem is then cons (i + 1) else I) perm [])
            |> fold (fn i => if i > k then cons (i - k + b) else I) is
              
           val res = map (fn x => Mode (m, is', x)) (cprods (map
            (fn (NONE, _) => [NONE]
              | (SOME js, arg) => map SOME (filter
                  (fn Mode (_, js', _) => js=js') (modes_of_term modes arg)))
                    (iss ~~ args1)))
          in res end
        end)) (AList.lookup op = modes name)
  in case strip_comb t' of
    (Const (name, _), args) => the_default default (mk_modes name args)
    | (Var ((name, _), _), args) => the (mk_modes name args)
    | (Free (name, _), args) => the (mk_modes name args)
    | _ => default end
  
and
*)
fun modes_of_term modes t =
  let
    val ks = map_index (fn (i, T) => (i, NONE)) (binder_types (fastype_of t));
    val default = [Mode (([], ks), ks, [])];
    fun mk_modes name args = Option.map (maps (fn (m as (iss, is)) =>
        let
          val (args1, args2) =
            if length args < length iss then
              error ("Too few arguments for inductive predicate " ^ name)
            else chop (length iss) args;
          val k = length args2;
          val prfx = map (rpair NONE) (1 upto k)
        in
          if not (is_prefix op = prfx is) then [] else
          let val is' = map (fn (i, t) => (i - k, t)) (List.drop (is, k))
          in map (fn x => Mode (m, is', x)) (cprods (map
            (fn (NONE, _) => [NONE]
              | (SOME js, arg) => map SOME (filter
                  (fn Mode (_, js', _) => js=js') (modes_of_term modes arg)))
                    (iss ~~ args1)))
          end
        end)) (AList.lookup op = modes name)

  in
    case strip_comb (Envir.eta_contract t) of
      (Const (name, _), args) => the_default default (mk_modes name args)
    | (Var ((name, _), _), args) => the (mk_modes name args)
    | (Free (name, _), args) => the (mk_modes name args)
    | (Abs _, []) => error "Abs at param position" (* modes_of_param default modes t *)
    | _ => default
  end
  
fun select_mode_prem thy modes vs ps =
  find_first (is_some o snd) (ps ~~ map
    (fn Prem (us, t) => find_first (fn Mode (_, is, _) =>
          let
            val (in_ts, out_ts) = split_smode is us;
            val (out_ts', in_ts') = List.partition (is_constrt thy) out_ts;
            val vTs = maps term_vTs out_ts';
            val dupTs = map snd (duplicates (op =) vTs) @
              List.mapPartial (AList.lookup (op =) vTs) vs;
          in
            terms_vs (in_ts @ in_ts') subset vs andalso
            forall (is_eqT o fastype_of) in_ts' andalso
            term_vs t subset vs andalso
            forall is_eqT dupTs
          end)
            (modes_of_term modes t handle Option =>
               error ("Bad predicate: " ^ Syntax.string_of_term_global thy t))
      | Negprem (us, t) => find_first (fn Mode (_, is, _) =>
        is = map (rpair NONE) (1 upto length us) andalso
            terms_vs us subset vs andalso
            term_vs t subset vs)
            (modes_of_term modes t handle Option =>
               error ("Bad predicate: " ^ Syntax.string_of_term_global thy t))
      | Sidecond t => if term_vs t subset vs then SOME (Mode (([], []), [], []))
          else NONE
      ) ps);

fun fold_prem f (Prem (args, _)) = fold f args
  | fold_prem f (Negprem (args, _)) = fold f args
  | fold_prem f (Sidecond t) = f t

fun all_subsets [] = [[]]
  | all_subsets (x::xs) = let val xss' = all_subsets xs in xss' @ (map (cons x) xss') end

fun generator vTs v = 
  let
    val T = the (AList.lookup (op =) vTs v)
  in
    (Generator (v, T), Mode (([], []), [], []))
  end;

fun gen_prem (Prem (us, t)) = GeneratorPrem (us, t)
  | gen_prem (Negprem (us, t)) = error "it is a negated prem"
  | gen_prem (Sidecond t) = error "it is a sidecond"
  | gen_prem _ = error "gen_prem : invalid input for gen_prem"

fun param_gen_prem param_vs (p as Prem (us, t as Free (v, _))) =
  if member (op =) param_vs v then
    GeneratorPrem (us, t)
  else p  
  | param_gen_prem param_vs p = p
  
fun check_mode_clause with_generator thy param_vs modes gen_modes (iss, is) (ts, ps) =
  let
    val modes' = modes @ List.mapPartial
      (fn (_, NONE) => NONE | (v, SOME js) => SOME (v, [([], js)]))
        (param_vs ~~ iss);
    val gen_modes' = gen_modes @ List.mapPartial
      (fn (_, NONE) => NONE | (v, SOME js) => SOME (v, [([], js)]))
        (param_vs ~~ iss);  
    val vTs = distinct (op =) ((fold o fold_prem) Term.add_frees ps (fold Term.add_frees ts []))
    val prem_vs = distinct (op =) ((fold o fold_prem) Term.add_free_names ps [])
    fun check_mode_prems acc_ps vs [] = SOME (acc_ps, vs)
      | check_mode_prems acc_ps vs ps = (case select_mode_prem thy modes' vs ps of
          NONE =>
            (if with_generator then
              (case select_mode_prem thy gen_modes' vs ps of
                SOME (p as Prem _, SOME mode) => check_mode_prems ((gen_prem p, mode) :: acc_ps) 
                  (case p of Prem (us, _) => vs union terms_vs us | _ => vs)
                  (filter_out (equal p) ps)
              | _ =>
                  let 
                    val all_generator_vs = all_subsets (prem_vs \\ vs) |> sort (int_ord o (pairself length))
                  in
                    case (find_first (fn generator_vs => is_some
                      (select_mode_prem thy modes' (vs union generator_vs) ps)) all_generator_vs) of
                      SOME generator_vs => check_mode_prems ((map (generator vTs) generator_vs) @ acc_ps)
                        (vs union generator_vs) ps
                    | NONE => NONE
                  end)
            else
              NONE)
        | SOME (p, SOME mode) => check_mode_prems ((if with_generator then param_gen_prem param_vs p else p, mode) :: acc_ps) 
            (case p of Prem (us, _) => vs union terms_vs us | _ => vs)
            (filter_out (equal p) ps))
    val (in_ts, in_ts') = List.partition (is_constrt thy) (fst (split_smode is ts));
    val in_vs = terms_vs in_ts;
    val concl_vs = terms_vs ts
  in
    if forall is_eqT (map snd (duplicates (op =) (maps term_vTs in_ts))) andalso
    forall (is_eqT o fastype_of) in_ts' then
      case check_mode_prems [] (param_vs union in_vs) ps of
         NONE => NONE
       | SOME (acc_ps, vs) =>
         if with_generator then
           SOME (ts, (rev acc_ps) @ (map (generator vTs) (concl_vs \\ vs))) 
         else
           if concl_vs subset vs then SOME (ts, rev acc_ps) else NONE
    else NONE
  end;

fun print_failed_mode options thy modes p m rs i =
  if show_mode_inference options then
    let
      val _ = Output.tracing ("Clause " ^ string_of_int (i + 1) ^ " of " ^
      p ^ " violates mode " ^ string_of_mode m)
      val _ = Output.tracing (string_of_clause thy p (nth rs i))
    in () end
  else ()

fun check_modes_pred options with_generator thy param_vs clauses modes gen_modes (p, ms) =
  let val SOME rs = AList.lookup (op =) clauses p
  in (p, List.filter (fn m => case find_index
    (is_none o check_mode_clause with_generator thy param_vs modes gen_modes m) rs of
      ~1 => true
    | i => (print_failed_mode options thy modes p m rs i; false)) ms)
  end;

fun get_modes_pred with_generator thy param_vs clauses modes gen_modes (p, ms) =
  let
    val SOME rs = AList.lookup (op =) clauses p
  in
    (p, map (fn m =>
      (m, map (the o check_mode_clause with_generator thy param_vs modes gen_modes m) rs)) ms)
  end;
  
fun fixp f (x : (string * mode list) list) =
  let val y = f x
  in if x = y then x else fixp f y end;

fun infer_modes options thy extra_modes all_modes param_vs clauses =
  let
    val modes =
      fixp (fn modes =>
        map (check_modes_pred options false thy param_vs clauses (modes @ extra_modes) []) modes)
          all_modes
  in
    map (get_modes_pred false thy param_vs clauses (modes @ extra_modes) []) modes
  end;

fun remove_from rem [] = []
  | remove_from rem ((k, vs) :: xs) =
    (case AList.lookup (op =) rem k of
      NONE => (k, vs)
    | SOME vs' => (k, vs \\ vs'))
    :: remove_from rem xs
    
fun infer_modes_with_generator options thy extra_modes all_modes param_vs clauses =
  let
    val prednames = map fst clauses
    val extra_modes = all_modes_of thy
    val gen_modes = all_generator_modes_of thy
      |> filter_out (fn (name, _) => member (op =) prednames name)
    val starting_modes = remove_from extra_modes all_modes
    val modes =
      fixp (fn modes =>
        map (check_modes_pred options true thy param_vs clauses extra_modes (gen_modes @ modes)) modes)
         starting_modes 
  in
    map (get_modes_pred true thy param_vs clauses extra_modes (gen_modes @ modes)) modes
  end;

(* term construction *)

fun mk_v (names, vs) s T = (case AList.lookup (op =) vs s of
      NONE => (Free (s, T), (names, (s, [])::vs))
    | SOME xs =>
        let
          val s' = Name.variant names s;
          val v = Free (s', T)
        in
          (v, (s'::names, AList.update (op =) (s, v::xs) vs))
        end);

fun distinct_v (Free (s, T)) nvs = mk_v nvs s T
  | distinct_v (t $ u) nvs =
      let
        val (t', nvs') = distinct_v t nvs;
        val (u', nvs'') = distinct_v u nvs';
      in (t' $ u', nvs'') end
  | distinct_v x nvs = (x, nvs);

fun compile_match thy compfuns eqs eqs' out_ts success_t =
  let
    val eqs'' = maps mk_eq eqs @ eqs'
    val names = fold Term.add_free_names (success_t :: eqs'' @ out_ts) [];
    val name = Name.variant names "x";
    val name' = Name.variant (name :: names) "y";
    val T = mk_tupleT (map fastype_of out_ts);
    val U = fastype_of success_t;
    val U' = dest_predT compfuns U;
    val v = Free (name, T);
    val v' = Free (name', T);
  in
    lambda v (fst (Datatype.make_case
      (ProofContext.init thy) DatatypeCase.Quiet [] v
      [(mk_tuple out_ts,
        if null eqs'' then success_t
        else Const (@{const_name HOL.If}, HOLogic.boolT --> U --> U --> U) $
          foldr1 HOLogic.mk_conj eqs'' $ success_t $
            mk_bot compfuns U'),
       (v', mk_bot compfuns U')]))
  end;

(*FIXME function can be removed*)
fun mk_funcomp f t =
  let
    val names = Term.add_free_names t [];
    val Ts = binder_types (fastype_of t);
    val vs = map Free
      (Name.variant_list names (replicate (length Ts) "x") ~~ Ts)
  in
    fold_rev lambda vs (f (list_comb (t, vs)))
  end;

fun compile_param size thy compfuns (NONE, t) = t
  | compile_param size thy compfuns (m as SOME (Mode ((iss, is'), is, ms)), t) =
   let
     val (f, args) = strip_comb (Envir.eta_contract t)
     val (params, args') = chop (length ms) args
     val params' = map (compile_param size thy compfuns) (ms ~~ params)
     val mk_fun_of = case size of NONE => mk_fun_of | SOME _ => mk_sizelim_fun_of
     val funT_of = case size of NONE => funT_of | SOME _ => sizelim_funT_of
     val f' =
       case f of
         Const (name, T) => mk_fun_of compfuns thy (name, T) (iss, is')
       | Free (name, T) => Free (name, funT_of compfuns (iss, is') T)
       | _ => error ("PredicateCompiler: illegal parameter term")
   in
     list_comb (f', params' @ args')
   end

fun compile_expr size thy ((Mode (mode, is, ms)), t) =
  case strip_comb t of
    (Const (name, T), params) =>
       let
         val params' = map (compile_param size thy PredicateCompFuns.compfuns) (ms ~~ params)
         val mk_fun_of = case size of NONE => mk_fun_of | SOME _ => mk_sizelim_fun_of
       in
         list_comb (mk_fun_of PredicateCompFuns.compfuns thy (name, T) mode, params')
       end
  | (Free (name, T), args) =>
       let 
         val funT_of = case size of NONE => funT_of | SOME _ => sizelim_funT_of 
       in
         list_comb (Free (name, funT_of PredicateCompFuns.compfuns ([], is) T), args)
       end;
       
fun compile_gen_expr size thy compfuns ((Mode (mode, is, ms)), t) inargs =
  case strip_comb t of
    (Const (name, T), params) =>
      let
        val params' = map (compile_param size thy PredicateCompFuns.compfuns) (ms ~~ params)
      in
        list_comb (mk_generator_of compfuns thy (name, T) mode, params' @ inargs)
      end
    | (Free (name, T), params) =>
    lift_pred compfuns
    (list_comb (Free (name, sizelim_funT_of PredicateCompFuns.compfuns ([], is) T), params @ inargs))
      
          
(** specific rpred functions -- move them to the correct place in this file *)

fun mk_Eval_of size ((x, T), NONE) names = (x, names)
  | mk_Eval_of size ((x, T), SOME mode) names =
	let
    val Ts = binder_types T
    (*val argnames = Name.variant_list names
        (map (fn i => "x" ^ string_of_int i) (1 upto (length Ts)));
    val args = map Free (argnames ~~ Ts)
    val (inargs, outargs) = split_smode mode args*)
		fun mk_split_lambda [] t = lambda (Free (Name.variant names "x", HOLogic.unitT)) t
			| mk_split_lambda [x] t = lambda x t
			| mk_split_lambda xs t =
			let
				fun mk_split_lambda' (x::y::[]) t = HOLogic.mk_split (lambda x (lambda y t))
					| mk_split_lambda' (x::xs) t = HOLogic.mk_split (lambda x (mk_split_lambda' xs t))
			in
				mk_split_lambda' xs t
			end;
  	fun mk_arg (i, T) =
		  let
	  	  val vname = Name.variant names ("x" ^ string_of_int i)
		    val default = Free (vname, T)
		  in 
		    case AList.lookup (op =) mode i of
		      NONE => (([], [default]), [default])
			  | SOME NONE => (([default], []), [default])
			  | SOME (SOME pis) =>
				  case HOLogic.strip_tupleT T of
						[] => error "pair mode but unit tuple" (*(([default], []), [default])*)
					| [_] => error "pair mode but not a tuple" (*(([default], []), [default])*)
					| Ts =>
					  let
							val vnames = Name.variant_list names
								(map (fn j => "x" ^ string_of_int i ^ "p" ^ string_of_int j)
									(1 upto length Ts))
							val args = map Free (vnames ~~ Ts)
							fun split_args (i, arg) (ins, outs) =
							  if member (op =) pis i then
							    (arg::ins, outs)
								else
								  (ins, arg::outs)
							val (inargs, outargs) = fold_rev split_args ((1 upto length Ts) ~~ args) ([], [])
							fun tuple args = if null args then [] else [HOLogic.mk_tuple args]
						in ((tuple inargs, tuple outargs), args) end
			end
		val (inoutargs, args) = split_list (map mk_arg (1 upto (length Ts) ~~ Ts))
    val (inargs, outargs) = pairself flat (split_list inoutargs)
    val size_t = case size of NONE => [] | SOME (polarity, size_t) => [polarity, size_t]
		val r = PredicateCompFuns.mk_Eval (list_comb (x, inargs @ size_t), mk_tuple outargs)
    val t = fold_rev mk_split_lambda args r
  in
    (t, names)
  end;

fun compile_arg size thy param_vs iss arg = 
  let
    val funT_of = case size of NONE => funT_of | SOME _ => sizelim_funT_of
    fun map_params (t as Free (f, T)) =
      if member (op =) param_vs f then
        case (the (AList.lookup (op =) (param_vs ~~ iss) f)) of
          SOME is => let val T' = funT_of PredicateCompFuns.compfuns ([], is) T
            in fst (mk_Eval_of size ((Free (f, T'), T), SOME is) []) end
        | NONE => t
      else t
      | map_params t = t
    in map_aterms map_params arg end
  
fun compile_clause compfuns size thy all_vs param_vs (iss, is) inp (ts, moded_ps) =
  let
    fun check_constrt t (names, eqs) =
      if is_constrt thy t then (t, (names, eqs)) else
        let
          val s = Name.variant names "x";
          val v = Free (s, fastype_of t)
        in (v, (s::names, HOLogic.mk_eq (v, t)::eqs)) end;

    val (in_ts, out_ts) = split_smode is ts;
    val (in_ts', (all_vs', eqs)) =
      fold_map check_constrt in_ts (all_vs, []);

    fun compile_prems out_ts' vs names [] =
          let
            val (out_ts'', (names', eqs')) =
              fold_map check_constrt out_ts' (names, []);
            val (out_ts''', (names'', constr_vs)) = fold_map distinct_v
              out_ts'' (names', map (rpair []) vs);
          in
            compile_match thy compfuns constr_vs (eqs @ eqs') out_ts'''
              (mk_single compfuns (mk_tuple out_ts))
          end
      | compile_prems out_ts vs names ((p, mode as Mode ((_, is), _, _)) :: ps) =
          let
            val vs' = distinct (op =) (flat (vs :: map term_vs out_ts));
            val (out_ts', (names', eqs)) =
              fold_map check_constrt out_ts (names, [])
            val (out_ts'', (names'', constr_vs')) = fold_map distinct_v
              out_ts' ((names', map (rpair []) vs))
            val (compiled_clause, rest) = case p of
               Prem (us, t) =>
                 let
                   val (in_ts, out_ts''') = split_smode is us;
                   val in_ts = map (compile_arg size thy param_vs iss) in_ts
                   val args = case size of
                     NONE => in_ts
                   | SOME (polarity, size_t) => in_ts @ [polarity, size_t]
                   val u = lift_pred compfuns
                     (list_comb (compile_expr size thy (mode, t), args))
                   val rest = compile_prems out_ts''' vs' names'' ps
                 in
                   (u, rest)
                 end
             | Negprem (us, t) =>
                 let
                   val (in_ts, out_ts''') = split_smode is us
                   val size' = Option.map (apfst HOLogic.mk_not) size
                   val args = case size' of
                     NONE => in_ts
                   | SOME (polarity, size_t) => in_ts @ [polarity, size_t]
                   val u = lift_pred compfuns (mk_not PredicateCompFuns.compfuns
                     (list_comb (compile_expr size' thy (mode, t), args)))
                   val rest = compile_prems out_ts''' vs' names'' ps
                 in
                   (u, rest)
                 end
             | Sidecond t =>
                 let
                   val rest = compile_prems [] vs' names'' ps;
                 in
                   (mk_if compfuns t, rest)
                 end
             | GeneratorPrem (us, t) =>
                 let
                   val (in_ts, out_ts''') = split_smode is us;
                   val args = case size of
                     NONE => in_ts
                     | SOME (polarity, size_t) => in_ts @ [polarity, size_t]
                   val u = compile_gen_expr size thy compfuns (mode, t) args
                   val rest = compile_prems out_ts''' vs' names'' ps
                 in
                   (u, rest)
                 end
             | Generator (v, T) =>
                 let
                 val u = lift_random (HOLogic.mk_random T (snd (the size)))
                   val rest = compile_prems [Free (v, T)]  vs' names'' ps;
                 in
                   (u, rest)
                 end
          in
            compile_match thy compfuns constr_vs' eqs out_ts''
              (mk_bind compfuns (compiled_clause, rest))
          end
    val prem_t = compile_prems in_ts' param_vs all_vs' moded_ps;
  in
    mk_bind compfuns (mk_single compfuns inp, prem_t)
  end

fun compile_pred compfuns mk_fun_of use_size thy all_vs param_vs s T mode moded_cls =
  let
	  val (Ts1, Ts2) = chop (length (fst mode)) (binder_types T)
    val (Us1, Us2) = split_smodeT (snd mode) Ts2
    val funT_of = if use_size then sizelim_funT_of else funT_of
    val Ts1' = map2 (fn NONE => I | SOME is => funT_of PredicateCompFuns.compfuns ([], is)) (fst mode) Ts1
  	fun mk_input_term (i, NONE) =
		    [Free (Name.variant (all_vs @ param_vs) ("x" ^ string_of_int i), nth Ts2 (i - 1))]
		  | mk_input_term (i, SOME pis) = case HOLogic.strip_tupleT (nth Ts2 (i - 1)) of
						   [] => error "strange unit input"
					   | [T] => [Free (Name.variant (all_vs @ param_vs) ("x" ^ string_of_int i), nth Ts2 (i - 1))]
						 | Ts => let
							 val vnames = Name.variant_list (all_vs @ param_vs)
								(map (fn j => "x" ^ string_of_int i ^ "p" ^ string_of_int j)
									pis)
						 in if null pis then []
						   else [HOLogic.mk_tuple (map Free (vnames ~~ map (fn j => nth Ts (j - 1)) pis))] end
		val in_ts = maps mk_input_term (snd mode)
    val params = map2 (fn s => fn T => Free (s, T)) param_vs Ts1'
    val [depth_name, polarity_name] = Name.variant_list (all_vs @ param_vs) ["depth", "polarity"]
    val size = Free (depth_name, @{typ "code_numeral"})
    val polarity = Free (polarity_name, @{typ "bool"})
    val decr_size =
      if use_size then
        SOME (polarity, Const ("HOL.minus_class.minus", @{typ "code_numeral => code_numeral => code_numeral"})
          $ size $ Const ("HOL.one_class.one", @{typ "Code_Numeral.code_numeral"}))
      else
        NONE
    val cl_ts =
      map (compile_clause compfuns decr_size
        thy all_vs param_vs mode (mk_tuple in_ts)) moded_cls;
    val t = foldr1 (mk_sup compfuns) cl_ts
    val T' = mk_predT compfuns (mk_tupleT Us2)
    val if_const = Const (@{const_name "If"}, @{typ bool} --> T' --> T' --> T')
    val full_mode = null Us2
    val size_t = 
      if_const $ HOLogic.mk_eq (size, @{term "0 :: code_numeral"})
      $ (if full_mode then 
          if_const $ polarity $ mk_bot compfuns (dest_predT compfuns T') $ mk_single compfuns HOLogic.unit
        else
          mk_bot compfuns (dest_predT compfuns T'))
      $ t
    val fun_const = mk_fun_of compfuns thy (s, T) mode
    val eq = if use_size then
      (list_comb (fun_const, params @ in_ts @ [polarity, size]), size_t)
    else
      (list_comb (fun_const, params @ in_ts), t)
  in
    HOLogic.mk_Trueprop (HOLogic.mk_eq eq)
  end;
  
(* special setup for simpset *)                  
val HOL_basic_ss' = HOL_basic_ss addsimps (@{thms "HOL.simp_thms"} @ [@{thm Pair_eq}])
  setSolver (mk_solver "all_tac_solver" (fn _ => fn _ => all_tac))
	setSolver (mk_solver "True_solver" (fn _ => rtac @{thm TrueI}))

(* Definition of executable functions and their intro and elim rules *)

fun print_arities arities = tracing ("Arities:\n" ^
  cat_lines (map (fn (s, (ks, k)) => s ^ ": " ^
    space_implode " -> " (map
      (fn NONE => "X" | SOME k' => string_of_int k')
        (ks @ [SOME k]))) arities));

fun create_intro_elim_rule (mode as (iss, is)) defthm mode_id funT pred thy =
let
  val Ts = binder_types (fastype_of pred)
  val funtrm = Const (mode_id, funT)
  val (Ts1, Ts2) = chop (length iss) Ts;
  val Ts1' = map2 (fn NONE => I | SOME is => funT_of (PredicateCompFuns.compfuns) ([], is)) iss Ts1
	val param_names = Name.variant_list []
    (map (fn i => "x" ^ string_of_int i) (1 upto (length Ts1)));
  val params = map Free (param_names ~~ Ts1')
	fun mk_args (i, T) argnames =
    let
		  val vname = Name.variant (param_names @ argnames) ("x" ^ string_of_int (length Ts1' + i))
		  val default = (Free (vname, T), vname :: argnames)
	  in
  	  case AList.lookup (op =) is i of
						 NONE => default
					 | SOME NONE => default
        	 | SOME (SOME pis) =>
					   case HOLogic.strip_tupleT T of
						   [] => default
					   | [_] => default
						 | Ts => 
						let
							val vnames = Name.variant_list (param_names @ argnames)
								(map (fn j => "x" ^ string_of_int (length Ts1' + i) ^ "p" ^ string_of_int j)
									(1 upto (length Ts)))
						 in (HOLogic.mk_tuple (map Free (vnames ~~ Ts)), vnames  @ argnames) end
		end
	val (args, argnames) = fold_map mk_args (1 upto (length Ts2) ~~ Ts2) []
  val (inargs, outargs) = split_smode is args
  val param_names' = Name.variant_list (param_names @ argnames)
    (map (fn i => "p" ^ string_of_int i) (1 upto (length iss)))
  val param_vs = map Free (param_names' ~~ Ts1)
  val (params', names) = fold_map (mk_Eval_of NONE) ((params ~~ Ts1) ~~ iss) []
  val predpropI = HOLogic.mk_Trueprop (list_comb (pred, param_vs @ args))
  val predpropE = HOLogic.mk_Trueprop (list_comb (pred, params' @ args))
  val param_eqs = map (HOLogic.mk_Trueprop o HOLogic.mk_eq) (param_vs ~~ params')
  val funargs = params @ inargs
  val funpropE = HOLogic.mk_Trueprop (PredicateCompFuns.mk_Eval (list_comb (funtrm, funargs),
                  if null outargs then Free("y", HOLogic.unitT) else mk_tuple outargs))
  val funpropI = HOLogic.mk_Trueprop (PredicateCompFuns.mk_Eval (list_comb (funtrm, funargs),
                   mk_tuple outargs))
  val introtrm = Logic.list_implies (predpropI :: param_eqs, funpropI)
  val simprules = [defthm, @{thm eval_pred},
	  @{thm "split_beta"}, @{thm "fst_conv"}, @{thm "snd_conv"}, @{thm pair_collapse}]
  val unfolddef_tac = Simplifier.asm_full_simp_tac (HOL_basic_ss addsimps simprules) 1
  val introthm = Goal.prove (ProofContext.init thy) (argnames @ param_names @ param_names' @ ["y"]) [] introtrm (fn {...} => unfolddef_tac)
  val P = HOLogic.mk_Trueprop (Free ("P", HOLogic.boolT));
  val elimtrm = Logic.list_implies ([funpropE, Logic.mk_implies (predpropE, P)], P)
  val elimthm = Goal.prove (ProofContext.init thy) (argnames @ param_names @ param_names' @ ["y", "P"]) [] elimtrm (fn {...} => unfolddef_tac)
in
  (introthm, elimthm)
end;

fun create_constname_of_mode thy prefix name mode = 
  let
    fun string_of_mode mode = if null mode then "0"
      else space_implode "_" (map (fn (i, NONE) => string_of_int i | (i, SOME pis) => string_of_int i ^ "p"
        ^ space_implode "p" (map string_of_int pis)) mode)
    val HOmode = space_implode "_and_"
      (fold (fn NONE => I | SOME mode => cons (string_of_mode mode)) (fst mode) [])
  in
    (Sign.full_bname thy (prefix ^ (Long_Name.base_name name))) ^
      (if HOmode = "" then "_" else "_for_" ^ HOmode ^ "_yields_") ^ (string_of_mode (snd mode))
  end;

fun split_tupleT is T =
	let
		fun split_tuple' _ _ [] = ([], [])
			| split_tuple' is i (T::Ts) =
			(if i mem is then apfst else apsnd) (cons T)
				(split_tuple' is (i+1) Ts)
	in
	  split_tuple' is 1 (HOLogic.strip_tupleT T)
  end
	
fun mk_arg xin xout pis T =
  let
	  val n = length (HOLogic.strip_tupleT T)
		val ni = length pis
	  fun mk_proj i j t =
		  (if i = j then I else HOLogic.mk_fst)
			  (funpow (i - 1) HOLogic.mk_snd t)
	  fun mk_arg' i (si, so) = if i mem pis then
		    (mk_proj si ni xin, (si+1, so))
		  else
			  (mk_proj so (n - ni) xout, (si, so+1))
	  val (args, _) = fold_map mk_arg' (1 upto n) (1, 1)
	in
	  HOLogic.mk_tuple args
	end

fun create_definitions preds (name, modes) thy =
  let
    val compfuns = PredicateCompFuns.compfuns
    val T = AList.lookup (op =) preds name |> the
    fun create_definition (mode as (iss, is)) thy = let
      val mode_cname = create_constname_of_mode thy "" name mode
      val mode_cbasename = Long_Name.base_name mode_cname
      val Ts = binder_types T
      val (Ts1, Ts2) = chop (length iss) Ts
      val (Us1, Us2) =  split_smodeT is Ts2
      val Ts1' = map2 (fn NONE => I | SOME is => funT_of compfuns ([], is)) iss Ts1
      val funT = (Ts1' @ Us1) ---> (mk_predT compfuns (mk_tupleT Us2))
      val names = Name.variant_list []
        (map (fn i => "x" ^ string_of_int i) (1 upto (length Ts)));
			(* old *)
			(*
		  val xs = map Free (names ~~ (Ts1' @ Ts2))
      val (xparams, xargs) = chop (length iss) xs
      val (xins, xouts) = split_smode is xargs
			*)
			(* new *)
			val param_names = Name.variant_list []
			  (map (fn i => "x" ^ string_of_int i) (1 upto (length Ts1')))
		  val xparams = map Free (param_names ~~ Ts1')
      fun mk_vars (i, T) names =
			  let
				  val vname = Name.variant names ("x" ^ string_of_int (length Ts1' + i))
				in
					case AList.lookup (op =) is i of
						 NONE => ((([], [Free (vname, T)]), Free (vname, T)), vname :: names)
					 | SOME NONE => ((([Free (vname, T)], []), Free (vname, T)), vname :: names)
        	 | SOME (SOME pis) =>
					   let
						   val (Tins, Touts) = split_tupleT pis T
							 val name_in = Name.variant names ("x" ^ string_of_int (length Ts1' + i) ^ "in")
							 val name_out = Name.variant names ("x" ^ string_of_int (length Ts1' + i) ^ "out")
						   val xin = Free (name_in, HOLogic.mk_tupleT Tins)
							 val xout = Free (name_out, HOLogic.mk_tupleT Touts)
							 val xarg = mk_arg xin xout pis T
						 in (((if null Tins then [] else [xin], if null Touts then [] else [xout]), xarg), name_in :: name_out :: names) end
						 end
   	  val (xinoutargs, names) = fold_map mk_vars ((1 upto (length Ts2)) ~~ Ts2) param_names
      val (xinout, xargs) = split_list xinoutargs
			val (xins, xouts) = pairself flat (split_list xinout)
			val (xparams', names') = fold_map (mk_Eval_of NONE) ((xparams ~~ Ts1) ~~ iss) names
      fun mk_split_lambda [] t = lambda (Free (Name.variant names' "x", HOLogic.unitT)) t
        | mk_split_lambda [x] t = lambda x t
        | mk_split_lambda xs t =
        let
          fun mk_split_lambda' (x::y::[]) t = HOLogic.mk_split (lambda x (lambda y t))
            | mk_split_lambda' (x::xs) t = HOLogic.mk_split (lambda x (mk_split_lambda' xs t))
        in
          mk_split_lambda' xs t
        end;
      val predterm = PredicateCompFuns.mk_Enum (mk_split_lambda xouts
        (list_comb (Const (name, T), xparams' @ xargs)))
      val lhs = list_comb (Const (mode_cname, funT), xparams @ xins)
      val def = Logic.mk_equals (lhs, predterm)
      val ([definition], thy') = thy |>
        Sign.add_consts_i [(Binding.name mode_cbasename, funT, NoSyn)] |>
        PureThy.add_defs false [((Binding.name (mode_cbasename ^ "_def"), def), [])]
      val (intro, elim) =
        create_intro_elim_rule mode definition mode_cname funT (Const (name, T)) thy'
      in thy'
			  |> add_predfun name mode (mode_cname, definition, intro, elim)
        |> PureThy.store_thm (Binding.name (mode_cbasename ^ "I"), intro) |> snd
        |> PureThy.store_thm (Binding.name (mode_cbasename ^ "E"), elim)  |> snd
        |> Theory.checkpoint
      end;
  in
    fold create_definition modes thy
  end;

fun sizelim_create_definitions preds (name, modes) thy =
  let
    val T = AList.lookup (op =) preds name |> the
    fun create_definition mode thy =
      let
        val mode_cname = create_constname_of_mode thy "sizelim_" name mode
        val funT = sizelim_funT_of PredicateCompFuns.compfuns mode T
      in
        thy |> Sign.add_consts_i [(Binding.name (Long_Name.base_name mode_cname), funT, NoSyn)]
        |> set_sizelim_function_name name mode mode_cname 
      end;
  in
    fold create_definition modes thy
  end;

fun generator_funT_of (iss, is) T =
  let
    val Ts = binder_types T
    val (paramTs, (inargTs, outargTs)) = split_modeT (iss, is) Ts
    val paramTs' = map2 (fn SOME is => sizelim_funT_of PredicateCompFuns.compfuns ([], is) | NONE => I) iss paramTs 
  in
    (paramTs' @ inargTs @ [@{typ "code_numeral"}]) ---> (mk_predT RPredCompFuns.compfuns (mk_tupleT outargTs))
  end

fun rpred_create_definitions preds (name, modes) thy =
  let
    val T = AList.lookup (op =) preds name |> the
    fun create_definition mode thy =
      let
        val mode_cname = create_constname_of_mode thy "gen_" name mode
        val funT = generator_funT_of mode T
      in
        thy |> Sign.add_consts_i [(Binding.name (Long_Name.base_name mode_cname), funT, NoSyn)]
        |> set_generator_name name mode mode_cname 
      end;
  in
    fold create_definition modes thy
  end;
  
(* Proving equivalence of term *)

fun is_Type (Type _) = true
  | is_Type _ = false

(* returns true if t is an application of an datatype constructor *)
(* which then consequently would be splitted *)
(* else false *)
fun is_constructor thy t =
  if (is_Type (fastype_of t)) then
    (case Datatype.get_info thy ((fst o dest_Type o fastype_of) t) of
      NONE => false
    | SOME info => (let
      val constr_consts = maps (fn (_, (_, _, constrs)) => map fst constrs) (#descr info)
      val (c, _) = strip_comb t
      in (case c of
        Const (name, _) => name mem_string constr_consts
        | _ => false) end))
  else false

(* MAJOR FIXME:  prove_params should be simple
 - different form of introrule for parameters ? *)
fun prove_param thy (NONE, t) = TRY (rtac @{thm refl} 1)
  | prove_param thy (m as SOME (Mode (mode, is, ms)), t) =
  let
    val  (f, args) = strip_comb (Envir.eta_contract t)
    val (params, _) = chop (length ms) args
    val f_tac = case f of
      Const (name, T) => simp_tac (HOL_basic_ss addsimps 
         ([@{thm eval_pred}, (predfun_definition_of thy name mode),
         @{thm "split_eta"}, @{thm "split_beta"}, @{thm "fst_conv"},
				 @{thm "snd_conv"}, @{thm pair_collapse}, @{thm "Product_Type.split_conv"}])) 1
    | Free _ => TRY (rtac @{thm refl} 1)
    | Abs _ => error "prove_param: No valid parameter term"
  in
    REPEAT_DETERM (etac @{thm thin_rl} 1)
    THEN REPEAT_DETERM (rtac @{thm ext} 1)
    THEN print_tac "prove_param"
    THEN f_tac
    THEN print_tac "after simplification in prove_args"
    THEN (EVERY (map (prove_param thy) (ms ~~ params)))
    THEN (REPEAT_DETERM (atac 1))
  end

fun prove_expr thy (Mode (mode, is, ms), t, us) (premposition : int) =
  case strip_comb t of
    (Const (name, T), args) =>  
      let
        val introrule = predfun_intro_of thy name mode
        val (args1, args2) = chop (length ms) args
      in
        rtac @{thm bindI} 1
        THEN print_tac "before intro rule:"
        (* for the right assumption in first position *)
        THEN rotate_tac premposition 1
        THEN debug_tac (Display.string_of_thm (ProofContext.init thy) introrule)
        THEN rtac introrule 1
        THEN print_tac "after intro rule"
        (* work with parameter arguments *)
        THEN (atac 1)
        THEN (print_tac "parameter goal")
        THEN (EVERY (map (prove_param thy) (ms ~~ args1)))
        THEN (REPEAT_DETERM (atac 1))
      end
  | _ => rtac @{thm bindI} 1
	  THEN asm_full_simp_tac
		  (HOL_basic_ss' addsimps [@{thm "split_eta"}, @{thm "split_beta"}, @{thm "fst_conv"},
				 @{thm "snd_conv"}, @{thm pair_collapse}]) 1
	  THEN (atac 1)
	  THEN print_tac "after prove parameter call"
		

fun SOLVED tac st = FILTER (fn st' => nprems_of st' = nprems_of st - 1) tac st; 

fun SOLVEDALL tac st = FILTER (fn st' => nprems_of st' = 0) tac st

fun prove_match thy (out_ts : term list) = let
  fun get_case_rewrite t =
    if (is_constructor thy t) then let
      val case_rewrites = (#case_rewrites (Datatype.the_info thy
        ((fst o dest_Type o fastype_of) t)))
      in case_rewrites @ (flat (map get_case_rewrite (snd (strip_comb t)))) end
    else []
  val simprules = @{thm "unit.cases"} :: @{thm "prod.cases"} :: (flat (map get_case_rewrite out_ts))
(* replace TRY by determining if it necessary - are there equations when calling compile match? *)
in
   (* make this simpset better! *)
  asm_full_simp_tac (HOL_basic_ss' addsimps simprules) 1
  THEN print_tac "after prove_match:"
  THEN (DETERM (TRY (EqSubst.eqsubst_tac (ProofContext.init thy) [0] [@{thm "HOL.if_P"}] 1
         THEN (REPEAT_DETERM (rtac @{thm conjI} 1 THEN (SOLVED (asm_simp_tac HOL_basic_ss 1))))
         THEN (SOLVED (asm_simp_tac HOL_basic_ss 1)))))
  THEN print_tac "after if simplification"
end;

(* corresponds to compile_fun -- maybe call that also compile_sidecond? *)

fun prove_sidecond thy modes t =
  let
    fun preds_of t nameTs = case strip_comb t of 
      (f as Const (name, T), args) =>
        if AList.defined (op =) modes name then (name, T) :: nameTs
          else fold preds_of args nameTs
      | _ => nameTs
    val preds = preds_of t []
    val defs = map
      (fn (pred, T) => predfun_definition_of thy pred
        ([], map (rpair NONE) (1 upto (length (binder_types T)))))
        preds
  in 
    (* remove not_False_eq_True when simpset in prove_match is better *)
    simp_tac (HOL_basic_ss addsimps
      (@{thms "HOL.simp_thms"} @ (@{thm not_False_eq_True} :: @{thm eval_pred} :: defs))) 1 
    (* need better control here! *)
  end

fun prove_clause thy nargs modes (iss, is) (_, clauses) (ts, moded_ps) =
  let
    val (in_ts, clause_out_ts) = split_smode is ts;
    fun prove_prems out_ts [] =
      (prove_match thy out_ts)
			THEN print_tac "before simplifying assumptions"
      THEN asm_full_simp_tac HOL_basic_ss' 1
			THEN print_tac "before single intro rule"
      THEN (rtac (if null clause_out_ts then @{thm singleI_unit} else @{thm singleI}) 1)
    | prove_prems out_ts ((p, mode as Mode ((iss, is), _, param_modes)) :: ps) =
      let
        val premposition = (find_index (equal p) clauses) + nargs
        val rest_tac = (case p of Prem (us, t) =>
            let
              val (_, out_ts''') = split_smode is us
              val rec_tac = prove_prems out_ts''' ps
            in
              print_tac "before clause:"
              THEN asm_simp_tac HOL_basic_ss 1
              THEN print_tac "before prove_expr:"
              THEN prove_expr thy (mode, t, us) premposition
              THEN print_tac "after prove_expr:"
              THEN rec_tac
            end
          | Negprem (us, t) =>
            let
              val (_, out_ts''') = split_smode is us
              val rec_tac = prove_prems out_ts''' ps
              val name = (case strip_comb t of (Const (c, _), _) => SOME c | _ => NONE)
              val (_, params) = strip_comb t
            in
              rtac @{thm bindI} 1
              THEN (if (is_some name) then
                  simp_tac (HOL_basic_ss addsimps [predfun_definition_of thy (the name) (iss, is)]) 1
                  THEN rtac @{thm not_predI} 1
                  THEN simp_tac (HOL_basic_ss addsimps [@{thm not_False_eq_True}]) 1
                  THEN (REPEAT_DETERM (atac 1))
                  (* FIXME: work with parameter arguments *)
                  THEN (EVERY (map (prove_param thy) (param_modes ~~ params)))
                else
                  rtac @{thm not_predI'} 1)
                  THEN simp_tac (HOL_basic_ss addsimps [@{thm not_False_eq_True}]) 1
              THEN rec_tac
            end
          | Sidecond t =>
           rtac @{thm bindI} 1
           THEN rtac @{thm if_predI} 1
           THEN print_tac "before sidecond:"
           THEN prove_sidecond thy modes t
           THEN print_tac "after sidecond:"
           THEN prove_prems [] ps)
      in (prove_match thy out_ts)
          THEN rest_tac
      end;
    val prems_tac = prove_prems in_ts moded_ps
  in
    rtac @{thm bindI} 1
    THEN rtac @{thm singleI} 1
    THEN prems_tac
  end;

fun select_sup 1 1 = []
  | select_sup _ 1 = [rtac @{thm supI1}]
  | select_sup n i = (rtac @{thm supI2})::(select_sup (n - 1) (i - 1));

fun prove_one_direction options thy clauses preds modes pred mode moded_clauses =
  let
    val T = the (AList.lookup (op =) preds pred)
    val nargs = length (binder_types T) - nparams_of thy pred
    val pred_case_rule = the_elim_of thy pred
  in
    REPEAT_DETERM (CHANGED (rewtac @{thm "split_paired_all"}))
		THEN print_tac' options "before applying elim rule"
    THEN etac (predfun_elim_of thy pred mode) 1
    THEN etac pred_case_rule 1
    THEN (EVERY (map
           (fn i => EVERY' (select_sup (length moded_clauses) i) i) 
             (1 upto (length moded_clauses))))
    THEN (EVERY (map2 (prove_clause thy nargs modes mode) clauses moded_clauses))
    THEN print_tac "proved one direction"
  end;

(** Proof in the other direction **)

fun prove_match2 thy out_ts = let
  fun split_term_tac (Free _) = all_tac
    | split_term_tac t =
      if (is_constructor thy t) then let
        val info = Datatype.the_info thy ((fst o dest_Type o fastype_of) t)
        val num_of_constrs = length (#case_rewrites info)
        (* special treatment of pairs -- because of fishing *)
        val split_rules = case (fst o dest_Type o fastype_of) t of
          "*" => [@{thm prod.split_asm}] 
          | _ => PureThy.get_thms thy (((fst o dest_Type o fastype_of) t) ^ ".split_asm")
        val (_, ts) = strip_comb t
      in
        (print_tac ("Term " ^ (Syntax.string_of_term_global thy t) ^ 
          "splitting with rules \n" ^
        commas (map (Display.string_of_thm_global thy) split_rules)))
        THEN TRY ((Splitter.split_asm_tac split_rules 1)
        THEN (print_tac "after splitting with split_asm rules")
        (* THEN (Simplifier.asm_full_simp_tac HOL_basic_ss 1)
          THEN (DETERM (TRY (etac @{thm Pair_inject} 1)))*)
          THEN (REPEAT_DETERM_N (num_of_constrs - 1) (etac @{thm botE} 1 ORELSE etac @{thm botE} 2)))
        THEN (assert_tac (Max_number_of_subgoals 2))
        THEN (EVERY (map split_term_tac ts))
      end
    else all_tac
  in
    split_term_tac (mk_tuple out_ts)
    THEN (DETERM (TRY ((Splitter.split_asm_tac [@{thm "split_if_asm"}] 1) THEN (etac @{thm botE} 2))))
  end

(* VERY LARGE SIMILIRATIY to function prove_param 
-- join both functions
*)
(* TODO: remove function *)

fun prove_param2 thy (NONE, t) = all_tac 
  | prove_param2 thy (m as SOME (Mode (mode, is, ms)), t) = let
    val  (f, args) = strip_comb (Envir.eta_contract t)
    val (params, _) = chop (length ms) args
    val f_tac = case f of
        Const (name, T) => full_simp_tac (HOL_basic_ss addsimps 
           (@{thm eval_pred}::(predfun_definition_of thy name mode)
           :: @{thm "Product_Type.split_conv"}::[])) 1
      | Free _ => all_tac
      | _ => error "prove_param2: illegal parameter term"
  in  
    print_tac "before simplification in prove_args:"
    THEN f_tac
    THEN print_tac "after simplification in prove_args"
    THEN (EVERY (map (prove_param2 thy) (ms ~~ params)))
  end


fun prove_expr2 thy (Mode (mode, is, ms), t) = 
  (case strip_comb t of
    (Const (name, T), args) =>
      etac @{thm bindE} 1
      THEN (REPEAT_DETERM (CHANGED (rewtac @{thm "split_paired_all"})))
      THEN print_tac "prove_expr2-before"
      THEN (debug_tac (Syntax.string_of_term_global thy
        (prop_of (predfun_elim_of thy name mode))))
      THEN (etac (predfun_elim_of thy name mode) 1)
      THEN print_tac "prove_expr2"
      THEN (EVERY (map (prove_param2 thy) (ms ~~ args)))
      THEN print_tac "finished prove_expr2"      
    | _ => etac @{thm bindE} 1)
    
(* FIXME: what is this for? *)
(* replace defined by has_mode thy pred *)
(* TODO: rewrite function *)
fun prove_sidecond2 thy modes t = let
  fun preds_of t nameTs = case strip_comb t of 
    (f as Const (name, T), args) =>
      if AList.defined (op =) modes name then (name, T) :: nameTs
        else fold preds_of args nameTs
    | _ => nameTs
  val preds = preds_of t []
  val defs = map
    (fn (pred, T) => predfun_definition_of thy pred 
      ([], map (rpair NONE) (1 upto (length (binder_types T)))))
      preds
  in
   (* only simplify the one assumption *)
   full_simp_tac (HOL_basic_ss' addsimps @{thm eval_pred} :: defs) 1 
   (* need better control here! *)
   THEN print_tac "after sidecond2 simplification"
   end
  
fun prove_clause2 thy modes pred (iss, is) (ts, ps) i =
  let
    val pred_intro_rule = nth (intros_of thy pred) (i - 1)
    val (in_ts, clause_out_ts) = split_smode is ts;
    fun prove_prems2 out_ts [] =
      print_tac "before prove_match2 - last call:"
      THEN prove_match2 thy out_ts
      THEN print_tac "after prove_match2 - last call:"
      THEN (etac @{thm singleE} 1)
      THEN (REPEAT_DETERM (etac @{thm Pair_inject} 1))
      THEN (asm_full_simp_tac HOL_basic_ss' 1)
      THEN (REPEAT_DETERM (etac @{thm Pair_inject} 1))
      THEN (asm_full_simp_tac HOL_basic_ss' 1)
      THEN SOLVED (print_tac "state before applying intro rule:"
      THEN (rtac pred_intro_rule 1)
      (* How to handle equality correctly? *)
      THEN (print_tac "state before assumption matching")
      THEN (REPEAT (atac 1 ORELSE 
         (CHANGED (asm_full_simp_tac (HOL_basic_ss' addsimps
					 [@{thm split_eta}, @{thm "split_beta"}, @{thm "fst_conv"}, @{thm "snd_conv"}, @{thm pair_collapse}]) 1)
          THEN print_tac "state after simp_tac:"))))
    | prove_prems2 out_ts ((p, mode as Mode ((iss, is), _, param_modes)) :: ps) =
      let
        val rest_tac = (case p of
          Prem (us, t) =>
          let
            val (_, out_ts''') = split_smode is us
            val rec_tac = prove_prems2 out_ts''' ps
          in
            (prove_expr2 thy (mode, t)) THEN rec_tac
          end
        | Negprem (us, t) =>
          let
            val (_, out_ts''') = split_smode is us
            val rec_tac = prove_prems2 out_ts''' ps
            val name = (case strip_comb t of (Const (c, _), _) => SOME c | _ => NONE)
            val (_, params) = strip_comb t
          in
            print_tac "before neg prem 2"
            THEN etac @{thm bindE} 1
            THEN (if is_some name then
                full_simp_tac (HOL_basic_ss addsimps [predfun_definition_of thy (the name) (iss, is)]) 1 
                THEN etac @{thm not_predE} 1
                THEN simp_tac (HOL_basic_ss addsimps [@{thm not_False_eq_True}]) 1
                THEN (EVERY (map (prove_param2 thy) (param_modes ~~ params)))
              else
                etac @{thm not_predE'} 1)
            THEN rec_tac
          end 
        | Sidecond t =>
          etac @{thm bindE} 1
          THEN etac @{thm if_predE} 1
          THEN prove_sidecond2 thy modes t 
          THEN prove_prems2 [] ps)
      in print_tac "before prove_match2:"
         THEN prove_match2 thy out_ts
         THEN print_tac "after prove_match2:"
         THEN rest_tac
      end;
    val prems_tac = prove_prems2 in_ts ps 
  in
    print_tac "starting prove_clause2"
    THEN etac @{thm bindE} 1
    THEN (etac @{thm singleE'} 1)
    THEN (TRY (etac @{thm Pair_inject} 1))
    THEN print_tac "after singleE':"
    THEN prems_tac
  end;
 
fun prove_other_direction thy modes pred mode moded_clauses =
  let
    fun prove_clause clause i =
      (if i < length moded_clauses then etac @{thm supE} 1 else all_tac)
      THEN (prove_clause2 thy modes pred mode clause i)
  in
    (DETERM (TRY (rtac @{thm unit.induct} 1)))
     THEN (REPEAT_DETERM (CHANGED (rewtac @{thm split_paired_all})))
     THEN (rtac (predfun_intro_of thy pred mode) 1)
     THEN (REPEAT_DETERM (rtac @{thm refl} 2))
     THEN (EVERY (map2 prove_clause moded_clauses (1 upto (length moded_clauses))))
  end;

(** proof procedure **)

fun prove_pred options thy clauses preds modes pred mode (moded_clauses, compiled_term) =
  let
    val ctxt = ProofContext.init thy
    val clauses = the (AList.lookup (op =) clauses pred)
  in
    Goal.prove ctxt (Term.add_free_names compiled_term []) [] compiled_term
      (if !do_proofs then
        (fn _ =>
        rtac @{thm pred_iffI} 1
				THEN print_tac' options "after pred_iffI"
        THEN prove_one_direction options thy clauses preds modes pred mode moded_clauses
        THEN print_tac' options "proved one direction"
        THEN prove_other_direction thy modes pred mode moded_clauses
        THEN print_tac' options "proved other direction")
      else (fn _ => setmp quick_and_dirty true SkipProof.cheat_tac thy))
  end;

(* composition of mode inference, definition, compilation and proof *)

(** auxillary combinators for table of preds and modes **)

fun map_preds_modes f preds_modes_table =
  map (fn (pred, modes) =>
    (pred, map (fn (mode, value) => (mode, f pred mode value)) modes)) preds_modes_table

fun join_preds_modes table1 table2 =
  map_preds_modes (fn pred => fn mode => fn value =>
    (value, the (AList.lookup (op =) (the (AList.lookup (op =) table2 pred)) mode))) table1
    
fun maps_modes preds_modes_table =
  map (fn (pred, modes) =>
    (pred, map (fn (mode, value) => value) modes)) preds_modes_table  
    
fun compile_preds compfuns mk_fun_of use_size thy all_vs param_vs preds moded_clauses =
  map_preds_modes (fn pred => compile_pred compfuns mk_fun_of use_size thy all_vs param_vs pred
      (the (AList.lookup (op =) preds pred))) moded_clauses  
  
fun prove options thy clauses preds modes moded_clauses compiled_terms =
  map_preds_modes (prove_pred options thy clauses preds modes)
    (join_preds_modes moded_clauses compiled_terms)

fun prove_by_skip options thy _ _ _ _ compiled_terms =
  map_preds_modes (fn pred => fn mode => fn t => Drule.standard (setmp quick_and_dirty true (SkipProof.make_thm thy) t))
    compiled_terms

fun dest_prem thy params t =
  (case strip_comb t of
    (v as Free _, ts) => if v mem params then Prem (ts, v) else Sidecond t
  | (c as Const (@{const_name Not}, _), [t]) => (case dest_prem thy params t of          
      Prem (ts, t) => Negprem (ts, t)
    | Negprem _ => error ("Double negation not allowed in premise: " ^ (Syntax.string_of_term_global thy (c $ t))) 
    | Sidecond t => Sidecond (c $ t))
  | (c as Const (s, _), ts) =>
    if is_registered thy s then
      let val (ts1, ts2) = chop (nparams_of thy s) ts
      in Prem (ts2, list_comb (c, ts1)) end
    else Sidecond t
  | _ => Sidecond t)
    
fun prepare_intrs thy prednames intros =
  let
    val intrs = map prop_of intros
    val nparams = nparams_of thy (hd prednames)
    val preds = distinct (fn ((c1, _), (c2, _)) => c1 = c2) (map (dest_Const o fst o (strip_intro_concl nparams)) intrs)
    val (preds, intrs) = unify_consts thy (map Const preds) intrs
    val ([preds, intrs], _) = fold_burrow (Variable.import_terms false) [preds, intrs] (ProofContext.init thy)
    val preds = map dest_Const preds
    val extra_modes = all_modes_of thy |> filter_out (fn (name, _) => member (op =) prednames name)
    val _ $ u = Logic.strip_imp_concl (hd intrs);
    val params = List.take (snd (strip_comb u), nparams);
    val param_vs = maps term_vs params
    val all_vs = terms_vs intrs
    fun add_clause intr (clauses, arities) =
    let
      val _ $ t = Logic.strip_imp_concl intr;
      val (Const (name, T), ts) = strip_comb t;
      val (ts1, ts2) = chop nparams ts;
      val prems = map (dest_prem thy params o HOLogic.dest_Trueprop) (Logic.strip_imp_prems intr);
      val (Ts, Us) = chop nparams (binder_types T)
    in
      (AList.update op = (name, these (AList.lookup op = clauses name) @
        [(ts2, prems)]) clauses,
       AList.update op = (name, (map (fn U => (case strip_type U of
                 (Rs as _ :: _, Type ("bool", [])) => SOME (length Rs)
               | _ => NONE)) Ts,
             length Us)) arities)
    end;
    val (clauses, arities) = fold add_clause intrs ([], []);
    fun modes_of_arities arities =
      (map (fn (s, (ks, k)) => (s, cprod (cprods (map
            (fn NONE => [NONE]
              | SOME k' => map SOME (map (map (rpair NONE)) (subsets 1 k'))) ks),
       map (map (rpair NONE)) (subsets 1 k)))) arities)
    fun modes_of_typ T =
      let
        val (Ts, Us) = chop nparams (binder_types T)
        fun all_smodes_of_typs Ts = cprods_subset (
          map_index (fn (i, U) =>
            case HOLogic.strip_tupleT U of
              [] => [(i + 1, NONE)]
            | [U] => [(i + 1, NONE)]
            | Us =>  (i + 1, NONE) ::
              (map (pair (i + 1) o SOME) ((subsets 1 (length Us)) \\ [[], 1 upto (length Us)])))
          Ts)
      in
        cprod (cprods (map (fn T => case strip_type T of
          (Rs as _ :: _, Type ("bool", [])) => map SOME (all_smodes_of_typs Rs) | _ => [NONE]) Ts),
           all_smodes_of_typs Us)
      end
    val all_modes = map (fn (s, T) => (s, modes_of_typ T)) preds
  in (preds, nparams, all_vs, param_vs, extra_modes, clauses, all_modes) end;

fun check_format_of_intro_rule thy intro =
  let
    val concl = Logic.strip_imp_concl (prop_of intro)
    val (p, args) = strip_comb (HOLogic.dest_Trueprop concl)
    val params = List.take (args, nparams_of thy (fst (dest_Const p)))
    fun check_arg arg = case HOLogic.strip_tupleT (fastype_of arg) of
      (Ts as _ :: _ :: _) =>
        if (length (HOLogic.strip_tuple arg) = length Ts) then true
        else
        error ("Format of introduction rule is invalid: tuples must be expanded:"
        ^ (Syntax.string_of_term_global thy arg) ^ " in " ^
        (Display.string_of_thm_global thy intro)) 
      | _ => true
    val prems = Logic.strip_imp_prems (prop_of intro)
    fun check_prem (Prem (args, _)) = forall check_arg args
      | check_prem (Negprem (args, _)) = forall check_arg args
      | check_prem _ = true
  in
    forall check_arg args andalso
    forall (check_prem o dest_prem thy params o HOLogic.dest_Trueprop) prems
  end

(*
fun check_intros_elim_match thy prednames =
  let
    fun check predname =
      let
        val intros = intros_of thy predname
        val elim = the_elim_of thy predname
        val nparams = nparams_of thy predname
        val elim' =
          (Drule.standard o (setmp quick_and_dirty true (SkipProof.make_thm thy)))
          (mk_casesrule (ProofContext.init thy) nparams intros)
      in
        if not (Thm.equiv_thm (elim, elim')) then
          error "Introduction and elimination rules do not match!"
        else true
      end
  in forall check prednames end
*)


(** main function of predicate compiler **)

fun add_equations_of steps options prednames thy =
  let
    val _ = print_step options ("Starting predicate compiler for predicates " ^ commas prednames ^ "...")
    val _ = tracing (commas (map (Display.string_of_thm_global thy) (maps (intros_of thy) prednames)))
      (*val _ = check_intros_elim_match thy prednames*)
      (*val _ = map (check_format_of_intro_rule thy) (maps (intros_of thy) prednames)*)
    val (preds, nparams, all_vs, param_vs, extra_modes, clauses, all_modes) =
      prepare_intrs thy prednames (maps (intros_of thy) prednames)
    val _ = print_step options "Infering modes..."
    val moded_clauses = #infer_modes steps options thy extra_modes all_modes param_vs clauses 
    val modes = map (fn (p, mps) => (p, map fst mps)) moded_clauses
    val _ = check_expected_modes options modes
    val _ = print_modes modes
    val _ = print_moded_clauses thy moded_clauses
    val _ = print_step options "Defining executable functions..."
    val thy' = fold (#create_definitions steps preds) modes thy
      |> Theory.checkpoint
    val _ = print_step options "Compiling equations..."
    val compiled_terms =
      (#compile_preds steps) thy' all_vs param_vs preds moded_clauses
    val _ = print_compiled_terms thy' compiled_terms
    val _ = print_step options "Proving equations..."
    val result_thms = #prove steps options thy' clauses preds (extra_modes @ modes)
      moded_clauses compiled_terms
    val qname = #qname steps
    (* val attrib = gn thy => Attrib.attribute_i thy Code.add_eqn_attrib *)
    val attrib = fn thy => Attrib.attribute_i thy (Attrib.internal (K (Thm.declaration_attribute
      (fn thm => Context.mapping (Code.add_eqn thm) I))))
    val thy'' = fold (fn (name, result_thms) => fn thy => snd (PureThy.add_thmss
      [((Binding.qualify true (Long_Name.base_name name) (Binding.name qname), result_thms),
        [attrib thy ])] thy))
      (maps_modes result_thms) thy'
      |> Theory.checkpoint
  in
    thy''
  end

fun extend' value_of edges_of key (G, visited) =
  let
    val (G', v) = case try (Graph.get_node G) key of
        SOME v => (G, v)
      | NONE => (Graph.new_node (key, value_of key) G, value_of key)
    val (G'', visited') = fold (extend' value_of edges_of) (edges_of (key, v) \\ visited)
      (G', key :: visited) 
  in
    (fold (Graph.add_edge o (pair key)) (edges_of (key, v)) G'', visited')
  end;

fun extend value_of edges_of key G = fst (extend' value_of edges_of key (G, [])) 
  
fun gen_add_equations steps options names thy =
  let
    val thy' = PredData.map (fold (extend (fetch_pred_data thy) (depending_preds_of thy)) names) thy
      |> Theory.checkpoint;
    fun strong_conn_of gr keys =
      Graph.strong_conn (Graph.subgraph (member (op =) (Graph.all_succs gr keys)) gr)
    val scc = strong_conn_of (PredData.get thy') names
    val thy'' = fold_rev
      (fn preds => fn thy =>
        if #are_not_defined steps thy preds then
          add_equations_of steps options preds thy else thy)
      scc thy' |> Theory.checkpoint
  in thy'' end

(* different instantiantions of the predicate compiler *)

val add_equations = gen_add_equations
  {infer_modes = infer_modes,
  create_definitions = create_definitions,
  compile_preds = compile_preds PredicateCompFuns.compfuns mk_fun_of false,
  prove = prove,
  are_not_defined = fn thy => forall (null o modes_of thy),
  qname = "equation"}

val add_sizelim_equations = gen_add_equations
  {infer_modes = infer_modes,
  create_definitions = sizelim_create_definitions,
  compile_preds = compile_preds PredicateCompFuns.compfuns mk_sizelim_fun_of true,
  prove = prove_by_skip,
  are_not_defined = fn thy => forall (null o sizelim_modes_of thy),
  qname = "sizelim_equation"
  }

val add_quickcheck_equations = gen_add_equations
  {infer_modes = infer_modes_with_generator,
  create_definitions = rpred_create_definitions,
  compile_preds = compile_preds RPredCompFuns.compfuns mk_generator_of true,
  prove = prove_by_skip,
  are_not_defined = fn thy => forall (null o rpred_modes_of thy),
  qname = "rpred_equation"}

(** user interface **)

(* code_pred_intro attribute *)

fun attrib f = Thm.declaration_attribute (fn thm => Context.mapping (f thm) I);

val code_pred_intros_attrib = attrib add_intro;


(*FIXME
- Naming of auxiliary rules necessary?
- add default code equations P x y z = P_i_i_i x y z
*)

val setup = PredData.put (Graph.empty) #>
  Attrib.setup @{binding code_pred_intros} (Scan.succeed (attrib add_intro))
    "adding alternative introduction rules for code generation of inductive predicates"
  (*FIXME name discrepancy in attribs and ML code*)
  (*FIXME intros should be better named intro*)

(* TODO: make TheoryDataFun to GenericDataFun & remove duplication of local theory and theory *)
fun generic_code_pred prep_const options raw_const lthy =
  let
    val thy = ProofContext.theory_of lthy
    val const = prep_const thy raw_const
    val lthy' = LocalTheory.theory (PredData.map
        (extend (fetch_pred_data thy) (depending_preds_of thy) const)) lthy
      |> LocalTheory.checkpoint
    val thy' = ProofContext.theory_of lthy'
    val preds = Graph.all_preds (PredData.get thy') [const] |> filter_out (has_elim thy')
    fun mk_cases const =
      let
        val nparams = nparams_of thy' const
        val intros = intros_of thy' const
      in mk_casesrule lthy' nparams intros end  
    val cases_rules = map mk_cases preds
    val cases =
      map (fn case_rule => RuleCases.Case {fixes = [],
        assumes = [("", Logic.strip_imp_prems case_rule)],
        binds = [], cases = []}) cases_rules
    val case_env = map2 (fn p => fn c => (Long_Name.base_name p, SOME c)) preds cases
    val lthy'' = lthy'
      |> fold Variable.auto_fixes cases_rules 
      |> ProofContext.add_cases true case_env
    fun after_qed thms goal_ctxt =
      let
        val global_thms = ProofContext.export goal_ctxt
          (ProofContext.init (ProofContext.theory_of goal_ctxt)) (map the_single thms)
      in
        goal_ctxt |> LocalTheory.theory (fold set_elim global_thms #>
          (if is_rpred options then
            (add_equations options [const] #>
             add_sizelim_equations options [const] #> add_quickcheck_equations options [const])
           else if is_sizelim options then
             add_sizelim_equations options [const]
           else
             add_equations options [const]))
      end  
  in
    Proof.theorem_i NONE after_qed (map (single o (rpair [])) cases_rules) lthy''
  end;

val code_pred = generic_code_pred (K I);
val code_pred_cmd = generic_code_pred Code.read_const

(* transformation for code generation *)

val eval_ref = Unsynchronized.ref (NONE : (unit -> term Predicate.pred) option);

(*FIXME turn this into an LCF-guarded preprocessor for comprehensions*)
fun analyze_compr thy t_compr =
  let
    val split = case t_compr of (Const (@{const_name Collect}, _) $ t) => t
      | _ => error ("Not a set comprehension: " ^ Syntax.string_of_term_global thy t_compr);
    val (body, Ts, fp) = HOLogic.strip_psplits split;
    val (pred as Const (name, T), all_args) = strip_comb body;
    val (params, args) = chop (nparams_of thy name) all_args;
    val user_mode = map_filter I (map_index
      (fn (i, t) => case t of Bound j => if j < length Ts then NONE
        else SOME (i+1) | _ => SOME (i+1)) args); (*FIXME dangling bounds should not occur*)
    val user_mode' = map (rpair NONE) user_mode
    val modes = filter (fn Mode (_, is, _) => is = user_mode')
      (modes_of_term (all_modes_of thy) (list_comb (pred, params)));
    val m = case modes
     of [] => error ("No mode possible for comprehension "
                ^ Syntax.string_of_term_global thy t_compr)
      | [m] => m
      | m :: _ :: _ => (warning ("Multiple modes possible for comprehension "
                ^ Syntax.string_of_term_global thy t_compr); m);
    val (inargs, outargs) = split_smode user_mode' args;
    val t_pred = list_comb (compile_expr NONE thy (m, list_comb (pred, params)), inargs);
    val t_eval = if null outargs then t_pred else
      let
        val outargs_bounds = map (fn Bound i => i) outargs;
        val outargsTs = map (nth Ts) outargs_bounds;
        val T_pred = HOLogic.mk_tupleT outargsTs;
        val T_compr = HOLogic.mk_ptupleT fp Ts;
        val arrange_bounds = map_index I outargs_bounds
          |> sort (prod_ord (K EQUAL) int_ord)
          |> map fst;
        val arrange = funpow (length outargs_bounds - 1) HOLogic.mk_split
          (Term.list_abs (map (pair "") outargsTs,
            HOLogic.mk_ptuple fp T_compr (map Bound arrange_bounds)))
      in mk_map PredicateCompFuns.compfuns T_pred T_compr arrange t_pred end
  in t_eval end;

fun eval thy t_compr =
  let
    val t = analyze_compr thy t_compr;
    val T = dest_predT PredicateCompFuns.compfuns (fastype_of t);
    val t' = mk_map PredicateCompFuns.compfuns T HOLogic.termT (HOLogic.term_of_const T) t;
  in (T, Code_ML.eval NONE ("Predicate_Compile_Core.eval_ref", eval_ref) Predicate.map thy t' []) end;

fun values ctxt k t_compr =
  let
    val thy = ProofContext.theory_of ctxt;
    val (T, t) = eval thy t_compr;
    val setT = HOLogic.mk_setT T;
    val (ts, _) = Predicate.yieldn k t;
    val elemsT = HOLogic.mk_set T ts;
  in if k = ~1 orelse length ts < k then elemsT
    else Const (@{const_name Set.union}, setT --> setT --> setT) $ elemsT $ t_compr
  end;
  (*
fun random_values ctxt k t = 
  let
    val thy = ProofContext.theory_of ctxt
    val _ = 
  in
  end;
  *)
fun values_cmd modes k raw_t state =
  let
    val ctxt = Toplevel.context_of state;
    val t = Syntax.read_term ctxt raw_t;
    val t' = values ctxt k t;
    val ty' = Term.type_of t';
    val ctxt' = Variable.auto_fixes t' ctxt;
    val p = PrintMode.with_modes modes (fn () =>
      Pretty.block [Pretty.quote (Syntax.pretty_term ctxt' t'), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ ctxt' ty')]) ();
  in Pretty.writeln p end;

local structure P = OuterParse in

val opt_modes = Scan.optional (P.$$$ "(" |-- P.!!! (Scan.repeat1 P.xname --| P.$$$ ")")) [];

val _ = OuterSyntax.improper_command "values" "enumerate and print comprehensions" OuterKeyword.diag
  (opt_modes -- Scan.optional P.nat ~1 -- P.term
    >> (fn ((modes, k), t) => Toplevel.no_timing o Toplevel.keep
        (values_cmd modes k t)));

end;

end;
