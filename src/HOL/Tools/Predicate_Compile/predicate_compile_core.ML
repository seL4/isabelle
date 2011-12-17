(*  Title:      HOL/Tools/Predicate_Compile/predicate_compile_core.ML
    Author:     Lukas Bulwahn, TU Muenchen

A compiler from predicates specified by intro/elim rules to equations.
*)

signature PREDICATE_COMPILE_CORE =
sig
  type mode = Predicate_Compile_Aux.mode
  type options = Predicate_Compile_Aux.options
  type compilation = Predicate_Compile_Aux.compilation
  type compilation_funs = Predicate_Compile_Aux.compilation_funs
  
  val setup : theory -> theory
  val code_pred : options -> string -> Proof.context -> Proof.state
  val code_pred_cmd : options -> string -> Proof.context -> Proof.state
  val values_cmd : string list -> mode option list option
    -> ((string option * bool) * (compilation * int list)) -> int -> string -> Toplevel.state -> unit

  val values_timeout : real Config.T
  
  val print_stored_rules : Proof.context -> unit
  val print_all_modes : compilation -> Proof.context -> unit

  val put_pred_result : (unit -> term Predicate.pred) -> Proof.context -> Proof.context
  val put_pred_random_result : (unit -> int * int -> term Predicate.pred * (int * int)) ->
    Proof.context -> Proof.context
  val put_dseq_result : (unit -> term DSequence.dseq) -> Proof.context -> Proof.context
  val put_dseq_random_result : (unit -> int -> int -> int * int -> term DSequence.dseq * (int * int)) ->
    Proof.context -> Proof.context
  val put_new_dseq_result : (unit -> int -> term Lazy_Sequence.lazy_sequence) ->
    Proof.context -> Proof.context
  val put_lseq_random_result :
    (unit -> int -> int -> int * int -> int -> term Lazy_Sequence.lazy_sequence) ->
    Proof.context -> Proof.context
  val put_lseq_random_stats_result :
    (unit -> int -> int -> int * int -> int -> (term * int) Lazy_Sequence.lazy_sequence) ->
    Proof.context -> Proof.context

  val code_pred_intro_attrib : attribute
  (* used by Quickcheck_Generator *) 
  (* temporary for testing of the compilation *)
  val add_equations : options -> string list -> theory -> theory
  val add_depth_limited_random_equations : options -> string list -> theory -> theory
  val add_random_dseq_equations : options -> string list -> theory -> theory
  val add_new_random_dseq_equations : options -> string list -> theory -> theory
  val add_generator_dseq_equations : options -> string list -> theory -> theory
  val add_generator_cps_equations : options -> string list -> theory -> theory
  val mk_tracing : string -> term -> term
  val prepare_intrs : options -> Proof.context -> string list -> thm list ->
    ((string * typ) list * string list * string list * (string * mode list) list *
      (string *  (Term.term list * Predicate_Compile_Aux.indprem list) list) list)
  type mode_analysis_options =
   {use_generators : bool,
    reorder_premises : bool,
    infer_pos_and_neg_modes : bool}  
  datatype mode_derivation = Mode_App of mode_derivation * mode_derivation | Context of mode
    | Mode_Pair of mode_derivation * mode_derivation | Term of mode
  val head_mode_of : mode_derivation -> mode
  type moded_clause = term list * (Predicate_Compile_Aux.indprem * mode_derivation) list
  type 'a pred_mode_table = (string * ((bool * mode) * 'a) list) list

end;

structure Predicate_Compile_Core : PREDICATE_COMPILE_CORE =
struct

open Predicate_Compile_Aux;
open Core_Data;
open Mode_Inference;
open Predicate_Compile_Proof;

(** fundamentals **)

(* syntactic operations *)

fun mk_eq (x, xs) =
  let fun mk_eqs _ [] = []
        | mk_eqs a (b::cs) =
            HOLogic.mk_eq (Free (a, fastype_of b), b) :: mk_eqs a cs
  in mk_eqs x xs end;

fun mk_scomp (t, u) =
  let
    val T = fastype_of t
    val U = fastype_of u
    val [A] = binder_types T
    val D = body_type U                   
  in 
    Const (@{const_name "scomp"}, T --> U --> A --> D) $ t $ u
  end;

fun dest_randomT (Type ("fun", [@{typ Random.seed},
  Type (@{type_name Product_Type.prod}, [Type (@{type_name Product_Type.prod}, [T, @{typ "unit => Code_Evaluation.term"}]) ,@{typ Random.seed}])])) = T
  | dest_randomT T = raise TYPE ("dest_randomT", [T], [])

fun mk_tracing s t =
  Const(@{const_name Code_Evaluation.tracing},
    @{typ String.literal} --> (fastype_of t) --> (fastype_of t)) $ (HOLogic.mk_literal s) $ t

(* representation of inferred clauses with modes *)

type moded_clause = term list * (indprem * mode_derivation) list

type 'a pred_mode_table = (string * ((bool * mode) * 'a) list) list

(* diagnostic display functions *)

fun print_modes options modes =
  if show_modes options then
    tracing ("Inferred modes:\n" ^
      cat_lines (map (fn (s, ms) => s ^ ": " ^ commas (map
        (fn (p, m) => string_of_mode m ^ (if p then "pos" else "neg")) ms)) modes))
  else ()

fun print_pred_mode_table string_of_entry pred_mode_table =
  let
    fun print_mode pred ((pol, mode), entry) =  "mode : " ^ string_of_mode mode
      ^ string_of_entry pred mode entry
    fun print_pred (pred, modes) =
      "predicate " ^ pred ^ ": " ^ cat_lines (map (print_mode pred) modes)
    val _ = tracing (cat_lines (map print_pred pred_mode_table))
  in () end;

fun print_compiled_terms options ctxt =
  if show_compilation options then
    print_pred_mode_table (fn _ => fn _ => Syntax.string_of_term ctxt)
  else K ()

fun print_stored_rules ctxt =
  let
    val preds = Graph.keys (PredData.get (Proof_Context.theory_of ctxt))
    fun print pred () = let
      val _ = writeln ("predicate: " ^ pred)
      val _ = writeln ("introrules: ")
      val _ = fold (fn thm => fn u => writeln (Display.string_of_thm ctxt thm))
        (rev (intros_of ctxt pred)) ()
    in
      if (has_elim ctxt pred) then
        writeln ("elimrule: " ^ Display.string_of_thm ctxt (the_elim_of ctxt pred))
      else
        writeln ("no elimrule defined")
    end
  in
    fold print preds ()
  end;

fun print_all_modes compilation ctxt =
  let
    val _ = writeln ("Inferred modes:")
    fun print (pred, modes) u =
      let
        val _ = writeln ("predicate: " ^ pred)
        val _ = writeln ("modes: " ^ (commas (map string_of_mode modes)))
      in u end
  in
    fold print (all_modes_of compilation ctxt) ()
  end

(* validity checks *)

fun check_expected_modes options preds modes =
  case expected_modes options of
    SOME (s, ms) => (case AList.lookup (op =) modes s of
      SOME modes =>
        let
          val modes' = map snd modes
        in
          if not (eq_set eq_mode (ms, modes')) then
            error ("expected modes were not inferred:\n"
            ^ "  inferred modes for " ^ s ^ ": " ^ commas (map string_of_mode modes')  ^ "\n"
            ^ "  expected modes for " ^ s ^ ": " ^ commas (map string_of_mode ms))
          else ()
        end
      | NONE => ())
  | NONE => ()

fun check_proposed_modes options preds modes errors =
  map (fn (s, _) => case proposed_modes options s of
    SOME ms => (case AList.lookup (op =) modes s of
      SOME inferred_ms =>
        let
          val preds_without_modes = map fst (filter (null o snd) modes)
          val modes' = map snd inferred_ms
        in
          if not (eq_set eq_mode (ms, modes')) then
            error ("expected modes were not inferred:\n"
            ^ "  inferred modes for " ^ s ^ ": " ^ commas (map string_of_mode modes')  ^ "\n"
            ^ "  expected modes for " ^ s ^ ": " ^ commas (map string_of_mode ms) ^ "\n"
            ^ (if show_invalid_clauses options then
            ("For the following clauses, the following modes could not be inferred: " ^ "\n"
            ^ cat_lines errors) else "") ^
            (if not (null preds_without_modes) then
              "\n" ^ "No mode inferred for the predicates " ^ commas preds_without_modes
            else ""))
          else ()
        end
      | NONE => ())
  | NONE => ()) preds

fun check_matches_type ctxt predname T ms =
  let
    fun check (m as Fun (m1, m2)) (Type("fun", [T1,T2])) = check m1 T1 andalso check m2 T2
      | check m (T as Type("fun", _)) = (m = Input orelse m = Output)
      | check (Pair (m1, m2)) (Type (@{type_name Product_Type.prod}, [T1, T2])) =
          check m1 T1 andalso check m2 T2 
      | check Input T = true
      | check Output T = true
      | check Bool @{typ bool} = true
      | check _ _ = false
    fun check_consistent_modes ms =
      if forall (fn Fun (m1', m2') => true | _ => false) ms then
        pairself check_consistent_modes (split_list (map (fn Fun (m1, m2) => (m1, m2)) ms))
        |> (fn (res1, res2) => res1 andalso res2) 
      else if forall (fn Input => true | Output => true | Pair _ => true | _ => false) ms then
        true
      else if forall (fn Bool => true | _ => false) ms then
        true
      else
        false
    val _ = map
      (fn mode =>
        if length (strip_fun_mode mode) = length (binder_types T)
          andalso (forall (uncurry check) (strip_fun_mode mode ~~ binder_types T)) then ()
        else error (string_of_mode mode ^ " is not a valid mode for " ^ Syntax.string_of_typ ctxt T
        ^ " at predicate " ^ predname)) ms
    val _ =
     if check_consistent_modes ms then ()
     else error (commas (map string_of_mode ms) ^
       " are inconsistent modes for predicate " ^ predname)
  in
    ms
  end

(* compilation modifiers *)

structure Comp_Mod =
struct

datatype comp_modifiers = Comp_Modifiers of
{
  compilation : compilation,
  function_name_prefix : string,
  compfuns : compilation_funs,
  mk_random : typ -> term list -> term,
  modify_funT : typ -> typ,
  additional_arguments : string list -> term list,
  wrap_compilation : compilation_funs -> string -> typ -> mode -> term list -> term -> term,
  transform_additional_arguments : indprem -> term list -> term list
}

fun dest_comp_modifiers (Comp_Modifiers c) = c

val compilation = #compilation o dest_comp_modifiers
val function_name_prefix = #function_name_prefix o dest_comp_modifiers
val compfuns = #compfuns o dest_comp_modifiers

val mk_random = #mk_random o dest_comp_modifiers
val funT_of' = funT_of o compfuns
val modify_funT = #modify_funT o dest_comp_modifiers
fun funT_of comp mode = modify_funT comp o funT_of' comp mode

val additional_arguments = #additional_arguments o dest_comp_modifiers
val wrap_compilation = #wrap_compilation o dest_comp_modifiers
val transform_additional_arguments = #transform_additional_arguments o dest_comp_modifiers

fun set_compfuns compfuns' (Comp_Modifiers {compilation, function_name_prefix, compfuns, mk_random,
    modify_funT, additional_arguments, wrap_compilation, transform_additional_arguments}) =
    (Comp_Modifiers {compilation = compilation, function_name_prefix = function_name_prefix,
    compfuns = compfuns', mk_random = mk_random, modify_funT = modify_funT,
    additional_arguments = additional_arguments, wrap_compilation = wrap_compilation,
    transform_additional_arguments = transform_additional_arguments})

end;

fun unlimited_compfuns_of true New_Pos_Random_DSeq =
    New_Pos_Random_Sequence_CompFuns.depth_unlimited_compfuns
  | unlimited_compfuns_of false New_Pos_Random_DSeq =
    New_Neg_Random_Sequence_CompFuns.depth_unlimited_compfuns
  | unlimited_compfuns_of true Pos_Generator_DSeq =
    New_Pos_DSequence_CompFuns.depth_unlimited_compfuns
  | unlimited_compfuns_of false Pos_Generator_DSeq =
    New_Neg_DSequence_CompFuns.depth_unlimited_compfuns
  | unlimited_compfuns_of _ c =
    raise Fail ("No unlimited compfuns for compilation " ^ string_of_compilation c)

fun limited_compfuns_of true Predicate_Compile_Aux.New_Pos_Random_DSeq =
    New_Pos_Random_Sequence_CompFuns.depth_limited_compfuns
  | limited_compfuns_of false Predicate_Compile_Aux.New_Pos_Random_DSeq =
    New_Neg_Random_Sequence_CompFuns.depth_limited_compfuns
  | limited_compfuns_of true Pos_Generator_DSeq =
    New_Pos_DSequence_CompFuns.depth_limited_compfuns
  | limited_compfuns_of false Pos_Generator_DSeq =
    New_Neg_DSequence_CompFuns.depth_limited_compfuns
  | limited_compfuns_of _ c =
    raise Fail ("No limited compfuns for compilation " ^ string_of_compilation c)

val depth_limited_comp_modifiers = Comp_Mod.Comp_Modifiers
  {
  compilation = Depth_Limited,
  function_name_prefix = "depth_limited_",
  compfuns = Predicate_Comp_Funs.compfuns,
  mk_random = (fn _ => error "no random generation"),
  additional_arguments = fn names =>
    let
      val depth_name = singleton (Name.variant_list names) "depth"
    in [Free (depth_name, @{typ code_numeral})] end,
  modify_funT = (fn T => let val (Ts, U) = strip_type T
  val Ts' = [@{typ code_numeral}] in (Ts @ Ts') ---> U end),
  wrap_compilation =
    fn compfuns => fn s => fn T => fn mode => fn additional_arguments => fn compilation =>
    let
      val [depth] = additional_arguments
      val (_, Ts) = split_modeT mode (binder_types T)
      val T' = mk_monadT compfuns (HOLogic.mk_tupleT Ts)
      val if_const = Const (@{const_name "If"}, @{typ bool} --> T' --> T' --> T')
    in
      if_const $ HOLogic.mk_eq (depth, @{term "0 :: code_numeral"})
        $ mk_empty compfuns (dest_monadT compfuns T')
        $ compilation
    end,
  transform_additional_arguments =
    fn prem => fn additional_arguments =>
    let
      val [depth] = additional_arguments
      val depth' =
        Const (@{const_name Groups.minus}, @{typ "code_numeral => code_numeral => code_numeral"})
          $ depth $ Const (@{const_name Groups.one}, @{typ "Code_Numeral.code_numeral"})
    in [depth'] end
  }

val random_comp_modifiers = Comp_Mod.Comp_Modifiers
  {
  compilation = Random,
  function_name_prefix = "random_",
  compfuns = Predicate_Comp_Funs.compfuns,
  mk_random = (fn T => fn additional_arguments =>
  list_comb (Const(@{const_name Quickcheck.iter},
  [@{typ code_numeral}, @{typ code_numeral}, @{typ Random.seed}] ---> 
    Predicate_Comp_Funs.mk_monadT T), additional_arguments)),
  modify_funT = (fn T =>
    let
      val (Ts, U) = strip_type T
      val Ts' = [@{typ code_numeral}, @{typ code_numeral}, @{typ "code_numeral * code_numeral"}]
    in (Ts @ Ts') ---> U end),
  additional_arguments = (fn names =>
    let
      val [nrandom, size, seed] = Name.variant_list names ["nrandom", "size", "seed"]
    in
      [Free (nrandom, @{typ code_numeral}), Free (size, @{typ code_numeral}),
        Free (seed, @{typ "code_numeral * code_numeral"})]
    end),
  wrap_compilation = K (K (K (K (K I))))
    : (compilation_funs -> string -> typ -> mode -> term list -> term -> term),
  transform_additional_arguments = K I : (indprem -> term list -> term list)
  }

val depth_limited_random_comp_modifiers = Comp_Mod.Comp_Modifiers
  {
  compilation = Depth_Limited_Random,
  function_name_prefix = "depth_limited_random_",
  compfuns = Predicate_Comp_Funs.compfuns,
  mk_random = (fn T => fn additional_arguments =>
  list_comb (Const(@{const_name Quickcheck.iter},
  [@{typ code_numeral}, @{typ code_numeral}, @{typ Random.seed}] ---> 
    Predicate_Comp_Funs.mk_monadT T), tl additional_arguments)),
  modify_funT = (fn T =>
    let
      val (Ts, U) = strip_type T
      val Ts' = [@{typ code_numeral}, @{typ code_numeral}, @{typ code_numeral},
        @{typ "code_numeral * code_numeral"}]
    in (Ts @ Ts') ---> U end),
  additional_arguments = (fn names =>
    let
      val [depth, nrandom, size, seed] = Name.variant_list names ["depth", "nrandom", "size", "seed"]
    in
      [Free (depth, @{typ code_numeral}), Free (nrandom, @{typ code_numeral}),
        Free (size, @{typ code_numeral}), Free (seed, @{typ "code_numeral * code_numeral"})]
    end),
  wrap_compilation =
  fn compfuns => fn s => fn T => fn mode => fn additional_arguments => fn compilation =>
    let
      val depth = hd (additional_arguments)
      val (_, Ts) = split_map_modeT (fn m => fn T => (SOME (funT_of compfuns m T), NONE))
        mode (binder_types T)
      val T' = mk_monadT compfuns (HOLogic.mk_tupleT Ts)
      val if_const = Const (@{const_name "If"}, @{typ bool} --> T' --> T' --> T')
    in
      if_const $ HOLogic.mk_eq (depth, @{term "0 :: code_numeral"})
        $ mk_empty compfuns (dest_monadT compfuns T')
        $ compilation
    end,
  transform_additional_arguments =
    fn prem => fn additional_arguments =>
    let
      val [depth, nrandom, size, seed] = additional_arguments
      val depth' =
        Const (@{const_name Groups.minus}, @{typ "code_numeral => code_numeral => code_numeral"})
          $ depth $ Const (@{const_name Groups.one}, @{typ "Code_Numeral.code_numeral"})
    in [depth', nrandom, size, seed] end
}

val predicate_comp_modifiers = Comp_Mod.Comp_Modifiers
  {
  compilation = Pred,
  function_name_prefix = "",
  compfuns = Predicate_Comp_Funs.compfuns,
  mk_random = (fn _ => error "no random generation"),
  modify_funT = I,
  additional_arguments = K [],
  wrap_compilation = K (K (K (K (K I))))
   : (compilation_funs -> string -> typ -> mode -> term list -> term -> term),
  transform_additional_arguments = K I : (indprem -> term list -> term list)
  }

val annotated_comp_modifiers = Comp_Mod.Comp_Modifiers
  {
  compilation = Annotated,
  function_name_prefix = "annotated_",
  compfuns = Predicate_Comp_Funs.compfuns,
  mk_random = (fn _ => error "no random generation"),
  modify_funT = I,
  additional_arguments = K [],
  wrap_compilation =
    fn compfuns => fn s => fn T => fn mode => fn additional_arguments => fn compilation =>
      mk_tracing ("calling predicate " ^ s ^
        " with mode " ^ string_of_mode mode) compilation,
  transform_additional_arguments = K I : (indprem -> term list -> term list)
  }

val dseq_comp_modifiers = Comp_Mod.Comp_Modifiers
  {
  compilation = DSeq,
  function_name_prefix = "dseq_",
  compfuns = DSequence_CompFuns.compfuns,
  mk_random = (fn _ => error "no random generation in dseq"),
  modify_funT = I,
  additional_arguments = K [],
  wrap_compilation = K (K (K (K (K I))))
   : (compilation_funs -> string -> typ -> mode -> term list -> term -> term),
  transform_additional_arguments = K I : (indprem -> term list -> term list)
  }

val pos_random_dseq_comp_modifiers = Comp_Mod.Comp_Modifiers
  {
  compilation = Pos_Random_DSeq,
  function_name_prefix = "random_dseq_",
  compfuns = Random_Sequence_CompFuns.compfuns,
  mk_random = (fn T => fn additional_arguments =>
  let
    val random = Const ("Quickcheck.random_class.random",
      @{typ code_numeral} --> @{typ Random.seed} -->
        HOLogic.mk_prodT (HOLogic.mk_prodT (T, @{typ "unit => term"}), @{typ Random.seed}))
  in
    Const ("Random_Sequence.Random", (@{typ code_numeral} --> @{typ Random.seed} -->
      HOLogic.mk_prodT (HOLogic.mk_prodT (T, @{typ "unit => term"}), @{typ Random.seed})) -->
      Random_Sequence_CompFuns.mk_random_dseqT T) $ random
  end),

  modify_funT = I,
  additional_arguments = K [],
  wrap_compilation = K (K (K (K (K I))))
   : (compilation_funs -> string -> typ -> mode -> term list -> term -> term),
  transform_additional_arguments = K I : (indprem -> term list -> term list)
  }

val neg_random_dseq_comp_modifiers = Comp_Mod.Comp_Modifiers
  {
  compilation = Neg_Random_DSeq,
  function_name_prefix = "random_dseq_neg_",
  compfuns = Random_Sequence_CompFuns.compfuns,
  mk_random = (fn _ => error "no random generation"),
  modify_funT = I,
  additional_arguments = K [],
  wrap_compilation = K (K (K (K (K I))))
   : (compilation_funs -> string -> typ -> mode -> term list -> term -> term),
  transform_additional_arguments = K I : (indprem -> term list -> term list)
  }


val new_pos_random_dseq_comp_modifiers = Comp_Mod.Comp_Modifiers
  {
  compilation = New_Pos_Random_DSeq,
  function_name_prefix = "new_random_dseq_",
  compfuns = New_Pos_Random_Sequence_CompFuns.depth_limited_compfuns,
  mk_random = (fn T => fn additional_arguments =>
  let
    val random = Const ("Quickcheck.random_class.random",
      @{typ code_numeral} --> @{typ Random.seed} -->
        HOLogic.mk_prodT (HOLogic.mk_prodT (T, @{typ "unit => term"}), @{typ Random.seed}))
  in
    Const ("New_Random_Sequence.Random", (@{typ code_numeral} --> @{typ Random.seed} -->
      HOLogic.mk_prodT (HOLogic.mk_prodT (T, @{typ "unit => term"}), @{typ Random.seed})) -->
      New_Pos_Random_Sequence_CompFuns.mk_pos_random_dseqT T) $ random
  end),
  modify_funT = I,
  additional_arguments = K [],
  wrap_compilation = K (K (K (K (K I))))
   : (compilation_funs -> string -> typ -> mode -> term list -> term -> term),
  transform_additional_arguments = K I : (indprem -> term list -> term list)
  }

val new_neg_random_dseq_comp_modifiers = Comp_Mod.Comp_Modifiers
  {
  compilation = New_Neg_Random_DSeq,
  function_name_prefix = "new_random_dseq_neg_",
  compfuns = New_Neg_Random_Sequence_CompFuns.depth_limited_compfuns,
  mk_random = (fn _ => error "no random generation"),
  modify_funT = I,
  additional_arguments = K [],
  wrap_compilation = K (K (K (K (K I))))
   : (compilation_funs -> string -> typ -> mode -> term list -> term -> term),
  transform_additional_arguments = K I : (indprem -> term list -> term list)
  }

val pos_generator_dseq_comp_modifiers = Comp_Mod.Comp_Modifiers
  {
  compilation = Pos_Generator_DSeq,
  function_name_prefix = "generator_dseq_",
  compfuns = New_Pos_DSequence_CompFuns.depth_limited_compfuns,
  mk_random =
    (fn T => fn additional_arguments =>
      Const (@{const_name "Lazy_Sequence.small_lazy_class.small_lazy"},
        @{typ "Code_Numeral.code_numeral"} --> Type (@{type_name "Lazy_Sequence.lazy_sequence"}, [T]))),
  modify_funT = I,
  additional_arguments = K [],
  wrap_compilation = K (K (K (K (K I))))
   : (compilation_funs -> string -> typ -> mode -> term list -> term -> term),
  transform_additional_arguments = K I : (indprem -> term list -> term list)
  }
  
val neg_generator_dseq_comp_modifiers = Comp_Mod.Comp_Modifiers
  {
  compilation = Neg_Generator_DSeq,
  function_name_prefix = "generator_dseq_neg_",
  compfuns = New_Neg_DSequence_CompFuns.depth_limited_compfuns,
  mk_random = (fn _ => error "no random generation"),
  modify_funT = I,
  additional_arguments = K [],
  wrap_compilation = K (K (K (K (K I))))
   : (compilation_funs -> string -> typ -> mode -> term list -> term -> term),
  transform_additional_arguments = K I : (indprem -> term list -> term list)
  }

val pos_generator_cps_comp_modifiers = Comp_Mod.Comp_Modifiers
  {
  compilation = Pos_Generator_CPS,
  function_name_prefix = "generator_cps_pos_",
  compfuns = Pos_Bounded_CPS_Comp_Funs.compfuns,
  mk_random =
    (fn T => fn additional_arguments =>
       Const (@{const_name "Quickcheck_Exhaustive.exhaustive"},
       (T --> @{typ "(bool * term list) option"}) -->
         @{typ "code_numeral => (bool * term list) option"})),
  modify_funT = I,
  additional_arguments = K [],
  wrap_compilation = K (K (K (K (K I))))
   : (compilation_funs -> string -> typ -> mode -> term list -> term -> term),
  transform_additional_arguments = K I : (indprem -> term list -> term list)
  }  

val neg_generator_cps_comp_modifiers = Comp_Mod.Comp_Modifiers
  {
  compilation = Neg_Generator_CPS,
  function_name_prefix = "generator_cps_neg_",
  compfuns = Neg_Bounded_CPS_Comp_Funs.compfuns,
  mk_random = (fn _ => error "No enumerators"),
  modify_funT = I,
  additional_arguments = K [],
  wrap_compilation = K (K (K (K (K I))))
   : (compilation_funs -> string -> typ -> mode -> term list -> term -> term),
  transform_additional_arguments = K I : (indprem -> term list -> term list)
  }
  
fun negative_comp_modifiers_of comp_modifiers =
    (case Comp_Mod.compilation comp_modifiers of
      Pos_Random_DSeq => neg_random_dseq_comp_modifiers
    | Neg_Random_DSeq => pos_random_dseq_comp_modifiers
    | New_Pos_Random_DSeq => new_neg_random_dseq_comp_modifiers
    | New_Neg_Random_DSeq => new_pos_random_dseq_comp_modifiers 
    | Pos_Generator_DSeq => neg_generator_dseq_comp_modifiers
    | Neg_Generator_DSeq => pos_generator_dseq_comp_modifiers
    | Pos_Generator_CPS => neg_generator_cps_comp_modifiers
    | Neg_Generator_CPS => pos_generator_cps_comp_modifiers
    | c => comp_modifiers)

(* term construction *)

fun mk_v (names, vs) s T = (case AList.lookup (op =) vs s of
      NONE => (Free (s, T), (names, (s, [])::vs))
    | SOME xs =>
        let
          val s' = singleton (Name.variant_list names) s;
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


(** specific rpred functions -- move them to the correct place in this file *)
fun mk_Eval_of (P as (Free (f, _)), T) mode =
  let
    fun mk_bounds (Type (@{type_name Product_Type.prod}, [T1, T2])) i =
          let
            val (bs2, i') = mk_bounds T2 i 
            val (bs1, i'') = mk_bounds T1 i'
          in
            (HOLogic.pair_const T1 T2 $ bs1 $ bs2, i'' + 1)
          end
      | mk_bounds T i = (Bound i, i + 1)
    fun mk_prod ((t1, T1), (t2, T2)) = (HOLogic.pair_const T1 T2 $ t1 $ t2, HOLogic.mk_prodT (T1, T2))
    fun mk_tuple [] = (HOLogic.unit, HOLogic.unitT)
      | mk_tuple tTs = foldr1 mk_prod tTs
    fun mk_split_abs (T as Type (@{type_name Product_Type.prod}, [T1, T2])) t =
          absdummy T
            (HOLogic.split_const (T1, T2, @{typ bool}) $ (mk_split_abs T1 (mk_split_abs T2 t)))
      | mk_split_abs T t = absdummy T t
    val args = rev (fst (fold_map mk_bounds (rev (binder_types T)) 0))
    val (inargs, outargs) = split_mode mode args
    val (inTs, outTs) = split_map_modeT (fn _ => fn T => (SOME T, NONE)) mode (binder_types T)
    val inner_term = Predicate_Comp_Funs.mk_Eval (list_comb (P, inargs), fst (mk_tuple (outargs ~~ outTs)))
  in
    fold_rev mk_split_abs (binder_types T) inner_term
  end

fun compile_arg compilation_modifiers additional_arguments ctxt param_modes arg = 
  let
    fun map_params (t as Free (f, T)) =
      (case (AList.lookup (op =) param_modes f) of
          SOME mode =>
            let
              val T' = Comp_Mod.funT_of compilation_modifiers mode T
            in
              mk_Eval_of (Free (f, T'), T) mode
            end
        | NONE => t)
      | map_params t = t
  in
    map_aterms map_params arg
  end

fun compile_match compilation_modifiers additional_arguments ctxt param_modes
      eqs eqs' out_ts success_t =
  let
    val compfuns = Comp_Mod.compfuns compilation_modifiers
    val eqs'' = maps mk_eq eqs @ eqs'
    val eqs'' =
      map (compile_arg compilation_modifiers additional_arguments ctxt param_modes) eqs''
    val names = fold Term.add_free_names (success_t :: eqs'' @ out_ts) [];
    val name = singleton (Name.variant_list names) "x";
    val name' = singleton (Name.variant_list (name :: names)) "y";
    val T = HOLogic.mk_tupleT (map fastype_of out_ts);
    val U = fastype_of success_t;
    val U' = dest_monadT compfuns U;
    val v = Free (name, T);
    val v' = Free (name', T);
  in
    lambda v (Datatype_Case.make_case ctxt Datatype_Case.Quiet [] v
      [(HOLogic.mk_tuple out_ts,
        if null eqs'' then success_t
        else Const (@{const_name HOL.If}, HOLogic.boolT --> U --> U --> U) $
          foldr1 HOLogic.mk_conj eqs'' $ success_t $
            mk_empty compfuns U'),
       (v', mk_empty compfuns U')])
  end;

fun string_of_tderiv ctxt (t, deriv) = 
  (case (t, deriv) of
    (t1 $ t2, Mode_App (deriv1, deriv2)) =>
      string_of_tderiv ctxt (t1, deriv1) ^ " $ " ^ string_of_tderiv ctxt (t2, deriv2)
  | (Const (@{const_name Pair}, _) $ t1 $ t2, Mode_Pair (deriv1, deriv2)) =>
    "(" ^ string_of_tderiv ctxt (t1, deriv1) ^ ", " ^ string_of_tderiv ctxt (t2, deriv2) ^ ")"
  | (t, Term Input) => Syntax.string_of_term ctxt t ^ "[Input]"
  | (t, Term Output) => Syntax.string_of_term ctxt t ^ "[Output]"
  | (t, Context m) => Syntax.string_of_term ctxt t ^ "[" ^ string_of_mode m ^ "]")

fun compile_expr compilation_modifiers ctxt (t, deriv) param_modes additional_arguments =
  let
    val compfuns = Comp_Mod.compfuns compilation_modifiers
    fun expr_of (t, deriv) =
      (case (t, deriv) of
        (t, Term Input) => SOME (compile_arg compilation_modifiers additional_arguments ctxt param_modes t)
      | (t, Term Output) => NONE
      | (Const (name, T), Context mode) =>
        (case alternative_compilation_of ctxt name mode of
          SOME alt_comp => SOME (alt_comp compfuns T)
        | NONE =>
          SOME (Const (function_name_of (Comp_Mod.compilation compilation_modifiers)
            ctxt name mode,
            Comp_Mod.funT_of compilation_modifiers mode T)))
      | (Free (s, T), Context m) =>
        (case (AList.lookup (op =) param_modes s) of
          SOME mode => SOME (Free (s, Comp_Mod.funT_of compilation_modifiers m T))
        | NONE =>
        let
          val bs = map (pair "x") (binder_types (fastype_of t))
          val bounds = map Bound (rev (0 upto (length bs) - 1))
        in SOME (list_abs (bs, mk_if compfuns (list_comb (t, bounds)))) end)
      | (t, Context m) =>
        let
          val bs = map (pair "x") (binder_types (fastype_of t))
          val bounds = map Bound (rev (0 upto (length bs) - 1))
        in SOME (list_abs (bs, mk_if compfuns (list_comb (t, bounds)))) end
      | (Const (@{const_name Pair}, _) $ t1 $ t2, Mode_Pair (d1, d2)) =>
        (case (expr_of (t1, d1), expr_of (t2, d2)) of
          (NONE, NONE) => NONE
        | (NONE, SOME t) => SOME t
        | (SOME t, NONE) => SOME t
        | (SOME t1, SOME t2) => SOME (HOLogic.mk_prod (t1, t2)))
      | (t1 $ t2, Mode_App (deriv1, deriv2)) =>
        (case (expr_of (t1, deriv1), expr_of (t2, deriv2)) of
          (SOME t, NONE) => SOME t
         | (SOME t, SOME u) => SOME (t $ u)
         | _ => error "something went wrong here!"))
  in
    list_comb (the (expr_of (t, deriv)), additional_arguments)
  end

fun compile_clause compilation_modifiers ctxt all_vs param_modes additional_arguments
  inp (in_ts, out_ts) moded_ps =
  let
    val compfuns = Comp_Mod.compfuns compilation_modifiers
    val compile_match = compile_match compilation_modifiers
      additional_arguments ctxt param_modes
    val (in_ts', (all_vs', eqs)) =
      fold_map (collect_non_invertible_subterms ctxt) in_ts (all_vs, []);
    fun compile_prems out_ts' vs names [] =
          let
            val (out_ts'', (names', eqs')) =
              fold_map (collect_non_invertible_subterms ctxt) out_ts' (names, []);
            val (out_ts''', (names'', constr_vs)) = fold_map distinct_v
              out_ts'' (names', map (rpair []) vs);
            val processed_out_ts = map (compile_arg compilation_modifiers additional_arguments
              ctxt param_modes) out_ts
          in
            compile_match constr_vs (eqs @ eqs') out_ts'''
              (mk_single compfuns (HOLogic.mk_tuple processed_out_ts))
          end
      | compile_prems out_ts vs names ((p, deriv) :: ps) =
          let
            val vs' = distinct (op =) (flat (vs :: map term_vs out_ts));
            val (out_ts', (names', eqs)) =
              fold_map (collect_non_invertible_subterms ctxt) out_ts (names, [])
            val (out_ts'', (names'', constr_vs')) = fold_map distinct_v
              out_ts' ((names', map (rpair []) vs))
            val mode = head_mode_of deriv
            val additional_arguments' =
              Comp_Mod.transform_additional_arguments compilation_modifiers p additional_arguments
            val (compiled_clause, rest) = case p of
               Prem t =>
                 let
                   val u =
                     compile_expr compilation_modifiers ctxt (t, deriv) param_modes additional_arguments'
                   val (_, out_ts''') = split_mode mode (snd (strip_comb t))
                   val rest = compile_prems out_ts''' vs' names'' ps
                 in
                   (u, rest)
                 end
             | Negprem t =>
                 let
                   val neg_compilation_modifiers =
                     negative_comp_modifiers_of compilation_modifiers
                   val u = mk_not compfuns
                     (compile_expr neg_compilation_modifiers ctxt (t, deriv) param_modes additional_arguments')
                   val (_, out_ts''') = split_mode mode (snd (strip_comb t))
                   val rest = compile_prems out_ts''' vs' names'' ps
                 in
                   (u, rest)
                 end
             | Sidecond t =>
                 let
                   val t = compile_arg compilation_modifiers additional_arguments
                     ctxt param_modes t
                   val rest = compile_prems [] vs' names'' ps;
                 in
                   (mk_if compfuns t, rest)
                 end
             | Generator (v, T) =>
                 let
                   val u = Comp_Mod.mk_random compilation_modifiers T additional_arguments
                   val rest = compile_prems [Free (v, T)]  vs' names'' ps;
                 in
                   (u, rest)
                 end
          in
            compile_match constr_vs' eqs out_ts''
              (mk_bind compfuns (compiled_clause, rest))
          end
    val prem_t = compile_prems in_ts' (map fst param_modes) all_vs' moded_ps;
  in
    mk_bind compfuns (mk_single compfuns inp, prem_t)
  end

(* switch detection *)

(** argument position of an inductive predicates and the executable functions **)

type position = int * int list

fun input_positions_pair Input = [[]]
  | input_positions_pair Output = []
  | input_positions_pair (Fun _) = []
  | input_positions_pair (Pair (m1, m2)) =
    map (cons 1) (input_positions_pair m1) @ map (cons 2) (input_positions_pair m2)

fun input_positions_of_mode mode = flat (map_index
   (fn (i, Input) => [(i, [])]
   | (_, Output) => []
   | (_, Fun _) => []
   | (i, m as Pair (m1, m2)) => map (pair i) (input_positions_pair m))
     (Predicate_Compile_Aux.strip_fun_mode mode))

fun argument_position_pair mode [] = []
  | argument_position_pair (Pair (Fun _, m2)) (2 :: is) = argument_position_pair m2 is
  | argument_position_pair (Pair (m1, m2)) (i :: is) =
    (if eq_mode (m1, Output) andalso i = 2 then
      argument_position_pair m2 is
    else if eq_mode (m2, Output) andalso i = 1 then
      argument_position_pair m1 is
    else (i :: argument_position_pair (if i = 1 then m1 else m2) is))

fun argument_position_of mode (i, is) =
  (i - (length (filter (fn Output => true | Fun _ => true | _ => false)
    (List.take (strip_fun_mode mode, i)))),
  argument_position_pair (nth (strip_fun_mode mode) i) is)

fun nth_pair [] t = t
  | nth_pair (1 :: is) (Const (@{const_name Pair}, _) $ t1 $ _) = nth_pair is t1
  | nth_pair (2 :: is) (Const (@{const_name Pair}, _) $ _ $ t2) = nth_pair is t2
  | nth_pair _ _ = raise Fail "unexpected input for nth_tuple"

(** switch detection analysis **)

fun find_switch_test ctxt (i, is) (ts, prems) =
  let
    val t = nth_pair is (nth ts i)
    val T = fastype_of t
  in
    case T of
      TFree _ => NONE
    | Type (Tcon, _) =>
      (case Datatype.get_constrs (Proof_Context.theory_of ctxt) Tcon of
        NONE => NONE
      | SOME cs =>
        (case strip_comb t of
          (Var _, []) => NONE
        | (Free _, []) => NONE
        | (Const (c, T), _) => if AList.defined (op =) cs c then SOME (c, T) else NONE))
  end

fun partition_clause ctxt pos moded_clauses =
  let
    fun insert_list eq (key, value) = AList.map_default eq (key, []) (cons value)
    fun find_switch_test' moded_clause (cases, left) =
      case find_switch_test ctxt pos moded_clause of
        SOME (c, T) => (insert_list (op =) ((c, T), moded_clause) cases, left)
      | NONE => (cases, moded_clause :: left)
  in
    fold find_switch_test' moded_clauses ([], [])
  end

datatype switch_tree =
  Atom of moded_clause list | Node of (position * ((string * typ) * switch_tree) list) * switch_tree

fun mk_switch_tree ctxt mode moded_clauses =
  let
    fun select_best_switch moded_clauses input_position best_switch =
      let
        val ord = option_ord (rev_order o int_ord o (pairself (length o snd o snd)))
        val partition = partition_clause ctxt input_position moded_clauses
        val switch = if (length (fst partition) > 1) then SOME (input_position, partition) else NONE
      in
        case ord (switch, best_switch) of LESS => best_switch
          | EQUAL => best_switch | GREATER => switch
      end
    fun detect_switches moded_clauses =
      case fold (select_best_switch moded_clauses) (input_positions_of_mode mode) NONE of
        SOME (best_pos, (switched_on, left_clauses)) =>
          Node ((best_pos, map (apsnd detect_switches) switched_on),
            detect_switches left_clauses)
      | NONE => Atom moded_clauses
  in
    detect_switches moded_clauses
  end

(** compilation of detected switches **)

fun destruct_constructor_pattern (pat, obj) =
  (case strip_comb pat of
    (f as Free _, []) => cons (pat, obj)
  | (Const (c, T), pat_args) =>
    (case strip_comb obj of
      (Const (c', T'), obj_args) =>
        (if c = c' andalso T = T' then
          fold destruct_constructor_pattern (pat_args ~~ obj_args)
        else raise Fail "pattern and object mismatch")
    | _ => raise Fail "unexpected object")
  | _ => raise Fail "unexpected pattern")


fun compile_switch compilation_modifiers ctxt all_vs param_modes additional_arguments mode
  in_ts' outTs switch_tree =
  let
    val compfuns = Comp_Mod.compfuns compilation_modifiers
    val thy = Proof_Context.theory_of ctxt
    fun compile_switch_tree _ _ (Atom []) = NONE
      | compile_switch_tree all_vs ctxt_eqs (Atom moded_clauses) =
        let
          val in_ts' = map (Pattern.rewrite_term thy ctxt_eqs []) in_ts'
          fun compile_clause' (ts, moded_ps) =
            let
              val (ts, out_ts) = split_mode mode ts
              val subst = fold destruct_constructor_pattern (in_ts' ~~ ts) []
              val (fsubst, pat') = List.partition (fn (_, Free _) => true | _ => false) subst
              val moded_ps' = (map o apfst o map_indprem)
                (Pattern.rewrite_term thy (map swap fsubst) []) moded_ps
              val inp = HOLogic.mk_tuple (map fst pat')
              val in_ts' = map (Pattern.rewrite_term thy (map swap fsubst) []) (map snd pat')
              val out_ts' = map (Pattern.rewrite_term thy (map swap fsubst) []) out_ts
            in
              compile_clause compilation_modifiers ctxt all_vs param_modes additional_arguments
                inp (in_ts', out_ts') moded_ps'
            end
        in SOME (foldr1 (mk_plus compfuns) (map compile_clause' moded_clauses)) end
    | compile_switch_tree all_vs ctxt_eqs (Node ((position, switched_clauses), left_clauses)) =
      let
        val (i, is) = argument_position_of mode position
        val inp_var = nth_pair is (nth in_ts' i)
        val x = singleton (Name.variant_list all_vs) "x"
        val xt = Free (x, fastype_of inp_var)
        fun compile_single_case ((c, T), switched) =
          let
            val Ts = binder_types T
            val argnames = Name.variant_list (x :: all_vs)
              (map (fn i => "c" ^ string_of_int i) (1 upto length Ts))
            val args = map2 (curry Free) argnames Ts
            val pattern = list_comb (Const (c, T), args)
            val ctxt_eqs' = (inp_var, pattern) :: ctxt_eqs
            val compilation = the_default (mk_empty compfuns (HOLogic.mk_tupleT outTs))
              (compile_switch_tree (argnames @ x :: all_vs) ctxt_eqs' switched)
        in
          (pattern, compilation)
        end
        val switch = Datatype_Case.make_case ctxt Datatype_Case.Quiet [] inp_var
          ((map compile_single_case switched_clauses) @
            [(xt, mk_empty compfuns (HOLogic.mk_tupleT outTs))])
      in
        case compile_switch_tree all_vs ctxt_eqs left_clauses of
          NONE => SOME switch
        | SOME left_comp => SOME (mk_plus compfuns (switch, left_comp))
      end
  in
    compile_switch_tree all_vs [] switch_tree
  end

(* compilation of predicates *)

fun compile_pred options compilation_modifiers ctxt all_vs param_vs s T (pol, mode) moded_cls =
  let
    val is_terminating = false (* FIXME: requires an termination analysis *)  
    val compilation_modifiers =
      (if pol then compilation_modifiers else
        negative_comp_modifiers_of compilation_modifiers)
      |> (if is_depth_limited_compilation (Comp_Mod.compilation compilation_modifiers) then
           (if is_terminating then
             (Comp_Mod.set_compfuns (unlimited_compfuns_of pol (Comp_Mod.compilation compilation_modifiers)))
           else
             (Comp_Mod.set_compfuns (limited_compfuns_of pol (Comp_Mod.compilation compilation_modifiers))))
         else I)
    val additional_arguments = Comp_Mod.additional_arguments compilation_modifiers
      (all_vs @ param_vs)
    val compfuns = Comp_Mod.compfuns compilation_modifiers
    fun is_param_type (T as Type ("fun",[_ , T'])) =
      is_some (try (dest_monadT compfuns) T) orelse is_param_type T'
      | is_param_type T = is_some (try (dest_monadT compfuns) T)
    val (inpTs, outTs) = split_map_modeT (fn m => fn T => (SOME (funT_of compfuns m T), NONE)) mode
      (binder_types T)
    val funT = Comp_Mod.funT_of compilation_modifiers mode T
    val (in_ts, _) = fold_map (fold_map_aterms_prodT (curry HOLogic.mk_prod)
      (fn T => fn (param_vs, names) =>
        if is_param_type T then
          (Free (hd param_vs, T), (tl param_vs, names))
        else
          let
            val new = singleton (Name.variant_list names) "x"
          in (Free (new, T), (param_vs, new :: names)) end)) inpTs
        (param_vs, (all_vs @ param_vs))
    val in_ts' = map_filter (map_filter_prod
      (fn t as Free (x, _) => if member (op =) param_vs x then NONE else SOME t | t => SOME t)) in_ts
    val param_modes = param_vs ~~ ho_arg_modes_of mode
    val compilation =
      if detect_switches options then
        the_default (mk_empty compfuns (HOLogic.mk_tupleT outTs))
          (compile_switch compilation_modifiers ctxt all_vs param_modes additional_arguments mode
            in_ts' outTs (mk_switch_tree ctxt mode moded_cls))
      else
        let
          val cl_ts =
            map (fn (ts, moded_prems) => 
              compile_clause compilation_modifiers ctxt all_vs param_modes additional_arguments
                (HOLogic.mk_tuple in_ts') (split_mode mode ts) moded_prems) moded_cls;
        in
          Comp_Mod.wrap_compilation compilation_modifiers compfuns s T mode additional_arguments
            (if null cl_ts then
              mk_empty compfuns (HOLogic.mk_tupleT outTs)
            else
              foldr1 (mk_plus compfuns) cl_ts)
        end
    val fun_const =
      Const (function_name_of (Comp_Mod.compilation compilation_modifiers)
      ctxt s mode, funT)
  in
    HOLogic.mk_Trueprop
      (HOLogic.mk_eq (list_comb (fun_const, in_ts @ additional_arguments), compilation))
  end;

(* Definition of executable functions and their intro and elim rules *)

fun print_arities arities = tracing ("Arities:\n" ^
  cat_lines (map (fn (s, (ks, k)) => s ^ ": " ^
    space_implode " -> " (map
      (fn NONE => "X" | SOME k' => string_of_int k')
        (ks @ [SOME k]))) arities));

fun strip_split_abs (Const (@{const_name prod_case}, _) $ t) = strip_split_abs t
  | strip_split_abs (Abs (_, _, t)) = strip_split_abs t
  | strip_split_abs t = t

fun mk_args is_eval (m as Pair (m1, m2), T as Type (@{type_name Product_Type.prod}, [T1, T2])) names =
    if eq_mode (m, Input) orelse eq_mode (m, Output) then
      let
        val x = singleton (Name.variant_list names) "x"
      in
        (Free (x, T), x :: names)
      end
    else
      let
        val (t1, names') = mk_args is_eval (m1, T1) names
        val (t2, names'') = mk_args is_eval (m2, T2) names'
      in
        (HOLogic.mk_prod (t1, t2), names'')
      end
  | mk_args is_eval ((m as Fun _), T) names =
    let
      val funT = funT_of Predicate_Comp_Funs.compfuns m T
      val x = singleton (Name.variant_list names) "x"
      val (args, _) = fold_map (mk_args is_eval) (strip_fun_mode m ~~ binder_types T) (x :: names)
      val (inargs, outargs) = split_map_mode (fn _ => fn t => (SOME t, NONE)) m args
      val t = fold_rev HOLogic.tupled_lambda args (Predicate_Comp_Funs.mk_Eval
        (list_comb (Free (x, funT), inargs), HOLogic.mk_tuple outargs))
    in
      (if is_eval then t else Free (x, funT), x :: names)
    end
  | mk_args is_eval (_, T) names =
    let
      val x = singleton (Name.variant_list names) "x"
    in
      (Free (x, T), x :: names)
    end

fun create_intro_elim_rule ctxt mode defthm mode_id funT pred =
  let
    val funtrm = Const (mode_id, funT)
    val Ts = binder_types (fastype_of pred)
    val (args, argnames) = fold_map (mk_args true) (strip_fun_mode mode ~~ Ts) []
    fun strip_eval _ t =
      let
        val t' = strip_split_abs t
        val (r, _) = Predicate_Comp_Funs.dest_Eval t'
      in (SOME (fst (strip_comb r)), NONE) end
    val (inargs, outargs) = split_map_mode strip_eval mode args
    val eval_hoargs = ho_args_of mode args
    val hoargTs = ho_argsT_of mode Ts
    val hoarg_names' =
      Name.variant_list argnames ((map (fn i => "x" ^ string_of_int i)) (1 upto (length hoargTs)))
    val hoargs' = map2 (curry Free) hoarg_names' hoargTs
    val args' = replace_ho_args mode hoargs' args
    val predpropI = HOLogic.mk_Trueprop (list_comb (pred, args'))
    val predpropE = HOLogic.mk_Trueprop (list_comb (pred, args))
    val param_eqs = map2 (HOLogic.mk_Trueprop oo (curry HOLogic.mk_eq)) eval_hoargs hoargs'
    val funpropE = HOLogic.mk_Trueprop (Predicate_Comp_Funs.mk_Eval (list_comb (funtrm, inargs),
                    if null outargs then Free("y", HOLogic.unitT) else HOLogic.mk_tuple outargs))
    val funpropI = HOLogic.mk_Trueprop (Predicate_Comp_Funs.mk_Eval (list_comb (funtrm, inargs),
                     HOLogic.mk_tuple outargs))
    val introtrm = Logic.list_implies (predpropI :: param_eqs, funpropI)
    val simprules = [defthm, @{thm eval_pred},
      @{thm "split_beta"}, @{thm "fst_conv"}, @{thm "snd_conv"}, @{thm pair_collapse}]
    val unfolddef_tac = Simplifier.asm_full_simp_tac (HOL_basic_ss addsimps simprules) 1
    val introthm = Goal.prove ctxt
      (argnames @ hoarg_names' @ ["y"]) [] introtrm (fn _ => unfolddef_tac)
    val P = HOLogic.mk_Trueprop (Free ("P", HOLogic.boolT));
    val elimtrm = Logic.list_implies ([funpropE, Logic.mk_implies (predpropE, P)], P)
    val elimthm = Goal.prove ctxt
      (argnames @ ["y", "P"]) [] elimtrm (fn _ => unfolddef_tac)
    val opt_neg_introthm =
      if is_all_input mode then
        let
          val neg_predpropI = HOLogic.mk_Trueprop (HOLogic.mk_not (list_comb (pred, args')))
          val neg_funpropI =
            HOLogic.mk_Trueprop (Predicate_Comp_Funs.mk_Eval
              (Predicate_Comp_Funs.mk_not (list_comb (funtrm, inargs)), HOLogic.unit))
          val neg_introtrm = Logic.list_implies (neg_predpropI :: param_eqs, neg_funpropI)
          val tac =
            Simplifier.asm_full_simp_tac (HOL_basic_ss addsimps
              (@{thm if_False} :: @{thm Predicate.not_pred_eq} :: simprules)) 1
            THEN rtac @{thm Predicate.singleI} 1
        in SOME (Goal.prove ctxt (argnames @ hoarg_names') []
            neg_introtrm (fn _ => tac))
        end
      else NONE
  in
    ((introthm, elimthm), opt_neg_introthm)
  end

fun create_constname_of_mode options thy prefix name T mode = 
  let
    val system_proposal = prefix ^ (Long_Name.base_name name)
      ^ "_" ^ ascii_string_of_mode mode
    val name = the_default system_proposal (proposed_names options name mode)
  in
    Sign.full_bname thy name
  end;

fun create_definitions options preds (name, modes) thy =
  let
    val compfuns = Predicate_Comp_Funs.compfuns
    val T = AList.lookup (op =) preds name |> the
    fun create_definition mode thy =
      let
        val mode_cname = create_constname_of_mode options thy "" name T mode
        val mode_cbasename = Long_Name.base_name mode_cname
        val funT = funT_of compfuns mode T
        val (args, _) = fold_map (mk_args true) ((strip_fun_mode mode) ~~ (binder_types T)) []
        fun strip_eval m t =
          let
            val t' = strip_split_abs t
            val (r, _) = Predicate_Comp_Funs.dest_Eval t'
          in (SOME (fst (strip_comb r)), NONE) end
        val (inargs, outargs) = split_map_mode strip_eval mode args
        val predterm = fold_rev HOLogic.tupled_lambda inargs
          (Predicate_Comp_Funs.mk_Enum (HOLogic.tupled_lambda (HOLogic.mk_tuple outargs)
            (list_comb (Const (name, T), args))))
        val lhs = Const (mode_cname, funT)
        val def = Logic.mk_equals (lhs, predterm)
        val ([definition], thy') = thy |>
          Sign.add_consts_i [(Binding.name mode_cbasename, funT, NoSyn)] |>
          Global_Theory.add_defs false [((Binding.name (mode_cbasename ^ "_def"), def), [])]
        val ctxt' = Proof_Context.init_global thy'
        val rules as ((intro, elim), _) =
          create_intro_elim_rule ctxt' mode definition mode_cname funT (Const (name, T))
        in thy'
          |> set_function_name Pred name mode mode_cname
          |> add_predfun_data name mode (definition, rules)
          |> Global_Theory.store_thm (Binding.name (mode_cbasename ^ "I"), intro) |> snd
          |> Global_Theory.store_thm (Binding.name (mode_cbasename ^ "E"), elim)  |> snd
          |> Theory.checkpoint
        end;
  in
    thy |> defined_function_of Pred name |> fold create_definition modes
  end;

fun define_functions comp_modifiers compfuns options preds (name, modes) thy =
  let
    val T = AList.lookup (op =) preds name |> the
    fun create_definition mode thy =
      let
        val function_name_prefix = Comp_Mod.function_name_prefix comp_modifiers
        val mode_cname = create_constname_of_mode options thy function_name_prefix name T mode
        val funT = Comp_Mod.funT_of comp_modifiers mode T
      in
        thy |> Sign.add_consts_i [(Binding.name (Long_Name.base_name mode_cname), funT, NoSyn)]
        |> set_function_name (Comp_Mod.compilation comp_modifiers) name mode mode_cname
      end;
  in
    thy
    |> defined_function_of (Comp_Mod.compilation comp_modifiers) name
    |> fold create_definition modes
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

fun compile_preds options comp_modifiers ctxt all_vs param_vs preds moded_clauses =
  map_preds_modes (fn pred => compile_pred options comp_modifiers ctxt all_vs param_vs pred
      (the (AList.lookup (op =) preds pred))) moded_clauses

fun prove options thy clauses preds moded_clauses compiled_terms =
  map_preds_modes (prove_pred options thy clauses preds)
    (join_preds_modes moded_clauses compiled_terms)

fun prove_by_skip options thy _ _ _ compiled_terms =
  map_preds_modes
    (fn pred => fn mode => fn t => Drule.export_without_context (Skip_Proof.make_thm thy t))
    compiled_terms

(* preparation of introduction rules into special datastructures *)
fun dest_prem ctxt params t =
  (case strip_comb t of
    (v as Free _, ts) => if member (op =) params v then Prem t else Sidecond t
  | (c as Const (@{const_name Not}, _), [t]) => (case dest_prem ctxt params t of
      Prem t => Negprem t
    | Negprem _ => error ("Double negation not allowed in premise: " ^
        Syntax.string_of_term ctxt (c $ t)) 
    | Sidecond t => Sidecond (c $ t))
  | (c as Const (s, _), ts) =>
    if is_registered ctxt s then Prem t else Sidecond t
  | _ => Sidecond t)

fun prepare_intrs options ctxt prednames intros =
  let
    val thy = Proof_Context.theory_of ctxt
    val intrs = map prop_of intros
    val preds = map (fn c => Const (c, Sign.the_const_type thy c)) prednames
    val (preds, intrs) = unify_consts thy preds intrs
    val ([preds, intrs], _) = fold_burrow (Variable.import_terms false) [preds, intrs] ctxt
    val preds = map dest_Const preds
    val all_vs = terms_vs intrs
    fun generate_modes s T =
      if member (op =) (no_higher_order_predicate options) s then
        all_smodes_of_typ T
      else
        all_modes_of_typ T
    val all_modes = 
      map (fn (s, T) =>
        (s, case proposed_modes options s of
            SOME ms => check_matches_type ctxt s T ms
          | NONE => generate_modes s T)) preds
    val params =
      case intrs of
        [] =>
          let
            val T = snd (hd preds)
            val one_mode = hd (the (AList.lookup (op =) all_modes (fst (hd preds))))
            val paramTs =
              ho_argsT_of one_mode (binder_types T)
            val param_names = Name.variant_list [] (map (fn i => "p" ^ string_of_int i)
              (1 upto length paramTs))
          in
            map2 (curry Free) param_names paramTs
          end
      | (intr :: _) =>
        let
          val (p, args) = strip_comb (HOLogic.dest_Trueprop (Logic.strip_imp_concl intr))
          val one_mode = hd (the (AList.lookup (op =) all_modes (fst (dest_Const p))))
        in
          ho_args_of one_mode args
        end
    val param_vs = map (fst o dest_Free) params
    fun add_clause intr clauses =
      let
        val (Const (name, T), ts) = strip_comb (HOLogic.dest_Trueprop (Logic.strip_imp_concl intr))
        val prems = map (dest_prem ctxt params o HOLogic.dest_Trueprop) (Logic.strip_imp_prems intr)
      in
        AList.update op = (name, these (AList.lookup op = clauses name) @
          [(ts, prems)]) clauses
      end;
    val clauses = fold add_clause intrs []
  in
    (preds, all_vs, param_vs, all_modes, clauses)
  end;

(* sanity check of introduction rules *)
(* TODO: rethink check with new modes *)
(*
fun check_format_of_intro_rule thy intro =
  let
    val concl = Logic.strip_imp_concl (prop_of intro)
    val (p, args) = strip_comb (HOLogic.dest_Trueprop concl)
    val params = fst (chop (nparams_of thy (fst (dest_Const p))) args)
    fun check_arg arg = case HOLogic.strip_tupleT (fastype_of arg) of
      (Ts as _ :: _ :: _) =>
        if length (HOLogic.strip_tuple arg) = length Ts then
          true
        else
          error ("Format of introduction rule is invalid: tuples must be expanded:"
          ^ (Syntax.string_of_term_global thy arg) ^ " in " ^
          (Display.string_of_thm_global thy intro)) 
      | _ => true
    val prems = Logic.strip_imp_prems (prop_of intro)
    fun check_prem (Prem t) = forall check_arg args
      | check_prem (Negprem t) = forall check_arg args
      | check_prem _ = true
  in
    forall check_arg args andalso
    forall (check_prem o dest_prem thy params o HOLogic.dest_Trueprop) prems
  end
*)
(*
fun check_intros_elim_match thy prednames =
  let
    fun check predname =
      let
        val intros = intros_of thy predname
        val elim = the_elim_of thy predname
        val nparams = nparams_of thy predname
        val elim' =
          (Drule.export_without_context o Skip_Proof.make_thm thy)
          (mk_casesrule (Proof_Context.init_global thy) nparams intros)
      in
        if not (Thm.equiv_thm (elim, elim')) then
          error "Introduction and elimination rules do not match!"
        else true
      end
  in forall check prednames end
*)

(* create code equation *)

fun add_code_equations ctxt preds result_thmss =
  let
    fun add_code_equation (predname, T) (pred, result_thms) =
      let
        val full_mode = fold_rev (curry Fun) (map (K Input) (binder_types T)) Bool
      in
        if member (op =) (modes_of Pred ctxt predname) full_mode then
          let
            val Ts = binder_types T
            val arg_names = Name.variant_list []
              (map (fn i => "x" ^ string_of_int i) (1 upto length Ts))
            val args = map2 (curry Free) arg_names Ts
            val predfun = Const (function_name_of Pred ctxt predname full_mode,
              Ts ---> Predicate_Comp_Funs.mk_monadT @{typ unit})
            val rhs = @{term Predicate.holds} $ (list_comb (predfun, args))
            val eq_term = HOLogic.mk_Trueprop
              (HOLogic.mk_eq (list_comb (Const (predname, T), args), rhs))
            val def = predfun_definition_of ctxt predname full_mode
            val tac = fn _ => Simplifier.simp_tac
              (HOL_basic_ss addsimps [def, @{thm holds_eq}, @{thm eval_pred}]) 1
            val eq = Goal.prove ctxt arg_names [] eq_term tac
          in
            (pred, result_thms @ [eq])
          end
        else
          (pred, result_thms)
      end
  in
    map2 add_code_equation preds result_thmss
  end

(** main function of predicate compiler **)

datatype steps = Steps of
  {
  define_functions : options -> (string * typ) list -> string * (bool * mode) list -> theory -> theory,
  prove : options -> theory -> (string * (term list * indprem list) list) list -> (string * typ) list
    -> moded_clause list pred_mode_table -> term pred_mode_table -> thm pred_mode_table,
  add_code_equations : Proof.context -> (string * typ) list
    -> (string * thm list) list -> (string * thm list) list,
  comp_modifiers : Comp_Mod.comp_modifiers,
  use_generators : bool,
  qname : bstring
  }

fun add_equations_of steps mode_analysis_options options prednames thy =
  let
    fun dest_steps (Steps s) = s
    val compilation = Comp_Mod.compilation (#comp_modifiers (dest_steps steps))
    val ctxt = Proof_Context.init_global thy
    val _ = print_step options
      ("Starting predicate compiler (compilation: " ^ string_of_compilation compilation
        ^ ") for predicates " ^ commas prednames ^ "...")
      (*val _ = check_intros_elim_match thy prednames*)
      (*val _ = map (check_format_of_intro_rule thy) (maps (intros_of thy) prednames)*)
    val _ =
      if show_intermediate_results options then
        tracing (commas (map (Display.string_of_thm ctxt) (maps (intros_of ctxt) prednames)))
      else ()
    val (preds, all_vs, param_vs, all_modes, clauses) =
      prepare_intrs options ctxt prednames (maps (intros_of ctxt) prednames)
    val _ = print_step options "Infering modes..."
    val (lookup_mode, lookup_neg_mode, needs_random) = (modes_of compilation ctxt,
      modes_of (negative_compilation_of compilation) ctxt, needs_random ctxt)
    val ((moded_clauses, needs_random), errors) =
      cond_timeit (Config.get ctxt Quickcheck.timing) "Infering modes"
      (fn _ => infer_modes mode_analysis_options
        options (lookup_mode, lookup_neg_mode, needs_random) ctxt preds all_modes param_vs clauses)
    val thy' = fold (fn (s, ms) => set_needs_random s ms) needs_random thy
    val modes = map (fn (p, mps) => (p, map fst mps)) moded_clauses
    val _ = check_expected_modes options preds modes
    val _ = check_proposed_modes options preds modes errors
    val _ = print_modes options modes
    val _ = print_step options "Defining executable functions..."
    val thy'' =
      cond_timeit (Config.get ctxt Quickcheck.timing) "Defining executable functions..."
      (fn _ => fold (#define_functions (dest_steps steps) options preds) modes thy'
      |> Theory.checkpoint)
    val ctxt'' = Proof_Context.init_global thy''
    val _ = print_step options "Compiling equations..."
    val compiled_terms =
      cond_timeit (Config.get ctxt Quickcheck.timing) "Compiling equations...." (fn _ =>
        compile_preds options
          (#comp_modifiers (dest_steps steps)) ctxt'' all_vs param_vs preds moded_clauses)
    val _ = print_compiled_terms options ctxt'' compiled_terms
    val _ = print_step options "Proving equations..."
    val result_thms =
      cond_timeit (Config.get ctxt Quickcheck.timing) "Proving equations...." (fn _ =>
      #prove (dest_steps steps) options thy'' clauses preds moded_clauses compiled_terms)
    val result_thms' = #add_code_equations (dest_steps steps) ctxt'' preds
      (maps_modes result_thms)
    val qname = #qname (dest_steps steps)
    (* FIXME !? *)
    val attrib = fn thy => Attrib.attribute_i thy (Attrib.internal (K (Thm.declaration_attribute
      (fn thm => Context.mapping (Code.add_eqn thm) I))))
    val thy''' =
      cond_timeit (Config.get ctxt Quickcheck.timing) "Setting code equations...." (fn _ =>
      fold (fn (name, result_thms) => fn thy => snd (Global_Theory.add_thmss
      [((Binding.qualify true (Long_Name.base_name name) (Binding.name qname), result_thms),
        [attrib thy ])] thy))
      result_thms' thy'' |> Theory.checkpoint)
  in
    thy'''
  end
  
fun gen_add_equations steps options names thy =
  let
    fun dest_steps (Steps s) = s
    val defined = defined_functions (Comp_Mod.compilation (#comp_modifiers (dest_steps steps)))
    val thy' = extend_intro_graph names thy |> Theory.checkpoint;
    fun strong_conn_of gr keys =
      Graph.strong_conn (Graph.subgraph (member (op =) (Graph.all_succs gr keys)) gr)
    val scc = strong_conn_of (PredData.get thy') names
    val thy'' = fold preprocess_intros (flat scc) thy'
    val thy''' = fold_rev
      (fn preds => fn thy =>
        if not (forall (defined (Proof_Context.init_global thy)) preds) then
          let
            val mode_analysis_options = {use_generators = #use_generators (dest_steps steps),
              reorder_premises =
                not (no_topmost_reordering options andalso not (null (inter (op =) preds names))),
              infer_pos_and_neg_modes = #use_generators (dest_steps steps)}
          in
            add_equations_of steps mode_analysis_options options preds thy
          end
        else thy)
      scc thy'' |> Theory.checkpoint
  in thy''' end

val add_equations = gen_add_equations
  (Steps {
  define_functions =
    fn options => fn preds => fn (s, modes) =>
      create_definitions
      options preds (s, map_filter (fn (true, m) => SOME m | _ => NONE) modes),
  prove = prove,
  add_code_equations = add_code_equations,
  comp_modifiers = predicate_comp_modifiers,
  use_generators = false,
  qname = "equation"})

val add_depth_limited_equations = gen_add_equations
  (Steps {
  define_functions =
    fn options => fn preds => fn (s, modes) =>
    define_functions depth_limited_comp_modifiers Predicate_Comp_Funs.compfuns
    options preds (s, map_filter (fn (true, m) => SOME m | _ => NONE) modes),
  prove = prove_by_skip,
  add_code_equations = K (K I),
  comp_modifiers = depth_limited_comp_modifiers,
  use_generators = false,
  qname = "depth_limited_equation"})

val add_annotated_equations = gen_add_equations
  (Steps {
  define_functions =
    fn options => fn preds => fn (s, modes) =>
      define_functions annotated_comp_modifiers Predicate_Comp_Funs.compfuns options preds
      (s, map_filter (fn (true, m) => SOME m | _ => NONE) modes),
  prove = prove_by_skip,
  add_code_equations = K (K I),
  comp_modifiers = annotated_comp_modifiers,
  use_generators = false,
  qname = "annotated_equation"})

val add_random_equations = gen_add_equations
  (Steps {
  define_functions =
    fn options => fn preds => fn (s, modes) =>
      define_functions random_comp_modifiers Predicate_Comp_Funs.compfuns options preds
      (s, map_filter (fn (true, m) => SOME m | _ => NONE) modes),
  comp_modifiers = random_comp_modifiers,
  prove = prove_by_skip,
  add_code_equations = K (K I),
  use_generators = true,
  qname = "random_equation"})

val add_depth_limited_random_equations = gen_add_equations
  (Steps {
  define_functions =
    fn options => fn preds => fn (s, modes) =>
      define_functions depth_limited_random_comp_modifiers Predicate_Comp_Funs.compfuns options preds
      (s, map_filter (fn (true, m) => SOME m | _ => NONE) modes),
  comp_modifiers = depth_limited_random_comp_modifiers,
  prove = prove_by_skip,
  add_code_equations = K (K I),
  use_generators = true,
  qname = "depth_limited_random_equation"})

val add_dseq_equations = gen_add_equations
  (Steps {
  define_functions =
  fn options => fn preds => fn (s, modes) =>
    define_functions dseq_comp_modifiers DSequence_CompFuns.compfuns
    options preds (s, map_filter (fn (true, m) => SOME m | _ => NONE) modes),
  prove = prove_by_skip,
  add_code_equations = K (K I),
  comp_modifiers = dseq_comp_modifiers,
  use_generators = false,
  qname = "dseq_equation"})

val add_random_dseq_equations = gen_add_equations
  (Steps {
  define_functions =
    fn options => fn preds => fn (s, modes) =>
    let
      val pos_modes = map_filter (fn (true, m) => SOME m | _ => NONE) modes
      val neg_modes = map_filter (fn (false, m) => SOME m | _ => NONE) modes
    in define_functions pos_random_dseq_comp_modifiers Random_Sequence_CompFuns.compfuns
      options preds (s, pos_modes)
      #> define_functions neg_random_dseq_comp_modifiers Random_Sequence_CompFuns.compfuns
      options preds (s, neg_modes)
    end,
  prove = prove_by_skip,
  add_code_equations = K (K I),
  comp_modifiers = pos_random_dseq_comp_modifiers,
  use_generators = true,
  qname = "random_dseq_equation"})

val add_new_random_dseq_equations = gen_add_equations
  (Steps {
  define_functions =
    fn options => fn preds => fn (s, modes) =>
    let
      val pos_modes = map_filter (fn (true, m) => SOME m | _ => NONE) modes
      val neg_modes = map_filter (fn (false, m) => SOME m | _ => NONE) modes
    in define_functions new_pos_random_dseq_comp_modifiers New_Pos_Random_Sequence_CompFuns.depth_limited_compfuns
      options preds (s, pos_modes)
      #> define_functions new_neg_random_dseq_comp_modifiers New_Neg_Random_Sequence_CompFuns.depth_limited_compfuns
      options preds (s, neg_modes)
    end,
  prove = prove_by_skip,
  add_code_equations = K (K I),
  comp_modifiers = new_pos_random_dseq_comp_modifiers,
  use_generators = true,
  qname = "new_random_dseq_equation"})

val add_generator_dseq_equations = gen_add_equations
  (Steps {
  define_functions =
  fn options => fn preds => fn (s, modes) =>
    let
      val pos_modes = map_filter (fn (true, m) => SOME m | _ => NONE) modes
      val neg_modes = map_filter (fn (false, m) => SOME m | _ => NONE) modes
    in 
      define_functions pos_generator_dseq_comp_modifiers New_Pos_DSequence_CompFuns.depth_limited_compfuns
        options preds (s, pos_modes)
      #> define_functions neg_generator_dseq_comp_modifiers New_Neg_DSequence_CompFuns.depth_limited_compfuns
        options preds (s, neg_modes)
    end,
  prove = prove_by_skip,
  add_code_equations = K (K I),
  comp_modifiers = pos_generator_dseq_comp_modifiers,
  use_generators = true,
  qname = "generator_dseq_equation"})

val add_generator_cps_equations = gen_add_equations
  (Steps {
  define_functions =
  fn options => fn preds => fn (s, modes) =>
    let
      val pos_modes = map_filter (fn (true, m) => SOME m | _ => NONE) modes
      val neg_modes = map_filter (fn (false, m) => SOME m | _ => NONE) modes
    in 
      define_functions pos_generator_cps_comp_modifiers Pos_Bounded_CPS_Comp_Funs.compfuns
        options preds (s, pos_modes)
      #> define_functions neg_generator_cps_comp_modifiers Neg_Bounded_CPS_Comp_Funs.compfuns
        options preds (s, neg_modes)
    end,
  prove = prove_by_skip,
  add_code_equations = K (K I),
  comp_modifiers = pos_generator_cps_comp_modifiers,
  use_generators = true,
  qname = "generator_cps_equation"})
  
  
(** user interface **)

(* code_pred_intro attribute *)

fun attrib' f opt_case_name =
  Thm.declaration_attribute (fn thm => Context.mapping (f (opt_case_name, thm)) I);

val code_pred_intro_attrib = attrib' add_intro NONE;

(*FIXME
- Naming of auxiliary rules necessary?
*)

(* values_timeout configuration *)

val default_values_timeout = if ML_System.is_smlnj then 1200.0 else 40.0

val values_timeout = Attrib.setup_config_real @{binding values_timeout} (K default_values_timeout)

val setup = PredData.put (Graph.empty) #>
  Attrib.setup @{binding code_pred_intro} (Scan.lift (Scan.option Args.name) >> attrib' add_intro)
    "adding alternative introduction rules for code generation of inductive predicates"

(* TODO: make Theory_Data to Generic_Data & remove duplication of local theory and theory *)
(* FIXME ... this is important to avoid changing the background theory below *)
fun generic_code_pred prep_const options raw_const lthy =
  let
    val thy = Proof_Context.theory_of lthy
    val const = prep_const thy raw_const
    val lthy' = Local_Theory.background_theory (extend_intro_graph [const]) lthy
    val thy' = Proof_Context.theory_of lthy'
    val ctxt' = Proof_Context.init_global thy'
    val preds = Graph.all_succs (PredData.get thy') [const] |> filter_out (has_elim ctxt')
    fun mk_cases const =
      let
        val T = Sign.the_const_type thy' const
        val pred = Const (const, T)
        val intros = intros_of ctxt' const
      in mk_casesrule lthy' pred intros end  
    val cases_rules = map mk_cases preds
    val cases =
      map2 (fn pred_name => fn case_rule => Rule_Cases.Case {fixes = [],
        assumes = ("that", tl (Logic.strip_imp_prems case_rule))
          :: (map_filter (fn (fact_name, fact) => Option.map (rpair [fact]) fact_name)
            ((SOME (Long_Name.base_name pred_name ^ ".prems") :: names_of ctxt' pred_name) ~~ Logic.strip_imp_prems case_rule)),
        binds = [], cases = []}) preds cases_rules
    val case_env = map2 (fn p => fn c => (Long_Name.base_name p, SOME c)) preds cases
    val lthy'' = lthy'
      |> fold Variable.auto_fixes cases_rules
      |> Proof_Context.add_cases true case_env
    fun after_qed thms goal_ctxt =
      let
        val global_thms = Proof_Context.export goal_ctxt
          (Proof_Context.init_global (Proof_Context.theory_of goal_ctxt)) (map the_single thms)
      in
        goal_ctxt |> Local_Theory.background_theory (fold set_elim global_thms #>
          ((case compilation options of
             Pred => add_equations
           | DSeq => add_dseq_equations
           | Pos_Random_DSeq => add_random_dseq_equations
           | Depth_Limited => add_depth_limited_equations
           | Random => add_random_equations
           | Depth_Limited_Random => add_depth_limited_random_equations
           | New_Pos_Random_DSeq => add_new_random_dseq_equations
           | Pos_Generator_DSeq => add_generator_dseq_equations
           | Pos_Generator_CPS => add_generator_cps_equations
           | compilation => error ("Compilation not supported")
           ) options [const]))
      end
  in
    Proof.theorem NONE after_qed (map (single o (rpair [])) cases_rules) lthy''
  end;

val code_pred = generic_code_pred (K I);
val code_pred_cmd = generic_code_pred Code.read_const

(* transformation for code generation *)

(* FIXME just one data slot (record) per program unit *)

structure Pred_Result = Proof_Data
(
  type T = unit -> term Predicate.pred
  (* FIXME avoid user error with non-user text *)
  fun init _ () = error "Pred_Result"
);
val put_pred_result = Pred_Result.put;

structure Pred_Random_Result = Proof_Data
(
  type T = unit -> int * int -> term Predicate.pred * (int * int)
  (* FIXME avoid user error with non-user text *)
  fun init _ () = error "Pred_Random_Result"
);
val put_pred_random_result = Pred_Random_Result.put;

structure Dseq_Result = Proof_Data
(
  type T = unit -> term DSequence.dseq
  (* FIXME avoid user error with non-user text *)
  fun init _ () = error "Dseq_Result"
);
val put_dseq_result = Dseq_Result.put;

structure Dseq_Random_Result = Proof_Data
(
  type T = unit -> int -> int -> int * int -> term DSequence.dseq * (int * int)
  (* FIXME avoid user error with non-user text *)
  fun init _ () = error "Dseq_Random_Result"
);
val put_dseq_random_result = Dseq_Random_Result.put;

structure New_Dseq_Result = Proof_Data
(
  type T = unit -> int -> term Lazy_Sequence.lazy_sequence
  (* FIXME avoid user error with non-user text *)
  fun init _ () = error "New_Dseq_Random_Result"
);
val put_new_dseq_result = New_Dseq_Result.put;

structure Lseq_Random_Result = Proof_Data
(
  type T = unit -> int -> int -> int * int -> int -> term Lazy_Sequence.lazy_sequence
  (* FIXME avoid user error with non-user text *)
  fun init _ () = error "Lseq_Random_Result"
);
val put_lseq_random_result = Lseq_Random_Result.put;

structure Lseq_Random_Stats_Result = Proof_Data
(
  type T = unit -> int -> int -> int * int -> int -> (term * int) Lazy_Sequence.lazy_sequence
  (* FIXME avoid user error with non-user text *)
  fun init _ () = error "Lseq_Random_Stats_Result"
);
val put_lseq_random_stats_result = Lseq_Random_Stats_Result.put;

fun dest_special_compr t =
  let
    val (inner_t, T_compr) = case t of (Const (@{const_name Collect}, _) $ Abs (x, T, t)) => (t, T)
      | _ => raise TERM ("dest_special_compr", [t])
    val (Ts, conj) = apfst (map snd) (Predicate_Compile_Aux.strip_ex inner_t)
    val [eq, body] = HOLogic.dest_conj conj
    val rhs = case HOLogic.dest_eq eq of
        (Bound i, rhs) => if i = length Ts then rhs else raise TERM ("dest_special_compr", [t])
      | _ => raise TERM ("dest_special_compr", [t])
    val output_names = Name.variant_list (fold Term.add_free_names [rhs, body] [])
      (map (fn i => "x" ^ string_of_int i) (1 upto length Ts))
    val output_frees = map2 (curry Free) output_names (rev Ts)
    val body = subst_bounds (output_frees, body)
    val output = subst_bounds (output_frees, rhs)
  in
    (((body, output), T_compr), output_names)
  end

fun dest_general_compr ctxt t_compr =
  let      
    val inner_t = case t_compr of (Const (@{const_name Collect}, _) $ t) => t
      | _ => error ("Not a set comprehension: " ^ Syntax.string_of_term ctxt t_compr);    
    val (body, Ts, fp) = HOLogic.strip_psplits inner_t;
    val output_names = Name.variant_list (Term.add_free_names body [])
      (map (fn i => "x" ^ string_of_int i) (1 upto length Ts))
    val output_frees = map2 (curry Free) output_names (rev Ts)
    val body = subst_bounds (output_frees, body)
    val T_compr = HOLogic.mk_ptupleT fp Ts
    val output = HOLogic.mk_ptuple fp T_compr (rev output_frees)
  in
    (((body, output), T_compr), output_names)
  end

(*FIXME turn this into an LCF-guarded preprocessor for comprehensions*)
fun analyze_compr ctxt (comp_modifiers, additional_arguments) param_user_modes
  (compilation, arguments) t_compr =
  let
    val compfuns = Comp_Mod.compfuns comp_modifiers
    val all_modes_of = all_modes_of compilation
    val (((body, output), T_compr), output_names) =
      case try dest_special_compr t_compr of SOME r => r | NONE => dest_general_compr ctxt t_compr
    val (pred as Const (name, T), all_args) =
      case strip_comb body of
        (Const (name, T), all_args) => (Const (name, T), all_args)
      | (head, _) => error ("Not a constant: " ^ Syntax.string_of_term ctxt head)
  in
    if defined_functions compilation ctxt name then
      let
        fun extract_mode (Const (@{const_name Pair}, _) $ t1 $ t2) = Pair (extract_mode t1, extract_mode t2)
          | extract_mode (Free (x, _)) = if member (op =) output_names x then Output else Input
          | extract_mode _ = Input
        val user_mode = fold_rev (curry Fun) (map extract_mode all_args) Bool
        fun valid modes1 modes2 =
          case int_ord (length modes1, length modes2) of
            GREATER => error "Not enough mode annotations"
          | LESS => error "Too many mode annotations"
          | EQUAL => forall (fn (m, NONE) => true | (m, SOME m2) => eq_mode (m, m2))
            (modes1 ~~ modes2)
        fun mode_instance_of (m1, m2) =
          let
            fun instance_of (Fun _, Input) = true
              | instance_of (Input, Input) = true
              | instance_of (Output, Output) = true
              | instance_of (Pair (m1, m2), Pair (m1', m2')) =
                  instance_of  (m1, m1') andalso instance_of (m2, m2')
              | instance_of (Pair (m1, m2), Input) =
                  instance_of (m1, Input) andalso instance_of (m2, Input)
              | instance_of (Pair (m1, m2), Output) =
                  instance_of (m1, Output) andalso instance_of (m2, Output)
              | instance_of (Input, Pair (m1, m2)) =
                  instance_of (Input, m1) andalso instance_of (Input, m2)
              | instance_of (Output, Pair (m1, m2)) =
                  instance_of (Output, m1) andalso instance_of (Output, m2)
              | instance_of _ = false
          in forall instance_of (strip_fun_mode m1 ~~ strip_fun_mode m2) end
        val derivs = all_derivations_of ctxt (all_modes_of ctxt) [] body
          |> filter (fn (d, missing_vars) =>
            let
              val (p_mode :: modes) = collect_context_modes d
            in
              null missing_vars andalso
              mode_instance_of (p_mode, user_mode) andalso
              the_default true (Option.map (valid modes) param_user_modes)
            end)
          |> map fst
        val deriv = case derivs of
            [] => error ("No mode possible for comprehension "
                    ^ Syntax.string_of_term ctxt t_compr)
          | [d] => d
          | d :: _ :: _ => (warning ("Multiple modes possible for comprehension "
                    ^ Syntax.string_of_term ctxt t_compr); d);
        val (_, outargs) = split_mode (head_mode_of deriv) all_args
        val t_pred = compile_expr comp_modifiers ctxt
          (body, deriv) [] additional_arguments;
        val T_pred = dest_monadT compfuns (fastype_of t_pred)
        val arrange = HOLogic.tupled_lambda (HOLogic.mk_tuple outargs) output
      in
        if null outargs then t_pred else mk_map compfuns T_pred T_compr arrange t_pred
      end
    else
      error "Evaluation with values is not possible because compilation with code_pred was not invoked"
  end

fun eval ctxt stats param_user_modes (options as (compilation, arguments)) k t_compr =
  let
    fun count xs x =
      let
        fun count' i [] = i
          | count' i (x' :: xs) = if x = x' then count' (i + 1) xs else count' i xs
      in count' 0 xs end
    fun accumulate xs = map (fn x => (x, count xs x)) (sort int_ord (distinct (op =) xs))
    val comp_modifiers =
      case compilation of
          Pred => predicate_comp_modifiers
        | Random => random_comp_modifiers
        | Depth_Limited => depth_limited_comp_modifiers
        | Depth_Limited_Random => depth_limited_random_comp_modifiers
        (*| Annotated => annotated_comp_modifiers*)
        | DSeq => dseq_comp_modifiers
        | Pos_Random_DSeq => pos_random_dseq_comp_modifiers
        | New_Pos_Random_DSeq => new_pos_random_dseq_comp_modifiers
        | Pos_Generator_DSeq => pos_generator_dseq_comp_modifiers
    val compfuns = Comp_Mod.compfuns comp_modifiers
    val additional_arguments =
      case compilation of
        Pred => []
      | Random => map (HOLogic.mk_number @{typ "code_numeral"}) arguments @
        [@{term "(1, 1) :: code_numeral * code_numeral"}]
      | Annotated => []
      | Depth_Limited => [HOLogic.mk_number @{typ "code_numeral"} (hd arguments)]
      | Depth_Limited_Random => map (HOLogic.mk_number @{typ "code_numeral"}) arguments @
        [@{term "(1, 1) :: code_numeral * code_numeral"}]
      | DSeq => []
      | Pos_Random_DSeq => []
      | New_Pos_Random_DSeq => []
      | Pos_Generator_DSeq => []
    val t = analyze_compr ctxt (comp_modifiers, additional_arguments) param_user_modes options t_compr;
    val T = dest_monadT compfuns (fastype_of t);
    val t' =
      if stats andalso compilation = New_Pos_Random_DSeq then
        mk_map compfuns T (HOLogic.mk_prodT (HOLogic.termT, @{typ code_numeral}))
          (absdummy T (HOLogic.mk_prod (HOLogic.term_of_const T $ Bound 0,
            @{term Code_Numeral.of_nat} $ (HOLogic.size_const T $ Bound 0)))) t
      else
        mk_map compfuns T HOLogic.termT (HOLogic.term_of_const T) t
    val thy = Proof_Context.theory_of ctxt
    val time_limit = seconds (Config.get ctxt values_timeout)
    val (ts, statistics) =
      (case compilation of
       (* Random =>
          fst (Predicate.yieldn k
          (Code_Eval.eval NONE ("Predicate_Compile_Core.random_eval_ref", random_eval_ref)
            (fn proc => fn g => fn s => g s |>> Predicate.map proc) thy t' []
            |> Random_Engine.run))*)
        Pos_Random_DSeq =>
          let
            val [nrandom, size, depth] = arguments
          in
            rpair NONE (TimeLimit.timeLimit time_limit (fn () => fst (DSequence.yieldn k
              (Code_Runtime.dynamic_value_strict (Dseq_Random_Result.get, put_dseq_random_result, "Predicate_Compile_Core.put_dseq_random_result")
                thy NONE (fn proc => fn g => fn nrandom => fn size => fn s => g nrandom size s |>> DSequence.map proc)
                  t' [] nrandom size
                |> Random_Engine.run)
              depth true)) ())
          end
      | DSeq =>
          rpair NONE (TimeLimit.timeLimit time_limit (fn () => fst (DSequence.yieldn k
            (Code_Runtime.dynamic_value_strict (Dseq_Result.get, put_dseq_result, "Predicate_Compile_Core.put_dseq_result")
              thy NONE DSequence.map t' []) (the_single arguments) true)) ())
      | Pos_Generator_DSeq =>
          let
            val depth = (the_single arguments)
          in
            rpair NONE (TimeLimit.timeLimit time_limit (fn () => fst (Lazy_Sequence.yieldn k
              (Code_Runtime.dynamic_value_strict (New_Dseq_Result.get, put_new_dseq_result, "Predicate_Compile_Core.put_new_dseq_result")
              thy NONE (fn proc => fn g => fn depth => g depth |> Lazy_Sequence.mapa proc)
              t' [] depth))) ())
          end
      | New_Pos_Random_DSeq =>
          let
            val [nrandom, size, depth] = arguments
            val seed = Random_Engine.next_seed ()
          in
            if stats then
              apsnd (SOME o accumulate) (split_list (TimeLimit.timeLimit time_limit
              (fn () => fst (Lazy_Sequence.yieldn k
                (Code_Runtime.dynamic_value_strict
                  (Lseq_Random_Stats_Result.get, put_lseq_random_stats_result, "Predicate_Compile_Core.put_lseq_random_stats_result")
                  thy NONE
                  (fn proc => fn g => fn nrandom => fn size => fn s => fn depth => g nrandom size s depth
                    |> Lazy_Sequence.mapa (apfst proc))
                    t' [] nrandom size seed depth))) ()))
            else rpair NONE
              (TimeLimit.timeLimit time_limit (fn () => fst (Lazy_Sequence.yieldn k
                (Code_Runtime.dynamic_value_strict
                  (Lseq_Random_Result.get, put_lseq_random_result, "Predicate_Compile_Core.put_lseq_random_result")
                  thy NONE 
                  (fn proc => fn g => fn nrandom => fn size => fn s => fn depth => g nrandom size s depth
                    |> Lazy_Sequence.mapa proc)
                    t' [] nrandom size seed depth))) ())
          end
      | _ =>
          rpair NONE (TimeLimit.timeLimit time_limit (fn () => fst (Predicate.yieldn k
            (Code_Runtime.dynamic_value_strict (Pred_Result.get, put_pred_result, "Predicate_Compile_Core.put_pred_result")
              thy NONE Predicate.map t' []))) ()))
     handle TimeLimit.TimeOut => error "Reached timeout during execution of values"
  in ((T, ts), statistics) end;

fun values param_user_modes ((raw_expected, stats), comp_options) k t_compr ctxt =
  let
    val ((T, ts), statistics) = eval ctxt stats param_user_modes comp_options k t_compr
    val setT = HOLogic.mk_setT T
    val elems = HOLogic.mk_set T ts
    val ([dots], ctxt') =
      Proof_Context.add_fixes [(@{binding dots}, SOME setT, Mixfix ("...", [], 1000))] ctxt 
    (* check expected values *)
    val union = Const (@{const_abbrev Set.union}, setT --> setT --> setT)
    val () =
      case raw_expected of
        NONE => ()
      | SOME s =>
        if eq_set (op =) (HOLogic.dest_set (Syntax.read_term ctxt s), ts) then ()
        else
          error ("expected and computed values do not match:\n" ^
            "expected values: " ^ Syntax.string_of_term ctxt (Syntax.read_term ctxt s) ^ "\n" ^
            "computed values: " ^ Syntax.string_of_term ctxt elems ^ "\n")
  in
    ((if k = ~1 orelse length ts < k then elems else union $ elems $ Free (dots, setT), statistics), ctxt')
  end;

fun values_cmd print_modes param_user_modes options k raw_t state =
  let
    val ctxt = Toplevel.context_of state
    val t = Syntax.read_term ctxt raw_t
    val ((t', stats), ctxt') = values param_user_modes options k t ctxt
    val ty' = Term.type_of t'
    val ctxt'' = Variable.auto_fixes t' ctxt'
    val pretty_stat =
      case stats of
          NONE => []
        | SOME xs =>
          let
            val total = fold (curry (op +)) (map snd xs) 0
            fun pretty_entry (s, n) =
              [Pretty.str "size", Pretty.brk 1,
               Pretty.str (string_of_int s), Pretty.str ":", Pretty.brk 1,
               Pretty.str (string_of_int n), Pretty.fbrk]
          in
            [Pretty.fbrk, Pretty.str "Statistics:", Pretty.fbrk,
             Pretty.str "total:", Pretty.brk 1, Pretty.str (string_of_int total), Pretty.fbrk]
             @ maps pretty_entry xs
          end
    val p = Print_Mode.with_modes print_modes (fn () =>
      Pretty.block ([Pretty.quote (Syntax.pretty_term ctxt'' t'), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ ctxt'' ty')]
        @ pretty_stat)) ();
  in Pretty.writeln p end;

end;
