(*  Title:      HOL/TPTP/TPTP_Parser/tptp_reconstruct.ML
    Author:     Nik Sultana, Cambridge University Computer Laboratory

Reconstructs TPTP proofs in Isabelle/HOL.
Specialised to work with proofs produced by LEO-II.

TODO
 - Proof transformation to remove "copy" steps, and perhaps other dud inferences.
*)

signature TPTP_RECONSTRUCT =
sig
  (* Interface used by TPTP_Reconstruct.thy, to define LEO-II proof reconstruction. *)

  datatype formula_kind =
      Conjunctive of bool option
    | Disjunctive of bool option
    | Biimplicational of bool option
    | Negative of bool option
    | Existential of bool option * typ
    | Universal of bool option * typ
    | Equational of bool option * typ
    | Atomic of bool option
    | Implicational of bool option
  type formula_meaning =
    (string *
     {role : TPTP_Syntax.role,
      fmla : term,
      source_inf_opt : TPTP_Proof.source_info option})
  type proof_annotation =
    {problem_name : TPTP_Problem_Name.problem_name,
     skolem_defs : ((*skolem const name*)string * Binding.binding) list,
     defs : ((*node name*)string * Binding.binding) list,
     axs : ((*node name*)string * Binding.binding) list,
     (*info for each node (for all lines in the TPTP proof)*)
     meta : formula_meaning list}
  type rule_info =
    {inference_name : string, (*name of calculus rule*)
     inference_fmla : term, (*the inference as a term*)
     parents : string list}

  exception UNPOLARISED of term

  val remove_polarity : bool -> term -> term * bool
  val interpret_bindings :
     TPTP_Problem_Name.problem_name -> theory -> TPTP_Proof.parent_detail list -> (string * term) list -> (string * term) list
  val diff_and_instantiate : Proof.context -> thm -> term -> term -> thm (*FIXME from library*)
  val strip_top_all_vars : (string * typ) list -> term -> (string * typ) list * term
  val strip_top_All_vars : term -> (string * typ) list * term
  val strip_top_All_var : term -> (string * typ) * term
  val new_consts_between : term -> term -> term list
  val get_pannot_of_prob : theory -> TPTP_Problem_Name.problem_name -> proof_annotation
  val inference_at_node : 'a -> TPTP_Problem_Name.problem_name -> formula_meaning list -> string -> rule_info option
  val node_info : (string * 'a) list -> ('a -> 'b) -> string -> 'b

  type step_id = string
  datatype rolling_stock =
      Step of step_id
    | Assumed
    | Unconjoin
    | Split of step_id (*where split occurs*) *
               step_id (*where split ends*) *
               step_id list (*children of the split*)
    | Synth_step of step_id (*A step which doesn't necessarily appear in
      the original proof, or which has been modified slightly for better
      handling by Isabelle*)
    | Annotated_step of step_id * string (*Same interpretation as
      "Step", except that additional information is attached. This is
      currently used for debugging: Steps are mapped to Annotated_steps
      and their rule names are included as strings*)
    | Definition of step_id (*Mirrors TPTP role*)
    | Axiom of step_id (*Mirrors TPTP role*)
    | Caboose


  (* Interface for using the proof reconstruction. *)

  val import_thm : bool -> Path.T list -> Path.T -> (proof_annotation -> theory -> proof_annotation * theory) -> theory -> theory
  val get_fmlas_of_prob : theory -> TPTP_Problem_Name.problem_name -> TPTP_Interpret.tptp_formula_meaning list
  val structure_fmla_meaning : 'a * 'b * 'c * 'd -> 'a * {fmla: 'c, role: 'b, source_inf_opt: 'd}
  val make_skeleton : Proof.context -> proof_annotation -> rolling_stock list
  val naive_reconstruct_tacs :
     (Proof.context -> TPTP_Problem_Name.problem_name -> step_id -> thm) ->
     TPTP_Problem_Name.problem_name -> Proof.context -> (rolling_stock * term option * (thm * tactic) option) list
  val naive_reconstruct_tac :
     Proof.context -> (Proof.context -> TPTP_Problem_Name.problem_name -> step_id -> thm) -> TPTP_Problem_Name.problem_name -> tactic
  val reconstruct : Proof.context -> (TPTP_Problem_Name.problem_name -> tactic) -> TPTP_Problem_Name.problem_name -> thm
end

structure TPTP_Reconstruct : TPTP_RECONSTRUCT =
struct

open TPTP_Reconstruct_Library
open TPTP_Syntax

(*FIXME move to more general struct*)
(*Extract the formulas of an imported TPTP problem -- these formulas
  may make up a proof*)
fun get_fmlas_of_prob thy prob_name : TPTP_Interpret.tptp_formula_meaning list =
  AList.lookup (op =) (TPTP_Interpret.get_manifests thy) prob_name
  |> the |> #3 (*get formulas*);


(** General **)

(* Proof annotations *)

(*FIXME modify TPTP_Interpret.tptp_formula_meaning into this type*)
type formula_meaning =
  (string *
   {role : TPTP_Syntax.role,
    fmla : term,
    source_inf_opt : TPTP_Proof.source_info option})

fun apply_to_parent_info f
   (n, {role, fmla, source_inf_opt}) =
  let
    val source_inf_opt' =
      case source_inf_opt of
          NONE => NONE
        | SOME (TPTP_Proof.Inference (inf_name, sinfos, pinfos)) =>
            SOME (TPTP_Proof.Inference (inf_name, sinfos, f pinfos))
  in
   (n, {role = role, fmla = fmla, source_inf_opt = source_inf_opt'})
  end

fun structure_fmla_meaning (s, r, t, info) =
  (s, {role = r, fmla = t, source_inf_opt = info})

type proof_annotation =
  {problem_name : TPTP_Problem_Name.problem_name,
   skolem_defs : ((*skolem const name*)string * Binding.binding) list,
   defs : ((*node name*)string * Binding.binding) list,
   axs : ((*node name*)string * Binding.binding) list,
   (*info for each node (for all lines in the TPTP proof)*)
   meta : formula_meaning list}

fun empty_pannot prob_name =
  {problem_name = prob_name,
   skolem_defs = [],
   defs = [],
   axs = [],
   meta = []}


(* Storage of proof data *)

exception MANIFEST of TPTP_Problem_Name.problem_name * string (*FIXME move to TPTP_Interpret?*)

type manifest = TPTP_Problem_Name.problem_name * proof_annotation

(*manifest equality simply depends on problem name*)
fun manifest_eq ((prob_name1, _), (prob_name2, _)) = prob_name1 = prob_name2

structure TPTP_Reconstruction_Data = Theory_Data
(
  type T = manifest list
  val empty = []
  fun merge data : T = Library.merge manifest_eq data
)
val get_manifests : theory -> manifest list = TPTP_Reconstruction_Data.get

fun update_manifest prob_name pannot thy =
  let
    val idx =
      find_index
        (fn (n, _) => n = prob_name)
        (get_manifests thy)
    val transf = (fn _ =>
      (prob_name, pannot))
  in
    TPTP_Reconstruction_Data.map
      (nth_map idx transf)
      thy
  end

(*similar to get_fmlas_of_prob but for proofs*)
fun get_pannot_of_prob thy prob_name : proof_annotation =
  case AList.lookup (op =) (get_manifests thy) prob_name of
      SOME pa => pa
    | NONE => raise (MANIFEST (prob_name, "Could not find proof annotation"))


(* Constants *)

(*Prefix used for naming inferences which were added during proof
transformation. (e.g., this is used to name "bind"-inference nodes
described below)*)
val inode_prefixK = "inode"

(*New inference rule name, which is added to indicate that some
variable has been instantiated. Additional proof metadata will
indicate which variable, and how it was instantiated*)
val bindK = "bind"

(*New inference rule name, which is added to indicate that some
(validity-preserving) preprocessing has been done to a (singleton)
clause prior to it being split.*)
val split_preprocessingK = "split_preprocessing"


(* Storage of internal values *)

type tptp_reconstruction_state = {next_int : int}
structure TPTP_Reconstruction_Internal_Data = Theory_Data
(
  type T = tptp_reconstruction_state
  val empty = {next_int = 0}
  fun merge data : T = snd data
)

(*increment internal counter, and obtain the current next value*)
fun get_next_int thy : int * theory =
  let
    val state = TPTP_Reconstruction_Internal_Data.get thy
    val state' = {next_int = 1 + #next_int state}
  in
    (#next_int state,
     TPTP_Reconstruction_Internal_Data.put state' thy)
  end

(*FIXME in some applications (e.g. where the name is used for an
   inference node) need to check that the name is fresh, to avoid
   collisions with other bits of the proof*)
val get_next_name =
  get_next_int
  #> apfst (fn i => inode_prefixK ^ Int.toString i)


(* Building the index *)

(*thrown when we're expecting a TPTP_Proof.Bind annotation but find something else*)
exception NON_BINDING
(*given a list of pairs consisting of a variable name and
  TPTP formula, returns the list consisting of the original
  variable name and the interpreted HOL formula. Needs the
  problem name to ensure use of correct interpretations for
  constants and types.*)
fun interpret_bindings (prob_name : TPTP_Problem_Name.problem_name) thy bindings acc =
  if null bindings then acc
  else
    case hd bindings of
        TPTP_Proof.Bind (v, fmla) =>
          let
            val (type_map, const_map) =
                case AList.lookup (op =) (TPTP_Interpret.get_manifests thy) prob_name of
                    NONE => raise (MANIFEST (prob_name, "Problem details not found in interpretation manifest"))
                  | SOME (type_map, const_map, _) => (type_map, const_map)

            (*FIXME get config from the envir or make it parameter*)
            val config =
              {cautious = true,
               problem_name = SOME prob_name}
            val result =
              (v,
               TPTP_Interpret.interpret_formula
                config TPTP_Syntax.THF
                const_map [] type_map fmla thy
               |> fst)
          in
            interpret_bindings prob_name thy (tl bindings) (result :: acc)
          end
      | _ => raise NON_BINDING

type rule_info =
  {inference_name : string, (*name of calculus rule*)
   inference_fmla : term, (*the inference as a term*)
   parents : string list}

(*Instantiates a binding in orig_parent_fmla. Used in a proof
  transformation to factor out instantiations from inferences.*)
fun apply_binding thy prob_name orig_parent_fmla target_fmla bindings =
  let
    val bindings' = interpret_bindings prob_name thy bindings []

    (*capture selected free variables. these variables, and their
      intended de Bruijn index, are included in "var_ctxt"*)
    fun bind_free_vars var_ctxt t =
      case t of
          Const _ => t
        | Var _ => t
        | Bound _ => t
        | Abs (x, ty, t') => Abs (x, ty, bind_free_vars (x :: var_ctxt) t')
        | Free (x, ty) =>
            let
              val idx = find_index (fn y => y = x) var_ctxt
            in
              if idx > ~1 andalso
                 ty = dummyT (*this check not really needed*) then
                  Bound idx
              else t
            end
        | t1 $ t2 => bind_free_vars var_ctxt t1 $ bind_free_vars var_ctxt t2

    (*Instantiate specific quantified variables:
      Look for subterms of form (! (% x. M)) where "x" appears as a "bound_var",
      then replace "x" for "body" in "M".
      Should only be applied at formula top level -- i.e., once past the quantifier
      prefix we needn't bother with looking for bound_vars.
      "var"_ctxt is used to keep track of lambda-bindings we encounter, to capture
      free variables in "body" correctly (i.e., replace Free with Bound having the
      right index)*)
    fun instantiate_bound (binding as (bound_var, body)) (initial as (var_ctxt, t))  =
      case t of
          Const _ => initial
        | Free _ => initial
        | Var _ => initial
        | Bound _ => initial
        | Abs _ => initial
        | t1 $ (t2 as Abs (x, ty, t')) =>
            if is_Const t1 then
              (*Could be fooled by shadowing, but if order matters
                then should still be able to handle formulas like
                (! X, X. F).*)
              if x = bound_var andalso
                 dest_Const_name t1 = \<^const_name>\<open>All\<close> then
                  (*Body might contain free variables, so bind them using "var_ctxt".
                    this involves replacing instances of Free with instances of Bound
                    at the right index.*)
                  let val body' = bind_free_vars var_ctxt body
                  in
                    (var_ctxt,
                     betapply (t2, body'))
                  end
              else
                  let
                    val (var_ctxt', rest) = instantiate_bound binding (x :: var_ctxt, t')
                  in
                    (var_ctxt',
                     t1 $ Abs (x, ty, rest))
                  end
            else initial
        | t1 $ t2 =>
            let
              val (var_ctxt', rest) = instantiate_bound binding (var_ctxt, t2)
            in
              (var_ctxt', t1 $ rest)
            end

    (*Here we preempt the following problem:
     if have (! X1, X2, X3. body), and X1 is instantiated to
     "c X2 X3", then the current code will yield
     (! X2, X3, X2a, X3a. body').
     To avoid this, we must first push X1 in, before calling
     instantiate_bound, to make sure that bound variables don't
     get free.*)
    fun safe_instantiate_bound (binding as (bound_var, body)) (var_ctxt, t) =
       instantiate_bound binding
         (var_ctxt, push_allvar_in bound_var t)

    (*return true if one of the types is polymorphic*)
    fun is_polymorphic tys =
      if null tys then false
      else
        case hd tys of
            Type (_, tys') => is_polymorphic (tl tys @ tys')
          | TFree _ => true
          | TVar _ => true

    (*find the type of a quantified variable, at the "topmost" binding
      occurrence*)
    local
      fun type_of_quantified_var' s ts =
        if null ts then NONE
        else
          case hd ts of
              Const _ => type_of_quantified_var' s (tl ts)
            | Free _ => type_of_quantified_var' s (tl ts)
            | Var _ => type_of_quantified_var' s (tl ts)
            | Bound _ => type_of_quantified_var' s (tl ts)
            | Abs (s', ty, t') =>
                if s = s' then SOME ty
                else type_of_quantified_var' s (t' :: tl ts)
            | t1 $ t2 => type_of_quantified_var' s (t1 :: t2 :: tl ts)
    in
      fun type_of_quantified_var s =
        single #> type_of_quantified_var' s
    end

    (*Form the universal closure of "t".
      NOTE remark above "val frees" about ordering of quantified variables*)
    fun close_formula t =
      let
          (*The ordering of Frees in this list affects the order in which variables appear
            in the quantification prefix. Currently this is assumed not to matter.
            This consists of a list of pairs: the first element consists of the "original"
            free variable, and the latter consists of the monomorphised equivalent. The
            two elements are identical if the original is already monomorphic.
            This monomorphisation is needed since, owing to TPTP's lack of type annotations,
            variables might not be constrained by type info. This results in them being
            interpreted as polymorphic. E.g., this issue comes up in CSR148^1*)
          val frees_monomorphised =
            fold_aterms
              (fn t => fn rest =>
                 if is_Free t then
                   let
                     val (s, ty) = dest_Free t
                     val ty' =
                       if ty = dummyT orelse is_polymorphic [ty] then
                         the (type_of_quantified_var s target_fmla)
                       else ty
                   in insert (op =) (t, Free (s, ty')) rest
                   end
                 else rest)
              t []
      in
        Term.subst_free frees_monomorphised t
        |> fold (fn (s, ty) => fn t =>
                    HOLogic.mk_all (s, ty, t))
              (map (snd #> dest_Free) frees_monomorphised)
      end

    (*FIXME currently assuming that we're only ever given a single binding each time this is called*)
    val _ = \<^assert> (length bindings' = 1)

  in
    fold safe_instantiate_bound bindings' ([], HOLogic.dest_Trueprop orig_parent_fmla)
    |> snd (*discard var typing context*)
    |> close_formula
    |> singleton (Type_Infer_Context.infer_types (Context.proof_of (Context.Theory thy)))
    |> HOLogic.mk_Trueprop
    |> rpair bindings'
  end

exception RECONSTRUCT of string

(*Some of these may be redundant wrt the original aims of this
  datatype, but it's useful to have a datatype to classify formulas
  for use by other functions as well.*)
datatype formula_kind =
    Conjunctive of bool option
  | Disjunctive of bool option
  | Biimplicational of bool option
  | Negative of bool option
  | Existential of bool option * typ
  | Universal of bool option * typ
  | Equational of bool option * typ
  | Atomic of bool option
  | Implicational of bool option

exception UNPOLARISED of term
(*Remove "= $true" or "= $false$ from the edge
  of a formula. Use "try" in case formula is not
  polarised.*)
fun remove_polarity strict formula =
  case try HOLogic.dest_eq formula of
      NONE => if strict then raise (UNPOLARISED formula)
              else (formula, true)
    | SOME (x, p as \<^term>\<open>True\<close>) => (x, true)
    | SOME (x, p as \<^term>\<open>False\<close>) => (x, false)
    | SOME (x, _) =>
        if strict then raise (UNPOLARISED formula)
        else (formula, true)

(*flattens a formula wrt associative operators*)
fun flatten formula_kind formula =
  let
    fun is_conj (Const (\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) = true
      | is_conj _ = false
    fun is_disj (Const (\<^const_name>\<open>HOL.disj\<close>, _) $ _ $ _) = true
      | is_disj _ = false
    fun is_iff (Const (\<^const_name>\<open>HOL.eq\<close>, ty) $ _ $ _) =
          ty = ([HOLogic.boolT, HOLogic.boolT] ---> HOLogic.boolT)
      | is_iff _ = false

    fun flatten' formula acc =
      case formula of
          Const (\<^const_name>\<open>HOL.conj\<close>, _) $ t1 $ t2 =>
            (case formula_kind of
                 Conjunctive _ =>
                   let
                     val left =
                       if is_conj t1 then flatten' t1 acc else (t1 :: acc)
                   in
                       if is_conj t2 then flatten' t2 left else (t2 :: left)
                   end
               | _ => formula :: acc)
        | Const (\<^const_name>\<open>HOL.disj\<close>, _) $ t1 $ t2 =>
            (case formula_kind of
                 Disjunctive _ =>
                   let
                     val left =
                       if is_disj t1 then flatten' t1 acc else (t1 :: acc)
                   in
                       if is_disj t2 then flatten' t2 left else (t2 :: left)
                   end
               | _ => formula :: acc)
        | Const (\<^const_name>\<open>HOL.eq\<close>, ty) $ t1 $ t2 =>
            if ty = ([HOLogic.boolT, HOLogic.boolT] ---> HOLogic.boolT) then
              case formula_kind of
                   Biimplicational _ =>
                     let
                       val left =
                         if is_iff t1 then flatten' t1 acc else (t1 :: acc)
                     in
                         if is_iff t2 then flatten' t2 left else (t2 :: left)
                     end
                 | _ => formula :: acc
            else formula :: acc
        | _ => [formula]

    val formula' = try_dest_Trueprop formula
  in
    case formula_kind of
        Conjunctive (SOME _) =>
          remove_polarity false formula'
          |> fst
          |> (fn t => flatten' t [])
      | Disjunctive (SOME _) =>
          remove_polarity false formula'
          |> fst
          |> (fn t => flatten' t [])
      | Biimplicational (SOME _) =>
          remove_polarity false formula'
          |> fst
          |> (fn t => flatten' t [])
      | _ => flatten' formula' []
  end

fun node_info fms projector node_name =
  case AList.lookup (op =) fms node_name of
      NONE =>
        raise (RECONSTRUCT ("node " ^ node_name ^
                            " doesn't exist"))
    | SOME info => projector info

(*Given a list of parent infos, extract the parent node names
  and the additional info (e.g., if there was an instantiation
  in addition to the inference).
  if "filtered"=true then exclude axiom and definition parents*)
fun dest_parent_infos filtered fms parent_infos : {name : string, details : TPTP_Proof.parent_detail list} list =
  let
    (*Removes "definition" dependencies since these play no
      logical role -- i.e. they just give the expansions of
      constants.
      Removes "axiom" dependencies since these do not need to
      be derived; the reconstruction handler in "leo2_tac" can
      pick up the relevant axioms (using the info in the proof
      annotation) and use them in its reconstruction.
    *)
    val filter_deps =
      filter (fn {name, ...} =>
        let
          val role = node_info fms #role name
        in role <> TPTP_Syntax.Role_Definition andalso
            role <> TPTP_Syntax.Role_Axiom
        end)
    val parent_nodelist =
      parent_infos
      |> map (fn n =>
                 case n of
                     TPTP_Proof.Parent parent => {name = parent, details = []}
                   | TPTP_Proof.ParentWithDetails (parent, details) =>
                     {name = parent, details = details})
  in
    parent_nodelist
    |> filtered ? filter_deps
  end

fun parents_of_node fms n =
  case node_info fms #source_inf_opt n of
      NONE => []
    | SOME (TPTP_Proof.File _) => []
    | SOME (TPTP_Proof.Inference (_, _ : TPTP_Proof.useful_info_as list, parent_infos)) =>
        dest_parent_infos false fms parent_infos
        |> map #name

exception FIND_ANCESTOR_USING_RULE of string
(*BFS for an ancestor inference involving a specific rule*)
fun find_ancestor_using_rule pannot inference_rule (fringe : string list) : string =
  if null fringe then
    raise (FIND_ANCESTOR_USING_RULE inference_rule)
  else
    case node_info (#meta pannot) #source_inf_opt (hd fringe) of
        NONE => find_ancestor_using_rule pannot inference_rule (tl fringe)
      | SOME (TPTP_Proof.File _) => find_ancestor_using_rule pannot inference_rule (tl fringe)
      | SOME (TPTP_Proof.Inference (rule_name, _ : TPTP_Proof.useful_info_as list, parent_infos)) =>
          if rule_name = inference_rule then hd fringe
          else
            find_ancestor_using_rule pannot inference_rule
             (tl fringe @
              map #name (dest_parent_infos true (#meta pannot) parent_infos))

(*Given a node in the proof, produce the term representing the inference
  that took place in that step, the inference rule used, and which
  other (non-axiom and non-definition) nodes participated in the
  inference*)
fun inference_at_node thy (prob_name : TPTP_Problem_Name.problem_name)
     (fms : formula_meaning list) from : rule_info option =
    let
      exception INFERENCE_AT_NODE of string

      (*lookup formula associated with a node*)
      val fmla_of_node =
          node_info fms #fmla
          #> try_dest_Trueprop

      fun build_inference_info rule_name parent_infos =
        let
          val _ = \<^assert> (not (null parent_infos))

          (*hypothesis formulas (with bindings already
            instantiated during the proof-transformation
            applied when loading the proof),
            including any axioms or definitions*)
          val parent_nodes =
            dest_parent_infos false fms parent_infos
            |> map #name

          val parent_fmlas = map fmla_of_node (rev(*FIXME can do away with this? it matters because of order of conjunction. is there a matching rev elsewhere?*) parent_nodes)

          val inference_term =
            if null parent_fmlas then
                fmla_of_node from
                |> HOLogic.mk_Trueprop
            else
                Logic.mk_implies
                 (fold
                    (curry HOLogic.mk_conj)
                    (tl parent_fmlas)
                    (hd parent_fmlas)
                  |> HOLogic.mk_Trueprop,
                  fmla_of_node from |> HOLogic.mk_Trueprop)
        in
          SOME {inference_name = rule_name,
                inference_fmla = inference_term,
                parents = parent_nodes}
        end
    in
      (*examine node's "source" annotation: we're only interested
        if it's an inference*)
      case node_info fms #source_inf_opt from of
                NONE => NONE
              | SOME (TPTP_Proof.File _) => NONE
              | SOME (TPTP_Proof.Inference (rule_name, _ : TPTP_Proof.useful_info_as list, parent_infos)) =>
                  if List.null parent_infos then
                    raise (INFERENCE_AT_NODE
                            ("empty parent list for node " ^
                             from ^ ": check proof format"))
                  else
                    build_inference_info rule_name parent_infos
    end


(** Proof skeleton **)

(* Emulating skeleton steps *)

(*
Builds a rule (thm) of the following form:


                  prem1                   premn
                   ...         ...         ...
   major_prem     conc1                   concn
  -----------------------------------------------
                    conclusion

where major_prem is a disjunction of prem1,...,premn.
*)
fun make_elimination_rule_t ctxt major_prem prems_and_concs conclusion =
  let
    val thy = Proof_Context.theory_of ctxt
    val minor_prems =
      map (fn (v, conc) =>
        Logic.mk_implies (v, HOLogic.mk_Trueprop conc))
        prems_and_concs
  in
    (Logic.list_implies
     (major_prem :: minor_prems,
     conclusion))
  end

(*In summary, we emulate an n-way splitting rule via an n-way
  disjunction elimination.

  Given a split formula and conclusion, we prove a rule which
  simulates the split. The conclusion is assumed to be a conjunction
  of conclusions for each branch of the split. The
  "minor_prem_assumptions" are the assumptions discharged in each
  branch; they're passed to the function to make sure that the
  generated rule is compatible with the skeleton (since the skeleton
  fixes the "order" of the reconstruction, based on the proof's
  structure).

  Concretely, if P is "(_ & _) = $false" or "(_ | _) = $true" then
  splitting behaves as follows:

                     P
      -------------------------------
       _ = $false         _ = $false
          ...       ...       ...
           R1                  Rn
      -------------------------------
               R1 & ... & Rn

  Splitting (binary) iffs works as follows:

                  (A <=> B) = $false
      ------------------------------------------
       (A => B) = $false      (B => A) = $false
             ...                     ...
              R1                      R2
      ------------------------------------------
                        R1 & R2
*)
fun simulate_split ctxt split_fmla minor_prem_assumptions conclusion =
  let
    val prems_and_concs =
      ListPair.zip (minor_prem_assumptions, flatten (Conjunctive NONE) conclusion)

    val rule_t = make_elimination_rule_t ctxt split_fmla prems_and_concs conclusion

    (*these are replaced by fresh variables in the abstract term*)
    val abstraction_subterms =
      (map (try_dest_Trueprop #> remove_polarity true #> fst)
              minor_prem_assumptions)

    (*generate an abstract rule as a term...*)
    val abs_rule_t =
      abstract
        abstraction_subterms
        rule_t
      |> snd (*ignore mapping info. this is a bit wasteful*)
             (*FIXME optimisation: instead on relying on diff
                to regenerate this info, could use it directly*)

    (*...and validate the abstract rule*)
    val abs_rule_thm =
      Goal.prove ctxt [] [] abs_rule_t
       (fn pdata => HEADGOAL (blast_tac (#context pdata)))
      |> Drule.export_without_context
  in
    (*Instantiate the abstract rule based on the contents of the
      required instance*)
    diff_and_instantiate ctxt abs_rule_thm (Thm.prop_of abs_rule_thm) rule_t
  end


(* Building the skeleton *)

type step_id = string
datatype rolling_stock =
    Step of step_id
  | Assumed
  | Unconjoin
  | Split of step_id (*where split occurs*) *
             step_id (*where split ends*) *
             step_id list (*children of the split*)
  | Synth_step of step_id (*A step which doesn't necessarily appear in
    the original proof, or which has been modified slightly for better
    handling by Isabelle*) (*FIXME "inodes" should be made into Synth_steps*)
  | Annotated_step of step_id * string (*Same interpretation as
    "Step", except that additional information is attached. This is
    currently used for debugging: Steps are mapped to Annotated_steps
    and their rule names are included as strings*)
  | Definition of step_id (*Mirrors TPTP role*)
  | Axiom of step_id (*Mirrors TPTP role*)
(*  | Derived of step_id -- to be used by memoization*)
  | Caboose

fun stock_to_string (Step n) = n
  | stock_to_string (Annotated_step (n, anno)) = n ^ "(" ^ anno ^ ")"
  | stock_to_string _ = error "Stock is not a step" (*FIXME more meaningful message*)

fun filter_by_role tptp_role =
  filter
   (fn (_, info) =>
       #role info = tptp_role)

fun filter_by_name node_name =
  filter
   (fn (n, _) =>
       n = node_name)

exception NO_MARKER_NODE
(*We fall back on node "1" in case the proof is not that of a theorem*)
fun proof_beginning_node fms =
  let
    val result =
      cascaded_filter_single true
       [filter_by_role TPTP_Syntax.Role_Conjecture,
        filter_by_name "1"] (*FIXME const*)
       fms
  in
    case result of
        SOME x => fst x (*get the node name*)
      | NONE => raise NO_MARKER_NODE
  end

(*Get the name of the node where the proof ends*)
fun proof_end_node fms =
  (*FIXME this isn't very nice: we assume that the last line in the
    proof file is the closing line of the proof. It would be nicer if
    such a line is specially marked (with a role), since there is no
    obvious ordering on names, since they can be strings.
    Another way would be to run an analysis on the graph to find
    this node, since it has properties which should make it unique
    in a graph*)
  fms
  |> hd (*since proof has been reversed prior*)
  |> fst (*get node name*)

(*Generate list of (possibly reconstructed) inferences which can be
  composed together to reconstruct the whole proof.*)
fun make_skeleton ctxt (pannot : proof_annotation) : rolling_stock list =
  let
    val thy = Proof_Context.theory_of ctxt

    fun stock_is_ax_or_def (Axiom _) = true
      | stock_is_ax_or_def (Definition _) = true
      | stock_is_ax_or_def _ = false

    fun stock_of n =
      case node_info (#meta pannot) #role n of
          TPTP_Syntax.Role_Definition => (true, Definition n)
        | TPTP_Syntax.Role_Axiom => (true, Axiom n)
        | _ => (false, Step n)

    fun n_is_split_conjecture (inference_info : rule_info option) =
      case inference_info of
          NONE => false
        | SOME inference_info => #inference_name inference_info = "split_conjecture"

    (*Different kinds of inference sequences:
        - Linear: (just add a step to the skeleton)
           ---...---

        - Fan-in: (treat each in-path as conjoined with the others. Linearise all the paths, and concatenate them.)
                  /---...
           ------<
                  \---...

        - Real split: Instead of treating as a conjunction, as in
           normal fan-ins, we need to treat specially by looking
           at the location where the split occurs, and turn the
           split inference into a validity-preserving subproof.
           As with fan-ins, we handle each fan-in path, and
           concatenate.
                  /---...---\
           ------<           >------
                  \---...---/

        - Fake split: (treat like linear, since there isn't a split-node)
           ------<---...----------

      Different kinds of sequences endings:
        - "Stop before": Non-decreasing list of nodes where should terminate.
                         This starts off with the end node, and the split_nodes
                         will be added dynamically as the skeleton is built.
        - Axiom/Definition
     *)

    (*The following functions build the skeleton for the reconstruction starting
      from the node labelled "n" and stopping just before an element in stop_just_befores*)
    (*FIXME could throw exception if none of stop_just_befores is ever encountered*)

    (*This approach below is naive because it linearises the proof DAG, and this would
      duplicate some effort if the DAG isn't already linear.*)
    exception SKELETON

    fun check_parents stop_just_befores n =
      let
        val parents = parents_of_node (#meta pannot) n
      in
        if length parents = 1 then
          AList.lookup (op =) stop_just_befores (the_single parents)
        else
          NONE
      end

    fun naive_skeleton' stop_just_befores n =
      case check_parents stop_just_befores n of
          SOME skel => skel
        | NONE =>
            let
              val inference_info = inference_at_node thy (#problem_name pannot) (#meta pannot) n
            in
                if is_none inference_info then
                  (*this is the case for the conjecture, definitions and axioms*)
                    if node_info (#meta pannot) #role n = TPTP_Syntax.Role_Definition then
                      [(Definition n), Assumed]
                    else if node_info (#meta pannot) #role n = TPTP_Syntax.Role_Axiom then
                      [Axiom n]
                    else raise SKELETON
                else
                  let
                    val inference_info = the inference_info
                    val parents = #parents inference_info
                  in
                    (*FIXME memoize antecedent_steps?*)
                    if #inference_name inference_info = "solved_all_splits" andalso length parents > 1 then
                      (*splitting involves fanning out then in; this is to be
                        treated different than other fan-out-ins.*)
                      let
                        (*find where the proofs fanned-out: pick some antecedent,
                          then find ancestor to use a "split_conjecture" inference.*)
                        (*NOTE we assume that splits can't be nested*)
                        val split_node =
                          find_ancestor_using_rule pannot "split_conjecture" [hd parents]
                          |> parents_of_node (#meta pannot)
                          |> the_single

                        (*compute the skeletons starting at parents to either the split_node
                          if the antecedent is descended from the split_node, or the
                          stop_just_before otherwise*)
                        val skeletons_up =
                          map (naive_skeleton' ((split_node, [Assumed]) :: stop_just_befores)) parents
                      in
                        (*point to the split node, so that custom rule can be built later on*)
                        Step n :: (Split (split_node, n, parents)) :: (*this will create the elimination rule*)
                         naive_skeleton' stop_just_befores split_node @ (*this will discharge the major premise*)
                         flat skeletons_up @ [Assumed] (*this will discharge the minor premises*)
                      end
                    else if length parents > 1 then
                      (*Handle fan-in nodes which aren't split-sinks by
                        enclosing each branch but one in conjI-assumption invocations*)
                        let
                          val skeletons_up =
                            map (naive_skeleton' stop_just_befores) parents
                        in
                          Step n :: concat_between skeletons_up (SOME Unconjoin, NONE) @ [Assumed]
                        end
                    else
                      Step n :: naive_skeleton' stop_just_befores (the_single parents)
                  end
            end
  in
    if List.null (#meta pannot) then [] (*in case "proof" file is empty*)
    else
      naive_skeleton'
       [(proof_beginning_node (#meta pannot), [Assumed])]
       (proof_end_node (#meta pannot))
      (*make last step the Caboose*)
      |> rev |> tl |> cons Caboose |> rev (*FIXME hacky*)
  end


(* Using the skeleton *)

exception SKELETON
local
    (*Change the negated assumption (which is output by the contradiction rule) into
      a form familiar to Leo2*)
    val neg_eq_false =
      @{lemma "!! P. (~ P) ==> (P = False)" by auto}

    (*FIXME this is just a dummy thm to annotate the assumption tac "atac"*)
    val solved_all_splits =
      @{lemma "False = True ==> False" by auto}

    fun skel_to_naive_tactic ctxt prover_tac prob_name skel memo = fn st =>
      let
        val thy = Proof_Context.theory_of ctxt
        val pannot = get_pannot_of_prob thy prob_name
        fun tac_and_memo node memo =
          case AList.lookup (op =) memo node of
              NONE =>
                let
                  val tac =
                    (*FIXME formula_sizelimit not being
                            checked here*)
                    prover_tac ctxt prob_name node
                in (tac, (node, tac) :: memo) end
            | SOME tac => (tac, memo)
        fun rest skel' memo =
          skel_to_naive_tactic ctxt prover_tac prob_name skel' memo

        val tactic =
          if null skel then
            raise SKELETON (*FIXME or classify it as a Caboose: TRY (HEADGOAL atac) *)
          else
            case hd skel of
                Assumed => TRY (HEADGOAL (assume_tac ctxt)) THEN rest (tl skel) memo
              | Caboose => TRY (HEADGOAL (assume_tac ctxt))
              | Unconjoin => resolve_tac ctxt @{thms conjI} 1 THEN rest (tl skel) memo
              | Split (split_node, solved_node, antes) =>
                  let
                    val split_fmla = node_info (#meta pannot) #fmla split_node
                    val conclusion =
                      (inference_at_node thy prob_name (#meta pannot) solved_node
                       |> the
                       |> #inference_fmla)
                      |> Logic.dest_implies (*FIXME there might be !!-variables?*)
                      |> #1
                    val minor_prems_assumps =
                      map (fn ante => find_ancestor_using_rule pannot "split_conjecture" [ante]) antes
                      |> map (node_info (#meta pannot) #fmla)
                    val split_thm =
                      simulate_split ctxt split_fmla minor_prems_assumps conclusion
                  in
                    resolve_tac ctxt [split_thm] 1 THEN rest (tl skel) memo
                  end
              | Step s =>
                  let
                    val (th, memo') = tac_and_memo s memo
                  in
                    resolve_tac ctxt [th] 1 THEN rest (tl skel) memo'
                  end
              | Definition n =>
                  let
                    val def_thm =
                      case AList.lookup (op =) (#defs pannot) n of
                          NONE => error ("Did not find definition: " ^ n)
                        | SOME binding => Global_Theory.get_thm thy (Binding.name_of binding)
                  in
                    resolve_tac ctxt [def_thm] 1 THEN rest (tl skel) memo
                  end
              | Axiom n =>
                  let
                    val ax_thm =
                      case AList.lookup (op =) (#axs pannot) n of
                          NONE => error ("Did not find axiom: " ^ n)
                        | SOME binding => Global_Theory.get_thm thy (Binding.name_of binding)
                  in
                    resolve_tac ctxt [ax_thm] 1 THEN rest (tl skel) memo
                  end
              | _ => raise SKELETON
      in tactic st end
(*FIXME fuse these*)
    (*As above, but creates debug-friendly tactic.
      This is also used for "partial proof reconstruction"*)
    fun skel_to_naive_tactic_dbg prover_tac ctxt prob_name skel (memo : (string * (thm * tactic) option) list) =
      let
        val thy = Proof_Context.theory_of ctxt
        val pannot = get_pannot_of_prob thy prob_name

(* FIXME !???!
        fun rtac_wrap thm_f i = fn st =>
          let
            val thy = Thm.theory_of_thm st
          in
            rtac (thm_f thy) i st
          end
*)

        (*Some nodes don't have an inference name, such as the conjecture,
          definitions and axioms. Such nodes shouldn't appear in the
          skeleton.*)
        fun inference_name_of_node node =
           case AList.lookup (op =) (#meta pannot) node of
               NONE => (warning "Inference step lacks an inference name"; "(Shouldn't be here)")
             | SOME info =>
                 case #source_inf_opt info of
                     SOME (TPTP_Proof.Inference (infname, _, _)) =>
                       infname
                   | _ => (warning "Inference step lacks an inference name"; "(Shouldn't be here)")

        fun inference_fmla node =
          case inference_at_node thy prob_name (#meta pannot) node of
              NONE => NONE
            | SOME {inference_fmla, ...} => SOME inference_fmla

        fun rest memo' ctxt' = skel_to_naive_tactic_dbg prover_tac ctxt' prob_name (tl skel) memo'
        (*reconstruct the inference. also set timeout in case
          tactic takes too long*)
        val try_make_step =
          (*FIXME const timeout*)
          (* Timeout.apply (Time.fromSeconds 5) *)
          (fn ctxt' =>
             let
               fun thm ctxt'' = prover_tac ctxt'' prob_name (hd skel |> stock_to_string)
               val reconstructed_inference = thm ctxt'
               fun rec_inf_tac st = HEADGOAL (resolve_tac ctxt' [thm ctxt']) st
             in (reconstructed_inference,
                 rec_inf_tac)
             end)
        fun ignore_interpretation_exn f x = SOME (f x)
          handle INTERPRET_INFERENCE => NONE
      in
        if List.null skel then
          raise SKELETON
        (*FIXME or classify it as follows:
          [(Caboose,
            Thm.prop_of @{thm asm_rl}
            |> SOME,
            SOME (@{thm asm_rl}, TRY (HEADGOAL atac)))]
         *)
        else
          case hd skel of
              Assumed =>
                (hd skel,
                 Thm.prop_of @{thm asm_rl}
                 |> SOME,
                 SOME (@{thm asm_rl}, TRY (HEADGOAL (assume_tac ctxt)))) :: rest memo ctxt
            | Caboose =>
                [(Caboose,
                  Thm.prop_of @{thm asm_rl}
                  |> SOME,
                  SOME (@{thm asm_rl}, TRY (HEADGOAL (assume_tac ctxt))))]
            | Unconjoin =>
                (hd skel,
                 Thm.prop_of @{thm conjI}
                 |> SOME,
                 SOME (@{thm conjI}, resolve_tac ctxt @{thms conjI} 1)) :: rest memo ctxt
            | Split (split_node, solved_node, antes) =>
                let
                  val split_fmla = node_info (#meta pannot) #fmla split_node
                  val conclusion =
                        (inference_at_node thy prob_name (#meta pannot) solved_node
                         |> the
                         |> #inference_fmla)
                        |> Logic.dest_implies (*FIXME there might be !!-variables?*)
                        |> #1
                  val minor_prems_assumps =
                      map (fn ante => find_ancestor_using_rule pannot "split_conjecture" [ante]) antes
                      |> map (node_info (#meta pannot) #fmla)
                  val split_thm =
                      simulate_split ctxt split_fmla minor_prems_assumps conclusion
                in
                  (hd skel,
                   Thm.prop_of split_thm
                   |> SOME,
                   SOME (split_thm, resolve_tac ctxt [split_thm] 1)) :: rest memo ctxt
                end
            | Step node =>
                let
                  val inference_name = inference_name_of_node node
                  val inference_fmla = inference_fmla node

                  (*FIXME debugging code
                  val _ =
                    if Config.get ctxt tptp_trace_reconstruction then
                       (tracing ("handling node " ^ node);
                        tracing ("inference " ^ inference_name);
                        if is_some inference_fmla then
                          tracing ("formula size " ^ Int.toString (Term.size_of_term (the inference_fmla)))
                        else ()(*;
                        tracing ("formula " ^ @{make_string inference_fmla}) *))
                    else ()*)

                  val (inference_instance_thm, memo', ctxt') =
                    case AList.lookup (op =) memo node of
                        NONE =>
                          let
                            val (thm, ctxt') =
                              (*Instead of NONE could have another value indicating that the formula was too big*)
                                if is_some inference_fmla andalso
                                   (*FIXME could have different inference rules have different sizelimits*)
                                   exceeds_tptp_max_term_size ctxt (Term.size_of_term (the inference_fmla)) then
                                    (
                                     warning ("Gave up on node " ^ node ^ " because of fmla size " ^
                                              Int.toString (Term.size_of_term (the inference_fmla)));
                                     (NONE, ctxt)
                                    )
                                else
                                  let
                                    val maybe_thm = ignore_interpretation_exn try_make_step ctxt
(* FIXME !???!
                                    val ctxt' =
                                      if is_some maybe_thm then
                                        the maybe_thm
                                        |> #1
                                        |> Thm.theory_of_thm |> Proof_Context.init_global
                                      else ctxt
*)
                                  in
                                    (maybe_thm, ctxt)
                                  end
                          in (thm, (node, thm) :: memo, ctxt') end
                      | SOME maybe_thm => (maybe_thm, memo, ctxt)
                in
                  (Annotated_step (node, inference_name),
                   inference_fmla,
                   inference_instance_thm) :: rest memo' ctxt'
                end
            | Definition n =>
                let
                  fun def_thm thy =
                    case AList.lookup (op =) (#defs pannot) n of
                        NONE => error ("Did not find definition: " ^ n)
                      | SOME binding => Global_Theory.get_thm thy (Binding.name_of binding)
                in
                  (hd skel,
                   Thm.prop_of (def_thm thy)
                   |> SOME,
                   SOME (def_thm thy, HEADGOAL (resolve_tac ctxt [def_thm thy]))) :: rest memo ctxt
                end
            | Axiom n =>
                let
                  val ax_thm =
                    case AList.lookup (op =) (#axs pannot) n of
                        NONE => error ("Did not find axiom: " ^ n)
                      | SOME binding => Global_Theory.get_thm thy (Binding.name_of binding)
                in
                  (hd skel,
                   Thm.prop_of ax_thm
                   |> SOME,
                   SOME (ax_thm, resolve_tac ctxt [ax_thm] 1)) :: rest memo ctxt
                end
      end

    (*The next function handles cases where Leo2 doesn't include the solved_all_splits
      step at the end (e.g. because there wouldn't be a split -- the proof
      would be linear*)
    fun sas_if_needed_tac ctxt prob_name =
      let
        val thy = Proof_Context.theory_of ctxt
        val pannot = get_pannot_of_prob thy prob_name
        val last_inference_info_opt =
          find_first
           (fn (_, info) => #role info = TPTP_Syntax.Role_Plain)
           (#meta pannot)
        val last_inference_info =
          case last_inference_info_opt of
              NONE => NONE
            | SOME (_, info) => #source_inf_opt info
      in
        if is_some last_inference_info andalso
         TPTP_Proof.is_inference_called "solved_all_splits"
          (the last_inference_info)
        then (@{thm asm_rl}, all_tac)
        else (solved_all_splits, TRY (resolve_tac ctxt [solved_all_splits] 1))
      end
in
  (*Build a tactic from a skeleton. This is naive because it uses the naive skeleton.
    The inference interpretation ("prover_tac") is a parameter -- it would usually be
    different for different provers.*)
  fun naive_reconstruct_tac ctxt prover_tac prob_name =
    let
      val thy = Proof_Context.theory_of ctxt
    in
      resolve_tac ctxt @{thms ccontr} 1
      THEN dresolve_tac ctxt [neg_eq_false] 1
      THEN (sas_if_needed_tac ctxt prob_name |> #2)
      THEN skel_to_naive_tactic ctxt prover_tac prob_name
       (make_skeleton ctxt
        (get_pannot_of_prob thy prob_name)) []
    end

  (*As above, but generates a list of tactics. This is useful for debugging, to apply
    the tactics one by one manually.*)
  fun naive_reconstruct_tacs prover_tac prob_name ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
    in
      (Synth_step "ccontr", Thm.prop_of @{thm ccontr} |> SOME,
       SOME (@{thm ccontr}, resolve_tac ctxt @{thms ccontr} 1)) ::
      (Synth_step "neg_eq_false", Thm.prop_of neg_eq_false |> SOME,
       SOME (neg_eq_false, dresolve_tac ctxt [neg_eq_false] 1)) ::
      (Synth_step "sas_if_needed_tac", Thm.prop_of @{thm asm_rl} (*FIXME *) |> SOME,
       SOME (sas_if_needed_tac ctxt prob_name)) ::
      skel_to_naive_tactic_dbg prover_tac ctxt prob_name
       (make_skeleton ctxt
        (get_pannot_of_prob thy prob_name)) []
    end
end

(*Produces a theorem given a tactic and a parsed proof. This function is handy
to test reconstruction, since it automates the interpretation and proving of the
parsed proof's goal.*)
fun reconstruct ctxt tactic prob_name =
  let
    val thy = Proof_Context.theory_of ctxt
    val pannot = get_pannot_of_prob thy prob_name
    val goal =
      #meta pannot
      |> filter (fn (_, info) =>
          #role info = TPTP_Syntax.Role_Conjecture)
  in
    if null (#meta pannot) then
      (*since the proof is empty, return a trivial result.*)
      @{thm TrueI}
    else if null goal then
      raise (RECONSTRUCT "Proof lacks conjecture")
    else
      the_single goal
      |> snd |> #fmla
      |> (fn fmla => Goal.prove ctxt [] [] fmla (fn _ => tactic prob_name))
  end


(** Skolemisation setup **)

(*Ignore these constants if they appear in the conclusion but not the hypothesis*)
(*FIXME possibly incomplete*)
val ignore_consts =
  [HOLogic.conj, HOLogic.disj, HOLogic.imp, HOLogic.Not]

(*Difference between the constants appearing between two terms, minus "ignore_consts"*)
fun new_consts_between t1 t2 =
  filter
   (fn n => not (exists (fn n' => n' = n) ignore_consts))
   (list_diff (consts_in t2) (consts_in t1))

(*Generate definition binding for an equation*)
fun mk_bind_eq prob_name params ((n, ty), t) =
  let
    val bnd =
      Binding.name (Long_Name.base_name n ^ "_def")
      |> Binding.qualify false (TPTP_Problem_Name.mangle_problem_name prob_name)
    val t' =
      Term.list_comb (Const (n, ty), params)
      |> rpair t
      |> HOLogic.mk_eq
      |> HOLogic.mk_Trueprop
      |> fold Logic.all params
  in
    (bnd, t')
  end

(*Generate binding for an axiom. Similar to "mk_bind_eq"*)
fun mk_bind_ax prob_name node t =
  let
    val bnd =
      Binding.name node
      (*FIXME add suffix? e.g. ^ "_ax"*)
      |> Binding.qualify false (TPTP_Problem_Name.mangle_problem_name prob_name)
  in
    (bnd, t)
  end

(*Extract the constant name, type, and its definition*)
fun get_defn_components
  (Const (\<^const_name>\<open>HOL.Trueprop\<close>, _) $
    (Const (\<^const_name>\<open>HOL.eq\<close>, _) $
      Const (name, ty) $ t)) = ((name, ty), t)


(*** Proof transformations ***)

(*Transforms a proof_annotation value.
  Argument "f" is the proof transformer*)
fun transf_pannot f (pannot : proof_annotation) : (theory * proof_annotation) =
  let
    val (thy', fms') = f (#meta pannot)
  in
    (thy',
     {problem_name = #problem_name pannot,
      skolem_defs = #skolem_defs pannot,
      defs = #defs pannot,
      axs = #axs pannot,
      meta = fms'})
  end


(** Proof transformer to add virtual inference steps
    encoding "bind" annotations in Leo-II proofs **)

(*
Involves finding an inference of this form:

       (!x1 ... xn. F)   ...   Cn
  ------------------------------------ (Rule name)
          G[t1/x1, ..., tn/xn]

and turn it into this:


     (!x1 ... xn. F)
  ---------------------- bind
   F[t1/x1, ..., tn/xn]           ...   Cn
  -------------------------------------------- (Rule name)
                    G

where "bind" is an inference rule (distinct from any rule name used
by Leo2) to indicate such inferences.  This transformation is used
to factor out instantiations, thus allowing the reconstruction to
focus on (Rule name) rather than "(Rule name) + instantiations".
*)
fun interpolate_binds prob_name thy fms : theory * formula_meaning list =
  let
    fun factor_out_bind target_node pinfo intermediate_thy =
      case pinfo of
         TPTP_Proof.ParentWithDetails (n, pdetails) =>
           (*create new node which contains the "bind" inference,
             to be added to graph*)
           let
             val (new_node_name, thy') = get_next_name intermediate_thy
             val orig_fmla = node_info fms #fmla n
             val target_fmla = node_info fms #fmla target_node
             val new_node =
              (new_node_name,
               {role = TPTP_Syntax.Role_Plain,
                fmla = apply_binding thy' prob_name orig_fmla target_fmla pdetails |> fst,
                source_inf_opt =
                  SOME (TPTP_Proof.Inference (bindK, [], [pinfo]))})
           in
             ((TPTP_Proof.Parent new_node_name, SOME new_node), thy')
           end
       | _ => ((pinfo, NONE), intermediate_thy)
    fun process_nodes (step as (n, data)) (intermediate_thy, rest) =
      case #source_inf_opt data of
          SOME (TPTP_Proof.Inference (inf_name, sinfos, pinfos)) =>
            let
              val ((pinfos', parent_nodes), thy') =
                fold_map (factor_out_bind n) pinfos intermediate_thy
                |> apfst ListPair.unzip
              val step' =
                (n, {role = #role data, fmla = #fmla data,
                 source_inf_opt = SOME (TPTP_Proof.Inference (inf_name, sinfos, pinfos'))})
            in (thy', fold_options parent_nodes @ step' :: rest) end
        | _ => (intermediate_thy, step :: rest)
  in
    fold process_nodes fms (thy, [])
    (*new_nodes must come at the beginning, since we assume that the last line in a proof is the closing line*)
    |> apsnd rev
  end


(** Proof transformer to add virtual inference steps
    encoding any transformation done immediately prior
    to a splitting step **)

(*
Involves finding an inference of this form:

                   F = $false
  ----------------------------------- split_conjecture
    (F1 = $false) ... (Fn = $false)

where F doesn't have an "and" or "iff" at the top level,
and turn it into this:

                   F = $false
  ----------------------------------- split_preprocessing
            (F1 % ... % Fn) = $false
  ----------------------------------- split_conjecture
    (F1 = $false) ... (Fn = $false)

where "%" is either an "and" or an "iff" connective.
This transformation is used to clarify the clause structure, to
make it immediately "obvious" how splitting is taking place
(by factoring out the other syntactic transformations -- e.g.
related to quantifiers -- performed by Leo2). Having the clause
in this "clearer" form makes the inference amenable to handling
using the "abstraction" technique, which allows us to validate
large inferences.
*)
exception PREPROCESS_SPLITS
fun preprocess_splits prob_name thy fms : theory * formula_meaning list =
  let
    (*Simulate the transformation done by Leo2's preprocessing
      step during splitting.
      NOTE: we assume that the clause is a singleton

      This transformation does the following:
       - miniscopes !-quantifiers (and recurs)
       - removes redundant ?-quantifiers (and recurs)
       - eliminates double negation (and recurs)
       - breaks up conjunction (and recurs)
       - expands iff (and doesn't recur)*)
    fun transform_fmla i fmla_t =
      case fmla_t of
          Const (\<^const_name>\<open>HOL.All\<close>, ty) $ Abs (s, ty', t') =>
            let
              val (i', fmla_ts) = transform_fmla i t'
            in
              if i' > i then
                (i' + 1,
                 map (fn t =>
                  Const (\<^const_name>\<open>HOL.All\<close>, ty) $ Abs (s, ty', t))
                fmla_ts)
              else (i, [fmla_t])
            end
        | Const (\<^const_name>\<open>HOL.Ex\<close>, ty) $ Abs (s, ty', t') =>
            if loose_bvar (t', 0) then
              (i, [fmla_t])
            else transform_fmla (i + 1) t'
        | \<^term>\<open>HOL.Not\<close> $ (\<^term>\<open>HOL.Not\<close> $ t') =>
            transform_fmla (i + 1) t'
        | \<^term>\<open>HOL.conj\<close> $ t1 $ t2 =>
            let
              val (i1, fmla_t1s) = transform_fmla (i + 1) t1
              val (i2, fmla_t2s) = transform_fmla (i + 1) t2
            in
              (i1 + i2 - i, fmla_t1s @ fmla_t2s)
            end
        | Const (\<^const_name>\<open>HOL.eq\<close>, ty) $ t1 $ t2 =>
            let
              val (T1, (T2, res)) =
                dest_funT ty
                |> apsnd dest_funT
            in
              if T1 = HOLogic.boolT andalso T2 = HOLogic.boolT andalso
                 res = HOLogic.boolT then
                (i + 1,
                  [HOLogic.mk_imp (t1, t2),
                   HOLogic.mk_imp (t2, t1)])
              else (i, [fmla_t])
            end
        | _ => (i, [fmla_t])

    fun preprocess_split thy split_node_name fmla_t =
      (*create new node which contains the new inference,
        to be added to graph*)
      let
        val (node_name, thy') = get_next_name thy
        val (changes, fmla_conjs) =
          transform_fmla 0 fmla_t
          |> apsnd rev (*otherwise we run into problems because
                         of commutativity of conjunction*)
        val target_fmla =
          fold (curry HOLogic.mk_conj) (tl fmla_conjs) (hd fmla_conjs)
        val new_node =
         (node_name,
          {role = TPTP_Syntax.Role_Plain,
           fmla =
             HOLogic.mk_eq (target_fmla, \<^term>\<open>False\<close>) (*polarise*)
             |> HOLogic.mk_Trueprop,
           source_inf_opt =
             SOME (TPTP_Proof.Inference (split_preprocessingK, [], [TPTP_Proof.Parent split_node_name]))})
      in
        if changes = 0 then NONE
        else SOME (TPTP_Proof.Parent node_name, new_node, thy')
      end
  in
    fold
     (fn step as (n, data) => fn (intermediate_thy, redirections, rest) =>
       case #source_inf_opt data of
            SOME (TPTP_Proof.Inference
                   (inf_name, sinfos, pinfos)) =>
              if inf_name <> "split_conjecture" then
                (intermediate_thy, redirections, step :: rest)
              else
                let
                  (*
                   NOTE: here we assume that the node only has one
                         parent, and that there is no additional
                         parent info.
                   *)
                  val split_node_name =
                    case pinfos of
                        [TPTP_Proof.Parent n] => n
                      | _ => raise PREPROCESS_SPLITS
                (*check if we've already handled that already node*)
                in
                  case AList.lookup (op =) redirections split_node_name of
                      SOME preprocessed_split_node_name =>
                        let
                          val step' =
                            apply_to_parent_info (fn _ => [TPTP_Proof.Parent preprocessed_split_node_name]) step
                        in (intermediate_thy, redirections, step' :: rest) end
                    | NONE =>
                        let
                          (*we know the polarity to be $false, from knowing Leo2*)
                          val split_fmla =
                            try_dest_Trueprop (node_info fms #fmla split_node_name)
                            |> remove_polarity true
                            |> fst

                          val preprocess_result =
                            preprocess_split intermediate_thy
                              split_node_name
                              split_fmla
                        in
                          if is_none preprocess_result then
                            (*no preprocessing done by Leo2, so no need to introduce
                              a virtual inference. cache this result by
                              redirecting the split_node to itself*)
                            (intermediate_thy,
                             (split_node_name, split_node_name) :: redirections,
                             step :: rest)
                          else
                            let
                              val (new_parent_info, new_parent_node, thy') = the preprocess_result
                              val step' =
                                (n, {role = #role data, fmla = #fmla data,
                                 source_inf_opt = SOME (TPTP_Proof.Inference (inf_name, sinfos, [new_parent_info]))})
                            in
                              (thy',
                               (split_node_name, fst new_parent_node) :: redirections,
                               step' :: new_parent_node :: rest)
                            end
                        end
                end
          | _ => (intermediate_thy, redirections, step :: rest))
     (rev fms) (*this allows us to put new inferences before other inferences which use them*)
     (thy, [], [])
    |> (fn (x, _, z) => (x, z)) (*discard redirection info*)
  end


(** Proof transformer to remove repeated quantification **)

exception DROP_REPEATED_QUANTIFICATION
fun drop_repeated_quantification thy (fms : formula_meaning list) : theory * formula_meaning list =
  let
    (*In case of repeated quantification, removes outer quantification.
      Only need to look at top-level, since the repeated quantification
      generally occurs at clause level*)
    fun remove_repeated_quantification seen t =
      case t of
          (*NOTE we're assuming that variables having the same name, have the same type throughout*)
          Const (\<^const_name>\<open>HOL.All\<close>, ty) $ Abs (s, ty', t') =>
            let
              val (seen_so_far, seen') =
                case AList.lookup (op =) seen s of
                    NONE => (0, (s, 0) :: seen)
                  | SOME n => (n + 1, AList.update (op =) (s, n + 1) seen)
              val (pre_final_t, final_seen) = remove_repeated_quantification seen' t'
              val final_t =
                case AList.lookup (op =) final_seen s of
                    NONE => raise DROP_REPEATED_QUANTIFICATION
                  | SOME n =>
                      if n > seen_so_far then pre_final_t
                      else Const (\<^const_name>\<open>HOL.All\<close>, ty) $ Abs (s, ty', pre_final_t)
            in (final_t, final_seen) end
        | _ => (t, seen)

    fun remove_repeated_quantification' (n, {role, fmla, source_inf_opt}) =
      (n,
       {role = role,
        fmla =
          try_dest_Trueprop fmla
          |> remove_repeated_quantification []
          |> fst
          |> HOLogic.mk_Trueprop,
        source_inf_opt = source_inf_opt})
  in
    (thy, map remove_repeated_quantification' fms)
  end


(** Proof transformer to detect a redundant splitting and remove
    the redundant branch. **)

fun node_is_inference fms rule_name node_name =
  case node_info fms #source_inf_opt node_name of
      NONE => false
    | SOME (TPTP_Proof.File _) => false
    | SOME (TPTP_Proof.Inference (rule_name', _, _)) => rule_name' = rule_name

(*In this analysis we're interested if there exists a split-free
  path between the end of the proof and the negated conjecture.
  If so, then this path (or the shortest such path) could be
  retained, and the rest of the proof erased.*)
datatype branch_info =
    Split_free (*Path is not part of a split. This is only used when path reaches the negated conjecture.*)
  | Split_present (*Path is one of a number of splits. Such paths are excluded.*)
  | Coinconsistent of int (*Path leads to a clause which is inconsistent with nodes concluded by other paths.
                            Therefore this path should be kept if the others are kept
                            (i.e., unless one of them results from a split)*)
  | No_info (*Analysis hasn't come across anything definite yet, though it still hasn't completed.*)
(*A "paths" value consist of every way of reaching the destination,
  including information come across it so far. Taking the head of
  each way gives the fringe. All paths should share the same source
  and sink.*)
type path = (branch_info * string list)
exception PRUNE_REDUNDANT_SPLITS
fun prune_redundant_splits prob_name thy fms : theory * formula_meaning list =
  let
    (*All paths start at the contradiction*)
    val initial_path = (No_info, [proof_end_node fms])
    (*All paths should end at the proof's beginning*)
    val end_node = proof_beginning_node fms

    fun compute_path (path as ((info,
                       (n :: ns)) : path))(*i.e. node list can't be empty*)
        intermediate_thy =
      case info of
          Split_free => (([path], []), intermediate_thy)
        | Coinconsistent branch_id =>
            (*If this branch has a split_conjecture parent then all "sibling" branches get erased.*)
            (*This branch can't lead to yet another coinconsistent branch (in the case of Leo2).*)
            let
              val parent_nodes = parents_of_node fms n
            in
              if exists (node_is_inference fms "split_conjecture") parent_nodes then
                (([], [branch_id]), intermediate_thy) (*all related branches are to be deleted*)
              else
                list_prod [] parent_nodes (n :: ns)
                |> map (fn ns' => (Coinconsistent branch_id, ns'))
                |> (fn x => ((x, []), intermediate_thy))
            end

        | No_info =>
            let
              val parent_nodes = parents_of_node fms n

              (*if this node is a consistency checking node then parent nodes will be marked as coinconsistent*)
              val (thy', new_branch_info) =
                if node_is_inference fms "fo_atp_e" n orelse
                   node_is_inference fms "res" n then
                  let
                    val (i', intermediate_thy') = get_next_int intermediate_thy
                  in
                    (intermediate_thy', SOME (Coinconsistent i'))
                  end
                else (intermediate_thy, NONE)
            in
              if exists (node_is_inference fms "split_conjecture") parent_nodes then
                (([], []), thy')
              else
                list_prod [] parent_nodes (n :: ns)
                |> map (fn ns' =>
                          let
                            val info =
                              if is_some new_branch_info then the new_branch_info
                              else
                                if hd ns' = end_node then Split_free else No_info
                          in (info, ns') end)
                |> (fn x => ((x, []), thy'))
            end
        | _ => raise PRUNE_REDUNDANT_SPLITS

    fun compute_paths intermediate_thy (paths : path list) =
      if filter (fn (_, ns) => ns <> [] andalso hd ns = end_node) paths = paths then
        (*fixpoint reached when all paths are at the head position*)
        (intermediate_thy, paths)
      else
        let
          val filtered_paths = filter (fn (info, _) : path => info <> Split_present) paths (*not interested in paths containing a split*)
          val (paths', thy') =
            fold_map compute_path filtered_paths intermediate_thy
        in
          paths'
          |> ListPair.unzip (*we get a list of pairs of lists. we want a pair of lists*)
          |> (fn (paths, branch_ids) =>
               (flat paths,
                (*remove duplicate branch_ids*)
                fold (Library.insert (op =)) (flat branch_ids) []))
          (*filter paths having branch_ids appearing in the second list*)
          |> (fn (paths, branch_ids) =>
              filter (fn (info, _) =>
                        case info of
                            Coinconsistent branch_id => exists (fn x => x = branch_id) branch_ids
                          | _ => true) paths)
          |> compute_paths thy'
        end

    val (thy', paths) =
      compute_paths thy [initial_path]
      |> apsnd
          (filter (fn (branch_info, _) =>
                  case branch_info of
                      Split_free => true
                    | Coinconsistent _ => true
                    | _ => false))
    (*Extract subset of fms which is used in a path.
      Also, remove references (in parent info annotations) to erased nodes.*)
    fun path_to_fms ((_, nodes) : path) =
      fold
       (fn n => fn fms' =>
          case AList.lookup (op =) fms' n of
              SOME _ => fms'
            | NONE =>
               let
                 val node_info = the (AList.lookup (op =) fms n)

                 val source_info' =
                   case #source_inf_opt node_info of
                       NONE => error "Only the conjecture is an orphan"
                     | SOME (source_info as TPTP_Proof.File _) => source_info
                     | SOME (source_info as
                             TPTP_Proof.Inference (inference_name,
                                                   useful_infos : TPTP_Proof.useful_info_as list,
                                                   parent_infos)) =>
                         let
                           fun is_node_in_fms' parent_info =
                             let
                               val parent_nodename =
                                 case parent_info of
                                     TPTP_Proof.Parent n => n
                                   | TPTP_Proof.ParentWithDetails (n, _) => n
                             in
                               case AList.lookup (op =) fms' parent_nodename of
                                   NONE => false
                                 | SOME _ => true
                             end
                         in
                           TPTP_Proof.Inference (inference_name,
                                                 useful_infos,
                                                 filter is_node_in_fms' parent_infos)
                         end
               in
                   (n,
                    {role = #role node_info,
                     fmla = #fmla node_info,
                     source_inf_opt = SOME source_info'}) :: fms'
               end)
       nodes
       []
  in
    if null paths then (thy', fms) else
      (thy',
       hd(*FIXME could pick path based on length, or some notion of "difficulty"*) paths
       |> path_to_fms)
  end


(*** Main functions ***)

(*interpret proof*)
fun import_thm cautious path_prefixes file_name
 (on_load : proof_annotation -> theory -> (proof_annotation * theory)) thy =
  let
    val prob_name =
      Path.file_name file_name
      |> TPTP_Problem_Name.parse_problem_name
    val thy1 = TPTP_Interpret.import_file cautious path_prefixes file_name [] [] thy
    val fms = get_fmlas_of_prob thy1 prob_name
  in
    if List.null fms then
      (warning ("File " ^ Path.print file_name ^ " appears empty!");
       TPTP_Reconstruction_Data.map (cons ((prob_name, empty_pannot prob_name))) thy1)
    else
      let
        val defn_equations =
          filter (fn (_, role, _, _) => role = TPTP_Syntax.Role_Definition) fms
          |> map (fn (node, _, t, _) =>
               (node,
                get_defn_components t
                |> mk_bind_eq prob_name []))
        val axioms =
          filter (fn (_, role, _, _) => role = TPTP_Syntax.Role_Axiom) fms
          |> map (fn (node, _, t, _) =>
               (node,
                mk_bind_ax prob_name node t))

        (*add definitions and axioms to the theory*)
        val thy2 =
          fold
           (fn bnd => fn thy =>
              let
                val ((name, thm), thy') = Thm.add_axiom_global bnd thy
              in Global_Theory.add_thm ((#1 bnd, thm), []) thy' |> #2 end)
           (map snd defn_equations @ map snd axioms)
          thy1

        (*apply global proof transformations*)
        val (thy3, pre_pannot) : theory * proof_annotation =
          transf_pannot
           (prune_redundant_splits prob_name thy2
            #-> interpolate_binds prob_name
            #-> preprocess_splits prob_name
            #-> drop_repeated_quantification)
           {problem_name = prob_name,
            skolem_defs = [],
            defs = map (apsnd fst) defn_equations,
            axs = map (apsnd fst) axioms,
            meta = map (fn (n, r, t, info) => (n, {role=r, fmla=t, source_inf_opt=info})) fms}

        (*store pannot*)
        val thy4 = TPTP_Reconstruction_Data.map (cons ((prob_name, pre_pannot))) thy3

        (*run hook, which might result in changed pannot and theory*)
        val (pannot, thy5) = on_load pre_pannot thy4

      (*store the most recent pannot*)
      in TPTP_Reconstruction_Data.map (cons ((prob_name, pannot))) thy5 end
  end

(*This has been disabled since it requires a hook to be specified to use "import_thm"
val _ =
  Outer_Syntax.command @{command_keyword import_leo2_proof} "import TPTP proof"
    (Parse.path >> (fn name =>
      Toplevel.theory (fn thy =>
       let val path = Path.explode name
       in import_thm true [Path.dir path, Path.explode "$TPTP"] path (*FIXME hook needs to be given here*)
thy end)))
*)


(** Archive **)
(*FIXME move elsewhere*)
(*This contains currently unused, but possibly useful, functions written
  during experimentation, in case they are useful later on*)

(*given a list of rules and a node, return
  SOME (rule name) if that node's rule name
  belongs to the list of rules*)
fun match_rules_of_current (pannot : proof_annotation) rules n =
  case node_info (#meta pannot) #source_inf_opt n of
      NONE => NONE
    | SOME (TPTP_Proof.File _) => NONE
    | SOME (TPTP_Proof.Inference (rule_name, _ : TPTP_Proof.useful_info_as list, _)) =>
        if member (op =) rules rule_name then SOME rule_name else NONE

(*given a node and a list of rules, determine
  whether all the rules can be matched to
  parent nodes. If nonstrict then there may be
  more parents than given rules.*)
fun match_rules_of_immediate_previous (pannot : proof_annotation) strict rules n =
  case node_info (#meta pannot) #source_inf_opt n of
      NONE => null rules
    | SOME (TPTP_Proof.File _) => null rules
    | SOME (TPTP_Proof.Inference (rule_name, _ : TPTP_Proof.useful_info_as list, parent_infos)) =>
        let
          val matched_rules : string option list =
            map (match_rules_of_current pannot rules)
                (dest_parent_infos true (#meta pannot) parent_infos |> map #name)
        in
          if strict andalso member (op =) matched_rules NONE then false
          else
            (*check that all the rules were matched*)
            fold
              (fn (rule : string) => fn (st, matches : string option list) =>
                 if not st then (st, matches)
                 else
                   let
                     val idx = find_index (fn match => SOME rule = match) matches
                   in
                     if idx < 0 then (false, matches)
                     else
                       (st, nth_drop idx matches)
                   end)
             rules
             (true, matched_rules)
            |> #1 (*discard the other info*)
        end
end
