(*  Title:      HOL/Tools/Function/fun.ML
    Author:     Alexander Krauss, TU Muenchen

Sequential mode for function definitions
Command "fun" for fully automated function definitions
*)

signature FUNCTION_FUN =
sig
  val add_fun : Function_Common.function_config ->
    (binding * typ option * mixfix) list -> (Attrib.binding * term) list ->
    bool -> local_theory -> Proof.context
  val add_fun_cmd : Function_Common.function_config ->
    (binding * string option * mixfix) list -> (Attrib.binding * string) list ->
    bool -> local_theory -> Proof.context

  val setup : theory -> theory
end

structure Function_Fun : FUNCTION_FUN =
struct

open Function_Lib
open Function_Common


fun check_pats ctxt geq =
  let
    fun err str = error (cat_lines ["Malformed definition:",
      str ^ " not allowed in sequential mode.",
      Syntax.string_of_term ctxt geq])
    val thy = ProofContext.theory_of ctxt

    fun check_constr_pattern (Bound _) = ()
      | check_constr_pattern t =
      let
        val (hd, args) = strip_comb t
      in
        (((case Datatype.info_of_constr thy (dest_Const hd) of
             SOME _ => ()
           | NONE => err "Non-constructor pattern")
          handle TERM ("dest_Const", _) => err "Non-constructor patterns");
         map check_constr_pattern args;
         ())
      end

    val (_, qs, gs, args, _) = split_def ctxt geq

    val _ = if not (null gs) then err "Conditional equations" else ()
    val _ = map check_constr_pattern args

    (* just count occurrences to check linearity *)
    val _ = if fold (fold_aterms (fn Bound _ => Integer.add 1 | _ => I)) args 0 > length qs
      then err "Nonlinear patterns" else ()
  in
    ()
  end

val by_pat_completeness_auto =
  Proof.global_future_terminal_proof
    (Method.Basic Pat_Completeness.pat_completeness,
     SOME (Method.Source_i (Args.src (("HOL.auto", []), Position.none))))

fun termination_by method int =
  Function.termination_proof NONE
  #> Proof.global_future_terminal_proof (Method.Basic method, NONE) int

fun mk_catchall fixes arity_of =
  let
    fun mk_eqn ((fname, fT), _) =
      let
        val n = arity_of fname
        val (argTs, rT) = chop n (binder_types fT)
          |> apsnd (fn Ts => Ts ---> body_type fT)

        val qs = map Free (Name.invent_list [] "a" n ~~ argTs)
      in
        HOLogic.mk_eq(list_comb (Free (fname, fT), qs),
          Const ("HOL.undefined", rT))
        |> HOLogic.mk_Trueprop
        |> fold_rev Logic.all qs
      end
  in
    map mk_eqn fixes
  end

fun add_catchall ctxt fixes spec =
  let val fqgars = map (split_def ctxt) spec
      val arity_of = map (fn (fname,_,_,args,_) => (fname, length args)) fqgars
                     |> AList.lookup (op =) #> the
  in
    spec @ mk_catchall fixes arity_of
  end

fun warn_if_redundant ctxt origs tss =
  let
    fun msg t = "Ignoring redundant equation: " ^ quote (Syntax.string_of_term ctxt t)

    val (tss', _) = chop (length origs) tss
    fun check (t, []) = (warning (msg t); [])
      | check (t, s) = s
  in
    (map check (origs ~~ tss'); tss)
  end

fun sequential_preproc (config as FunctionConfig {sequential, ...}) ctxt fixes spec =
  if sequential then
    let
      val (bnds, eqss) = split_list spec

      val eqs = map the_single eqss

      val feqs = eqs
        |> tap (check_defs ctxt fixes) (* Standard checks *)
        |> tap (map (check_pats ctxt)) (* More checks for sequential mode *)

      val compleqs = add_catchall ctxt fixes feqs (* Completion *)

      val spliteqs = warn_if_redundant ctxt feqs
        (Function_Split.split_all_equations ctxt compleqs)

      fun restore_spec thms =
        bnds ~~ take (length bnds) (unflat spliteqs thms)

      val spliteqs' = flat (take (length bnds) spliteqs)
      val fnames = map (fst o fst) fixes
      val indices = map (fn eq => find_index (curry op = (fname_of eq)) fnames) spliteqs'

      fun sort xs = partition_list (fn i => fn (j,_) => i = j) 0 (length fnames - 1) (indices ~~ xs)
        |> map (map snd)


      val bnds' = bnds @ replicate (length spliteqs - length bnds) Attrib.empty_binding

      (* using theorem names for case name currently disabled *)
      val case_names = map_index (fn (i, (_, es)) => mk_case_names i "" (length es)) 
        (bnds' ~~ spliteqs) |> flat
    in
      (flat spliteqs, restore_spec, sort, case_names)
    end
  else
    Function_Common.empty_preproc check_defs config ctxt fixes spec

val setup =
  Context.theory_map (Function_Common.set_preproc sequential_preproc)


val fun_config = FunctionConfig { sequential=true, default="%x. undefined" (*FIXME dynamic scoping*), 
  domintros=false, partials=false, tailrec=false }

fun gen_fun add config fixes statements int lthy =
  lthy
  |> add fixes statements config
  |> by_pat_completeness_auto int
  |> Local_Theory.restore
  |> termination_by (Function_Common.get_termination_prover lthy) int

val add_fun = gen_fun Function.add_function
val add_fun_cmd = gen_fun Function.add_function_cmd



local structure P = OuterParse and K = OuterKeyword in

val _ =
  OuterSyntax.local_theory' "fun" "define general recursive functions (short version)" K.thy_decl
  (function_parser fun_config
     >> (fn ((config, fixes), statements) => add_fun_cmd config fixes statements));

end

end
