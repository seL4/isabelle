(*  Title:      HOL/Tools/Function/function_common.ML
    Author:     Alexander Krauss, TU Muenchen

Common definitions and other infrastructure for the function package.
*)

signature FUNCTION_COMMON =
sig
  type info =
   {is_partial : bool,
    defname : binding,
      (*contains no logical entities: invariant under morphisms:*)
    add_simps : (binding -> binding) -> string -> (binding -> binding) ->
      Token.src list -> thm list -> local_theory -> thm list * local_theory,
    fnames : binding list,
    case_names : string list,
    fs : term list,
    R : term,
    dom: term,
    psimps: thm list,
    pinducts: thm list,
    simps : thm list option,
    inducts : thm list option,
    termination : thm,
    totality : thm option,
    cases : thm list,
    pelims: thm list list,
    elims: thm list list option,
    input_eqns: term list}
  val profile : bool Unsynchronized.ref
  val PROFILE : string -> ('a -> 'b) -> 'a -> 'b
  val mk_acc : typ -> term -> term
  val split_def : Proof.context -> (string -> 'a) -> term ->
    string * (string * typ) list * term list * term list * term
  val check_defs : Proof.context -> ((string * typ) * 'a) list -> term list -> unit
  type fixes = ((string * typ) * mixfix) list
  type 'a spec = (Attrib.binding * 'a list) list
  datatype function_config = FunctionConfig of
   {sequential: bool,
    default: string option,
    domintros: bool,
    partials: bool}
  type preproc = function_config -> Proof.context -> fixes -> term spec ->
    term list * (thm list -> thm spec) * (thm list -> thm list list) * string list
  val fname_of : term -> string
  val mk_case_names : int -> string -> int -> string list
  val empty_preproc : (Proof.context -> ((string * typ) * mixfix) list -> term list -> 'c) ->
    preproc
  val termination_rule_tac : Proof.context -> int -> tactic
  val store_termination_rule : thm -> Context.generic -> Context.generic
  val retrieve_function_data : Proof.context -> term -> (term * info) list
  val add_function_data : info -> Context.generic -> Context.generic
  val termination_prover_tac : bool -> Proof.context -> tactic
  val set_termination_prover : (bool -> Proof.context -> tactic) -> Context.generic ->
    Context.generic
  val get_preproc: Proof.context -> preproc
  val set_preproc: preproc -> Context.generic -> Context.generic
  datatype function_result = FunctionResult of
   {fs: term list,
    G: term,
    R: term,
    dom: term,
    psimps : thm list,
    simple_pinducts : thm list,
    cases : thm list,
    pelims : thm list list,
    termination : thm,
    domintros : thm list option}
  val transform_function_data : morphism -> info -> info
  val import_function_data : term -> Proof.context -> info option
  val import_last_function : Proof.context -> info option
  val default_config : function_config
  val function_parser : function_config ->
    (function_config * ((binding * string option * mixfix) list * Specification.multi_specs_cmd)) parser
end

structure Function_Common : FUNCTION_COMMON =
struct

local open Function_Lib in

(* info *)

type info =
 {is_partial : bool,
  defname : binding,
    (*contains no logical entities: invariant under morphisms:*)
  add_simps : (binding -> binding) -> string -> (binding -> binding) ->
    Token.src list -> thm list -> local_theory -> thm list * local_theory,
  fnames : binding list,
  case_names : string list,
  fs : term list,
  R : term,
  dom: term,
  psimps: thm list,
  pinducts: thm list,
  simps : thm list option,
  inducts : thm list option,
  termination : thm,
  totality : thm option,
  cases : thm list,
  pelims : thm list list,
  elims : thm list list option,
  input_eqns: term list}

fun transform_function_data phi ({add_simps, case_names, fnames, fs, R, dom, psimps, pinducts,
  simps, inducts, termination, totality, defname, is_partial, cases, pelims, elims, input_eqns} : info) =
    let
      val term = Morphism.term phi
      val thm = Morphism.thm phi
      val fact = Morphism.fact phi
    in
      { add_simps = add_simps, case_names = case_names, fnames = fnames,
        fs = map term fs, R = term R, dom = term dom, psimps = fact psimps,
        pinducts = fact pinducts, simps = Option.map fact simps,
        inducts = Option.map fact inducts, termination = thm termination,
        totality = Option.map thm totality, defname = Morphism.binding phi defname,
        is_partial = is_partial, cases = fact cases,
        pelims = map fact pelims, elims = Option.map (map fact) elims,
        input_eqns = map term input_eqns }
    end


(* profiling *)

val profile = Unsynchronized.ref false

fun PROFILE msg = if !profile then timeap_msg msg else I

val acc_const_name = \<^const_name>\<open>Wellfounded.accp\<close>
fun mk_acc domT R =
  Const (acc_const_name, (domT --> domT --> HOLogic.boolT) --> domT --> HOLogic.boolT) $ R


(* analyzing function equations *)

fun split_def ctxt check_head geq =
  let
    fun input_error msg = cat_lines [msg, Syntax.string_of_term ctxt geq]
    val qs = Term.strip_qnt_vars \<^const_name>\<open>Pure.all\<close> geq
    val imp = Term.strip_qnt_body \<^const_name>\<open>Pure.all\<close> geq
    val (gs, eq) = Logic.strip_horn imp

    val (f_args, rhs) = HOLogic.dest_eq (HOLogic.dest_Trueprop eq)
      handle TERM _ => error (input_error "Not an equation")

    val (head, args) = strip_comb f_args

    val fname = fst (dest_Free head) handle TERM _ => ""
    val _ = check_head fname
  in
    (fname, qs, gs, args, rhs)
  end

(*check for various errors in the input*)
fun check_defs ctxt fixes eqs =
  let
    val fnames = map (fst o fst) fixes

    fun check geq =
      let
        fun input_error msg = error (cat_lines [msg, Syntax.string_of_term ctxt geq])

        fun check_head fname =
          member (op =) fnames fname orelse
          input_error ("Illegal equation head. Expected " ^ commas_quote fnames)

        val (fname, qs, gs, args, rhs) = split_def ctxt check_head geq

        val _ = length args > 0 orelse input_error "Function has no arguments:"

        fun add_bvs t is = add_loose_bnos (t, 0, is)
        val rvs = (subtract (op =) (fold add_bvs args []) (add_bvs rhs []))
                    |> map (fst o nth (rev qs))

        val _ = null rvs orelse input_error
          ("Variable" ^ plural " " "s " rvs ^ commas_quote rvs ^
           " occur" ^ plural "s" "" rvs ^ " on right hand side only:")

        val _ = forall (not o Term.exists_subterm
          (fn Free (n, _) => member (op =) fnames n | _ => false)) (gs @ args)
          orelse input_error "Defined function may not occur in premises or arguments"

        val freeargs = map (fn t => subst_bounds (rev (map Free qs), t)) args
        val funvars =
          filter
            (fn q => exists (exists_subterm (fn (Free q') $ _ => q = q' | _ => false)) freeargs) qs
        val _ = null funvars orelse (warning (cat_lines
          ["Bound variable" ^ plural " " "s " funvars ^
          commas_quote (map fst funvars) ^ " occur" ^ plural "s" "" funvars ^
          " in function position.", "Misspelled constructor???"]); true)
      in
        (fname, length args)
      end

    val grouped_args = AList.group (op =) (map check eqs)
    val _ = grouped_args
      |> map (fn (fname, ars) =>
        length (distinct (op =) ars) = 1 orelse
          error ("Function " ^ quote fname ^
            " has different numbers of arguments in different equations"))

    val not_defined = subtract (op =) (map fst grouped_args) fnames
    val _ = null not_defined
      orelse error ("No defining equations for function" ^
        plural " " "s " not_defined ^ commas_quote not_defined)
  in () end


(* preprocessors *)

type fixes = ((string * typ) * mixfix) list
type 'a spec = (Attrib.binding * 'a list) list

datatype function_config = FunctionConfig of
 {sequential: bool,
  default: string option,
  domintros: bool,
  partials: bool}

type preproc = function_config -> Proof.context -> fixes -> term spec ->
  term list * (thm list -> thm spec) * (thm list -> thm list list) * string list

val fname_of = fst o dest_Free o fst o strip_comb o fst o HOLogic.dest_eq o
  HOLogic.dest_Trueprop o Logic.strip_imp_concl o snd o dest_all_all

fun mk_case_names i "" k = mk_case_names i (string_of_int (i + 1)) k
  | mk_case_names _ _ 0 = []
  | mk_case_names _ n 1 = [n]
  | mk_case_names _ n k = map (fn i => n ^ "_" ^ string_of_int i) (1 upto k)

fun empty_preproc check (_: function_config) (ctxt: Proof.context) (fixes: fixes) spec =
  let
    val (bnds, tss) = split_list spec
    val ts = flat tss
    val _ = check ctxt fixes ts
    val fnames = map (fst o fst) fixes
    val indices = map (fn eq => find_index (curry op = (fname_of eq)) fnames) ts

    fun sort xs = partition_list (fn i => fn (j,_) => i = j) 0 (length fnames - 1)
      (indices ~~ xs) |> map (map snd)

    (* using theorem names for case name currently disabled *)
    val cnames = map_index (fn (i, _) => mk_case_names i "" 1) bnds |> flat
  in
    (ts, curry op ~~ bnds o Library.unflat tss, sort, cnames)
  end


(* context data *)

structure Data = Generic_Data
(
  type T =
    thm list *
    (term * info) Item_Net.T *
    (bool -> Proof.context -> tactic) *
    preproc
  val empty: T =
   ([],
    Item_Net.init (op aconv o apply2 fst) (single o fst),
    fn _ => error "Termination prover not configured",
    empty_preproc check_defs)
  fun merge
   ((termination_rules1, functions1, termination_prover1, preproc1),
    (termination_rules2, functions2, _, _)) : T =
   (Thm.merge_thms (termination_rules1, termination_rules2),
    Item_Net.merge (functions1, functions2),
    termination_prover1,
    preproc1)
)

fun termination_rule_tac ctxt = resolve_tac ctxt (#1 (Data.get (Context.Proof ctxt)))

val store_termination_rule = Data.map o @{apply 4(1)} o cons o Thm.trim_context

val get_functions = #2 o Data.get o Context.Proof

fun retrieve_function_data ctxt t =
  Item_Net.retrieve (get_functions ctxt) t
  |> (map o apsnd) (transform_function_data (Morphism.transfer_morphism' ctxt));

val add_function_data =
  transform_function_data Morphism.trim_context_morphism #>
  (fn info as {fs, termination, ...} =>
    (Data.map o @{apply 4(2)}) (fold (fn f => Item_Net.update (f, info)) fs)
    #> store_termination_rule termination)

fun termination_prover_tac quiet ctxt = #3 (Data.get (Context.Proof ctxt)) quiet ctxt
val set_termination_prover = Data.map o @{apply 4(3)} o K

val get_preproc = #4 o Data.get o Context.Proof
val set_preproc = Data.map o @{apply 4(4)} o K


(* function definition result data *)

datatype function_result = FunctionResult of
 {fs: term list,
  G: term,
  R: term,
  dom: term,
  psimps : thm list,
  simple_pinducts : thm list,
  cases : thm list,
  pelims : thm list list,
  termination : thm,
  domintros : thm list option}

fun import_function_data t ctxt =
  let
    val ct = Thm.cterm_of ctxt t
    fun inst_morph u =
      Morphism.instantiate_morphism (Thm.match (Thm.cterm_of ctxt u, ct))
    fun match (u, data) =
      SOME (transform_function_data (inst_morph u) data) handle Pattern.MATCH => NONE
  in
    get_first match (retrieve_function_data ctxt t)
    |> Option.map (transform_function_data (Morphism.transfer_morphism' ctxt))
  end

fun import_last_function ctxt =
  (case Item_Net.content (get_functions ctxt) of
    [] => NONE
  | (t, _) :: _ =>
      let val (t', ctxt') = yield_singleton (Variable.import_terms true) t ctxt
      in import_function_data t' ctxt' end)


(* configuration management *)

datatype function_opt =
    Sequential
  | Default of string
  | DomIntros
  | No_Partials

fun apply_opt Sequential (FunctionConfig {sequential = _, default, domintros, partials}) =
      FunctionConfig
        {sequential = true, default = default, domintros = domintros, partials = partials}
  | apply_opt (Default d) (FunctionConfig {sequential, default = _, domintros, partials}) =
      FunctionConfig
        {sequential = sequential, default = SOME d, domintros = domintros, partials = partials}
  | apply_opt DomIntros (FunctionConfig {sequential, default, domintros = _, partials}) =
      FunctionConfig
        {sequential = sequential, default = default, domintros = true, partials = partials}
  | apply_opt No_Partials (FunctionConfig {sequential, default, domintros, partials = _}) =
      FunctionConfig
        {sequential = sequential, default = default, domintros = domintros, partials = false}

val default_config =
  FunctionConfig { sequential=false, default=NONE,
    domintros=false, partials=true}

local
  val option_parser = Parse.group (fn () => "option")
    ((Parse.reserved "sequential" >> K Sequential)
     || ((Parse.reserved "default" |-- Parse.term) >> Default)
     || (Parse.reserved "domintros" >> K DomIntros)
     || (Parse.reserved "no_partials" >> K No_Partials))

  fun config_parser default =
    (Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.!!! (Parse.list1 option_parser) --| \<^keyword>\<open>)\<close>) [])
     >> (fn opts => fold apply_opt opts default)
in
  fun function_parser default_cfg =
      config_parser default_cfg -- Parse_Spec.specification
end


end
end
