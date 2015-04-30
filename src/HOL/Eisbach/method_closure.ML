(*  Title:      method_closure.ML
    Author:     Daniel Matichuk, NICTA/UNSW

Facilities for treating method syntax as a closure, with abstraction
over terms, facts and other methods.

The 'method' command allows to define new proof methods by combining
existing ones with their usual syntax.
*)

signature METHOD_CLOSURE =
sig
  val is_dummy: thm -> bool
  val tag_free_thm: thm -> thm
  val free_aware_rule_attribute: thm list -> (Context.generic -> thm -> thm) -> Thm.attribute
  val read_inner_method: Proof.context -> Token.src -> Method.text
  val read_text_closure: Proof.context -> Token.src -> Token.src * Method.text
  val read_inner_text_closure: Proof.context -> Input.source -> Token.src * Method.text
  val method_evaluate: Method.text -> Proof.context -> Method.method
  val get_inner_method: Proof.context -> string * Position.T ->
    (term list * (string list * string list)) * Method.text
  val eval_inner_method: Proof.context -> (term list * string list) * Method.text ->
    term list -> (string * thm list) list -> Method.method list ->
    Proof.context -> Method.method
  val method_definition: binding -> (binding * typ option * mixfix) list ->
    binding list -> binding list -> binding list -> Token.src -> local_theory -> local_theory
  val method_definition_cmd: binding -> (binding * string option * mixfix) list ->
    binding list -> binding list -> binding list -> Token.src -> local_theory -> local_theory
end;

structure Method_Closure: METHOD_CLOSURE =
struct

(* context data *)

structure Data = Generic_Data
(
  type T =
    ((term list * (string list * string list)) * Method.text) Symtab.table;
  val empty: T = Symtab.empty;
  val extend = I;
  fun merge (methods1,methods2) : T =
    (Symtab.merge (K true) (methods1, methods2));
);

val get_methods = Data.get o Context.Proof;
val map_methods = Data.map;


structure Local_Data = Proof_Data
(
  type T =
    Method.method Symtab.table *  (*dynamic methods*)
    (term list -> Proof.context -> Method.method)  (*recursive method*);
  fun init _ : T = (Symtab.empty, fn _ => fn _ => Method.fail);
);

fun lookup_dynamic_method full_name ctxt =
  (case Symtab.lookup (#1 (Local_Data.get ctxt)) full_name of
    SOME m => m
  | NONE => error ("Illegal use of internal Eisbach method: " ^ quote full_name));

val update_dynamic_method = Local_Data.map o apfst o Symtab.update;

val get_recursive_method = #2 o Local_Data.get;
val put_recursive_method = Local_Data.map o apsnd o K;


(* free thm *)

fun is_dummy thm =
  (case try Logic.dest_term (Thm.concl_of (perhaps (try Goal.conclude) thm)) of
    NONE => false
  | SOME t => Term.is_dummy_pattern t);

val free_thmN = "Method_Closure.free_thm";
fun tag_free_thm thm = Thm.tag_rule (free_thmN, "") thm;

val dummy_free_thm = tag_free_thm Drule.dummy_thm;

fun is_free_thm thm = Properties.defined (Thm.get_tags thm) free_thmN;

fun is_free_fact [thm] = is_free_thm thm
  | is_free_fact _ = false;

fun free_aware_rule_attribute args f =
  Thm.rule_attribute (fn context => fn thm =>
    if exists is_free_thm (thm :: args) then dummy_free_thm
    else f context thm);


(* thm semantics for combined methods with internal parser. Simulates outer syntax parsing. *)
(* Creates closures for each combined method while parsing, based on the parse context *)

fun read_inner_method ctxt src =
  let
    val toks = Token.args_of_src src;
    val parser = Parse.!!! (Method.parser' ctxt 0 --| Scan.ahead Parse.eof);
  in
    (case Scan.read Token.stopper parser toks of
      SOME (method_text, pos) => (Method.report (method_text, pos); method_text)
    | NONE => error ("Failed to parse method" ^ Position.here (#2 (Token.name_of_src src))))
  end;

fun read_text_closure ctxt source =
  let
    val src = Token.init_assignable_src source;
    val method_text = read_inner_method ctxt src;
    val method_text' = Method.map_source (Method.method_closure ctxt) method_text;
    (*FIXME: Does not markup method parameters. Needs to be done by Method.parser' directly. *)
    val _ = Method.map_source (fn src => (try (Method.check_name ctxt) (Token.name_of_src src);src)) method_text;
    val src' = Token.closure_src src;
  in (src', method_text') end;

fun read_inner_text_closure ctxt input =
  let
    val keywords = Thy_Header.get_keywords' ctxt;
    val toks =
      Input.source_explode input
      |> Token.read_no_commands keywords (Scan.one Token.not_eof);
  in read_text_closure ctxt (Token.src ("", Input.pos_of input) toks) end;


val parse_method =
  Args.context -- Scan.lift (Parse.token Parse.cartouche) >> (fn (ctxt, tok) =>
    (case Token.get_value tok of
      NONE =>
        let
           val input = Token.input_of tok;
           val (src,text) = read_inner_text_closure ctxt input;
           val _ = Token.assign (SOME (Token.Source src)) tok;
        in text end
    | SOME (Token.Source src) => read_inner_method ctxt src
    | SOME _ =>
        error ("Unexpected inner token value for method cartouche" ^
          Position.here (Token.pos_of tok))));

fun method_evaluate text ctxt : Method.method = fn facts => fn st =>
  if is_dummy st then Seq.empty
  else Method.evaluate text (Config.put Method.closure false ctxt) facts st;


fun parse_term_args args =
  Args.context :|-- (fn ctxt =>
    let
      fun parse T =
        (if T = propT then Syntax.parse_prop ctxt else Syntax.parse_term ctxt)
        #> Type.constraint (Type_Infer.paramify_vars T);

      fun do_parse' T =
        Parse_Tools.name_term >>
          (fn Parse_Tools.Parse_Val (s, f) => (parse T s, f)
            | Parse_Tools.Real_Val t' => (t', K ()));

      fun do_parse (Var (_, T)) = do_parse' T
        | do_parse (Free (_, T)) = do_parse' T
        | do_parse t = error ("Unexpected method parameter: " ^ Syntax.string_of_term ctxt t);

       fun rep [] x = Scan.succeed [] x
         | rep (t :: ts) x  = (do_parse t -- rep ts >> op ::) x;

      fun check ts =
        let
          val (ts, fs) = split_list ts;
          val ts' = Syntax.check_terms ctxt ts |> Variable.polymorphic ctxt;
          val _ = ListPair.app (fn (f, t) => f t) (fs, ts');
        in ts' end;
    in Scan.lift (rep args) >> check end);

fun match_term_args ctxt args ts =
  let
    val match_types = Sign.typ_match (Proof_Context.theory_of ctxt) o apply2 Term.fastype_of;
    val tyenv = fold match_types (args ~~ ts) Vartab.empty;
    val tenv =
      fold (fn ((xi, T), t) => Vartab.update_new (xi, (T, t)))
        (map Term.dest_Var args ~~ ts) Vartab.empty;
  in Envir.Envir {maxidx = ~1, tenv = tenv, tyenv = tyenv} end;

fun check_attrib ctxt attrib =
  let
    val name = Binding.name_of attrib;
    val pos = Binding.pos_of attrib;
    val named_thm = Named_Theorems.check ctxt (name, pos);
    val parser: Method.modifier parser =
      Args.$$$ name -- Args.colon >>
        K {init = I, attribute = Named_Theorems.add named_thm, pos = pos};
  in (named_thm, parser) end;


fun instantiate_text env text =
  let val morphism = Morphism.term_morphism "instantiate_text" (Envir.norm_term env);
  in Method.map_source (Token.transform_src morphism) text end;

fun evaluate_dynamic_thm ctxt name =
  (case (try (Named_Theorems.get ctxt) name) of
    SOME thms => thms
  | NONE => Proof_Context.get_thms ctxt name);


fun evaluate_named_theorems ctxt =
  (Method.map_source o Token.map_values)
    (fn Token.Fact (SOME name, _) =>
          Token.Fact (SOME name, evaluate_dynamic_thm ctxt name)
      | x => x);

fun evaluate_method_def fix_env raw_text ctxt =
  let
    val text = raw_text
      |> instantiate_text fix_env
      |> evaluate_named_theorems ctxt;
  in method_evaluate text ctxt end;

fun setup_local_method binding lthy =
  let
    val full_name = Local_Theory.full_name lthy binding;
  in
    lthy
    |> update_dynamic_method (full_name, Method.fail)
    |> Method.local_setup binding (Scan.succeed (lookup_dynamic_method full_name)) "(internal)"
  end;

fun setup_local_fact binding = Named_Theorems.declare binding "";

fun parse_method_args method_names =
  let
    fun bind_method (name, text) ctxt =
      update_dynamic_method (name, method_evaluate text ctxt) ctxt;

    fun do_parse t = parse_method >> pair t;
    fun rep [] x = Scan.succeed [] x
      | rep (t :: ts) x  = (do_parse t -- rep ts >> op ::) x;
  in rep method_names >> fold bind_method end;


(* FIXME redundant!? -- base name of binding is not changed by usual morphisms*)
fun Morphism_name phi name =
  Morphism.binding phi (Binding.make (name, Position.none)) |> Binding.name_of;

fun add_method binding ((fixes, declares, methods), text) lthy =
  lthy |>
  Local_Theory.declaration {syntax = false, pervasive = true} (fn phi =>
    map_methods
      (Symtab.update (Local_Theory.full_name lthy binding,
        (((map (Morphism.term phi) fixes),
          (map (Morphism_name phi) declares, map (Morphism_name phi) methods)),
          Method.map_source (Token.transform_src phi) text))));

fun get_inner_method ctxt (xname, pos) =
  let
    val name = Method.check_name ctxt (xname, pos);
  in
    (case Symtab.lookup (get_methods ctxt) name of
      SOME entry => entry
    | NONE => error ("Unknown Eisbach method: " ^ quote name ^ Position.here pos))
  end;

fun eval_inner_method ctxt0 header fixes attribs methods =
  let
    val ((term_args, hmethods), text) = header;

    fun match fixes = (* FIXME proper context!? *)
      (case Seq.pull (Unify.matchers (Context.Proof ctxt0) (term_args ~~ fixes)) of
        SOME (env, _) => env
      | NONE => error "Couldn't match term arguments");

    fun add_thms (name, thms) =
      fold (Context.proof_map o Named_Theorems.add_thm name) thms;

    val setup_ctxt = fold add_thms attribs
      #> fold update_dynamic_method (hmethods ~~ methods)
      #> put_recursive_method (fn fixes => evaluate_method_def (match fixes) text);
  in
    fn ctxt => evaluate_method_def (match fixes) text (setup_ctxt ctxt)
  end;

fun gen_method_definition prep_vars name vars uses attribs methods source lthy =
  let
    val (uses_nms, lthy1) = lthy
      |> Proof_Context.concealed
      |> Local_Theory.open_target |-> Proof_Context.private_scope
      |> Local_Theory.map_background_naming (Name_Space.add_path (Binding.name_of name))
      |> Config.put Method.old_section_parser true
      |> fold setup_local_method methods
      |> fold_map setup_local_fact uses;

    val ((xs, Ts), lthy2) = lthy1
      |> prep_vars vars |-> Proof_Context.add_fixes
      |-> (fn xs => fold_map Proof_Context.inferred_param xs #>> pair xs);

    val term_args = map Free (xs ~~ Ts);
    val (named_thms, modifiers) = map (check_attrib lthy2) (attribs @ uses) |> split_list;
    val self_name :: method_names = map (Local_Theory.full_name lthy2) (name :: methods);

    fun parser args eval =
      apfst (Config.put_generic Method.old_section_parser true) #>
      (parse_term_args args --|
        Method.sections modifiers --
        (*Scan.depend (fn context => Scan.succeed () >> (K (fold XNamed_Theorems.empty uses_nms context, ()))) --*)  (* FIXME *)
        parse_method_args method_names >> eval);

    val lthy3 = lthy2
      |> Method.local_setup (Binding.make (Binding.name_of name, Position.none))
        (parser term_args
          (fn (fixes, decl) => fn ctxt => get_recursive_method ctxt fixes (decl ctxt))) "(internal)";

    val (src, text) = read_text_closure lthy3 source;

    val morphism =
      Variable.export_morphism lthy3
        (lthy
          |> Proof_Context.transfer (Proof_Context.theory_of lthy3)
          |> Token.declare_maxidx_src src
          |> Variable.declare_maxidx (Variable.maxidx_of lthy3));

    val text' = Method.map_source (Token.transform_src morphism) text;
    val term_args' = map (Morphism.term morphism) term_args;

    fun real_exec ts ctxt =
      evaluate_method_def (match_term_args ctxt term_args' ts) text' ctxt;
    val real_parser =
      parser term_args' (fn (fixes, decl) => fn ctxt =>
        real_exec fixes (put_recursive_method real_exec (decl ctxt)));
  in
    lthy3
    |> Local_Theory.close_target
    |> Proof_Context.restore_naming lthy
    |> Method.local_setup name real_parser "(defined in Eisbach)"
    |> add_method name ((term_args', named_thms, method_names), text')
  end;

val method_definition = gen_method_definition Proof_Context.cert_vars;
val method_definition_cmd = gen_method_definition Proof_Context.read_vars;

val _ =
  Outer_Syntax.local_theory @{command_keyword method} "Eisbach method definition"
    (Parse.binding -- Parse.for_fixes --
      ((Scan.optional (@{keyword "uses"} |-- Parse.!!! (Scan.repeat1 Parse.binding)) []) --
        (Scan.optional (@{keyword "declares"} |-- Parse.!!! (Scan.repeat1 Parse.binding)) [])) --
      (Scan.optional (@{keyword "methods"} |-- Parse.!!! (Scan.repeat1 Parse.binding)) []) --
      Parse.!!! (@{keyword "="}
        |-- (Parse.position (Parse.args1 (K true)) >> (fn (args, pos) => Token.src ("", pos) args)))
      >> (fn ((((name, vars), (uses, attribs)), methods), source) =>
        method_definition_cmd name vars uses attribs methods source));
end;
