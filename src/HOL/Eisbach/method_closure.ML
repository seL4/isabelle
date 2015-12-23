(*  Title:      HOL/Eisbach/method_closure.ML
    Author:     Daniel Matichuk, NICTA/UNSW

Facilities for treating method syntax as a closure, with abstraction
over terms, facts and other methods.

The 'method' command allows to define new proof methods by combining
existing ones with their usual syntax.
*)

signature METHOD_CLOSURE =
sig
  val get_method: Proof.context -> string * Position.T ->
    (term list * (string list * string list)) * Method.text
  val eval_method: Proof.context -> (term list * string list) * Method.text ->
    term list -> (string * thm list) list -> (Proof.context -> Method.method) list ->
    Proof.context -> Method.method
  val read: Proof.context -> Token.src -> Method.text
  val read_closure: Proof.context -> Token.src -> Method.text * Token.src
  val read_closure_input: Proof.context -> Input.source -> Method.text * Token.src
  val method_text: Method.text context_parser
  val method_evaluate: Method.text -> Proof.context -> Method.method
  val method: binding -> (binding * typ option * mixfix) list -> binding list ->
    binding list -> binding list -> Token.src -> local_theory -> string * local_theory
  val method_cmd: binding -> (binding * string option * mixfix) list -> binding list ->
    binding list -> binding list -> Token.src -> local_theory -> string * local_theory
end;

structure Method_Closure: METHOD_CLOSURE =
struct

(* context data for ML antiquotation *)

structure Data = Generic_Data
(
  type T = ((term list * (string list * string list)) * Method.text) Symtab.table;
  val empty: T = Symtab.empty;
  val extend = I;
  fun merge data : T = Symtab.merge (K true) data;
);

fun get_method ctxt (xname, pos) =
  let
    val name = Method.check_name ctxt (xname, pos);
  in
    (case Symtab.lookup (Data.get (Context.Proof ctxt)) name of
      SOME entry => entry
    | NONE => error ("Unknown Eisbach method: " ^ quote name ^ Position.here pos))
  end;

(* FIXME redundant!? -- base name of binding is not changed by usual morphisms*)
fun Morphism_name phi name =
  Morphism.binding phi (Binding.make (name, Position.none)) |> Binding.name_of;

fun add_method binding ((fixes, declares, methods), text) lthy =
  lthy |>
  Local_Theory.declaration {syntax = false, pervasive = true} (fn phi =>
    Data.map
      (Symtab.update (Local_Theory.full_name lthy binding,
        (((map (Morphism.term phi) fixes),
          (map (Morphism_name phi) declares, map (Morphism_name phi) methods)),
          (Method.map_source o map) (Token.transform phi) text))));


(* context data for method definition *)

structure Local_Data = Proof_Data
(
  type T =
    (Proof.context -> Method.method) Symtab.table *  (*dynamic methods*)
    (term list -> Proof.context -> Method.method)  (*recursive method*);
  fun init _ : T = (Symtab.empty, fn _ => fn _ => Method.fail);
);

fun lookup_dynamic_method ctxt full_name =
  (case Symtab.lookup (#1 (Local_Data.get ctxt)) full_name of
    SOME m => m
  | NONE => error ("Illegal use of internal Eisbach method: " ^ quote full_name));

val update_dynamic_method = Local_Data.map o apfst o Symtab.update;

val get_recursive_method = #2 o Local_Data.get;
val put_recursive_method = Local_Data.map o apsnd o K;


(* read method text *)

fun read ctxt src =
  (case Scan.read Token.stopper (Parse.!!! (Method.parser 0 --| Scan.ahead Parse.eof)) src of
    SOME (text, range) =>
      if Method.checked_text text then text
      else (Method.report (text, range); Method.check_text ctxt text)
  | NONE =>
      error ("Failed to parse method" ^ Position.here (Position.set_range (Token.range_of src))));

fun read_closure ctxt src0 =
  let
    val src1 = map Token.init_assignable src0;
    val text = read ctxt src1 |> Method.map_source (Method.method_closure ctxt);
    val src2 = map Token.closure src1;
  in (text, src2) end;

fun read_closure_input ctxt =
  Input.source_explode #>
  Token.read_no_commands (Thy_Header.get_keywords' ctxt) (Scan.one Token.not_eof) #>
  read_closure ctxt;

val method_text =
  Args.context -- Scan.lift (Parse.token Parse.text) >> (fn (ctxt, tok) =>
    (case Token.get_value tok of
      SOME (Token.Source src) => read ctxt src
    | _ =>
        let
          val (text, src) = read_closure_input ctxt (Token.input_of tok);
          val _ = Token.assign (SOME (Token.Source src)) tok;
        in text end));


(* evaluate method text *)

fun method_evaluate text ctxt =
  let
    val text' =
      text |> (Method.map_source o map o Token.map_facts)
        (fn SOME name =>
              (case Proof_Context.lookup_fact ctxt name of
                SOME (false, ths) => K ths
              | _ => I)
          | NONE => I);
    val ctxt' = Config.put Method.closure false ctxt;
  in fn facts => Method.RUNTIME (fn st => Method.evaluate text' ctxt' facts st) end;

fun method_instantiate env text =
  let
    val morphism = Morphism.term_morphism "method_instantiate" (Envir.norm_term env);
    val text' = (Method.map_source o map) (Token.transform morphism) text;
  in method_evaluate text' end;



(** Isar command **)

local

fun setup_local_method binding lthy =
  let
    val full_name = Local_Theory.full_name lthy binding;
    fun get_method ctxt = lookup_dynamic_method ctxt full_name ctxt;
  in
    lthy
    |> update_dynamic_method (full_name, K Method.fail)
    |> Method.local_setup binding (Scan.succeed get_method) "(internal)"
  end;

fun check_attrib ctxt attrib =
  let
    val name = Binding.name_of attrib;
    val pos = Binding.pos_of attrib;
    val named_thm = Named_Theorems.check ctxt (name, pos);
    val parser: Method.modifier parser =
      Args.$$$ name -- Args.colon >>
        K {init = I, attribute = Named_Theorems.add named_thm, pos = pos};
  in (named_thm, parser) end;

fun dummy_named_thm named_thm =
  Context.proof_map
    (Named_Theorems.clear named_thm
      #> Named_Theorems.add_thm named_thm Drule.free_dummy_thm);

fun parse_term_args args =
  Args.context :|-- (fn ctxt =>
    let
      val ctxt' = Proof_Context.set_mode (Proof_Context.mode_schematic) ctxt;

      fun parse T =
        (if T = propT then Syntax.parse_prop ctxt' else Syntax.parse_term ctxt')
        #> Type.constraint (Type_Infer.paramify_vars T);

      fun do_parse' T =
        Parse_Tools.name_term >> Parse_Tools.parse_val_cases (parse T);

      fun do_parse (Var (_, T)) = do_parse' T
        | do_parse (Free (_, T)) = do_parse' T
        | do_parse t = error ("Unexpected method parameter: " ^ Syntax.string_of_term ctxt' t);

       fun rep [] x = Scan.succeed [] x
         | rep (t :: ts) x  = (do_parse t ::: rep ts) x;

      fun check ts =
        let
          val (ts, fs) = split_list ts;
          val ts' = Syntax.check_terms ctxt' ts |> Variable.polymorphic ctxt';
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

fun parse_method_args method_names =
  let
    fun bind_method (name, text) ctxt =
      let
        val method = method_evaluate text;
        val inner_update = method o update_dynamic_method (name, K (method ctxt));
      in update_dynamic_method (name, inner_update) ctxt end;

    fun rep [] x = Scan.succeed [] x
      | rep (t :: ts) x = ((method_text >> pair t) ::: rep ts) x;
  in rep method_names >> fold bind_method end;

fun gen_method add_fixes name vars uses declares methods source lthy =
  let
    val (uses_internal, lthy1) = lthy
      |> Proof_Context.concealed
      |> Local_Theory.open_target |-> Proof_Context.private_scope
      |> Local_Theory.map_background_naming (Name_Space.add_path (Binding.name_of name))
      |> Config.put Method.old_section_parser true
      |> fold setup_local_method methods
      |> fold_map (fn b => Named_Theorems.declare b "") uses;

    val (term_args, lthy2) = lthy1
      |> add_fixes vars |-> fold_map Proof_Context.inferred_param |>> map Free;

    val (named_thms, modifiers) = map (check_attrib lthy2) (declares @ uses) |> split_list;
    val method_names = map (Local_Theory.full_name lthy2) methods;

    fun parser args =
      apfst (Config.put_generic Method.old_section_parser true) #>
      (parse_term_args args --
        parse_method_args method_names --|
        (Scan.depend (fn context =>
          Scan.succeed (fold Named_Theorems.clear uses_internal context, ())) --
         Method.sections modifiers));

    val lthy3 = lthy2
      |> fold dummy_named_thm named_thms
      |> Method.local_setup (Binding.make (Binding.name_of name, Position.none))
        (parser term_args >> (fn (fixes, decl) =>
          fn ctxt => get_recursive_method ctxt fixes (decl ctxt))) "(internal)";

    val (text, src) = read_closure lthy3 source;

    val morphism =
      Variable.export_morphism lthy3
        (lthy
          |> Proof_Context.transfer (Proof_Context.theory_of lthy3)
          |> fold Token.declare_maxidx src
          |> Variable.declare_maxidx (Variable.maxidx_of lthy3));

    val text' = (Method.map_source o map) (Token.transform morphism) text;
    val term_args' = map (Morphism.term morphism) term_args;

    fun real_exec ts ctxt =
      method_instantiate (match_term_args ctxt term_args' ts) text' ctxt;
    val real_parser =
      parser term_args' >> (fn (fixes, decl) => fn ctxt =>
        real_exec fixes (put_recursive_method real_exec (decl ctxt)));
  in
    lthy3
    |> Local_Theory.close_target
    |> Proof_Context.restore_naming lthy
    |> Method.local_setup name real_parser "(defined in Eisbach)"
    |> add_method name ((term_args', named_thms, method_names), text')
    |> pair (Local_Theory.full_name lthy name)
  end;

in

val method = gen_method Proof_Context.add_fixes;
val method_cmd = gen_method Proof_Context.add_fixes_cmd;

end;

val _ =
  Outer_Syntax.local_theory @{command_keyword method} "Eisbach method definition"
    (Parse.binding -- Parse.for_fixes --
      ((Scan.optional (@{keyword "methods"} |-- Parse.!!! (Scan.repeat1 Parse.binding)) []) --
        (Scan.optional (@{keyword "uses"} |-- Parse.!!! (Scan.repeat1 Parse.binding)) [])) --
      (Scan.optional (@{keyword "declares"} |-- Parse.!!! (Scan.repeat1 Parse.binding)) []) --
      Parse.!!! (@{keyword "="} |-- Parse.args1 (K true)) >>
      (fn ((((name, vars), (methods, uses)), declares), src) =>
        #2 o method_cmd name vars uses declares methods src));



(** ML antiquotation **)

fun eval_method ctxt0 header fixes attribs methods =
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
      #> put_recursive_method (fn xs => method_instantiate (match xs) text);
  in
    fn ctxt => method_instantiate (match fixes) text (setup_ctxt ctxt)
  end;

val _ =
  Theory.setup
    (ML_Antiquotation.inline @{binding method}  (* FIXME ML_Antiquotation.value (!?) *)
      (Args.context -- Scan.lift (Args.mode "drop_cases") -- Scan.lift (Parse.position Parse.name)
        >> (fn ((ctxt, drop_cases), nameref) =>
          let
            val ((targs, (factargs, margs)), _) = get_method ctxt nameref;

            val has_factargs = not (null factargs);

            val (targnms, ctxt') =
              fold_map (fn (Var ((x, _), _)) => ML_Context.variant x) targs ctxt;
            val (margnms, ctxt'') = fold_map ML_Context.variant margs ctxt';
            val (factsnm, _) = ML_Context.variant "facts" ctxt'';

            val fn_header =
              margnms
              |> has_factargs ? append [factsnm]
              |> append targnms
              |> map (fn nm => "fn " ^ nm ^ " => ")
              |> implode;

            val ML_context = ML_Context.struct_name ctxt ^ ".ML_context";
            val ml_inner =
              ML_Syntax.atomic
                ("Method_Closure.get_method " ^  ML_context ^
                  ML_Syntax.print_pair ML_Syntax.print_string ML_Syntax.print_position nameref ^
                  "|> (fn ((targs, (_, margs)), text) => Method_Closure.eval_method " ^
                  ML_context ^ " ((targs, margs), text))");

            val drop_cases_suffix =
              if drop_cases then "#> (fn f => (fn ctxt => fn thms => f ctxt thms |> Seq.map snd))"
              else "";

            val factsnm = if has_factargs then factsnm else "[]";
          in
            ML_Syntax.atomic
              (fn_header ^ ml_inner ^ " " ^ ML_Syntax.print_list I targnms ^ " " ^
                factsnm ^ " " ^
                ML_Syntax.print_list I margnms ^ drop_cases_suffix)
          end)));

end;
