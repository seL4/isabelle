(*  Title:      HOL/Eisbach/method_closure.ML
    Author:     Daniel Matichuk, NICTA/UNSW

Facilities for treating method syntax as a closure, with abstraction
over terms, facts and other methods.

The 'method' command allows to define new proof methods by combining
existing ones with their usual syntax.
*)

signature METHOD_CLOSURE =
sig
  val apply_method: Proof.context -> string -> term list -> thm list list ->
    (Proof.context -> Method.method) list -> Proof.context -> thm list -> context_tactic
  val method: binding -> (binding * typ option * mixfix) list -> binding list ->
    binding list -> binding list -> Token.src -> local_theory -> string * local_theory
  val method_cmd: binding -> (binding * string option * mixfix) list -> binding list ->
    binding list -> binding list -> Token.src -> local_theory -> string * local_theory
end;

structure Method_Closure: METHOD_CLOSURE =
struct

(* auxiliary data for method definition *)

structure Method_Definition = Proof_Data
(
  type T =
    (Proof.context -> Method.method) Symtab.table *  (*dynamic methods*)
    (term list -> Proof.context -> Method.method) Symtab.table  (*recursive methods*);
  fun init _ : T = (Symtab.empty, Symtab.empty);
);

fun lookup_dynamic_method ctxt full_name =
  (case Symtab.lookup (#1 (Method_Definition.get ctxt)) full_name of
    SOME m => m ctxt
  | NONE => error ("Illegal use of internal Eisbach method: " ^ quote full_name));

val update_dynamic_method = Method_Definition.map o apfst o Symtab.update;

fun get_recursive_method full_name ts ctxt =
  (case Symtab.lookup (#2 (Method_Definition.get ctxt)) full_name of
    SOME m => m ts ctxt
  | NONE => error ("Illegal use of internal Eisbach method: " ^ quote full_name));

val put_recursive_method = Method_Definition.map o apsnd o Symtab.update;


(* stored method closures *)

type closure = {vars: term list, named_thms: string list, methods: string list, body: Method.text};

structure Data = Generic_Data
(
  type T = closure Symtab.table;
  val empty: T = Symtab.empty;
  val extend = I;
  fun merge data : T = Symtab.merge (K true) data;
);

fun get_closure ctxt name =
  (case Symtab.lookup (Data.get (Context.Proof ctxt)) name of
    SOME closure => closure
  | NONE => error ("Unknown Eisbach method: " ^ quote name));

fun put_closure binding (closure: closure) lthy =
  let
    val name = Local_Theory.full_name lthy binding;
  in
    lthy |> Local_Theory.declaration {syntax = false, pervasive = true} (fn phi =>
      Data.map
        (Symtab.update (name,
          {vars = map (Morphism.term phi) (#vars closure),
           named_thms = #named_thms closure,
           methods = #methods closure,
           body = (Method.map_source o map) (Token.transform phi) (#body closure)})))
  end;


(* instantiate and evaluate method text *)

fun method_instantiate vars body ts ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val subst = fold (Pattern.match thy) (vars ~~ ts) (Vartab.empty, Vartab.empty);
    val morphism = Morphism.term_morphism "method_instantiate" (Envir.subst_term subst);
    val body' = (Method.map_source o map) (Token.transform morphism) body;
  in Method.evaluate_runtime body' ctxt end;



(** apply method closure **)

fun recursive_method full_name vars body ts =
  let val m = method_instantiate vars body
  in put_recursive_method (full_name, m) #> m ts end;

fun apply_method ctxt method_name terms facts methods =
  let
    fun declare_facts (name :: names) (fact :: facts) =
          fold (Context.proof_map o Named_Theorems.add_thm name) fact
          #> declare_facts names facts
      | declare_facts _ [] = I
      | declare_facts [] (_ :: _) = error ("Excessive facts for method " ^ quote method_name);
    val {vars, named_thms, methods = method_args, body} = get_closure ctxt method_name;
  in
    declare_facts named_thms facts
    #> fold update_dynamic_method (method_args ~~ methods)
    #> recursive_method method_name vars body terms
  end;



(** define method closure **)

local

fun setup_local_method binding lthy =
  let
    val full_name = Local_Theory.full_name lthy binding;
    fun dynamic_method ctxt = lookup_dynamic_method ctxt full_name;
  in
    lthy
    |> update_dynamic_method (full_name, K Method.fail)
    |> Method.local_setup binding (Scan.succeed dynamic_method) "(internal)"
  end;

fun check_named_thm ctxt binding =
  let
    val bname = Binding.name_of binding;
    val pos = Binding.pos_of binding;
    val full_name = Named_Theorems.check ctxt (bname, pos);
    val parser: Method.modifier parser =
      Args.$$$ bname -- Args.colon
        >> K {init = I, attribute = Named_Theorems.add full_name, pos = pos};
  in (full_name, parser) end;

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

fun parse_method_args method_args =
  let
    fun bind_method (name, text) ctxt =
      let
        val method = Method.evaluate_runtime text;
        val inner_update = method o update_dynamic_method (name, K (method ctxt));
      in update_dynamic_method (name, inner_update) ctxt end;

    fun rep [] x = Scan.succeed [] x
      | rep (m :: ms) x = ((Method.text_closure >> pair m) ::: rep ms) x;
  in rep method_args >> fold bind_method end;

fun gen_method add_fixes name vars uses declares methods source lthy =
  let
    val (uses_internal, lthy1) = lthy
      |> Proof_Context.concealed
      |> Local_Theory.begin_target
      |-> Proof_Context.private_scope
      |> Local_Theory.map_background_naming (Name_Space.add_path (Binding.name_of name))
      |> Config.put Method.old_section_parser true
      |> fold setup_local_method methods
      |> fold_map (fn b => Named_Theorems.declare b "") uses;

    val (term_args, lthy2) = lthy1
      |> add_fixes vars |-> fold_map Proof_Context.inferred_param |>> map Free;

    val (named_thms, modifiers) = map (check_named_thm lthy2) (declares @ uses) |> split_list;

    val method_args = map (Local_Theory.full_name lthy2) methods;

    fun parser args meth =
      apfst (Config.put_generic Method.old_section_parser true) #>
      (parse_term_args args --
        parse_method_args method_args --|
        (Scan.depend (fn context =>
          Scan.succeed (fold Named_Theorems.clear uses_internal context, ())) --
         Method.sections modifiers)) >> (fn (ts, decl) => meth ts o decl);

    val full_name = Local_Theory.full_name lthy name;

    val lthy3 = lthy2
      |> Method.local_setup (Binding.make (Binding.name_of name, Position.none))
        (parser term_args (get_recursive_method full_name)) "(internal)"
      |> put_recursive_method (full_name, fn _ => fn _ => Method.fail);

    val (text, src) =
      Method.read_closure (Config.put Proof_Context.dynamic_facts_dummy true lthy3) source;

    val morphism =
      Variable.export_morphism lthy3
        (lthy
          |> Proof_Context.transfer (Proof_Context.theory_of lthy3)
          |> fold Token.declare_maxidx src
          |> Variable.declare_maxidx (Variable.maxidx_of lthy3));

    val text' = (Method.map_source o map) (Token.transform morphism) text;
    val term_args' = map (Morphism.term morphism) term_args;
  in
    lthy3
    |> Local_Theory.close_target
    |> Proof_Context.restore_naming lthy
    |> put_closure name
        {vars = term_args', named_thms = named_thms, methods = method_args, body = text'}
    |> Method.local_setup name
        (Args.context :|-- (fn ctxt =>
          let val {body, vars, ...} = get_closure ctxt full_name in
            parser vars (recursive_method full_name vars body) end)) ""
    |> pair full_name
  end;

in

val method = gen_method Proof_Context.add_fixes;
val method_cmd = gen_method Proof_Context.add_fixes_cmd;

end;

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>method\<close> "Eisbach method definition"
    (Parse.binding -- Parse.for_fixes --
      ((Scan.optional (\<^keyword>\<open>methods\<close> |-- Parse.!!! (Scan.repeat1 Parse.binding)) []) --
        (Scan.optional (\<^keyword>\<open>uses\<close> |-- Parse.!!! (Scan.repeat1 Parse.binding)) [])) --
      (Scan.optional (\<^keyword>\<open>declares\<close> |-- Parse.!!! (Scan.repeat1 Parse.binding)) []) --
      Parse.!!! (\<^keyword>\<open>=\<close> |-- Parse.args1 (K true)) >>
      (fn ((((name, vars), (methods, uses)), declares), src) =>
        #2 o method_cmd name vars uses declares methods src));

end;
