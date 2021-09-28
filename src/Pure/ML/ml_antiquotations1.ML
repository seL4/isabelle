(*  Title:      Pure/ML/ml_antiquotations1.ML
    Author:     Makarius

Miscellaneous ML antiquotations: part 1.
*)

signature ML_ANTIQUOTATIONS1 =
sig
  val make_judgment: Proof.context -> term -> term
  val dest_judgment: Proof.context -> term -> term
end;

structure ML_Antiquotations1: ML_ANTIQUOTATIONS1 =
struct

(* ML support *)

val _ = Theory.setup
 (ML_Antiquotation.inline \<^binding>\<open>undefined\<close>
    (Scan.succeed "(raise General.Match)") #>

  ML_Antiquotation.inline \<^binding>\<open>assert\<close>
    (Scan.succeed "(fn b => if b then () else raise General.Fail \"Assertion failed\")") #>

  ML_Antiquotation.declaration_embedded \<^binding>\<open>print\<close>
    (Scan.lift (Scan.optional Args.embedded "Output.writeln"))
      (fn src => fn output => fn ctxt =>
        let
          val struct_name = ML_Context.struct_name ctxt;
          val (_, pos) = Token.name_of_src src;
          val (a, ctxt') = ML_Context.variant "output" ctxt;
          val env =
            "val " ^ a ^ ": string -> unit =\n\
            \  (" ^ output ^ ") o (fn s => s ^ Position.here (" ^
            ML_Syntax.print_position pos ^ "));\n";
          val body =
            "(fn x => (" ^ struct_name ^ "." ^ a ^ " (" ^ ML_Pretty.make_string_fn ^ " x); x))";
        in (K (env, body), ctxt') end) #>

  ML_Antiquotation.value \<^binding>\<open>rat\<close>
    (Scan.lift (Scan.optional (Args.$$$ "~" >> K ~1) 1 -- Parse.nat --
      Scan.optional (Args.$$$ "/" |-- Parse.nat) 1) >> (fn ((sign, a), b) =>
        "Rat.make " ^ ML_Syntax.print_pair ML_Syntax.print_int ML_Syntax.print_int (sign * a, b))) #>

  ML_Antiquotation.conditional \<^binding>\<open>if_linux\<close> (fn _ => ML_System.platform_is_linux) #>
  ML_Antiquotation.conditional \<^binding>\<open>if_macos\<close> (fn _ => ML_System.platform_is_macos) #>
  ML_Antiquotation.conditional \<^binding>\<open>if_windows\<close> (fn _ => ML_System.platform_is_windows) #>
  ML_Antiquotation.conditional \<^binding>\<open>if_unix\<close> (fn _ => ML_System.platform_is_unix));


(* formal entities *)

val _ = Theory.setup
 (ML_Antiquotation.value_embedded \<^binding>\<open>system_option\<close>
    (Args.context -- Scan.lift Args.embedded_position >> (fn (ctxt, (name, pos)) =>
      (Completion.check_option (Options.default ()) ctxt (name, pos) |> ML_Syntax.print_string))) #>

  ML_Antiquotation.value_embedded \<^binding>\<open>theory\<close>
    (Args.context -- Scan.lift Args.embedded_position >> (fn (ctxt, (name, pos)) =>
      (Theory.check {long = false} ctxt (name, pos);
       "Context.get_theory {long = false} (Proof_Context.theory_of ML_context) " ^
        ML_Syntax.print_string name))
    || Scan.succeed "Proof_Context.theory_of ML_context") #>

  ML_Antiquotation.value_embedded \<^binding>\<open>theory_context\<close>
    (Args.context -- Scan.lift Args.embedded_position >> (fn (ctxt, (name, pos)) =>
      (Theory.check {long = false} ctxt (name, pos);
       "Proof_Context.get_global (Proof_Context.theory_of ML_context) " ^
        ML_Syntax.print_string name))) #>

  ML_Antiquotation.inline \<^binding>\<open>context\<close>
    (Args.context >> (fn ctxt => ML_Context.struct_name ctxt ^ ".ML_context")) #>

  ML_Antiquotation.inline_embedded \<^binding>\<open>typ\<close>
    (Args.typ >> (ML_Syntax.atomic o ML_Syntax.print_typ)) #>

  ML_Antiquotation.inline_embedded \<^binding>\<open>term\<close>
    (Args.term >> (ML_Syntax.atomic o ML_Syntax.print_term)) #>

  ML_Antiquotation.inline_embedded \<^binding>\<open>prop\<close>
    (Args.prop >> (ML_Syntax.atomic o ML_Syntax.print_term)) #>

  ML_Antiquotation.value_embedded \<^binding>\<open>ctyp\<close> (Args.typ >> (fn T =>
    "Thm.ctyp_of ML_context " ^ ML_Syntax.atomic (ML_Syntax.print_typ T))) #>

  ML_Antiquotation.value_embedded \<^binding>\<open>cterm\<close> (Args.term >> (fn t =>
    "Thm.cterm_of ML_context " ^ ML_Syntax.atomic (ML_Syntax.print_term t))) #>

  ML_Antiquotation.value_embedded \<^binding>\<open>cprop\<close> (Args.prop >> (fn t =>
    "Thm.cterm_of ML_context " ^ ML_Syntax.atomic (ML_Syntax.print_term t))) #>

  ML_Antiquotation.inline_embedded \<^binding>\<open>oracle_name\<close>
    (Args.context -- Scan.lift Args.embedded_position >> (fn (ctxt, (name, pos)) =>
      ML_Syntax.print_string (Thm.check_oracle ctxt (name, pos)))));


(* schematic variables *)

val schematic_input =
  Args.context -- Scan.lift Args.embedded_input >> (fn (ctxt, src) =>
    (Proof_Context.set_mode Proof_Context.mode_schematic ctxt,
      (Syntax.implode_input src, Input.pos_of src)));

val _ = Theory.setup
  (ML_Antiquotation.inline_embedded \<^binding>\<open>tvar\<close>
    (schematic_input >> (fn (ctxt, (s, pos)) =>
      (case Syntax.read_typ ctxt s of
        TVar v => ML_Syntax.print_pair ML_Syntax.print_indexname ML_Syntax.print_sort v
      | _ => error ("Schematic type variable expected" ^ Position.here pos)))) #>
   ML_Antiquotation.inline_embedded \<^binding>\<open>var\<close>
    (schematic_input >> (fn (ctxt, (s, pos)) =>
      (case Syntax.read_term ctxt s of
        Var v => ML_Syntax.print_pair ML_Syntax.print_indexname ML_Syntax.print_typ v
      | _ => error ("Schematic variable expected" ^ Position.here pos)))));


(* type classes *)

fun class syn = Args.context -- Scan.lift Args.embedded_inner_syntax >> (fn (ctxt, s) =>
  Proof_Context.read_class ctxt s
  |> syn ? Lexicon.mark_class
  |> ML_Syntax.print_string);

val _ = Theory.setup
 (ML_Antiquotation.inline_embedded \<^binding>\<open>class\<close> (class false) #>
  ML_Antiquotation.inline_embedded \<^binding>\<open>class_syntax\<close> (class true) #>

  ML_Antiquotation.inline_embedded \<^binding>\<open>sort\<close>
    (Args.context -- Scan.lift Args.embedded_inner_syntax >> (fn (ctxt, s) =>
      ML_Syntax.atomic (ML_Syntax.print_sort (Syntax.read_sort ctxt s)))));


(* type constructors *)

fun type_name kind check = Args.context -- Scan.lift Args.embedded_token
  >> (fn (ctxt, tok) =>
    let
      val s = Token.inner_syntax_of tok;
      val (_, pos) = Input.source_content (Token.input_of tok);
      val Type (c, _) = Proof_Context.read_type_name {proper = true, strict = false} ctxt s;
      val decl = Type.the_decl (Proof_Context.tsig_of ctxt) (c, pos);
      val res =
        (case try check (c, decl) of
          SOME res => res
        | NONE => error ("Not a " ^ kind ^ ": " ^ quote c ^ Position.here pos));
    in ML_Syntax.print_string res end);

val _ = Theory.setup
 (ML_Antiquotation.inline_embedded \<^binding>\<open>type_name\<close>
    (type_name "logical type" (fn (c, Type.LogicalType _) => c)) #>
  ML_Antiquotation.inline_embedded \<^binding>\<open>type_abbrev\<close>
    (type_name "type abbreviation" (fn (c, Type.Abbreviation _) => c)) #>
  ML_Antiquotation.inline_embedded \<^binding>\<open>nonterminal\<close>
    (type_name "nonterminal" (fn (c, Type.Nonterminal) => c)) #>
  ML_Antiquotation.inline_embedded \<^binding>\<open>type_syntax\<close>
    (type_name "type" (fn (c, _) => Lexicon.mark_type c)));


(* constants *)

fun const_name check = Args.context -- Scan.lift Args.embedded_token
  >> (fn (ctxt, tok) =>
    let
      val s = Token.inner_syntax_of tok;
      val (_, pos) = Input.source_content (Token.input_of tok);
      val Const (c, _) = Proof_Context.read_const {proper = true, strict = false} ctxt s;
      val res = check (Proof_Context.consts_of ctxt, c)
        handle TYPE (msg, _, _) => error (msg ^ Position.here pos);
    in ML_Syntax.print_string res end);

val _ = Theory.setup
 (ML_Antiquotation.inline_embedded \<^binding>\<open>const_name\<close>
    (const_name (fn (consts, c) => (Consts.the_const consts c; c))) #>
  ML_Antiquotation.inline_embedded \<^binding>\<open>const_abbrev\<close>
    (const_name (fn (consts, c) => (Consts.the_abbreviation consts c; c))) #>
  ML_Antiquotation.inline_embedded \<^binding>\<open>const_syntax\<close>
    (const_name (fn (_, c) => Lexicon.mark_const c)) #>

  ML_Antiquotation.inline_embedded \<^binding>\<open>syntax_const\<close>
    (Args.context -- Scan.lift Args.embedded_position >> (fn (ctxt, arg) =>
      ML_Syntax.print_string (Proof_Context.check_syntax_const ctxt arg))) #>

  ML_Antiquotation.inline_embedded \<^binding>\<open>const\<close>
    (Args.context -- Scan.lift (Parse.position Args.embedded_inner_syntax) -- Scan.optional
        (Scan.lift (Args.$$$ "(") |-- Parse.enum1' "," Args.typ --| Scan.lift (Args.$$$ ")")) []
      >> (fn ((ctxt, (raw_c, pos)), Ts) =>
        let
          val Const (c, _) =
            Proof_Context.read_const {proper = true, strict = true} ctxt raw_c;
          val consts = Proof_Context.consts_of ctxt;
          val n = length (Consts.typargs consts (c, Consts.type_scheme consts c));
          val _ = length Ts <> n andalso
            error ("Constant requires " ^ string_of_int n ^ " type argument(s): " ^
              quote c ^ enclose "(" ")" (commas (replicate n "_")) ^ Position.here pos);
          val const = Const (c, Consts.instance consts (c, Ts));
        in ML_Syntax.atomic (ML_Syntax.print_term const) end)));


(* object-logic judgment *)

fun make_judgment ctxt =
  let val const = Object_Logic.judgment_const ctxt
  in fn t => Const const $ t end;

fun dest_judgment ctxt =
  let
    val is_judgment = Object_Logic.is_judgment ctxt;
    val drop_judgment = Object_Logic.drop_judgment ctxt;
  in
    fn t =>
      if is_judgment t then drop_judgment t
      else raise TERM ("dest_judgment", [t])
  end;

val _ = Theory.setup
 (ML_Antiquotation.value \<^binding>\<open>make_judgment\<close>
   (Scan.succeed "ML_Antiquotations1.make_judgment ML_context") #>
  ML_Antiquotation.value \<^binding>\<open>dest_judgment\<close>
   (Scan.succeed "ML_Antiquotations1.dest_judgment ML_context"));


(* type/term constructors *)

local

fun read_embedded ctxt src parse =
  let
    val keywords = Thy_Header.get_keywords' ctxt;
    val input = #1 (Token.syntax (Scan.lift Args.embedded_input) src ctxt);
    val syms = Input.source_explode input;
  in
    (case Token.read_body keywords parse syms of
      SOME res => res
    | NONE => error ("Bad input" ^ Position.here (Input.pos_of input)))
  end;

fun ml_args ctxt args =
  let
    val (decls, ctxt') = fold_map (ML_Context.expand_antiquotes) args ctxt;
    fun decl' ctxt'' = map (fn decl => decl ctxt'') decls;
  in (decl', ctxt') end

val parse_name = Parse.input Parse.name;

val parse_arg =
  Parse.input Parse.underscore >> ML_Lex.read_source ||
  Parse.embedded_input >> ML_Lex.read_source ||
  Parse.control >> (ML_Lex.read_symbols o Antiquote.control_symbols);

val parse_args = Scan.repeat parse_arg;
val parse_for_args =
  Scan.optional ((Parse.position (Parse.$$$ "for") >> #2) -- Parse.!!! parse_args)
    (Position.none, []);

fun parse_body b =
  if b then Parse.$$$ "=>" |-- Parse.!!! Parse.embedded_input >> (ML_Lex.read_source #> single)
  else Scan.succeed [];

fun is_dummy [Antiquote.Text tok] = ML_Lex.content_of tok = "_"
  | is_dummy _ = false;

val ml = ML_Lex.tokenize_no_range;
val ml_range = ML_Lex.tokenize_range;
val ml_dummy = ml "_";
fun ml_enclose range x = ml "(" @ x @ ml_range range ")";
fun ml_parens x = ml "(" @ x @ ml ")";
fun ml_bracks x = ml "[" @ x @ ml "]";
fun ml_commas xs = flat (separate (ml ", ") xs);
val ml_list = ml_bracks o ml_commas;
val ml_string = ml o ML_Syntax.print_string;
fun ml_pair (x, y) = ml_parens (ml_commas [x, y]);

fun type_antiquotation binding {function} =
  ML_Context.add_antiquotation binding true
    (fn range => fn src => fn ctxt =>
      let
        val ((s, type_args), fn_body) =
          read_embedded ctxt src (parse_name -- parse_args -- parse_body function);
        val pos = Input.pos_of s;

        val Type (c, Ts) =
          Proof_Context.read_type_name {proper = true, strict = true} ctxt
            (Syntax.implode_input s);
        val n = length Ts;
        val _ =
          length type_args = n orelse
            error ("Type constructor " ^ quote (Proof_Context.markup_type ctxt c) ^
              " takes " ^ string_of_int n ^ " argument(s)" ^ Position.here pos);

        val (decls1, ctxt1) = ml_args ctxt type_args;
        val (decls2, ctxt2) = ml_args ctxt1 fn_body;
        fun decl' ctxt' =
          let
            val (ml_args_env, ml_args_body) = split_list (decls1 ctxt');
            val (ml_fn_env, ml_fn_body) = split_list (decls2 ctxt');
            val ml1 =
              ml_enclose range (ml "Term.Type " @ ml_pair (ml_string c, ml_list ml_args_body));
            val ml2 =
              if function then
                ml_enclose range
                 (ml_range range "fn " @ ml1 @ ml "=> " @ flat ml_fn_body @
                  ml "| T => " @ ml_range range "raise" @
                  ml " Term.TYPE (" @ ml_string ("Type_fn " ^ quote c) @ ml ", [T], [])")
              else ml1;
          in (flat (ml_args_env @ ml_fn_env), ml2) end;
      in (decl', ctxt2) end);

fun const_antiquotation binding {pattern, function} =
  ML_Context.add_antiquotation binding true
    (fn range => fn src => fn ctxt =>
      let
        val (((s, type_args), (for_pos, term_args)), fn_body) =
          read_embedded ctxt src (parse_name -- parse_args -- parse_for_args -- parse_body function);
        val _ = Context_Position.report ctxt for_pos (Markup.keyword_properties Markup.keyword1);

        val Const (c, T) =
          Proof_Context.read_const {proper = true, strict = true} ctxt
            (Syntax.implode_input s);

        val consts = Proof_Context.consts_of ctxt;
        val type_paths = Consts.type_arguments consts c;
        val type_params = map Term.dest_TVar (Consts.typargs consts (c, T));

        val n = length type_params;
        val m = length (Term.binder_types T);

        fun err msg =
          error ("Constant " ^ quote (Proof_Context.markup_const ctxt c) ^ msg ^
            Position.here (Input.pos_of s));
        val _ =
          length type_args <> n andalso err (" takes " ^ string_of_int n ^ " type argument(s)");
        val _ =
          length term_args > m andalso Term.is_Type (Term.body_type T) andalso
            err (" cannot have more than " ^ string_of_int m ^ " argument(s)");

        val (decls1, ctxt1) = ml_args ctxt type_args;
        val (decls2, ctxt2) = ml_args ctxt1 term_args;
        val (decls3, ctxt3) = ml_args ctxt2 fn_body;
        fun decl' ctxt' =
          let
            val (ml_args_env1, ml_args_body1) = split_list (decls1 ctxt');
            val (ml_args_env2, ml_args_body2) = split_list (decls2 ctxt');
            val (ml_fn_env, ml_fn_body) = split_list (decls3 ctxt');

            val relevant = map is_dummy type_args ~~ type_paths;
            fun relevant_path is =
              not pattern orelse
                let val p = rev is
                in relevant |> exists (fn (u, q) => not u andalso is_prefix (op =) p q) end;

            val ml_typarg = the o AList.lookup (op =) (type_params ~~ ml_args_body1);
            fun ml_typ is (Type (d, Us)) =
                  if relevant_path is then
                    ml "Term.Type " @
                    ml_pair (ml_string d, ml_list (map_index (fn (i, U) => ml_typ (i :: is) U) Us))
                  else ml_dummy
              | ml_typ is (TVar arg) = if relevant_path is then ml_typarg arg else ml_dummy
              | ml_typ _ (TFree _) = raise Match;

            fun ml_app [] = ml "Term.Const " @ ml_pair (ml_string c, ml_typ [] T)
              | ml_app (u :: us) = ml "Term.$ " @ ml_pair (ml_app us, u);

            val ml_env = flat (ml_args_env1 @ ml_args_env2 @ ml_fn_env);
            val ml1 = ml_enclose range (ml_app (rev ml_args_body2));
            val ml2 =
              if function then
                ml_enclose range
                 (ml_range range "fn " @ ml1 @ ml "=> " @ flat ml_fn_body @
                  ml "| t => " @ ml_range range "raise" @
                  ml " Term.TERM (" @ ml_string ("Const_fn " ^ quote c) @ ml ", [t])")
              else ml1;
          in (ml_env, ml2) end;
      in (decl', ctxt3) end);

val _ = Theory.setup
 (type_antiquotation \<^binding>\<open>Type\<close> {function = false} #>
  type_antiquotation \<^binding>\<open>Type_fn\<close> {function = true} #>
  const_antiquotation \<^binding>\<open>Const\<close> {pattern = false, function = false} #>
  const_antiquotation \<^binding>\<open>Const_\<close> {pattern = true, function = false} #>
  const_antiquotation \<^binding>\<open>Const_fn\<close> {pattern = true, function = true});

in end;


(* special forms *)

val _ = Theory.setup
 (ML_Antiquotation.special_form \<^binding>\<open>try\<close> "() |> Basics.try" #>
  ML_Antiquotation.special_form \<^binding>\<open>can\<close> "() |> Basics.can");


(* basic combinators *)

local

val parameter = Parse.position Parse.nat >> (fn (n, pos) =>
  if n > 1 then n else error ("Bad parameter: " ^ string_of_int n ^ Position.here pos));

fun indices n = map string_of_int (1 upto n);

fun empty n = replicate_string n " []";
fun dummy n = replicate_string n " _";
fun vars x n = implode (map (fn a => " " ^ x ^ a) (indices n));
fun cons n = implode (map (fn a => " (x" ^ a ^ " :: xs" ^ a ^ ")") (indices n));

val tuple = enclose "(" ")" o commas;
fun tuple_empty n = tuple (replicate n "[]");
fun tuple_vars x n = tuple (map (fn a => x ^ a) (indices n));
fun tuple_cons n = "(" ^ tuple_vars "x" n ^ " :: xs)"
fun cons_tuple n = tuple (map (fn a => "x" ^ a ^ " :: xs" ^ a) (indices n));

in

val _ = Theory.setup
 (ML_Antiquotation.value \<^binding>\<open>map\<close>
    (Scan.lift parameter >> (fn n =>
      "fn f =>\n\
      \  let\n\
      \    fun map _" ^ empty n ^ " = []\n\
      \      | map f" ^ cons n ^ " = f" ^ vars "x" n ^ " :: map f" ^ vars "xs" n ^ "\n\
      \      | map _" ^  dummy n ^ " = raise ListPair.UnequalLengths\n" ^
      "  in map f end")) #>
  ML_Antiquotation.value \<^binding>\<open>fold\<close>
    (Scan.lift parameter >> (fn n =>
      "fn f =>\n\
      \  let\n\
      \    fun fold _" ^ empty n ^ " a = a\n\
      \      | fold f" ^ cons n ^ " a = fold f" ^ vars "xs" n ^ " (f" ^ vars "x" n ^ " a)\n\
      \      | fold _" ^  dummy n ^ " _ = raise ListPair.UnequalLengths\n" ^
      "  in fold f end")) #>
  ML_Antiquotation.value \<^binding>\<open>fold_map\<close>
    (Scan.lift parameter >> (fn n =>
      "fn f =>\n\
      \  let\n\
      \    fun fold_map _" ^ empty n ^ " a = ([], a)\n\
      \      | fold_map f" ^ cons n ^ " a =\n\
      \          let\n\
      \            val (x, a') = f" ^ vars "x" n ^ " a\n\
      \            val (xs, a'') = fold_map f" ^ vars "xs" n ^ " a'\n\
      \          in (x :: xs, a'') end\n\
      \      | fold_map _" ^  dummy n ^ " _ = raise ListPair.UnequalLengths\n" ^
      "  in fold_map f end")) #>
  ML_Antiquotation.value \<^binding>\<open>split_list\<close>
    (Scan.lift parameter >> (fn n =>
      "fn list =>\n\
      \  let\n\
      \    fun split_list [] =" ^ tuple_empty n ^ "\n\
      \      | split_list" ^ tuple_cons n ^ " =\n\
      \          let val" ^ tuple_vars "xs" n ^ " = split_list xs\n\
      \          in " ^ cons_tuple n ^ "end\n\
      \  in split_list list end")) #>
  ML_Antiquotation.value \<^binding>\<open>apply\<close>
    (Scan.lift (parameter -- Scan.option (Args.parens (Parse.position Parse.nat))) >>
      (fn (n, opt_index) =>
        let
          val cond =
            (case opt_index of
              NONE => K true
            | SOME (index, index_pos) =>
                if 1 <= index andalso index <= n then equal (string_of_int index)
                else error ("Bad index: " ^ string_of_int index ^ Position.here index_pos));
        in
          "fn f => fn " ^ tuple_vars "x" n ^ " => " ^
            tuple (map (fn a => (if cond a then "f x" else "x") ^ a) (indices n))
        end)));

end;


(* outer syntax *)

val _ = Theory.setup
 (ML_Antiquotation.value_embedded \<^binding>\<open>keyword\<close>
    (Args.context --
      Scan.lift (Parse.embedded_position || Parse.position (Parse.keyword_with (K true)))
      >> (fn (ctxt, (name, pos)) =>
        if Keyword.is_keyword (Thy_Header.get_keywords' ctxt) name then
          (Context_Position.report ctxt pos (Token.keyword_markup (true, Markup.keyword2) name);
           "Parse.$$$ " ^ ML_Syntax.print_string name)
        else error ("Bad outer syntax keyword " ^ quote name ^ Position.here pos))) #>
  ML_Antiquotation.value_embedded \<^binding>\<open>command_keyword\<close>
    (Args.context -- Scan.lift Parse.embedded_position >> (fn (ctxt, (name, pos)) =>
      (case Keyword.command_markup (Thy_Header.get_keywords' ctxt) name of
        SOME markup =>
         (Context_Position.reports ctxt [(pos, markup), (pos, Markup.keyword1)];
          ML_Syntax.print_pair ML_Syntax.print_string ML_Syntax.print_position (name, pos))
      | NONE => error ("Bad outer syntax command " ^ quote name ^ Position.here pos)))));

end;
