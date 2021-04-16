(*  Title:      Pure/ML/ml_antiquotations.ML
    Author:     Makarius

Miscellaneous ML antiquotations.
*)

structure ML_Antiquotations: sig end =
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
      ML_Syntax.print_string (Thm.check_oracle ctxt (name, pos)))) #>

  ML_Antiquotation.inline_embedded \<^binding>\<open>method\<close>
    (Args.context -- Scan.lift Args.embedded_position >> (fn (ctxt, (name, pos)) =>
      ML_Syntax.print_string (Method.check_name ctxt (name, pos)))));


(* locales *)

val _ = Theory.setup
 (ML_Antiquotation.inline_embedded \<^binding>\<open>locale\<close>
   (Args.context -- Scan.lift Args.embedded_position >> (fn (ctxt, (name, pos)) =>
      Locale.check (Proof_Context.theory_of ctxt) (name, pos)
      |> ML_Syntax.print_string)));


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
    (Args.context -- Scan.lift Args.embedded_position >> (fn (ctxt, (c, pos)) =>
      if is_some (Syntax.lookup_const (Proof_Context.syn_of ctxt) c)
      then ML_Syntax.print_string c
      else error ("Unknown syntax const: " ^ quote c ^ Position.here pos))) #>

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
