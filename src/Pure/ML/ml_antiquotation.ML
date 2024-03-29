(*  Title:      Pure/ML/ml_antiquotation.ML
    Author:     Makarius

ML antiquotations.
*)

signature ML_ANTIQUOTATION =
sig
  val value_decl: string -> string -> Proof.context ->
    (Proof.context -> string * string) * Proof.context
  val declaration: binding -> 'a context_parser ->
    (Token.src -> 'a -> Proof.context -> (Proof.context -> string * string) * Proof.context) ->
    theory -> theory
  val declaration_embedded: binding -> 'a context_parser ->
    (Token.src -> 'a -> Proof.context -> (Proof.context -> string * string) * Proof.context) ->
    theory -> theory
  val inline: binding -> string context_parser -> theory -> theory
  val inline_embedded: binding -> string context_parser -> theory -> theory
  val value: binding -> string context_parser -> theory -> theory
  val value_embedded: binding -> string context_parser -> theory -> theory
  val special_form: binding ->
    (Proof.context -> Input.source -> string * ML_Lex.token Antiquote.antiquote list list) ->
    theory -> theory
  val conditional: binding -> (Proof.context -> bool) -> theory -> theory
end;

structure ML_Antiquotation: ML_ANTIQUOTATION =
struct

(* define antiquotations *)

fun value_decl a s ctxt =
  let
    val (b, ctxt') = ML_Context.variant a ctxt;
    val env = "val " ^ b ^ " = " ^ s ^ ";\n";
    val body = ML_Context.struct_name ctxt ^ "." ^ b;
    fun decl (_: Proof.context) = (env, body);
  in (decl, ctxt') end;

local

fun gen_declaration name embedded scan body =
  ML_Context.add_antiquotation name embedded
    (fn range => fn src => fn orig_ctxt =>
      let
        val (x, _) = Token.syntax scan src orig_ctxt;
        val (decl, ctxt') = body src x orig_ctxt;
      in (decl #> apply2 (ML_Lex.tokenize_range range), ctxt') end);

fun gen_inline name embedded scan =
  gen_declaration name embedded scan (fn _ => fn s => fn ctxt => (K ("", s), ctxt));

fun gen_value name embedded scan =
  gen_declaration name embedded scan (fn _ => value_decl (Binding.name_of name));

in

fun declaration name = gen_declaration name false;
fun declaration_embedded name = gen_declaration name true;

fun inline name = gen_inline name false;
fun inline_embedded name = gen_inline name true;

fun value name = gen_value name false;
fun value_embedded name = gen_value name true;

end;


(* ML macros *)

fun special_form binding parse =
  ML_Context.add_antiquotation binding true
    (fn _ => fn src => fn ctxt =>
      let
        val input = Token.read ctxt Parse.embedded_input src;
        val tokenize = ML_Lex.tokenize_no_range;
        val tokenize_range = ML_Lex.tokenize_range (Input.range_of input);
        val eq = tokenize " = ";

        val (operator, sections) = parse ctxt input;
        val (decls, ctxt') = ML_Context.expand_antiquotes_list sections ctxt;
        fun decl' ctxt'' =
          let
            val (sections_env, sections_body) = split_list (decls ctxt'');
            val sections_bind =
              sections_body |> map_index (fn (i, body) =>
                let
                  val name = tokenize ("expr" ^ (if i = 0 then "" else string_of_int i));
                  val bind = if i = 0 then tokenize "val " else tokenize "and ";
                in (bind @ name @ eq @ body, name) end);
            val ml_body' =
              tokenize "let " @ maps #1 sections_bind @
              tokenize " val " @ tokenize_range "result" @ eq @
              tokenize operator @ maps #2 sections_bind @ tokenize " in result end";
          in (flat sections_env, ml_body') end;
      in (decl', ctxt') end);

fun conditional binding check =
  ML_Context.add_antiquotation binding true
    (fn _ => fn src => fn ctxt =>
      let val s = Token.read ctxt Parse.embedded_input src in
        if check ctxt then ML_Context.read_antiquotes s ctxt
        else (K ([], []), ctxt)
      end);


(* basic antiquotations *)

val _ = Theory.setup
 (declaration (Binding.make ("here", \<^here>)) (Scan.succeed ())
    (fn src => fn () =>
      value_decl "position" (ML_Syntax.print_position (#2 (Token.name_of_src src)))) #>

  inline (Binding.make ("make_string", \<^here>)) (Args.context >> K ML_Pretty.make_string_fn) #>

  value_embedded (Binding.make ("binding", \<^here>))
    (Scan.lift Parse.embedded_input >> (ML_Syntax.make_binding o Input.source_content)) #>

  value_embedded (Binding.make ("cartouche", \<^here>))
    (Scan.lift Args.cartouche_input >> (fn source =>
      "Input.source true " ^ ML_Syntax.print_string (Input.text_of source) ^ " " ^
        ML_Syntax.atomic (ML_Syntax.print_range (Input.range_of source)))) #>

  inline_embedded (Binding.make ("verbatim", \<^here>))
    (Scan.lift Parse.embedded >> ML_Syntax.print_string));

end;
