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
  val special_form: binding -> string -> theory -> theory
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

fun special_form binding operator =
  ML_Context.add_antiquotation binding true
    (fn _ => fn src => fn ctxt =>
      let
        val (s, _) = Token.syntax (Scan.lift Args.embedded_input) src ctxt;
        val tokenize = ML_Lex.tokenize_range Position.no_range;
        val tokenize_range = ML_Lex.tokenize_range (Input.range_of s);

        val (decl, ctxt') = ML_Context.expand_antiquotes (ML_Lex.read_source s) ctxt;
        fun decl' ctxt'' =
          let
            val (ml_env, ml_body) = decl ctxt'';
            val ml_body' =
              tokenize "let val expr = (fn () => " @ ml_body @ tokenize ");" @
              tokenize " val " @ tokenize_range "result" @
              tokenize (" = " ^ operator ^ " expr; in result end");
          in (ml_env, ml_body') end;
      in (decl', ctxt') end);

fun conditional binding check =
  ML_Context.add_antiquotation binding true
    (fn _ => fn src => fn ctxt =>
      let val (s, _) = Token.syntax (Scan.lift Args.embedded_input) src ctxt in
        if check ctxt then
          ML_Context.expand_antiquotes (ML_Lex.read_source s) ctxt
        else (K ([], []), ctxt)
      end);


(* basic antiquotations *)

val _ = Theory.setup
 (declaration (Binding.make ("here", \<^here>)) (Scan.succeed ())
    (fn src => fn () =>
      value_decl "position" (ML_Syntax.print_position (#2 (Token.name_of_src src)))) #>

  inline (Binding.make ("make_string", \<^here>)) (Args.context >> K ML_Pretty.make_string_fn) #>

  value_embedded (Binding.make ("binding", \<^here>))
    (Scan.lift (Parse.input Args.embedded) >> (ML_Syntax.make_binding o Input.source_content)) #>

  value_embedded (Binding.make ("cartouche", \<^here>))
    (Scan.lift Args.cartouche_input >> (fn source =>
      "Input.source true " ^ ML_Syntax.print_string (Input.text_of source) ^ " " ^
        ML_Syntax.atomic (ML_Syntax.print_range (Input.range_of source)))) #>

  inline_embedded (Binding.make ("verbatim", \<^here>))
    (Scan.lift Args.embedded >> ML_Syntax.print_string));

end;
