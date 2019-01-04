(*  Title:      Pure/ML/ml_antiquotation.ML
    Author:     Makarius

ML antiquotations.
*)

signature ML_ANTIQUOTATION =
sig
  val declaration: binding -> 'a context_parser ->
    (Token.src -> 'a -> Proof.context -> ML_Context.decl * Proof.context) ->
    theory -> theory
  val declaration_embedded: binding -> 'a context_parser ->
    (Token.src -> 'a -> Proof.context -> ML_Context.decl * Proof.context) ->
    theory -> theory
  val inline: binding -> string context_parser -> theory -> theory
  val inline_embedded: binding -> string context_parser -> theory -> theory
  val value: binding -> string context_parser -> theory -> theory
  val value_embedded: binding -> string context_parser -> theory -> theory
end;

structure ML_Antiquotation: ML_ANTIQUOTATION =
struct

(* define antiquotations *)

local

fun gen_declaration name embedded scan body =
  ML_Context.add_antiquotation name embedded
    (fn src => fn orig_ctxt =>
      let val (x, _) = Token.syntax scan src orig_ctxt
      in body src x orig_ctxt end);

fun gen_inline name embedded scan =
  gen_declaration name embedded scan (fn _ => fn s => fn ctxt => (K ("", s), ctxt));

fun gen_value name embedded scan =
  gen_declaration name embedded scan (fn _ => ML_Context.value_decl (Binding.name_of name));

in

fun declaration name = gen_declaration name false;
fun declaration_embedded name = gen_declaration name true;

fun inline name = gen_inline name false;
fun inline_embedded name = gen_inline name true;

fun value name = gen_value name false;
fun value_embedded name = gen_value name true;

end;


(* basic antiquotations *)

val _ = Theory.setup
 (declaration (Binding.make ("here", \<^here>)) (Scan.succeed ())
    (fn src => fn () =>
      ML_Context.value_decl "position" (ML_Syntax.print_position (#2 (Token.name_of_src src)))) #>

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
