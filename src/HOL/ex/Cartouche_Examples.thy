(*  Title:      HOL/ex/Cartouche_Examples.thy
    Author:     Makarius
*)

section \<open>Some examples with text cartouches\<close>

theory Cartouche_Examples
  imports Main
  keywords "cartouche" :: diag
begin

subsection \<open>Regular outer syntax\<close>

text \<open>Text cartouches may be used in the outer syntax category \<open>text\<close>,
  as alternative to the traditional \<open>verbatim\<close> tokens.  An example is
  this text block.\<close>  \<comment> \<open>The same works for small side-comments.\<close>

notepad
begin
  txt \<open>Cartouches work as additional syntax for embedded language tokens
    (types, terms, props) and as a replacement for the \<open>altstring\<close> category
    (for literal fact references). For example:\<close>

  fix x y :: 'a
  assume \<open>x = y\<close>
  note \<open>x = y\<close>
  have \<open>x = y\<close> by (rule \<open>x = y\<close>)
  from \<open>x = y\<close> have \<open>x = y\<close> .

  txt \<open>Of course, this can be nested inside formal comments and
    antiquotations, e.g. like this @{thm \<open>x = y\<close>} or this @{thm sym
    [OF \<open>x = y\<close>]}.\<close>

  have \<open>x = y\<close>
    by (tactic \<open>resolve_tac \<^context> @{thms \<open>x = y\<close>} 1\<close>)
      \<comment> \<open>more cartouches involving ML\<close>
end


subsection \<open>Outer syntax: cartouche within command syntax\<close>

ML \<open>
  Outer_Syntax.command \<^command_keyword>\<open>cartouche\<close> ""
    (Parse.cartouche >> (fn s =>
      Toplevel.keep (fn _ => writeln s)))
\<close>

cartouche \<open>abc\<close>
cartouche \<open>abc \<open>\<alpha>\<beta>\<gamma>\<close> xzy\<close>


subsection \<open>Inner syntax: string literals via cartouche\<close>

ML \<open>
  local
    fun mk_char (s, pos) =
      let
        val c =
          if Symbol.is_ascii s then ord s
          else if s = "\<newline>" then 10
          else error ("String literal contains illegal symbol: " ^ quote s ^ Position.here pos);
      in list_comb (Syntax.const \<^const_syntax>\<open>Char\<close>, String_Syntax.mk_bits_syntax 8 c) end;

    fun mk_string [] = Const (\<^const_syntax>\<open>Nil\<close>, \<^typ>\<open>string\<close>)
      | mk_string (s :: ss) =
          Syntax.const \<^const_syntax>\<open>Cons\<close> $ mk_char s $ mk_string ss;

  in
    fun string_tr content args =
      let fun err () = raise TERM ("string_tr", args) in
        (case args of
          [(c as Const (\<^syntax_const>\<open>_constrain\<close>, _)) $ Free (s, _) $ p] =>
            (case Term_Position.decode_position1 p of
              SOME pos => c $ mk_string (content (s, pos)) $ p
            | NONE => err ())
        | _ => err ())
      end;
  end;
\<close>

syntax "_cartouche_string" :: \<open>cartouche_position \<Rightarrow> string\<close>  (\<open>_\<close>)

parse_translation \<open>
  [(\<^syntax_const>\<open>_cartouche_string\<close>,
    K (string_tr (Symbol_Pos.cartouche_content o Symbol_Pos.explode)))]
\<close>

term \<open>\<open>\<close>\<close>
term \<open>\<open>abc\<close>\<close>
term \<open>\<open>abc\<close> @ \<open>xyz\<close>\<close>
term \<open>\<open>\<newline>\<close>\<close>


subsection \<open>Alternate outer and inner syntax: string literals\<close>

subsubsection \<open>Nested quotes\<close>

syntax "_string_string" :: \<open>string_position \<Rightarrow> string\<close>  (\<open>_\<close>)

parse_translation \<open>
  [(\<^syntax_const>\<open>_string_string\<close>, K (string_tr Lexicon.explode_string))]
\<close>

term \<open>""\<close>
term \<open>"abc"\<close>
term \<open>"abc" @ "xyz"\<close>
term \<open>"\<newline>"\<close>
term \<open>"\001\010\100"\<close>


subsubsection \<open>Further nesting: antiquotations\<close>

ML \<open>
  \<^term>\<open>""\<close>;
  \<^term>\<open>"abc"\<close>;
  \<^term>\<open>"abc" @ "xyz"\<close>;
  \<^term>\<open>"\<newline>"\<close>;
  \<^term>\<open>"\001\010\100"\<close>;
\<close>

text \<open>
  \<^ML>\<open>
      (
        \<^term>\<open>""\<close>;
        \<^term>\<open>"abc"\<close>;
        \<^term>\<open>"abc" @ "xyz"\<close>;
        \<^term>\<open>"\<newline>"\<close>;
        \<^term>\<open>"\001\010\100"\<close>
      )
    \<close>
\<close>


subsubsection \<open>Uniform nesting of sub-languages: document source, ML, term, string literals\<close>

text
\<open>
  \<^ML>\<open>
      (
        \<^term>\<open>""\<close>;
        \<^term>\<open>"abc"\<close>;
        \<^term>\<open>"abc" @ "xyz"\<close>;
        \<^term>\<open>"\<newline>"\<close>;
        \<^term>\<open>"\001\010\100"\<close>
      )
    \<close>
\<close>


subsection \<open>Proof method syntax: ML tactic expression\<close>

ML \<open>
structure ML_Tactic:
sig
  val set: (Proof.context -> tactic) -> Proof.context -> Proof.context
  val ml_tactic: Input.source -> Proof.context -> tactic
end =
struct
  structure Data = Proof_Data(type T = Proof.context -> tactic fun init _ = K no_tac);

  val set = Data.put;

  fun ml_tactic source ctxt =
    let
      val ctxt' = ctxt
        |> Context.proof_map (ML_Context.expression (Input.pos_of source)
          (ML_Lex.read "Theory.local_setup (ML_Tactic.set (fn ctxt: Proof.context => (" @
           ML_Lex.read_source source @ ML_Lex.read ")))"));
    in Data.get ctxt' ctxt end;
end
\<close>


subsubsection \<open>Explicit version: method with cartouche argument\<close>

method_setup ml_tactic = \<open>
  Scan.lift Args.cartouche_input
    >> (fn arg => fn ctxt => SIMPLE_METHOD (ML_Tactic.ml_tactic arg ctxt))
\<close>

lemma \<open>A \<and> B \<longrightarrow> B \<and> A\<close>
  apply (ml_tactic \<open>resolve_tac \<^context> @{thms impI} 1\<close>)
  apply (ml_tactic \<open>eresolve_tac \<^context> @{thms conjE} 1\<close>)
  apply (ml_tactic \<open>resolve_tac \<^context> @{thms conjI} 1\<close>)
  apply (ml_tactic \<open>ALLGOALS (assume_tac \<^context>)\<close>)
  done

lemma \<open>A \<and> B \<longrightarrow> B \<and> A\<close> by (ml_tactic \<open>blast_tac ctxt 1\<close>)

ML \<open>@{lemma \<open>A \<and> B \<longrightarrow> B \<and> A\<close> by (ml_tactic \<open>blast_tac ctxt 1\<close>)}\<close>

text \<open>\<^ML>\<open>@{lemma \<open>A \<and> B \<longrightarrow> B \<and> A\<close> by (ml_tactic \<open>blast_tac ctxt 1\<close>)}\<close>\<close>


subsubsection \<open>Implicit version: method with special name "cartouche" (dynamic!)\<close>

method_setup "cartouche" = \<open>
  Scan.lift Args.cartouche_input
    >> (fn arg => fn ctxt => SIMPLE_METHOD (ML_Tactic.ml_tactic arg ctxt))
\<close>

lemma \<open>A \<and> B \<longrightarrow> B \<and> A\<close>
  apply \<open>resolve_tac \<^context> @{thms impI} 1\<close>
  apply \<open>eresolve_tac \<^context> @{thms conjE} 1\<close>
  apply \<open>resolve_tac \<^context> @{thms conjI} 1\<close>
  apply \<open>ALLGOALS (assume_tac \<^context>)\<close>
  done

lemma \<open>A \<and> B \<longrightarrow> B \<and> A\<close>
  by (\<open>resolve_tac \<^context> @{thms impI} 1\<close>,
    \<open>eresolve_tac \<^context> @{thms conjE} 1\<close>,
    \<open>resolve_tac \<^context> @{thms conjI} 1\<close>,
    \<open>assume_tac \<^context> 1\<close>+)


subsection \<open>ML syntax\<close>

text \<open>Input source with position information:\<close>
ML \<open>
  val s: Input.source = \<open>abc123def456\<close>;
  Output.information ("Look here!" ^ Position.here (Input.pos_of s));

  \<open>abc123def456\<close> |> Input.source_explode |> List.app (fn (s, pos) =>
    if Symbol.is_digit s then Position.report pos Markup.ML_numeral else ());
\<close>

end
