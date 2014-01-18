header {* Some examples with text cartouches *}

theory Cartouche_Examples
imports Main
keywords "cartouche" :: diag
begin

subsection {* Outer syntax *}

ML {*
  Outer_Syntax.improper_command @{command_spec "cartouche"} ""
    (Parse.cartouche >> (fn s =>
      Toplevel.imperative (fn () => writeln s)))
*}

cartouche \<open>abc\<close>
cartouche \<open>abc \<open>\<alpha>\<beta>\<gamma>\<close> xzy\<close>


subsection {* Inner syntax *}

syntax "_string_cartouche" :: "cartouche_position \<Rightarrow> string"  ("STR _")

parse_translation {*
  let
    val mk_nib =
      Syntax.const o Lexicon.mark_const o
        fst o Term.dest_Const o HOLogic.mk_nibble;

    fun mk_char (s, pos) =
      let
        val c =
          if Symbol.is_ascii s then ord s
          else if s = "" then 10
          else error ("String literal contains illegal symbol: " ^ quote s ^ Position.here pos);
      in Syntax.const @{const_syntax Char} $ mk_nib (c div 16) $ mk_nib (c mod 16) end;

    fun mk_string [] = Const (@{const_syntax Nil}, @{typ string})
      | mk_string (s :: ss) =
          Syntax.const @{const_syntax Cons} $ mk_char s $ mk_string ss;

    fun string_tr ctxt args =
      let fun err () = raise TERM ("string_tr", []) in
        (case args of
          [(c as Const (@{syntax_const "_constrain"}, _)) $ Free (s, _) $ p] =>
            (case Term_Position.decode_position p of
              SOME (pos, _) =>
                c $ mk_string (Symbol_Pos.cartouche_content (Symbol_Pos.explode (s, pos))) $ p
            | NONE => err ())
        | _ => err ())
      end;
  in
    [(@{syntax_const "_string_cartouche"}, string_tr)]
  end
*}

term "STR \<open>\<close>"
term "STR \<open>abc\<close>"
lemma "STR \<open>abc\<close> @ STR \<open>xyz\<close> = STR \<open>abcxyz\<close>" by simp

end
