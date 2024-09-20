(*  Title:      HOL/Tools/Nunchaku/nunchaku_display.ML
    Author:     Jasmin Blanchette, VU Amsterdam
    Copyright   2015, 2016, 2017

Pretty printing of Isabelle/HOL models for Nunchaku.
*)

signature NUNCHAKU_DISPLAY =
sig
  type isa_model = Nunchaku_Reconstruct.isa_model

  val pretty_of_isa_model_opt: Proof.context -> isa_model option -> Pretty.T
end;

structure Nunchaku_Display : NUNCHAKU_DISPLAY =
struct

open Nunchaku_Util;
open Nunchaku_Reconstruct;

val indent_size = 2;

val pretty_indent = Pretty.indent indent_size;

fun sorting_str_of_typ (TFree (s, _)) = "a" ^ s
  | sorting_str_of_typ (Type (s, Ts)) = "b" ^ s ^ implode_space (map sorting_str_of_typ Ts)
  | sorting_str_of_typ (TVar _) = "X";

fun sorting_str_of_term (Const (s, T)) = "b" ^ s ^ sorting_str_of_typ T
  | sorting_str_of_term (Free (s, _)) = "a" ^ s
  | sorting_str_of_term (t $ u) = sorting_str_of_term t ^ " " ^ sorting_str_of_term u
  | sorting_str_of_term (Abs (_, T, t)) = "c" ^ sorting_str_of_typ T ^ " " ^ sorting_str_of_term t
  | sorting_str_of_term _ = "X";

val basic_defs_sym = @{thms rmember_def[abs_def]};

fun fold_basic_def ctxt =
  let val thy = Proof_Context.theory_of ctxt in
    Pattern.rewrite_term thy (map (Logic.dest_equals o Thm.prop_of) basic_defs_sym) []
  end;

fun pretty_of_isa_model_opt _ NONE =
    pretty_indent (Pretty.str "Model unavailable due to internal error")
  | pretty_of_isa_model_opt ctxt0 (SOME {type_model, free_model, pat_complete_model,
      pat_incomplete_model, skolem_model, auxiliary_model}) =
    let
      val ctxt = ctxt0 |> Config.put show_question_marks false;
      fun pretty_of_typ_entry (T, atoms) =
        Pretty.block (Pretty.breaks [Syntax.pretty_typ ctxt T, Pretty.str "=",
           Pretty.enum "," "{" "}" (map (Syntax.pretty_term ctxt) atoms)]);

      fun pretty_of_term_entry (t, value) =
        let
          val no_types_ctxt = ctxt |> Config.put show_types false;
          val schematic_ctxt = ctxt |> Proof_Context.set_mode Proof_Context.mode_schematic;

          val show_types = Config.get ctxt show_types;
          val value' =
            value
            |> perhaps (try (Syntax.check_term schematic_ctxt))
            |> perhaps (try (fold_basic_def ctxt));
          val T = fastype_of t;
          val T' = if T = dummyT then try fastype_of value' |> the_default T else T;
          val t' = t |> show_types ? Type.constraint T';
        in
          Pretty.block (Pretty.breaks
            [Syntax.pretty_term ctxt t'
             |> (show_types andalso T' <> dummyT) ? (single #> Pretty.enclose "(" ")"),
             Pretty.str "=", Syntax.pretty_term no_types_ctxt value'])
        end;

      fun chunks_of_entries sorting_str_of pretty_of title entries =
        if not (null entries) then
          (if title = "" then [] else [Pretty.str (title ^ plural_s_for_list entries ^ ":")]) @
          map (pretty_indent o pretty_of) (sort_by (sorting_str_of o fst) entries)
        else
          [];

      val chunks =
        (if null free_model then
           [pretty_indent (Pretty.str "No free variables")]
         else
           chunks_of_entries sorting_str_of_term pretty_of_term_entry "" free_model) @
        chunks_of_entries sorting_str_of_term pretty_of_term_entry "Skolem constant" skolem_model @
        chunks_of_entries sorting_str_of_term pretty_of_term_entry
          "Potentially underspecified constant" pat_incomplete_model @
        chunks_of_entries sorting_str_of_term pretty_of_term_entry "Fully specified constant"
          pat_complete_model @
        chunks_of_entries sorting_str_of_term pretty_of_term_entry "Auxiliary variable"
          auxiliary_model @
        chunks_of_entries sorting_str_of_typ pretty_of_typ_entry "Type" type_model;
    in
      Pretty.chunks chunks
    end;

end;
