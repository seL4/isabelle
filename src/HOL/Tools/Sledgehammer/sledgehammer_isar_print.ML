(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_isar_print.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Steffen Juilf Smolka, TU Muenchen

Basic mapping from proof data structures to proof strings.
*)

signature SLEDGEHAMMER_ISAR_PRINT =
sig
  type isar_proof = Sledgehammer_Isar_Proof.isar_proof
  type reconstructor = Sledgehammer_Reconstructor.reconstructor
  type one_line_params = Sledgehammer_Reconstructor.one_line_params

  val string_of_reconstructor : reconstructor -> string
  val one_line_proof_text : int -> one_line_params -> string
  val string_of_proof : Proof.context -> string -> string -> int -> int -> isar_proof -> string
end;

structure Sledgehammer_Isar_Print : SLEDGEHAMMER_ISAR_PRINT =
struct

open ATP_Util
open ATP_Proof
open ATP_Problem_Generate
open ATP_Proof_Reconstruct
open Sledgehammer_Util
open Sledgehammer_Reconstructor
open Sledgehammer_Isar_Proof
open Sledgehammer_Isar_Annotate


(** reconstructors **)

fun string_of_reconstructor (Metis (type_enc, lam_trans)) = metis_call type_enc lam_trans
  | string_of_reconstructor SMT = smtN


(** one-liner reconstructor proofs **)

fun show_time NONE = ""
  | show_time (SOME ext_time) = " (" ^ string_of_ext_time ext_time ^ ")"

(* FIXME: Various bugs, esp. with "unfolding"
fun unusing_chained_facts _ 0 = ""
  | unusing_chained_facts used_chaineds num_chained =
    if length used_chaineds = num_chained then ""
    else if null used_chaineds then "(* using no facts *) "
    else "(* using only " ^ space_implode " " used_chaineds ^ " *) "
*)

fun apply_on_subgoal _ 1 = "by "
  | apply_on_subgoal 1 _ = "apply "
  | apply_on_subgoal i n =
    "prefer " ^ string_of_int i ^ " " ^ apply_on_subgoal 1 n

fun using_labels [] = ""
  | using_labels ls = "using " ^ space_implode " " (map string_of_label ls) ^ " "

fun command_call name [] =
    name |> not (Symbol_Pos.is_identifier name) ? enclose "(" ")"
  | command_call name args = "(" ^ name ^ " " ^ space_implode " " args ^ ")"

fun reconstructor_command reconstr i n used_chaineds num_chained (ls, ss) =
  (* unusing_chained_facts used_chaineds num_chained ^ *)
  using_labels ls ^ apply_on_subgoal i n ^ command_call (string_of_reconstructor reconstr) ss

fun try_command_line banner time command =
  banner ^ ": " ^
  Active.sendback_markup [Markup.padding_command] command ^
  show_time time ^ "."

fun minimize_line _ [] = ""
  | minimize_line minimize_command ss =
    (case minimize_command ss of
      "" => ""
    | command => "\nTo minimize: " ^ Active.sendback_markup [Markup.padding_command] command ^ ".")

fun split_used_facts facts =
  facts |> List.partition (fn (_, (sc, _)) => sc = Chained)
        |> pairself (sort_distinct (string_ord o pairself fst))

fun one_line_proof_text num_chained
    ((reconstr, play), banner, used_facts, minimize_command, subgoal, subgoal_count) =
  let
    val (chained, extra) = split_used_facts used_facts
    val (failed, ext_time) =
      (case play of
        Played time => (false, (SOME (false, time)))
      | Play_Timed_Out time => (false, SOME (true, time))
      | Play_Failed => (true, NONE)
      | Not_Played => (false, NONE))
    val try_line =
      ([], map fst extra)
      |> reconstructor_command reconstr subgoal subgoal_count (map fst chained) num_chained
      |> (if failed then
            enclose "One-line proof reconstruction failed: "
                     ".\n(Invoking \"sledgehammer\" with \"[strict]\" might \
                     \solve this.)"
          else
            try_command_line banner ext_time)
  in
    try_line ^ minimize_line minimize_command (map fst (extra @ chained))
  end


(** detailed Isar proofs **)

val indent_size = 2

fun string_of_proof ctxt type_enc lam_trans i n proof =
  let
    (* Make sure only type constraints inserted by the type annotation code are printed. *)
    val ctxt =
      ctxt |> Config.put show_markup false
           |> Config.put Printer.show_type_emphasis false
           |> Config.put show_types false
           |> Config.put show_sorts false
           |> Config.put show_consts false

    val register_fixes = map Free #> fold Variable.auto_fixes

    fun add_suffix suffix (s, ctxt) = (s ^ suffix, ctxt)

    fun of_indent ind = replicate_string (ind * indent_size) " "
    fun of_moreover ind = of_indent ind ^ "moreover\n"
    fun of_label l = if l = no_label then "" else string_of_label l ^ ": "

    fun of_obtain qs nr =
      (if nr > 1 orelse (nr = 1 andalso member (op =) qs Then) then
         "ultimately "
       else if nr = 1 orelse member (op =) qs Then then
         "then "
       else
         "") ^ "obtain"

    fun of_show_have qs = if member (op =) qs Show then "show" else "have"
    fun of_thus_hence qs = if member (op =) qs Show then "thus" else "hence"

    fun of_have qs nr =
      if nr > 1 orelse (nr = 1 andalso member (op =) qs Then) then
        "ultimately " ^ of_show_have qs
      else if nr = 1 orelse member (op =) qs Then then
        of_thus_hence qs
      else
        of_show_have qs

    fun add_term term (s, ctxt) =
      (s ^ (term
            |> singleton (Syntax.uncheck_terms ctxt)
            |> annotate_types ctxt
            |> with_vanilla_print_mode (Syntax.unparse_term ctxt #> Pretty.string_of)
            |> simplify_spaces
            |> maybe_quote),
       ctxt |> Variable.auto_fixes term)

    fun by_method meth = "by " ^
      (case meth of
        Simp_Method => "simp"
      | Simp_Size_Method => "(simp add: size_ne_size_imp_ne)"
      | Auto_Method => "auto"
      | Fastforce_Method => "fastforce"
      | Force_Method => "force"
      | Arith_Method => "arith"
      | Blast_Method => "blast"
      | Meson_Method => "meson"
      | _ => raise Fail "Sledgehammer_Isar_Print: by_method")

    fun with_facts none _ [] [] = none
      | with_facts _ some ls ss = some (space_implode " " (map string_of_label ls @ ss))

    val using_facts = with_facts "" (enclose "using " " ")

    (* Local facts are always passed via "using", which affects "meson" and "metis". This is
       arguably stylistically superior, because it emphasises the structure of the proof. It is also
       more robust w.r.t. preplay: Preplay is performed before chaining of local facts with "hence"
       and "thus" is introduced. See also "tac_of_method" in "Sledgehammer_Isar_Preplay". *)
    fun of_method ls ss Metis_Method =
        using_facts ls [] ^ reconstructor_command (Metis (type_enc, lam_trans)) 1 1 [] 0 ([], ss)
      | of_method ls ss Meson_Method =
        using_facts ls [] ^ with_facts "by meson" (enclose "by (meson " ")") [] ss
      | of_method ls ss meth = using_facts ls ss ^ by_method meth

    fun of_byline ind (ls, ss) meth =
      let
        val ls = ls |> sort_distinct label_ord
        val ss = ss |> sort_distinct string_ord
      in
        "\n" ^ of_indent (ind + 1) ^ of_method ls ss meth
      end

    fun of_free (s, T) =
      maybe_quote s ^ " :: " ^
      maybe_quote (simplify_spaces (with_vanilla_print_mode (Syntax.string_of_typ ctxt) T))

    fun add_frees xs (s, ctxt) =
      (s ^ space_implode " and " (map of_free xs), ctxt |> register_fixes xs)

    fun add_fix _ [] = I
      | add_fix ind xs =
        add_suffix (of_indent ind ^ "fix ")
        #> add_frees xs
        #> add_suffix "\n"

    fun add_assm ind (l, t) =
      add_suffix (of_indent ind ^ "assume " ^ of_label l)
      #> add_term t
      #> add_suffix "\n"

    fun add_assms ind assms = fold (add_assm ind) assms

    fun add_step_post ind l t facts meth =
      add_suffix (of_label l)
      #> add_term t
      #> add_suffix (of_byline ind facts meth ^ "\n")

    fun of_subproof ind ctxt proof =
      let
        val ind = ind + 1
        val s = of_proof ind ctxt proof
        val prefix = "{ "
        val suffix = " }"
      in
        replicate_string (ind * indent_size - size prefix) " " ^ prefix ^
        String.extract (s, ind * indent_size, SOME (size s - ind * indent_size - 1)) ^
        suffix ^ "\n"
      end
    and of_subproofs _ _ _ [] = ""
      | of_subproofs ind ctxt qs subproofs =
        (if member (op =) qs Then then of_moreover ind else "") ^
        space_implode (of_moreover ind) (map (of_subproof ind ctxt) subproofs)
    and add_step_pre ind qs subproofs (s, ctxt) =
      (s ^ of_subproofs ind ctxt qs subproofs ^ of_indent ind, ctxt)
    and add_step ind (Let (t1, t2)) =
        add_suffix (of_indent ind ^ "let ")
        #> add_term t1
        #> add_suffix " = "
        #> add_term t2
        #> add_suffix "\n"
      | add_step ind (Prove (qs, xs, l, t, subproofs, (facts, (meth :: _) :: _))) =
        add_step_pre ind qs subproofs
        #> (case xs of
            [] => add_suffix (of_have qs (length subproofs) ^ " ")
          | _ =>
            add_suffix (of_obtain qs (length subproofs) ^ " ")
            #> add_frees xs
            #> add_suffix " where ")
        #> add_step_post ind l t facts meth
    and add_steps ind = fold (add_step ind)
    and of_proof ind ctxt (Proof (xs, assms, steps)) =
      ("", ctxt) |> add_fix ind xs |> add_assms ind assms |> add_steps ind steps |> fst
  in
    (* One-step Metis proofs are pointless; better use the one-liner directly. *)
    (case proof of
      Proof ([], [], []) => "" (* degenerate case: the conjecture is "True" with Z3 *)
    | Proof ([], [], [Prove (_, [], _, _, [], (_, (Metis_Method :: _) :: _))]) => ""
    | _ =>
      (if i <> 1 then "prefer " ^ string_of_int i ^ "\n" else "") ^
      of_indent 0 ^ "proof -\n" ^ of_proof 1 ctxt proof ^
      of_indent 0 ^ (if n <> 1 then "next" else "qed"))
  end

end;
