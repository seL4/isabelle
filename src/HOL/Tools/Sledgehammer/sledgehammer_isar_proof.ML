(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_isar_proof.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Steffen Juilf Smolka, TU Muenchen

Basic data structures for representing and basic methods
for dealing with Isar proof texts.
*)

signature SLEDGEHAMMER_ISAR_PROOF =
sig
  type label = string * int
  type facts = label list * string list (* local and global facts *)

  datatype isar_qualifier = Show | Then

  datatype isar_proof =
    Proof of (string * typ) list * (label * term) list * isar_step list
  and isar_step =
    Let of term * term |
    Prove of isar_qualifier list * (string * typ) list * label * term * isar_proof list *
      (facts * proof_method list list)
  and proof_method =
    Metis_Method | Simp_Method | Simp_Size_Method | Auto_Method | Fastforce_Method | Force_Method |
    Arith_Method | Blast_Method | Meson_Method

  val no_label : label
  val no_facts : facts

  val label_ord : label * label -> order
  val string_of_label : label -> string

  val steps_of_proof : isar_proof -> isar_step list

  val label_of_step : isar_step -> label option
  val byline_of_step : isar_step -> (facts * proof_method list list) option

  val fold_isar_steps : (isar_step -> 'a -> 'a) -> isar_step list -> 'a -> 'a
  val map_isar_steps : (isar_step -> isar_step) -> isar_proof -> isar_proof
  val add_isar_steps : isar_step list -> int -> int

  structure Canonical_Label_Tab : TABLE

  (** canonical proof labels: 1, 2, 3, ... in postorder **)
  val canonical_label_ord : (label * label) -> order
  val relabel_proof_canonically : isar_proof -> isar_proof

  val string_of_proof : Proof.context -> string -> string -> int -> int -> isar_proof -> string
end;

structure Sledgehammer_Isar_Proof : SLEDGEHAMMER_ISAR_PROOF =
struct

open ATP_Util
open ATP_Proof
open ATP_Problem_Generate
open ATP_Proof_Reconstruct
open Sledgehammer_Util
open Sledgehammer_Reconstructor
open Sledgehammer_Isar_Annotate

type label = string * int
type facts = label list * string list (* local and global facts *)

datatype isar_qualifier = Show | Then

datatype isar_proof =
  Proof of (string * typ) list * (label * term) list * isar_step list
and isar_step =
  Let of term * term |
  Prove of isar_qualifier list * (string * typ) list * label * term * isar_proof list *
    (facts * proof_method list list)
and proof_method =
  Metis_Method | Simp_Method | Simp_Size_Method | Auto_Method | Fastforce_Method | Force_Method |
  Arith_Method | Blast_Method | Meson_Method

val no_label = ("", ~1)
val no_facts = ([],[])

val label_ord = pairself swap #> prod_ord int_ord fast_string_ord

fun string_of_label (s, num) = s ^ string_of_int num

fun steps_of_proof (Proof (_, _, steps)) = steps

fun label_of_step (Prove (_, _, l, _, _, _)) = SOME l
  | label_of_step _ = NONE

fun subproofs_of_step (Prove (_, _, _, _, subproofs, _)) = SOME subproofs
  | subproofs_of_step _ = NONE

fun byline_of_step (Prove (_, _, _, _, _, byline)) = SOME byline
  | byline_of_step _ = NONE

fun fold_isar_step f step =
  fold (steps_of_proof #> fold_isar_steps f) (these (subproofs_of_step step)) #> f step
and fold_isar_steps f = fold (fold_isar_step f)

fun map_isar_steps f =
  let
    fun map_proof (Proof (fix, assms, steps)) = Proof (fix, assms, map map_step steps)
    and map_step (step as Let _) = f step
      | map_step (Prove (qs, xs, l, t, subproofs, by)) =
        f (Prove (qs, xs, l, t, map map_proof subproofs, by))
  in map_proof end

val add_isar_steps = fold_isar_steps (fn Prove _ => Integer.add 1 | _ => I)

(* canonical proof labels: 1, 2, 3, ... in post traversal order *)
fun canonical_label_ord (((_, i1), (_, i2)) : label * label) = int_ord (i1, i2)

structure Canonical_Label_Tab = Table(
  type key = label
  val ord = canonical_label_ord)

fun relabel_proof_canonically proof =
  let
    fun next_label l (next, subst) =
      let val l' = ("", next) in (l', (next + 1, (l, l') :: subst)) end

    fun do_byline by (_, subst) = apfst (apfst (map (AList.lookup (op =) subst #> the))) by
    handle Option.Option =>
      raise Fail "Sledgehammer_Isar_Proof: relabel_proof_canonically"

    fun do_assm (l, t) state =
      let
        val (l, state) = next_label l state
      in ((l, t), state) end

    fun do_proof (Proof (fix, assms, steps)) state =
      let
        val (assms, state) = fold_map do_assm assms state
        val (steps, state) = fold_map do_step steps state
      in
        (Proof (fix, assms, steps), state)
      end

    and do_step (step as Let _) state = (step, state)
      | do_step (Prove (qs, fix, l, t, subproofs, by)) state=
        let
          val by = do_byline by state
          val (subproofs, state) = fold_map do_proof subproofs state
          val (l, state) = next_label l state
        in
          (Prove (qs, fix, l, t, subproofs, by), state)
        end
  in
    fst (do_proof proof (0, []))
  end

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
      (if nr > 1 orelse (nr = 1 andalso member (op =) qs Then) then "ultimately "
       else if nr = 1 orelse member (op =) qs Then then "then "
       else "") ^ "obtain"

    fun of_show_have qs = if member (op =) qs Show then "show" else "have"
    fun of_thus_hence qs = if member (op =) qs Show then "thus" else "hence"

    fun of_have qs nr =
      if nr > 1 orelse (nr = 1 andalso member (op =) qs Then) then "ultimately " ^ of_show_have qs
      else if nr = 1 orelse member (op =) qs Then then of_thus_hence qs
      else of_show_have qs

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
    fun by_facts meth ls ss = "by " ^ with_facts meth (enclose ("by (" ^ meth) ")") ls ss

    (* Local facts are always passed via "using", which affects "meson" and "metis". This is
       arguably stylistically superior, because it emphasises the structure of the proof. It is also
       more robust w.r.t. preplay: Preplay is performed before chaining of local facts with "hence"
       and "thus" is introduced. See also "tac_of_method" in "Sledgehammer_Isar_Preplay". *)
    fun of_method ls ss Metis_Method =
        using_facts ls [] ^ by_facts (metis_call type_enc lam_trans) [] ss
      | of_method ls ss Meson_Method = using_facts ls [] ^ by_facts "meson" [] ss
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
