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

  datatype proof_method =
    Metis_Method of string option * string option |
    Simp_Method |
    Simp_Size_Method |
    Auto_Method |
    Fastforce_Method |
    Force_Method |
    Arith_Method |
    Blast_Method |
    Meson_Method |
    Algebra_Method

  datatype isar_proof =
    Proof of (string * typ) list * (label * term) list * isar_step list
  and isar_step =
    Let of term * term |
    Prove of isar_qualifier list * (string * typ) list * label * term * isar_proof list
      * facts * proof_method list

  val no_label : label

  val label_ord : label * label -> order
  val string_of_label : label -> string

  val string_of_proof_method : proof_method -> string

  val steps_of_isar_proof : isar_proof -> isar_step list

  val label_of_isar_step : isar_step -> label option
  val facts_of_isar_step : isar_step -> facts
  val proof_methods_of_isar_step : isar_step -> proof_method list

  val fold_isar_steps : (isar_step -> 'a -> 'a) -> isar_step list -> 'a -> 'a
  val map_isar_steps : (isar_step -> isar_step) -> isar_proof -> isar_proof
  val add_isar_steps : isar_step list -> int -> int

  structure Canonical_Label_Tab : TABLE

  val canonical_label_ord : (label * label) -> order

  val chain_isar_proof : isar_proof -> isar_proof
  val kill_useless_labels_in_isar_proof : isar_proof -> isar_proof
  val relabel_isar_proof_canonically : isar_proof -> isar_proof
  val relabel_isar_proof_finally : isar_proof -> isar_proof

  val string_of_isar_proof : Proof.context -> int -> int ->
    (label -> proof_method list -> string) -> isar_proof -> string
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

datatype proof_method =
  Metis_Method of string option * string option |
  Simp_Method |
  Simp_Size_Method |
  Auto_Method |
  Fastforce_Method |
  Force_Method |
  Arith_Method |
  Blast_Method |
  Meson_Method |
  Algebra_Method

datatype isar_proof =
  Proof of (string * typ) list * (label * term) list * isar_step list
and isar_step =
  Let of term * term |
  Prove of isar_qualifier list * (string * typ) list * label * term * isar_proof list
    * facts * proof_method list

val no_label = ("", ~1)

val label_ord = pairself swap #> prod_ord int_ord fast_string_ord

fun string_of_label (s, num) = s ^ string_of_int num

fun string_of_proof_method meth =
  (case meth of
    Metis_Method (NONE, NONE) => "metis"
  | Metis_Method (type_enc_opt, lam_trans_opt) =>
    "metis (" ^ commas (map_filter I [type_enc_opt, lam_trans_opt]) ^ ")"
  | Simp_Method => "simp"
  | Simp_Size_Method => "simp add: size_ne_size_imp_ne"
  | Auto_Method => "auto"
  | Fastforce_Method => "fastforce"
  | Force_Method => "force"
  | Arith_Method => "arith"
  | Blast_Method => "blast"
  | Meson_Method => "meson"
  | Algebra_Method => "algebra")

fun steps_of_isar_proof (Proof (_, _, steps)) = steps

fun label_of_isar_step (Prove (_, _, l, _, _, _, _)) = SOME l
  | label_of_isar_step _ = NONE

fun subproofs_of_isar_step (Prove (_, _, _, _, subs, _, _)) = subs
  | subproofs_of_isar_step _ = []

fun facts_of_isar_step (Prove (_, _, _, _, _, facts, _)) = facts
  | facts_of_isar_step _ = ([], [])

fun proof_methods_of_isar_step (Prove (_, _, _, _, _, _, meths)) = meths
  | proof_methods_of_isar_step _ = []

fun fold_isar_step f step =
  fold (steps_of_isar_proof #> fold_isar_steps f) (subproofs_of_isar_step step) #> f step
and fold_isar_steps f = fold (fold_isar_step f)

fun map_isar_steps f =
  let
    fun map_proof (Proof (fix, assms, steps)) = Proof (fix, assms, map map_step steps)
    and map_step (step as Let _) = f step
      | map_step (Prove (qs, xs, l, t, subs, facts, meths)) =
        f (Prove (qs, xs, l, t, map map_proof subs, facts, meths))
  in map_proof end

val add_isar_steps = fold_isar_steps (fn Prove _ => Integer.add 1 | _ => I)

(* canonical proof labels: 1, 2, 3, ... in post traversal order *)
fun canonical_label_ord (((_, i1), (_, i2)) : label * label) = int_ord (i1, i2)

structure Canonical_Label_Tab = Table(
  type key = label
  val ord = canonical_label_ord)

fun chain_qs_lfs NONE lfs = ([], lfs)
  | chain_qs_lfs (SOME l0) lfs =
    if member (op =) lfs l0 then ([Then], lfs |> remove (op =) l0) else ([], lfs)
fun chain_isar_step lbl (Prove (qs, xs, l, t, subs, (lfs, gfs), meths)) =
    let val (qs', lfs) = chain_qs_lfs lbl lfs in
      Prove (qs' @ qs, xs, l, t, map chain_isar_proof subs, (lfs, gfs), meths)
    end
  | chain_isar_step _ step = step
and chain_isar_steps _ [] = []
  | chain_isar_steps (prev as SOME _) (i :: is) =
    chain_isar_step prev i :: chain_isar_steps (label_of_isar_step i) is
  | chain_isar_steps _ (i :: is) = i :: chain_isar_steps (label_of_isar_step i) is
and chain_isar_proof (Proof (fix, assms, steps)) =
  Proof (fix, assms, chain_isar_steps (try (List.last #> fst) assms) steps)

fun kill_useless_labels_in_isar_proof proof =
  let
    val used_ls =
      fold_isar_steps (facts_of_isar_step #> fst #> union (op =)) (steps_of_isar_proof proof) []

    fun kill_label l = if member (op =) used_ls l then l else no_label

    fun kill_step (Prove (qs, xs, l, t, subs, facts, meths)) =
        Prove (qs, xs, kill_label l, t, map kill_proof subs, facts, meths)
      | kill_step step = step
    and kill_proof (Proof (fix, assms, steps)) =
      Proof (fix, map (apfst kill_label) assms, map kill_step steps)
  in
    kill_proof proof
  end

fun relabel_isar_proof_canonically proof =
  let
    fun next_label l (next, subst) =
      let val l' = ("", next) in (l', (next + 1, (l, l') :: subst)) end

    fun relabel_step (Prove (qs, fix, l, t, subs, (lfs, gfs), meths)) (accum as (_, subst)) =
        let
          val lfs' = maps (the_list o AList.lookup (op =) subst) lfs
          val ((subs', l'), accum') = accum
            |> fold_map relabel_proof subs
            ||>> next_label l
        in
          (Prove (qs, fix, l', t, subs', (lfs', gfs), meths), accum')
        end
      | relabel_step step accum = (step, accum)
    and relabel_proof (Proof (fix, assms, steps)) =
      fold_map (fn (l, t) => next_label l #> apfst (rpair t)) assms
      ##>> fold_map relabel_step steps
      #>> (fn (assms, steps) => Proof (fix, assms, steps))
  in
    fst (relabel_proof proof (0, []))
  end

val assume_prefix = "a"
val have_prefix = "f"

val relabel_isar_proof_finally =
  let
    fun next_label depth prefix l (accum as (next, subst)) =
      if l = no_label then
        (l, accum)
      else
        let val l' = (replicate_string (depth + 1) prefix, next) in
          (l', (next + 1, (l, l') :: subst))
        end

    fun relabel_step depth (Prove (qs, xs, l, t, subs, (lfs, gfs), meths)) (accum as (_, subst)) =
        let
          val lfs' = maps (the_list o AList.lookup (op =) subst) lfs
          val (l', accum' as (next', subst')) = next_label depth have_prefix l accum
          val subs' = map (relabel_proof subst' (depth + 1)) subs
        in
          (Prove (qs, xs, l', t, subs', (lfs', gfs), meths), accum')
        end
      | relabel_step _ step accum = (step, accum)
    and relabel_proof subst depth (Proof (fix, assms, steps)) =
      (1, subst)
      |> fold_map (fn (l, t) => next_label depth assume_prefix l #> apfst (rpair t)) assms
      ||>> fold_map (relabel_step depth) steps
      |> (fn ((assms, steps), _) => Proof (fix, assms, steps))
  in
    relabel_proof [] 0
  end

val indent_size = 2

fun string_of_isar_proof ctxt i n comment_of proof =
  let
    (* Make sure only type constraints inserted by the type annotation code are printed. *)
    val ctxt =
      ctxt |> Config.put show_markup false
           |> Config.put Printer.show_type_emphasis false
           |> Config.put show_types false
           |> Config.put show_sorts false
           |> Config.put show_consts false

    val register_fixes = map Free #> fold Variable.auto_fixes

    fun add_str s' = apfst (suffix s')

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
            |> annotate_types_in_term ctxt
            |> with_vanilla_print_mode (Syntax.unparse_term ctxt #> Pretty.string_of)
            |> simplify_spaces
            |> maybe_quote),
       ctxt |> Variable.auto_fixes term)

    fun with_facts none _ [] [] = none
      | with_facts _ some ls ss = some (space_implode " " (map string_of_label ls @ ss))

    val using_facts = with_facts "" (enclose "using " " ")

    fun maybe_paren s = s |> String.isSubstring " " s ? enclose "(" ")"
    fun by_facts meth ls ss =
      "by " ^ with_facts (maybe_paren meth) (enclose ("(" ^ meth ^ " ") ")") ls ss

    fun is_direct_method (Metis_Method _) = true
      | is_direct_method Meson_Method = true
      | is_direct_method _ = false

    (* Local facts are always passed via "using", which affects "meson" and "metis". This is
       arguably stylistically superior, because it emphasises the structure of the proof. It is also
       more robust w.r.t. preplay: Preplay is performed before chaining of local facts with "hence"
       and "thus" is introduced. See also "tac_of_method" in "Sledgehammer_Isar_Preplay". *)
    fun of_method ls ss meth =
      let val direct = is_direct_method meth in
        using_facts ls (if direct then [] else ss) ^
        by_facts (string_of_proof_method meth) [] (if direct then ss else [])
      end

    fun of_free (s, T) =
      maybe_quote s ^ " :: " ^
      maybe_quote (simplify_spaces (with_vanilla_print_mode (Syntax.string_of_typ ctxt) T))

    fun add_frees xs (s, ctxt) =
      (s ^ space_implode " and " (map of_free xs), ctxt |> register_fixes xs)

    fun add_fix _ [] = I
      | add_fix ind xs = add_str (of_indent ind ^ "fix ") #> add_frees xs #> add_str "\n"

    fun add_assm ind (l, t) =
      add_str (of_indent ind ^ "assume " ^ of_label l) #> add_term t #> add_str "\n"

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
      | of_subproofs ind ctxt qs subs =
        (if member (op =) qs Then then of_moreover ind else "") ^
        space_implode (of_moreover ind) (map (of_subproof ind ctxt) subs)
    and add_step_pre ind qs subs (s, ctxt) =
      (s ^ of_subproofs ind ctxt qs subs ^ of_indent ind, ctxt)
    and add_step ind (Let (t1, t2)) =
        add_str (of_indent ind ^ "let ")
        #> add_term t1 #> add_str " = " #> add_term t2 #> add_str "\n"
      | add_step ind (Prove (qs, xs, l, t, subs, (ls, ss), meths as meth :: _)) =
        add_step_pre ind qs subs
        #> (case xs of
             [] => add_str (of_have qs (length subs) ^ " ")
           | _ => add_str (of_obtain qs (length subs) ^ " ") #> add_frees xs #> add_str " where ")
        #> add_str (of_label l)
        #> add_term t
        #> add_str (" " ^
             of_method (sort_distinct label_ord ls) (sort_distinct string_ord ss) meth ^
             (case comment_of l meths of
               "" => ""
             | comment => " (* " ^ comment ^ " *)") ^ "\n")
    and add_steps ind = fold (add_step ind)
    and of_proof ind ctxt (Proof (xs, assms, steps)) =
      ("", ctxt)
      |> add_fix ind xs
      |> fold (add_assm ind) assms
      |> add_steps ind steps
      |> fst
  in
    (* One-step Metis proofs are pointless; better use the one-liner directly. *)
    (case proof of
      Proof ([], [], []) => "" (* degenerate case: the conjecture is "True" with Z3 *)
    | Proof ([], [], [Prove (_, [], _, _, [], _, Metis_Method _ :: _)]) => ""
    | _ =>
      (if i <> 1 then "prefer " ^ string_of_int i ^ "\n" else "") ^
      of_indent 0 ^ "proof -\n" ^ of_proof 1 ctxt proof ^
      of_indent 0 ^ (if n <> 1 then "next" else "qed"))
  end

end;
