(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_proof.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Steffen Juilf Smolka, TU Muenchen

Basic data structures for representing and basic methods
for dealing with Isar proof texts.
*)

signature SLEDGEHAMMER_PROOF =
sig
  type label = string * int
  type facts = label list * string list (* local & global facts *)

  datatype isar_qualifier = Show | Then

  datatype fix = Fix of (string * typ) list
  datatype assms = Assume of (label * term) list

  datatype isar_proof =
    Proof of fix * assms * isar_step list
  and isar_step =
    Let of term * term |
    (* for |fix|>0, this is an obtain step; step may contain subproofs *)
    Prove of isar_qualifier list * fix * label * term * isar_proof list * byline
  and byline =
    By of facts * proof_method
  and proof_method =
    MetisM |
    SimpM |
    AutoM |
    FastforceM |
    ForceM |
    ArithM |
    BlastM

  val no_label : label
  val no_facts : facts

  val label_ord : label * label -> order

  val dummy_isar_step : isar_step

  val string_of_label : label -> string

  val fix_of_proof : isar_proof -> fix
  val assms_of_proof : isar_proof -> assms
  val steps_of_proof : isar_proof -> isar_step list

  val label_of_step : isar_step -> label option
  val subproofs_of_step : isar_step -> isar_proof list option
  val byline_of_step : isar_step -> byline option
  val proof_method_of_step : isar_step -> proof_method option

  val fold_isar_step : (isar_step -> 'a -> 'a) -> isar_step -> 'a -> 'a
  val fold_isar_steps :
    (isar_step -> 'a -> 'a) -> isar_step list -> 'a -> 'a

  val map_isar_steps : (isar_step -> isar_step) -> isar_proof -> isar_proof

  val map_facts_of_byline : (facts -> facts) -> byline -> byline

  val add_proof_steps : isar_step list -> int -> int

  (** canonical proof labels: 1, 2, 3, ... in postorder **)
  val canonical_label_ord : (label * label) -> order
  val relabel_proof_canonically : isar_proof -> isar_proof

  structure Canonical_Lbl_Tab : TABLE

end;

structure Sledgehammer_Proof : SLEDGEHAMMER_PROOF =
struct

type label = string * int
type facts = label list * string list (* local and global facts *)

datatype isar_qualifier = Show | Then

datatype fix = Fix of (string * typ) list
datatype assms = Assume of (label * term) list

datatype isar_proof =
  Proof of fix * assms * isar_step list
and isar_step =
  Let of term * term |
  (* for |fix|>0, this is an obtain step; step may contain subproofs *)
  Prove of isar_qualifier list * fix * label * term * isar_proof list * byline
and byline =
  By of facts * proof_method
and proof_method =
  MetisM |
  SimpM |
  AutoM |
  FastforceM |
  ForceM |
  ArithM |
  BlastM

val no_label = ("", ~1)
val no_facts = ([],[])

val label_ord = pairself swap #> prod_ord int_ord fast_string_ord

val dummy_isar_step = Let (Term.dummy, Term.dummy)

fun string_of_label (s, num) = s ^ string_of_int num

fun fix_of_proof (Proof (fix, _, _)) = fix
fun assms_of_proof (Proof (_, assms, _)) = assms
fun steps_of_proof (Proof (_, _, steps)) = steps

fun label_of_step (Prove (_, _, l, _, _, _)) = SOME l
  | label_of_step _ = NONE

fun subproofs_of_step (Prove (_, _, _, _, subproofs, _)) = SOME subproofs
  | subproofs_of_step _ = NONE

fun byline_of_step (Prove (_, _, _, _, _, byline)) = SOME byline
  | byline_of_step _ = NONE

fun proof_method_of_step (Prove (_, _, _, _, _, By(_, method))) = SOME method
  | proof_method_of_step _ = NONE

fun fold_isar_steps f = fold (fold_isar_step f)
and fold_isar_step f step s =
  fold (steps_of_proof #> fold_isar_steps f)
       (these (subproofs_of_step step)) s
    |> f step

fun map_isar_steps f proof =
  let
    fun do_proof (Proof (fix, assms, steps)) =
      Proof (fix, assms, map do_step steps)

    and do_step (step as Let _) = f step
      | do_step (Prove (qs, xs, l, t, subproofs, by)) =
          let
            val subproofs = map do_proof subproofs
            val step = Prove (qs, xs, l, t, subproofs, by)
          in
            f step
          end
  in
    do_proof proof
  end

fun map_facts_of_byline f (By (facts, method)) = By (f facts, method)

val add_proof_steps = fold_isar_steps (fn Prove _ => Integer.add 1 | _ => I)


(** canonical proof labels: 1, 2, 3, ... in post traversal order **)

fun canonical_label_ord (((_, i1), (_, i2)) : label * label) = int_ord (i1, i2)

structure Canonical_Lbl_Tab = Table(
  type key = label
  val ord = canonical_label_ord)

fun relabel_proof_canonically proof =
  let
    fun next_label l (next, subst) =
      let val l' = ("", next) in (l', (next + 1, (l, l') :: subst)) end

    fun do_byline by (_, subst) =
      by |> map_facts_of_byline (apfst (map (AList.lookup (op =) subst #> the)))
    handle Option.Option =>
      raise Fail "Sledgehammer_Proof: relabel_proof_canonically"

    fun do_assm (l, t) state =
      let
        val (l, state) = next_label l state
      in ((l, t), state) end

    fun do_proof (Proof (fix, Assume assms, steps)) state =
      let
        val (assms, state) = fold_map do_assm assms state
        val (steps, state) = fold_map do_step steps state
      in
        (Proof (fix, Assume assms, steps), state)
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

end;
