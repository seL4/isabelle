(*  Title:       HOL/Tools/function_package/lexicographic_order.ML
    Author:      Lukas Bulwahn, TU Muenchen

Method for termination proofs with lexicographic orderings.
*)

signature LEXICOGRAPHIC_ORDER =
sig
  val lex_order_tac : Proof.context -> tactic -> tactic
  val lexicographic_order_tac : Proof.context -> tactic
  val lexicographic_order : Proof.context -> Proof.method

  val setup: theory -> theory
end

structure LexicographicOrder : LEXICOGRAPHIC_ORDER =
struct

open FundefLib

(** General stuff **)

fun mk_measures domT mfuns =
    let 
        val relT = HOLogic.mk_setT (HOLogic.mk_prodT (domT, domT))
        val mlexT = (domT --> HOLogic.natT) --> relT --> relT
        fun mk_ms [] = Const (@{const_name Set.empty}, relT)
          | mk_ms (f::fs) = 
            Const (@{const_name "mlex_prod"}, mlexT) $ f $ mk_ms fs
    in
        mk_ms mfuns
    end

fun del_index n [] = []
  | del_index n (x :: xs) =
    if n > 0 then x :: del_index (n - 1) xs else xs

fun transpose ([]::_) = []
  | transpose xss = map hd xss :: transpose (map tl xss)

(** Matrix cell datatype **)

datatype cell = Less of thm| LessEq of (thm * thm) | None of (thm * thm) | False of thm;

fun is_Less (Less _) = true
  | is_Less _ = false

fun is_LessEq (LessEq _) = true
  | is_LessEq _ = false

fun pr_cell (Less _ ) = " < "
  | pr_cell (LessEq _) = " <="
  | pr_cell (None _) = " ? "
  | pr_cell (False _) = " F "


(** Proof attempts to build the matrix **)

fun dest_term (t : term) =
    let
      val (vars, prop) = FundefLib.dest_all_all t
      val (prems, concl) = Logic.strip_horn prop
      val (lhs, rhs) = concl
                         |> HOLogic.dest_Trueprop
                         |> HOLogic.dest_mem |> fst
                         |> HOLogic.dest_prod
    in
      (vars, prems, lhs, rhs)
    end

fun mk_goal (vars, prems, lhs, rhs) rel =
    let
      val concl = HOLogic.mk_binrel rel (lhs, rhs) |> HOLogic.mk_Trueprop
    in
      fold_rev Logic.all vars (Logic.list_implies (prems, concl))
    end

fun prove thy solve_tac t =
    cterm_of thy t |> Goal.init
    |> SINGLE solve_tac |> the

fun mk_cell (thy : theory) solve_tac (vars, prems, lhs, rhs) mfun =
    let
      val goals = cterm_of thy o mk_goal (vars, prems, mfun $ lhs, mfun $ rhs)
    in
      case try_proof (goals @{const_name HOL.less}) solve_tac of
        Solved thm => Less thm
      | Stuck thm => 
        (case try_proof (goals @{const_name HOL.less_eq}) solve_tac of
           Solved thm2 => LessEq (thm2, thm)
         | Stuck thm2 => 
           if prems_of thm2 = [HOLogic.Trueprop $ HOLogic.false_const] then False thm2
           else None (thm2, thm)
         | _ => raise Match) (* FIXME *)
      | _ => raise Match
    end


(** Search algorithms **)

fun check_col ls = forall (fn c => is_Less c orelse is_LessEq c) ls andalso not (forall (is_LessEq) ls)

fun transform_table table col = table |> filter_out (fn x => is_Less (nth x col)) |> map (del_index col)

fun transform_order col order = map (fn x => if x >= col then x + 1 else x) order

(* simple depth-first search algorithm for the table *)
fun search_table table =
    case table of
      [] => SOME []
    | _ =>
      let
        val col = find_index (check_col) (transpose table)
      in case col of
           ~1 => NONE
         | _ =>
           let
             val order_opt = (table, col) |-> transform_table |> search_table
           in case order_opt of
                NONE => NONE
              | SOME order =>SOME (col :: transform_order col order)
           end
      end

(** Proof Reconstruction **)

(* prove row :: cell list -> tactic *)
fun prove_row (Less less_thm :: _) =
    (rtac @{thm "mlex_less"} 1)
    THEN PRIMITIVE (Thm.elim_implies less_thm)
  | prove_row (LessEq (lesseq_thm, _) :: tail) =
    (rtac @{thm "mlex_leq"} 1)
    THEN PRIMITIVE (Thm.elim_implies lesseq_thm)
    THEN prove_row tail
  | prove_row _ = sys_error "lexicographic_order"


(** Error reporting **)

fun pr_table table = writeln (cat_lines (map (fn r => concat (map pr_cell r)) table))

fun pr_goals ctxt st =
    Display.pretty_goals_aux (Syntax.pp ctxt) Markup.none (true, false) (Thm.nprems_of st) st
     |> Pretty.chunks
     |> Pretty.string_of

fun row_index i = chr (i + 97)
fun col_index j = string_of_int (j + 1)

fun pr_unprovable_cell _ ((i,j), Less _) = ""
  | pr_unprovable_cell ctxt ((i,j), LessEq (_, st)) =
      "(" ^ row_index i ^ ", " ^ col_index j ^ ", <):\n" ^ pr_goals ctxt st
  | pr_unprovable_cell ctxt ((i,j), None (st_leq, st_less)) =
      "(" ^ row_index i ^ ", " ^ col_index j ^ ", <):\n" ^ pr_goals ctxt st_less
      ^ "\n(" ^ row_index i ^ ", " ^ col_index j ^ ", <=):\n" ^ pr_goals ctxt st_leq
  | pr_unprovable_cell ctxt ((i,j), False st) =
      "(" ^ row_index i ^ ", " ^ col_index j ^ ", <):\n" ^ pr_goals ctxt st

fun pr_unprovable_subgoals ctxt table =
    table
     |> map_index (fn (i,cs) => map_index (fn (j,x) => ((i,j), x)) cs)
     |> flat
     |> map (pr_unprovable_cell ctxt)

fun no_order_msg ctxt table tl measure_funs =
    let
      val prterm = Syntax.string_of_term ctxt
      fun pr_fun t i = string_of_int i ^ ") " ^ prterm t

      fun pr_goal t i =
          let
            val (_, _, lhs, rhs) = dest_term t
          in (* also show prems? *)
               i ^ ") " ^ prterm rhs ^ " ~> " ^ prterm lhs
          end

      val gc = map (fn i => chr (i + 96)) (1 upto length table)
      val mc = 1 upto length measure_funs
      val tstr = "Result matrix:" ::  "   " ^ concat (map (enclose " " " " o string_of_int) mc)
                 :: map2 (fn r => fn i => i ^ ": " ^ concat (map pr_cell r)) table gc
      val gstr = "Calls:" :: map2 (prefix "  " oo pr_goal) tl gc
      val mstr = "Measures:" :: map2 (prefix "  " oo pr_fun) measure_funs mc
      val ustr = "Unfinished subgoals:" :: pr_unprovable_subgoals ctxt table
    in
      cat_lines (ustr @ gstr @ mstr @ tstr @ ["", "Could not find lexicographic termination order."])
    end

(** The Main Function **)

fun lex_order_tac ctxt solve_tac (st: thm) =
    let
      val thy = ProofContext.theory_of ctxt
      val ((trueprop $ (wf $ rel)) :: tl) = prems_of st

      val (domT, _) = HOLogic.dest_prodT (HOLogic.dest_setT (fastype_of rel))

      val measure_funs = MeasureFunctions.get_measure_functions ctxt domT (* 1: generate measures *)

      (* 2: create table *)
      val table = map (fn t => map (mk_cell thy solve_tac (dest_term t)) measure_funs) tl

      val order = the (search_table table) (* 3: search table *)
          handle Option => error (no_order_msg ctxt table tl measure_funs)

      val clean_table = map (fn x => map (nth x) order) table

      val relation = mk_measures domT (map (nth measure_funs) order)
      val _ = writeln ("Found termination order: " ^ quote (Syntax.string_of_term ctxt relation))

    in (* 4: proof reconstruction *)
      st |> (PRIMITIVE (cterm_instantiate [(cterm_of thy rel, cterm_of thy relation)])
              THEN (REPEAT (rtac @{thm "wf_mlex"} 1))
              THEN (rtac @{thm "wf_empty"} 1)
              THEN EVERY (map prove_row clean_table))
    end

fun lexicographic_order_tac ctxt =
  TRY (FundefCommon.apply_termination_rule ctxt 1)
  THEN lex_order_tac ctxt (auto_tac (local_clasimpset_of ctxt addsimps2 FundefCommon.TerminationSimps.get ctxt))

val lexicographic_order = SIMPLE_METHOD o lexicographic_order_tac

val setup = Method.add_methods [("lexicographic_order", Method.only_sectioned_args clasimp_modifiers lexicographic_order,
                                 "termination prover for lexicographic orderings")]
     #> Context.theory_map (FundefCommon.set_termination_prover lexicographic_order)

end;

