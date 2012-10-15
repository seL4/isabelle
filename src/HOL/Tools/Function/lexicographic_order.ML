(*  Title:       HOL/Tools/Function/lexicographic_order.ML
    Author:      Lukas Bulwahn, TU Muenchen
    Author:      Alexander Krauss, TU Muenchen

Termination proofs with lexicographic orders.
*)

signature LEXICOGRAPHIC_ORDER =
sig
  val lex_order_tac : bool -> Proof.context -> tactic -> tactic
  val lexicographic_order_tac : bool -> Proof.context -> tactic
  val setup: theory -> theory
end

structure Lexicographic_Order : LEXICOGRAPHIC_ORDER =
struct

open Function_Lib

(** General stuff **)

fun mk_measures domT mfuns =
  let
    val relT = HOLogic.mk_setT (HOLogic.mk_prodT (domT, domT))
    val mlexT = (domT --> HOLogic.natT) --> relT --> relT
    fun mk_ms [] = Const (@{const_abbrev Set.empty}, relT)
      | mk_ms (f::fs) =
        Const (@{const_name mlex_prod}, mlexT) $ f $ mk_ms fs
  in
    mk_ms mfuns
  end

fun del_index n [] = []
  | del_index n (x :: xs) =
  if n > 0 then x :: del_index (n - 1) xs else xs

fun transpose ([]::_) = []
  | transpose xss = map hd xss :: transpose (map tl xss)

(** Matrix cell datatype **)

datatype cell =
  Less of thm | LessEq of (thm * thm) | None of (thm * thm) | False of thm;

fun is_Less lcell = case Lazy.force lcell of Less _ => true | _ => false;
fun is_LessEq lcell = case Lazy.force lcell of LessEq _ => true | _ => false;


(** Proof attempts to build the matrix **)

fun dest_term t =
  let
    val (vars, prop) = Function_Lib.dest_all_all t
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

fun mk_cell thy solve_tac (vars, prems, lhs, rhs) mfun = Lazy.lazy (fn _ =>
  let
    val goals = cterm_of thy o mk_goal (vars, prems, mfun $ lhs, mfun $ rhs)
  in
    case try_proof (goals @{const_name Orderings.less}) solve_tac of
      Solved thm => Less thm
    | Stuck thm =>
      (case try_proof (goals @{const_name Orderings.less_eq}) solve_tac of
         Solved thm2 => LessEq (thm2, thm)
       | Stuck thm2 =>
         if prems_of thm2 = [HOLogic.Trueprop $ @{term False}] then False thm2
         else None (thm2, thm)
       | _ => raise Match) (* FIXME *)
    | _ => raise Match
  end);


(** Search algorithms **)

fun check_col ls = forall (fn c => is_Less c orelse is_LessEq c) ls andalso not (forall is_LessEq ls)

fun transform_table table col = table |> filter_out (fn x => is_Less (nth x col)) |> map (del_index col)

fun transform_order col order = map (fn x => if x >= col then x + 1 else x) order

(* simple depth-first search algorithm for the table *)
fun search_table [] = SOME []
  | search_table table =
    case find_index check_col (transpose table) of
       ~1 => NONE
     | col =>
         (case (table, col) |-> transform_table |> search_table of
            NONE => NONE
          | SOME order => SOME (col :: transform_order col order))


(** Proof Reconstruction **)

fun prove_row (c :: cs) =
  (case Lazy.force c of
     Less thm =>
       rtac @{thm "mlex_less"} 1
       THEN PRIMITIVE (Thm.elim_implies thm)
   | LessEq (thm, _) =>
       rtac @{thm "mlex_leq"} 1
       THEN PRIMITIVE (Thm.elim_implies thm)
       THEN prove_row cs
   | _ => raise General.Fail "lexicographic_order")
 | prove_row [] = no_tac;


(** Error reporting **)

fun pr_goals ctxt st =
  Pretty.string_of
    (Goal_Display.pretty_goal
      {main = Config.get ctxt Goal_Display.show_main_goal, limit = false} ctxt st)

fun row_index i = chr (i + 97)  (* FIXME not scalable wrt. chr range *)
fun col_index j = string_of_int (j + 1)  (* FIXME not scalable wrt. table layout *)

fun pr_unprovable_cell _ ((i,j), Less _) = []
  | pr_unprovable_cell ctxt ((i,j), LessEq (_, st)) =
      ["(" ^ row_index i ^ ", " ^ col_index j ^ ", <):\n" ^ pr_goals ctxt st]
  | pr_unprovable_cell ctxt ((i,j), None (st_leq, st_less)) =
      ["(" ^ row_index i ^ ", " ^ col_index j ^ ", <):\n" ^ pr_goals ctxt st_less ^
       "\n(" ^ row_index i ^ ", " ^ col_index j ^ ", <=):\n" ^ pr_goals ctxt st_leq]
  | pr_unprovable_cell ctxt ((i,j), False st) =
      ["(" ^ row_index i ^ ", " ^ col_index j ^ ", <):\n" ^ pr_goals ctxt st]

fun pr_unprovable_subgoals ctxt table =
  table
  |> map_index (fn (i,cs) => map_index (fn (j,x) => ((i,j), x)) cs)
  |> flat
  |> maps (pr_unprovable_cell ctxt)

fun pr_cell (Less _ ) = " < "
  | pr_cell (LessEq _) = " <="
  | pr_cell (None _) = " ? "
  | pr_cell (False _) = " F "

fun no_order_msg ctxt ltable tl measure_funs =
  let
    val table = map (map Lazy.force) ltable
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
    val tstr = "Result matrix:" ::  ("   " ^ implode (map (enclose " " " " o string_of_int) mc))
      :: map2 (fn r => fn i => i ^ ": " ^ implode (map pr_cell r)) table gc
    val gstr = "Calls:" :: map2 (prefix "  " oo pr_goal) tl gc
    val mstr = "Measures:" :: map2 (prefix "  " oo pr_fun) measure_funs mc
    val ustr = "Unfinished subgoals:" :: pr_unprovable_subgoals ctxt table
  in
    cat_lines (ustr @ gstr @ mstr @ tstr @
    ["", "Could not find lexicographic termination order."])
  end

(** The Main Function **)

fun lex_order_tac quiet ctxt solve_tac (st: thm) =
  let
    val thy = Proof_Context.theory_of ctxt
    val ((_ $ (_ $ rel)) :: tl) = prems_of st

    val (domT, _) = HOLogic.dest_prodT (HOLogic.dest_setT (fastype_of rel))

    val measure_funs = (* 1: generate measures *)
      MeasureFunctions.get_measure_functions ctxt domT

    val table = (* 2: create table *)
      map (fn t => map (mk_cell thy solve_tac (dest_term t)) measure_funs) tl
  in
    case search_table table of
      NONE => if quiet then no_tac st else error (no_order_msg ctxt table tl measure_funs)
    | SOME order =>
      let
        val clean_table = map (fn x => map (nth x) order) table
        val relation = mk_measures domT (map (nth measure_funs) order)
        val _ =
          if not quiet then
            Pretty.writeln (Pretty.block
              [Pretty.str "Found termination order:", Pretty.brk 1,
                Pretty.quote (Syntax.pretty_term ctxt relation)])
          else ()

      in (* 4: proof reconstruction *)
        st |> (PRIMITIVE (cterm_instantiate [(cterm_of thy rel, cterm_of thy relation)])
        THEN (REPEAT (rtac @{thm "wf_mlex"} 1))
        THEN (rtac @{thm "wf_empty"} 1)
        THEN EVERY (map prove_row clean_table))
      end
  end

fun lexicographic_order_tac quiet ctxt =
  TRY (Function_Common.apply_termination_rule ctxt 1) THEN
  lex_order_tac quiet ctxt
    (auto_tac (map_simpset (fn ss => ss addsimps Function_Common.Termination_Simps.get ctxt) ctxt))

val setup =
  Context.theory_map (Function_Common.set_termination_prover (lexicographic_order_tac false))

end;
