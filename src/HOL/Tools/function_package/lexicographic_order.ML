(*  Title:       HOL/Tools/function_package/lexicographic_order.ML
    ID:          $Id$
    Author:      Lukas Bulwahn, TU Muenchen

Method for termination proofs with lexicographic orderings.
*)

signature LEXICOGRAPHIC_ORDER =
sig
  val lexicographic_order : thm list -> Proof.context -> Method.method

  (* exported for use by size-change termination prototype.
     FIXME: provide a common interface later *)
  val mk_base_funs : theory -> typ -> term list
  (* exported for debugging *)
  val setup: theory -> theory
end

structure LexicographicOrder : LEXICOGRAPHIC_ORDER =
struct

(** User-declared size functions **)

structure SizeFunsData = GenericDataFun
(
  type T = term NetRules.T;
  val empty = NetRules.init (op aconv) I
  val copy = I
  val extend = I
  fun merge _ (tab1, tab2) = NetRules.merge (tab1, tab2)
);

fun add_sfun f ctxt = 
  SizeFunsData.map (NetRules.insert (singleton (Variable.polymorphic (Context.proof_of ctxt)) f)) ctxt
val add_sfun_attr = Attrib.syntax (Args.term >> (fn f => Thm.declaration_attribute (K (add_sfun f))))

fun get_sfuns T thy =
    map_filter (fn f => SOME (Envir.subst_TVars (Type.typ_match (Sign.tsig_of thy)
                                                                (domain_type (fastype_of f), T)
                                                                Vartab.empty) 
                                                f)
                   handle Type.TYPE_MATCH => NONE)
               (NetRules.rules (SizeFunsData.get (Context.Theory thy)))

(** General stuff **)

fun mk_measures domT mfuns =
    let 
        val relT = HOLogic.mk_setT (HOLogic.mk_prodT (domT, domT))
        val mlexT = (domT --> HOLogic.natT) --> relT --> relT
        fun mk_ms [] = Const (@{const_name "{}"}, relT)
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

fun thm_of_cell (Less thm) = thm
  | thm_of_cell (LessEq (thm, _)) = thm
  | thm_of_cell (False thm) = thm
  | thm_of_cell (None (thm, _)) = thm

fun pr_cell (Less _ ) = " < "
  | pr_cell (LessEq _) = " <="
  | pr_cell (None _) = " ? "
  | pr_cell (False _) = " F "


(** Generating Measure Functions **)

fun mk_comp g f =
    let
      val fT = fastype_of f
      val gT as (Type ("fun", [xT, _])) = fastype_of g
      val comp = Abs ("f", fT, Abs ("g", gT, Abs ("x", xT, Bound 2 $ (Bound 1 $ Bound 0))))
    in
      Envir.beta_norm (comp $ f $ g)
    end

fun mk_base_funs thy (T as Type("*", [fT, sT])) = (* products *)
      map (mk_comp (Const ("fst", T --> fT))) (mk_base_funs thy fT)
    @ map (mk_comp (Const ("snd", T --> sT))) (mk_base_funs thy sT)

  | mk_base_funs thy T = (* default: size function, if available *)
    if Sorts.of_sort (Sign.classes_of thy) (T, [HOLogic.class_size])
    then (HOLogic.size_const T) :: get_sfuns T thy
    else get_sfuns T thy

fun mk_sum_case f1 f2 =
    let
      val Type ("fun", [fT, Q]) = fastype_of f1
      val Type ("fun", [sT, _]) = fastype_of f2
    in
      Const (@{const_name "Sum_Type.sum_case"}, (fT --> Q) --> (sT --> Q) --> Type("+", [fT, sT]) --> Q) $ f1 $ f2
    end

fun constant_0 T = Abs ("x", T, HOLogic.zero)
fun constant_1 T = Abs ("x", T, HOLogic.Suc_zero)

fun mk_funorder_funs (Type ("+", [fT, sT])) =
      map (fn m => mk_sum_case m (constant_0 sT)) (mk_funorder_funs fT)
    @ map (fn m => mk_sum_case (constant_0 fT) m) (mk_funorder_funs sT)
  | mk_funorder_funs T = [ constant_1 T ]

fun mk_ext_base_funs thy (Type("+", [fT, sT])) =
      map_product mk_sum_case (mk_ext_base_funs thy fT) (mk_ext_base_funs thy sT)
  | mk_ext_base_funs thy T = mk_base_funs thy T

fun mk_all_measure_funs thy (T as Type ("+", _)) =
    mk_ext_base_funs thy T @ mk_funorder_funs T
  | mk_all_measure_funs thy T = mk_base_funs thy T


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
      Logic.list_implies (prems, concl)
        |> fold_rev FundefLib.mk_forall vars
    end

fun prove thy solve_tac t =
    cterm_of thy t |> Goal.init
    |> SINGLE solve_tac |> the

fun mk_cell (thy : theory) solve_tac (vars, prems, lhs, rhs) mfun =
    let
      val goals = mk_goal (vars, prems, mfun $ lhs, mfun $ rhs)
      val less_thm = goals @{const_name HOL.less} |> prove thy solve_tac
    in
      if Thm.no_prems less_thm then
        Less (Goal.finish less_thm)
      else
        let
          val lesseq_thm = goals @{const_name HOL.less_eq} |> prove thy solve_tac
        in
          if Thm.no_prems lesseq_thm then
            LessEq (Goal.finish lesseq_thm, less_thm)
          else
            if prems_of lesseq_thm = [HOLogic.Trueprop $ HOLogic.false_const] then False lesseq_thm
            else None (lesseq_thm, less_thm)
        end
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

(* find all positions of elements in a list *)
fun find_index_list P =
    let fun find _ [] = []
          | find n (x :: xs) = if P x then n :: find (n + 1) xs else find (n + 1) xs
    in find 0 end

(* simple breadth-first search algorithm for the table *)
fun bfs_search_table nodes =
    case nodes of
      [] => sys_error "INTERNAL ERROR IN lexicographic order termination tactic - fun search_table (breadth search finished)"
    | (node::rnodes) => let
        val (order, table) = node
      in
        case table of
          [] => SOME (foldr (fn (c, order) => c :: transform_order c order) [] (rev order))
        | _ => let
            val cols = find_index_list (check_col) (transpose table)
          in
            case cols of
              [] => NONE
            | _ => let
              val newtables = map (transform_table table) cols
              val neworders = map (fn c => c :: order) cols
              val newnodes = neworders ~~ newtables
            in
              bfs_search_table (rnodes @ newnodes)
            end
          end
      end

fun nsearch_table table = bfs_search_table [([], table)]

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
  | pr_unprovable_cell ctxt ((i,j), None (st_less, st_leq)) =
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
fun lexicographic_order_tac ctxt solve_tac (st: thm) =
    let
      val thy = theory_of_thm st
      val ((trueprop $ (wf $ rel)) :: tl) = prems_of st

      val (domT, _) = HOLogic.dest_prodT (HOLogic.dest_setT (fastype_of rel))

      val measure_funs = mk_all_measure_funs thy domT (* 1: generate measures *)

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

fun lexicographic_order thms ctxt = 
    Method.SIMPLE_METHOD (TRY (FundefCommon.apply_termination_rule ctxt 1)
                          THEN lexicographic_order_tac ctxt (auto_tac (local_clasimpset_of ctxt)))

val setup = Method.add_methods [("lexicographic_order", Method.bang_sectioned_args clasimp_modifiers lexicographic_order,
                                 "termination prover for lexicographic orderings")]
    #> Attrib.add_attributes [("measure_function", add_sfun_attr, "declare custom measure function")]

end
