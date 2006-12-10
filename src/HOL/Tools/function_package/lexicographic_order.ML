(*  Title:       HOL/Tools/function_package/lexicographic_order.ML
    ID:          $Id$
    Author:      Lukas Bulwahn, TU Muenchen

Method for termination proofs with lexicographic orderings.
*)

signature LEXICOGRAPHIC_ORDER =
sig
  val lexicographic_order : Proof.context -> Method.method

  (* exported for use by size-change termination prototype.
     FIXME: provide a common interface later *)
  val mk_base_funs : typ -> term list

  val setup: theory -> theory
end

structure LexicographicOrder : LEXICOGRAPHIC_ORDER =
struct

(* Theory dependencies *)
val measures = "List.measures"
val wf_measures = thm "wf_measures"
val measures_less = thm "measures_less"
val measures_lesseq = thm "measures_lesseq"
                      
fun del_index (n, []) = []
  | del_index (n, x :: xs) =
    if n>0 then x :: del_index (n - 1, xs) else xs 

fun transpose ([]::_) = []
  | transpose xss = map hd xss :: transpose (map tl xss)

fun mk_sum_case (f1, f2) =
    case (fastype_of f1, fastype_of f2) of
      (Type("fun", [A, B]), Type("fun", [C, D])) =>
      if (B = D) then
        Const("Datatype.sum.sum_case", (A --> B) --> (C --> D) --> Type("+", [A,C]) --> B) $ f1 $ f2
      else raise TERM ("mk_sum_case: range type mismatch", [f1, f2]) 
    | _ => raise TERM ("mk_sum_case", [f1, f2])
                 
fun dest_wf (Const ("Wellfounded_Recursion.wf", _) $ t) = t
  | dest_wf t = raise TERM ("dest_wf", [t])
                      
datatype cell = Less of thm | LessEq of thm | None of thm | False of thm;
         
fun is_Less cell = case cell of (Less _) => true | _ => false  
                                                        
fun is_LessEq cell = case cell of (LessEq _) => true | _ => false
                                                            
fun thm_of_cell cell =
    case cell of 
      Less thm => thm
    | LessEq thm => thm
    | False thm => thm
    | None thm => thm
                  
fun mk_base_fun_bodys (t : term) (tt : typ) =
    case tt of
      Type("*", [ft, st]) => (mk_base_fun_bodys (Const("fst", tt --> ft) $ t) ft) @ (mk_base_fun_bodys (Const("snd", tt --> st) $ t) st)      
    | _ => [(t, tt)]
           
fun mk_base_fun_header fulltyp (t, typ) =
    if typ = HOLogic.natT then
      Abs ("x", fulltyp, t)
    else Abs ("x", fulltyp, Const("Nat.size", typ --> HOLogic.natT) $ t)
         
fun mk_base_funs (tt: typ) = 
    mk_base_fun_bodys (Bound 0) tt |>
                      map (mk_base_fun_header tt)
    
fun mk_ext_base_funs (tt : typ) =
    case tt of
      Type("+", [ft, st]) =>
      product (mk_ext_base_funs ft) (mk_ext_base_funs st)
              |> map mk_sum_case
    | _ => mk_base_funs tt
           
fun dest_term (t : term) =
    let
      val (vars, prop) = (FundefLib.dest_all_all t)
      val prems = Logic.strip_imp_prems prop
      val (tuple, rel) = Logic.strip_imp_concl prop
                         |> HOLogic.dest_Trueprop 
                         |> HOLogic.dest_mem
      val (lhs, rhs) = HOLogic.dest_prod tuple
    in
      (vars, prems, lhs, rhs, rel)
    end
    
fun mk_goal (vars, prems, lhs, rhs) rel =
    let 
      val concl = HOLogic.mk_binrel rel (lhs, rhs) |> HOLogic.mk_Trueprop
    in  
      Logic.list_implies (prems, concl) |>
                         fold_rev FundefLib.mk_forall vars
    end
    
fun prove (thy: theory) (t: term) =
    cterm_of thy t |> Goal.init 
    |> SINGLE (CLASIMPSET auto_tac) |> the
    
fun mk_cell (thy : theory) (vars, prems) (lhs, rhs) = 
    let 
      val goals = mk_goal (vars, prems, lhs, rhs) 
      val less_thm = goals "Orderings.less" |> prove thy
    in
      if Thm.no_prems less_thm then
        Less (Goal.finish less_thm)
      else
        let
          val lesseq_thm = goals "Orderings.less_eq" |> prove thy
        in
          if Thm.no_prems lesseq_thm then
            LessEq (Goal.finish lesseq_thm)
          else 
            if prems_of lesseq_thm = [HOLogic.Trueprop $ HOLogic.false_const] then False lesseq_thm
            else None lesseq_thm
        end
    end
    
fun mk_row (thy: theory) base_funs (t : term) =
    let
      val (vars, prems, lhs, rhs, _) = dest_term t
      val lhs_list = map (fn x => x $ lhs) base_funs
      val rhs_list = map (fn x => x $ rhs) base_funs
    in
      map (mk_cell thy (vars, prems)) (lhs_list ~~ rhs_list)
    end
      
(* simple depth-first search algorithm for the table *)
fun search_table table =
    case table of
      [] => SOME []
    | _ =>
      let
        val check_col = forall (fn c => is_Less c orelse is_LessEq c)
        val col = find_index (check_col) (transpose table)
      in case col of
           ~1 => NONE 
         | _ =>
           let
             val order_opt = table |> filter_out (fn x => is_Less (nth x col)) |> map (curry del_index col) |> search_table
             val transform_order = (fn col => map (fn x => if x>=col then x+1 else x))
           in case order_opt of
                NONE => NONE
              | SOME order =>SOME (col::(transform_order col order))
           end
      end
      
fun prove_row row (st : thm) =
    case row of
      [] => sys_error "INTERNAL ERROR IN lexicographic order termination tactic - fun prove_row (row is empty)" 
    | cell::tail =>
      case cell of
        Less less_thm =>
        let
          val next_thm = st |> SINGLE (rtac measures_less 1) |> the
        in
          implies_elim next_thm less_thm
        end
      | LessEq lesseq_thm =>
        let
          val next_thm = st |> SINGLE (rtac measures_lesseq 1) |> the
        in
          implies_elim next_thm lesseq_thm 
          |> prove_row tail
        end
      | _ => sys_error "INTERNAL ERROR IN lexicographic order termination tactic - fun prove_row (Only expecting Less or LessEq)"
             
fun pr_unprovable_subgoals table =
    filter (fn x => not (is_Less x) andalso not (is_LessEq x)) (flat table)
    |> map ((fn th => Pretty.string_of (Pretty.chunks (Display.pretty_goals (Thm.nprems_of th) th))) o thm_of_cell)
    
fun pr_goal thy t i = 
    let
      val (_, prems, lhs, rhs, _) = dest_term t 
      val prterm = string_of_cterm o (cterm_of thy)
    in
      (* also show prems? *)
        i ^ ") " ^ (prterm lhs) ^ " '<' " ^ (prterm rhs) 
    end
    
fun pr_fun thy t i =
    (string_of_int i) ^ ") " ^ (string_of_cterm (cterm_of thy t))
    
fun pr_cell cell = case cell of Less _ => " <  " 
                              | LessEq _ => " <= " 
                              | None _ => " N  "
                              | False _ => " F  "
                                             
(* fun pr_err: prints the table if tactic failed *)
fun pr_err table thy tl base_funs =  
    let 
      val gc = map (fn i => chr (i + 96)) (1 upto (length table))
      val mc = 1 upto (length base_funs)
      val tstr = ("   " ^ (concat (map (fn i => " " ^ (string_of_int i) ^ "  ") mc))) ::
                 (map2 (fn r => fn i => i ^ ": " ^ (concat (map pr_cell r))) table gc)
      val gstr = ("Goals:"::(map2 (pr_goal thy) tl gc))
      val mstr = ("Measures:"::(map2 (pr_fun thy) base_funs mc))   
      val ustr = ("Unfinished subgoals:"::(pr_unprovable_subgoals table))
    in
      tstr @ gstr @ mstr @ ustr
    end
      
(* the main function: create table, search table, create relation,
   and prove the subgoals *)  (* FIXME proper goal addressing -- do not hardwire 1 *)
fun lexicographic_order_tac ctxt (st: thm) = 
    let
      val thy = theory_of_thm st
      val termination_thm = the (FundefCommon.get_termination_rule ctxt)
      val next_st = SINGLE (rtac termination_thm 1) st |> the
      val premlist = prems_of next_st
    in
      case premlist of 
            [] => error "invalid number of subgoals for this tactic - expecting at least 1 subgoal" 
          | (wf::tl) => let
    val (var, prop) = FundefLib.dest_all wf
    val rel = HOLogic.dest_Trueprop prop |> dest_wf |> head_of
    val crel = cterm_of thy rel
    val base_funs = mk_ext_base_funs (fastype_of var)
    val _ = writeln "Creating table"
    val table = map (mk_row thy base_funs) tl
    val _ = writeln "Searching for lexicographic order"
    val possible_order = search_table table
      in
    case possible_order of 
        NONE => error (cat_lines ("Could not prove it by lexicographic order:"::(pr_err table thy tl base_funs)))
      | SOME order  => let
      val clean_table = map (fn x => map (nth x) order) table
      val funs = map (nth base_funs) order
      val list = HOLogic.mk_list (fastype_of var --> HOLogic.natT) funs
      val relterm = Abs ("x", fastype_of var, Const(measures, (fastype_of list) --> (range_type (fastype_of rel))) $ list)
      val crelterm = cterm_of thy relterm
      val _ = writeln ("Instantiating R with " ^ (string_of_cterm crelterm))
      val _ = writeln "Proving subgoals"
        in
      next_st |> cterm_instantiate [(crel, crelterm)]
        |> SINGLE (rtac wf_measures 1) |> the
        |> fold prove_row clean_table
        |> Seq.single
                    end
            end
    end

val lexicographic_order = Method.SIMPLE_METHOD o lexicographic_order_tac

val setup = Method.add_methods [("lexicographic_order", Method.ctxt_args lexicographic_order, "termination prover for lexicographic orderings")]

end
