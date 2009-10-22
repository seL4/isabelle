(*  Title:      HOL/SizeChange/sct.ML
    Author:     Alexander Krauss, TU Muenchen

Tactics for size change termination.
*)
signature SCT =
sig
  val abs_rel_tac : tactic
  val mk_call_graph : Proof.context -> tactic
end

structure Sct : SCT =
struct

fun matrix [] ys = []
  | matrix (x::xs) ys = map (pair x) ys :: matrix xs ys

fun map_matrix f xss = map (map f) xss

val scgT = @{typ "nat scg"}
val acgT = @{typ "nat acg"}

fun edgeT nT eT = HOLogic.mk_prodT (nT, HOLogic.mk_prodT (eT, nT))
fun graphT nT eT = Type ("Graphs.graph", [nT, eT])

fun graph_const nT eT = Const ("Graphs.graph.Graph", HOLogic.mk_setT (edgeT nT eT) --> graphT nT eT)

val stepP_const = "Interpretation.stepP"
val stepP_def = thm "Interpretation.stepP.simps"

fun mk_stepP RD1 RD2 M1 M2 Rel =
    let val RDT = fastype_of RD1
      val MT = fastype_of M1
    in
      Const (stepP_const, RDT --> RDT --> MT --> MT --> (fastype_of Rel) --> HOLogic.boolT)
            $ RD1 $ RD2 $ M1 $ M2 $ Rel
    end

val no_stepI = thm "Interpretation.no_stepI"

val approx_const = "Interpretation.approx"
val approx_empty = thm "Interpretation.approx_empty"
val approx_less = thm "Interpretation.approx_less"
val approx_leq = thm "Interpretation.approx_leq"

fun mk_approx G RD1 RD2 Ms1 Ms2 =
    let val RDT = fastype_of RD1
      val MsT = fastype_of Ms1
    in Const (approx_const, scgT --> RDT --> RDT --> MsT --> MsT --> HOLogic.boolT) $ G $ RD1 $ RD2 $ Ms1 $ Ms2 end

val sound_int_const = "Interpretation.sound_int"
val sound_int_def = thm "Interpretation.sound_int_def"
fun mk_sound_int A RDs M =
    let val RDsT = fastype_of RDs
      val MT = fastype_of M
    in Const (sound_int_const, acgT --> RDsT --> MT --> HOLogic.boolT) $ A $ RDs $ M end


val nth_const = "List.nth"
fun mk_nth xs =
    let val lT as Type (_, [T]) = fastype_of xs
    in Const (nth_const, lT --> HOLogic.natT --> T) $ xs end


val has_edge_simps = [thm "Graphs.has_edge_def", thm "Graphs.dest_graph.simps"]

val all_less_zero = thm "Interpretation.all_less_zero"
val all_less_Suc = thm "Interpretation.all_less_Suc"

(* --> Library? *)
fun del_index n [] = []
  | del_index n (x :: xs) =
    if n>0 then x :: del_index (n - 1) xs else xs

(* Lists as finite multisets *)

fun remove1 eq x [] = []
  | remove1 eq x (y :: ys) = if eq (x, y) then ys else y :: remove1 eq x ys

fun multi_union eq [] ys = ys
  | multi_union eq (x::xs) ys = x :: multi_union eq xs (remove1 eq x ys)

fun dest_ex (Const ("Ex", _) $ Abs (a as (_,T,_))) =
    let
      val (n, body) = Term.dest_abs a
    in
      (Free (n, T), body)
    end
  | dest_ex _ = raise Match

fun dest_all_ex (t as (Const ("Ex",_) $ _)) =
    let
      val (v,b) = dest_ex t
      val (vs, b') = dest_all_ex b
    in
      (v :: vs, b')
    end
  | dest_all_ex t = ([],t)

fun dist_vars [] vs = (null vs orelse error "dist_vars"; [])
  | dist_vars (T::Ts) vs =
    case find_index (fn v => fastype_of v = T) vs of
      ~1 => Free ("", T) :: dist_vars Ts vs
    |  i => (nth vs i) :: dist_vars Ts (del_index i vs)

fun dest_case rebind t =
    let
      val ((_ $ _ $ rhs) :: (_ $ _ $ match) :: guards) = HOLogic.dest_conj t
      val guard = case guards of [] => HOLogic.true_const | gs => foldr1 HOLogic.mk_conj gs
    in
      foldr1 HOLogic.mk_prod [rebind guard, rebind rhs, rebind match]
    end

fun bind_many [] = I
  | bind_many vs = FundefLib.tupled_lambda (foldr1 HOLogic.mk_prod vs)

(* Builds relation descriptions from a relation definition *)
fun mk_reldescs (Abs a) =
    let
      val (_, Abs a') = Term.dest_abs a
      val (_, b) = Term.dest_abs a'
      val cases = HOLogic.dest_disj b
      val (vss, bs) = split_list (map dest_all_ex cases)
      val unionTs = fold (multi_union (op =)) (map (map fastype_of) vss) []
      val rebind = map (bind_many o dist_vars unionTs) vss

      val RDs = map2 dest_case rebind bs
    in
      HOLogic.mk_list (fastype_of (hd RDs)) RDs
    end

fun abs_rel_tac (st : thm) =
    let
      val thy = theory_of_thm st
      val (def, rd) = HOLogic.dest_eq (HOLogic.dest_Trueprop (hd (prems_of st)))
      val RDs = cterm_of thy (mk_reldescs def)
      val rdvar = Var (the_single (Term.add_vars rd [])) |> cterm_of thy
    in
      Seq.single (cterm_instantiate [(rdvar, RDs)] st)
    end






(* very primitive *)
fun measures_of ctxt RD =
    let
      val domT = range_type (fastype_of (fst (HOLogic.dest_prod (snd (HOLogic.dest_prod RD)))))
      val measures = MeasureFunctions.get_measure_functions ctxt domT
    in
      measures
    end

val mk_number = HOLogic.mk_nat
val dest_number = HOLogic.dest_nat

fun nums_to i = map_range mk_number i

val nth_simps = [@{thm List.nth_Cons_0}, @{thm List.nth_Cons_Suc}]
val nth_ss = (HOL_basic_ss addsimps nth_simps)
val simp_nth_tac = simp_tac nth_ss


fun tabulate_tlist thy l =
    let
      val n = length (HOLogic.dest_list l)
      val table = Inttab.make (map_range (fn i => (i, Simplifier.rewrite nth_ss (cterm_of thy (mk_nth l $ mk_number i)))) n)
    in
      the o Inttab.lookup table
    end

val get_elem = snd o Logic.dest_equals o prop_of

fun inst_nums thy i j (t:thm) =
  instantiate' [] [NONE, NONE, NONE, SOME (cterm_of thy (mk_number i)), NONE, SOME (cterm_of thy (mk_number j))] t

datatype call_fact =
   NoStep of thm
 | Graph of (term * thm)

fun rand (_ $ t) = t

fun setup_probe_goal ctxt domT Dtab Mtab (i, j) =
    let
      val css = clasimpset_of ctxt
      val thy = ProofContext.theory_of ctxt
      val RD1 = get_elem (Dtab i)
      val RD2 = get_elem (Dtab j)
      val Ms1 = get_elem (Mtab i)
      val Ms2 = get_elem (Mtab j)

      val Mst1 = HOLogic.dest_list (rand Ms1)
      val Mst2 = HOLogic.dest_list (rand Ms2)

      val mvar1 = Free ("sctmfv1", domT --> HOLogic.natT)
      val mvar2 = Free ("sctmfv2", domT --> HOLogic.natT)
      val relvar = Free ("sctmfrel", HOLogic.natT --> HOLogic.natT --> HOLogic.boolT)
      val N = length Mst1 and M = length Mst2
      val saved_state = HOLogic.mk_Trueprop (mk_stepP RD1 RD2 mvar1 mvar2 relvar)
                         |> cterm_of thy
                         |> Goal.init
                         |> auto_tac css |> Seq.hd

      val no_step = saved_state
                      |> forall_intr (cterm_of thy relvar)
                      |> forall_elim (cterm_of thy (Abs ("", HOLogic.natT, Abs ("", HOLogic.natT, HOLogic.false_const))))
                      |> auto_tac css |> Seq.hd

    in
      if Thm.no_prems no_step
      then NoStep (Goal.finish ctxt no_step RS no_stepI)
      else
        let
          fun set_m1 i =
              let
                val M1 = nth Mst1 i
                val with_m1 = saved_state
                                |> forall_intr (cterm_of thy mvar1)
                                |> forall_elim (cterm_of thy M1)
                                |> auto_tac css |> Seq.hd

                fun set_m2 j =
                    let
                      val M2 = nth Mst2 j
                      val with_m2 = with_m1
                                      |> forall_intr (cterm_of thy mvar2)
                                      |> forall_elim (cterm_of thy M2)
                                      |> auto_tac css |> Seq.hd

                      val decr = forall_intr (cterm_of thy relvar)
                                   #> forall_elim (cterm_of thy @{const HOL.less(nat)})
                                   #> auto_tac css #> Seq.hd

                      val decreq = forall_intr (cterm_of thy relvar)
                                     #> forall_elim (cterm_of thy @{const HOL.less_eq(nat)})
                                     #> auto_tac css #> Seq.hd

                      val thm1 = decr with_m2
                    in
                      if Thm.no_prems thm1
                      then ((rtac (inst_nums thy i j approx_less) 1) THEN (simp_nth_tac 1) THEN (rtac (Goal.finish ctxt thm1) 1))
                      else let val thm2 = decreq with_m2 in
                             if Thm.no_prems thm2
                             then ((rtac (inst_nums thy i j approx_leq) 1) THEN (simp_nth_tac 1) THEN (rtac (Goal.finish ctxt thm2) 1))
                             else all_tac end
                    end
              in set_m2 end

          val goal = HOLogic.mk_Trueprop (mk_approx (Var (("G", 0), scgT)) RD1 RD2 Ms1 Ms2)

          val tac = (EVERY (map_range (fn n => EVERY (map_range (set_m1 n) M)) N))
                      THEN (rtac approx_empty 1)

          val approx_thm = goal
                    |> cterm_of thy
                    |> Goal.init
                    |> tac |> Seq.hd
                    |> Goal.finish ctxt

          val _ $ (_ $ G $ _ $ _ $ _ $ _) = prop_of approx_thm
        in
          Graph (G, approx_thm)
        end
    end

fun mk_edge m G n = HOLogic.mk_prod (m, HOLogic.mk_prod (G, n))

fun in_graph_tac ctxt =
    simp_tac (HOL_basic_ss addsimps has_edge_simps) 1
    THEN (simp_tac (simpset_of ctxt) 1) (* FIXME reduce simpset *)

fun approx_tac _ (NoStep thm) = rtac disjI1 1 THEN rtac thm 1
  | approx_tac ctxt (Graph (G, thm)) =
    rtac disjI2 1
    THEN rtac exI 1
    THEN rtac conjI 1
    THEN rtac thm 2
    THEN (in_graph_tac ctxt)

fun all_less_tac [] = rtac all_less_zero 1
  | all_less_tac (t :: ts) = rtac all_less_Suc 1
                                  THEN simp_nth_tac 1
                                  THEN t
                                  THEN all_less_tac ts


fun mk_length l = HOLogic.size_const (fastype_of l) $ l;
val length_simps = thms "Interpretation.length_simps"



fun mk_call_graph ctxt (st : thm) =
    let
      val thy = ProofContext.theory_of ctxt
      val _ $ _ $ RDlist $ _ = HOLogic.dest_Trueprop (hd (prems_of st))

      val RDs = HOLogic.dest_list RDlist
      val n = length RDs

      val Mss = map (measures_of ctxt) RDs

      val domT = domain_type (fastype_of (hd (hd Mss)))

      val mfuns = map (fn Ms => mk_nth (HOLogic.mk_list (fastype_of (hd Ms)) Ms)) Mss
                      |> (fn l => HOLogic.mk_list (fastype_of (hd l)) l)

      val Dtab = tabulate_tlist thy RDlist
      val Mtab = tabulate_tlist thy mfuns

      val len_simp = Simplifier.rewrite (HOL_basic_ss addsimps length_simps) (cterm_of thy (mk_length RDlist))

      val mlens = map length Mss

      val indices = (n - 1 downto 0)
      val pairs = matrix indices indices
      val parts = map_matrix (fn (n,m) =>
                                 (timeap_msg (string_of_int n ^ "," ^ string_of_int m)
                                             (setup_probe_goal ctxt domT Dtab Mtab) (n,m))) pairs


      val s = fold_index (fn (i, cs) => fold_index (fn (j, Graph (G, _)) => prefix ("(" ^ string_of_int i ^ "," ^ string_of_int j ^ "): " ^
                                                                            Syntax.string_of_term ctxt G ^ ",\n")
                                                     | _ => I) cs) parts ""
      val _ = warning s


      val ACG = map_filter (fn (Graph (G, _),(m, n)) => SOME (mk_edge (mk_number m) G (mk_number n)) | _ => NONE) (flat parts ~~ flat pairs)
                    |> HOLogic.mk_set (edgeT HOLogic.natT scgT)
                    |> curry op $ (graph_const HOLogic.natT scgT)


      val sound_int_goal = HOLogic.mk_Trueprop (mk_sound_int ACG RDlist mfuns)

      val tac =
          unfold_tac [sound_int_def, len_simp] (simpset_of ctxt)
            THEN all_less_tac (map (all_less_tac o map (approx_tac ctxt)) parts)
    in
      tac (instantiate' [] [SOME (cterm_of thy ACG), SOME (cterm_of thy mfuns)] st)
    end


end







