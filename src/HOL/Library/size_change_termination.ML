
structure SCT = struct

fun matrix [] ys = []
  | matrix (x::xs) ys = map (pair x) ys :: matrix xs ys

fun map_matrix f xss = map (map f) xss

val scgT = Sign.read_typ (the_context (), K NONE) "scg"
val acgT = Sign.read_typ (the_context (), K NONE) "acg"

fun edgeT nT eT = HOLogic.mk_prodT (nT, HOLogic.mk_prodT (eT, nT))
fun graphT nT eT = Type ("Graphs.graph", [nT, eT])

fun graph_const nT eT = Const ("Graphs.graph.Graph", HOLogic.mk_setT (edgeT nT eT) --> graphT nT eT)


val no_step_const = "SCT_Interpretation.no_step"
val no_step_def = thm "SCT_Interpretation.no_step_def"
val no_stepI = thm "SCT_Interpretation.no_stepI"

fun mk_no_step RD1 RD2 = 
    let val RDT = fastype_of RD1
    in Const (no_step_const, RDT --> RDT --> HOLogic.boolT) $ RD1 $ RD2 end

val decr_const = "SCT_Interpretation.decr"
val decr_def = thm "SCT_Interpretation.decr_def"

fun mk_decr RD1 RD2 M1 M2 = 
    let val RDT = fastype_of RD1
      val MT = fastype_of M1
    in Const (decr_const, RDT --> RDT --> MT --> MT --> HOLogic.boolT) $ RD1 $ RD2 $ M1 $ M2 end

val decreq_const = "SCT_Interpretation.decreq"
val decreq_def = thm "SCT_Interpretation.decreq_def"

fun mk_decreq RD1 RD2 M1 M2 = 
    let val RDT = fastype_of RD1
      val MT = fastype_of M1
    in Const (decreq_const, RDT --> RDT --> MT --> MT --> HOLogic.boolT) $ RD1 $ RD2 $ M1 $ M2 end

val stepP_const = "SCT_Interpretation.stepP"
val stepP_def = thm "SCT_Interpretation.stepP.simps"

fun mk_stepP RD1 RD2 M1 M2 Rel = 
    let val RDT = fastype_of RD1
      val MT = fastype_of M1
    in 
      Const (stepP_const, RDT --> RDT --> MT --> MT --> (fastype_of Rel) --> HOLogic.boolT) 
            $ RD1 $ RD2 $ M1 $ M2 $ Rel 
    end

val approx_const = "SCT_Interpretation.approx"
val approx_empty = thm "SCT_Interpretation.approx_empty"
val approx_less = thm "SCT_Interpretation.approx_less"
val approx_leq = thm "SCT_Interpretation.approx_leq"

fun mk_approx G RD1 RD2 Ms1 Ms2 = 
    let val RDT = fastype_of RD1
      val MsT = fastype_of Ms1
    in Const (approx_const, scgT --> RDT --> RDT --> MsT --> MsT --> HOLogic.boolT) $ G $ RD1 $ RD2 $ Ms1 $ Ms2 end

val sound_int_const = "SCT_Interpretation.sound_int"
val sound_int_def = thm "SCT_Interpretation.sound_int_def"
fun mk_sound_int A RDs M =
    let val RDsT = fastype_of RDs
      val MT = fastype_of M
    in Const (sound_int_const, acgT --> RDsT --> MT --> HOLogic.boolT) $ A $ RDs $ M end


val nth_const = "List.nth"
fun mk_nth xs =
    let val lT as Type (_, [T]) = fastype_of xs
    in Const (nth_const, lT --> HOLogic.natT --> T) $ xs end


val less_nat_const = Const ("Orderings.less", HOLogic.natT --> HOLogic.natT --> HOLogic.boolT)
val lesseq_nat_const = Const ("Orderings.less_eq", HOLogic.natT --> HOLogic.natT --> HOLogic.boolT)


(*
val has_edge_const = "Graphs.has_edge"
fun mk_has_edge G n e n' =
    let val nT = fastype_of n and eT = fastype_of e
    in Const (has_edge_const, graphT nT eT --> nT --> eT --> nT --> HOLogic.boolT) $ n $ e $ n' end
*)


val has_edge_simps = [thm "Graphs.has_edge_def", thm "Graphs.dest_graph.simps"]

val all_less_zero = thm "SCT_Interpretation.all_less_zero"
val all_less_Suc = thm "SCT_Interpretation.all_less_Suc"



(* Lists as finite multisets *)

(* --> Library *)
fun del_index n [] = []
  | del_index n (x :: xs) =
    if n>0 then x :: del_index (n - 1) xs else xs 


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


fun dist_vars [] vs = (assert (null vs) "dist_vars"; [])
  | dist_vars (T::Ts) vs = 
    case find_index (fn v => fastype_of v = T) vs of
      ~1 => Free ("", T) :: dist_vars Ts vs
    |  i => (nth vs i) :: dist_vars Ts (del_index i vs)


fun dest_case rebind t =
    let
      val (_ $ _ $ rhs :: _ $ _ $ match :: guards) = HOLogic.dest_conj t
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
fun measures_of RD =
    let
      val domT = range_type (fastype_of (fst (HOLogic.dest_prod (snd (HOLogic.dest_prod RD)))))
      val measures = LexicographicOrder.mk_base_funs domT
    in
      measures
    end



val mk_number = HOLogic.mk_nat
val dest_number = HOLogic.dest_nat

fun nums_to i = map mk_number (0 upto (i - 1))


fun unfold_then_auto thm = 
    (SIMPSET (unfold_tac [thm]))
      THEN (CLASIMPSET auto_tac)

val nth_simps = [thm "List.nth_Cons_0", thm "List.nth_Cons_Suc"]
val nth_ss = (HOL_basic_ss addsimps nth_simps)
val simp_nth_tac = simp_tac nth_ss



fun tabulate_tlist thy l =
    let
      val n = length (HOLogic.dest_list l)
      val table = Inttab.make (map (fn i => (i, Simplifier.rewrite nth_ss (cterm_of thy (mk_nth l $ mk_number i)))) (0 upto n - 1))
    in
      the o Inttab.lookup table
    end

val get_elem = snd o Logic.dest_equals o prop_of


(* Attempt a proof of a given goal *)

datatype proof_result = 
    Success of thm
  | Stuck of thm
  | Fail
  | False
  | Timeout (* not implemented *)

fun try_to_prove tactic cgoal =
    case SINGLE tactic (Goal.init cgoal) of
      NONE => Fail
    | SOME st => if Thm.no_prems st 
                 then Success (Goal.finish st)
                 else if prems_of st = [HOLogic.Trueprop $ HOLogic.false_const] then False 
                 else Stuck st

fun simple_result (Success thm) = SOME thm
  | simple_result _ = NONE


fun inst_nums thy i j (t:thm) = 
  instantiate' [] [NONE, NONE, NONE, SOME (cterm_of thy (mk_number i)), NONE, SOME (cterm_of thy (mk_number j))] t

datatype call_fact =
   NoStep of thm
 | Graph of (term * thm)

fun rand (_ $ t) = t

fun setup_probe_goal thy domT Dtab Mtab (i, j) =
    let
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
                         |> CLASIMPSET auto_tac |> Seq.hd
                         
      val no_step = saved_state 
                      |> forall_intr (cterm_of thy relvar)
                      |> forall_elim (cterm_of thy (Abs ("", HOLogic.natT, Abs ("", HOLogic.natT, HOLogic.false_const))))
                      |> CLASIMPSET auto_tac |> Seq.hd

    in
      if Thm.no_prems no_step
      then NoStep (Goal.finish no_step RS no_stepI)
      else
        let
          fun set_m1 i =
              let 
                val M1 = nth Mst1 i
                val with_m1 = saved_state
                                |> forall_intr (cterm_of thy mvar1)
                                |> forall_elim (cterm_of thy M1)
                                |> CLASIMPSET auto_tac |> Seq.hd

                fun set_m2 j = 
                    let 
                      val M2 = nth Mst2 j
                      val with_m2 = with_m1
                                      |> forall_intr (cterm_of thy mvar2)
                                      |> forall_elim (cterm_of thy M2)
                                      |> CLASIMPSET auto_tac |> Seq.hd

                      val decr = forall_intr (cterm_of thy relvar)
                                   #> forall_elim (cterm_of thy less_nat_const)
                                   #> CLASIMPSET auto_tac #> Seq.hd

                      val decreq = forall_intr (cterm_of thy relvar)
                                     #> forall_elim (cterm_of thy lesseq_nat_const)
                                     #> CLASIMPSET auto_tac #> Seq.hd

                      val thm1 = decr with_m2
                    in
                      if Thm.no_prems thm1 
                      then ((rtac (inst_nums thy i j approx_less) 1) THEN (simp_nth_tac 1) THEN (rtac (Goal.finish thm1) 1))
                      else let val thm2 = decreq with_m2 in
                             if Thm.no_prems thm2 
                             then ((rtac (inst_nums thy i j approx_leq) 1) THEN (simp_nth_tac 1) THEN (rtac (Goal.finish thm2) 1))
                             else all_tac end
                    end
              in set_m2 end

          val goal = HOLogic.mk_Trueprop (mk_approx (Var (("G", 0), scgT)) RD1 RD2 Ms1 Ms2)

          val tac = (EVERY (map (fn n => EVERY (map (set_m1 n) (0 upto M - 1))) (0 upto N - 1)))
                      THEN (rtac approx_empty 1)

          val approx_thm = goal 
                    |> cterm_of thy
                    |> Goal.init
                    |> tac |> Seq.hd
                    |> Goal.finish

          val _ $ (_ $ G $ _ $ _ $ _ $ _) = prop_of approx_thm
        in
          Graph (G, approx_thm)
        end
    end





fun probe_nostep thy Dtab i j =
    HOLogic.mk_Trueprop (mk_no_step (get_elem (Dtab i)) (get_elem (Dtab j))) 
      |> cterm_of thy
      |> try_to_prove (unfold_then_auto no_step_def)
      |> simple_result

fun probe_decr thy RD1 RD2 m1 m2 =
    HOLogic.mk_Trueprop (mk_decr RD1 RD2 m1 m2)
      |> cterm_of thy 
      |> try_to_prove (unfold_then_auto decr_def)
      |> simple_result

fun probe_decreq thy RD1 RD2 m1 m2 =
    HOLogic.mk_Trueprop (mk_decreq RD1 RD2 m1 m2)
      |> cterm_of thy 
      |> try_to_prove (unfold_then_auto decreq_def)
      |> simple_result


fun pr_tac (st : thm) = Seq.single (Output.warning (PolyML.makestring st); st)
fun pr_thm (st : thm) = (Output.warning (PolyML.makestring st); st)


fun build_approximating_graph thy Dtab Mtab Mss mlens mint nint =
    let 
      val D1 = Dtab mint and D2 = Dtab nint
      val Mst1 = Mtab mint and Mst2 = Mtab nint

      val RD1 = get_elem D1 and RD2 = get_elem D2
      val Ms1 = get_elem Mst1 and Ms2 = get_elem Mst2

      val goal = HOLogic.mk_Trueprop (mk_approx (Var (("G", 0), scgT)) RD1 RD2 Ms1 Ms2)

      val Ms1 = nth (nth Mss mint) and Ms2 = nth (nth Mss mint)

      fun add_edge (i,j) = 
          case timeap_msg ("decr(" ^ string_of_int i ^ "," ^ string_of_int j ^ ")")
                          (probe_decr thy RD1 RD2 (Ms1 i)) (Ms2 j) of
            SOME thm => (Output.warning "Success"; (rtac (inst_nums thy i j approx_less) 1) THEN (simp_nth_tac 1) THEN (rtac thm 1))
          | NONE => case timeap_msg ("decr(" ^ string_of_int i ^ "," ^ string_of_int j ^ ")")
                                    (probe_decreq thy RD1 RD2 (Ms1 i)) (Ms2 j) of
                      SOME thm => (Output.warning "Success"; (rtac (inst_nums thy i j approx_leq) 1) THEN (simp_nth_tac 1) THEN (rtac thm 1))
                    | NONE => all_tac

      val approx_thm =
          goal
            |> cterm_of thy
            |> Goal.init
            |> SINGLE ((EVERY (map add_edge (product (0 upto (nth mlens mint) - 1) (0 upto (nth mlens nint) - 1))))
                       THEN (rtac approx_empty 1))
            |> the
            |> Goal.finish

      val _ $ (_ $ G $ _ $ _ $ _ $ _) = prop_of approx_thm
    in
      (G, approx_thm)
    end



fun prove_call_fact thy Dtab Mtab Mss mlens (m, n) =
    case probe_nostep thy Dtab m n of
      SOME thm => (Output.warning "NoStep"; NoStep thm)
    | NONE => Graph (build_approximating_graph thy Dtab Mtab Mss mlens m n)


fun mk_edge m G n = HOLogic.mk_prod (m, HOLogic.mk_prod (G, n))


fun mk_set T [] = Const ("{}", HOLogic.mk_setT T)
  | mk_set T (x :: xs) = Const ("insert",
      T --> HOLogic.mk_setT T --> HOLogic.mk_setT T) $ x $ mk_set T xs

fun dest_set (Const ("{}", _)) = []
  | dest_set (Const ("insert", _) $ x $ xs) = x :: dest_set xs

val pr_graph = Sign.string_of_term


fun pr_matrix thy = map_matrix (fn Graph (G, _) => pr_graph thy G | _ => "X")

val in_graph_tac = 
    simp_tac (HOL_basic_ss addsimps has_edge_simps) 1
    THEN SIMPSET (fn x => simp_tac x 1) (* FIXME reduce simpset *)

fun approx_tac (NoStep thm) = rtac disjI1 1 THEN rtac thm 1
  | approx_tac (Graph (G, thm)) =
    rtac disjI2 1 
    THEN rtac exI 1
    THEN rtac conjI 1
    THEN rtac thm 2
    THEN in_graph_tac

fun all_less_tac [] = rtac all_less_zero 1
  | all_less_tac (t :: ts) = rtac all_less_Suc 1 
                                  THEN simp_nth_tac 1
                                  THEN t 
                                  THEN all_less_tac ts


val length_const = "Nat.size"
fun mk_length l = Const (length_const, fastype_of l --> HOLogic.natT) $ l
val length_simps = thms "SCT_Interpretation.length_simps"



fun mk_call_graph (st : thm) =
    let
      val thy = theory_of_thm st
      val _ $ _ $ RDlist $ _ = HOLogic.dest_Trueprop (hd (prems_of st))

      val RDs = HOLogic.dest_list RDlist
      val n = length RDs 

      val Mss = map measures_of RDs

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
                                             (setup_probe_goal thy domT Dtab Mtab) (n,m))) pairs


      val s = fold_index (fn (i, cs) => fold_index (fn (j, Graph (G, _)) => prefix ("(" ^ string_of_int i ^ "," ^ string_of_int j ^ "): " ^
                                                                            pr_graph thy G ^ ",\n")
                                                     | _ => I) cs) parts ""
      val _ = Output.warning s
  

      val ACG = map_filter (fn (Graph (G, _),(m, n)) => SOME (mk_edge (mk_number m) G (mk_number n)) | _ => NONE) (flat parts ~~ flat pairs)
                    |> mk_set (edgeT HOLogic.natT scgT)
                    |> curry op $ (graph_const HOLogic.natT scgT)


      val sound_int_goal = HOLogic.mk_Trueprop (mk_sound_int ACG RDlist mfuns)

      val tac = 
          (SIMPSET (unfold_tac [sound_int_def, len_simp]))
            THEN all_less_tac (map (all_less_tac o map approx_tac) parts)
    in
      tac (instantiate' [] [SOME (cterm_of thy ACG), SOME (cterm_of thy mfuns)] st)
    end
                  











(* Faster implementation of transitive closures *)

(* sedge: Only relevant edges. Qtrees have separate value for 0 *)
datatype sedge = LESS | LEQ | BOTH



datatype key = KHere | K0 of key | K1 of key

datatype 'a stree = 
  sLeaf of 'a
  | sBranch of ('a * 'a stree * 'a stree)

(*
fun lookup (sLeaf x) KHere = x
  | lookup (sBranch x s t) KHere = x
  | lookup (sBranch x s t) (K0 k) = lookup s k
  | lookup (sBranch x s t) (K1 k) = lookup t k
  | lookup _ _ = raise Match
*)

datatype 'a qtree =
  QEmpty
  | QNode of 'a
  | QQuad of ('a qtree * 'a qtree * 'a qtree * 'a qtree)

fun qlookup z QEmpty k l = z
  | qlookup z (QNode S) k l = S
  | qlookup z (QQuad (a, b, c, d)) (K0 k) (K0 l) = qlookup z a k l
  | qlookup z (QQuad (a, b, c, d)) (K0 k) (K1 l) = qlookup z b k l
  | qlookup z (QQuad (a, b, c, d)) (K1 k) (K0 l) = qlookup z c k l
  | qlookup z (QQuad (a, b, c, d)) (K1 k) (K1 l) = qlookup z d k l
  | qlookup _ _ _ _ = raise Match



(* Size-change graphs *)

type
  scg = sedge qtree


(* addition of single edges *)
fun add_sedge BOTH _ = BOTH
  | add_sedge LESS LESS = LESS
  | add_sedge LESS _ = BOTH
  | add_sedge LEQ LEQ = LEQ
  | add_sedge LEQ _ = BOTH

fun mult_sedge LESS _ = LESS
  | mult_sedge _ LESS = LESS
  | mult_sedge LEQ x = x
  | mult_sedge BOTH _ = BOTH

fun subsumes_edge LESS LESS = true
  | subsumes_edge LEQ _ = true
  | subsumes_edge _ _ = false




(* subsumes_SCG G H := G contains strictly less estimations than H *)
fun subsumes_SCG (QEmpty : scg) (H : scg) = true
  | subsumes_SCG (QQuad (a, b, c, d)) (QQuad (e,f,g,h)) =
    (subsumes_SCG a e) andalso (subsumes_SCG b f)
    andalso (subsumes_SCG c g) andalso (subsumes_SCG d h)
  | subsumes_SCG (QNode e) (QNode e') = subsumes_edge e e'
  | subsumes_SCG _ QEmpty = false
  | subsumes_SCG _ _ = raise Match


(* managing lists of SCGs. *)

(* 
 Graphs are partially ordered. A list of graphs has the invariant that no G,H with G <= H.
 To maintain this when adding a new graph G, check 
   (1) G <= H for some H in l => Do nothing
   (2) has to be added. Then, all H <= G can be removed. 

 We can check (2) first, removing all smaller graphs. 
 If we could remove at least one, just add G in the end (Invariant!).
 Otherwise, check again, if G needs to be added at all. 

 OTOH, doing (1) first is probably better, because it does not produce garbage unless needed.

 The definition is tail-recursive. Order is not preserved (unneccessary).
*)



fun add_scg' G Hs = (* returns a flag indicating if the graph was really added *)
    if exists (fn H => subsumes_SCG H G) Hs then (false, Hs)  (* redundant addition *)
    else (true, G :: remove (uncurry subsumes_SCG) G Hs) (* remove all new redundancy and add G *)
         (* NB: This does the second checks twice :-( *)

(* Simpler version *)
fun add_scg' G Hs = (not (member (op =) Hs G), insert (op =) G Hs)


val add_scg = snd oo add_scg' (* without flag *)





(* quadtrees *)

fun keylen 0 = 0 
  | keylen n = (keylen (n div 2)) + 1

fun mk_key 0 _  = KHere
  | mk_key l m = if m mod 2 = 0 
                 then K0 (mk_key (l - 1) (m div 2)) 
                 else K1 (mk_key (l - 1) (m div 2)) 


fun qupdate f KHere KHere n = f n
  | qupdate f (K0 k) (K0 k') (QQuad (a, b, c, d)) = QQuad (qupdate f k k' a, b, c, d)
  | qupdate f (K0 k) (K1 k') (QQuad (a, b, c, d)) = QQuad (a, qupdate f k k' b, c, d)
  | qupdate f (K1 k) (K0 k') (QQuad (a, b, c, d)) = QQuad (a, b, qupdate f k k' c, d)
  | qupdate f (K1 k) (K1 k') (QQuad (a, b, c, d)) = QQuad (a, b, c, qupdate f k k' d)








(* quadtree composition *)

fun qadd A QEmpty q = q
  | qadd A q QEmpty = q
  | qadd A (QNode s) (QNode t) = QNode (A s t)
  | qadd A (QQuad (a, b, c, d)) (QQuad (e, f, g, h)) =
    QQuad (qadd A a e, qadd A b f, qadd A c g, qadd A d h)
  | qadd _ _ _ = raise Match


fun qmult A m QEmpty H = QEmpty
  | qmult A m G QEmpty = QEmpty
  | qmult A m (QNode x) (QNode y) = QNode (m x y)
  | qmult A m (QQuad (a, b, c, d)) (QQuad (e, f, g, h)) = 
    QQuad ((qadd A (qmult A m a e) (qmult A m b g)),
           (qadd A (qmult A m a f) (qmult A m b h)),
           (qadd A (qmult A m c e) (qmult A m d g)),
           (qadd A (qmult A m c f) (qmult A m d h)))
  | qmult _ _ _ _ = raise Match


val (mult_scg : scg -> scg -> scg) = qmult add_sedge mult_sedge

(* Misc notes:

- When building the tcl: Check on addition and raise FAIL if the property is not true... (pract)

- Can we reduce subsumption checking by some integer fingerprints?

 Number of edges: LESS(G) LEQ(G)
  G <= H ==> E(G) <= E(H)
  


How to check:

For each pair of adjacent edges: n -> m -> q
 compute all product SCGS and check if they are subsumed by something in the tcl.

 all midnode m: all fromnode n: all tonode q: alledges (n,m) e: alledges (m,q) e': subsumes (e*e') (edgs m,q)

 This is still quite a lot of checking... But: no garbage, just inspection. Can probably be done in logic. 

*)



(* Operations on lists: These preserve the invariants *)
fun SCGs_mult Gs Hs = fold (fn (G,H) => add_scg (mult_scg G H)) (product Gs Hs) []
val SCGs_plus = fold add_scg


fun add_scgs Gs Hs = fold_rev (fn G => fn (Xs,As) => 
                                      let val (b, Xs') = add_scg' G Xs
                                      in (Xs', if b then G::As else As) end)
                          Gs (Hs,[])

(* Transitive Closure for lists of SCGs *)
fun SCGs_tcl Gs =
    let
      fun aux S [] = S
        | aux S (H::HS) =
          let val (S', Ns) = add_scgs (map (mult_scg H) Gs) S
          in aux S' (SCGs_plus Ns HS) end
    in
      aux Gs Gs
    end



(* Kleene algorithm: DP version, with imperative array... *)




(* Terrible imperative stuff: *)
type matrix = scg list array array

fun mupdate i j f M = 
    let 
      val row = Array.sub (M, i)
      val x = Array.sub (row, j)
    in 
      Array.update (row, j, f x)
    end

fun mget i j M = Array.sub(Array.sub(M,i),j)

fun print_scg (x : scg) = Output.warning (PolyML.makestring x);


fun kleene add mult tcl M =
    let
      val n = Array.length M

      fun update Mkk i j k = 
          let
            val Mik = mget i k M
            val Mkj = mget k j M
          in
            mupdate i j (fn X => X |> add (mult Mik (mult Mkk Mkj))
                                   |> add (mult Mik Mkj))
                    M
          end

      fun step k () =
          let
            val _ = mupdate k k tcl M
            val Mkk = mget k k M

            val no_k = filter_out (fn i => i = k) (0 upto (n - 1)) 
            val _ = fold (fn i => fold (fn j => K (update Mkk i j k)) no_k) no_k ()

            val _ = fold (fn i => K (update Mkk i k k)) no_k ()

            val _ = fold (fn j => K (update Mkk k j k)) no_k ()
          in
            ()
          end
    in
      fold step (0 upto (n - 1)) ()
    end

val (SCGs_kleene : matrix -> unit) = kleene SCGs_plus SCGs_mult SCGs_tcl


fun andop x y = x andalso y
fun orop x y = x orelse y

fun array2 n x = Array.tabulate (n, (fn i => Array.array (n, x)))

(*val bool_kleene = kleene orop andop I


fun test_bool () =
    let
      val M = array2 2 false
      val _ = mupdate 0 1 (K true) M
      val _ = mupdate 1 0 (K true) M
      val _ = bool_kleene M
    in
      M
    end
*)

(* Standard 2-2-Size-change graphs *)

val swap = QQuad(QEmpty, QNode LEQ,
                 QNode LEQ, QEmpty)

val swapRTop = QQuad(QNode LESS, QNode LEQ,
                     QNode LEQ, QEmpty)

val BTopRBot = QQuad(QNode LEQ, QEmpty,
                     QEmpty, QNode LESS)

val RTopBBot = QQuad(QNode LESS, QEmpty,
                     QEmpty, QNode LEQ)

val R2Straight = QQuad(QNode LESS, QEmpty,
                       QEmpty, QNode LESS)

val R3StraightUp = QQuad(QNode LESS, QEmpty,
                         QNode LESS, QNode LESS)

val R3StraightDn = QQuad(QNode LESS, QNode LESS,
                         QEmpty, QNode LESS)




val diag = QQuad(QEmpty, QNode LEQ,
                 QEmpty, QEmpty)

val straight = QQuad(QNode LEQ, QEmpty,
                     QEmpty, QEmpty)



val R467913 = ([R2Straight, R3StraightDn, R3StraightDn] @ replicate 11 R2Straight @ [R3StraightUp, R3StraightUp])
                |> map single

val swapPos = [(0,8),(0,9),(0,10),(3,4),(3,5),(11,12)]

val BRPos = (map (pair 5) (0 :: (3 upto 7)))
            @ (map (pair 8) [8,9,11,12,13])
            @ (map (pair 12) [8,9,11,12,13])

val RBPos = map (pair 10) (3 upto 10)

fun afold f arr x = Array.foldl (uncurry f) x arr

fun msize M = afold (afold (curry op + o length)) M 0

fun TestM () =
    let
      val M = array2 16 ([] : scg list)
      val _ = Array.update (M, 4, Array.fromList R467913)
      val _ = Array.update (M, 6, Array.fromList R467913)
      val _ = Array.update (M, 7, Array.fromList R467913)
      val _ = Array.update (M, 9, Array.fromList R467913)
      val _ = Array.update (M, 13, Array.fromList R467913)

      val _ = map (fn (i,j) => mupdate i j (K [swap]) M) swapPos
      val _ = map (fn (i,j) => mupdate i j (K [BTopRBot]) M) BRPos
      val _ = map (fn (i,j) => mupdate i j (K [RTopBBot]) M) RBPos

      val _ = mupdate 1 14 (K [swapRTop]) M
      val _ = mupdate 2 15 (K [swapRTop]) M

      val G = [QQuad (QNode LEQ, QNode LESS, QEmpty, QNode LESS)]
      val _ = mupdate 5 1 (K G) M
      val _ = mupdate 8 2 (K G) M
      val _ = mupdate 12 2 (K G) M

      val G = [QQuad (QNode LESS, QEmpty, QNode LESS, QNode LEQ)]
      val _ = mupdate 10 14 (K G) M

      val G = [QQuad (QEmpty, QNode LEQ, QNode LESS, QNode LESS)]
      val _ = mupdate 14 1 (K G) M
      val _ = mupdate 14 2 (K G) M
      val _ = mupdate 15 1 (K G) M
      val _ = mupdate 15 2 (K G) M
    in
      M
    end





fun add_edge x QEmpty = QNode x
  | add_edge x (QNode y) = QNode (add_sedge x y)


fun sedge2ML (Const ("SCT_Definition.sedge.LESS", _)) = LESS
  | sedge2ML (Const ("SCT_Definition.sedge.LEQ", _)) = LEQ
















end                   






