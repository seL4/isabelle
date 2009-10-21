(*  Title:       HOL/Tools/Function/scnp_solve.ML
    Author:      Armin Heller, TU Muenchen
    Author:      Alexander Krauss, TU Muenchen

Generate certificates for SCNP using a SAT solver
*)


signature SCNP_SOLVE =
sig

  datatype edge = GTR | GEQ
  datatype graph = G of int * int * (int * edge * int) list
  datatype graph_problem = GP of int list * graph list

  datatype label = MIN | MAX | MS

  type certificate =
    label                   (* which order *)
    * (int * int) list list (* (multi)sets *)
    * int list              (* strictly ordered calls *)
    * (int -> bool -> int -> (int * int) option) (* covering function *)

  val generate_certificate : bool -> label list -> graph_problem -> certificate option

  val solver : string Unsynchronized.ref
end

structure ScnpSolve : SCNP_SOLVE =
struct

(** Graph problems **)

datatype edge = GTR | GEQ ;
datatype graph = G of int * int * (int * edge * int) list ;
datatype graph_problem = GP of int list * graph list ;

datatype label = MIN | MAX | MS ;
type certificate =
  label
  * (int * int) list list
  * int list
  * (int -> bool -> int -> (int * int) option)

fun graph_at (GP (_, gs), i) = nth gs i ;
fun num_prog_pts (GP (arities, _)) = length arities ;
fun num_graphs (GP (_, gs)) = length gs ;
fun arity (GP (arities, gl)) i = nth arities i ;
fun ndigits (GP (arities, _)) = IntInf.log2 (Integer.sum arities) + 1


(** Propositional formulas **)

val Not = PropLogic.Not and And = PropLogic.And and Or = PropLogic.Or
val BoolVar = PropLogic.BoolVar
fun Implies (p, q) = Or (Not p, q)
fun Equiv (p, q) = And (Implies (p, q), Implies (q, p))
val all = PropLogic.all

(* finite indexed quantifiers:

iforall n f   <==>      /\
                       /  \  f i
                      0<=i<n
 *)
fun iforall n f = all (map f (0 upto n - 1))
fun iexists n f = PropLogic.exists (map f (0 upto n - 1))
fun iforall2 n m f = all (map_product f (0 upto n - 1) (0 upto m - 1))

fun the_one var n x = all (var x :: map (Not o var) (remove (op =) x (0 upto n - 1)))
fun exactly_one n f = iexists n (the_one f n)

(* SAT solving *)
val solver = Unsynchronized.ref "auto";
fun sat_solver x =
  FundefCommon.PROFILE "sat_solving..." (SatSolver.invoke_solver (!solver)) x

(* "Virtual constructors" for various propositional variables *)
fun var_constrs (gp as GP (arities, gl)) =
  let
    val n = Int.max (num_graphs gp, num_prog_pts gp)
    val k = fold Integer.max arities 1

    (* Injective, provided  a < 8, x < n, and i < k. *)
    fun prod a x i j = ((j * k + i) * n + x) * 8 + a + 1

    fun ES (g, i, j) = BoolVar (prod 0 g i j)
    fun EW (g, i, j) = BoolVar (prod 1 g i j)
    fun WEAK g       = BoolVar (prod 2 g 0 0)
    fun STRICT g     = BoolVar (prod 3 g 0 0)
    fun P (p, i)     = BoolVar (prod 4 p i 0)
    fun GAM (g, i, j)= BoolVar (prod 5 g i j)
    fun EPS (g, i)   = BoolVar (prod 6 g i 0)
    fun TAG (p, i) b = BoolVar (prod 7 p i b)
  in
    (ES,EW,WEAK,STRICT,P,GAM,EPS,TAG)
  end


fun graph_info gp g =
  let
    val G (p, q, edgs) = graph_at (gp, g)
  in
    (g, p, q, arity gp p, arity gp q, edgs)
  end


(* Order-independent part of encoding *)

fun encode_graphs bits gp =
  let
    val ng = num_graphs gp
    val (ES,EW,_,_,_,_,_,TAG) = var_constrs gp

    fun encode_constraint_strict 0 (x, y) = PropLogic.False
      | encode_constraint_strict k (x, y) =
        Or (And (TAG x (k - 1), Not (TAG y (k - 1))),
            And (Equiv (TAG x (k - 1), TAG y (k - 1)),
                 encode_constraint_strict (k - 1) (x, y)))

    fun encode_constraint_weak k (x, y) =
        Or (encode_constraint_strict k (x, y),
            iforall k (fn i => Equiv (TAG x i, TAG y i)))

    fun encode_graph (g, p, q, n, m, edges) =
      let
        fun encode_edge i j =
          if exists (fn x => x = (i, GTR, j)) edges then
            And (ES (g, i, j), EW (g, i, j))
          else if not (exists (fn x => x = (i, GEQ, j)) edges) then
            And (Not (ES (g, i, j)), Not (EW (g, i, j)))
          else
            And (
              Equiv (ES (g, i, j),
                     encode_constraint_strict bits ((p, i), (q, j))),
              Equiv (EW (g, i, j),
                     encode_constraint_weak bits ((p, i), (q, j))))
       in
        iforall2 n m encode_edge
      end
  in
    iforall ng (encode_graph o graph_info gp)
  end


(* Order-specific part of encoding *)

fun encode bits gp mu =
  let
    val ng = num_graphs gp
    val (ES,EW,WEAK,STRICT,P,GAM,EPS,_) = var_constrs gp

    fun encode_graph MAX (g, p, q, n, m, _) =
        And (
          Equiv (WEAK g,
            iforall m (fn j =>
              Implies (P (q, j),
                iexists n (fn i =>
                  And (P (p, i), EW (g, i, j)))))),
          Equiv (STRICT g,
            And (
              iforall m (fn j =>
                Implies (P (q, j),
                  iexists n (fn i =>
                    And (P (p, i), ES (g, i, j))))),
              iexists n (fn i => P (p, i)))))
      | encode_graph MIN (g, p, q, n, m, _) =
        And (
          Equiv (WEAK g,
            iforall n (fn i =>
              Implies (P (p, i),
                iexists m (fn j =>
                  And (P (q, j), EW (g, i, j)))))),
          Equiv (STRICT g,
            And (
              iforall n (fn i =>
                Implies (P (p, i),
                  iexists m (fn j =>
                    And (P (q, j), ES (g, i, j))))),
              iexists m (fn j => P (q, j)))))
      | encode_graph MS (g, p, q, n, m, _) =
        all [
          Equiv (WEAK g,
            iforall m (fn j =>
              Implies (P (q, j),
                iexists n (fn i => GAM (g, i, j))))),
          Equiv (STRICT g,
            iexists n (fn i =>
              And (P (p, i), Not (EPS (g, i))))),
          iforall2 n m (fn i => fn j =>
            Implies (GAM (g, i, j),
              all [
                P (p, i),
                P (q, j),
                EW (g, i, j),
                Equiv (Not (EPS (g, i)), ES (g, i, j))])),
          iforall n (fn i =>
            Implies (And (P (p, i), EPS (g, i)),
              exactly_one m (fn j => GAM (g, i, j))))
        ]
  in
    all [
      encode_graphs bits gp,
      iforall ng (encode_graph mu o graph_info gp),
      iforall ng (fn x => WEAK x),
      iexists ng (fn x => STRICT x)
    ]
  end


(*Generieren des level-mapping und diverser output*)
fun mk_certificate bits label gp f =
  let
    val (ES,EW,WEAK,STRICT,P,GAM,EPS,TAG) = var_constrs gp
    fun assign (PropLogic.BoolVar v) = the_default false (f v)
    fun assignTag i j =
      (fold (fn x => fn y => 2 * y + (if assign (TAG (i, j) x) then 1 else 0))
        (bits - 1 downto 0) 0)

    val level_mapping =
      let fun prog_pt_mapping p =
            map_filter (fn x => if assign (P(p, x)) then SOME (x, assignTag p x) else NONE)
              (0 upto (arity gp p) - 1)
      in map prog_pt_mapping (0 upto num_prog_pts gp - 1) end

    val strict_list = filter (assign o STRICT) (0 upto num_graphs gp - 1)

    fun covering_pair g bStrict j =
      let
        val (_, p, q, n, m, _) = graph_info gp g

        fun cover        MAX j = find_index (fn i => assign (P (p, i))      andalso      assign (EW  (g, i, j))) (0 upto n - 1)
          | cover        MS  k = find_index (fn i =>                                     assign (GAM (g, i, k))) (0 upto n - 1)
          | cover        MIN i = find_index (fn j => assign (P (q, j))      andalso      assign (EW  (g, i, j))) (0 upto m - 1)
        fun cover_strict MAX j = find_index (fn i => assign (P (p, i))      andalso      assign (ES  (g, i, j))) (0 upto n - 1)
          | cover_strict MS  k = find_index (fn i => assign (GAM (g, i, k)) andalso not (assign (EPS (g, i)  ))) (0 upto n - 1)
          | cover_strict MIN i = find_index (fn j => assign (P (q, j))      andalso      assign (ES  (g, i, j))) (0 upto m - 1)
        val i = if bStrict then cover_strict label j else cover label j
      in
        find_first (fn x => fst x = i) (nth level_mapping (if label = MIN then q else p))
      end
  in
    (label, level_mapping, strict_list, covering_pair)
  end

(*interface for the proof reconstruction*)
fun generate_certificate use_tags labels gp =
  let
    val bits = if use_tags then ndigits gp else 0
  in
    get_first
      (fn l => case sat_solver (encode bits gp l) of
                 SatSolver.SATISFIABLE f => SOME (mk_certificate bits l gp f)
               | _ => NONE)
      labels
  end
end
