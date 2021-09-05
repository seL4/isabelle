(*  Title:      HOL/Library/Sum_of_Squares/sum_of_squares.ML
    Author:     Amine Chaieb, University of Cambridge
    Author:     Philipp Meyer, TU Muenchen

A tactic for proving nonlinear inequalities.
*)

signature SUM_OF_SQUARES =
sig
  datatype proof_method = Certificate of RealArith.pss_tree | Prover of string -> string
  val sos_tac: (RealArith.pss_tree -> unit) -> proof_method -> Proof.context -> int -> tactic
  val trace: bool Config.T
  val debug: bool Config.T
  val trace_message: Proof.context -> (unit -> string) -> unit
  val debug_message: Proof.context -> (unit -> string) -> unit
  exception Failure of string;
end

structure Sum_of_Squares: SUM_OF_SQUARES =
struct

val max = Integer.max;

val denominator_rat = Rat.dest #> snd #> Rat.of_int;

fun int_of_rat a =
  (case Rat.dest a of
    (i, 1) => i
  | _ => error "int_of_rat: not an int");

fun lcm_rat x y =
  Rat.of_int (Integer.lcm (int_of_rat x) (int_of_rat y));

fun rat_pow r i =
 let fun pow r i =
   if i = 0 then @1 else
   let val d = pow r (i div 2)
   in d * d * (if i mod 2 = 0 then @1 else r)
   end
 in if i < 0 then pow (Rat.inv r) (~ i) else pow r i end;

fun round_rat r =
  let
    val (a,b) = Rat.dest (abs r)
    val d = a div b
    val s = if r < @0 then ~ o Rat.of_int else Rat.of_int
    val x2 = 2 * (a - (b * d))
  in s (if x2 >= b then d + 1 else d) end


val trace = Attrib.setup_config_bool \<^binding>\<open>sos_trace\<close> (K false);
val debug = Attrib.setup_config_bool \<^binding>\<open>sos_debug\<close> (K false);

fun trace_message ctxt msg =
  if Config.get ctxt trace orelse Config.get ctxt debug then tracing (msg ()) else ();
fun debug_message ctxt msg = if Config.get ctxt debug then tracing (msg ()) else ();

exception Sanity;

exception Unsolvable;

exception Failure of string;

datatype proof_method =
    Certificate of RealArith.pss_tree
  | Prover of (string -> string)

(* Turn a rational into a decimal string with d sig digits.                  *)

local

fun normalize y =
  if abs y < @1/10 then normalize (@10 * y) - 1
  else if abs y >= @1 then normalize (y / @10) + 1
  else 0

in

fun decimalize d x =
  if x = @0 then "0.0"
  else
    let
      val y = abs x
      val e = normalize y
      val z = rat_pow @10 (~ e) * y + @1
      val k = int_of_rat (round_rat (rat_pow @10 d * z))
    in
      (if x < @0 then "-0." else "0.") ^
      implode (tl (raw_explode(string_of_int k))) ^
      (if e = 0 then "" else "e" ^ string_of_int e)
    end

end;

(* Iterations over numbers, and lists indexed by numbers.                    *)

fun itern k l f a =
  (case l of
    [] => a
  | h::t => itern (k + 1) t f (f h k a));

fun iter (m,n) f a =
  if n < m then a
  else iter (m + 1, n) f (f m a);

(* The main types.                                                           *)

type vector = int * Rat.rat FuncUtil.Intfunc.table;

type matrix = (int * int) * Rat.rat FuncUtil.Intpairfunc.table;

fun iszero (_, r) = r = @0;


(* Vectors. Conventionally indexed 1..n.                                     *)

fun vector_0 n = (n, FuncUtil.Intfunc.empty): vector;

fun dim (v: vector) = fst v;

fun vector_cmul c (v: vector) =
  let val n = dim v in
    if c = @0 then vector_0 n
    else (n,FuncUtil.Intfunc.map (fn _ => fn x => c * x) (snd v))
  end;

fun vector_of_list l =
  let val n = length l in
    (n, fold_rev FuncUtil.Intfunc.update (1 upto n ~~ l) FuncUtil.Intfunc.empty): vector
  end;

(* Matrices; again rows and columns indexed from 1.                          *)

fun dimensions (m: matrix) = fst m;

fun row k (m: matrix) : vector =
  let val (_, j) = dimensions m in
    (j,
      FuncUtil.Intpairfunc.fold (fn ((i, j), c) => fn a =>
        if i = k then FuncUtil.Intfunc.update (j, c) a else a) (snd m) FuncUtil.Intfunc.empty)
  end;

(* Monomials.                                                                *)

fun monomial_eval assig m =
  FuncUtil.Ctermfunc.fold (fn (x, k) => fn a => a * rat_pow (FuncUtil.Ctermfunc.apply assig x) k)
    m @1;

val monomial_1 = FuncUtil.Ctermfunc.empty;

fun monomial_var x = FuncUtil.Ctermfunc.onefunc (x, 1);

val monomial_mul =
  FuncUtil.Ctermfunc.combine Integer.add (K false);

fun monomial_multidegree m =
  FuncUtil.Ctermfunc.fold (fn (_, k) => fn a => k + a) m 0;

fun monomial_variables m = FuncUtil.Ctermfunc.dom m;

(* Polynomials.                                                              *)

fun eval assig p =
  FuncUtil.Monomialfunc.fold (fn (m, c) => fn a => a + c * monomial_eval assig m) p @0;

val poly_0 = FuncUtil.Monomialfunc.empty;

fun poly_isconst p =
  FuncUtil.Monomialfunc.fold (fn (m, _) => fn a => FuncUtil.Ctermfunc.is_empty m andalso a)
    p true;

fun poly_var x = FuncUtil.Monomialfunc.onefunc (monomial_var x, @1);

fun poly_const c =
  if c = @0 then poly_0 else FuncUtil.Monomialfunc.onefunc (monomial_1, c);

fun poly_cmul c p =
  if c = @0 then poly_0
  else FuncUtil.Monomialfunc.map (fn _ => fn x => c * x) p;

fun poly_neg p = FuncUtil.Monomialfunc.map (K ~) p;


fun poly_add p1 p2 =
  FuncUtil.Monomialfunc.combine (curry op +) (fn x => x = @0) p1 p2;

fun poly_sub p1 p2 = poly_add p1 (poly_neg p2);

fun poly_cmmul (c,m) p =
  if c = @0 then poly_0
  else
    if FuncUtil.Ctermfunc.is_empty m
    then FuncUtil.Monomialfunc.map (fn _ => fn d => c * d) p
    else
      FuncUtil.Monomialfunc.fold (fn (m', d) => fn a =>
          (FuncUtil.Monomialfunc.update (monomial_mul m m', c * d) a)) p poly_0;

fun poly_mul p1 p2 =
  FuncUtil.Monomialfunc.fold (fn (m, c) => fn a => poly_add (poly_cmmul (c,m) p2) a) p1 poly_0;

fun poly_square p = poly_mul p p;

fun poly_pow p k =
  if k = 0 then poly_const @1
  else if k = 1 then p
  else
    let val q = poly_square(poly_pow p (k div 2))
    in if k mod 2 = 1 then poly_mul p q else q end;

fun multidegree p =
  FuncUtil.Monomialfunc.fold (fn (m, _) => fn a => max (monomial_multidegree m) a) p 0;

fun poly_variables p =
  sort Thm.fast_term_ord
    (FuncUtil.Monomialfunc.fold_rev
      (fn (m, _) => union (is_equal o Thm.fast_term_ord) (monomial_variables m)) p []);

(* Conversion from HOL term.                                                 *)

local
  val neg_tm = \<^cterm>\<open>uminus :: real \<Rightarrow> _\<close>
  val add_tm = \<^cterm>\<open>(+) :: real \<Rightarrow> _\<close>
  val sub_tm = \<^cterm>\<open>(-) :: real \<Rightarrow> _\<close>
  val mul_tm = \<^cterm>\<open>(*) :: real \<Rightarrow> _\<close>
  val inv_tm = \<^cterm>\<open>inverse :: real \<Rightarrow> _\<close>
  val div_tm = \<^cterm>\<open>(/) :: real \<Rightarrow> _\<close>
  val pow_tm = \<^cterm>\<open>(^) :: real \<Rightarrow> _\<close>
  val zero_tm = \<^cterm>\<open>0:: real\<close>
  val is_numeral = can (HOLogic.dest_number o Thm.term_of)
  fun poly_of_term tm =
    if tm aconvc zero_tm then poly_0
    else
      if RealArith.is_ratconst tm
      then poly_const(RealArith.dest_ratconst tm)
      else
       (let
          val (lop, r) = Thm.dest_comb tm
        in
          if lop aconvc neg_tm then poly_neg(poly_of_term r)
          else if lop aconvc inv_tm then
            let val p = poly_of_term r in
              if poly_isconst p
              then poly_const(Rat.inv (eval FuncUtil.Ctermfunc.empty p))
              else error "poly_of_term: inverse of non-constant polyomial"
            end
          else
           (let
              val (opr,l) = Thm.dest_comb lop
            in
              if opr aconvc pow_tm andalso is_numeral r
              then poly_pow (poly_of_term l) ((snd o HOLogic.dest_number o Thm.term_of) r)
              else if opr aconvc add_tm
              then poly_add (poly_of_term l) (poly_of_term r)
              else if opr aconvc sub_tm
              then poly_sub (poly_of_term l) (poly_of_term r)
              else if opr aconvc mul_tm
              then poly_mul (poly_of_term l) (poly_of_term r)
              else if opr aconvc div_tm
              then
                let
                  val p = poly_of_term l
                  val q = poly_of_term r
                in
                  if poly_isconst q
                  then poly_cmul (Rat.inv (eval FuncUtil.Ctermfunc.empty q)) p
                  else error "poly_of_term: division by non-constant polynomial"
                end
              else poly_var tm
            end handle CTERM ("dest_comb",_) => poly_var tm)
        end handle CTERM ("dest_comb",_) => poly_var tm)
in
  val poly_of_term = fn tm =>
    if type_of (Thm.term_of tm) = \<^typ>\<open>real\<close>
    then poly_of_term tm
    else error "poly_of_term: term does not have real type"
end;


(* String of vector (just a list of space-separated numbers). *)

fun sdpa_of_vector (v: vector) =
  let
    val n = dim v
    val strs =
      map (decimalize 20 o (fn i => FuncUtil.Intfunc.tryapplyd (snd v) i @0)) (1 upto n)
  in space_implode " " strs ^ "\n" end;

fun triple_int_ord ((a, b, c), (a', b', c')) =
  prod_ord int_ord (prod_ord int_ord int_ord) ((a, (b, c)), (a', (b', c')));
structure Inttriplefunc = FuncFun(type key = int * int * int val ord = triple_int_ord);


(* Parse back csdp output. *)

local

val decimal_digits = Scan.many1 Symbol.is_ascii_digit
val decimal_nat = decimal_digits >> (#1 o Library.read_int);
val decimal_int = decimal_nat >> Rat.of_int;

val decimal_sig =
  decimal_int -- Scan.option (Scan.$$ "." |-- decimal_digits) >>
  (fn (a, NONE) => a
    | (a, SOME bs) => a + Rat.of_int (#1 (Library.read_int bs)) / rat_pow @10 (length bs));

fun signed neg parse = $$ "-" |-- parse >> neg || $$ "+" |-- parse || parse;
val exponent = ($$ "e" || $$ "E") |-- signed ~ decimal_nat;

val decimal =
  signed ~ decimal_sig -- Scan.optional exponent 0
    >> (fn (a, b) => a * rat_pow @10 b);

val csdp_output =
  decimal -- Scan.repeat (Scan.$$ " " |-- Scan.option decimal) --| Scan.many Symbol.not_eof
    >> (fn (a, bs) => vector_of_list (a :: map_filter I bs));

in

fun parse_csdpoutput s =
  Symbol.scanner "Malformed CSDP output" csdp_output (raw_explode s);

end;


(* Try some apparently sensible scaling first. Note that this is purely to   *)
(* get a cleaner translation to floating-point, and doesn't affect any of    *)
(* the results, in principle. In practice it seems a lot better when there   *)
(* are extreme numbers in the original problem.                              *)

(* Version for (int*int*int) keys *)
local
  fun max_rat x y = if x < y then y else x
  fun common_denominator fld amat acc =
    fld (fn (_,c) => fn a => lcm_rat (denominator_rat c) a) amat acc
  fun maximal_element fld amat acc =
    fld (fn (_,c) => fn maxa => max_rat maxa (abs c)) amat acc
  fun float_of_rat x =
    let val (a,b) = Rat.dest x
    in Real.fromInt a / Real.fromInt b end;
  fun int_of_float x = (trunc x handle Overflow => 0 | Domain => 0)
in

fun tri_scale_then solver (obj:vector) mats =
  let
    val cd1 = fold_rev (common_denominator Inttriplefunc.fold) mats @1
    val cd2 = common_denominator FuncUtil.Intfunc.fold (snd obj) @1
    val mats' = map (Inttriplefunc.map (fn _ => fn x => cd1 * x)) mats
    val obj' = vector_cmul cd2 obj
    val max1 = fold_rev (maximal_element Inttriplefunc.fold) mats' @0
    val max2 = maximal_element FuncUtil.Intfunc.fold (snd obj') @0
    val scal1 = rat_pow @2 (20 - int_of_float(Math.ln (float_of_rat max1) / Math.ln 2.0))
    val scal2 = rat_pow @2 (20 - int_of_float(Math.ln (float_of_rat max2) / Math.ln 2.0))
    val mats'' = map (Inttriplefunc.map (fn _ => fn x => x * scal1)) mats'
    val obj'' = vector_cmul scal2 obj'
  in solver obj'' mats'' end
end;

(* Round a vector to "nice" rationals.                                       *)

fun nice_rational n x = round_rat (n * x) / n;
fun nice_vector n ((d,v) : vector) =
  (d, FuncUtil.Intfunc.fold (fn (i,c) => fn a =>
      let val y = nice_rational n c in
        if c = @0 then a
        else FuncUtil.Intfunc.update (i,y) a
      end) v FuncUtil.Intfunc.empty): vector

fun dest_ord f x = is_equal (f x);

(* Stuff for "equations" ((int*int*int)->num functions).                         *)

fun tri_equation_cmul c eq =
  if c = @0 then Inttriplefunc.empty
  else Inttriplefunc.map (fn _ => fn d => c * d) eq;

fun tri_equation_add eq1 eq2 =
  Inttriplefunc.combine (curry op +) (fn x => x = @0) eq1 eq2;

fun tri_equation_eval assig eq =
  let
    fun value v = Inttriplefunc.apply assig v
  in Inttriplefunc.fold (fn (v, c) => fn a => a + value v * c) eq @0 end;

(* Eliminate all variables, in an essentially arbitrary order.               *)

fun tri_eliminate_all_equations one =
  let
    fun choose_variable eq =
      let val (v,_) = Inttriplefunc.choose eq
      in
        if is_equal (triple_int_ord(v,one)) then
          let
            val eq' = Inttriplefunc.delete_safe v eq
          in
            if Inttriplefunc.is_empty eq' then error "choose_variable"
            else fst (Inttriplefunc.choose eq')
          end
        else v
      end

    fun eliminate dun eqs =
      (case eqs of
        [] => dun
      | eq :: oeqs =>
          if Inttriplefunc.is_empty eq then eliminate dun oeqs
          else
            let
              val v = choose_variable eq
              val a = Inttriplefunc.apply eq v
              val eq' =
                tri_equation_cmul ((Rat.of_int ~1) / a) (Inttriplefunc.delete_safe v eq)
              fun elim e =
                let val b = Inttriplefunc.tryapplyd e v @0 in
                  if b = @0 then e
                  else tri_equation_add e (tri_equation_cmul (~ b / a) eq)
                end
            in
              eliminate (Inttriplefunc.update(v, eq') (Inttriplefunc.map (K elim) dun))
                (map elim oeqs)
            end)
  in
    fn eqs =>
      let
        val assig = eliminate Inttriplefunc.empty eqs
        val vs = Inttriplefunc.fold (fn (_, f) => fn a =>
          remove (dest_ord triple_int_ord) one (Inttriplefunc.dom f) @ a) assig []
      in (distinct (dest_ord triple_int_ord) vs,assig) end
  end;

(* Multiply equation-parametrized poly by regular poly and add accumulator.  *)

fun tri_epoly_pmul p q acc =
  FuncUtil.Monomialfunc.fold (fn (m1, c) => fn a =>
    FuncUtil.Monomialfunc.fold (fn (m2, e) => fn b =>
      let
        val m =  monomial_mul m1 m2
        val es = FuncUtil.Monomialfunc.tryapplyd b m Inttriplefunc.empty
      in
        FuncUtil.Monomialfunc.update (m,tri_equation_add (tri_equation_cmul c e) es) b
      end) q a) p acc;

(* Hence produce the "relevant" monomials: those whose squares lie in the    *)
(* Newton polytope of the monomials in the input. (This is enough according  *)
(* to Reznik: "Extremal PSD forms with few terms", Duke Math. Journal,       *)
(* vol 45, pp. 363--374, 1978.                                               *)
(*                                                                           *)
(* These are ordered in sort of decreasing degree. In particular the         *)
(* constant monomial is last; this gives an order in diagonalization of the  *)
(* quadratic form that will tend to display constants.                       *)

(* Diagonalize (Cholesky/LDU) the matrix corresponding to a quadratic form.  *)

local
  fun diagonalize n i m =
    if FuncUtil.Intpairfunc.is_empty (snd m) then []
    else
      let
        val a11 = FuncUtil.Intpairfunc.tryapplyd (snd m) (i,i) @0
      in
        if a11 < @0 then raise Failure "diagonalize: not PSD"
        else if a11 = @0 then
          if FuncUtil.Intfunc.is_empty (snd (row i m))
          then diagonalize n (i + 1) m
          else raise Failure "diagonalize: not PSD ___ "
        else
          let
            val v = row i m
            val v' =
              (fst v, FuncUtil.Intfunc.fold (fn (i, c) => fn a =>
                let val y = c / a11
                in if y = @0 then a else FuncUtil.Intfunc.update (i,y) a
                end) (snd v) FuncUtil.Intfunc.empty)
            fun upt0 x y a =
              if y = @0 then a
              else FuncUtil.Intpairfunc.update (x,y) a
            val m' =
              ((n, n),
                iter (i + 1, n) (fn j =>
                  iter (i + 1, n) (fn k =>
                    (upt0 (j, k)
                      (FuncUtil.Intpairfunc.tryapplyd (snd m) (j, k) @0 -
                        FuncUtil.Intfunc.tryapplyd (snd v) j @0 *
                        FuncUtil.Intfunc.tryapplyd (snd v') k @0))))
                    FuncUtil.Intpairfunc.empty)
          in (a11, v') :: diagonalize n (i + 1) m' end
      end
in
  fun diag m =
    let
      val nn = dimensions m
      val n = fst nn
    in
      if snd nn <> n then error "diagonalize: non-square matrix"
      else diagonalize n 1 m
    end
end;

(* Enumeration of monomials with given multidegree bound.                    *)

fun enumerate_monomials d vars =
  if d < 0 then []
  else if d = 0 then [FuncUtil.Ctermfunc.empty]
  else if null vars then [monomial_1]
  else
    let val alts =
      map_range (fn k =>
        let
          val oths = enumerate_monomials (d - k) (tl vars)
        in map (fn ks => if k = 0 then ks else FuncUtil.Ctermfunc.update (hd vars, k) ks) oths end)
        (d + 1)
  in flat alts end;

(* Enumerate products of distinct input polys with degree <= d.              *)
(* We ignore any constant input polynomials.                                 *)
(* Give the output polynomial and a record of how it was derived.            *)

fun enumerate_products d pols =
  if d = 0 then [(poly_const @1, RealArith.Rational_lt @1)]
  else if d < 0 then []
  else
    (case pols of
      [] => [(poly_const @1, RealArith.Rational_lt @1)]
    | (p, b) :: ps =>
        let val e = multidegree p in
          if e = 0 then enumerate_products d ps
          else
            enumerate_products d ps @
            map (fn (q, c) => (poly_mul p q, RealArith.Product (b, c)))
              (enumerate_products (d - e) ps)
        end)

(* Convert regular polynomial. Note that we treat (0,0,0) as -1.             *)

fun epoly_of_poly p =
  FuncUtil.Monomialfunc.fold (fn (m, c) => fn a =>
      FuncUtil.Monomialfunc.update (m, Inttriplefunc.onefunc ((0, 0, 0), ~ c)) a)
    p FuncUtil.Monomialfunc.empty;

(* String for block diagonal matrix numbered k.                              *)

fun sdpa_of_blockdiagonal k m =
  let
    val pfx = string_of_int k ^" "
    val ents =
      Inttriplefunc.fold
        (fn ((b, i, j), c) => fn a => if i > j then a else ((b, i, j), c) :: a)
        m []
    val entss = sort (triple_int_ord o apply2 fst) ents
  in
    fold_rev (fn ((b,i,j),c) => fn a =>
      pfx ^ string_of_int b ^ " " ^ string_of_int i ^ " " ^ string_of_int j ^
      " " ^ decimalize 20 c ^ "\n" ^ a) entss ""
  end;

(* SDPA for problem using block diagonal (i.e. multiple SDPs)                *)

fun sdpa_of_blockproblem nblocks blocksizes obj mats =
  let val m = length mats - 1
  in
    string_of_int m ^ "\n" ^
    string_of_int nblocks ^ "\n" ^
    (space_implode " " (map string_of_int blocksizes)) ^
    "\n" ^
    sdpa_of_vector obj ^
    fold_rev (fn (k, m) => fn a => sdpa_of_blockdiagonal (k - 1) m ^ a)
      (1 upto length mats ~~ mats) ""
  end;

(* Run prover on a problem in block diagonal form.                       *)

fun run_blockproblem prover nblocks blocksizes obj mats =
  parse_csdpoutput (prover (sdpa_of_blockproblem nblocks blocksizes obj mats))

(* 3D versions of matrix operations to consider blocks separately.           *)

val bmatrix_add = Inttriplefunc.combine (curry op +) (fn x => x = @0);
fun bmatrix_cmul c bm =
  if c = @0 then Inttriplefunc.empty
  else Inttriplefunc.map (fn _ => fn x => c * x) bm;

val bmatrix_neg = bmatrix_cmul (Rat.of_int ~1);

(* Smash a block matrix into components.                                     *)

fun blocks blocksizes bm =
  map (fn (bs, b0) =>
    let
      val m =
        Inttriplefunc.fold
          (fn ((b, i, j), c) => fn a =>
            if b = b0 then FuncUtil.Intpairfunc.update ((i, j), c) a else a)
        bm FuncUtil.Intpairfunc.empty
      val _ = FuncUtil.Intpairfunc.fold (fn ((i, j), _) => fn a => max a (max i j)) m 0
    in (((bs, bs), m): matrix) end)
  (blocksizes ~~ (1 upto length blocksizes));

(* FIXME : Get rid of this !!!*)
local
  fun tryfind_with msg _ [] = raise Failure msg
    | tryfind_with _ f (x::xs) = (f x handle Failure s => tryfind_with s f xs);
in
  fun tryfind f = tryfind_with "tryfind" f
end

(* Positiv- and Nullstellensatz. Flag "linf" forces a linear representation. *)

fun real_positivnullstellensatz_general ctxt prover linf d eqs leqs pol =
  let
    val vars =
      fold_rev (union (op aconvc) o poly_variables)
        (pol :: eqs @ map fst leqs) []
    val monoid =
      if linf then
        (poly_const @1, RealArith.Rational_lt @1)::
        (filter (fn (p,_) => multidegree p <= d) leqs)
      else enumerate_products d leqs
    val nblocks = length monoid
    fun mk_idmultiplier k p =
      let
        val e = d - multidegree p
        val mons = enumerate_monomials e vars
        val nons = mons ~~ (1 upto length mons)
      in
        (mons,
          fold_rev (fn (m, n) =>
            FuncUtil.Monomialfunc.update (m, Inttriplefunc.onefunc ((~k, ~n, n), @1)))
          nons FuncUtil.Monomialfunc.empty)
      end

    fun mk_sqmultiplier k (p,_) =
      let
        val e = (d - multidegree p) div 2
        val mons = enumerate_monomials e vars
        val nons = mons ~~ (1 upto length mons)
      in
        (mons,
          fold_rev (fn (m1, n1) =>
            fold_rev (fn (m2, n2) => fn a =>
              let val m = monomial_mul m1 m2 in
                if n1 > n2 then a
                else
                  let
                    val c = if n1 = n2 then @1 else @2
                    val e = FuncUtil.Monomialfunc.tryapplyd a m Inttriplefunc.empty
                  in
                    FuncUtil.Monomialfunc.update
                      (m, tri_equation_add (Inttriplefunc.onefunc ((k, n1, n2), c)) e) a
                  end
              end) nons) nons FuncUtil.Monomialfunc.empty)
      end

    val (sqmonlist,sqs) = split_list (map2 mk_sqmultiplier (1 upto length monoid) monoid)
    val (_(*idmonlist*),ids) =  split_list (map2 mk_idmultiplier (1 upto length eqs) eqs)
    val blocksizes = map length sqmonlist
    val bigsum =
      fold_rev (fn (p, q) => fn a => tri_epoly_pmul p q a) (eqs ~~ ids)
        (fold_rev (fn ((p, _), s) => fn a => tri_epoly_pmul p s a) (monoid ~~ sqs)
          (epoly_of_poly (poly_neg pol)))
    val eqns = FuncUtil.Monomialfunc.fold (fn (_, e) => fn a => e :: a) bigsum []
    val (pvs, assig) = tri_eliminate_all_equations (0, 0, 0) eqns
    val qvars = (0, 0, 0) :: pvs
    val allassig =
      fold_rev (fn v => Inttriplefunc.update (v, (Inttriplefunc.onefunc (v, @1)))) pvs assig
    fun mk_matrix v =
      Inttriplefunc.fold (fn ((b, i, j), ass) => fn m =>
          if b < 0 then m
          else
            let val c = Inttriplefunc.tryapplyd ass v @0 in
              if c = @0 then m
              else Inttriplefunc.update ((b, j, i), c) (Inttriplefunc.update ((b, i, j), c) m)
            end)
        allassig Inttriplefunc.empty
    val diagents =
      Inttriplefunc.fold
        (fn ((b, i, j), e) => fn a => if b > 0 andalso i = j then tri_equation_add e a else a)
        allassig Inttriplefunc.empty

    val mats = map mk_matrix qvars
    val obj =
      (length pvs,
        itern 1 pvs (fn v => fn i =>
          FuncUtil.Intfunc.updatep iszero (i,Inttriplefunc.tryapplyd diagents v @0))
          FuncUtil.Intfunc.empty)
    val raw_vec =
      if null pvs then vector_0 0
      else tri_scale_then (run_blockproblem prover nblocks blocksizes) obj mats
    fun int_element (_, v) i = FuncUtil.Intfunc.tryapplyd v i @0

    fun find_rounding d =
      let
        val _ =
          debug_message ctxt (fn () => "Trying rounding with limit "^Rat.string_of_rat d ^ "\n")
        val vec = nice_vector d raw_vec
        val blockmat =
          iter (1, dim vec)
            (fn i => fn a => bmatrix_add (bmatrix_cmul (int_element vec i) (nth mats i)) a)
            (bmatrix_neg (nth mats 0))
        val allmats = blocks blocksizes blockmat
      in (vec, map diag allmats) end
    val (vec, ratdias) =
      if null pvs then find_rounding @1
      else tryfind find_rounding (map Rat.of_int (1 upto 31) @ map (rat_pow @2) (5 upto 66))
    val newassigs =
      fold_rev (fn k => Inttriplefunc.update (nth pvs (k - 1), int_element vec k))
        (1 upto dim vec) (Inttriplefunc.onefunc ((0, 0, 0), Rat.of_int ~1))
    val finalassigs =
      Inttriplefunc.fold (fn (v, e) => fn a =>
        Inttriplefunc.update (v, tri_equation_eval newassigs e) a) allassig newassigs
    fun poly_of_epoly p =
      FuncUtil.Monomialfunc.fold (fn (v, e) => fn a =>
          FuncUtil.Monomialfunc.updatep iszero (v, tri_equation_eval finalassigs e) a)
        p FuncUtil.Monomialfunc.empty
    fun mk_sos mons =
      let
        fun mk_sq (c, m) =
          (c, fold_rev (fn k => fn a =>
              FuncUtil.Monomialfunc.updatep iszero (nth mons (k - 1), int_element m k) a)
            (1 upto length mons) FuncUtil.Monomialfunc.empty)
      in map mk_sq end
    val sqs = map2 mk_sos sqmonlist ratdias
    val cfs = map poly_of_epoly ids
    val msq = filter (fn (_, b) => not (null b)) (map2 pair monoid sqs)
    fun eval_sq sqs = fold_rev (fn (c, q) => poly_add (poly_cmul c (poly_mul q q))) sqs poly_0
    val sanity =
      fold_rev (fn ((p, _), s) => poly_add (poly_mul p (eval_sq s))) msq
        (fold_rev (fn (p, q) => poly_add (poly_mul p q)) (cfs ~~ eqs) (poly_neg pol))
  in
    if not(FuncUtil.Monomialfunc.is_empty sanity) then raise Sanity
    else (cfs, map (fn (a, b) => (snd a, b)) msq)
  end


(* Iterative deepening.                                                      *)

fun deepen ctxt f n =
  (trace_message ctxt (fn () => "Searching with depth limit " ^ string_of_int n);
    (f n handle Failure s =>
      (trace_message ctxt (fn () => "failed with message: " ^ s); deepen ctxt f (n + 1))));


(* Map back polynomials and their composites to a positivstellensatz.        *)

fun cterm_of_sqterm (c, p) = RealArith.Product (RealArith.Rational_lt c, RealArith.Square p);

fun cterm_of_sos (pr,sqs) =
  if null sqs then pr
  else RealArith.Product (pr, foldr1 RealArith.Sum (map cterm_of_sqterm sqs));

(* Interface to HOL.                                                         *)
local
  open Conv
  val concl = Thm.dest_arg o Thm.cprop_of
in
(* FIXME: Replace tryfind by get_first !! *)
fun real_nonlinear_prover proof_method ctxt =
  let
    val {add = _, mul = _, neg = _, pow = _, sub = _, main = real_poly_conv} =
      Semiring_Normalizer.semiring_normalizers_ord_wrapper ctxt
        (the (Semiring_Normalizer.match ctxt \<^cterm>\<open>(0::real) + 1\<close>))
        Thm.term_ord
    fun mainf cert_choice translator (eqs, les, lts) =
      let
        val eq0 = map (poly_of_term o Thm.dest_arg1 o concl) eqs
        val le0 = map (poly_of_term o Thm.dest_arg o concl) les
        val lt0 = map (poly_of_term o Thm.dest_arg o concl) lts
        val eqp0 = map_index (fn (i, t) => (t,RealArith.Axiom_eq i)) eq0
        val lep0 = map_index (fn (i, t) => (t,RealArith.Axiom_le i)) le0
        val ltp0 = map_index (fn (i, t) => (t,RealArith.Axiom_lt i)) lt0
        val (keq,eq) = List.partition (fn (p, _) => multidegree p = 0) eqp0
        val (klep,lep) = List.partition (fn (p, _) => multidegree p = 0) lep0
        val (kltp,ltp) = List.partition (fn (p, _) => multidegree p = 0) ltp0
        fun trivial_axiom (p, ax) =
          (case ax of
            RealArith.Axiom_eq n =>
              if eval FuncUtil.Ctermfunc.empty p <> @0 then nth eqs n
              else raise Failure "trivial_axiom: Not a trivial axiom"
          | RealArith.Axiom_le n =>
              if eval FuncUtil.Ctermfunc.empty p < @0 then nth les n
              else raise Failure "trivial_axiom: Not a trivial axiom"
          | RealArith.Axiom_lt n =>
              if eval FuncUtil.Ctermfunc.empty p <= @0 then nth lts n
              else raise Failure "trivial_axiom: Not a trivial axiom"
          | _ => error "trivial_axiom: Not a trivial axiom")
      in
        let val th = tryfind trivial_axiom (keq @ klep @ kltp) in
          (fconv_rule (arg_conv (arg1_conv (real_poly_conv ctxt))
            then_conv Numeral_Simprocs.field_comp_conv ctxt) th,
            RealArith.Trivial)
        end handle Failure _ =>
          let
            val proof =
              (case proof_method of
                Certificate certs =>
                  (* choose certificate *)
                  let
                    fun chose_cert [] (RealArith.Cert c) = c
                      | chose_cert (RealArith.Left::s) (RealArith.Branch (l, _)) = chose_cert s l
                      | chose_cert (RealArith.Right::s) (RealArith.Branch (_, r)) = chose_cert s r
                      | chose_cert _ _ = error "certificate tree in invalid form"
                  in
                    chose_cert cert_choice certs
                  end
              | Prover prover =>
                  (* call prover *)
                  let
                    val pol = fold_rev poly_mul (map fst ltp) (poly_const @1)
                    val leq = lep @ ltp
                    fun tryall d =
                      let
                        val e = multidegree pol
                        val k = if e = 0 then 0 else d div e
                        val eq' = map fst eq
                      in
                        tryfind (fn i =>
                            (d, i, real_positivnullstellensatz_general ctxt prover false d eq' leq
                              (poly_neg(poly_pow pol i))))
                          (0 upto k)
                      end
                    val (_,i,(cert_ideal,cert_cone)) = deepen ctxt tryall 0
                    val proofs_ideal =
                      map2 (fn q => fn (_,ax) => RealArith.Eqmul(q,ax)) cert_ideal eq
                    val proofs_cone = map cterm_of_sos cert_cone
                    val proof_ne =
                      if null ltp then RealArith.Rational_lt @1
                      else
                        let val p = foldr1 RealArith.Product (map snd ltp) in
                          funpow i (fn q => RealArith.Product (p, q))
                            (RealArith.Rational_lt @1)
                        end
                  in
                    foldr1 RealArith.Sum (proof_ne :: proofs_ideal @ proofs_cone)
                  end)
          in
            (translator (eqs,les,lts) proof, RealArith.Cert proof)
          end
      end
  in mainf end
end

(* FIXME : This is very bad!!!*)
fun subst_conv eqs t =
  let
    val t' = fold (Thm.lambda o Thm.lhs_of) eqs t
  in
    Conv.fconv_rule (Thm.beta_conversion true)
      (fold (fn a => fn b => Thm.combination b a) eqs (Thm.reflexive t'))
  end

(* A wrapper that tries to substitute away variables first.                  *)

local
  open Conv
  val concl = Thm.dest_arg o Thm.cprop_of
  val shuffle1 =
    fconv_rule (rewr_conv @{lemma "(a + x == y) == (x == y - (a::real))"
      by (atomize (full)) (simp add: field_simps)})
  val shuffle2 =
    fconv_rule (rewr_conv @{lemma "(x + a == y) ==  (x == y - (a::real))"
      by (atomize (full)) (simp add: field_simps)})
  fun substitutable_monomial fvs tm =
    (case Thm.term_of tm of
      Free (_, \<^typ>\<open>real\<close>) =>
        if not (member (op aconvc) fvs tm) then (@1, tm)
        else raise Failure "substitutable_monomial"
    | \<^term>\<open>(*) :: real \<Rightarrow> _\<close> $ _ $ (Free _) =>
        if RealArith.is_ratconst (Thm.dest_arg1 tm) andalso
          not (member (op aconvc) fvs (Thm.dest_arg tm))
        then (RealArith.dest_ratconst (Thm.dest_arg1 tm), Thm.dest_arg tm)
        else raise Failure "substitutable_monomial"
    | \<^term>\<open>(+) :: real \<Rightarrow> _\<close>$_$_ =>
         (substitutable_monomial (merge (op aconvc) (fvs, Drule.cterm_frees_of (Thm.dest_arg tm)))
           (Thm.dest_arg1 tm)
           handle Failure _ =>
            substitutable_monomial (merge (op aconvc) (fvs, Drule.cterm_frees_of (Thm.dest_arg1 tm)))
              (Thm.dest_arg tm))
    | _ => raise Failure "substitutable_monomial")

  fun isolate_variable v th =
    let
      val w = Thm.dest_arg1 (Thm.cprop_of th)
    in
      if v aconvc w then th
      else
        (case Thm.term_of w of
          \<^term>\<open>(+) :: real \<Rightarrow> _\<close> $ _ $ _ =>
            if Thm.dest_arg1 w aconvc v then shuffle2 th
            else isolate_variable v (shuffle1 th)
        | _ => error "isolate variable : This should not happen?")
   end
in

fun real_nonlinear_subst_prover prover ctxt =
  let
    val {add = _, mul = real_poly_mul_conv, neg = _, pow = _, sub = _, main = real_poly_conv} =
      Semiring_Normalizer.semiring_normalizers_ord_wrapper ctxt
        (the (Semiring_Normalizer.match ctxt \<^cterm>\<open>(0::real) + 1\<close>))
        Thm.term_ord

    fun make_substitution th =
      let
        val (c,v) = substitutable_monomial [] (Thm.dest_arg1(concl th))
        val th1 =
          Drule.arg_cong_rule
            (Thm.apply \<^cterm>\<open>(*) :: real \<Rightarrow> _\<close> (RealArith.cterm_of_rat (Rat.inv c)))
            (mk_meta_eq th)
        val th2 = fconv_rule (binop_conv (real_poly_mul_conv ctxt)) th1
      in fconv_rule (arg_conv (real_poly_conv ctxt)) (isolate_variable v th2) end

    fun oprconv cv ct =
      let val g = Thm.dest_fun2 ct in
        if g aconvc \<^cterm>\<open>(\<le>) :: real \<Rightarrow> _\<close> orelse g aconvc \<^cterm>\<open>(<) :: real \<Rightarrow> _\<close>
        then arg_conv cv ct else arg1_conv cv ct
      end
    fun mainf cert_choice translator =
      let
        fun substfirst (eqs, les, lts) =
          (let
              val eth = tryfind make_substitution eqs
              val modify =
                fconv_rule (arg_conv (oprconv(subst_conv [eth] then_conv (real_poly_conv ctxt))))
            in
              substfirst
                (filter_out
                  (fn t => (Thm.dest_arg1 o Thm.dest_arg o Thm.cprop_of) t aconvc \<^cterm>\<open>0::real\<close>)
                  (map modify eqs),
                  map modify les,
                  map modify lts)
            end handle Failure  _ =>
              real_nonlinear_prover prover ctxt cert_choice translator (rev eqs, rev les, rev lts))
      in substfirst end
  in mainf end

(* Overall function. *)

fun real_sos prover ctxt =
  RealArith.gen_prover_real_arith ctxt (real_nonlinear_subst_prover prover ctxt)

end;

val known_sos_constants =
  [\<^term>\<open>(\<Longrightarrow>)\<close>, \<^term>\<open>Trueprop\<close>,
   \<^term>\<open>HOL.False\<close>, \<^term>\<open>HOL.implies\<close>, \<^term>\<open>HOL.conj\<close>, \<^term>\<open>HOL.disj\<close>,
   \<^term>\<open>Not\<close>, \<^term>\<open>(=) :: bool \<Rightarrow> _\<close>,
   \<^term>\<open>All :: (real \<Rightarrow> _) \<Rightarrow> _\<close>, \<^term>\<open>Ex :: (real \<Rightarrow> _) \<Rightarrow> _\<close>,
   \<^term>\<open>(=) :: real \<Rightarrow> _\<close>, \<^term>\<open>(<) :: real \<Rightarrow> _\<close>,
   \<^term>\<open>(\<le>) :: real \<Rightarrow> _\<close>,
   \<^term>\<open>(+) :: real \<Rightarrow> _\<close>, \<^term>\<open>(-) :: real \<Rightarrow> _\<close>,
   \<^term>\<open>(*) :: real \<Rightarrow> _\<close>, \<^term>\<open>uminus :: real \<Rightarrow> _\<close>,
   \<^term>\<open>(/) :: real \<Rightarrow> _\<close>, \<^term>\<open>inverse :: real \<Rightarrow> _\<close>,
   \<^term>\<open>(^) :: real \<Rightarrow> _\<close>, \<^term>\<open>abs :: real \<Rightarrow> _\<close>,
   \<^term>\<open>min :: real \<Rightarrow> _\<close>, \<^term>\<open>max :: real \<Rightarrow> _\<close>,
   \<^term>\<open>0::real\<close>, \<^term>\<open>1::real\<close>,
   \<^term>\<open>numeral :: num \<Rightarrow> nat\<close>,
   \<^term>\<open>numeral :: num \<Rightarrow> real\<close>,
   \<^term>\<open>Num.Bit0\<close>, \<^term>\<open>Num.Bit1\<close>, \<^term>\<open>Num.One\<close>];

fun check_sos kcts ct =
  let
    val t = Thm.term_of ct
    val _ =
      if not (null (Term.add_tfrees t []) andalso null (Term.add_tvars t []))
      then error "SOS: not sos. Additional type varables"
      else ()
    val fs = Term.add_frees t []
    val _ =
      if exists (fn ((_,T)) => not (T = \<^typ>\<open>real\<close>)) fs
      then error "SOS: not sos. Variables with type not real"
      else ()
    val vs = Term.add_vars t []
    val _ =
      if exists (fn ((_,T)) => not (T = \<^typ>\<open>real\<close>)) vs
      then error "SOS: not sos. Variables with type not real"
      else ()
    val ukcs = subtract (fn (t,p) => Const p aconv t) kcts (Term.add_consts t [])
    val _ =
      if null ukcs then ()
      else error ("SOSO: Unknown constants in Subgoal:" ^ commas (map fst ukcs))
  in () end

fun core_sos_tac print_cert prover = SUBPROOF (fn {concl, context = ctxt, ...} =>
  let
    val _ = check_sos known_sos_constants concl
    val (th, certificates) = real_sos prover ctxt (Thm.dest_arg concl)
    val _ = print_cert certificates
  in resolve_tac ctxt [th] 1 end);

fun default_SOME _ NONE v = SOME v
  | default_SOME _ (SOME v) _ = SOME v;

fun lift_SOME f NONE a = f a
  | lift_SOME _ (SOME a) _ = SOME a;


local
  val is_numeral = can (HOLogic.dest_number o Thm.term_of)
in
  fun get_denom b ct =
    (case Thm.term_of ct of
      \<^term>\<open>(/) :: real \<Rightarrow> _\<close> $ _ $ _ =>
        if is_numeral (Thm.dest_arg ct)
        then get_denom b (Thm.dest_arg1 ct)
        else default_SOME (get_denom b) (get_denom b (Thm.dest_arg ct)) (Thm.dest_arg ct, b)
    | \<^term>\<open>(<) :: real \<Rightarrow> _\<close> $ _ $ _ =>
        lift_SOME (get_denom true) (get_denom true (Thm.dest_arg ct)) (Thm.dest_arg1 ct)
    | \<^term>\<open>(\<le>) :: real \<Rightarrow> _\<close> $ _ $ _ =>
        lift_SOME (get_denom true) (get_denom true (Thm.dest_arg ct)) (Thm.dest_arg1 ct)
    | _ $ _ => lift_SOME (get_denom b) (get_denom b (Thm.dest_fun ct)) (Thm.dest_arg ct)
    | _ => NONE)
end;

val sos_ss = @{context}
  |> fold Simplifier.add_simp @{thms field_simps}
  |> Simplifier.del_simp @{thm mult_nonneg_nonneg}
  |> Simplifier.simpset_of;

fun elim_one_denom_tac ctxt = CSUBGOAL (fn (P, i) =>
  (case get_denom false P of
    NONE => no_tac
  | SOME (d, ord) =>
      let
        val simp_ctxt = ctxt
          |> Simplifier.put_simpset sos_ss
        val th =
          Thm.instantiate' [] [SOME d, SOME (Thm.dest_arg P)]
            (if ord then @{lemma "(d=0 \<longrightarrow> P) \<and> (d>0 \<longrightarrow> P) \<and> (d<(0::real) \<longrightarrow> P) \<Longrightarrow> P" by auto}
             else @{lemma "(d=0 \<longrightarrow> P) \<and> (d \<noteq> (0::real) \<longrightarrow> P) \<Longrightarrow> P" by blast})
      in resolve_tac ctxt [th] i THEN Simplifier.asm_full_simp_tac simp_ctxt i end));

fun elim_denom_tac ctxt i = REPEAT (elim_one_denom_tac ctxt i);

fun sos_tac print_cert prover ctxt =
  Object_Logic.full_atomize_tac ctxt THEN'
  elim_denom_tac ctxt THEN'
  core_sos_tac print_cert prover ctxt;

end;
