(* ========================================================================= *)
(* METIS TESTS                                                               *)
(* Copyright (c) 2004-2006 Joe Hurd                                          *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Dummy versions of Moscow ML declarations to stop MLton barfing.           *)
(* ------------------------------------------------------------------------- *)

(*mlton
val quotation = ref true;
val quietdec  = ref true;
val loadPath  = ref ([] : string list);
val load = fn (_ : string) => ();
val installPP = fn (_ : 'a Parser.pp) => ();
*)

(* ------------------------------------------------------------------------- *)
(* Load and open some useful modules                                         *)
(* ------------------------------------------------------------------------- *)

val () = loadPath := !loadPath @ ["../bin/mosml"];
val () = app load ["Tptp"];

open Useful;

val () = installPP Term.pp;
val () = installPP Formula.pp;
val () = installPP Subst.pp;
val () = installPP Thm.pp;
val () = installPP Rewrite.pp;
val () = installPP Clause.pp;

val time = Portable.time;

(*DEBUG
  val () = print "Running in DEBUG mode.\n"
*)

(* ------------------------------------------------------------------------- *)
(* Problem data.                                                             *)
(* ------------------------------------------------------------------------- *)

val ref oldquietdec = quietdec;
val () = quietdec := true;
val () = quotation := true;
use "../src/problems.sml";
val () = quietdec := oldquietdec;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun partialOrderToString (SOME LESS) = "SOME LESS"
  | partialOrderToString (SOME GREATER) = "SOME GREATER"
  | partialOrderToString (SOME EQUAL) = "SOME EQUAL"
  | partialOrderToString NONE = "NONE";

fun SAY s =
  print
  ("-------------------------------------" ^
   "-------------------------------------\n" ^ s ^ "\n\n");

fun printval p x = (print (PP.pp_to_string 79 p x ^ "\n\n"); x);

val pvBool = printval Parser.ppBool
and pvPo = printval (Parser.ppMap partialOrderToString Parser.ppString)
and pvFm = printval Formula.pp
and pvFms = printval (Parser.ppList Formula.pp)
and pvThm = printval Thm.pp
and pvEqn : Rule.equation -> Rule.equation = printval (Parser.ppMap snd Thm.pp)
and pvNet = printval (LiteralNet.pp Parser.ppInt)
and pvRw = printval Rewrite.pp
and pvU = printval Units.pp
and pvLits = printval LiteralSet.pp
and pvCl = printval Clause.pp
and pvCls = printval (Parser.ppList Clause.pp);

val T = Term.parse
and A = Atom.parse
and L = Literal.parse
and F = Formula.parse
and S = Subst.fromList;
val AX = Thm.axiom o LiteralSet.fromList o map L;
fun CL q =
    Clause.mk {parameters = Clause.default, id = Clause.newId (), thm = AX q};
val Q = (fn th => (Thm.destUnitEq th, th)) o AX o singleton
and U = (fn th => (Thm.destUnit th, th)) o AX o singleton;

fun test_fun p r a =
  if r = a then p a ^ "\n" else
    (print ("\n\n" ^
            "test: should have\n-->" ^ p r ^ "<--\n\n" ^
            "test: actually have\n-->" ^ p a ^ "<--\n\n");
     raise Fail "test: failed a test");

fun test p r a = print (test_fun p r a ^ "\n");

val test_tm = test Term.toString o Term.parse;

val test_fm = test Formula.toString o Formula.parse;

fun test_id p f a = test p a (f a);

fun chop_newline s =
    if String.sub (s,0) = #"\n" then String.extract (s,1,NONE) else s;

fun unquote (QUOTE q) = q
  | unquote (ANTIQUOTE _) = raise Fail "unquote";

(***
fun quick_prove slv goal =
  let
    val {thms,hyps} = Thm.clauses goal
    val solv = initialize slv
  in
    (printval (pp_map Option.isSome pp_bool) o (time o try) refute)
    (solv {limit = unlimited, thms = thms, hyps = hyps})
  end;

val meson_prove =
    quick_prove (Solver.apply_sos_filter Solver.all_negative meson);
val resolution_prove = quick_prove resolution;
val metis_prove = quick_prove metis;

fun quick_solve slv n ruls =
  printval (pp_list (pp_list pp_thm)) o
  (time o try)
  (solve
   (initialize slv {limit = unlimited, thms = axiomatize ruls, hyps = []}) n);

val meson_solve = quick_solve meson 1;
val prolog_solve = quick_solve prolog 1;
val resolution_solve = quick_solve resolution 1;
val metis_solve = quick_solve metis 1;

val pfm  = printval pp_formula;
val pfms = printval (pp_list pp_formula);
***)

(* ------------------------------------------------------------------------- *)
val () = SAY "The parser and pretty-printer";
(* ------------------------------------------------------------------------- *)

fun prep l = (chop_newline o String.concat o map unquote) l;

fun mini_print n = withRef (Parser.lineLength,n) Formula.toString;

fun testlen_pp n q =
    (fn s => test_fun I s ((mini_print n o Formula.fromString) s))
      (prep q);

fun test_pp q = print (testlen_pp 40 q ^ "\n");

val () = test_pp `3 = f x`;

val () = test_pp `f x y = y`;

val () = test_pp `P x y`;

val () = test_pp `P (f x) y`;

val () = test_pp `f x = 3`;

val () = test_pp `!x. P x y`;

val () = test_pp `!x y. P x y`;

val () = test_pp `!x y z. P x y z`;

val () = test_pp `x = y`;

val () = test_pp `x = 3`;

val () = test_pp `x + y = y`;

val () = test_pp `x / y * z = w`;

val () = test_pp `x * y * z = x * (y * z)`;

val () = test_pp `!x. ?y. x <= y /\ y <= x`;

val () = test_pp `?x. !y. x + y = y /\ y <= x`;

val () = test_pp `p /\ q \/ r /\ p ==> q <=> p`;

val () = test_pp `p`;

val () = test_pp `~!x. bool x`;

val () = test_pp `p ==> !x. bool x`;

val () = test_pp `p ==> ~!x. bool x`;

val () = test_pp `~!x. bool x`;

val () = test_pp `~~!x. bool x`;

val () = test_pp `hello + there <> everybody`;

val () = test_pp `!x y. ?z. x < z /\ y < z`;

val () = test_pp `~(!x. P x) <=> ?y. ~P y`;

val () = test_pp `?y. x < y ==> !v. ?w. x * v < y * w`;

val () = test_pp `(<=)`;

val () = test_pp `(<=) <= b`;

val () = test_pp `(<=) <= (+)`;

val () = test_pp `(<=) x`;

val () = test_pp `(<=) <= (+) x`;

val () = test_pp `~B (P % ((,) % c_a % v_b))`;

val () = test_pp `B ((<=) % 0 % (LENGTH % NIL))`;

val () = test_pp `~(a = b)`;

val () = test_pp `!x. p x ==> !y. p y`;

val () = test_pp `(!x. p x) ==> !y. p y`;

val () = test_pp `!x. ~~x = x`;

val () = test_pp `x + (y + z) = a`;

val () = test_pp `(x @ y) @ z = a`;

val () = test_pp `p ((a @ a) @ a = a)`;

val () = test_pp `!x y z. (x @ y) @ z = (x @ z) @ y @ z`;

val () = test_pp `~(!x. q x) /\ p`;

val () = test_pp `!x. f (~~x) b (~c)`;

val () = test_pp `p ==> ~(a /\ b)`;

val () = test_pp `!water. drinks (water)`;

val () = test_pp `!vat water. drinks ((vat) p x (water))`;

val () = test_pp `!x y. ~{x < y} /\ T`;

val () = test_pp `[3]`;

val () = test_pp `
!x y z. ?x' y' z'.
  P x y z ==> P x' y' z'`;

val () = test_pp `
(!x. P x ==> !x. Q x) /\
((!x. Q x \/ R x) ==> ?x. Q x /\ R x) /\
((?x. R x) ==> !x. L x ==> M x) ==>
!x. P x /\ L x ==> M x`;

val () = test_pp `
!x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
  x12 x13 x14 x15 x16 x17 x18 x19 x20
  x21 x22 x23 x24 x25 x26 x27 x28 x29
  x30 x31 x32. ?y0 y1 y2 y3 y4 y5 y6 y7.
  P`;

val () = test_pp `
!x x x x x x x x x x x x x x x x x x x x
  x x x x x x x x x x. ?y y y y y y y y
  y y y y y y y y y y y.
  P (x, y) /\ P (x, y) /\ P (x, y) /\
  P (x, y) /\ P (x, y) /\ P (x, y) /\
  P (x, y) /\ P (x, y) /\ P (x, y) /\
  P (x, y) /\ P (x, y) /\ P (x, y) /\
  P (x, y) /\ P (x, y) /\
  ~~~~~~~~~~~~~f
                 (f (f (f x y) (f x y))
                    (f (f x y) (f x y)))
                 (f (f (f x y) (f x y))
                    (f (f x y) (f x y)))`;

val () = test_pp `
(!x. x = x) /\
(!x y. ~(x = y) \/ y = x) /\
(!x y z.
   ~(x = y) \/ ~(y = z) \/ x = z) /\
(!x y z. b . x . y . z = x . (y . z)) /\
(!x y. t . x . y = y . x) /\
(!x y z. ~(x = y) \/ x . z = y . z) /\
(!x y z. ~(x = y) \/ z . x = z . y) ==>
~(b . (b . (t . b) . b) . t . x . y .
  z = y . (x . z)) ==> F`;

(* ------------------------------------------------------------------------- *)
val () = SAY "Substitution";
(* ------------------------------------------------------------------------- *)

val () = test I "x" (Term.variantPrime (NameSet.fromList ["y","z" ]) "x");

val () = test I "x'" (Term.variantPrime (NameSet.fromList ["x","y" ]) "x");

val () = test I "x''" (Term.variantPrime (NameSet.fromList ["x","x'"]) "x");

val () = test I "x" (Term.variantNum (NameSet.fromList ["y","z"]) "x");

val () = test I "x0" (Term.variantNum (NameSet.fromList ["x","y"]) "x");

val () = test I "x1" (Term.variantNum (NameSet.fromList ["x","x0"]) "x");

val () =
    test_fm
      `!x. x = $z`
      (Formula.subst (S [("y", Term.Var "z")]) (F`!x. x = $y`));

val () =
    test_fm
      `!x'. x' = $x`
      (Formula.subst (S [("y", Term.Var "x")]) (F`!x. x = $y`));

val () =
    test_fm
      `!x' x''. x' = $x ==> x' = x''`
      (Formula.subst (S [("y", Term.Var "x")]) (F`!x x'. x = $y ==> x = x'`));

(* ------------------------------------------------------------------------- *)
val () = SAY "Unification";
(* ------------------------------------------------------------------------- *)

fun unify_and_apply tm1 tm2 =
    Subst.subst (Subst.unify Subst.empty tm1 tm2) tm1;

val () = test_tm `c` (unify_and_apply (Term.Var "x") (Term.Fn ("c", [])));

val () = test_tm `c` (unify_and_apply (Term.Fn ("c", [])) (Term.Var "x"));

val () =
    test_tm
      `f c`
      (unify_and_apply
         (Term.Fn ("f", [Term.Var "x"]))
         (Term.Fn ("f", [Term.Fn ("c", [])])));
      
val () = test_tm `f 0 0 0` (unify_and_apply (T`f 0 $x $x`) (T`f $y $y $z`));

fun f x y = (printval Subst.pp (Atom.unify Subst.empty x y); ());

val () = f ("P", [Term.Var "x"]) ("P", [Term.Var "x"]);

val () = f ("P", [Term.Var "x"]) ("P", [Term.Fn ("c",[])]);

val () = f (A`P c_x`) (A`P $x`);

val () = f (A`q $x (f $x)`) (A`q $y $z`);

(* ------------------------------------------------------------------------- *)
val () = SAY "The logical kernel";
(* ------------------------------------------------------------------------- *)

val th0 = AX [`p`,`q`];
val th1 = AX [`~p`,`r`];
val th2 = Thm.resolve (L`p`) th0 th1;
val _ = printval Proof.pp (Proof.proof th2);

val th0 = Rule.relationCongruence Atom.eqRelation;
val th1 =
    Thm.subst (S [("y0",T`$x`),("y1",T`$y`),("x1",T`$z`),("x0",T`$x`)]) th0;
val th2 = Thm.resolve (L`$x = $x`) Rule.reflexivity th1;
val th3 = Rule.symNeq (L`~($z = $y)`) th2;
val _ = printval Proof.pp (Proof.proof th3);

(* Testing the elimination of redundancies in proofs *)

val th0 = Rule.reflexivity;
val th1 = Thm.subst (S [("x", Term.Fn ("f", [Term.Var "y"]))]) th0;
val th2 = Thm.subst (S [("y", Term.mkConst "c")]) th1;
val _ = printval Proof.pp (Proof.proof th2);

(* ------------------------------------------------------------------------- *)
val () = SAY "Derived rules of inference";
(* ------------------------------------------------------------------------- *)

val th0 = pvThm (AX [`$x = a`, `f a = $x`, `~(a = b)`, `a = $x`,
                     `$x = a`, `a = $x`, `~(b = a)`]);
val th1 = pvThm (Rule.removeSym th0);
val th2 = pvThm (Rule.symEq (L`a = $x`) th0);
val th3 = pvThm (Rule.symEq (L`f a = $x`) th0);
val th5 = pvThm (Rule.symNeq (L`~(a = b)`) th0);

(* Testing the rewrConv conversion *)
val (x_y as (x,y), eqTh) = pvEqn (Q`e * (i $z * $z) = e`);
val tm = Term.Fn ("f",[x]);
val path : int list = [0];
val reflTh = Thm.refl tm;
val reflLit = Thm.destUnit reflTh;
val th = Thm.equality reflLit (1 :: path) y;
val th = Thm.resolve reflLit reflTh th;
val th = pvThm (try (Thm.resolve (Literal.mkEq x_y) eqTh) th);

(* ------------------------------------------------------------------------- *)
val () = SAY "Discrimination nets for literals";
(* ------------------------------------------------------------------------- *)

val n = pvNet (LiteralNet.new {fifo = true});
val n = pvNet (LiteralNet.insert n (L`P (f c $x a)`, 1));
val n = pvNet (LiteralNet.insert n (L`P (f c $y a)`, 2));
val n = pvNet (LiteralNet.insert n (L`P (f c a a)`, 3));
val n = pvNet (LiteralNet.insert n (L`P (f c b a)`, 4));
val n = pvNet (LiteralNet.insert n (L`~Q`, 5));
val n = pvNet (LiteralNet.insert n (L`~Q`, 6));
val n = pvNet (LiteralNet.insert n (L`~Q`, 7));
val n = pvNet (LiteralNet.insert n (L`~Q`, 8));

(* ------------------------------------------------------------------------- *)
val () = SAY "The Knuth-Bendix ordering on terms";
(* ------------------------------------------------------------------------- *)

val kboOrder = KnuthBendixOrder.default;
val kboCmp = KnuthBendixOrder.compare kboOrder;

val x = pvPo (kboCmp (T`f a`, T`g b`));
val x = pvPo (kboCmp (T`f a b`, T`g b`));
val x = pvPo (kboCmp (T`f $x`, T`g a`));
val x = pvPo (kboCmp (T`f a $x`, T`g $x`));
val x = pvPo (kboCmp (T`f $x`, T`g $x`));
val x = pvPo (kboCmp (T`f $x`, T`f $x`));
val x = pvPo (kboCmp (T`$x + $y`, T`$x + $x`));
val x = pvPo (kboCmp (T`$x + $y + $x`, T`$y + $x + $x`));
val x = pvPo (kboCmp (T`$x + $y + $x`, T`$y * $x + $x`));
val x = pvPo (kboCmp (T`a`, T`$x`));
val x = pvPo (kboCmp (T`f a`, T`$x`));
val x = pvPo (kboCmp (T`f $x (f $y $z)`, T`f (f $x $y) $z`));
val x = pvPo (kboCmp (T`f (g $x a)`, T`f (h a $x)`));
val x = pvPo (kboCmp (T`f (g a)`, T`f (h $x)`));
val x = pvPo (kboCmp (T`f (h a)`, T`f (g $x)`));
val x = pvPo (kboCmp (T`f $y`, T`f (g a b c)`));

(* ------------------------------------------------------------------------- *)
val () = SAY "Rewriting";
(* ------------------------------------------------------------------------- *)

val eqnsToRw = Rewrite.addList (Rewrite.new kboCmp) o enumerate;

val eqns = [Q`e * $x = $x`, Q`$x * e = $x`, Q`i $x * $x = e`, Q`$x * i $x = e`];
val ax = pvThm (AX [`e * (i $z * $z) = i e * e`]);
val th = pvThm (Rewrite.orderedRewrite kboCmp eqns ax);

val rw = pvRw (eqnsToRw eqns);
val th = pvThm (snd (try (Rewrite.rewriteConv rw kboCmp) (T`e * e`)));
val th = pvThm (snd (try (Rewrite.rewriteConv rw kboCmp) (T`e * (i $z * $z)`)));
val th = pvThm (try (Rewrite.rewriteRule rw kboCmp) ax);

(* Bug check: in this one a literal goes missing, due to the Resolve in Subst *)
val eqns = [Q`f a = a`];
val ax = pvThm (AX [`~(g (f a) = b)`, `~(f a = a)`]);
val th = pvThm (try (Rewrite.orderedRewrite kboCmp eqns) ax);

(* Bug check: term paths were not being reversed before use *)
val eqns = [Q`a = f a`];
val ax = pvThm (AX [`a <= f (f a)`]);
val th = pvThm (try (Rewrite.orderedRewrite kboCmp eqns) ax);

(* Bug check: Equality used to complain if the literal didn't exist *)
val eqns = [Q`b = f a`];
val ax = pvThm (AX [`~(f a = f a)`]);
val th = pvThm (try (Rewrite.orderedRewrite kboCmp eqns) ax);

(* Testing the rewriting with disequalities in the same clause *)
val ax = pvThm (AX [`~(a = b)`, `P a`, `P b`]);
val th = pvThm (try (Rewrite.orderedRewrite kboCmp []) ax);

val ax = pvThm (AX [`~(f $x = $x)`, `P (f a)`, `P (f $x)`, `P (f $y)`]);
val th = pvThm (try (Rewrite.orderedRewrite kboCmp []) ax);

val ax = pvThm
  (AX [`~(f (f (f (f (f $x)))) = $x)`,
          `~(f (f (f (f (f (f (f (f $x))))))) = $x)`,
          `P (f $x)`]);
val th = pvThm (try (Rewrite.orderedRewrite kboCmp []) ax);

(* Symmetry should yield a tautology on ground clauses *)
val ax = pvThm (AX [`~(a = b)`, `b = a`]);
val th = pvThm (try (Rewrite.orderedRewrite kboCmp []) ax);

(* Transitivity should yield a tautology on ground clauses *)
val ax = pvThm (AX [`~(a = b)`, `~(b = c)`, `a = c`]);
val th = pvThm (try (Rewrite.orderedRewrite kboCmp []) ax);

(* Extended transitivity should yield a tautology on ground clauses *)
val ax = pvThm (AX [`~(a = b)`, `~(b = c)`, `~(c = d)`, `a = d`]);
val th = pvThm (try (Rewrite.orderedRewrite kboCmp []) ax);

(* ------------------------------------------------------------------------- *)
val () = SAY "Unit cache";
(* ------------------------------------------------------------------------- *)

val u = pvU (Units.add Units.empty (U`~p $x`));
val u = pvU (Units.add u (U`a = b`));
val _ = pvThm (Units.reduce u (AX [`p 0`,`~(b = a)`]));

(* ------------------------------------------------------------------------- *)
val () = SAY "Negation normal form";
(* ------------------------------------------------------------------------- *)

val nnf = Normalize.nnf;

val _ = pvFm (nnf (F`p /\ ~p`));
val _ = pvFm (nnf (F`(!x. P x) ==> ((?y. Q y) <=> (?z. P z /\ Q z))`));
val _ = pvFm (nnf (F`~(~(p <=> q) <=> r) <=> ~(p <=> ~(q <=> r))`));

(* ------------------------------------------------------------------------- *)
val () = SAY "Conjunctive normal form";
(* ------------------------------------------------------------------------- *)

val cnf = pvFms o Normalize.cnf o Formula.Not o Formula.generalize o F;

val _ = cnf `p \/ ~p`;
val _ = cnf `~((p /\ (q \/ r /\ s)) /\ (~p \/ ~q \/ ~s))`;
val _ = cnf `~((p /\ (q \/ r /\ s)) /\ (~p \/ ~q \/ ~s) /\ (p \/ ~p))`;
val _ = cnf `~(~(p <=> q) <=> r) <=> ~(p <=> ~(q <=> r))`;
val _ = cnf `((p <=> q) <=> r) <=> (p <=> (q <=> r))`;
val _ = cnf `~(!x. ?y. x < y ==> !v. ?w. x * v < y * w)`;
val _ = cnf `~(!x. P x ==> (?y z. Q y \/ ~(?z. P z /\ Q z)))`;
val _ = cnf `~(?x y. x + y = 2)`;

val _ = cnf
  `(!x. P x ==> (!x. Q x)) /\ ((!x. Q x \/ R x) ==> (?x. Q x /\ R x)) /\
   ((?x. R x) ==> (!x. L x ==> M x)) ==> (!x. P x /\ L x ==> M x)`;

(* verbose
use "../test/large-problem.sml";
val large_problem = time F large_problem_quotation;
val large_refute = time (Formula.Not o Formula.generalize) large_problem;
val _ = time Normalize.cnf large_refute;

User: 0.256  System: 0.002  GC: 0.060  Real: 0.261  (* Parsing *)
User: 0.017  System: 0.000  GC: 0.000  Real: 0.017  (* Negation *)
User: 0.706  System: 0.004  GC: 0.050  Real: 0.724  (* CNF *)
*)

(***
(* ------------------------------------------------------------------------- *)
val () = SAY "Finite models";
(* ------------------------------------------------------------------------- *)

val pv = printval M.pp_model;
fun f m fm =
  let
    val PRINT_TIMING_INFO = false
    val TIME_PER_SAMPLE = false
    val RANDOM_SAMPLES = 1000
    val timex_fn = if PRINT_TIMING_INFO then timed_many else timed
    val timey_fn = if PRINT_TIMING_INFO then timed_many else timed
    val (tx,i) = timex_fn (M.checkn m fm) RANDOM_SAMPLES
    val tx = if TIME_PER_SAMPLE then tx / Real.fromInt RANDOM_SAMPLES else tx
    val rx = Real.round (100.0 * Real.fromInt i / Real.fromInt RANDOM_SAMPLES)
    val (ty,(j,n)) = timey_fn (M.count m) fm
    val ty = if TIME_PER_SAMPLE then ty / Real.fromInt n else ty
    val ry = Real.round (100.0 * Real.fromInt j / Real.fromInt n)
    val () =
      if not PRINT_TIMING_INFO then () else
        print ("random sample time =     " ^ real_to_string tx ^ "s\n" ^
               "exhaustive search time = " ^ real_to_string ty ^ "s\n")
  in
    print (formula_to_string fm ^ "   random sampling = " ^ int_to_string rx ^
           "%   exhaustive search = " ^ int_to_string ry ^ "%\n\n")
  end;

val group_axioms = map Syntax.parseFormula
  [`e * x = x`, `i x * x = e`, `x * y * z = x * (y * z)`];

val group_thms = map Syntax.parseFormula
  [`x * e = x`, `x * i x = e`, `i (i x) = x`];

val m = pv (M.new M.defaults);
val () = app (f m) (group_axioms @ group_thms);
val m = pv (M.perturb group_axioms 1000 m);
val () = app (f m) (group_axioms @ group_thms);

(* Given the multiplication, can perturbations find inverse and identity? *)
val gfix = M.map_fix (fn "*" => SOME "+" | _ => NONE) M.modulo_fix;
val gparm = M.update_fix (M.fix_merge gfix) o M.update_size (K 10);
val m = pv (M.new (gparm M.defaults));
val () = app (f m) (group_axioms @ group_thms);
val m = pv (M.perturb group_axioms 1000 m);
val () = app (f m) (group_axioms @ group_thms);
val () = print ("e = " ^ M.term_to_string m (Syntax.parseTerm `e`) ^ "\n\n");
val () = print ("i x =\n" ^ M.term_to_string m (Syntax.parseTerm `i x`) ^ "\n");
val () = print ("x * y =\n" ^ M.term_to_string m (Syntax.parseTerm `x * y`) ^ "\n");
val () = print ("x = y =\n"^M.formula_to_string m (Syntax.parseFormula `x = y`)^"\n");

(* ------------------------------------------------------------------------- *)
val () = SAY "Completion engine";
(* ------------------------------------------------------------------------- *)

val pv = printval C.pp_completion;
fun wght ("i",1) = 0 | wght ("*",2) = 2 | wght _ = 1;
fun prec (("i",1),("i",1)) = EQUAL
  | prec (_,("i",1)) = LESS
  | prec (("i",1),_) = GREATER
  | prec ((f,m),(g,n)) =
  if m < n then LESS else if m > n then GREATER else String.compare (f,g);
val c_parm = {weight = wght, precedence = prec, precision = 3};
val c_emp = C.empty (T.empty c_parm);
val add = try (foldl (fn (q,r) => C.add (axiom [q]) r) c_emp);

val c = pv (add [`f (f x) = g x`]);
val c = pv (funpow 2 C.deduce c);

val c = pv (add [`x * y * z = x * (y * z)`, `1 * x = x`, `i x * x = 1`]);
val c = pv (funpow 44 C.deduce c);

val c = pv (add [`x*y * z = x * (y*z)`, `1 * x = x`, `x * 1 = x`, `x * x = 1`]);
val c = pv (funpow 4 C.deduce c);
***)
(* ------------------------------------------------------------------------- *)
val () = SAY "Syntax checking the problem sets";
(* ------------------------------------------------------------------------- *)

local
  fun same n = raise Fail ("Two goals called " ^ n);

  fun dup n n' =
      raise Fail ("Goal " ^ n' ^ " is probable duplicate of " ^ n);

  fun quot fm =
      let
        fun f (v,s) = Subst.insert s (v, Term.Var "_")

        val sub = NameSet.foldl f Subst.empty (Formula.freeVars fm)
      in
        Formula.subst sub fm
      end;

  val quot_clauses =
      Formula.listMkConj o sort Formula.compare o
      map (quot o snd o Formula.stripForall) o Formula.stripConj;

  fun quotient (Formula.Imp (a, Formula.Imp (b, Formula.False))) =
      Formula.Imp (quot_clauses a, Formula.Imp (quot_clauses b, Formula.False))
    | quotient fm = fm;

  fun check ({name,goal,...}, acc) =
    let
      val g = prep goal
      val p =
          Formula.fromString g
          handle Parser.NoParse =>
                 raise Error ("failed to parse problem " ^ name)
        
      val () =
        case List.find (fn (n,_) => n = name) acc of NONE => ()
        | SOME _ => same name

      val () =
        case List.find (fn (_,x) => x = p) acc of NONE => ()
        | SOME (n,_) => dup n name

      val _ =
        test_fun I g (mini_print (!Parser.lineLength) p)
        handle e => (print ("Error in problem " ^ name ^ "\n\n"); raise e)
    in
      (name,p) :: acc
    end;
in
  fun check_syntax (p : problem list) =
      (foldl check [] p; print "ok\n\n");
end;

val () = check_syntax problems;

(* ------------------------------------------------------------------------- *)
val () = SAY "Parsing TPTP problems";
(* ------------------------------------------------------------------------- *)

fun tptp f =
    case Tptp.toGoal (Tptp.read {filename = "../data/problems/all/" ^ f}) of
      Tptp.Fof goal => pvFm goal
    | Tptp.Cnf prob => pvFm (Problem.toClauses prob);

val Agatha = tptp "PUZ001-1.tptp";

(* ------------------------------------------------------------------------- *)
val () = SAY "Clauses";
(* ------------------------------------------------------------------------- *)

val cl = pvCl (CL[`P $x`,`P $y`]);
val _ = pvLits (Clause.largestLiterals cl);
val _ = pvCls (Clause.factor cl);
val cl = pvCl (CL[`$x = $y`,`f $y = f $x`]);
val _ = pvLits (Clause.largestLiterals cl);
val cl = pvCl (CL[`$x = f $y`,`f $x = $y`]);
val _ = pvLits (Clause.largestLiterals cl);
val cl = pvCl (CL[`s = a`,`s = b`,`h b c`]);
val _ = pvLits (Clause.largestLiterals cl);
val cl = pvCl (CL[`a = a`,`a = b`,`h b c`]);
val _ = pvLits (Clause.largestLiterals cl);

(* ------------------------------------------------------------------------- *)
(* Exporting problems to an external FOL datatype.                           *)
(* ------------------------------------------------------------------------- *)

(*
printDepth := 10000000;

datatype xterm =
  Fun of string * xterm list
| Var of string;

datatype xformula =
  All of xterm list * xformula
| Exi of xterm list * xformula
| Iff of xformula * xformula
| Imp of xformula * xformula
| And of xformula * xformula
| Or of xformula * xformula
| Not of xformula
| Tm of xterm
| BoolT
| BoolF
| Box; (*which can be ignored entirely*)

fun xterm (Term.Var v) = Var v
  | xterm (Term.Fn (f,a)) = Fun (f, map xterm a);

fun xformula Term.True = BoolT
  | xformula Term.False = BoolF
  | xformula (Term.Atom tm) = Tm (xterm tm)
  | xformula (Term.Not p) = Not (xformula p)
  | xformula (Term.And (p,q)) = And (xformula p, xformula q)
  | xformula (Term.Or (p,q)) = Or (xformula p, xformula q)
  | xformula (Term.Imp (p,q)) = Imp (xformula p, xformula q)
  | xformula (Term.Iff (p,q)) = Iff (xformula p, xformula q)
  | xformula fm =
  (case strip_exists fm of ([],_) =>
    (case strip_forall fm of ([],_) => raise Fail "xformula: can't identify"
     | (vs,p) => All (map Var vs, xformula p))
   | (vs,p) => Exi (map Var vs, xformula p));

fun xproblem {name, goal : thing quotation} =
  {name = name, goal = xformula (Syntax.parseFormula goal)};

val xset = map xproblem;

val xnonequality = xset Problem.nonequality;
*)

(***
(* ------------------------------------------------------------------------- *)
val () = SAY "Problems for provers";
(* ------------------------------------------------------------------------- *)

(* Non-equality *)

val p59 = pfm (Syntax.parseFormula `(!x. P x <=> ~P (f x)) ==> ?x. P x /\ ~P (f x)`);

val p39 = pfm (Syntax.parseFormula `~?x. !y. P y x <=> ~P y y`);

(* Equality *)

val p48 = (pfm o Syntax.parseFormula)
  `(a = b \/ c = d) /\ (a = c \/ b = d) ==> a = d \/ b = c`;

val cong = (pfm o Syntax.parseFormula)
  `(!x. f (f (f (f (f x)))) = x) /\ (!x. f (f (f x)) = x) ==> !x. f x = x`;

(* Impossible problems to test failure modes *)

val square = (pfm o Syntax.parseFormula)
  `sq 0 should_be_zero_here /\
   (!x. sq x x ==> sq 0 (s x)) /\ (!x y. sq x y ==> sq (s x) y) ==>
   sq 0 (s (s (s (s (s (s (s (s (s (s (s (s 0))))))))))))`;

(* ------------------------------------------------------------------------- *)
val () = SAY "Problems for solvers";
(* ------------------------------------------------------------------------- *)

val fib_rules = (pfm o Syntax.parseFormula)
  `(!x. x + 0 = x) /\ (!x y z. x + y = z ==> x + suc y = suc z) /\
   fib 0 = 0 /\ fib (suc 0) = suc 0 /\
   (!x y z w.
      fib x = y /\ fib (suc x) = z /\ y + z = w ==> fib (suc (suc x)) = w)`;

val fib_query = pfms [Syntax.parseFormula `fib x = suc (suc y)`];

val agatha_rules = (pfm o Syntax.parseFormula)
  `lives agatha /\ lives butler /\ lives charles /\
   (killed agatha agatha \/ killed butler agatha \/ killed charles agatha) /\
   (!x y. killed x y ==> hates x y /\ ~richer x y) /\
   (!x. hates agatha x ==> ~hates charles x) /\
   hates agatha agatha /\ hates agatha charles /\
   (!x. lives x /\ ~richer x agatha ==> hates butler x) /\
   (!x. hates agatha x ==> hates butler x) /\
   (!x. ~hates x agatha \/ ~hates x butler \/ ~hates x charles)`;

val agatha_query1 = pfms [Syntax.parseFormula `killed x agatha`];
val agatha_query2 = pfms [Syntax.parseFormula `~killed x agatha`];
val agatha_query3 = pfms (map Syntax.parseFormula [`killed x agatha`, `lives x`]);

val subset_rules = (pfm o Syntax.parseFormula)
  `subset nil nil /\
   (!v x y. subset x y ==> subset (v :: x) (v :: y)) /\
   (!v x y. subset x y ==> subset x        (v :: y))`;

val subset_query1 = pfms [Syntax.parseFormula `subset x (0 :: 1 :: 2 :: nil)`];
val subset_query2 = pfms [Syntax.parseFormula `subset (0 :: 1 :: 2 :: nil) x`];

val matchorder_rules = (pfm o Syntax.parseFormula)
  `p 0 3 /\
   (!x. p x 4) /\
   (!x. p x 3 ==> p (s (s (s x))) 3) /\
   (!x. p (s x) 3 ==> p x 3)`;

val matchorder_query = pfms [Syntax.parseFormula `p (s 0) 3`];

val ackermann_rules = (pfm o Syntax.parseFormula)
  `(!x. ack 0 x = s x) /\
   (!x y. ack x (s 0) = y ==> ack (s x) 0 = y) /\
   (!x y z. ack (s x) y = w /\ ack x w = z ==> ack (s x) (s y) = z)`;

val ackermann_query = pfms [Syntax.parseFormula `ack (s (s (s 0))) 0 = x`];

(* ------------------------------------------------------------------------- *)
(* Debugging Central.                                                        *)
(* ------------------------------------------------------------------------- *)

(*
val () = Useful.trace_level := 4;
val () = Clause.show_constraint := true;

local
  open Resolution;
  val to_parm = Termorder.update_precision I Termorder.defaults;
  val cl_parm = {term_order = true, literal_order = true,
                 order_stickiness = 0, termorder_parm = to_parm};
in
  val tres_prove = (quick_prove o resolution')
    ("tres",
     {clause_parm = cl_parm,
      set_parm    = Clauseset.defaults,
      sos_parm    = Support.defaults});
end;

val prob = Syntax.parseFormula `
  (!x. x = x) /\ (!x y z v. x + y <= z + v \/ ~(x <= z) \/ ~(y <= v)) /\
  (!x. x + 0 = x) /\ (!x. x + ~x = 0) /\
  (!x y z. x + (y + z) = x + y + z) ==>
  ~d <= 0 /\ c + d <= i /\ ~(c <= i) ==> F`;
val prob = Syntax.parseFormula (get std "P21");
val prob = Syntax.parseFormula (get std "ROB002-1");
val prob = Syntax.parseFormula (get std "KLEIN_GROUP_COMMUTATIVE");
val prob = Syntax.parseFormula (get hol "pred_set_1");

(*
(cnf o Not o generalize) prob;
stop;
*)

tres_prove prob;
stop;

val SOME th = meson_prove prob;
print (proof_to_string' 70 (proof th));

stop;
*)

(* ------------------------------------------------------------------------- *)
val () = SAY "Meson prover";
(* ------------------------------------------------------------------------- *)

val meson_prove_p59 = meson_prove p59;
val meson_prove_p39 = meson_prove p39;

val meson_prove_p48  = meson_prove p48;
val meson_prove_cong = meson_prove cong;

val meson_prove_square = meson_prove square;

(* ------------------------------------------------------------------------- *)
val () = SAY "Meson solver";
(* ------------------------------------------------------------------------- *)

val meson_solve_fib = meson_solve fib_rules fib_query;

val meson_solve_agatha1 = meson_solve agatha_rules agatha_query1;
val meson_solve_agatha2 = meson_solve agatha_rules agatha_query2;
val meson_solve_agatha3 = meson_solve agatha_rules agatha_query3;

val meson_solve_subset1 = meson_solve subset_rules subset_query1;
val meson_solve_subset2 = meson_solve subset_rules subset_query2;

val meson_solve_matchorder = meson_solve matchorder_rules matchorder_query;

val meson_solve_ackermann = meson_solve ackermann_rules ackermann_query;

(* ------------------------------------------------------------------------- *)
val () = SAY "Prolog solver";
(* ------------------------------------------------------------------------- *)

val prolog_solve_subset1 = prolog_solve subset_rules subset_query1;
val prolog_solve_subset2 = prolog_solve subset_rules subset_query2;

val prolog_solve_matchorder = prolog_solve matchorder_rules matchorder_query;

(* ------------------------------------------------------------------------- *)
val () = SAY "Resolution prover";
(* ------------------------------------------------------------------------- *)

val resolution_prove_p59 = resolution_prove p59;
val resolution_prove_p39 = resolution_prove p39;

val resolution_prove_p48  = resolution_prove p48;
val resolution_prove_cong = resolution_prove cong;

(* It would appear that resolution can't detect that this is unprovable
val resolution_prove_square = resolution_prove square; *)

(* Printing proofs
load "Problem";
val p21 = Syntax.parseFormula (Problem.get Problem.std "P21");
val p21_cnf = cnf (Not (generalize p21));
val SOME th = resolution_prove p21;
print (proof_to_string' 70 (proof th));
*)

(* ------------------------------------------------------------------------- *)
val () = SAY "Metis prover";
(* ------------------------------------------------------------------------- *)

val metis_prove_p59 = metis_prove p59;
val metis_prove_p39 = metis_prove p39;

val metis_prove_p48  = metis_prove p48;
val metis_prove_cong = metis_prove cong;

(* Poor delta is terribly slow at giving up on impossible problems
   and in any case resolution can't detect that this is unprovable.
val metis_prove_square = metis_prove square; *)
***)
