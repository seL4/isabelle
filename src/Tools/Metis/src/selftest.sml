(* ========================================================================= *)
(* METIS TESTS                                                               *)
(* Copyright (c) 2004 Joe Hurd, distributed under the BSD License            *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Dummy versions of Moscow ML declarations to stop real compilers barfing.  *)
(* ------------------------------------------------------------------------- *)

(*mlton
val quotation = ref true;
val quietdec  = ref true;
val loadPath  = ref ([] : string list);
val load = fn (_ : string) => ();
*)

(*polyml
val quotation = ref true;
val quietdec  = ref true;
val loadPath  = ref ([] : string list);
val load = fn (_ : string) => ();
*)

(* ------------------------------------------------------------------------- *)
(* Load and open some useful modules                                         *)
(* ------------------------------------------------------------------------- *)

val () = loadPath := !loadPath @ ["../bin/mosml"];
val () = app load ["Options"];

open Useful;

val time = Portable.time;

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
    TextIO.print
      ("-------------------------------------" ^
       "-------------------------------------\n" ^ s ^ "\n\n");

fun printval p x = (TextIO.print (Print.toString p x ^ "\n\n"); x);

fun mkCl p th = Clause.mk {parameters = p, id = Clause.newId (), thm = th};

val pvBool = printval Print.ppBool
and pvPo = printval (Print.ppMap partialOrderToString Print.ppString)
and pvFm = printval Formula.pp
and pvFms = printval (Print.ppList Formula.pp)
and pvThm = printval Thm.pp
and pvEqn : Rule.equation -> Rule.equation = printval (Print.ppMap snd Thm.pp)
and pvNet = printval (LiteralNet.pp Print.ppInt)
and pvRw = printval Rewrite.pp
and pvU = printval Units.pp
and pvLits = printval LiteralSet.pp
and pvCl = printval Clause.pp
and pvCls = printval (Print.ppList Clause.pp)
and pvM = printval Model.pp;

val NV = Name.fromString
and NF = Name.fromString
and NR = Name.fromString;
val V = Term.Var o NV
and C = (fn c => Term.Fn (NF c, []))
and T = Term.parse
and A = Atom.parse
and L = Literal.parse
and F = Formula.parse
and S = Subst.fromList;
val LS = LiteralSet.fromList o List.map L;
val AX = Thm.axiom o LS;
val CL = mkCl Clause.default o AX;
val Q = (fn th => (Thm.destUnitEq th, th)) o AX o singleton
and U = (fn th => (Thm.destUnit th, th)) o AX o singleton;

fun test_fun eq p r a =
  if eq r a then p a ^ "\n" else
    (TextIO.print
       ("\n\n" ^
        "test: should have\n-->" ^ p r ^ "<--\n\n" ^
        "test: actually have\n-->" ^ p a ^ "<--\n\n");
     raise Fail "test: failed a test");

fun test eq p r a = TextIO.print (test_fun eq p r a ^ "\n");

val test_tm = test Term.equal Term.toString o Term.parse;

val test_fm = test Formula.equal Formula.toString o Formula.parse;

fun test_id p f a = test p a (f a);

fun chop_newline s =
    if String.sub (s,0) = #"\n" then String.extract (s,1,NONE) else s;

fun unquote (QUOTE q) = q
  | unquote (ANTIQUOTE _) = raise Fail "unquote";

(* ------------------------------------------------------------------------- *)
val () = SAY "The parser and pretty-printer";
(* ------------------------------------------------------------------------- *)

fun prep l = (chop_newline o String.concat o List.map unquote) l;

fun mini_print n fm = withRef (Print.lineLength,n) Formula.toString fm;

fun testlen_pp n q =
    (fn s => test_fun equal I s ((mini_print n o Formula.fromString) s))
      (prep q);

fun test_pp q = TextIO.print (testlen_pp 40 q ^ "\n");

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
(!x.
   extremely__long__predicate__name) /\
F`;

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

val () =
    test Name.equal Name.toString (NV"x")
      (Term.variantPrime (NameSet.fromList [NV"y",NV"z" ]) (NV"x"));

val () =
    test Name.equal Name.toString (NV"x'")
      (Term.variantPrime (NameSet.fromList [NV"x",NV"y" ]) (NV"x"));

val () =
    test Name.equal Name.toString (NV"x''")
      (Term.variantPrime (NameSet.fromList [NV"x",NV"x'"]) (NV"x"));

val () =
    test Name.equal Name.toString (NV"x")
      (Term.variantNum (NameSet.fromList [NV"y",NV"z"]) (NV"x"));

val () =
    test Name.equal Name.toString (NV"x0")
      (Term.variantNum (NameSet.fromList [NV"x",NV"y"]) (NV"x"));

val () =
    test Name.equal Name.toString (NV"x1")
      (Term.variantNum (NameSet.fromList [NV"x",NV"x0"]) (NV"x"));

val () =
    test_fm
      `!x. x = $z`
      (Formula.subst (S [(NV"y", V"z")]) (F`!x. x = $y`));

val () =
    test_fm
      `!x'. x' = $x`
      (Formula.subst (S [(NV"y", V"x")]) (F`!x. x = $y`));

val () =
    test_fm
      `!x' x''. x' = $x ==> x' = x''`
      (Formula.subst (S [(NV"y", V"x")])
         (F`!x x'. x = $y ==> x = x'`));

(* ------------------------------------------------------------------------- *)
val () = SAY "Unification";
(* ------------------------------------------------------------------------- *)

fun unify_and_apply tm1 tm2 =
    Subst.subst (Subst.unify Subst.empty tm1 tm2) tm1;

val () = test_tm `c` (unify_and_apply (V"x") (C"c"));

val () = test_tm `c` (unify_and_apply (C"c") (V"x"));

val () =
    test_tm
      `f c`
      (unify_and_apply
         (Term.Fn (NF"f", [V"x"]))
         (Term.Fn (NF"f", [C"c"])));

val () = test_tm `f 0 0 0` (unify_and_apply (T`f 0 $x $x`) (T`f $y $y $z`));

fun f x y = (printval Subst.pp (Atom.unify Subst.empty x y); ());

val () = f (NR"P", [V"x"]) (NR"P", [V"x"]);

val () = f (NR"P", [V"x"]) (NR"P", [C"c"]);

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
    Thm.subst (S [(NV"y0",T`$x`),(NV"y1",T`$y`),(NV"x1",T`$z`),(NV"x0",T`$x`)]) th0;
val th2 = Thm.resolve (L`$x = $x`) Rule.reflexivity th1;
val th3 = Rule.symNeq (L`~($z = $y)`) th2;
val _ = printval Proof.pp (Proof.proof th3);

(* Testing the elimination of redundancies in proofs *)

val th0 = Rule.reflexivity;
val th1 = Thm.subst (S [(NV"x", Term.Fn (NF"f", [V"y"]))]) th0;
val th2 = Thm.subst (S [(NV"y", C"c")]) th1;
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
val tm = Term.Fn (NF"f",[x]);
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
val x = pvPo (kboCmp (T`$x * $y + $x * $z`, T`$x * ($y + $z)`));

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

local
  fun clauseToFormula cl =
      Formula.listMkDisj (LiteralSet.transform Literal.toFormula cl);
in
  fun clausesToFormula cls = Formula.listMkConj (List.map clauseToFormula cls);
end;

val cnf' = pvFm o clausesToFormula o Normalize.cnf o F;

val cnf = pvFm o clausesToFormula o Normalize.cnf o
          Formula.Not o Formula.generalize o F;

val _ = cnf `p \/ ~p`;
val _ = cnf `~((p /\ (q \/ r /\ s)) /\ (~p \/ ~q \/ ~s))`;
val _ = cnf `~((p /\ (q \/ r /\ s)) /\ (~p \/ ~q \/ ~s) /\ (p \/ ~p))`;
val _ = cnf `~(~(p <=> q) <=> r) <=> ~(p <=> ~(q <=> r))`;
val _ = cnf `((p <=> q) <=> r) <=> (p <=> (q <=> r))`;
val _ = cnf `~(!x. ?y. x < y ==> !v. ?w. x * v < y * w)`;
val _ = cnf `~(!x. P x ==> (?y z. Q y \/ ~(?z. P z /\ Q z)))`;
val _ = cnf `~(?x y. x + y = 2)`;
val _ = cnf' `(!x. p x) \/ (!y. r $x y)`;

val _ = cnf
  `(!x. P x ==> (!x. Q x)) /\ ((!x. Q x \/ R x) ==> (?x. Q x /\ R x)) /\
   ((?x. R x) ==> (!x. L x ==> M x)) ==> (!x. P x /\ L x ==> M x)`;

(* ------------------------------------------------------------------------- *)
val () = SAY "Finite models";
(* ------------------------------------------------------------------------- *)

fun checkModelClause M cl =
    let
      val randomSamples = 100

      fun addRandomSample {T,F} =
          let
            val {T = T', F = F'} = Model.checkClause {maxChecks = SOME 1} M cl
          in
            {T = T + T', F = F + F'}
          end

      val {T,F} = funpow randomSamples addRandomSample {T = 0, F = 0}
      val rx = Real.fromInt T / Real.fromInt (T + F)

      val {T,F} = Model.checkClause {maxChecks = NONE} M cl
      val ry = Real.fromInt T / Real.fromInt (T + F)
    in
      [Formula.toString (LiteralSet.disjoin cl),
       " | random sampling = " ^ percentToString rx,
       " | exhaustive = " ^ percentToString ry]
    end;

local
  val format =
      [{leftAlign = true, padChar = #" "},
       {leftAlign = true, padChar = #" "},
       {leftAlign = true, padChar = #" "}];
in
  fun checkModel M cls =
      let
        val table = List.map (checkModelClause M) cls

        val rows = alignTable format table

        val () = TextIO.print (join "\n" rows ^ "\n\n")
      in
        ()
      end;
end;

fun perturbModel M cls n =
    let
      val N = {size = Model.size M}

      fun perturbClause (fv,cl) =
          let
            val V = Model.randomValuation N fv
          in
            if Model.interpretClause M V cl then ()
            else Model.perturbClause M V cl
          end

      val cls = List.map (fn cl => (LiteralSet.freeVars cl, cl)) cls

      fun perturbClauses () = app perturbClause cls

      val () = funpow n perturbClauses ()
    in
      M
    end;

val groupAxioms =
    [LS[`0 + $x = $x`],
     LS[`~$x + $x = 0`],
     LS[`$x + $y + $z = $x + ($y + $z)`]];

val groupThms =
    [LS[`$x + 0 = $x`],
     LS[`$x + ~$x = 0`],
     LS[`~~$x = $x`]];

fun newM fixed = Model.new {size = 8, fixed = fixed};
val M = pvM (newM Model.basicFixed);
val () = checkModel M (groupAxioms @ groupThms);
val M = pvM (perturbModel M groupAxioms 1000);
val () = checkModel M (groupAxioms @ groupThms);
val M = pvM (newM (Model.unionFixed Model.modularFixed Model.basicFixed));
val () = checkModel M (groupAxioms @ groupThms);

(* ------------------------------------------------------------------------- *)
val () = SAY "Checking the standard model";
(* ------------------------------------------------------------------------- *)

fun ppPercentClause (r,cl) =
    let
      val ind = 6

      val p = percentToString r

      val fm = LiteralSet.disjoin cl
    in
      Print.consistentBlock ind
        [Print.ppString p,
         Print.ppString (nChars #" " (ind - size p)),
         Formula.pp fm]
    end;

val standardModel = Model.new Model.default;

fun checkStandardModelClause cl =
    let
      val {T,F} = Model.checkClause {maxChecks = SOME 1000} standardModel cl
      val r = Real.fromInt T / Real.fromInt (T + F)
    in
      (r,cl)
    end;

val pvPCl = printval ppPercentClause

(* Equality *)

val cl = LS[`$x = $x`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`~($x = $y)`,`$y = $x`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`~($x = $y)`,`~($y = $z)`,`$x = $z`];
val _ = pvPCl (checkStandardModelClause cl);

(* Projections *)

val cl = LS[`project1 $x1 = $x1`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project1 $x1 $x2 = $x1`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project2 $x1 $x2 = $x2`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project1 $x1 $x2 $x3 = $x1`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project2 $x1 $x2 $x3 = $x2`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project3 $x1 $x2 $x3 = $x3`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project1 $x1 $x2 $x3 $x4 = $x1`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project2 $x1 $x2 $x3 $x4 = $x2`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project3 $x1 $x2 $x3 $x4 = $x3`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project4 $x1 $x2 $x3 $x4 = $x4`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project1 $x1 $x2 $x3 $x4 $x5 = $x1`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project2 $x1 $x2 $x3 $x4 $x5 = $x2`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project3 $x1 $x2 $x3 $x4 $x5 = $x3`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project4 $x1 $x2 $x3 $x4 $x5 = $x4`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project5 $x1 $x2 $x3 $x4 $x5 = $x5`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project1 $x1 $x2 $x3 $x4 $x5 $x6 = $x1`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project2 $x1 $x2 $x3 $x4 $x5 $x6 = $x2`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project3 $x1 $x2 $x3 $x4 $x5 $x6 = $x3`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project4 $x1 $x2 $x3 $x4 $x5 $x6 = $x4`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project5 $x1 $x2 $x3 $x4 $x5 $x6 = $x5`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project6 $x1 $x2 $x3 $x4 $x5 $x6 = $x6`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project1 $x1 $x2 $x3 $x4 $x5 $x6 $x7 = $x1`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project2 $x1 $x2 $x3 $x4 $x5 $x6 $x7 = $x2`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project3 $x1 $x2 $x3 $x4 $x5 $x6 $x7 = $x3`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project4 $x1 $x2 $x3 $x4 $x5 $x6 $x7 = $x4`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project5 $x1 $x2 $x3 $x4 $x5 $x6 $x7 = $x5`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project6 $x1 $x2 $x3 $x4 $x5 $x6 $x7 = $x6`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project7 $x1 $x2 $x3 $x4 $x5 $x6 $x7 = $x7`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project1 $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8 = $x1`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project2 $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8 = $x2`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project3 $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8 = $x3`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project4 $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8 = $x4`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project5 $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8 = $x5`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project6 $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8 = $x6`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project7 $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8 = $x7`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project8 $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8 = $x8`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project1 $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8 $x9 = $x1`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project2 $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8 $x9 = $x2`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project3 $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8 $x9 = $x3`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project4 $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8 $x9 = $x4`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project5 $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8 $x9 = $x5`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project6 $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8 $x9 = $x6`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project7 $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8 $x9 = $x7`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project8 $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8 $x9 = $x8`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`project9 $x1 $x2 $x3 $x4 $x5 $x6 $x7 $x8 $x9 = $x9`];
val _ = pvPCl (checkStandardModelClause cl);

(* Arithmetic *)

(* Zero *)
val cl = LS[`~isZero $x`,`$x = 0`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`isZero $x`,`~($x = 0)`];
val _ = pvPCl (checkStandardModelClause cl);

(* Positive numerals *)
val cl = LS[`0 + 1 = 1`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`1 + 1 = 2`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`2 + 1 = 3`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`3 + 1 = 4`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`4 + 1 = 5`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`5 + 1 = 6`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`6 + 1 = 7`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`7 + 1 = 8`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`8 + 1 = 9`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`9 + 1 = 10`];
val _ = pvPCl (checkStandardModelClause cl);

(* Negative numerals *)
val cl = LS[`~1 = negative1`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`~2 = negative2`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`~3 = negative3`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`~4 = negative4`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`~5 = negative5`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`~6 = negative6`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`~7 = negative7`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`~8 = negative8`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`~9 = negative9`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`~10 = negative10`];
val _ = pvPCl (checkStandardModelClause cl);

(* Addition *)
val cl = LS[`0 + $x = $x`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`$x + $y = $y + $x`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`$x + ($y + $z) = ($x + $y) + $z`];
val _ = pvPCl (checkStandardModelClause cl);

(* Negation *)
val cl = LS[`~$x + $x = 0`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`~~$x = $x`];
val _ = pvPCl (checkStandardModelClause cl);

(* Subtraction *)
val cl = LS[`$x - $y = $x + ~$y`];
val _ = pvPCl (checkStandardModelClause cl);

(* Successor *)
val cl = LS[`suc $x = $x + 1`];
val _ = pvPCl (checkStandardModelClause cl);

(* Predecessor *)
val cl = LS[`pre $x = $x - 1`];
val _ = pvPCl (checkStandardModelClause cl);

(* Ordering *)
val cl = LS[`$x <= $x`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`~($x <= $y)`,`~($y <= $z)`,`$x <= $z`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`~($x <= $y)`,`~($y <= $x)`,`$x = $y`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`0 <= $x`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`~($x >= $y)`,`$y <= $x`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`$x >= $y`,`~($y <= $x)`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`$x > $y`,`$x <= $y`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`~($x > $y)`,`~($x <= $y)`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`$x < $y`,`$y <= $x`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`~($x < $y)`,`~($y <= $x)`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`$x = 0`,`~($x <= $y)`,`~$y <= ~$x`];
val _ = pvPCl (checkStandardModelClause cl);

(* Multiplication *)
val cl = LS[`1 * $x = $x`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`0 * $x = 0`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`$x * $y = $y * $x`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`$x * ($y * $z) = ($x * $y) * $z`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`$x * ($y + $z) = ($x * $y) + ($x * $z)`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`$x * ~$y = ~($x * $y)`];
val _ = pvPCl (checkStandardModelClause cl);

(* Division *)
val cl = LS[`$y = 0`,`$x mod $y < $y`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`$y * ($x div $y) + $x mod $y = $x`];
val _ = pvPCl (checkStandardModelClause cl);

(* Exponentiation *)
val cl = LS[`exp $x 0 = 1`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`$y = 0`,`exp $x $y = $x * exp $x (pre $y)`];
val _ = pvPCl (checkStandardModelClause cl);

(* Divides *)
val cl = LS[`divides $x $x`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`~(divides $x $y)`,`~(divides $y $z)`,`divides $x $z`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`~(divides $x $y)`,`~(divides $y $x)`,`$x = $y`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`divides 1 $x`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`divides $x 0`];
val _ = pvPCl (checkStandardModelClause cl);

(* Even and odd *)
val cl = LS[`even 0`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`$x = 0`,`~(even (pre $x))`,`odd $x`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`$x = 0`,`~(odd (pre $x))`,`even $x`];
val _ = pvPCl (checkStandardModelClause cl);

(* Sets *)

(* The empty set *)
val cl = LS[`~member $x empty`];
val _ = pvPCl (checkStandardModelClause cl);

(* The universal set *)
val cl = LS[`member $x universe`];
val _ = pvPCl (checkStandardModelClause cl);

(* Complement *)
val cl = LS[`member $x $y`,`member $x (complement $y)`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`~(member $x $y)`,`~member $x (complement $y)`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`complement (complement $x) = $x`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`complement empty = universe`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`complement universe = empty`];
val _ = pvPCl (checkStandardModelClause cl);

(* The subset relation *)
val cl = LS[`subset $x $x`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`~subset $x $y`,`~subset $y $z`,`subset $x $z`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`~subset $x $y`,`~subset $y $x`,`$x = $y`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`subset empty $x`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`subset $x universe`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`~subset $x $y`,`subset (complement $y) (complement $x)`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`~member $x $y`,`~subset $y $z`,`member $x $z`];
val _ = pvPCl (checkStandardModelClause cl);

(* Union *)
val cl = LS[`union $x $y = union $y $x`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`union $x (union $y $z) = union (union $x $y) $z`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`union empty $x = $x`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`union universe $x = universe`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`subset $x (union $x $y)`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`~member $x (union $y $z)`,`member $x $y`,`member $x $z`];
val _ = pvPCl (checkStandardModelClause cl);

(* Intersection *)
val cl = LS[`intersect $x $y =
             complement (union (complement $x) (complement $y))`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`subset (intersect $x $y) $x`];
val _ = pvPCl (checkStandardModelClause cl);

(* Difference *)
val cl = LS[`difference $x $y = intersect $x (complement $y)`];
val _ = pvPCl (checkStandardModelClause cl);

(* Symmetric difference *)
val cl = LS[`symmetricDifference $x $y =
             union (difference $x $y) (difference $y $x)`];
val _ = pvPCl (checkStandardModelClause cl);

(* Insert *)
val cl = LS[`member $x (insert $x $y)`];
val _ = pvPCl (checkStandardModelClause cl);

(* Singleton *)
val cl = LS[`singleton $x = (insert $x empty)`];
val _ = pvPCl (checkStandardModelClause cl);

(* Cardinality *)
val cl = LS[`card empty = 0`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`member $x $y`,`card (insert $x $y) = suc (card $y)`];
val _ = pvPCl (checkStandardModelClause cl);

(* Lists *)

(* Nil *)
val cl = LS[`null nil`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`~null $x`, `$x = nil`];
val _ = pvPCl (checkStandardModelClause cl);

(* Cons *)
val cl = LS[`~(nil = $x :: $y)`];
val _ = pvPCl (checkStandardModelClause cl);

(* Append *)
val cl = LS[`$x @ ($y @ $z) = ($x @ $y) @ $z`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`nil @ $x = $x`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`$x @ nil = $x`];
val _ = pvPCl (checkStandardModelClause cl);

(* Length *)
val cl = LS[`length nil = 0`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`length ($x :: $y) >= length $y`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`length ($x @ $y) >= length $x`];
val _ = pvPCl (checkStandardModelClause cl);
val cl = LS[`length ($x @ $y) >= length $y`];
val _ = pvPCl (checkStandardModelClause cl);

(* Tail *)
val cl = LS[`null $x`,`suc (length (tail $x)) = length $x`];
val _ = pvPCl (checkStandardModelClause cl);

(* ------------------------------------------------------------------------- *)
val () = SAY "Clauses";
(* ------------------------------------------------------------------------- *)

val cl = pvCl (CL[`P $x`,`P $y`]);
val _ = pvLits (Clause.largestLiterals cl);
val _ = pvCls (Clause.factor cl);
val cl = pvCl (CL[`P $x`,`~P (f $x)`]);
val _ = pvLits (Clause.largestLiterals cl);
val cl = pvCl (CL[`$x = $y`,`f $y = f $x`]);
val _ = pvLits (Clause.largestLiterals cl);
val cl = pvCl (CL[`$x = f $y`,`f $x = $y`]);
val _ = pvLits (Clause.largestLiterals cl);
val cl = pvCl (CL[`s = a`,`s = b`,`h b c`]);
val _ = pvLits (Clause.largestLiterals cl);
val cl = pvCl (CL[`a = a`,`a = b`,`h b c`]);
val _ = pvLits (Clause.largestLiterals cl);

(* Test cases contributed by Larry Paulson *)

local
  val lnFnName = Name.fromString "ln"
  and expFnName = Name.fromString "exp"
  and divFnName = Name.fromString "/"

  val leRelName = Name.fromString "<";

  fun weight na =
      case na of
        (n,1) =>
        if Name.equal n lnFnName then 500
        else if Name.equal n expFnName then 500
        else 1
      | (n,2) =>
        if Name.equal n divFnName then 50
        else if Name.equal n leRelName then 20
        else 1
      | _ => 1;

  val ordering =
      {weight = weight, precedence = #precedence KnuthBendixOrder.default};

  val clauseParameters =
      {ordering = ordering,
       orderLiterals = Clause.UnsignedLiteralOrder,
       orderTerms = true};
in
  val LcpCL = mkCl clauseParameters o AX;
end;

val cl = pvCl (LcpCL[`~($y <= (2 + (2 * $x + pow $x 2)) / 2)`, `~(0 <= $x)`,
                     `$y <= exp $x`]);
val _ = pvLits (Clause.largestLiterals cl);

(* ------------------------------------------------------------------------- *)
val () = SAY "Syntax checking the problem sets";
(* ------------------------------------------------------------------------- *)

local
  fun same n = raise Fail ("Two goals called " ^ n);

  fun dup n n' =
      raise Fail ("Goal " ^ n' ^ " is probable duplicate of " ^ n);

  fun quot fm =
      let
        fun f (v,s) = Subst.insert s (v,V"_")

        val sub = NameSet.foldl f Subst.empty (Formula.freeVars fm)
      in
        Formula.subst sub fm
      end;

  val quot_clauses =
      Formula.listMkConj o sort Formula.compare o
      List.map (quot o snd o Formula.stripForall) o Formula.stripConj;

  fun quotient (Formula.Imp (a, Formula.Imp (b, Formula.False))) =
      Formula.Imp (quot_clauses a, Formula.Imp (quot_clauses b, Formula.False))
    | quotient fm = fm;

  fun check ({name,goal,...}, acc) =
    let
      val g = prep goal
      val p =
          Formula.fromString g
          handle Parse.NoParse =>
                 raise Error ("failed to parse problem " ^ name)

      val () =
        case List.find (fn (n,_) => n = name) acc of NONE => ()
        | SOME _ => same name

      val () =
        case List.find (fn (_,x) => Formula.equal x p) acc of NONE => ()
        | SOME (n,_) => dup n name

      val _ =
        test_fun equal I g (mini_print (!Print.lineLength) p)
        handle e =>
          (TextIO.print ("Error in problem " ^ name ^ "\n\n");
           raise e)
    in
      (name,p) :: acc
    end;
in
  fun check_syntax (p : problem list) =
      let
        val _ = List.foldl check [] p
      in
        TextIO.print "ok\n\n"
      end;
end;

val () = check_syntax problems;

(* ------------------------------------------------------------------------- *)
val () = SAY "Parsing TPTP problems";
(* ------------------------------------------------------------------------- *)

fun tptp f =
    let
      val () = TextIO.print ("parsing " ^ f ^ "... ")
      val filename = "tptp/" ^ f ^ ".tptp"
      val mapping = Tptp.defaultMapping
      val goal = Tptp.goal (Tptp.read {filename = filename, mapping = mapping})
      val () = TextIO.print "ok\n"
    in
      pvFm goal
    end;

val _ = tptp "PUZ001-1";
val _ = tptp "NO_FORMULAS";
val _ = tptp "SEPARATED_COMMENTS";
val _ = tptp "NUMBERED_FORMULAS";
val _ = tptp "DEFINED_TERMS";
val _ = tptp "SYSTEM_TERMS";
val _ = tptp "QUOTED_TERMS";
val _ = tptp "QUOTED_TERMS_IDENTITY";
val _ = tptp "QUOTED_TERMS_DIFFERENT";
val _ = tptp "QUOTED_TERMS_SPECIAL";
val _ = tptp "RENAMING_VARIABLES";
val _ = tptp "MIXED_PROBLEM";
val _ = tptp "BLOCK_COMMENTS";

(* ------------------------------------------------------------------------- *)
val () = SAY "The TPTP finite model";
(* ------------------------------------------------------------------------- *)

val _ = printval (Tptp.ppFixedMap Tptp.defaultMapping) Tptp.defaultFixedMap;
