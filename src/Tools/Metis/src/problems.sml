(* ========================================================================= *)
(* SOME SAMPLE PROBLEMS TO TEST PROOF PROCEDURES                             *)
(* Copyright (c) 2001-2007 Joe Hurd, distributed under the GNU GPL version 2 *)
(* ========================================================================= *)

(* ========================================================================= *)
(* A type of problems.                                                       *)
(* ========================================================================= *)

type problem =
     {name : string,
      comments : string list,
      goal : Formula.quotation};

(* ========================================================================= *)
(* Helper functions.                                                         *)
(* ========================================================================= *)

fun mkProblem description (problem : problem) : problem =
    let
      val {name,comments,goal} = problem
      val comments = if null comments then [] else "" :: comments
      val comments = "Collection: " ^ description :: comments
    in
      {name = name, comments = comments, goal = goal}
    end;

fun mkProblems description problems = map (mkProblem description) problems;

(* ========================================================================= *)
(* The collection of problems.                                               *)
(* ========================================================================= *)

val problems : problem list =

(* ========================================================================= *)
(* Problems without equality.                                                *)
(* ========================================================================= *)

mkProblems "Problems without equality from various sources" [

(* ------------------------------------------------------------------------- *)
(* Trivia (some of which demonstrate ex-bugs in provers).                    *)
(* ------------------------------------------------------------------------- *)

{name = "TRUE",
 comments = [],
 goal = `
T`},

{name = "SIMPLE",
 comments = [],
 goal = `
!x y. ?z. p x \/ p y ==> p z`},

{name = "CYCLIC",
 comments = [],
 goal = `
(!x. p (g (c x))) ==> ?z. p (g z)`},

{name = "MICHAEL_NORRISH_BUG",
 comments = [],
 goal = `
(!x. ?y. f y x x) ==> ?z. f z 0 0`},

{name = "RELATION_COMPOSITION",
 comments = [],
 goal = `
(!x. ?y. p x y) /\ (!x. ?y. q x y) /\
(!x y z. p x y /\ q y z ==> r x z) ==> !x. ?y. r x y`},

(* ------------------------------------------------------------------------- *)
(* Propositional Logic.                                                      *)
(* ------------------------------------------------------------------------- *)

{name = "PROP_1",
 comments = [],
 goal = `
p ==> q <=> ~q ==> ~p`},

{name = "PROP_2",
 comments = [],
 goal = `
~~p <=> p`},

{name = "PROP_3",
 comments = [],
 goal = `
~(p ==> q) ==> q ==> p`},

{name = "PROP_4",
 comments = [],
 goal = `
~p ==> q <=> ~q ==> p`},

{name = "PROP_5",
 comments = [],
 goal = `
(p \/ q ==> p \/ r) ==> p \/ (q ==> r)`},

{name = "PROP_6",
 comments = [],
 goal = `
p \/ ~p`},

{name = "PROP_7",
 comments = [],
 goal = `
p \/ ~~~p`},

{name = "PROP_8",
 comments = [],
 goal = `
((p ==> q) ==> p) ==> p`},

{name = "PROP_9",
 comments = [],
 goal = `
(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)`},

{name = "PROP_10",
 comments = [],
 goal = `
(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)`},

{name = "PROP_11",
 comments = [],
 goal = `
p <=> p`},

{name = "PROP_12",
 comments = [],
 goal = `
((p <=> q) <=> r) <=> p <=> q <=> r`},

{name = "PROP_13",
 comments = [],
 goal = `
p \/ q /\ r <=> (p \/ q) /\ (p \/ r)`},

{name = "PROP_14",
 comments = [],
 goal = `
(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)`},

{name = "PROP_15",
 comments = [],
 goal = `
p ==> q <=> ~p \/ q`},

{name = "PROP_16",
 comments = [],
 goal = `
(p ==> q) \/ (q ==> p)`},

{name = "PROP_17",
 comments = [],
 goal = `
p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)`},

{name = "MATHS4_EXAMPLE",
 comments = [],
 goal = `
(a \/ ~k ==> g) /\ (g ==> q) /\ ~q ==> k`},

{name = "LOGICPROOF_1996",
 comments = [],
 goal = `
(p ==> r) /\ (~p ==> ~q) /\ (p \/ q) ==> p /\ r`},

{name = "XOR_ASSOC",
 comments = [],
 goal = `
~(~(p <=> q) <=> r) <=> ~(p <=> ~(q <=> r))`},

{name = "ALL_3_CLAUSES",
 comments = [],
 goal = `
(p \/ q \/ r) /\ (p \/ q \/ ~r) /\ (p \/ ~q \/ r) /\ (p \/ ~q \/ ~r) /\
(~p \/ q \/ r) /\ (~p \/ q \/ ~r) /\ (~p \/ ~q \/ r) /\
(~p \/ ~q \/ ~r) ==> F`},

{name = "CLAUSE_SIMP",
 comments = [],
 goal = `
(lit ==> clause) ==> (lit \/ clause <=> clause)`},

(* ------------------------------------------------------------------------- *)
(* Monadic Predicate Logic.                                                  *)
(* ------------------------------------------------------------------------- *)

{name = "P18",
 comments = ["The drinker's principle."],
 goal = `
?very_popular_guy. !whole_pub. drinks very_popular_guy ==> drinks whole_pub`},

{name = "P19",
 comments = [],
 goal = `
?x. !y z. (p y ==> q z) ==> p x ==> q x`},

{name = "P20",
 comments = [],
 goal = `
(!x y. ?z. !w. p x /\ q y ==> r z /\ u w) /\ (!x y. p x /\ q y) ==> ?z. r z`},

{name = "P21",
 comments = [],
 goal = `
(?x. p ==> q x) /\ (?x. q x ==> p) ==> ?x. p <=> q x`},

{name = "P22",
 comments = [],
 goal = `
(!x. p <=> q x) ==> (p <=> !x. q x)`},

{name = "P23",
 comments = [],
 goal = `
(!x. p \/ q x) <=> p \/ !x. q x`},

{name = "P24",
 comments = [],
 goal = `
~(?x. u x /\ q x) /\ (!x. p x ==> q x \/ r x) /\ ~(?x. p x ==> ?x. q x) /\
(!x. q x /\ r x ==> u x) ==> ?x. p x /\ r x`},

{name = "P25",
 comments = [],
 goal = `
(?x. p x) /\ (!x. u x ==> ~g x /\ r x) /\ (!x. p x ==> g x /\ u x) /\
((!x. p x ==> q x) \/ ?x. q x /\ p x) ==> ?x. q x /\ p x`},

{name = "P26",
 comments = [],
 goal = `
((?x. p x) <=> ?x. q x) /\ (!x y. p x /\ q y ==> (r x <=> u y)) ==>
((!x. p x ==> r x) <=> !x. q x ==> u x)`},

{name = "P27",
 comments = [],
 goal = `
(?x. p x /\ ~q x) /\ (!x. p x ==> r x) /\ (!x. u x /\ s x ==> p x) /\
(?x. r x /\ ~q x) ==> (!x. u x ==> ~r x) ==> !x. u x ==> ~s x`},

{name = "P28",
 comments = [],
 goal = `
(!x. p x ==> !x. q x) /\ ((!x. q x \/ r x) ==> ?x. q x /\ r x) /\
((?x. r x) ==> !x. l x ==> m x) ==> !x. p x /\ l x ==> m x`},

{name = "P29",
 comments = [],
 goal = `
(?x. p x) /\ (?x. g x) ==>
((!x. p x ==> h x) /\ (!x. g x ==> j x) <=>
 !x y. p x /\ g y ==> h x /\ j y)`},

{name = "P30",
 comments = [],
 goal = `
(!x. p x \/ g x ==> ~h x) /\ (!x. (g x ==> ~u x) ==> p x /\ h x) ==>
!x. u x`},

{name = "P31",
 comments = [],
 goal = `
~(?x. p x /\ (g x \/ h x)) /\ (?x. q x /\ p x) /\ (!x. ~h x ==> j x) ==>
?x. q x /\ j x`},

{name = "P32",
 comments = [],
 goal = `
(!x. p x /\ (g x \/ h x) ==> q x) /\ (!x. q x /\ h x ==> j x) /\
(!x. r x ==> h x) ==> !x. p x /\ r x ==> j x`},

{name = "P33",
 comments = [],
 goal = `
(!x. p a /\ (p x ==> p b) ==> p c) <=>
(!x. p a ==> p x \/ p c) /\ (p a ==> p b ==> p c)`},

{name = "P34",
 comments =
["This gives rise to 5184 clauses when naively converted to CNF!"],
 goal = `
((?x. !y. p x <=> p y) <=> (?x. q x) <=> !y. q y) <=>
(?x. !y. q x <=> q y) <=> (?x. p x) <=> !y. p y`},

{name = "P35",
 comments = [],
 goal = `
?x y. p x y ==> !x y. p x y`},

(* ------------------------------------------------------------------------- *)
(* Predicate logic without functions.                                        *)
(* ------------------------------------------------------------------------- *)

{name = "P36",
 comments = [],
 goal = `
(!x. ?y. p x y) /\ (!x. ?y. g x y) /\
(!x y. p x y \/ g x y ==> !z. p y z \/ g y z ==> h x z) ==> !x. ?y. h x y`},

{name = "P37",
 comments = [],
 goal = `
(!z. ?w. !x. ?y. (p x z ==> p y w) /\ p y z /\ (p y w ==> ?v. q v w)) /\
(!x z. ~p x z ==> ?y. q y z) /\ ((?x y. q x y) ==> !x. r x x) ==>
!x. ?y. r x y`},

{name = "P38",
 comments = [],
 goal = `
(!x. p a /\ (p x ==> ?y. p y /\ r x y) ==> ?z w. p z /\ r x w /\ r w z) <=>
!x.
  (~p a \/ p x \/ ?z w. p z /\ r x w /\ r w z) /\
  (~p a \/ ~(?y. p y /\ r x y) \/ ?z w. p z /\ r x w /\ r w z)`},

{name = "P39",
 comments = [],
 goal = `
~?x. !y. p y x <=> ~p y y`},

{name = "P40",
 comments = [],
 goal = `
(?y. !x. p x y <=> p x x) ==> ~!x. ?y. !z. p z y <=> ~p z x`},

{name = "P41",
 comments = [],
 goal = `
(!z. ?y. !x. p x y <=> p x z /\ ~p x x) ==> ~?z. !x. p x z`},

{name = "P42",
 comments = [],
 goal = `
~?y. !x. p x y <=> ~?z. p x z /\ p z x`},

{name = "P43",
 comments = [],
 goal = `
(!x y. q x y <=> !z. p z x <=> p z y) ==> !x y. q x y <=> q y x`},

{name = "P44",
 comments = [],
 goal = `
(!x. p x ==> (?y. g y /\ h x y) /\ ?y. g y /\ ~h x y) /\
(?x. j x /\ !y. g y ==> h x y) ==> ?x. j x /\ ~p x`},

{name = "P45",
 comments = [],
 goal = `
(!x. p x /\ (!y. g y /\ h x y ==> j x y) ==> !y. g y /\ h x y ==> r y) /\
~(?y. l y /\ r y) /\
(?x. p x /\ (!y. h x y ==> l y) /\ !y. g y /\ h x y ==> j x y) ==>
?x. p x /\ ~?y. g y /\ h x y`},

{name = "P46",
 comments = [],
 goal = `
(!x. p x /\ (!y. p y /\ h y x ==> g y) ==> g x) /\
((?x. p x /\ ~g x) ==> ?x. p x /\ ~g x /\ !y. p y /\ ~g y ==> j x y) /\
(!x y. p x /\ p y /\ h x y ==> ~j y x) ==> !x. p x ==> g x`},

{name = "P50",
 comments = [],
 goal = `
(!x. f0 a x \/ !y. f0 x y) ==> ?x. !y. f0 x y`},

{name = "LOGICPROOF_L10",
 comments = [],
 goal = `
!x. ?y. ~(P y x <=> ~P y y)`},

{name = "BARBER",
 comments = ["One resolution of the barber paradox"],
 goal = `
(!x. man x ==> (shaves barber x <=> ~shaves x x)) ==> ~man barber`},

(* ------------------------------------------------------------------------- *)
(* Full predicate logic.                                                     *)
(* ------------------------------------------------------------------------- *)

{name = "LOGICPROOF_1999",
 comments = ["A non-theorem."],
 goal = `
(?x. p x /\ q x) ==> ?x. p (f x x) \/ !y. q y`},

{name = "P55",
 comments = ["Example from Manthey and Bry, CADE-9. [JRH]"],
 goal = `
lives agatha /\ lives butler /\ lives charles /\
(killed agatha agatha \/ killed butler agatha \/ killed charles agatha) /\
(!x y. killed x y ==> hates x y /\ ~richer x y) /\
(!x. hates agatha x ==> ~hates charles x) /\
(hates agatha agatha /\ hates agatha charles) /\
(!x. lives x /\ ~richer x agatha ==> hates butler x) /\
(!x. hates agatha x ==> hates butler x) /\
(!x. ~hates x agatha \/ ~hates x butler \/ ~hates x charles) ==>
killed agatha agatha /\ ~killed butler agatha /\ ~killed charles agatha`},

{name = "P57",
 comments = [],
 goal = `
p (f a b) (f b c) /\ p (f b c) (f a c) /\
(!x y z. p x y /\ p y z ==> p x z) ==> p (f a b) (f a c)`},

{name = "P58",
 comments = ["See info-hol 1498 [JRH]"],
 goal = `
!x. ?v w. !y z. p x /\ q y ==> (p v \/ r w) /\ (r z ==> q v)`},

{name = "P59",
 comments = [],
 goal = `
(!x. p x <=> ~p (f x)) ==> ?x. p x /\ ~p (f x)`},

{name = "P60",
 comments = [],
 goal = `
!x. p x (f x) <=> ?y. (!z. p z y ==> p z (f x)) /\ p x y`},

(* ------------------------------------------------------------------------- *)
(* From Gilmore's classic paper.                                             *)
(* ------------------------------------------------------------------------- *)

{name = "GILMORE_1",
 comments =
["Amazingly, this still seems non-trivial... in HOL [MESON_TAC] it",
 "works at depth 45! [JRH]",
 "Confirmed (depth=45, inferences=263702, time=148s), though if",
 "lemmaizing is used then a lemma is discovered at depth 29 that allows",
 "a much quicker proof (depth=30, inferences=10039, time=5.5s)."],
 goal = `
?x. !y z.
  (f y ==> g y <=> f x) /\ (f y ==> h y <=> g x) /\
  ((f y ==> g y) ==> h y <=> h x) ==> f z /\ g z /\ h z`},

{name = "GILMORE_2",
 comments =
["This is not valid, according to Gilmore. [JRH]",
 "Confirmed: ordered resolution quickly saturates."],
 goal = `
?x y. !z.
  (f x z <=> f z y) /\ (f z y <=> f z z) /\ (f x y <=> f y x) ==>
  (f x y <=> f x z)`},

{name = "GILMORE_3",
 comments = [],
 goal = `
?x. !y z.
  ((f y z ==> g y ==> h x) ==> f x x) /\ ((f z x ==> g x) ==> h z) /\
  f x y ==> f z z`},

{name = "GILMORE_4",
 comments = [],
 goal = `
?x y. !z. (f x y ==> f y z /\ f z z) /\ (f x y /\ g x y ==> g x z /\ g z z)`},

{name = "GILMORE_5",
 comments = [],
 goal = `
(!x. ?y. f x y \/ f y x) /\ (!x y. f y x ==> f y y) ==> ?z. f z z`},

{name = "GILMORE_6",
 comments = [],
 goal = `
!x. ?y.
  (?w. !v. f w x ==> g v w /\ g w x) ==>
  (?w. !v. f w y ==> g v w /\ g w y) \/
  !z v. ?w. g v z \/ h w y z ==> g z w`},

{name = "GILMORE_7",
 comments = [],
 goal = `
(!x. k x ==> ?y. l y /\ (f x y ==> g x y)) /\
(?z. k z /\ !w. l w ==> f z w) ==> ?v w. k v /\ l w /\ g v w`},

{name = "GILMORE_8",
 comments = [],
 goal = `
?x. !y z.
  ((f y z ==> g y ==> !w. ?v. h w v x) ==> f x x) /\
  ((f z x ==> g x) ==> !w. ?v. h w v z) /\ f x y ==> f z z`},

{name = "GILMORE_9",
 comments =
["Model elimination (in HOL):",
 "- With lemmaizing: (depth=18, inferences=15632, time=21s)",
 "- Without: gave up waiting after (depth=25, inferences=2125072, ...)"],
 goal = `
!x. ?y. !z.
  ((!w. ?v. f y w v /\ g y w /\ ~h y x) ==>
   (!w. ?v. f x w v /\ g z u /\ ~h x z) ==>
   !w. ?v. f x w v /\ g y w /\ ~h x y) /\
  ((!w. ?v. f x w v /\ g y w /\ ~h x y) ==>
   ~(!w. ?v. f x w v /\ g z w /\ ~h x z) ==>
   (!w. ?v. f y w v /\ g y w /\ ~h y x) /\
   !w. ?v. f z w v /\ g y w /\ ~h z y)`},

{name = "GILMORE_9a",
 comments =
["Translation of Gilmore procedure using separate definitions. [JRH]"],
 goal = `
(!x y. p x y <=> !w. ?v. f x w v /\ g y w /\ ~h x y) ==>
!x. ?y. !z.
  (p y x ==> p x z ==> p x y) /\ (p x y ==> ~p x z ==> p y x /\ p z y)`},

{name = "BAD_CONNECTIONS",
 comments =
["The interesting example where connections make the proof longer. [JRH]"],
 goal = `
~a /\ (a \/ b) /\ (c \/ d) /\ (~b \/ e \/ f) /\ (~c \/ ~e) /\ (~c \/ ~f) /\
(~b \/ g \/ h) /\ (~d \/ ~g) /\ (~d \/ ~h) ==> F`},

{name = "LOS",
 comments =
["The classic Los puzzle. (Clausal version MSC006-1 in the TPTP library.)",
 "Note: this is actually in the decidable AE subset, though that doesn't",
 "yield a very efficient proof. [JRH]"],
 goal = `
(!x y z. p x y ==> p y z ==> p x z) /\
(!x y z. q x y ==> q y z ==> q x z) /\ (!x y. q x y ==> q y x) /\
(!x y. p x y \/ q x y) ==> (!x y. p x y) \/ !x y. q x y`},

{name = "STEAM_ROLLER",
 comments = [],
 goal = `
((!x. p1 x ==> p0 x) /\ ?x. p1 x) /\ ((!x. p2 x ==> p0 x) /\ ?x. p2 x) /\
((!x. p3 x ==> p0 x) /\ ?x. p3 x) /\ ((!x. p4 x ==> p0 x) /\ ?x. p4 x) /\
((!x. p5 x ==> p0 x) /\ ?x. p5 x) /\ ((?x. q1 x) /\ !x. q1 x ==> q0 x) /\
(!x.
   p0 x ==>
   (!y. q0 y ==> r x y) \/
   !y. p0 y /\ s0 y x /\ (?z. q0 z /\ r y z) ==> r x y) /\
(!x y. p3 y /\ (p5 x \/ p4 x) ==> s0 x y) /\
(!x y. p3 x /\ p2 y ==> s0 x y) /\ (!x y. p2 x /\ p1 y ==> s0 x y) /\
(!x y. p1 x /\ (p2 y \/ q1 y) ==> ~r x y) /\
(!x y. p3 x /\ p4 y ==> r x y) /\ (!x y. p3 x /\ p5 y ==> ~r x y) /\
(!x. p4 x \/ p5 x ==> ?y. q0 y /\ r x y) ==>
?x y. p0 x /\ p0 y /\ ?z. q1 z /\ r y z /\ r x y`},

{name = "MODEL_COMPLETENESS",
 comments =
["An incestuous example used to establish completeness",
 "characterization. [JRH]"],
 goal = `
(!w x. sentence x ==> holds w x \/ holds w (not x)) /\
(!w x. ~(holds w x /\ holds w (not x))) ==>
((!x.
    sentence x ==>
    (!w. models w s ==> holds w x) \/
    !w. models w s ==> holds w (not x)) <=>
 !w v.
   models w s /\ models v s ==>
   !x. sentence x ==> (holds w x <=> holds v x))`}

] @

(* ========================================================================= *)
(* Problems with equality.                                                   *)
(* ========================================================================= *)

mkProblems "Equality problems from various sources" [

(* ------------------------------------------------------------------------- *)
(* Trivia (some of which demonstrate ex-bugs in the prover).                 *)
(* ------------------------------------------------------------------------- *)

{name = "REFLEXIVITY",
 comments = [],
 goal = `
c = c`},

{name = "SYMMETRY",
 comments = [],
 goal = `
!x y. x = y ==> y = x`},

{name = "TRANSITIVITY",
 comments = [],
 goal = `
!x y z. x = y /\ y = z ==> x = z`},

{name = "TRANS_SYMM",
 comments = [],
 goal = `
!x y z. x = y /\ y = z ==> z = x`},

{name = "SUBSTITUTIVITY",
 comments = [],
 goal = `
!x y. f x /\ x = y ==> f y`},

{name = "CYCLIC_SUBSTITUTION_BUG",
 comments = [],
 goal = `
!y. (!x. y = g (c x)) ==> ?z. y = g z`},

{name = "JUDITA_1",
 comments = [],
 goal = `
~(a = b) /\ (!x. x = c) ==> F`},

{name = "JUDITA_2",
 comments = [],
 goal = `
~(a = b) /\ (!x y. x = y) ==> F`},

{name = "JUDITA_3",
 comments = [],
 goal = `
p a /\ ~p b /\ (!x. x = c) ==> F`},

{name = "JUDITA_4",
 comments = [],
 goal = `
p a /\ ~p b /\ (!x y. x = y) ==> F`},

{name = "JUDITA_5",
 comments = [],
 goal = `
p a /\ p b /\ ~(a = b) /\ ~p c /\ (!x. x = a \/ x = d) ==> F`},

{name = "INJECTIVITY_1",
 comments = [],
 goal = `
(!x y. f x = f y ==> x = y) /\ f a = f b ==> a = b`},

{name = "INJECTIVITY_2",
 comments = [],
 goal = `
(!x y. g (f x) = g (f y) ==> x = y) /\ f a = f b ==> a = b`},

{name = "SELF_REWRITE",
 comments = [],
 goal = `
f (g (h c)) = h c /\ g (h c) = b /\ f b = a /\ (!x. ~(a = h x)) ==> F`},

(* ------------------------------------------------------------------------- *)
(* Simple equality problems.                                                 *)
(* ------------------------------------------------------------------------- *)

{name = "P48",
 comments = [],
 goal = `
(a = b \/ c = d) /\ (a = c \/ b = d) ==> a = d \/ b = c`},

{name = "P49",
 comments = [],
 goal = `
(?x y. !z. z = x \/ z = y) /\ p a /\ p b /\ ~(a = b) ==> !x. p x`},

{name = "P51",
 comments = [],
 goal = `
(?z w. !x y. f0 x y <=> x = z /\ y = w) ==>
?z. !x. (?w. !y. f0 x y <=> y = w) <=> x = z`},

{name = "P52",
 comments = [],
 goal = `
(?z w. !x y. f0 x y <=> x = z /\ y = w) ==>
?w. !y. (?z. !x. f0 x y <=> x = z) <=> y = w`},

{name = "UNSKOLEMIZED_MELHAM",
 comments = ["The Melham problem after an inverse skolemization step."],
 goal = `
(!x y. g x = g y ==> f x = f y) ==> !y. ?w. !x. y = g x ==> w = f x`},
 
{name = "CONGRUENCE_CLOSURE_EXAMPLE",
 comments = ["The example always given for congruence closure."],
 goal = `
!x. f (f (f (f (f x)))) = x /\ f (f (f x)) = x ==> f x = x`},

{name = "EWD_1",
 comments =
["A simple example (see EWD1266a and the application to Morley's",
 "theorem). [JRH]"],
 goal = `
(!x. f x ==> g x) /\ (?x. f x) /\ (!x y. g x /\ g y ==> x = y) ==>
!y. g y ==> f y`},

{name = "EWD_2",
 comments = [],
 goal = `
(!x. f (f x) = f x) /\ (!x. ?y. f y = x) ==> !x. f x = x`},

{name = "JIA",
 comments = ["Needs only the K combinator"],
 goal = `
(!x y. k . x . y = x) /\ (!v. P (v . a) a) /\ (!w. Q (w . b) b) ==>
!z. ?x y. P (z . x . y) x /\ Q (z . x . y) y`},

{name = "WISHNU",
 comments = ["Wishnu Prasetya's example. [JRH]"],
 goal = `
(?x. x = f (g x) /\ !x'. x' = f (g x') ==> x = x') <=>
?y. y = g (f y) /\ !y'. y' = g (f y') ==> y = y'`},

{name = "AGATHA",
 comments = ["An equality version of the Agatha puzzle. [JRH]"],
 goal = `
(?x. lives x /\ killed x agatha) /\
(lives agatha /\ lives butler /\ lives charles) /\
(!x. lives x ==> x = agatha \/ x = butler \/ x = charles) /\
(!x y. killed x y ==> hates x y) /\ (!x y. killed x y ==> ~richer x y) /\
(!x. hates agatha x ==> ~hates charles x) /\
(!x. ~(x = butler) ==> hates agatha x) /\
(!x. ~richer x agatha ==> hates butler x) /\
(!x. hates agatha x ==> hates butler x) /\ (!x. ?y. ~hates x y) /\
~(agatha = butler) ==>
killed agatha agatha /\ ~killed butler agatha /\ ~killed charles agatha`},

{name = "DIVIDES_9_1",
 comments = [],
 goal = `
(!x y. x * y = y * x) /\ (!x y z. x * y * z = x * (y * z)) /\
(!x y. divides x y <=> ?z. y = z * x) ==>
!x y z. divides x y ==> divides x (z * y)`},

{name = "DIVIDES_9_2",
 comments = [],
 goal = `
(!x y. x * y = y * x) /\ (!x y z. x * y * z = x * (y * z)) /\
(!x y. divides x y <=> ?z. z * x = y) ==>
!x y z. divides x y ==> divides x (z * y)`},

(* ------------------------------------------------------------------------- *)
(* Group theory examples.                                                    *)
(* ------------------------------------------------------------------------- *)

{name = "GROUP_INVERSE_INVERSE",
 comments = [],
 goal = `
(!x y z. x * (y * z) = x * y * z) /\ (!x. e * x = x) /\
(!x. i x * x = e) ==> !x. i (i x) = x`},

{name = "GROUP_RIGHT_INVERSE",
 comments = ["Size 18, 61814 seconds. [JRH]"],
 goal = `
(!x y z. x * (y * z) = x * y * z) /\ (!x. e * x = x) /\
(!x. i x * x = e) ==> !x. x * i x = e`},

{name = "GROUP_RIGHT_IDENTITY",
 comments = [],
 goal = `
(!x y z. x * (y * z) = x * y * z) /\ (!x. e * x = x) /\
(!x. i x * x = e) ==> !x. x * e = x`},

{name = "GROUP_IDENTITY_EQUIV",
 comments = [],
 goal = `
(!x y z. x * (y * z) = x * y * z) /\ (!x. e * x = x) /\
(!x. i x * x = e) ==> !x. x * x = x <=> x = e`},

{name = "KLEIN_GROUP_COMMUTATIVE",
 comments = [],
 goal = `
(!x y z. x * (y * z) = x * y * z) /\ (!x. e * x = x) /\ (!x. x * e = x) /\
(!x. x * x = e) ==> !x y. x * y = y * x`},

(* ------------------------------------------------------------------------- *)
(* Ring theory examples.                                                     *)
(* ------------------------------------------------------------------------- *)

{name = "JACOBSON_2",
 comments = [],
 goal = `
(!x. 0 + x = x) /\ (!x. x + 0 = x) /\ (!x. n x + x = 0) /\
(!x. x + n x = 0) /\ (!x y z. x + (y + z) = x + y + z) /\
(!x y. x + y = y + x) /\ (!x y z. x * (y * z) = x * y * z) /\
(!x y z. x * (y + z) = x * y + x * z) /\
(!x y z. (x + y) * z = x * z + y * z) /\ (!x. x * x = x) ==>
!x y. x * y = y * x`},

{name = "JACOBSON_3",
 comments = [],
 goal = `
(!x. 0 + x = x) /\ (!x. x + 0 = x) /\ (!x. n x + x = 0) /\
(!x. x + n x = 0) /\ (!x y z. x + (y + z) = x + y + z) /\
(!x y. x + y = y + x) /\ (!x y z. x * (y * z) = x * y * z) /\
(!x y z. x * (y + z) = x * y + x * z) /\
(!x y z. (x + y) * z = x * z + y * z) /\ (!x. x * (x * x) = x) ==>
!x y. x * y = y * x`}

] @

(* ========================================================================= *)
(* Some sample problems from the TPTP archive.                               *)
(* Note: for brevity some relation/function names have been shortened.       *)
(* ========================================================================= *)

mkProblems "Sample problems from the TPTP collection"

[

{name = "ALG005-1",
 comments = [],
 goal = `
(!x y. x + (y + x) = x) /\ (!x y. x + (x + y) = y + (y + x)) /\
(!x y z. x + y + z = x + z + (y + z)) /\ (!x y. x * y = x + (x + y)) ==>
~(a * b * c = a * (b * c)) ==> F`},

{name = "ALG006-1",
 comments = [],
 goal = `
(!x y. x + (y + x) = x) /\ (!x y. x + (x + y) = y + (y + x)) /\
(!x y z. x + y + z = x + z + (y + z)) ==> ~(a + c + b = a + b + c) ==> F`},

{name = "BOO021-1",
 comments = [],
 goal = `
(!x y. (x + y) * y = y) /\ (!x y z. x * (y + z) = y * x + z * x) /\
(!x. x + i x = 1) /\ (!x y. x * y + y = y) /\
(!x y z. x + y * z = (y + x) * (z + x)) /\ (!x. x * i x = 0) ==>
~(b * a = a * b) ==> F`},

{name = "COL058-2",
 comments = [],
 goal = `
(!x y. r (r 0 x) y = r x (r y y)) ==>
~(r (r (r 0 (r (r 0 (r 0 0)) (r 0 (r 0 0)))) (r 0 (r 0 0)))
    (r (r 0 (r (r 0 (r 0 0)) (r 0 (r 0 0)))) (r 0 (r 0 0))) =
  r (r 0 (r (r 0 (r 0 0)) (r 0 (r 0 0)))) (r 0 (r 0 0))) ==> F`},

{name = "COL060-3",
 comments = [],
 goal = `
(!x y z. b . x . y . z = x . (y . z)) /\ (!x y. t . x . y = y . x) ==>
~(b . (b . (t . b) . b) . t . x . y . z = y . (x . z)) ==> F`},

{name = "GEO002-4",
 comments = [],
 goal = `
(!x y z v. ~between x y z \/ ~between y v z \/ between x y v) /\
(!x y z. ~equidistant x y z z \/ x == y) /\
(!x y z v w.
   ~between x y z \/ ~between v z w \/
   between x (outer_pasch y x v w z) v) /\
(!x y z v w.
   ~between x y z \/ ~between v z w \/
   between w y (outer_pasch y x v w z)) /\
(!x y z v. between x y (extension x y z v)) /\
(!x y z v. equidistant x (extension y x z v) z v) /\
(!x y z v. ~(x == y) \/ ~between z v x \/ between z v y) ==>
~between a a b ==> F`},

{name = "GEO036-2",
 comments = [],
 goal = `
(!x y. equidistant x y y x) /\
(!x y z x' y' z'.
   ~equidistant x y z x' \/ ~equidistant x y y' z' \/
   equidistant z x' y' z') /\ (!x y z. ~equidistant x y z z \/ x = y) /\
(!x y z v. between x y (extension x y z v)) /\
(!x y z v. equidistant x (extension y x z v) z v) /\
(!x y z v w x' y' z'.
   ~equidistant x y z v \/ ~equidistant y w v x' \/
   ~equidistant x y' z z' \/ ~equidistant y y' v z' \/ ~between x y w \/
   ~between z v x' \/ x = y \/ equidistant w y' x' z') /\
(!x y. ~between x y x \/ x = y) /\
(!x y z v w.
   ~between x y z \/ ~between v w z \/
   between y (inner_pasch x y z w v) v) /\
(!x y z v w.
   ~between x y z \/ ~between v w z \/
   between w (inner_pasch x y z w v) x) /\
~between lower_dimension_point_1 lower_dimension_point_2
   lower_dimension_point_3 /\
~between lower_dimension_point_2 lower_dimension_point_3
   lower_dimension_point_1 /\
~between lower_dimension_point_3 lower_dimension_point_1
   lower_dimension_point_2 /\
(!x y z v w.
   ~equidistant x y x z \/ ~equidistant v y v z \/ ~equidistant w y w z \/
   between x v w \/ between v w x \/ between w x v \/ y = z) /\
(!x y z v w.
   ~between x y z \/ ~between v y w \/ x = y \/
   between x v (euclid1 x v y w z)) /\
(!x y z v w.
   ~between x y z \/ ~between v y w \/ x = y \/
   between x w (euclid2 x v y w z)) /\
(!x y z v w.
   ~between x y z \/ ~between v y w \/ x = y \/
   between (euclid1 x v y w z) z (euclid2 x v y w z)) /\
(!x y z x' y' z'.
   ~equidistant x y x z \/ ~equidistant x x' x y' \/ ~between x y x' \/
   ~between y z' x' \/ between z (continuous x y z z' x' y') y') /\
(!x y z x' y' z'.
   ~equidistant x y x z \/ ~equidistant x x' x y' \/ ~between x y x' \/
   ~between y z' x' \/ equidistant x z' x (continuous x y z z' x' y')) /\
(!x y z v. ~(x = y) \/ ~between x z v \/ between y z v) /\
(!x y z v. ~(x = y) \/ ~between z x v \/ between z y v) /\
(!x y z v. ~(x = y) \/ ~between z v x \/ between z v y) /\
(!x y z v w. ~(x = y) \/ ~equidistant x z v w \/ equidistant y z v w) /\
(!x y z v w. ~(x = y) \/ ~equidistant z x v w \/ equidistant z y v w) /\
(!x y z v w. ~(x = y) \/ ~equidistant z v x w \/ equidistant z v y w) /\
(!x y z v w. ~(x = y) \/ ~equidistant z v w x \/ equidistant z v w y) /\
(!x y z x' y' z'.
   ~(x = y) \/ inner_pasch x z x' y' z' = inner_pasch y z x' y' z') /\
(!x y z x' y' z'.
   ~(x = y) \/ inner_pasch z x x' y' z' = inner_pasch z y x' y' z') /\
(!x y z x' y' z'.
   ~(x = y) \/ inner_pasch z x' x y' z' = inner_pasch z x' y y' z') /\
(!x y z x' y' z'.
   ~(x = y) \/ inner_pasch z x' y' x z' = inner_pasch z x' y' y z') /\
(!x y z x' y' z'.
   ~(x = y) \/ inner_pasch z x' y' z' x = inner_pasch z x' y' z' y) /\
(!x y z x' y' z'.
   ~(x = y) \/ euclid1 x z x' y' z' = euclid1 y z x' y' z') /\
(!x y z x' y' z'.
   ~(x = y) \/ euclid1 z x x' y' z' = euclid1 z y x' y' z') /\
(!x y z x' y' z'.
   ~(x = y) \/ euclid1 z x' x y' z' = euclid1 z x' y y' z') /\
(!x y z x' y' z'.
   ~(x = y) \/ euclid1 z x' y' x z' = euclid1 z x' y' y z') /\
(!x y z x' y' z'.
   ~(x = y) \/ euclid1 z x' y' z' x = euclid1 z x' y' z' y) /\
(!x y z x' y' z'.
   ~(x = y) \/ euclid2 x z x' y' z' = euclid2 y z x' y' z') /\
(!x y z x' y' z'.
   ~(x = y) \/ euclid2 z x x' y' z' = euclid2 z y x' y' z') /\
(!x y z x' y' z'.
   ~(x = y) \/ euclid2 z x' x y' z' = euclid2 z x' y y' z') /\
(!x y z x' y' z'.
   ~(x = y) \/ euclid2 z x' y' x z' = euclid2 z x' y' y z') /\
(!x y z x' y' z'.
   ~(x = y) \/ euclid2 z x' y' z' x = euclid2 z x' y' z' y) /\
(!x y z v w. ~(x = y) \/ extension x z v w = extension y z v w) /\
(!x y z v w. ~(x = y) \/ extension z x v w = extension z y v w) /\
(!x y z v w. ~(x = y) \/ extension z v x w = extension z v y w) /\
(!x y z v w. ~(x = y) \/ extension z v w x = extension z v w y) /\
(!x y z v w x' y'.
   ~(x = y) \/ continuous x z v w x' y' = continuous y z v w x' y') /\
(!x y z v w x' y'.
   ~(x = y) \/ continuous z x v w x' y' = continuous z y v w x' y') /\
(!x y z v w x' y'.
   ~(x = y) \/ continuous z v x w x' y' = continuous z v y w x' y') /\
(!x y z v w x' y'.
   ~(x = y) \/ continuous z v w x x' y' = continuous z v w y x' y') /\
(!x y z v w x' y'.
   ~(x = y) \/ continuous z v w x' x y' = continuous z v w x' y y') /\
(!x y z v w x' y'.
   ~(x = y) \/ continuous z v w x' y' x = continuous z v w x' y' y) ==>
lower_dimension_point_1 = lower_dimension_point_2 \/
lower_dimension_point_2 = lower_dimension_point_3 \/
lower_dimension_point_1 = lower_dimension_point_3 ==> F`},

{name = "GRP010-4",
 comments = [],
 goal = `
(!x. x = x) /\ (!x y. ~(x = y) \/ y = x) /\
(!x y z. ~(x = y) \/ ~(y = z) \/ x = z) /\ (!x y. ~(x = y) \/ i x = i y) /\
(!x y z. ~(x = y) \/ x * z = y * z) /\
(!x y z. ~(x = y) \/ z * x = z * y) /\ (!x y z. x * y * z = x * (y * z)) /\
(!x. 1 * x = x) /\ (!x. i x * x = 1) /\ c * b = 1 ==> ~(b * c = 1) ==> F`},

{name = "GRP057-1",
 comments = [],
 goal = `
(!x. x = x) /\ (!x y. ~(x = y) \/ y = x) /\
(!x y z. ~(x = y) \/ ~(y = z) \/ x = z) /\
(!x y z v. x * i (i (i y * (i x * z)) * v * i (y * v)) = z) /\
(!x y. ~(x = y) \/ i x = i y) /\ (!x y z. ~(x = y) \/ x * z = y * z) /\
(!x y z. ~(x = y) \/ z * x = z * y) ==>
~(i a1 * a1 = i b1 * b1) \/ ~(i b2 * b2 * a2 = a2) \/
~(a3 * b3 * c3 = a3 * (b3 * c3)) ==> F`},

{name = "GRP086-1",
 comments = ["Bug check: used to be unsolvable without sticky constraints"],
 goal = `
(!x. x = x) /\ (!x y. ~(x = y) \/ y = x) /\
(!x y z. ~(x = y) \/ ~(y = z) \/ x = z) /\
(!x y z. x * (y * z * i (x * z)) = y) /\ (!x y. ~(x = y) \/ i x = i y) /\
(!x y z. ~(x = y) \/ x * z = y * z) /\
(!x y z. ~(x = y) \/ z * x = z * y) ==>
(!x y.
   ~(i a1 * a1 = i b1 * b1) \/ ~(i b2 * b2 * a2 = a2) \/
   ~(a3 * b3 * c3 = a3 * (b3 * c3)) \/ ~(x * y = y * x)) ==> F`},

{name = "GRP104-1",
 comments = [],
 goal = `
(!x. x = x) /\ (!x y. ~(x = y) \/ y = x) /\
(!x y z. ~(x = y) \/ ~(y = z) \/ x = z) /\
(!x y z.
   double_divide x
     (inverse
        (double_divide
           (inverse (double_divide (double_divide x y) (inverse z))) y)) =
   z) /\ (!x y. x * y = inverse (double_divide y x)) /\
(!x y. ~(x = y) \/ inverse x = inverse y) /\
(!x y z. ~(x = y) \/ x * z = y * z) /\
(!x y z. ~(x = y) \/ z * x = z * y) /\
(!x y z. ~(x = y) \/ double_divide x z = double_divide y z) /\
(!x y z. ~(x = y) \/ double_divide z x = double_divide z y) ==>
(!x y.
   ~(inverse a1 * a1 = inverse b1 * b1) \/ ~(inverse b2 * b2 * a2 = a2) \/
   ~(a3 * b3 * c3 = a3 * (b3 * c3)) \/ ~(x * y = y * x)) ==> F`},

{name = "GRP128-4.003",
 comments = [],
 goal = `
(!x y.
   ~elt x \/ ~elt y \/ product e_1 x y \/ product e_2 x y \/
   product e_3 x y) /\
(!x y.
   ~elt x \/ ~elt y \/ product x e_1 y \/ product x e_2 y \/
   product x e_3 y) /\ elt e_1 /\ elt e_2 /\ elt e_3 /\ ~(e_1 == e_2) /\
~(e_1 == e_3) /\ ~(e_2 == e_1) /\ ~(e_2 == e_3) /\ ~(e_3 == e_1) /\
~(e_3 == e_2) /\
(!x y.
   ~elt x \/ ~elt y \/ product x y e_1 \/ product x y e_2 \/
   product x y e_3) /\
(!x y z v. ~product x y z \/ ~product x y v \/ z == v) /\
(!x y z v. ~product x y z \/ ~product x v z \/ y == v) /\
(!x y z v. ~product x y z \/ ~product v y z \/ x == v) ==>
(!x y z v. product x y z \/ ~product x z v \/ ~product z y v) /\
(!x y z v. product x y z \/ ~product v x z \/ ~product v y x) /\
(!x y z v. ~product x y z \/ ~product z y v \/ product x z v) ==> F`},

{name = "HEN006-3",
 comments = [],
 goal = `
(!x. x = x) /\ (!x y. ~(x = y) \/ y = x) /\
(!x y z. ~(x = y) \/ ~(y = z) \/ x = z) /\
(!x y. ~(x <= y) \/ x / y = 0) /\ (!x y. ~(x / y = 0) \/ x <= y) /\
(!x y. x / y <= x) /\ (!x y z. x / y / (z / y) <= x / z / y) /\
(!x. 0 <= x) /\ (!x y. ~(x <= y) \/ ~(y <= x) \/ x = y) /\ (!x. x <= 1) /\
(!x y z. ~(x = y) \/ x / z = y / z) /\
(!x y z. ~(x = y) \/ z / x = z / y) /\
(!x y z. ~(x = y) \/ ~(x <= z) \/ y <= z) /\
(!x y z. ~(x = y) \/ ~(z <= x) \/ z <= y) /\ a / b <= d ==>
~(a / d <= b) ==> F`},

{name = "LAT005-3",
 comments = ["SAM's lemma"],
 goal = `
(!x. x = x) /\ (!x y. ~(x = y) \/ y = x) /\
(!x y z. ~(x = y) \/ ~(y = z) \/ x = z) /\ (!x. meet x x = x) /\
(!x. join x x = x) /\ (!x y. meet x (join x y) = x) /\
(!x y. join x (meet x y) = x) /\ (!x y. meet x y = meet y x) /\
(!x y. join x y = join y x) /\
(!x y z. meet (meet x y) z = meet x (meet y z)) /\
(!x y z. join (join x y) z = join x (join y z)) /\
(!x y z. ~(x = y) \/ join x z = join y z) /\
(!x y z. ~(x = y) \/ join z x = join z y) /\
(!x y z. ~(x = y) \/ meet x z = meet y z) /\
(!x y z. ~(x = y) \/ meet z x = meet z y) /\ (!x. meet x 0 = 0) /\
(!x. join x 0 = x) /\ (!x. meet x 1 = x) /\ (!x. join x 1 = 1) /\
(!x y z. ~(meet x y = x) \/ meet y (join x z) = join x (meet z y)) /\
(!x y. ~complement x y \/ meet x y = 0) /\
(!x y. ~complement x y \/ join x y = 1) /\
(!x y. ~(meet x y = 0) \/ ~(join x y = 1) \/ complement x y) /\
(!x y z. ~(x = y) \/ ~complement x z \/ complement y z) /\
(!x y z. ~(x = y) \/ ~complement z x \/ complement z y) /\
complement r1 (join a b) /\ complement r2 (meet a b) ==>
~(r1 = meet (join r1 (meet r2 b)) (join r1 (meet r2 a))) ==> F`},

{name = "LCL009-1",
 comments = [],
 goal = `
(!x y. ~p (x - y) \/ ~p x \/ p y) /\
(!x y z. p (x - y - (z - y - (x - z)))) ==>
~p (a - b - c - (a - (b - c))) ==> F`},

{name = "LCL087-1",
 comments =
["Solved quickly by resolution when NOT tracking term-ordering constraints."],
 goal = `
(!x y. ~p (implies x y) \/ ~p x \/ p y) /\
(!x y z v w.
   p
     (implies (implies (implies x y) (implies z v))
        (implies w (implies (implies v x) (implies z x))))) ==>
~p (implies a (implies b a)) ==> F`},

{name = "LCL107-1",
 comments = ["A very small problem that's tricky to prove."],
 goal = `
(!x y. ~p (x - y) \/ ~p x \/ p y) /\
(!x y z v w x' y'.
   p
     (x - y - z - (v - w - (x' - w - (x' - v) - y')) -
      (z - (y - x - y')))) ==> ~p (a - b - c - (e - b - (a - e - c))) ==> F`},

{name = "LCL187-1",
 comments = [],
 goal = `
(!x. axiom (or (not (or x x)) x)) /\ (!x y. axiom (or (not x) (or y x))) /\
(!x y. axiom (or (not (or x y)) (or y x))) /\
(!x y z. axiom (or (not (or x (or y z))) (or y (or x z)))) /\
(!x y z. axiom (or (not (or (not x) y)) (or (not (or z x)) (or z y)))) /\
(!x. theorem x \/ ~axiom x) /\
(!x y. theorem x \/ ~axiom (or (not y) x) \/ ~theorem y) /\
(!x y z.
   theorem (or (not x) y) \/ ~axiom (or (not x) z) \/
   ~theorem (or (not z) y)) ==>
~theorem (or (not p) (or (not (not p)) q)) ==> F`},

{name = "LDA007-3",
 comments = [],
 goal = `
(!x. x = x) /\ (!x y. ~(x = y) \/ y = x) /\
(!x y z. ~(x = y) \/ ~(y = z) \/ x = z) /\
(!x y z. f x (f y z) = f (f x y) (f x z)) /\
(!x y z. ~(x = y) \/ f x z = f y z) /\
(!x y z. ~(x = y) \/ f z x = f z y) /\ tt = f t t /\ ts = f t s /\
tt_ts = f tt ts /\ tk = f t k /\ tsk = f ts k ==>
~(f t tsk = f tt_ts tk) ==> F`},

{name = "NUM001-1",
 comments = [],
 goal = `
(!x. x == x) /\ (!x y z. ~(x == y) \/ ~(y == z) \/ x == z) /\
(!x y. x + y == y + x) /\ (!x y z. x + (y + z) == x + y + z) /\
(!x y. x + y - y == x) /\ (!x y. x == x + y - y) /\
(!x y z. x - y + z == x + z - y) /\ (!x y z. x + y - z == x - z + y) /\
(!x y z v. ~(x == y) \/ ~(z == x + v) \/ z == y + v) /\
(!x y z v. ~(x == y) \/ ~(z == v + x) \/ z == v + y) /\
(!x y z v. ~(x == y) \/ ~(z == x - v) \/ z == y - v) /\
(!x y z v. ~(x == y) \/ ~(z == v - x) \/ z == v - y) ==>
~(a + b + c == a + (b + c)) ==> F`},

{name = "NUM014-1",
 comments = [],
 goal = `
(!x. product x x (square x)) /\
(!x y z. ~product x y z \/ product y x z) /\
(!x y z. ~product x y z \/ divides x z) /\
(!x y z v.
   ~prime x \/ ~product y z v \/ ~divides x v \/ divides x y \/
   divides x z) /\ prime a /\ product a (square c) (square b) ==>
~divides a b ==> F`},

{name = "PUZ001-1",
 comments = [],
 goal = `
lives agatha /\ lives butler /\ lives charles /\
(!x y. ~killed x y \/ ~richer x y) /\
(!x. ~hates agatha x \/ ~hates charles x) /\
(!x. ~hates x agatha \/ ~hates x butler \/ ~hates x charles) /\
hates agatha agatha /\ hates agatha charles /\
(!x y. ~killed x y \/ hates x y) /\
(!x. ~hates agatha x \/ hates butler x) /\
(!x. ~lives x \/ richer x agatha \/ hates butler x) ==>
killed butler agatha \/ killed charles agatha ==> F`},

{name = "PUZ011-1",
 comments =
["Curiosity: solved trivially by meson without cache cutting, but not with."],
 goal = `
ocean atlantic /\ ocean indian /\ borders atlantic brazil /\
borders atlantic uruguay /\ borders atlantic venesuela /\
borders atlantic zaire /\ borders atlantic nigeria /\
borders atlantic angola /\ borders indian india /\
borders indian pakistan /\ borders indian iran /\ borders indian somalia /\
borders indian kenya /\ borders indian tanzania /\ south_american brazil /\
south_american uruguay /\ south_american venesuela /\ african zaire /\
african nigeria /\ african angola /\ african somalia /\ african kenya /\
african tanzania /\ asian india /\ asian pakistan /\ asian iran ==>
(!x y z.
   ~ocean x \/ ~borders x y \/ ~african y \/ ~borders x z \/ ~asian z) ==>
F`},

{name = "PUZ020-1",
 comments = [],
 goal = `
(!x. x = x) /\ (!x y. ~(x = y) \/ y = x) /\
(!x y z. ~(x = y) \/ ~(y = z) \/ x = z) /\
(!x y. ~(x = y) \/ statement_by x = statement_by y) /\
(!x. ~person x \/ knight x \/ knave x) /\
(!x. ~person x \/ ~knight x \/ ~knave x) /\
(!x y. ~says x y \/ a_truth y \/ ~a_truth y) /\
(!x y. ~says x y \/ ~(x = y)) /\ (!x y. ~says x y \/ y = statement_by x) /\
(!x y. ~person x \/ ~(x = statement_by y)) /\
(!x. ~person x \/ ~a_truth (statement_by x) \/ knight x) /\
(!x. ~person x \/ a_truth (statement_by x) \/ knave x) /\
(!x y. ~(x = y) \/ ~knight x \/ knight y) /\
(!x y. ~(x = y) \/ ~knave x \/ knave y) /\
(!x y. ~(x = y) \/ ~person x \/ person y) /\
(!x y z. ~(x = y) \/ ~says x z \/ says y z) /\
(!x y z. ~(x = y) \/ ~says z x \/ says z y) /\
(!x y. ~(x = y) \/ ~a_truth x \/ a_truth y) /\
(!x y. ~knight x \/ ~says x y \/ a_truth y) /\
(!x y. ~knave x \/ ~says x y \/ ~a_truth y) /\ person husband /\
person wife /\ ~(husband = wife) /\ says husband (statement_by husband) /\
(~a_truth (statement_by husband) \/ ~knight husband \/ knight wife) /\
(a_truth (statement_by husband) \/ ~knight husband) /\
(a_truth (statement_by husband) \/ knight wife) /\
(~knight wife \/ a_truth (statement_by husband)) ==> ~knight husband ==> F`},

{name = "ROB002-1",
 comments = [],
 goal = `
(!x. x = x) /\ (!x y. ~(x = y) \/ y = x) /\
(!x y z. ~(x = y) \/ ~(y = z) \/ x = z) /\ (!x y. x + y = y + x) /\
(!x y z. x + y + z = x + (y + z)) /\
(!x y. negate (negate (x + y) + negate (x + negate y)) = x) /\
(!x y z. ~(x = y) \/ x + z = y + z) /\
(!x y z. ~(x = y) \/ z + x = z + y) /\
(!x y. ~(x = y) \/ negate x = negate y) /\ (!x. negate (negate x) = x) ==>
~(negate (a + negate b) + negate (negate a + negate b) = b) ==> F`}

] @

(* ========================================================================= *)
(* Some problems from HOL.                                                   *)
(* ========================================================================= *)

mkProblems "HOL subgoals sent to MESON_TAC" [

{name = "Coder_4_0",
 comments = [],
 goal = `
(!x y.
   x = y \/ ~{x . (EXT_POINT . x . y)} \/ ~{y . (EXT_POINT . x . y)}) /\
(!x y. x = y \/ {x . (EXT_POINT . x . y)} \/ {y . (EXT_POINT . x . y)}) /\
(!x y. x = y \/ ~(x . (EXT_POINT . x . y) = y . (EXT_POINT . x . y))) /\
(!x y. ~{x} \/ ~(x = y) \/ {y}) /\ ~{existential . (K . falsity)} /\
{existential . (K . truth)} /\ ~{universal . (K . falsity)} /\
{universal . (K . truth)} /\ ~{falsity} /\ {truth} /\
(!x y z. ~(APPEND . x . y = APPEND . z . y) \/ x = z) /\
(!x y z. ~(APPEND . x . y = APPEND . x . z) \/ y = z) ==>
{wf_encoder . p . e} /\ (!x. e . x = f . x \/ ~{p . x}) /\
{wf_encoder . p . f} /\ {p . q} /\ {p . q'} /\
APPEND . (f . q) . r = APPEND . (f . q') . r' /\ q = q' /\ ~(r' = r) ==> F`},

{name = "DeepSyntax_47",
 comments = [],
 goal = `
(!x y z v. ~(x = y) \/ ~(z = v) \/ int_add x z = int_add y v) /\
(!x y. ~(x = y) \/ int_neg x = int_neg y) /\
(!x y. ~(x = y) \/ int_of_num x = int_of_num y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ int_lt y v \/ ~int_lt x z) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ eval_form y v \/ ~eval_form x z) /\
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y z v.
   int_lt (int_add x y) (int_add z v) \/ ~int_lt x z \/ ~int_lt y v) /\
(!x. int_add x (int_of_num 0) = x) /\
(!x. int_add x (int_neg x) = int_of_num 0) /\
(!x y z. int_add x (int_add y z) = int_add (int_add x y) z) ==>
int_lt (int_neg d) (int_of_num 0) /\ eval_form g x /\
int_lt (int_add x d) i /\ ~int_lt x i ==> F`},

{name = "divides_9",
 comments = [],
 goal = `
(!x y z v. ~(x = y) \/ ~(z = v) \/ x * z = y * v) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ divides y v \/ ~divides x z) /\
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y z. x * (y * z) = x * y * z) /\ (!x y. x * y = y * x) /\
(!x y. ~divides x y \/ y = gv1556 x y * x) /\
(!x y z. divides x y \/ ~(y = z * x)) ==>
divides gv1546 gv1547 /\ ~divides gv1546 (gv1547 * gv1548) ==> F`},

{name = "Encode_28",
 comments = [],
 goal = `
(!x y z v. ~(x = y) \/ ~(z = v) \/ MOD x z = MOD y v) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ x * z = y * v) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ x + z = y + v) /\
(!x y. ~(x = y) \/ NUMERAL x = NUMERAL y) /\
(!x y. ~(x = y) \/ BIT2 x = BIT2 y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ EXP x z = EXP y v) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ DIV x z = DIV y v) /\
(!x y. ~(x = y) \/ BIT1 x = BIT1 y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ y < v \/ ~(x < z)) /\
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y. x * y = y * x) /\
(!x y z. MOD (MOD x (y * z)) y = MOD x y \/ ~(0 < y) \/ ~(0 < z)) ==>
(!x.
   MOD x (NUMERAL (BIT2 ZERO)) = 0 \/
   MOD x (NUMERAL (BIT2 ZERO)) = NUMERAL (BIT1 ZERO)) /\
MOD
  (DIV x (NUMERAL (BIT2 ZERO)) * NUMERAL (BIT2 ZERO) +
   MOD x (NUMERAL (BIT2 ZERO)))
  (NUMERAL (BIT2 ZERO) * EXP (NUMERAL (BIT2 ZERO)) m) =
MOD
  (DIV y (NUMERAL (BIT2 ZERO)) * NUMERAL (BIT2 ZERO) +
   MOD y (NUMERAL (BIT2 ZERO)))
  (NUMERAL (BIT2 ZERO) * EXP (NUMERAL (BIT2 ZERO)) m) /\
0 < EXP (NUMERAL (BIT2 ZERO)) m /\ 0 < NUMERAL (BIT2 ZERO) /\
(!x y.
   ~(MOD (x * NUMERAL (BIT2 ZERO) + MOD (x) (NUMERAL (BIT2 ZERO)))
       (NUMERAL (BIT2 ZERO)) =
     MOD (y * NUMERAL (BIT2 ZERO) + MOD (y) (NUMERAL (BIT2 ZERO)))
       (NUMERAL (BIT2 ZERO)))) ==> F`},

{name = "euclid_4",
 comments = [],
 goal = `
(!x y z v. ~(x = y) \/ ~(z = v) \/ x * z = y * v) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ divides y v \/ ~divides x z) /\
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y z. x * (y * z) = x * y * z) /\
(!x y. ~divides x y \/ y = x * gv5371 x y) /\
(!x y z. divides x y \/ ~(y = x * z)) ==>
divides gv5316 gv5317 /\ divides gv5315 gv5316 /\
~divides gv5315 gv5317 ==> F`},

{name = "euclid_8",
 comments = [],
 goal = `
(!x y z v. ~(x = y) \/ ~(z = v) \/ x * z = y * v) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ divides y v \/ ~divides x z) /\
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y. x * y = y * x) /\ (!x y z. x * (y * z) = x * y * z) /\
(!x y. ~divides x y \/ y = x * gv7050 x y) /\
(!x y z. divides x y \/ ~(y = x * z)) ==>
divides gv7000 gv7001 /\ ~divides gv7000 (gv7002 * gv7001) ==> F`},

{name = "extra_arith_6",
 comments = [],
 goal = `
(!x y z v. ~(x = y) \/ ~(z = v) \/ x * z = y * v) /\
(!x y. ~(x = y) \/ SUC x = SUC y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ y < v \/ ~(x < z)) /\
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y z. ~(SUC x * y = SUC x * z) \/ y = z) /\
(!x y z. SUC x * y = SUC x * z \/ ~(y = z)) /\
(!x y z. x * (y * z) = x * y * z) /\ (!x y. x * y = y * x) ==>
SUC n * b = q * (SUC n * a) /\ 0 < SUC n /\ ~(b = q * a) ==> F`},

{name = "extra_real_5",
 comments = [],
 goal = `
~{existential . (K . falsity)} /\ {existential . (K . truth)} /\
~{universal . (K . falsity)} /\ {universal . (K . truth)} /\ ~{falsity} /\
{truth} ==>
(!x y z v.
   {real_lt . x . (sup . P)} \/ ~{P . y} \/ ~{real_lt . x . y} \/
   ~{P . z} \/ ~{real_lte . (gv6327 . v) . v}) /\
(!x y z.
   ~{real_lt . x . (sup . P)} \/ {P . (gv6327 . x)} \/ ~{P . y} \/
   ~{real_lte . (gv6327 . z) . z}) /\
(!x y z.
   ~{real_lt . x . (sup . P)} \/ {real_lt . x . (gv6327 . x)} \/
   ~{P . y} \/ ~{real_lte . (gv6327 . z) . z}) /\
(!x y z.
   ~{real_lt . x . (sup . P)} \/ {real_lt . x . (gv6327 . x)} \/
   ~{P . y} \/ {P . (gv6327 . z)}) /\
(!x y z.
   ~{real_lt . x . (sup . P)} \/ {P . (gv6327 . x)} \/ ~{P . y} \/
   {P . (gv6327 . z)}) /\
(!x y z v.
   {real_lt . x . (sup . P)} \/ ~{P . y} \/ ~{real_lt . x . y} \/
   ~{P . z} \/ {P . (gv6327 . v)}) /\ {P . x} /\
(!x. {real_lte . x . z} \/ ~{P . x}) /\
(!x.
   {real_lt . (gv6328 . x) . (gv6329 . x)} \/
   {real_lt . (gv6328 . x) . x}) /\
(!x. {P . (gv6329 . x)} \/ {real_lt . (gv6328 . x) . x}) /\
(!x y.
   ~{real_lt . (gv6328 . x) . y} \/ ~{P . y} \/
   ~{real_lt . (gv6328 . x) . x}) ==> F`},

{name = "gcd_19",
 comments = [],
 goal = `
(!x y z v. ~(x = y) \/ ~(z = v) \/ x + z = y + v) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ x * z = y * v) /\
(!x y. ~(x = y) \/ NUMERAL x = NUMERAL y) /\
(!x y. ~(x = y) \/ BIT1 x = BIT1 y) /\ (!x y. ~(x = y) \/ SUC x = SUC y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ y <= v \/ ~(x <= z)) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ divides y v \/ ~divides x z) /\
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y z. x * (y + z) = x * y + x * z) /\ (!x y. x + SUC y = SUC (x + y)) /\
(!x y. SUC x + y = SUC (x + y)) /\ (!x. x + 0 = x) /\ (!x. 0 + x = x) /\
(!x y. x * SUC y = x + x * y) /\ (!x y. SUC x * y = x * y + y) /\
(!x. x * NUMERAL (BIT1 ZERO) = x) /\ (!x. NUMERAL (BIT1 ZERO) * x = x) /\
(!x. x * 0 = 0) /\ (!x. 0 * x = 0) /\ (!x y z. x + (y + z) = x + y + z) /\
(!x y z. divides x y \/ ~divides x z \/ ~divides x (z + y)) ==>
~(x + z <= x) /\ divides c (d * SUC x) /\ divides c (d * SUC (x + z)) /\
~divides c (d * z) ==> F`},
 
{name = "gcd_20",
 comments = [],
 goal = `
(!x y z v. ~(x = y) \/ ~(z = v) \/ x + z = y + v) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ x * z = y * v) /\
(!x y. ~(x = y) \/ NUMERAL x = NUMERAL y) /\
(!x y. ~(x = y) \/ BIT1 x = BIT1 y) /\ (!x y. ~(x = y) \/ SUC x = SUC y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ y <= v \/ ~(x <= z)) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ divides y v \/ ~divides x z) /\
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y z. x * (y + z) = x * y + x * z) /\ (!x y. x + SUC y = SUC (x + y)) /\
(!x y. SUC x + y = SUC (x + y)) /\ (!x. x + 0 = x) /\ (!x. 0 + x = x) /\
(!x y. x * SUC y = x + x * y) /\ (!x y. SUC x * y = x * y + y) /\
(!x. x * NUMERAL (BIT1 ZERO) = x) /\ (!x. NUMERAL (BIT1 ZERO) * x = x) /\
(!x. x * 0 = 0) /\ (!x. 0 * x = 0) /\ (!x y z. x + (y + z) = x + y + z) /\
(!x y z. divides x y \/ ~divides x z \/ ~divides x (z + y)) ==>
y <= y + z /\ divides c (d * SUC (y + z)) /\ divides c (d * SUC y) /\
~divides c (d * z) ==> F`},

{name = "gcd_21",
 comments = [],
 goal = `
(!x y z v. ~(x = y) \/ ~(z = v) \/ x + z = y + v) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ x * z = y * v) /\
(!x y. ~(x = y) \/ NUMERAL x = NUMERAL y) /\
(!x y. ~(x = y) \/ BIT1 x = BIT1 y) /\ (!x y. ~(x = y) \/ SUC x = SUC y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ divides y v \/ ~divides x z) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ y <= v \/ ~(x <= z)) /\
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y z. x * (y + z) = x * y + x * z) /\ (!x y. x + SUC y = SUC (x + y)) /\
(!x y. SUC x + y = SUC (x + y)) /\ (!x. x + 0 = x) /\ (!x. 0 + x = x) /\
(!x y. x * SUC y = x + x * y) /\ (!x y. SUC x * y = x * y + y) /\
(!x. x * NUMERAL (BIT1 ZERO) = x) /\ (!x. NUMERAL (BIT1 ZERO) * x = x) /\
(!x. x * 0 = 0) /\ (!x. 0 * x = 0) /\ (!x y z. x + (y + z) = x + y + z) /\
(!x y z. divides x y \/ ~divides x z \/ ~divides x (z + y)) ==>
divides c (d * SUC y) /\ y <= y + z /\ divides c (d * SUC (y + z)) /\
~divides c (d * z) ==> F`},

{name = "int_arith_6",
 comments = [],
 goal = `
(!x y z v. ~(x = y) \/ ~(z = v) \/ int_mul x z = int_mul y v) /\
(!x y. ~(x = y) \/ int_of_num x = int_of_num y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ int_lt y v \/ ~int_lt x z) /\
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y. int_mul x y = int_mul y x) /\ (!x. ~int_lt x x) /\
(!x y z. ~(int_mul x y = int_mul z y) \/ y = int_of_num 0 \/ x = z) /\
(!x y z. int_mul x y = int_mul z y \/ ~(y = int_of_num 0)) /\
(!x y z. int_mul x y = int_mul z y \/ ~(x = z)) ==>
int_lt (int_of_num 0) gv1085 /\
int_mul gv1085 gv1086 = int_mul gv1085 gv1087 /\ ~(gv1086 = gv1087) ==> F`},

{name = "int_arith_139",
 comments = [],
 goal = `
(!x y z v. ~(x = y) \/ ~(z = v) \/ int_add x z = int_add y v) /\
(!x y. ~(x = y) \/ int_of_num x = int_of_num y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ int_le y v \/ ~int_le x z) /\
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x. int_add (int_of_num 0) x = x) /\
(!x y z v.
   int_le (int_add x y) (int_add z v) \/ ~int_le x z \/ ~int_le y v) /\
(!x y z. int_add x (int_add y z) = int_add (int_add x y) z) /\
(!x y. int_add x y = int_add y x) /\
(!x y z. ~int_le (int_add x y) (int_add x z) \/ int_le y z) /\
(!x y z. int_le (int_add x y) (int_add x z) \/ ~int_le y z) ==>
int_le x y /\ int_le (int_of_num 0) (int_add c x) /\
~int_le (int_of_num 0) (int_add c y) ==> F`},

{name = "llist_69",
 comments = [],
 goal = `
(!x y. ~(x = y) \/ LTL x = LTL y) /\ (!x y. ~(x = y) \/ SOME x = SOME y) /\
(!x y. ~(x = y) \/ LHD x = LHD y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ LCONS x z = LCONS y v) /\
(!x y. ~(x = y) \/ g x = g y) /\ (!x y. ~(x = y) \/ THE x = THE y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ LNTH z x = LNTH v y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ LDROP z x = LDROP v y) /\
(!x y. ~(x = y) \/ SUC x = SUC y) /\
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y z. ~(x = LCONS y z) \/ LTL x = SOME z) /\
(!x y z. ~(x = LCONS y z) \/ LHD x = SOME y) /\
(!x y z. x = LCONS y z \/ ~(LHD x = SOME y) \/ ~(LTL x = SOME z)) ==>
LTL (g (LCONS LNIL t)) =
SOME (g (LCONS (THE (LTL (THE (LNTH n t)))) (THE (LDROP (SUC n) t)))) /\
LHD (g (LCONS LNIL t)) = SOME (THE (LHD (THE (LNTH n t)))) /\
LHD (g t) = SOME (THE (LHD (THE (LNTH n t)))) /\
LTL (g t) =
SOME (g (LCONS (THE (LTL (THE (LNTH n t)))) (THE (LDROP (SUC n) t)))) /\
~(g (LCONS LNIL t) = g t) ==> F`},

{name = "MachineTransition_0",
 comments = [],
 goal = `
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y.
   x = y \/ ~{x . (EXT_POINT . x . y)} \/ ~{y . (EXT_POINT . x . y)}) /\
(!x y. x = y \/ {x . (EXT_POINT . x . y)} \/ {y . (EXT_POINT . x . y)}) /\
(!x y. x = y \/ ~(x . (EXT_POINT . x . y) = y . (EXT_POINT . x . y))) /\
(!x y. ~{x} \/ ~(x = y) \/ {y}) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ x . z = y . v) /\
~{existential . (K . falsity)} /\ {existential . (K . truth)} /\
~{universal . (K . falsity)} /\ {universal . (K . truth)} /\ ~{falsity} /\
{truth} /\ Eq = equality /\
(!x y z. ~{Next . x . y . z} \/ {x . (pair . (gv940 . x . y . z) . z)}) /\
(!x y z. ~{Next . x . y . z} \/ {y . (gv940 . x . y . z)}) /\
(!x y z v. {Next . x . y . z} \/ ~{y . v} \/ ~{x . (pair . v . z)}) /\
(!x y z. ~{Prev . x . y . z} \/ {y . (gv935 . x . y . z)}) /\
(!x y z. ~{Prev . x . y . z} \/ {x . (pair . z . (gv935 . x . y . z))}) /\
(!x y z v. {Prev . x . y . z} \/ ~{x . (pair . z . v)} \/ ~{y . v}) ==>
{Next . gv914 . (Eq . gv915) . gv916} /\
~{Prev . gv914 . (Eq . gv916) . gv915} ==> F`},

{name = "MachineTransition_2_1",
 comments = [],
 goal = `
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y.
   x = y \/ ~{x . (EXT_POINT . x . y)} \/ ~{y . (EXT_POINT . x . y)}) /\
(!x y. x = y \/ {x . (EXT_POINT . x . y)} \/ {y . (EXT_POINT . x . y)}) /\
(!x y. x = y \/ ~(x . (EXT_POINT . x . y) = y . (EXT_POINT . x . y))) /\
(!x y. ~{x} \/ ~(x = y) \/ {y}) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ x . z = y . v) /\
~{existential . (K . falsity)} /\ {existential . (K . truth)} /\
~{universal . (K . falsity)} /\ {universal . (K . truth)} /\ ~{falsity} /\
{truth} /\
(!x y z. ReachIn . x . (Next . x . y) . z = ReachIn . x . y . (SUC . z)) /\
(!x y z. ~{Next . x . y . z} \/ {x . (pair . (gv5488 . x . y . z) . z)}) /\
(!x y z. ~{Next . x . y . z} \/ {y . (gv5488 . x . y . z)}) /\
(!x y z v. {Next . x . y . z} \/ ~{y . v} \/ ~{x . (pair . v . z)}) /\
(!x y z. ReachIn . x . y . (SUC . z) = Next . x . (ReachIn . x . y . z)) /\
(!x y. ReachIn . x . y . 0 = y) ==>
{ReachIn . R . (Next . R . B) . gv5278 . state} /\
(!x. ~{ReachIn . R . B . gv5278 . x} \/ ~{R . (pair . x . state)}) ==> F`},

{name = "MachineTransition_52",
 comments = [],
 goal = `
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y.
   x = y \/ ~{x . (EXT_POINT . x . y)} \/ ~{y . (EXT_POINT . x . y)}) /\
(!x y. x = y \/ {x . (EXT_POINT . x . y)} \/ {y . (EXT_POINT . x . y)}) /\
(!x y. x = y \/ ~(x . (EXT_POINT . x . y) = y . (EXT_POINT . x . y))) /\
(!x y. ~{x} \/ ~(x = y) \/ {y}) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ x . z = y . v) /\
~{existential . (K . falsity)} /\ {existential . (K . truth)} /\
~{universal . (K . falsity)} /\ {universal . (K . truth)} /\ ~{falsity} /\
{truth} /\
(!x y z.
   {(<=) . (gv7028 . x . y . z) . (add . x . (NUMERAL . (BIT1 . ZERO)))} \/
   z . (add . x . (NUMERAL . (BIT1 . ZERO))) =
   y . (add . x . (NUMERAL . (BIT1 . ZERO)))) /\
(!x y z.
   ~(x . (gv7028 . y . z . x) = z . (gv7028 . y . z . x)) \/
   x . (add . y . (NUMERAL . (BIT1 . ZERO))) =
   z . (add . y . (NUMERAL . (BIT1 . ZERO)))) /\
(!x y z v.
   ~(x . (gv7028 . y . z . x) = z . (gv7028 . y . z . x)) \/
   x . v = z . v \/ ~{(<=) . v . y}) /\
(!x y z v.
   {(<=) . (gv7028 . x . y . z) . (add . x . (NUMERAL . (BIT1 . ZERO)))} \/
   z . v = y . v \/ ~{(<=) . v . x}) /\
(!x y z v.
   ~{(<=) . x . (add . y . (NUMERAL . (BIT1 . ZERO)))} \/ z . x = v . x \/
   ~(z . (gv7027 . y . v . z) = v . (gv7027 . y . v . z)) \/
   ~(z . (add . y . (NUMERAL . (BIT1 . ZERO))) =
     v . (add . y . (NUMERAL . (BIT1 . ZERO))))) /\
(!x y z v.
   ~{(<=) . x . (add . y . (NUMERAL . (BIT1 . ZERO)))} \/ z . x = v . x \/
   {(<=) . (gv7027 . y . v . z) . y} \/
   ~(z . (add . y . (NUMERAL . (BIT1 . ZERO))) =
     v . (add . y . (NUMERAL . (BIT1 . ZERO))))) ==>
({FinPath . (pair . R . s) . f2 . n} \/
 ~{FinPath . (pair . R . s) . f1 . n} \/ ~(f1 . gv7034 = f2 . gv7034)) /\
(~{FinPath . (pair . R . s) . f2 . n} \/
 {FinPath . (pair . R . s) . f1 . n} \/ ~(f1 . gv7034 = f2 . gv7034)) /\
(~{FinPath . (pair . R . s) . f2 . n} \/
 {FinPath . (pair . R . s) . f1 . n} \/ {(<=) . gv7034 . n}) /\
({FinPath . (pair . R . s) . f2 . n} \/
 ~{FinPath . (pair . R . s) . f1 . n} \/ {(<=) . gv7034 . n}) /\
(!x.
   f1 . x = f2 . x \/
   ~{(<=) . x . (add . n . (NUMERAL . (BIT1 . ZERO)))}) /\
{FinPath . (pair . R . s) . f2 . n} /\
{R . (pair . (f2 . n) . (f2 . (add . n . (NUMERAL . (BIT1 . ZERO)))))} /\
~{FinPath . (pair . R . s) . f1 . n} ==> F`},

{name = "measure_138",
 comments = [],
 goal = `
(!x y z. ~SUBSET x y \/ IN z y \/ ~IN z x) /\
(!x y. SUBSET x y \/ IN (gv122874 x y) x) /\
(!x y. SUBSET x y \/ ~IN (gv122874 x y) y) /\
(!x. sigma_algebra (sigma x)) /\ (!x y z. ~IN x (INTER y z) \/ IN x z) /\
(!x y z. ~IN x (INTER y z) \/ IN x y) /\
(!x y z. IN x (INTER y z) \/ ~IN x y \/ ~IN x z) /\
(!x y.
   ~sigma_algebra x \/ IN (BIGUNION y) x \/ ~countable y \/ ~SUBSET y x) /\
(!x y. ~sigma_algebra x \/ IN (COMPL y) x \/ ~IN y x) /\
(!x. ~sigma_algebra x \/ IN EMPTY x) /\
(!x.
   sigma_algebra x \/ ~IN EMPTY x \/ ~IN (COMPL (gv122851 x)) x \/
   SUBSET (gv122852 x) x) /\
(!x.
   sigma_algebra x \/ ~IN EMPTY x \/ IN (gv122851 x) x \/
   SUBSET (gv122852 x) x) /\
(!x.
   sigma_algebra x \/ ~IN EMPTY x \/ IN (gv122851 x) x \/
   countable (gv122852 x)) /\
(!x.
   sigma_algebra x \/ ~IN EMPTY x \/ ~IN (COMPL (gv122851 x)) x \/
   countable (gv122852 x)) /\
(!x.
   sigma_algebra x \/ ~IN EMPTY x \/ IN (gv122851 x) x \/
   ~IN (BIGUNION (gv122852 x)) x) /\
(!x.
   sigma_algebra x \/ ~IN EMPTY x \/ ~IN (COMPL (gv122851 x)) x \/
   ~IN (BIGUNION (gv122852 x)) x) ==>
SUBSET c (INTER p (sigma a)) /\
(!x. IN (BIGUNION x) p \/ ~countable x \/ ~SUBSET x (INTER p (sigma a))) /\
SUBSET a p /\ IN EMPTY p /\
(!x. IN (COMPL x) p \/ ~IN x (INTER p (sigma a))) /\ countable c /\
~IN (BIGUNION c) (sigma a) ==> F`},

{name = "Omega_13",
 comments = [],
 goal = `
(!x y z v. ~(x = y) \/ ~(z = v) \/ int_mul x z = int_mul y v) /\
(!x y. ~(x = y) \/ int_of_num x = int_of_num y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ evalupper y v \/ ~evalupper x z) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ int_lt y v \/ ~int_lt x z) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ int_le y v \/ ~int_le x z) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ y < v \/ ~(x < z)) /\
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y. ~int_le x y \/ int_lt x y \/ x = y) /\
(!x y. int_le x y \/ ~int_lt x y) /\ (!x y. int_le x y \/ ~(x = y)) /\
(!x y z.
   int_lt x y \/
   ~int_lt (int_mul (int_of_num z) x) (int_mul (int_of_num z) y) \/
   ~(0 < z)) /\
(!x y z.
   ~int_lt x y \/
   int_lt (int_mul (int_of_num z) x) (int_mul (int_of_num z) y) \/
   ~(0 < z)) /\ (!x y z. int_lt x y \/ ~int_le x z \/ ~int_lt z y) ==>
(!x y. evalupper x uppers \/ ~evalupper y uppers \/ ~int_lt x y) /\
int_le (int_mul (int_of_num p_1) x) p_2 /\ evalupper x uppers /\
int_lt y x /\ 0 < p_1 /\ ~int_le (int_mul (int_of_num p_1) y) p_2 ==> F`},

{name = "Omega_71",
 comments = [],
 goal = `
(!x y z v. ~(x = y) \/ ~(z = v) \/ int_mul x z = int_mul y v) /\
(!x y. ~(x = y) \/ int_of_num x = int_of_num y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ x * z = y * v) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ int_add x z = int_add y v) /\
(!x y. ~(x = y) \/ NUMERAL x = NUMERAL y) /\
(!x y. ~(x = y) \/ BIT1 x = BIT1 y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ (x, z) = (y, v)) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ evallower y v \/ ~evallower x z) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ y < v \/ ~(x < z)) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ rshadow_row v y \/ ~rshadow_row z x) /\
(!x y z v.
   ~(x = y) \/ ~(z = v) \/ dark_shadow_cond_row v y \/
   ~dark_shadow_cond_row z x) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ int_le y v \/ ~int_le x z) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ EVERY y v \/ ~EVERY x z) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ int_lt y v \/ ~int_lt x z) /\
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y. int_mul x y = int_mul y x) /\
(!x y z. int_mul x (int_mul y z) = int_mul (int_mul x y) z) /\
(!x y z.
   int_le x y \/
   ~int_le (int_mul (int_of_num z) x) (int_mul (int_of_num z) y) \/
   ~(0 < z)) /\
(!x y z.
   ~int_le x y \/
   int_le (int_mul (int_of_num z) x) (int_mul (int_of_num z) y) \/
   ~(0 < z)) ==>
(!x y z.
   evallower (gv6249 x y z) lowers \/ ~(0 < y) \/ ~evallower x lowers \/
   ~rshadow_row (y, z) lowers \/ ~dark_shadow_cond_row (y, z) lowers) /\
(!x y z.
   int_le (int_mul (int_of_num x) (gv6249 y x z)) z \/ ~(0 < x) \/
   ~evallower y lowers \/ ~rshadow_row (x, z) lowers \/
   ~dark_shadow_cond_row (x, z) lowers) /\ 0 < c /\
int_le R (int_mul (int_of_num d) x) /\ evallower x lowers /\ 0 < d /\
EVERY fst_nzero lowers /\
int_le (int_mul (int_of_num c) R) (int_mul (int_of_num d) L) /\
rshadow_row (c, L) lowers /\ dark_shadow_cond_row (c, L) lowers /\
(!x.
   ~int_lt (int_mul (int_of_num d) L)
      (int_mul (int_of_num (c * d))
         (int_add x (int_of_num (NUMERAL (BIT1 ZERO))))) \/
   ~int_lt (int_mul (int_of_num (c * d)) x) (int_mul (int_of_num c) R)) /\
int_le (int_mul (int_of_num c) y) L /\ evallower y lowers /\
int_le (int_mul (int_of_num (c * d)) y) (int_mul (int_of_num d) L) /\
int_le (int_mul (int_of_num c) R) (int_mul (int_of_num (c * d)) x) /\
int_lt (int_mul (int_of_num (c * d)) y) (int_mul (int_of_num c) R) /\
0 < c * d /\
int_le (int_mul (int_of_num c) R) (int_mul (int_of_num (c * d)) j) /\
int_le (int_mul (int_of_num (c * d)) j) (int_mul (int_of_num d) L) /\
int_le (int_mul (int_mul (int_of_num c) (int_of_num d)) j)
  (int_mul (int_of_num d) L) /\ ~int_le (int_mul (int_of_num c) j) L ==> F`},

{name = "pred_set_1",
 comments = ["Small problem that's hard for ordered resolution"],
 goal = `
(!x y z. ~(x <= y) \/ p z y \/ ~p z x) /\ (!x y. x <= y \/ ~p (a x y) y) /\
(!x y. x <= y \/ p (a x y) x) /\ (!x y z. ~p x (y * z) \/ p x z) /\
(!x y z. ~p x (y * z) \/ p x y) /\
(!x y z. p x (y * z) \/ ~p x y \/ ~p x z) ==>
b <= c /\ b <= d /\ ~(b <= c * d) ==> F`},

{name = "pred_set_54_1",
 comments = [],
 goal = `
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y.
   x = y \/ ~{x . (EXT_POINT . x . y)} \/ ~{y . (EXT_POINT . x . y)}) /\
(!x y. x = y \/ {x . (EXT_POINT . x . y)} \/ {y . (EXT_POINT . x . y)}) /\
(!x y. x = y \/ ~(x . (EXT_POINT . x . y) = y . (EXT_POINT . x . y))) /\
(!x y. ~{x} \/ ~(x = y) \/ {y}) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ x . z = y . v) /\
~{existential . (K . falsity)} /\ {existential . (K . truth)} /\
~{universal . (K . falsity)} /\ {universal . (K . truth)} /\ ~{falsity} /\
{truth} /\
(!x y z. ~{IN . x . (INSERT . y . z)} \/ x = y \/ {IN . x . z}) /\
(!x y z. {IN . x . (INSERT . y . z)} \/ ~(x = y)) /\
(!x y z. {IN . x . (INSERT . y . z)} \/ ~{IN . x . z}) ==>
(!x y z. f . x . (f . y . z) = f . y . (f . x . z)) /\
(!x y z.
   ITSET . f . (INSERT . x . y) . z =
   ITSET . f . (DELETE . y . x) . (f . x . z) \/
   ~{less_than . (CARD . y) . v} \/ ~{FINITE . y}) /\ v = CARD . s /\
{FINITE . s} /\ REST . (INSERT . x . s) = t /\
CHOICE . (INSERT . x . s) = y /\ ~{IN . y . t} /\ ~{IN . x . s} /\
INSERT . x . s = INSERT . y . t /\ ~(x = y) /\ ~{IN . x . t} ==> F`},

{name = "prob_44",
 comments = [],
 goal = `
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y.
   x = y \/ ~{x . (EXT_POINT . x . y)} \/ ~{y . (EXT_POINT . x . y)}) /\
(!x y. x = y \/ {x . (EXT_POINT . x . y)} \/ {y . (EXT_POINT . x . y)}) /\
(!x y. x = y \/ ~(x . (EXT_POINT . x . y) = y . (EXT_POINT . x . y))) /\
(!x y. ~{x} \/ ~(x = y) \/ {y}) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ x . z = y . v) /\
~{existential . (K . falsity)} /\ {existential . (K . truth)} /\
~{universal . (K . falsity)} /\ {universal . (K . truth)} /\ ~{falsity} /\
{truth} ==>
(!x y z.
   ~{IN . x . (prefix_set . x')} \/ ~{IN . x . (prefix_set . (x))} \/
   ~{IN . y . c} \/ ~{IN . (gv24939 . y) . (prefix_set . (x))} \/
   ~{IN . (gv24939 . y) . (prefix_set . y)} \/
   ~{IN . (gv24940 . z) . (prefix_set . z)} \/
   ~{IN . (gv24940 . z) . (prefix_set . x')} \/ ~{IN . z . c}) /\
(!x y z.
   ~{IN . x . (prefix_set . x')} \/ ~{IN . x . (prefix_set . (x))} \/
   ~{IN . y . c} \/ {IN . (gv24939 . y) . (prefix_set . (x))} \/
   {IN . (gv24939 . y) . (prefix_set . y)} \/
   ~{IN . (gv24940 . z) . (prefix_set . z)} \/
   ~{IN . (gv24940 . z) . (prefix_set . x')} \/ ~{IN . z . c}) /\
(!x y z.
   ~{IN . x . (prefix_set . x')} \/ ~{IN . x . (prefix_set . (x))} \/
   ~{IN . y . c} \/ {IN . (gv24939 . y) . (prefix_set . (x))} \/
   {IN . (gv24939 . y) . (prefix_set . y)} \/
   {IN . (gv24940 . z) . (prefix_set . z)} \/
   {IN . (gv24940 . z) . (prefix_set . x')} \/ ~{IN . z . c}) /\
(!x y z.
   ~{IN . x . (prefix_set . x')} \/ ~{IN . x . (prefix_set . (x))} \/
   ~{IN . y . c} \/ ~{IN . (gv24939 . y) . (prefix_set . (x))} \/
   ~{IN . (gv24939 . y) . (prefix_set . y)} \/
   {IN . (gv24940 . z) . (prefix_set . z)} \/
   {IN . (gv24940 . z) . (prefix_set . x')} \/ ~{IN . z . c}) /\
{IN . x' . c} /\
{IN . (PREIMAGE . ((o) . SND . f) . s) . (events . bern)} /\
(!x y.
   f . x =
   pair . (FST . (f . (prefix_seq . y))) . (sdrop . (LENGTH . y) . x) \/
   ~{IN . y . c} \/ ~{IN . x . (prefix_set . y)}) /\
{IN . ((o) . SND . f) .
 (measurable . (events . bern) . (events . bern))} /\
{countable . (range . ((o) . FST . f))} /\
{IN . ((o) . FST . f) . (measurable . (events . bern) . UNIV)} /\
{prefix_cover . c} /\ {IN . s . (events . bern)} /\ {IN . x . c} /\
({IN . x'' . (prefix_set . x)} \/ {IN . x'' . (prefix_set . x')}) /\
(~{IN . x'' . (prefix_set . x)} \/ ~{IN . x'' . (prefix_set . x')}) /\
{IN . x''' . (prefix_set . x)} /\ {IN . x''' . (prefix_set . x')} ==> F`},

{name = "prob_53",
 comments = [],
 goal = `
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y.
   x = y \/ ~{x . (EXT_POINT . x . y)} \/ ~{y . (EXT_POINT . x . y)}) /\
(!x y. x = y \/ {x . (EXT_POINT . x . y)} \/ {y . (EXT_POINT . x . y)}) /\
(!x y. x = y \/ ~(x . (EXT_POINT . x . y) = y . (EXT_POINT . x . y))) /\
(!x y. ~{x} \/ ~(x = y) \/ {y}) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ x . z = y . v) /\
~{existential . (K . falsity)} /\ {existential . (K . truth)} /\
~{universal . (K . falsity)} /\ {universal . (K . truth)} /\ ~{falsity} /\
{truth} ==>
(!x y z.
   ~{IN . x . (prefix_set . x''')} \/ ~{IN . x . (prefix_set . x'')} \/
   ~{IN . y . c} \/ ~{IN . (gv39280 . y) . (prefix_set . x'')} \/
   ~{IN . (gv39280 . y) . (prefix_set . y)} \/
   ~{IN . (gv39280 . z) . (prefix_set . z)} \/
   ~{IN . (gv39280 . z) . (prefix_set . x''')} \/ ~{IN . z . c}) /\
(!x y z.
   ~{IN . x . (prefix_set . x''')} \/ ~{IN . x . (prefix_set . x'')} \/
   ~{IN . y . c} \/ {IN . (gv39280 . y) . (prefix_set . x'')} \/
   {IN . (gv39280 . y) . (prefix_set . y)} \/
   ~{IN . (gv39280 . z) . (prefix_set . z)} \/
   ~{IN . (gv39280 . z) . (prefix_set . x''')} \/ ~{IN . z . c}) /\
(!x y z.
   ~{IN . x . (prefix_set . x''')} \/ ~{IN . x . (prefix_set . x'')} \/
   ~{IN . y . c} \/ {IN . (gv39280 . y) . (prefix_set . x'')} \/
   {IN . (gv39280 . y) . (prefix_set . y)} \/
   {IN . (gv39280 . z) . (prefix_set . z)} \/
   {IN . (gv39280 . z) . (prefix_set . x''')} \/ ~{IN . z . c}) /\
(!x y z.
   ~{IN . x . (prefix_set . x''')} \/ ~{IN . x . (prefix_set . x'')} \/
   ~{IN . y . c} \/ ~{IN . (gv39280 . y) . (prefix_set . x'')} \/
   ~{IN . (gv39280 . y) . (prefix_set . y)} \/
   {IN . (gv39280 . z) . (prefix_set . z)} \/
   {IN . (gv39280 . z) . (prefix_set . x''')} \/ ~{IN . z . c}) /\
{IN . x''' . c} /\
{IN . (PREIMAGE . ((o) . SND . f) . x') . (events . bern)} /\
{IN . x' . (events . bern)} /\ {prefix_cover . c} /\
{IN . ((o) . FST . f) . (measurable . (events . bern) . UNIV)} /\
{countable . (range . ((o) . FST . f))} /\
{IN . ((o) . SND . f) .
 (measurable . (events . bern) . (events . bern))} /\
(!x y.
   f . x =
   pair . (FST . (f . (prefix_seq . y))) . (sdrop . (LENGTH . y) . x) \/
   ~{IN . y . c} \/ ~{IN . x . (prefix_set . y)}) /\
{IN . (PREIMAGE . ((o) . FST . f) . x) . (events . bern)} /\
{IN . x'' . c} /\
({IN . x'''' . (prefix_set . x'')} \/
 {IN . x'''' . (prefix_set . x''')}) /\
(~{IN . x'''' . (prefix_set . x'')} \/
 ~{IN . x'''' . (prefix_set . x''')}) /\
{IN . x''''' . (prefix_set . x'')} /\
{IN . x''''' . (prefix_set . x''')} ==> F`},

{name = "prob_extra_22",
 comments = [],
 goal = `
~{existential . (K . falsity)} /\ {existential . (K . truth)} /\
~{universal . (K . falsity)} /\ {universal . (K . truth)} /\ ~{falsity} /\
{truth} ==>
{P . x} /\ (!x. {real_lte . x . z} \/ ~{P . x}) /\
(!x y z v.
   {real_lt . x . (sup . P)} \/ ~{P . y} \/ ~{real_lt . x . y} \/
   ~{P . z} \/ ~{real_lte . (gv13960 . v) . v}) /\
(!x y z.
   ~{real_lt . x . (sup . P)} \/ {P . (gv13960 . x)} \/ ~{P . y} \/
   ~{real_lte . (gv13960 . z) . z}) /\
(!x y z.
   ~{real_lt . x . (sup . P)} \/ {real_lt . x . (gv13960 . x)} \/
   ~{P . y} \/ ~{real_lte . (gv13960 . z) . z}) /\
(!x y z.
   ~{real_lt . x . (sup . P)} \/ {real_lt . x . (gv13960 . x)} \/
   ~{P . y} \/ {P . (gv13960 . z)}) /\
(!x y z.
   ~{real_lt . x . (sup . P)} \/ {P . (gv13960 . x)} \/ ~{P . y} \/
   {P . (gv13960 . z)}) /\
(!x y z v.
   {real_lt . x . (sup . P)} \/ ~{P . y} \/ ~{real_lt . x . y} \/
   ~{P . z} \/ {P . (gv13960 . v)}) /\
(!x.
   {real_lt . (gv13925 . x) . (gv13926 . x)} \/
   {real_lt . (gv13925 . x) . x}) /\
(!x. {P . (gv13926 . x)} \/ {real_lt . (gv13925 . x) . x}) /\
(!x y.
   ~{real_lt . (gv13925 . x) . y} \/ ~{P . y} \/
   ~{real_lt . (gv13925 . x) . x}) ==> F`},

{name = "root2_2",
 comments = [],
 goal = `
(!x y z v. ~(x = y) \/ ~(z = v) \/ x * z = y * v) /\
(!x y. ~(x = y) \/ NUMERAL x = NUMERAL y) /\
(!x y. ~(x = y) \/ BIT2 x = BIT2 y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ EXP x z = EXP y v) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ y < v \/ ~(x < z)) /\
(!x y. ~(x = y) \/ EVEN y \/ ~EVEN x) /\
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y.
   ~(EXP (NUMERAL (BIT2 ZERO) * x) (NUMERAL (BIT2 ZERO)) =
     NUMERAL (BIT2 ZERO) * EXP y (NUMERAL (BIT2 ZERO))) \/
   NUMERAL (BIT2 ZERO) * EXP x (NUMERAL (BIT2 ZERO)) =
   EXP y (NUMERAL (BIT2 ZERO))) /\
(!x y.
   EXP (NUMERAL (BIT2 ZERO) * x) (NUMERAL (BIT2 ZERO)) =
   NUMERAL (BIT2 ZERO) * EXP y (NUMERAL (BIT2 ZERO)) \/
   ~(NUMERAL (BIT2 ZERO) * EXP x (NUMERAL (BIT2 ZERO)) =
     EXP y (NUMERAL (BIT2 ZERO)))) /\
(!x. ~EVEN x \/ x = NUMERAL (BIT2 ZERO) * gv4671 x) /\
(!x y. EVEN x \/ ~(x = NUMERAL (BIT2 ZERO) * y)) /\
(!x y. ~EVEN (x * y) \/ EVEN x \/ EVEN y) /\
(!x y. EVEN (x * y) \/ ~EVEN x) /\ (!x y. EVEN (x * y) \/ ~EVEN y) /\
(!x. EXP x (NUMERAL (BIT2 ZERO)) = x * x) /\
(!x. EVEN (NUMERAL (BIT2 ZERO) * x)) ==>
EXP (NUMERAL (BIT2 ZERO) * k) (NUMERAL (BIT2 ZERO)) =
NUMERAL (BIT2 ZERO) * EXP n (NUMERAL (BIT2 ZERO)) /\
(!x y.
   ~(EXP x (NUMERAL (BIT2 ZERO)) =
     NUMERAL (BIT2 ZERO) * EXP y (NUMERAL (BIT2 ZERO))) \/ x = 0 \/
   ~(x < NUMERAL (BIT2 ZERO) * k)) /\
(!x y.
   ~(EXP x (NUMERAL (BIT2 ZERO)) =
     NUMERAL (BIT2 ZERO) * EXP y (NUMERAL (BIT2 ZERO))) \/ y = 0 \/
   ~(x < NUMERAL (BIT2 ZERO) * k)) /\
(!x. ~(n = NUMERAL (BIT2 ZERO) * x)) ==> F`},

{name = "TermRewriting_13",
 comments = [],
 goal = `
~{existential . (K . falsity)} /\ {existential . (K . truth)} /\
~{universal . (K . falsity)} /\ {universal . (K . truth)} /\ ~{falsity} /\
{truth} /\
(!x y z v.
   ~{RTC . x . y . z} \/ {RTC . x . v . z} \/ ~{RTC . x . v . y}) ==>
{WCR . R} /\ {SN . R} /\
(!x y z.
   ~{RTC . R . x . y} \/ ~{RTC . R . x . z} \/
   {RTC . R . y . (gv1300 . x . z . y)} \/ ~{TC . R . (x) . x}) /\
(!x y z.
   ~{RTC . R . x . y} \/ ~{RTC . R . x . z} \/
   {RTC . R . z . (gv1300 . x . z . y)} \/ ~{TC . R . (x) . x}) /\
{RTC . R . x . y} /\ {RTC . R . x . z} /\ {R . x . y1} /\
{RTC . R . y1 . y} /\ {R . x . z1} /\ {RTC . R . z1 . z} /\
{RTC . R . y1 . x0} /\ {RTC . R . z1 . x0} /\ {TC . R . x . y1} /\
{TC . R . x . z1} /\ {RTC . R . y . y2} /\ {RTC . R . x0 . y2} /\
{RTC . R . z . z2} /\ {RTC . R . x0 . z2} /\ {TC . R . x . x0} /\
(!x. ~{RTC . R . y . x} \/ ~{RTC . R . z . x}) ==> F`}

];
