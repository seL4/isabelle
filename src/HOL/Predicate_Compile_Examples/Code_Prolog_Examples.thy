theory Code_Prolog_Examples
imports "~~/src/HOL/Library/Code_Prolog"
begin

section {* Example append *}


inductive append
where
  "append [] ys ys"
| "append xs ys zs ==> append (x # xs) ys (x # zs)"

setup {* Code_Prolog.map_code_options (K
  {ensure_groundness = false,
   limit_globally = NONE,
   limited_types = [],
   limited_predicates = [],
   replacing = [],
   manual_reorder = []}) *}

values_prolog "{(x, y, z). append x y z}"

values_prolog 4 "{(z, x, y). append x y ((1::nat) # (2 # (3 # z)))}"

values_prolog 3 "{(x, y, z). append x y z}"

setup {* Code_Prolog.map_code_options (K
  {ensure_groundness = false,
   limit_globally = NONE,
   limited_types = [],
   limited_predicates = [],
   replacing = [],
   manual_reorder = []}) *}

values_prolog "{(x, y, z). append x y z}"

setup {* Code_Prolog.map_code_options (K
  {ensure_groundness = false,
   limit_globally = NONE,
   limited_types = [],
   limited_predicates = [],
   replacing = [],
   manual_reorder = []}) *}


section {* Example queens *}

inductive nodiag :: "int => int => int list => bool"
where
  "nodiag B D []"
| "D \<noteq> N - B ==> D \<noteq> B - N ==> Da = D + 1 ==> nodiag B Da L ==> nodiag B D (N # L)"

text {*
qdelete(A, [A|L], L).
qdelete(X, [A|Z], [A|R]) :-
  qdelete(X, Z, R).
*}

inductive qdelete :: "int => int list => int list => bool"
where
  "qdelete A (A # L) L"
| "qdelete X Z R ==> qdelete X (A # Z) (A # R)"

text {*
qperm([], []).
qperm([X|Y], K) :-
  qdelete(U, [X|Y], Z),
  K = [U|V],
  qperm(Z, V).
*}

inductive qperm :: "int list => int list => bool"
where
  "qperm [] []"
| "qdelete U (X # Y) Z ==> qperm Z V ==> qperm (X # Y) (U # V)"

text {*
safe([]).
safe([N|L]) :-
  nodiag(N, 1, L),
  safe(L).
*}

inductive safe :: "int list => bool"
where
  "safe []"
| "nodiag N 1 L ==> safe L ==> safe (N # L)"

text {*
queen(Data, Out) :-
  qperm(Data, Out),
  safe(Out)
*}

inductive queen :: "int list => int list => bool"
where
  "qperm Data Out ==> safe Out ==> queen Data Out"

inductive queen_9
where
  "queen [1,2,3,4,5,6,7,8,9] ys ==> queen_9 ys"

values_prolog 10 "{ys. queen_9 ys}"


section {* Example symbolic derivation *}

hide_const Pow

datatype_new expr = Log expr | Mult expr expr | Div expr expr | x | Num int | Plus expr expr
  | Minus expr expr | Uminus expr | Pow expr int | Exp expr

text {*

d(U + V, X, DU + DV) :-
  cut,
  d(U, X, DU),
  d(V, X, DV).
d(U - V, X, DU - DV) :-
  cut,
  d(U, X, DU),
  d(V, X, DV).
d(U * V, X, DU * V + U * DV) :-
  cut,
  d(U, X, DU),
  d(V, X, DV).
d(U / V, X, (DU * V - U * DV) / ^(V, 2)) :-
  cut,
  d(U, X, DU),
  d(V, X, DV).
d(^(U, N), X, DU * num(N) * ^(U, N1)) :-
  cut,
  N1 is N - 1,
  d(U, X, DU).
d(-U, X, -DU) :-
  cut,
  d(U, X, DU).
d(exp(U), X, exp(U) * DU) :-
  cut,
  d(U, X, DU).
d(log(U), X, DU / U) :-
  cut,
  d(U, X, DU).
d(x, X, num(1)) :-
  cut.
d(num(_), _, num(0)).

*}

inductive d :: "expr => expr => expr => bool"
where
  "d U X DU ==> d V X DV ==> d (Plus U V) X (Plus DU DV)"
| "d U X DU ==> d V X DV ==> d (Minus U V) X (Minus DU DV)"
| "d U X DU ==> d V X DV ==> d (Mult U V) X (Plus (Mult DU V) (Mult U DV))"
| "d U X DU ==> d V X DV ==> d (Div U V) X (Div (Minus (Mult DU V) (Mult U DV)) (Pow V 2))"
| "d U X DU ==> N1 = N - 1 ==> d (Pow U N) X (Mult DU (Mult (Num N) (Pow U N1)))"
| "d U X DU ==> d (Uminus U) X (Uminus DU)"
| "d U X DU ==> d (Exp U) X (Mult (Exp U) DU)"
| "d U X DU ==> d (Log U) X (Div DU U)"
| "d x X (Num 1)"
| "d (Num n) X (Num 0)"

text {*
ops8(E) :-
  d((x + num(1)) * ((^(x, 2) + num(2)) * (^(x, 3) + num(3))), x, E).

divide10(E) :-
  d(((((((((x / x) / x) / x) / x) / x) / x) / x) / x) / x, x, E).

log10(E) :-
  d(log(log(log(log(log(log(log(log(log(log(x)))))))))), x, E).

times10(E) :-
  d(((((((((x * x) * x) * x) * x) * x) * x) * x) * x) * x, x, E)
*}

inductive ops8 :: "expr => bool"
where
  "d (Mult (Plus x (Num 1)) (Mult (Plus (Pow x 2) (Num 2)) (Plus (Pow x 3) (Num 3)))) x e ==> ops8 e"

inductive divide10
where
  "d (Div (Div (Div (Div (Div (Div (Div (Div (Div x x) x) x) x) x) x) x) x) x) x e ==> divide10 e"

inductive log10
where
 "d (Log (Log (Log (Log (Log (Log (Log (Log (Log (Log x)))))))))) x e ==> log10 e"

inductive times10
where
  "d (Mult (Mult (Mult (Mult (Mult (Mult (Mult (Mult (Mult x x) x) x) x) x) x) x) x) x) x e ==> times10 e"

values_prolog "{e. ops8 e}"
values_prolog "{e. divide10 e}"
values_prolog "{e. log10 e}"
values_prolog "{e. times10 e}"

section {* Example negation *}

datatype_new abc = A | B | C

inductive notB :: "abc => bool"
where
  "y \<noteq> B \<Longrightarrow> notB y"

setup {* Code_Prolog.map_code_options (K
  {ensure_groundness = true,
   limit_globally = NONE,
   limited_types = [],
   limited_predicates = [],
   replacing = [],
   manual_reorder = []}) *}

values_prolog 2 "{y. notB y}"

inductive notAB :: "abc * abc \<Rightarrow> bool"
where
  "y \<noteq> A \<Longrightarrow> z \<noteq> B \<Longrightarrow> notAB (y, z)"

values_prolog 5 "{y. notAB y}"

section {* Example prolog conform variable names *}

inductive equals :: "abc => abc => bool"
where
  "equals y' y'"

values_prolog 1 "{(y, z). equals y z}"

end
