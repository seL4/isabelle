fun cread thy s = read_cterm (sign_of thy) (s, (TVar(("DUMMY",0),[])));
fun read thy = term_of o cread thy;
fun Term s = read WF1.thy s;

fun Rfunc thy R eqs =
   let val {induction,rules,theory,tcs} = 
              timeit(fn () => Tfl.Rfunction thy (read thy R) (read thy eqs))
   in {induction=induction, rules=rules, theory=theory, 
       tcs = map (cterm_of (sign_of theory)) tcs}
   end;

val Rfunction = Rfunc WF1.thy;

fun function tm = timeit (fn () => Tfl.function WF1.thy (Term tm));


(*---------------------------------------------------------------------------
 * Factorial. Notice how functions without pattern matching are often harder 
 * to deal with than those with! Unfortunately, not all functions can be 
 * described purely by pattern matching, e.g., "variant" as below.
 *---------------------------------------------------------------------------*)
function "fact x = (if (x = 0) then Suc 0 else x * fact (x - Suc 0))";

Rfunction"pred_nat"
         "fact x = (if (x = 0) then Suc 0 else x * fact (x - Suc 0))";

function "(Fact 0 = (Suc 0)) & \
     \    (Fact (Suc x) = (Fact x * Suc x))";

Rfunction "pred_nat"
          "(Fact 0 = (Suc 0)) & \
      \    (Fact (Suc x) = (Fact x * Suc x))";

(*---------------------------------------------------------------------------
 * Fibonacci.
 *---------------------------------------------------------------------------*)
function "(Fib 0 = (Suc 0)) &  \
     \    (Fib (Suc 0) = (Suc 0)) & \
     \    (Fib (Suc(Suc x)) = (Fib x + Fib (Suc x)))";

(* "<" doesn't currently work smoothly *)
Rfunction"{p::(nat*nat). fst p < snd p}"
         "(Fib 0 = (Suc 0)) & \
     \    (Fib (Suc 0) = (Suc 0)) & \
     \    (Fib (Suc(Suc x)) = (Fib x + Fib (Suc x)))";


(* "trancl pred" means "<" and works better *)
Rfunction"trancl pred_nat"
         "(Fib 0 = (Suc 0)) & \
     \    (Fib (Suc 0) = (Suc 0)) & \
     \    (Fib (Suc(Suc x)) = (Fib x + Fib (Suc x)))";

(*---------------------------------------------------------------------------
 * Ackermann.
 *---------------------------------------------------------------------------*)
Rfunction"pred_nat ** pred_nat"
         "(Ack (0,n) =  (n + Suc 0)) & \
    \    (Ack (Suc m,0) = (Ack (m, Suc 0))) & \
    \    (Ack (Suc m, Suc n) = Ack (m, Ack (Suc m, n)))";

(*---------------------------------------------------------------------------
 * Almost primitive recursion. 
 *---------------------------------------------------------------------------*)
function"(map2(f, [], L) = []) & \
    \    (map2(f, h#t, []) = []) & \
    \    (map2(f, h1#t1, h2#t2) = f h1 h2 # map2 (f, t1, t2))";

(* Swap arguments *)
function"(map2(([],L), f) = []) & \
    \    (map2((h#t, []), f) = []) &  \
    \    (map2((h1#t1, h2#t2), f) = f h1 h2 # map2((t1,t2),f))";

Rfunction
   "measure((length o fst o snd)::('a=>'b=>'c)*'a list*'b list => nat)"
    "(map2((f::'a=>'b=>'c), ([]::'a list), (L::'b list)) = [])  & \
\    (map2(f, h#t, []) = []) & \
\    (map2(f, h1#t1, h2#t2) = f h1 h2 # map2 (f, t1, t2))";

(*---------------------------------------------------------------------------
 * Relation "R" holds stepwise in a list
 *---------------------------------------------------------------------------*)
function"(finiteRchain ((R::'a=>'a=>bool),  ([]::'a list)) = True) & \
    \    (finiteRchain (R, [x]) = True) & \
    \    (finiteRchain (R, x#y#rst) = (R x y & finiteRchain(R, y#rst)))";


Rfunction"measure ((length o snd)::('a=>'a=>bool) * 'a list => nat)"
         "(finiteRchain((R::'a=>'a=>bool),  ([]::'a list)) = True) & \
     \    (finiteRchain(R, [x]) = True) & \
     \    (finiteRchain(R, x#y#rst) = (R x y & finiteRchain(R, y#rst)))";

(*---------------------------------------------------------------------------
 * Quicksort.
 *---------------------------------------------------------------------------*)
function"(qsort(ord,  []) = []) & \
    \    (qsort(ord, x#rst) = \
    \       qsort(ord,filter(not o ord x) rst) \
    \       @[x]@      \
    \       qsort(ord,filter(ord x) rst))";

Rfunction"measure ((length o snd)::('a=>'a=>bool) * 'a list => nat)"
         "(qsort((ord::'a=>'a=>bool),  ([]::'a list))  = []) & \
     \    (qsort(ord, x#rst) = \
     \       qsort(ord,filter(not o ord x) rst) \
     \       @[x]@  \
     \       qsort(ord,filter(ord x) rst))";

(*---------------------------------------------------------------------------
 * Variant.
 *---------------------------------------------------------------------------*)
function"variant(x, L) = (if (x mem L) then variant(Suc x, L) else x)";

Rfunction
 "measure(%(p::nat*nat list). length(filter(%y. fst(p) <= y) (snd p)))"
 "variant(x, L) = (if (x mem L) then variant(Suc x, L) else x)";

(*---------------------------------------------------------------------------
 * Euclid's algorithm
 *---------------------------------------------------------------------------*)
function"(gcd ((0::nat),(y::nat)) = y) & \
    \    (gcd (Suc x, 0) = Suc x) & \
    \    (gcd (Suc x, Suc y) =      \
    \        (if (y <= x) then gcd(x - y, Suc y) \
    \                     else gcd(Suc x, y - x)))";


(*---------------------------------------------------------------------------
 * Wrong answer because Isabelle rewriter (going bottom-up) attempts to
 * apply congruence rule for split to "split" but can't because split is only
 * partly applied. It then fails, instead of just not doing the rewrite.
 * Tobias has said he'll fix it.
 *
 * ... July 96 ... seems to have been fixed.
 *---------------------------------------------------------------------------*)
 
Rfunction"measure (split (op+) ::nat*nat=>nat)"
         "(gcd ((0::nat),(y::nat)) = y) & \
        \ (gcd (Suc x, 0) = Suc x) & \
        \ (gcd (Suc x, Suc y) = \
        \     (if (y <= x) then gcd(x - y, Suc y) \
        \                  else gcd(Suc x, y - x)))";

(*---------------------------------------------------------------------------
 * A simple nested function.
 *---------------------------------------------------------------------------*)
Rfunction"trancl pred_nat"
         "(g 0 = 0) & \
        \ (g(Suc x) = g(g x))";

(*---------------------------------------------------------------------------
 * A clever division algorithm. Primitive recursive.
 *---------------------------------------------------------------------------*)
function"(Div(0,x) = (0,0)) & \
       \ (Div(Suc x, y) =     \
       \     (let (q,r) = Div(x,y) \
       \      in if (y <= Suc r) then (Suc q,0) else (q, Suc r)))";

Rfunction"inv_image pred_nat (fst::nat*nat=>nat)"
         "(Div(0,x) = (0,0)) & \
        \ (Div(Suc x, y) =     \
        \    (let q = fst(Div(x,y)); \
        \         r = snd(Div(x,y))  \
        \     in                     \
        \     if (y <= Suc r) then (Suc q,0) else (q, Suc r)))";

(*---------------------------------------------------------------------------
 * Testing nested contexts.
 *---------------------------------------------------------------------------*)
function"(f(0,x) = (0,0)) & \
       \ (f(Suc x, y) = \
       \     (let z = x \
       \      in        \
       \      if (0<y) then (0,0) else f(z,y)))";


function"(f(0,x) = (0,0)) & \
       \ (f(Suc x, y) =     \
       \      (if y = x     \
       \       then (if (0<y) then (0,0) else f(x,y)) \
       \       else (x,y)))";


(*---------------------------------------------------------------------------
 * Naming trickery in lets.
 *---------------------------------------------------------------------------*)

(* No trick *)
function "(test(x, []) = x) & \
        \ (test(x,h#t) = (let y = Suc x in test(y,t)))";

(* Trick *)
function"(test(x, []) = x) & \
       \ (test(x,h#t) =      \
       \     (let x = Suc x  \
       \      in             \
       \      test(x,t)))";

(* Tricky naming, plus nested contexts *)
function "vary(x, L) =  \
        \   (if (x mem L) \
        \    then (let x = Suc x \
        \          in vary(x,L)) \
        \    else x)";


(*---------------------------------------------------------------------------
 * Handling paired lets of various kinds
 *---------------------------------------------------------------------------*)
function
    "(Fib(0) = Suc 0) &  \
   \ (Fib (Suc 0) = Suc 0) & \
   \ (Fib (Suc (Suc n)) =    \
   \     (let (x,y) = (Fib (Suc n), Fib n) in x+y))";


function
   "(qsort((ord::'a=>'a=>bool),  ([]::'a list))   = []) &  \
  \ (qsort(ord, x#rst) = \
  \     (let (L1,L2) = (filter(not o ord x) rst, \
  \                     filter (ord x) rst) \
  \      in  \
  \      qsort(ord,L1)@[x]@qsort(ord,L2)))";

function"(qsort((ord::'a=>'a=>bool),  ([]::'a list))   = []) & \
       \ (qsort(ord, x#rst) = \
       \    (let (L1,L2,P) = (filter(not o ord x) rst, \
       \                      filter (ord x) rst, x)   \
       \     in \
       \     qsort(ord,L1)@[x]@qsort(ord,L2)))";

function"(qsort((ord::'a=>'a=>bool),  ([]::'a list))   = []) & \
       \ (qsort(ord, x#rst) = \
       \     (let (L1,L2) = (filter(not o ord x) rst, \
       \                     filter (ord x) rst);     \
       \            (p,q) = (x,rst) \
       \      in \
       \      qsort(ord,L1)@[x]@qsort(ord,L2)))";


(*---------------------------------------------------------------------------
 * A biggish function
 *---------------------------------------------------------------------------*)

function"(acc1(A,[],s,xss,zs,xs) = \
\              (if xs=[] then (xss, zs) \
\                        else acc1(A, zs,s,(xss @ [xs]),[],[]))) & \
\         (acc1(A,(y#ys), s, xss, zs, xs) = \
\              (let s' = s; \
\                  zs' = (if fst A s' then [] else zs@[y]); \
\                  xs' = (if fst A s' then xs@zs@[y] else xs) \
\               in  \
\               acc1(A, ys, s', xss, zs', xs')))";


(*---------------------------------------------------------------------------
 * Nested, with context.
 *---------------------------------------------------------------------------*)
Rfunction"pred_nat"
  "(k 0 = 0) & \
\  (k (Suc n) = (let x = k (Suc 0)  \
\                in if (0=Suc 0) then k (Suc(Suc 0)) else n))";


(*---------------------------------------------------------------------------
 * A function that partitions a list into two around a predicate "P".
 *---------------------------------------------------------------------------*)
val {theory,induction,rules,tcs} = 
  Rfunction
   "inv_image pred_list \
    \  ((fst o snd)::('a=>bool)*'a list*'a list*'a list => 'a list)"

  "(part(P::'a=>bool, [], l1,l2) = (l1,l2)) & \
\  (part(P, h#rst, l1,l2) = \
\       (if P h then part(P,rst, h#l1,  l2) \
\               else part(P,rst,  l1,  h#l2)))";

  
(*---------------------------------------------------------------------------
 * Another quicksort. 
 *---------------------------------------------------------------------------*)
Rfunc theory "measure ((length o snd)::('a=>'a=>bool) * 'a list => nat)"
 "(fqsort(ord,[]) = []) & \
\ (fqsort(ord, x#rst) = \
 \   (let less = fst(part((%y. ord y x), rst,([],[]))); \
  \       more = snd(part((%y. ord y x), rst,([],[]))) \
   \  in \
    \ fqsort(ord,less)@[x]@fqsort(ord,more)))";

Rfunc theory "measure ((length o snd)::('a=>'a=>bool) * 'a list => nat)"
 "(fqsort(ord,[]) = []) & \
\  (fqsort(ord, x#rst) = \
 \   (let (less,more) = part((%y. ord y x), rst,([],[])) \
  \   in \
   \  fqsort(ord,less)@[x]@fqsort(ord,more)))";


(* Should fail on repeated variables. *)
function"(And(x,[]) = x) & \
      \  (And(y, y#t) = And(y, t))";

