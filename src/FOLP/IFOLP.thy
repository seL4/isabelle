(*  Title:      FOLP/IFOLP.thy
    ID:         $Id$
    Author:     Martin D Coen, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Intuitionistic First-Order Logic with Proofs
*)

IFOLP = Pure +

classes term < logic

default term

types
  p
  o

arities
  p,o :: logic

consts  
      (*** Judgements ***)
 "@Proof"       ::   "[p,o]=>prop"      ("(_ /: _)" [51,10] 5)
 Proof          ::   "[o,p]=>prop"
 EqProof        ::   "[p,p,o]=>prop"    ("(3_ /= _ :/ _)" [10,10,10] 5)
        
      (*** Logical Connectives -- Type Formers ***)
 "="            ::      "['a,'a] => o"  (infixl 50)
 True,False     ::      "o"
 Not            ::      "o => o"        ("~ _" [40] 40)
 "&"            ::      "[o,o] => o"    (infixr 35)
 "|"            ::      "[o,o] => o"    (infixr 30)
 "-->"          ::      "[o,o] => o"    (infixr 25)
 "<->"          ::      "[o,o] => o"    (infixr 25)
      (*Quantifiers*)
 All            ::      "('a => o) => o"        (binder "ALL " 10)
 Ex             ::      "('a => o) => o"        (binder "EX " 10)
 Ex1            ::      "('a => o) => o"        (binder "EX! " 10)
      (*Rewriting gadgets*)
 NORM           ::      "o => o"
 norm           ::      "'a => 'a"

      (*** Proof Term Formers: precedence must exceed 50 ***)
 tt             :: "p"
 contr          :: "p=>p"
 fst,snd        :: "p=>p"
 pair           :: "[p,p]=>p"           ("(1<_,/_>)")
 split          :: "[p, [p,p]=>p] =>p"
 inl,inr        :: "p=>p"
 when           :: "[p, p=>p, p=>p]=>p"
 lambda         :: "(p => p) => p"      (binder "lam " 55)
 "`"            :: "[p,p]=>p"           (infixl 60)
 alll           :: "['a=>p]=>p"         (binder "all " 55)
 "^"            :: "[p,'a]=>p"          (infixl 55)
 exists         :: "['a,p]=>p"          ("(1[_,/_])")
 xsplit         :: "[p,['a,p]=>p]=>p"
 ideq           :: "'a=>p"
 idpeel         :: "[p,'a=>p]=>p"
 nrm, NRM       :: "p"

rules

(**** Propositional logic ****)

(*Equality*)
(* Like Intensional Equality in MLTT - but proofs distinct from terms *)

ieqI      "ideq(a) : a=a"
ieqE      "[| p : a=b;  !!x. f(x) : P(x,x) |] ==> idpeel(p,f) : P(a,b)"

(* Truth and Falsity *)

TrueI     "tt : True"
FalseE    "a:False ==> contr(a):P"

(* Conjunction *)

conjI     "[| a:P;  b:Q |] ==> <a,b> : P&Q"
conjunct1 "p:P&Q ==> fst(p):P"
conjunct2 "p:P&Q ==> snd(p):Q"

(* Disjunction *)

disjI1    "a:P ==> inl(a):P|Q"
disjI2    "b:Q ==> inr(b):P|Q"
disjE     "[| a:P|Q;  !!x. x:P ==> f(x):R;  !!x. x:Q ==> g(x):R 
          |] ==> when(a,f,g):R"

(* Implication *)

impI      "(!!x. x:P ==> f(x):Q) ==> lam x. f(x):P-->Q"
mp        "[| f:P-->Q;  a:P |] ==> f`a:Q"

(*Quantifiers*)

allI      "(!!x. f(x) : P(x)) ==> all x. f(x) : ALL x. P(x)"
spec      "(f:ALL x. P(x)) ==> f^x : P(x)"

exI       "p : P(x) ==> [x,p] : EX x. P(x)"
exE       "[| p: EX x. P(x);  !!x u. u:P(x) ==> f(x,u) : R |] ==> xsplit(p,f):R"

(**** Equality between proofs ****)

prefl     "a : P ==> a = a : P"
psym      "a = b : P ==> b = a : P"
ptrans    "[| a = b : P;  b = c : P |] ==> a = c : P"

idpeelB   "[| !!x. f(x) : P(x,x) |] ==> idpeel(ideq(a),f) = f(a) : P(a,a)"

fstB      "a:P ==> fst(<a,b>) = a : P"
sndB      "b:Q ==> snd(<a,b>) = b : Q"
pairEC    "p:P&Q ==> p = <fst(p),snd(p)> : P&Q"

whenBinl  "[| a:P;  !!x. x:P ==> f(x) : Q |] ==> when(inl(a),f,g) = f(a) : Q"
whenBinr  "[| b:P;  !!x. x:P ==> g(x) : Q |] ==> when(inr(b),f,g) = g(b) : Q"
plusEC    "a:P|Q ==> when(a,%x. inl(x),%y. inr(y)) = p : P|Q"

applyB     "[| a:P;  !!x. x:P ==> b(x) : Q |] ==> (lam x. b(x)) ` a = b(a) : Q"
funEC      "f:P ==> f = lam x. f`x : P"

specB      "[| !!x. f(x) : P(x) |] ==> (all x. f(x)) ^ a = f(a) : P(a)"


(**** Definitions ****)

not_def              "~P == P-->False"
iff_def         "P<->Q == (P-->Q) & (Q-->P)"

(*Unique existence*)
ex1_def   "EX! x. P(x) == EX x. P(x) & (ALL y. P(y) --> y=x)"

(*Rewriting -- special constants to flag normalized terms and formulae*)
norm_eq "nrm : norm(x) = x"
NORM_iff        "NRM : NORM(P) <-> P"

end

ML

(*show_proofs:=true displays the proof terms -- they are ENORMOUS*)
val show_proofs = ref false;

fun proof_tr [p,P] = Const("Proof",dummyT) $ P $ p;

fun proof_tr' [P,p] = 
    if !show_proofs then Const("@Proof",dummyT) $ p $ P 
    else P  (*this case discards the proof term*);

val  parse_translation = [("@Proof", proof_tr)];
val print_translation  = [("Proof", proof_tr')];

