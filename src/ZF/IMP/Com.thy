(*  Title: 	ZF/IMP/Com.thy
    ID:         $Id$
    Author: 	Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM

Arithmetic expressions, Boolean expressions, Commands

And their Operational semantics
*)

Com = Datatype +

(** Arithmetic expressions **)
consts  loc  :: i
        aexp :: i

datatype <= "univ(loc Un (nat->nat) Un ((nat*nat) -> nat) )"
  "aexp" = N ("n: nat")
         | X ("x: loc")
         | Op1 ("f: nat -> nat", "a : aexp")
         | Op2 ("f: (nat*nat) -> nat", "a0 : aexp", "a1 : aexp")


(** Evaluation of arithmetic expressions **)
consts  evala    :: i
       "@evala"  :: [i,i,i] => o		("<_,_>/ -a-> _"  [0,0,50] 50)
translations
    "<ae,sig> -a-> n" == "<ae,sig,n> : evala"
inductive
  domains "evala" <= "aexp * (loc -> nat) * nat"
  intrs 
    N   "[| n:nat ; sigma:loc->nat |] ==> <N(n),sigma> -a-> n"
    X  	"[| x:loc;  sigma:loc->nat |] ==> <X(x),sigma> -a-> sigma`x"
    Op1 "[| <e,sigma> -a-> n;  f: nat -> nat |] ==> <Op1(f,e),sigma> -a-> f`n"
    Op2 "[| <e0,sigma> -a-> n0;  <e1,sigma>  -a-> n1; f: (nat*nat) -> nat |] 
           ==> <Op2(f,e0,e1),sigma> -a-> f`<n0,n1>"

  type_intrs "aexp.intrs@[apply_funtype]"


(** Boolean expressions **)
consts  bexp :: i

datatype <= "univ(aexp Un ((nat*nat)->bool) )"
  "bexp" = true
         | false
         | ROp  ("f: (nat*nat)->bool", "a0 : aexp", "a1 : aexp")
         | noti ("b : bexp")
         | andi ("b0 : bexp", "b1 : bexp")	(infixl 60)
         | ori  ("b0 : bexp", "b1 : bexp")	(infixl 60)


(** Evaluation of boolean expressions **)
consts evalb	:: i	
       "@evalb" :: [i,i,i] => o		("<_,_>/ -b-> _" [0,0,50] 50)

translations
    "<be,sig> -b-> b" == "<be,sig,b> : evalb"

inductive
  domains "evalb" <= "bexp * (loc -> nat) * bool"
  intrs (*avoid clash with ML constructors true, false*)
    tru   "[| sigma:loc -> nat |] ==> <true,sigma> -b-> 1"
    fls   "[| sigma:loc -> nat |] ==> <false,sigma> -b-> 0"
    ROp   "[| <a0,sigma> -a-> n0; <a1,sigma> -a-> n1; f: (nat*nat)->bool |] 
	   ==> <ROp(f,a0,a1),sigma> -b-> f`<n0,n1> "
    noti  "[| <b,sigma> -b-> w |] ==> <noti(b),sigma> -b-> not(w)"
    andi  "[| <b0,sigma> -b-> w0; <b1,sigma> -b-> w1 |] 
          ==> <b0 andi b1,sigma> -b-> (w0 and w1)"
    ori   "[| <b0,sigma> -b-> w0; <b1,sigma> -b-> w1 |] 
	    ==> <b0 ori b1,sigma> -b-> (w0 or w1)"

  type_intrs "bexp.intrs @   
	      [apply_funtype, and_type, or_type, bool_1I, bool_0I, not_type]"
  type_elims "[make_elim(evala.dom_subset RS subsetD)]"


(** Commands **)
consts  com :: i

datatype <= "univ(loc Un aexp Un bexp)"
  "com" = skip
        | ":="  ("x:loc", "a:aexp")		(infixl 60)
        | semic ("c0:com", "c1:com")		("_; _"  [60, 60] 10)
	| while ("b:bexp", "c:com")		("while _ do _"  60)
	| ifc   ("b:bexp", "c0:com", "c1:com")	("ifc _ then _ else _"  60)

(*Constructor ";" has low precedence to avoid syntactic ambiguities
  with [| m: nat; x: loc; ... |] ==> ...  It usually will need parentheses.*)

(** Execution of commands **)
consts  evalc    :: i
        "@evalc" :: [i,i,i] => o   		("<_,_>/ -c-> _" [0,0,50] 50)
	"assign" :: [i,i,i] => i   		("_[_'/_]"       [95,0,0] 95)

translations
       "<ce,sig> -c-> s" == "<ce,sig,s> : evalc"

defs 
	assign_def	"sigma[m/x] == lam y:loc. if(y=x,m,sigma`y)"

inductive
  domains "evalc" <= "com * (loc -> nat) * (loc -> nat)"
  intrs
    skip    "[| sigma: loc -> nat |] ==> <skip,sigma> -c-> sigma"

    assign  "[| m: nat; x: loc; <a,sigma> -a-> m |] ==> 
            <x := a,sigma> -c-> sigma[m/x]"

    semi    "[| <c0,sigma> -c-> sigma2; <c1,sigma2> -c-> sigma1 |] ==> 
            <c0 ; c1, sigma> -c-> sigma1"

    ifc1     "[| b:bexp; c1:com; sigma:loc->nat;   
		 <b,sigma> -b-> 1; <c0,sigma> -c-> sigma1 |] ==> 
             <ifc b then c0 else c1, sigma> -c-> sigma1"

    ifc0     "[| b:bexp; c0:com; sigma:loc->nat;   
		 <b,sigma> -b-> 0; <c1,sigma> -c-> sigma1 |] ==> 
             <ifc b then c0 else c1, sigma> -c-> sigma1"

    while0   "[| c: com; <b, sigma> -b-> 0 |] ==> 
             <while b do c,sigma> -c-> sigma "

    while1   "[| c : com; <b,sigma> -b-> 1; <c,sigma> -c-> sigma2; 
                <while b do c, sigma2> -c-> sigma1 |] ==> 
             <while b do c, sigma> -c-> sigma1 "

  con_defs   "[assign_def]"
  type_intrs "bexp.intrs @ com.intrs @ [if_type,lam_type,apply_type]"
  type_elims "[make_elim(evala.dom_subset RS subsetD),   
	      make_elim(evalb.dom_subset RS subsetD) ]"

end
