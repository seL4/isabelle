(*  Title:      HOLCF/ex/Classlib.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1995 Technical University Munich

Introduce various type classes.

!!! Has to be adapted to axclasses !!!
--------------------------------------


The class hierarchy is as follows:

        pcpo 
         |        
          ----------------
         |               | 
         |      --------------------- 
         |      |       |      |    | 
        per   cplus  cminus ctimes cdvi
         |
       equiv
       /  \
      /    \
     |     |
    qpo    eq
     | 
     |    
  qlinear


*)

Classlib = HOLCF +

(* -------------------------------------------------------------------- *)
(* class cplus with characteristic constant  ++                         *)
 
axclass cplus < pcpo	

instance lift :: (term)cplus

ops curried 
	"++"	:: "'a::cplus -> 'a -> 'a"		(cinfixl 65)



(* -------------------------------------------------------------------- *)
(* class cminus with characteristic constant --                         *)
 
axclass cminus < pcpo

instance lift :: (term)cminus

ops curried 
	"--"	:: "'a::cminus -> 'a -> 'a"		(cinfixl 65)



(* -------------------------------------------------------------------- *)
(* class ctimes with characteristic constant **                         *)
 
axclass ctimes < pcpo

instance lift :: (term)ctimes

ops curried 
	"**"	:: "'a::ctimes -> 'a -> 'a"		(cinfixl 70)



(* -------------------------------------------------------------------- *)
(* class cdiv with characteristic constant //                           *)
 
axclass cdiv < pcpo

instance lift :: (term)cdiv

ops curried 
	"//"	:: "'a::cdiv -> 'a -> 'a"		(cinfixl 70)



(* -------------------------------------------------------------------- *)
(* class per with characteristic constant .=                            *)
 
classes per < pcpo	

arities lift :: (term)per

ops curried 
	".="	:: "'a::per -> 'a -> tr"	(cinfixl 55)
syntax (symbols)
	"op .=" :: "'a::per => 'a => tr"	(infixl "\\<doteq>" 55)

rules 

strict_per	"(UU .= x) = UU & (x .= UU) = UU"
total_per	"[|x ~= UU; y ~= UU|] ==> (x .= y) ~= UU"
flat_per	"flat (x::'a::per)"

sym_per		"(x .= y) = (y .= x)"
trans_per	"[| (x .= y)=TT; (y .= z)=TT |] ==> (x .= z)=TT"

(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
(* class equiv is a refinement of of class per                          *)
 
classes equiv < per 	

arities lift :: (term)equiv

rules 

refl_per	"[|(x::'a::equiv) ~= UU|] ==> (x .= x)=TT"

(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
(* class eq is a refinement of of class equiv                           *)
 
classes eq < equiv  	

arities lift :: (term)eq

rules 

weq	"[| (x::'a::eq) ~= UU; y ~= UU |] ==> 
	 (x = y --> (x .=y) = TT) & (x ~= y --> (x .= y)=FF)"

end
