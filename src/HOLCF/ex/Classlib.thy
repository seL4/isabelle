(*  Title:      FOCUS/Classlib.thy
    ID:         $ $
    Author:     Franz Regensburger
    Copyright   1995 Technical University Munich

Introduce various type classes

!!! Has to be adapted to axclasses !!!
--------------------------------------

the trivial instance for ++ -- ** // is circ
the trivial instance for .= and .<=  is bullet

the class hierarchy is as follows

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
 
classes cplus < pcpo	

arities lift :: (term)cplus

ops curried 
	"++"	:: "'a::cplus -> 'a -> 'a"		(cinfixl 65)


(* class cplus has no characteristic axioms                             *)
(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
(* class cminus with characteristic constant --                         *)
 
classes cminus < pcpo	

arities lift :: (term)cminus

ops curried 
	"--"	:: "'a::cminus -> 'a -> 'a"		(cinfixl 65)

(* class cminus has no characteristic axioms                            *)
(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
(* class ctimes with characteristic constant **                         *)
 
classes ctimes < pcpo	

arities lift :: (term)ctimes

ops curried 
	"**"	:: "'a::ctimes -> 'a -> 'a"		(cinfixl 70)

(* class ctimes has no characteristic axioms                            *)
(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
(* class cdiv with characteristic constant //                           *)
 
classes cdiv < pcpo	

arities lift :: (term)cdiv

ops curried 
	"//"	:: "'a::cdiv -> 'a -> 'a"		(cinfixl 70)

(* class cdiv has no characteristic axioms                              *)
(* -------------------------------------------------------------------- *)

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
