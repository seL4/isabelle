(*  Title:      FOCUS/Classlib.thy
    ID:         $ $
    Author:     Franz Regensburger
    Copyright   1995 Technical University Munich

Introduce various type classes

The 8bit package is needed for this theory

The type void of HOLCF/Void.thy is a witness for all the introduced classes.
Inspect theory Witness.thy for all the proofs. 

the trivial instance for ++ -- ** // is LAM x y.(UU::void) 
the trivial instance for .= and .<=  is LAM x y.(UU::tr)

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

arities void :: cplus

ops curried 
	"++"	:: "'a::cplus -> 'a -> 'a"		(cinfixl 65)


(* class cplus has no characteristic axioms                             *)
(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
(* class cminus with characteristic constant --                         *)
 
classes cminus < pcpo	

arities void :: cminus

ops curried 
	"--"	:: "'a::cminus -> 'a -> 'a"		(cinfixl 65)

(* class cminus has no characteristic axioms                            *)
(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
(* class ctimes with characteristic constant **                         *)
 
classes ctimes < pcpo	

arities void :: ctimes

ops curried 
	"**"	:: "'a::ctimes -> 'a -> 'a"		(cinfixl 70)

(* class ctimes has no characteristic axioms                            *)
(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
(* class cdiv with characteristic constant //                           *)
 
classes cdiv < pcpo	

arities void :: cdiv

ops curried 
	"//"	:: "'a::cdiv -> 'a -> 'a"		(cinfixl 70)

(* class cdiv has no characteristic axioms                              *)
(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
(* class per with characteristic constant .=                            *)
 
classes per < pcpo	

arities void :: per

ops curried 
	".="	:: "'a::per -> 'a -> tr"	(cinfixl 55)
syntax (symbols)
	"op .=" :: "'a::per => 'a => tr"	(infixl "\\<doteq>" 55)

rules 

strict_per	"(UU .= x) = UU & (x .= UU) = UU"
total_per	"[|x ~= UU; y ~= UU|] ==> (x .= y) ~= UU"
flat_per	"flat (UU::'a::per)"

sym_per		"(x .= y) = (y .= x)"
trans_per	"[| (x .= y)=TT; (y .= z)=TT |] ==> (x .= z)=TT"

(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
(* class equiv is a refinement of of class per                          *)
 
classes equiv < per 	

arities void :: equiv

rules 

refl_per	"[|(x::'a::equiv) ~= UU|] ==> (x .= x)=TT"

(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
(* class eq is a refinement of of class equiv                           *)
 
classes eq < equiv  	

arities void :: eq

rules 

weq	"[| (x::'a::eq) ~= UU; y ~= UU |] ==> 
	 (x = y --> (x .=y) = TT) & (x ~= y --> (x .= y)=FF)"

(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
(* class qpo with characteristic constant .<=                           *)
(*  .<= is a partial order wrt an equivalence                           *)
 
classes qpo < equiv	

arities void :: qpo

ops curried 
	".<="	:: "'a::qpo -> 'a -> tr"	(cinfixl 55)
syntax (symbols)
	"op .<=":: "'a::qpo => 'a => tr"	(infixl "\\<preceq>" 55)
rules 

strict_qpo	"(UU .<= x) = UU & (x .<= UU) = UU"
total_qpo	"[|x ~= UU; y ~= UU|] ==> (x .<= y) ~= UU"

refl_qpo	"[|x ~= UU|] ==> (x .<= x)=TT"
antisym_qpo	"[| (x .<= y)=TT; (y .<= x)=TT |] ==> (x .=  y)=TT"
trans_qpo	"[| (x .<= y)=TT; (y .<= z)=TT |] ==> (x .<= z)=TT"

antisym_qpo_rev	"(x .= y)=TT ==> (x .<= y)=TT & (y .<= x)=TT" 

(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
(* irreflexive part .< defined via .<=                                  *)
 
ops curried 
	".<"	:: "'a::qpo -> 'a -> tr"	(cinfixl 55)
syntax (symbols)
	"op .<"	:: "'a::qpo => 'a => tr"	(infixl "\\<prec>" 55)

defs

qless_def	"(op .<) Ú LAM x y.If x .= y then FF else x .<= y fi"

(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
(* class qlinear is a refinement of of class qpo                        *)
 
classes qlinear < qpo  	

arities void :: qlinear

rules 

qlinear	"[|(x::'a::qlinear) ~= UU; y ~= UU|] ==> (x .<= y)=TT Á (y .<= x)=TT "

(* -------------------------------------------------------------------- *)

end
