(*  Title:      HOLCF/IOA/meta_theory/TLS.thy
    ID:         $Id$
    Author:     Olaf M"uller
    Copyright   1997  TU Muenchen

Temporal Logic of Steps -- tailored for I/O automata
*)   

		       
TLS = IOA + TL + 

default term

types

 ('a,'s)ioa_temp       = "('a option,'s)transition temporal" 
 ('a,'s)step_pred      = "('a option,'s)transition predicate"
  's state_pred        = "'s predicate"
 
consts


option_lift :: "('a => 'b) => 'b => ('a option => 'b)"
plift       :: "('a => bool) => ('a option => bool)"
 
temp_sat   :: "('a,'s)execution => ('a,'s)ioa_temp => bool"    (infixr "|==" 22)
xt1        :: "'s predicate => ('a,'s)step_pred"
xt2        :: "'a option predicate => ('a,'s)step_pred"

validTE    :: "('a,'s)ioa_temp => bool"
validIOA   :: "('a,'s)ioa => ('a,'s)ioa_temp => bool"


ex2seq     :: "('a,'s)execution => ('a option,'s)transition Seq"
ex2seqC    :: "('a,'s)pairs -> ('s => ('a option,'s)transition Seq)" 


defs

(* should be in Option as option_lift1, and option_map should be renamed to 
   option_lift2 *)
option_lift_def
  "option_lift f s y == case y of None => s | Some x => (f x)"

(* plift is used to determine that None action is always false in 
   transition predicates *)
plift_def
  "plift P == option_lift P False"

temp_sat_def
  "ex |== P == ((ex2seq ex) |= P)"

xt1_def
  "xt1 P tr == P (fst tr)"

xt2_def
  "xt2 P tr == P (fst (snd tr))"


(* FIX: Clarify type and Herkunft of a !! *)
ex2seq_def
  "ex2seq ex == ((ex2seqC `(snd ex)) (fst ex))"

ex2seqC_def
  "ex2seqC == (fix`(LAM h ex. (%s. case ex of 
      nil =>  (s,None,s)>>nil
    | x##xs => (flift1 (%pr.
                (s,Some (fst pr), snd pr)>> (h`xs) (snd pr)) 
                `x)
      )))"

validTE_def
  "validTE P == ! ex. (ex |== P)"

validIOA_def
  "validIOA A P == ! ex : executions A . (ex |== P)"

rules

ex2seq_UUAlt
  "ex2seq (s,UU) = (s,None,s)>>UU"


end

