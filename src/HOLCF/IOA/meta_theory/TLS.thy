(*  Title:      HOLCF/IOA/meta_theory/TLS.thy
    ID:         $Id$
    Author:     Olaf Müller
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Temporal Logic of Steps -- tailored for I/O automata.
*)   

		       
TLS = IOA + TL + 

default type

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

mkfin      :: "'a Seq => 'a Seq"

ex2seq     :: "('a,'s)execution => ('a option,'s)transition Seq"
ex2seqC    :: "('a,'s)pairs -> ('s => ('a option,'s)transition Seq)" 


defs

mkfin_def
  "mkfin s == if Partial s then @t. Finite t & s = t @@ UU
                           else s"

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

ex2seq_def
  "ex2seq ex == ((ex2seqC $(mkfin (snd ex))) (fst ex))"

ex2seqC_def
  "ex2seqC == (fix$(LAM h ex. (%s. case ex of 
      nil =>  (s,None,s)>>nil
    | x##xs => (flift1 (%pr.
                (s,Some (fst pr), snd pr)>> (h$xs) (snd pr)) 
                $x)
      )))"

validTE_def
  "validTE P == ! ex. (ex |== P)"

validIOA_def
  "validIOA A P == ! ex : executions A . (ex |== P)"



rules

mkfin_UU
  "mkfin UU = nil"

mkfin_nil
  "mkfin nil =nil"

mkfin_cons
  "(mkfin (a>>s)) = (a>>(mkfin s))"



end

