(*  Title: 	ZF/ex/contract.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson
    Copyright   1993  University of Cambridge

Inductive definition of (1-step) contractions and (mult-step) reductions
*)

Contract0 = Comb +
consts
  diamond   :: "i => o"
  I         :: "i"

  contract  :: "i"
  "-1->"    :: "[i,i] => o"    			(infixl 50)
  "--->"    :: "[i,i] => o"    			(infixl 50)

  parcontract :: "i"
  "=1=>"    :: "[i,i] => o"    			(infixl 50)
  "===>"    :: "[i,i] => o"    			(infixl 50)

translations
  "p -1-> q" == "<p,q> : contract"
  "p ---> q" == "<p,q> : contract^*"
  "p =1=> q" == "<p,q> : parcontract"
  "p ===> q" == "<p,q> : parcontract^+"

rules

  diamond_def "diamond(r) == ALL x y. <x,y>:r --> \
\                            (ALL y'. <x,y'>:r --> \
\                                 (EX z. <y,z>:r & <y',z> : r))"

  I_def       "I == S#K#K"

end
