Unify1 = Unifier + WF1 + "NNF" + 

datatype 'a subst = Fail | Subst ('a list)

consts

 "##"  :: "('a => 'b) => ('a => 'c) => 'a => ('b * 'c)"  (infixr 50)
   R0  :: "('a set * 'a set) set"
   R1  :: "(('a uterm * 'a uterm) * ('a uterm * 'a uterm)) set"
   R   :: "(('a uterm * 'a uterm) * ('a uterm * 'a uterm)) set"


rules

  point_to_prod_def "(f ## g) x == (f x, g x)"

  (* finite proper subset -- should go in WF1.thy maybe *)
  R0_def "R0 == {p. fst p < snd p & finite(snd p)}"

  R1_def "R1 == rprod (measure uterm_size) (measure uterm_size)"

  (* The termination relation for the Unify function *)
  R_def  "R == inv_image  (R0 ** R1)
                          ((%(x,y). vars_of x Un vars_of y) ## (%x.x))"

end
