(*  Title:      CCL/ex/nat.thy
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Programs defined over the natural numbers
*)

Nat = Wfd +

consts

  not              :: "i=>i"
  "#+","#*","#-",
  "##","#<","#<="  :: "[i,i]=>i"            (infixr 60)
  ackermann        :: "[i,i]=>i"

rules 

  not_def     "not(b) == if b then false else true"

  add_def     "a #+ b == nrec(a,b,%x g. succ(g))"
  mult_def    "a #* b == nrec(a,zero,%x g. b #+ g)"
  sub_def     "a #- b == letrec sub x y be ncase(y,x,%yy. ncase(x,zero,%xx. sub(xx,yy))) 
                        in sub(a,b)"
  le_def     "a #<= b == letrec le x y be ncase(x,true,%xx. ncase(y,false,%yy. le(xx,yy))) 
                        in le(a,b)"
  lt_def     "a #< b == not(b #<= a)"

  div_def    "a ## b == letrec div x y be if x #< y then zero else succ(div(x#-y,y)) 
                       in div(a,b)"
  ack_def    
  "ackermann(a,b) == letrec ack n m be ncase(n,succ(m),%x. 
                          ncase(m,ack(x,succ(zero)),%y. ack(x,ack(succ(x),y))))
                    in ack(a,b)"

end

