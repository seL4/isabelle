(*  Title       : Lim.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Theory of limits, continuity and 
                  differentiation of real=>real functions
*)

Lim = SEQ + RealAbs + 

(*-----------------------------------------------------------------------
    Limits, continuity and differentiation: standard and NS definitions
 -----------------------------------------------------------------------*)

constdefs
  LIM :: [real=>real,real,real] => bool
				("((_)/ -- (_)/ --> (_))" [60, 0, 60] 60)
  "f -- a --> L ==
     ALL r. Numeral0 < r --> 
	     (EX s. Numeral0 < s & (ALL x. (x ~= a & (abs(x + -a) < s)
			  --> abs(f x + -L) < r)))"

  NSLIM :: [real=>real,real,real] => bool
			      ("((_)/ -- (_)/ --NS> (_))" [60, 0, 60] 60)
  "f -- a --NS> L == (ALL x. (x ~= hypreal_of_real a & 
		      x @= hypreal_of_real a -->
		      (*f* f) x @= hypreal_of_real L))"   

  isCont :: [real=>real,real] => bool
  "isCont f a == (f -- a --> (f a))"        

  (* NS definition dispenses with limit notions *)
  isNSCont :: [real=>real,real] => bool
  "isNSCont f a == (ALL y. y @= hypreal_of_real a --> 
			   (*f* f) y @= hypreal_of_real (f a))"

  (* differentiation: D is derivative of function f at x *)
  deriv:: [real=>real,real,real] => bool
			    ("(DERIV (_)/ (_)/ :> (_))" [60, 0, 60] 60)
  "DERIV f x :> D == ((%h. (f(x + h) + -f(x))/h) -- Numeral0 --> D)"

  nsderiv :: [real=>real,real,real] => bool
			    ("(NSDERIV (_)/ (_)/ :> (_))" [60, 0, 60] 60)
  "NSDERIV f x :> D == (ALL h: Infinitesimal - {0}. 
			((*f* f)(hypreal_of_real x + h) + 
			 - hypreal_of_real (f x))/h @= hypreal_of_real D)"

  differentiable :: [real=>real,real] => bool   (infixl 60)
  "f differentiable x == (EX D. DERIV f x :> D)"

  NSdifferentiable :: [real=>real,real] => bool   (infixl 60)
  "f NSdifferentiable x == (EX D. NSDERIV f x :> D)"

  increment :: [real=>real,real,hypreal] => hypreal
  "increment f x h == (@inc. f NSdifferentiable x & 
		       inc = (*f* f)(hypreal_of_real x + h) + -hypreal_of_real (f x))"

  isUCont :: (real=>real) => bool
  "isUCont f ==  (ALL r. Numeral0 < r --> 
		      (EX s. Numeral0 < s & (ALL x y. abs(x + -y) < s
			    --> abs(f x + -f y) < r)))"

  isNSUCont :: (real=>real) => bool
  "isNSUCont f == (ALL x y. x @= y --> (*f* f) x @= (*f* f) y)"


(*Used in the proof of the Bolzano theorem*)
consts
  Bolzano_bisect :: "[real*real=>bool, real, real, nat] => (real*real)"

primrec
  "Bolzano_bisect P a b 0 = (a,b)"
  "Bolzano_bisect P a b (Suc n) =
      (let (x,y) = Bolzano_bisect P a b n
       in if P(x, (x+y)/2) then ((x+y)/2, y)
                            else (x, (x+y)/2) )"
  

end

