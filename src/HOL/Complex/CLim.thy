(*  Title       : CLim.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 2001 University of Edinburgh
    Description : A first theory of limits, continuity and 
                  differentiation for complex functions
*)

CLim = CSeries + 

constdefs

  CLIM :: [complex=>complex,complex,complex] => bool
				("((_)/ -- (_)/ --C> (_))" [60, 0, 60] 60)
  "f -- a --C> L ==
     ALL r. 0 < r --> 
	     (EX s. 0 < s & (ALL x. (x ~= a & (cmod(x - a) < s)
			  --> cmod(f x - L) < r)))"

  NSCLIM :: [complex=>complex,complex,complex] => bool
			      ("((_)/ -- (_)/ --NSC> (_))" [60, 0, 60] 60)
  "f -- a --NSC> L == (ALL x. (x ~= hcomplex_of_complex a & 
           		         x @c= hcomplex_of_complex a 
                                   --> ( *fc* f) x @c= hcomplex_of_complex L))"   

  (* f: C --> R *)
  CRLIM :: [complex=>real,complex,real] => bool
				("((_)/ -- (_)/ --CR> (_))" [60, 0, 60] 60)
  "f -- a --CR> L ==
     ALL r. 0 < r --> 
	     (EX s. 0 < s & (ALL x. (x ~= a & (cmod(x - a) < s)
			  --> abs(f x - L) < r)))"

  NSCRLIM :: [complex=>real,complex,real] => bool
			      ("((_)/ -- (_)/ --NSCR> (_))" [60, 0, 60] 60)
  "f -- a --NSCR> L == (ALL x. (x ~= hcomplex_of_complex a & 
           		         x @c= hcomplex_of_complex a 
                                   --> ( *fcR* f) x @= hypreal_of_real L))"   


  isContc :: [complex=>complex,complex] => bool
  "isContc f a == (f -- a --C> (f a))"        

  (* NS definition dispenses with limit notions *)
  isNSContc :: [complex=>complex,complex] => bool
  "isNSContc f a == (ALL y. y @c= hcomplex_of_complex a --> 
			   ( *fc* f) y @c= hcomplex_of_complex (f a))"

  isContCR :: [complex=>real,complex] => bool
  "isContCR f a == (f -- a --CR> (f a))"        

  (* NS definition dispenses with limit notions *)
  isNSContCR :: [complex=>real,complex] => bool
  "isNSContCR f a == (ALL y. y @c= hcomplex_of_complex a --> 
			   ( *fcR* f) y @= hypreal_of_real (f a))"

  (* differentiation: D is derivative of function f at x *)
  cderiv:: [complex=>complex,complex,complex] => bool
			    ("(CDERIV (_)/ (_)/ :> (_))" [60, 0, 60] 60)
  "CDERIV f x :> D == ((%h. (f(x + h) - f(x))/h) -- 0 --C> D)"

  nscderiv :: [complex=>complex,complex,complex] => bool
			    ("(NSCDERIV (_)/ (_)/ :> (_))" [60, 0, 60] 60)
  "NSCDERIV f x :> D == (ALL h: CInfinitesimal - {0}. 
			      (( *fc* f)(hcomplex_of_complex x + h)
        			 - hcomplex_of_complex (f x))/h @c= hcomplex_of_complex D)"

  cdifferentiable :: [complex=>complex,complex] => bool   (infixl 60)
  "f cdifferentiable x == (EX D. CDERIV f x :> D)"

  NSCdifferentiable :: [complex=>complex,complex] => bool   (infixl 60)
  "f NSCdifferentiable x == (EX D. NSCDERIV f x :> D)"


  isUContc :: (complex=>complex) => bool
  "isUContc f ==  (ALL r. 0 < r --> 
		      (EX s. 0 < s & (ALL x y. cmod(x - y) < s
			    --> cmod(f x - f y) < r)))"

  isNSUContc :: (complex=>complex) => bool
  "isNSUContc f == (ALL x y. x @c= y --> ( *fc* f) x @c= ( *fc* f) y)"

end 
