(*
    ID:         $Id$
    Author:     Amine Chaieb, TU Muenchen

Examples for Ferrante and Rackoff Algorithm.
*)

theory Ferrante_Rackoff_Ex
imports Complex_Main
begin

lemma "~ (ALL (x::real) y. x < y --> 10*x < 11*y)"
apply ferrack
done

lemma "ALL (x::real) y. x < y --> (10*(x + 5*y + -1) < 60*y)"
apply ferrack
done

lemma "EX (x::real) y. x ~= y --> x < y"
  apply ferrack
  done

lemma "EX (x::real) y. (x ~= y & 10*x ~= 9*y & 10*x < y) --> x < y"
  apply ferrack
  done
lemma "ALL (x::real) y. (x ~= y & 5*x <= y) --> 500*x <= 100*y"
  apply ferrack
  done

  (* 1 Alternations *)
lemma "ALL (x::real). (EX (y::real). 4*x + 3*y <= 0 & 4*x + 3*y >= -1)"
  by ferrack
lemma "ALL (x::real) < 0. (EX (y::real) > 0. 7*x + y > 0 & x - y <= 9)"
  by ferrack
lemma "EX (x::real). (0 < x & x < 1) --> (ALL y > 1. x + y ~= 1)"
  apply ferrack
  done
lemma "EX (x::real). (ALL y. y < 2 -->  2*(y - x) \<le> 0 )"
  apply ferrack
  done
lemma "ALL (x::real). x < 10 | x > 20 | (EX y. y>= 0 & y <= 10 & x+y = 20)"
  apply ferrack
  done
    (* Formulae with 3 quantifiers *)
  (* 0 Alternations *)
lemma "ALL (x::real) y z. x + y < z --> y >= z --> x < 0"
apply ferrack
done
lemma "EX (x::real) y z. x + 7*y < 5* z & 5*y >= 7*z & x < 0"
apply ferrack
done
lemma "ALL (x::real) y z. abs (x + y) <= z --> (abs z = z)"
apply ferrack
done

lemma "EX (x::real) y z. x + 7*y - 5* z < 0 & 5*y + 7*z + 3*x < 0"
apply ferrack
done

lemma "ALL (x::real) y z. (abs (5*x+3*y+z) <= 5*x+3*y+z & abs (5*x+3*y+z) >= - (5*x+3*y+z)) | (abs (5*x+3*y+z) >= 5*x+3*y+z & abs (5*x+3*y+z) <= - (5*x+3*y+z))"
apply ferrack
done
  (* 1 Alternations *)
lemma "ALL (x::real) y. x < y --> (EX z>0. x+z = y)"
  by ferrack
lemma "ALL (x::real) y. (EX z>0. abs (x - y) <= z )"
  by ferrack

lemma "EX (x::real) y. (ALL z<0. (z < x --> z <= y) & (z > y --> z >= x))"
  apply ferrack
  done

lemma "EX (x::real) y. (ALL z>=0. abs (3*x+7*y) <= 2*z + 1)"
  apply ferrack
  done
lemma "EX (x::real) y. (ALL z<0. (z < x --> z <= y) & (z > y --> z >= x))"
  apply ferrack
  done
  (* 2 Alternations *)
lemma "EX (x::real)>0. (ALL y. (EX z. 13* abs z \<noteq> abs (12*y - x) & 5*x - 3*(abs y) <= 7*z))"
  apply ferrack
  done
lemma "EX (x::real). abs (4*x + 17) < 4 & (ALL y . abs (x*34 - 34*y - 9) \<noteq> 0 \<longrightarrow> (EX z. 5*x - 3*abs y <= 7*z))"
  apply ferrack
  done

lemma "ALL (x::real). (EX y > abs (23*x - 9). (ALL z > abs (3*y - 19* abs x). x+z > 2*y))" 
  apply ferrack
  done

lemma "ALL (x::real). (EX y< abs (3*x - 1). (ALL z >= (3*abs x - 1). abs (12*x - 13*y + 19*z) > abs (23*x) ))" 
  apply ferrack
  done

lemma "EX (x::real). abs x < 100 & (ALL y > x. (EX z<2*y - x. 5*x - 3*y <= 7*z))"
  apply ferrack
  done

    (* Formulae with 4 quantifiers *)
    (* 0 Alternations *)
lemma "ALL (x::real) y z w. 7*x<3*y --> 5*y < 7*z --> z < 2*w --> 7*(2*w-x) > 2*y"
  apply ferrack
  done
lemma "ALL (x::real) y. ALL z >x. ALL w > y. abs (z-x) + abs (y-w + x) <= z - x + w-y+abs x"
  apply ferrack
  done
lemma "EX (x::real) y z w. 5*x + 3*z - 17*w + abs (y - 8*x + z) <= 89"
  apply ferrack
  done

lemma "EX (x::real) y z w. 5*x + 3*z - 17*w + 7* (y - 8*x + z) <= max y (7*z - x + w)"
  apply ferrack
  done

lemma "EX (x::real) y z w. min (5*x + 3*z) (17*w) + 5* abs (y - 8*x + z) <= max y (7*z - x + w)"
  apply ferrack
  done
    (* 1 Alternations *)
lemma "ALL (x::real) y z. (EX w >= (x+y+z). w <= abs x + abs y + abs z)"
  apply ferrack
  done
lemma "~(ALL (x::real). (EX y z w. 3* x + z*4 = 3*y & x + y < z & x> w & 3*x < w + y))"
  apply ferrack
  done
lemma "ALL (x::real) y. (EX z w. abs (x-y) = (z-w) & z*1234 < 233*x & w ~= y)"
  apply ferrack
  done
lemma "ALL (x::real). (EX y z w. min (5*x + 3*z) (17*w) + 5* abs (y - 8*x + z) <= max y (7*z - x + w))"
  apply ferrack
  done
lemma "EX (x::real) y z. (ALL w >= abs (x+y+z). w >= abs x + abs y + abs z)"
  apply ferrack
  done
    (* 2 Alternations *)
lemma "EX z. (ALL (x::real) y. (EX w >= (x+y+z). w <= abs x + abs y + abs z))"
  apply ferrack
  done
lemma "EX z. (ALL (x::real) < abs z. (EX y w. x< y & x < z & x> w & 3*x < w + y))"
  apply ferrack
  done
lemma "ALL (x::real) y. (EX z. (ALL w. abs (x-y) = abs (z-w) --> z < x & w ~= y))"
  apply ferrack
  done
lemma "EX y. (ALL (x::real). (EX z w. min (5*x + 3*z) (17*w) + 5* abs (y - 8*x + z) <= max y (7*z - x + w)))"
  apply ferrack
  done
lemma "EX (x::real) z. (ALL w >= 13*x - 4*z. (EX y. w >= abs x + abs y + z))"
  apply ferrack
  done
    (* 3 Alternations *)
lemma "EX (x::real). (ALL y < x. (EX z > (x+y). 
  (ALL w. 5*w + 10*x - z >= y --> w + 7*x + 3*z >= 2*y)))"
  apply ferrack
  done
lemma "EX (x::real). (ALL y. (EX z > y. 
  (ALL w . w < 13 --> w + 10*x - z >= y --> 5*w + 7*x + 13*z >= 2*y)))"
  apply ferrack
  done
lemma "ALL (x::real). (EX y. (ALL z>19. y <= x + z & (EX w. abs (y - x) < w)))"
  apply ferrack
  done
lemma "ALL (x::real). (EX y. (ALL z>19. y <= x + z & (EX w. abs (x + z) < w - y)))"
  apply ferrack
  done
lemma "ALL (x::real). (EX y. abs y ~= abs x & (ALL z> max x y. (EX w. w ~= y & w ~= z & 3*w - z >= x + y)))"
  apply ferrack
  done
end
