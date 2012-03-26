(* Author:     Amine Chaieb, TU Muenchen *)

header {* Examples for Ferrante and Rackoff's quantifier elimination procedure *}

theory Dense_Linear_Order_Ex
imports "~~/src/HOL/Decision_Procs/Dense_Linear_Order"
begin

lemma
  "\<exists>(y::'a::{linordered_field_inverse_zero}) <2. x + 3* y < 0 \<and> x - y >0"
  by ferrack

lemma "~ (ALL x (y::'a::{linordered_field_inverse_zero}). x < y --> 10*x < 11*y)"
  by ferrack

lemma "ALL (x::'a::{linordered_field_inverse_zero}) y. x < y --> (10*(x + 5*y + -1) < 60*y)"
  by ferrack

lemma "EX (x::'a::{linordered_field_inverse_zero}) y. x ~= y --> x < y"
  by ferrack

lemma "EX (x::'a::{linordered_field_inverse_zero}) y. (x ~= y & 10*x ~= 9*y & 10*x < y) --> x < y"
  by ferrack

lemma "ALL (x::'a::{linordered_field_inverse_zero}) y. (x ~= y & 5*x <= y) --> 500*x <= 100*y"
  by ferrack

lemma "ALL (x::'a::{linordered_field_inverse_zero}). (EX (y::'a::{linordered_field_inverse_zero}). 4*x + 3*y <= 0 & 4*x + 3*y >= -1)"
  by ferrack

lemma "ALL (x::'a::{linordered_field_inverse_zero}) < 0. (EX (y::'a::{linordered_field_inverse_zero}) > 0. 7*x + y > 0 & x - y <= 9)"
  by ferrack

lemma "EX (x::'a::{linordered_field_inverse_zero}). (0 < x & x < 1) --> (ALL y > 1. x + y ~= 1)"
  by ferrack

lemma "EX x. (ALL (y::'a::{linordered_field_inverse_zero}). y < 2 -->  2*(y - x) \<le> 0 )"
  by ferrack

lemma "ALL (x::'a::{linordered_field_inverse_zero}). x < 10 | x > 20 | (EX y. y>= 0 & y <= 10 & x+y = 20)"
  by ferrack

lemma "ALL (x::'a::{linordered_field_inverse_zero}) y z. x + y < z --> y >= z --> x < 0"
  by ferrack

lemma "EX (x::'a::{linordered_field_inverse_zero}) y z. x + 7*y < 5* z & 5*y >= 7*z & x < 0"
  by ferrack

lemma "ALL (x::'a::{linordered_field_inverse_zero}) y z. abs (x + y) <= z --> (abs z = z)"
  by ferrack

lemma "EX (x::'a::{linordered_field_inverse_zero}) y z. x + 7*y - 5* z < 0 & 5*y + 7*z + 3*x < 0"
  by ferrack

lemma "ALL (x::'a::{linordered_field_inverse_zero}) y z. (abs (5*x+3*y+z) <= 5*x+3*y+z & abs (5*x+3*y+z) >= - (5*x+3*y+z)) | (abs (5*x+3*y+z) >= 5*x+3*y+z & abs (5*x+3*y+z) <= - (5*x+3*y+z))"
  by ferrack

lemma "ALL (x::'a::{linordered_field_inverse_zero}) y. x < y --> (EX z>0. x+z = y)"
  by ferrack

lemma "ALL (x::'a::{linordered_field_inverse_zero}) y. x < y --> (EX z>0. x+z = y)"
  by ferrack

lemma "ALL (x::'a::{linordered_field_inverse_zero}) y. (EX z>0. abs (x - y) <= z )"
  by ferrack

lemma "EX (x::'a::{linordered_field_inverse_zero}) y. (ALL z<0. (z < x --> z <= y) & (z > y --> z >= x))"
  by ferrack

lemma "EX (x::'a::{linordered_field_inverse_zero}) y. (ALL z>=0. abs (3*x+7*y) <= 2*z + 1)"
  by ferrack

lemma "EX (x::'a::{linordered_field_inverse_zero}) y. (ALL z<0. (z < x --> z <= y) & (z > y --> z >= x))"
  by ferrack

lemma "EX (x::'a::{linordered_field_inverse_zero})>0. (ALL y. (EX z. 13* abs z \<noteq> abs (12*y - x) & 5*x - 3*(abs y) <= 7*z))"
  by ferrack

lemma "EX (x::'a::{linordered_field_inverse_zero}). abs (4*x + 17) < 4 & (ALL y . abs (x*34 - 34*y - 9) \<noteq> 0 \<longrightarrow> (EX z. 5*x - 3*abs y <= 7*z))"
  by ferrack

lemma "ALL (x::'a::{linordered_field_inverse_zero}). (EX y > abs (23*x - 9). (ALL z > abs (3*y - 19* abs x). x+z > 2*y))"
  by ferrack

lemma "ALL (x::'a::{linordered_field_inverse_zero}). (EX y< abs (3*x - 1). (ALL z >= (3*abs x - 1). abs (12*x - 13*y + 19*z) > abs (23*x) ))"
  by ferrack

lemma "EX (x::'a::{linordered_field_inverse_zero}). abs x < 100 & (ALL y > x. (EX z<2*y - x. 5*x - 3*y <= 7*z))"
  by ferrack

lemma "ALL (x::'a::{linordered_field_inverse_zero}) y z w. 7*x<3*y --> 5*y < 7*z --> z < 2*w --> 7*(2*w-x) > 2*y"
  by ferrack

lemma "EX (x::'a::{linordered_field_inverse_zero}) y z w. 5*x + 3*z - 17*w + abs (y - 8*x + z) <= 89"
  by ferrack

lemma "EX (x::'a::{linordered_field_inverse_zero}) y z w. 5*x + 3*z - 17*w + 7* (y - 8*x + z) <= max y (7*z - x + w)"
  by ferrack

lemma "EX (x::'a::{linordered_field_inverse_zero}) y z w. min (5*x + 3*z) (17*w) + 5* abs (y - 8*x + z) <= max y (7*z - x + w)"
  by ferrack

lemma "ALL (x::'a::{linordered_field_inverse_zero}) y z. (EX w >= (x+y+z). w <= abs x + abs y + abs z)"
  by ferrack

lemma "~(ALL (x::'a::{linordered_field_inverse_zero}). (EX y z w. 3* x + z*4 = 3*y & x + y < z & x> w & 3*x < w + y))"
  by ferrack

lemma "ALL (x::'a::{linordered_field_inverse_zero}) y. (EX z w. abs (x-y) = (z-w) & z*1234 < 233*x & w ~= y)"
  by ferrack

lemma "ALL (x::'a::{linordered_field_inverse_zero}). (EX y z w. min (5*x + 3*z) (17*w) + 5* abs (y - 8*x + z) <= max y (7*z - x + w))"
  by ferrack

lemma "EX (x::'a::{linordered_field_inverse_zero}) y z. (ALL w >= abs (x+y+z). w >= abs x + abs y + abs z)"
  by ferrack

lemma "EX z. (ALL (x::'a::{linordered_field_inverse_zero}) y. (EX w >= (x+y+z). w <= abs x + abs y + abs z))"
  by ferrack

lemma "EX z. (ALL (x::'a::{linordered_field_inverse_zero}) < abs z. (EX y w. x< y & x < z & x> w & 3*x < w + y))"
  by ferrack

lemma "ALL (x::'a::{linordered_field_inverse_zero}) y. (EX z. (ALL w. abs (x-y) = abs (z-w) --> z < x & w ~= y))"
  by ferrack

lemma "EX y. (ALL (x::'a::{linordered_field_inverse_zero}). (EX z w. min (5*x + 3*z) (17*w) + 5* abs (y - 8*x + z) <= max y (7*z - x + w)))"
  by ferrack

lemma "EX (x::'a::{linordered_field_inverse_zero}) z. (ALL w >= 13*x - 4*z. (EX y. w >= abs x + abs y + z))"
  by ferrack

lemma "EX (x::'a::{linordered_field_inverse_zero}). (ALL y < x. (EX z > (x+y).
  (ALL w. 5*w + 10*x - z >= y --> w + 7*x + 3*z >= 2*y)))"
  by ferrack

lemma "EX (x::'a::{linordered_field_inverse_zero}). (ALL y. (EX z > y.
  (ALL w . w < 13 --> w + 10*x - z >= y --> 5*w + 7*x + 13*z >= 2*y)))"
  by ferrack

lemma "EX (x::'a::{linordered_field_inverse_zero}) y z w. min (5*x + 3*z) (17*w) + 5* abs (y - 8*x + z) <= max y (7*z - x + w)"
  by ferrack

lemma "ALL (x::'a::{linordered_field_inverse_zero}). (EX y. (ALL z>19. y <= x + z & (EX w. abs (y - x) < w)))"
  by ferrack

lemma "ALL (x::'a::{linordered_field_inverse_zero}). (EX y. (ALL z>19. y <= x + z & (EX w. abs (x + z) < w - y)))"
  by ferrack

lemma "ALL (x::'a::{linordered_field_inverse_zero}). (EX y. abs y ~= abs x & (ALL z> max x y. (EX w. w ~= y & w ~= z & 3*w - z >= x + y)))"
  by ferrack

end
