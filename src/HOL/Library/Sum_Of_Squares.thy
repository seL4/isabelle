(* Title:      Library/Sum_Of_Squares
   Author:     Amine Chaieb, University of Cambridge

In order to use the method sos, call it with (sos remote_csdp) to use the remote solver
or install CSDP (https://projects.coin-or.org/Csdp/), set the Isabelle environment
variable CSDP_EXE and call it with (sos csdp). By default, sos calls remote_csdp.
This can take of the order of a minute for one sos call, because sos calls CSDP repeatedly.
If you install CSDP locally, sos calls typically takes only a few seconds.

*)

header {* A decision method for universal multivariate real arithmetic with addition, 
          multiplication and ordering using semidefinite programming*}

theory Sum_Of_Squares
imports Complex_Main (* "~~/src/HOL/Decision_Procs/Dense_Linear_Order" *)
uses
  ("positivstellensatz.ML")
  ("Sum_Of_Squares/sum_of_squares.ML")
  ("Sum_Of_Squares/sos_wrapper.ML")
begin

(* setup sos tactic *)

use "positivstellensatz.ML"
use "Sum_Of_Squares/sum_of_squares.ML"
use "Sum_Of_Squares/sos_wrapper.ML"

setup SosWrapper.setup

text{* Tests -- commented since they work only when csdp is installed  or take too long with remote csdps *}

(*
lemma "(3::real) * x + 7 * a < 4 & 3 < 2 * x \<Longrightarrow> a < 0" by sos

lemma "a1 >= 0 & a2 >= 0 \<and> (a1 * a1 + a2 * a2 = b1 * b1 + b2 * b2 + 2) \<and> (a1 * b1 + a2 * b2 = 0) --> a1 * a2 - b1 * b2 >= (0::real)" by sos

lemma "(3::real) * x + 7 * a < 4 & 3 < 2 * x --> a < 0" by sos

lemma "(0::real) <= x & x <= 1 & 0 <= y & y <= 1  --> x^2 + y^2 < 1 |(x - 1)^2 + y^2 < 1 | x^2 + (y - 1)^2 < 1 | (x - 1)^2 + (y - 1)^2 < 1" by sos

lemma "(0::real) <= x & 0 <= y & 0 <= z & x + y + z <= 3 --> x * y + x * z + y * z >= 3 * x * y * z" by sos

lemma "((x::real)^2 + y^2 + z^2 = 1) --> (x + y + z)^2 <= 3" by sos

lemma "(w^2 + x^2 + y^2 + z^2 = 1) --> (w + x + y + z)^2 <= (4::real)" by sos

lemma "(x::real) >= 1 & y >= 1 --> x * y >= x + y - 1" by sos

lemma "(x::real) > 1 & y > 1 --> x * y > x + y - 1" by sos; 

lemma "abs(x) <= 1 --> abs(64 * x^7 - 112 * x^5 + 56 * x^3 - 7 * x) <= (1::real)" by sos  
*)
(* ------------------------------------------------------------------------- *)
(* One component of denominator in dodecahedral example.                     *)
(* ------------------------------------------------------------------------- *)
(*
lemma "2 <= x & x <= 125841 / 50000 & 2 <= y & y <= 125841 / 50000 & 2 <= z & z <= 125841 / 50000 --> 2 * (x * z + x * y + y * z) - (x * x + y * y + z * z) >= (0::real)" by sos;
*)
(* ------------------------------------------------------------------------- *)
(* Over a larger but simpler interval.                                       *)
(* ------------------------------------------------------------------------- *)
(*
lemma "(2::real) <= x & x <= 4 & 2 <= y & y <= 4 & 2 <= z & z <= 4 --> 0 <= 2 * (x * z + x * y + y * z) - (x * x + y * y + z * z)" by sos
*)
(* ------------------------------------------------------------------------- *)
(* We can do 12. I think 12 is a sharp bound; see PP's certificate.          *)
(* ------------------------------------------------------------------------- *)
(*
lemma "2 <= (x::real) & x <= 4 & 2 <= y & y <= 4 & 2 <= z & z <= 4 --> 12 <= 2 * (x * z + x * y + y * z) - (x * x + y * y + z * z)" by sos
*)

(* ------------------------------------------------------------------------- *)
(* Inequality from sci.math (see "Leon-Sotelo, por favor").                  *)
(* ------------------------------------------------------------------------- *)
(*
lemma "0 <= (x::real) & 0 <= y & (x * y = 1) --> x + y <= x^2 + y^2" by sos 

lemma "0 <= (x::real) & 0 <= y & (x * y = 1) --> x * y * (x + y) <= x^2 + y^2" by sos 

lemma "0 <= (x::real) & 0 <= y --> x * y * (x + y)^2 <= (x^2 + y^2)^2" by sos

lemma "(0::real) <= a & 0 <= b & 0 <= c & c * (2 * a + b)^3/ 27 <= x \<longrightarrow> c * a^2 * b <= x" by sos
 
lemma "(0::real) < x --> 0 < 1 + x + x^2" by sos

lemma "(0::real) <= x --> 0 < 1 + x + x^2" by sos

lemma "(0::real) < 1 + x^2" by sos

lemma "(0::real) <= 1 + 2 * x + x^2" by sos

lemma "(0::real) < 1 + abs x" by sos

lemma "(0::real) < 1 + (1 + x)^2 * (abs x)" by sos



lemma "abs ((1::real) + x^2) = (1::real) + x^2" by sos
lemma "(3::real) * x + 7 * a < 4 \<and> 3 < 2 * x \<longrightarrow> a < 0" by sos

lemma "(0::real) < x --> 1 < y --> y * x <= z --> x < z" by sos
lemma "(1::real) < x --> x^2 < y --> 1 < y" by sos
lemma "(b::real)^2 < 4 * a * c --> ~(a * x^2 + b * x + c = 0)" by sos
lemma "(b::real)^2 < 4 * a * c --> ~(a * x^2 + b * x + c = 0)" by sos
lemma "((a::real) * x^2 + b * x + c = 0) --> b^2 >= 4 * a * c" by sos
lemma "(0::real) <= b & 0 <= c & 0 <= x & 0 <= y & (x^2 = c) & (y^2 = a^2 * c + b) --> a * c <= y * x" by sos
lemma "abs(x - z) <= e & abs(y - z) <= e & 0 <= u & 0 <= v & (u + v = 1) --> abs((u * x + v * y) - z) <= (e::real)" by sos
*)
(*
lemma "((x::real) - y - 2 * x^4 = 0) & 0 <= x & x <= 2 & 0 <= y & y <= 3 --> y^2 - 7 * y - 12 * x + 17 >= 0" by sos *) (* Too hard?*)
(*
lemma "(0::real) <= x --> (1 + x + x^2)/(1 + x^2) <= 1 + x"
apply sos
done

lemma "(0::real) <= x --> 1 - x <= 1 / (1 + x + x^2)"
apply sos
done

lemma "(x::real) <= 1 / 2 --> - x - 2 * x^2 <= - x / (1 - x)"
apply sos
done 

lemma "4*r^2 = p^2 - 4*q & r >= (0::real) & x^2 + p*x + q = 0 --> 2*(x::real) = - p + 2*r | 2*x = -p - 2*r" by sos
*)

end

