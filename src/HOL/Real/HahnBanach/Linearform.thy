(*  Title:      HOL/Real/HahnBanach/Linearform.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* Linearforms *}

theory Linearform = VectorSpace:

text{* A \emph{linear form} is a function on a vector
space into the reals that is additive and multiplicative. *}

constdefs
  is_linearform :: "['a::{minus, plus} set, 'a => real] => bool" 
  "is_linearform V f == 
      (ALL x: V. ALL y: V. f (x + y) = f x + f y) &
      (ALL x: V. ALL a. f (a (*) x) = a * (f x))" 

lemma is_linearformI [intro]: 
  "[| !! x y. [| x : V; y : V |] ==> f (x + y) = f x + f y;
    !! x c. x : V ==> f (c (*) x) = c * f x |]
 ==> is_linearform V f"
 by (unfold is_linearform_def) force

lemma linearform_add [intro??]: 
  "[| is_linearform V f; x:V; y:V |] ==> f (x + y) = f x + f y"
  by (unfold is_linearform_def) fast

lemma linearform_mult [intro??]: 
  "[| is_linearform V f; x:V |] ==>  f (a (*) x) = a * (f x)" 
  by (unfold is_linearform_def) fast

lemma linearform_neg [intro??]:
  "[|  is_vectorspace V; is_linearform V f; x:V|] 
  ==> f (- x) = - f x"
proof - 
  assume "is_linearform V f" "is_vectorspace V" "x:V"
  have "f (- x) = f ((- #1) (*) x)" by (simp! add: negate_eq1)
  also have "... = (- #1) * (f x)" by (rule linearform_mult)
  also have "... = - (f x)" by (simp!)
  finally show ?thesis .
qed

lemma linearform_diff [intro??]: 
  "[| is_vectorspace V; is_linearform V f; x:V; y:V |] 
  ==> f (x - y) = f x - f y"  
proof -
  assume "is_vectorspace V" "is_linearform V f" "x:V" "y:V"
  have "f (x - y) = f (x + - y)" by (simp! only: diff_eq1)
  also have "... = f x + f (- y)" 
    by (rule linearform_add) (simp!)+
  also have "f (- y) = - f y" by (rule linearform_neg)
  finally show "f (x - y) = f x - f y" by (simp!)
qed

text{* Every linear form yields $0$ for the $\zero$ vector.*}

lemma linearform_zero [intro??, simp]: 
  "[| is_vectorspace V; is_linearform V f |] ==> f 00 = #0" 
proof - 
  assume "is_vectorspace V" "is_linearform V f"
  have "f 00 = f (00 - 00)" by (simp!)
  also have "... = f 00 - f 00" 
    by (rule linearform_diff) (simp!)+
  also have "... = #0" by simp
  finally show "f 00 = #0" .
qed 

end