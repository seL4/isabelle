(*  Title:      HOL/Real/HahnBanach/Linearform.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* Linearforms *};

theory Linearform = LinearSpace:;

constdefs
  is_linearform :: "['a set, 'a => real] => bool" 
  "is_linearform V f == 
      (ALL x: V. ALL y: V. f (x [+] y) = f x + f y) &
      (ALL x: V. ALL a. f (a [*] x) = a * (f x))"; 

lemma is_linearformI [intro]: 
  "[| !! x y. [| x : V; y : V |] ==> f (x [+] y) = f x + f y;
    !! x c. x : V ==> f (c [*] x) = c * f x |]
 ==> is_linearform V f";
 by (unfold is_linearform_def) force;

lemma linearform_add_linear [intro!!]: 
  "[| is_linearform V f; x:V; y:V |] ==> f (x [+] y) = f x + f y";
  by (unfold is_linearform_def) auto;

lemma linearform_mult_linear [intro!!]: 
  "[| is_linearform V f; x:V |] ==>  f (a [*] x) = a * (f x)"; 
  by (unfold is_linearform_def) auto;

lemma linearform_neg_linear [intro!!]:
  "[|  is_vectorspace V; is_linearform V f; x:V|] ==> f ([-] x) = - f x";
proof -; 
  assume "is_linearform V f" "is_vectorspace V" "x:V"; 
  have "f ([-] x) = f ((- 1r) [*] x)"; by (unfold negate_def) simp;
  also; have "... = (- 1r) * (f x)"; by (rule linearform_mult_linear);
  also; have "... = - (f x)"; by (simp!);
  finally; show ?thesis; .;
qed;

lemma linearform_diff_linear [intro!!]: 
  "[| is_vectorspace V; is_linearform V f; x:V; y:V |] 
  ==> f (x [-] y) = f x - f y";  
proof -;
  assume "is_vectorspace V" "is_linearform V f" "x:V" "y:V";
  have "f (x [-] y) = f (x [+] [-] y)"; by (simp only: diff_def);
  also; have "... = f x + f ([-] y)"; 
    by (rule linearform_add_linear) (simp!)+;
  also; have "f ([-] y) = - f y"; by (rule linearform_neg_linear);
  finally; show "f (x [-] y) = f x - f y"; by (simp!);
qed;

lemma linearform_zero [intro!!, simp]: 
  "[| is_vectorspace V; is_linearform V f |] ==> f <0> = 0r"; 
proof -; 
  assume "is_vectorspace V" "is_linearform V f";
  have "f <0> = f (<0> [-] <0>)"; by (simp!);
  also; have "... = f <0> - f <0>"; 
    by (rule linearform_diff_linear) (simp!)+;
  also; have "... = 0r"; by simp;
  finally; show "f <0> = 0r"; .;
qed; 

end;