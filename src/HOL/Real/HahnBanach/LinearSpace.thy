(*  Title:      HOL/Real/HahnBanach/LinearSpace.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* Linear Spaces *};

theory LinearSpace = Bounds + Aux:;

subsection {* Signature *};

consts
  sum	:: "['a, 'a] => 'a"                              (infixl "[+]" 65)
  prod  :: "[real, 'a] => 'a"                            (infixr "[*]" 70) 
  zero  :: 'a                                            ("<0>");

constdefs
  negate :: "'a => 'a"                                   ("[-] _" [100] 100)
  "[-] x == (- 1r) [*] x"
  diff :: "'a => 'a => 'a"                               (infixl "[-]" 68)
  "x [-] y == x [+] [-] y";

subsection {* Vector space laws *}
(***
constdefs
  is_vectorspace :: "'a set => bool"
  "is_vectorspace V == V ~= {} 
   & (ALL x: V. ALL a. a [*] x: V)
   & (ALL x: V. ALL y: V. x [+] y = y [+] x)
   & (ALL x: V. ALL y: V. ALL z: V. x [+] y [+] z =  x [+] (y [+] z))
   & (ALL x: V. ALL y: V. x [+] y: V)
   & (ALL x: V. x [-] x = <0>)
   & (ALL x: V. <0> [+] x = x)
   & (ALL x: V. ALL y: V. ALL a. a [*] (x [+] y) = a [*] x [+] a [*] y)
   & (ALL x: V. ALL a b. (a + b) [*] x = a [*] x [+] b [*] x)
   & (ALL x: V. ALL a b. (a * b) [*] x = a [*] b [*] x)
   & (ALL x: V. 1r [*] x = x)"; 
***)
constdefs
  is_vectorspace :: "'a set => bool"
  "is_vectorspace V == V ~= {} 
   & (ALL x:V. ALL y:V. ALL z:V. ALL a b. 
        x [+] y: V 
      & a [*] x: V                         
      & x [+] y [+] z = x [+] (y [+] z)  
      & x [+] y = y [+] x             
      & x [-] x = <0>         
      & <0> [+] x = x 
      & a [*] (x [+] y) = a [*] x [+] a [*] y
      & (a + b) [*] x = a [*] x [+] b [*] x
      & (a * b) [*] x = a [*] b [*] x     
      & 1r [*] x = x)";

lemma vsI [intro]:
  "[| <0>:V; \
       ALL x: V. ALL y: V. x [+] y: V;
       ALL x: V. ALL a. a [*] x: V;    
       ALL x: V. ALL y: V. ALL z: V. x [+] y [+] z =  x [+] (y [+] z);
       ALL x: V. ALL y: V. x [+] y = y [+] x;
       ALL x: V. x [-] x = <0>;
       ALL x: V. <0> [+] x = x;
       ALL x: V. ALL y: V. ALL a. a [*] (x [+] y) = a [*] x [+] a [*] y;
       ALL x: V. ALL a b. (a + b) [*] x = a [*] x [+] b [*] x;
       ALL x: V. ALL a b. (a * b) [*] x = a [*] b [*] x; \
       ALL x: V. 1r [*] x = x |] ==> is_vectorspace V";
proof (unfold is_vectorspace_def, intro conjI ballI allI);
  fix x y z; assume "x:V" "y:V" "z:V"; 
  assume "ALL x: V. ALL y: V. ALL z: V. x [+] y [+] z =  x [+] (y [+] z)";
  thus "x [+] y [+] z =  x [+] (y [+] z)"; by (elim bspec[elimify]);
qed force+;

lemma vs_not_empty [intro !!]: "is_vectorspace V ==> (V ~= {})"; 
  by (unfold is_vectorspace_def) simp;
 
lemma vs_add_closed [simp, intro!!]: 
  "[| is_vectorspace V; x: V; y: V|] ==> x [+] y: V"; 
  by (unfold is_vectorspace_def) simp;

lemma vs_mult_closed [simp, intro!!]: 
  "[| is_vectorspace V; x: V |] ==> a [*] x: V"; 
  by (unfold is_vectorspace_def) simp;

lemma vs_diff_closed [simp, intro!!]: 
 "[| is_vectorspace V; x: V; y: V|] ==> x [-] y: V";
  by (unfold diff_def negate_def) simp;

lemma vs_neg_closed  [simp, intro!!]: 
  "[| is_vectorspace V; x: V |] ==>  [-] x: V";
  by (unfold negate_def) simp;

lemma vs_add_assoc [simp]:  
  "[| is_vectorspace V; x: V; y: V; z: V|]
   ==> x [+] y [+] z = x [+] (y [+] z)";
  by (unfold is_vectorspace_def) fast;

lemma vs_add_commute [simp]: 
  "[| is_vectorspace V; x:V; y:V |] ==> y [+] x = x [+] y";
  by (unfold is_vectorspace_def) simp;

lemma vs_add_left_commute [simp]:
  "[| is_vectorspace V; x:V; y:V; z:V |] 
  ==> x [+] (y [+] z) = y [+] (x [+] z)";
proof -;
  assume "is_vectorspace V" "x:V" "y:V" "z:V";
  hence "x [+] (y [+] z) = (x [+] y) [+] z"; 
    by (simp only: vs_add_assoc);
  also; have "... = (y [+] x) [+] z"; by (simp! only: vs_add_commute);
  also; have "... = y [+] (x [+] z)"; by (simp! only: vs_add_assoc);
  finally; show ?thesis; .;
qed;

theorems vs_add_ac = vs_add_assoc vs_add_commute vs_add_left_commute;

lemma vs_diff_self [simp]: 
  "[| is_vectorspace V; x:V |] ==>  x [-] x = <0>"; 
  by (unfold is_vectorspace_def) simp;

lemma zero_in_vs [simp, intro]: "is_vectorspace V ==> <0>:V";
proof -; 
  assume "is_vectorspace V";
  have "V ~= {}"; ..;
  hence "EX x. x:V"; by force;
  thus ?thesis; 
  proof; 
    fix x; assume "x:V"; 
    have "<0> = x [-] x"; by (simp!);
    also; have "... : V"; by (simp! only: vs_diff_closed);
    finally; show ?thesis; .;
  qed;
qed;

lemma vs_add_zero_left [simp]: 
  "[| is_vectorspace V; x:V |] ==>  <0> [+] x = x";
  by (unfold is_vectorspace_def) simp;

lemma vs_add_zero_right [simp]: 
  "[| is_vectorspace V; x:V |] ==>  x [+] <0> = x";
proof -;
  assume "is_vectorspace V" "x:V";
  hence "x [+] <0> = <0> [+] x"; by simp;
  also; have "... = x"; by (simp!);
  finally; show ?thesis; .;
qed;

lemma vs_add_mult_distrib1: 
  "[| is_vectorspace V; x:V; y:V |] 
  ==> a [*] (x [+] y) = a [*] x [+] a [*] y";
  by (unfold is_vectorspace_def) simp;

lemma vs_add_mult_distrib2: 
  "[| is_vectorspace V; x:V |] ==> (a + b) [*] x = a [*] x [+] b [*] x"; 
  by (unfold is_vectorspace_def) simp;

lemma vs_mult_assoc: 
  "[| is_vectorspace V; x:V |] ==> (a * b) [*] x = a [*] (b [*] x)";   
  by (unfold is_vectorspace_def) simp;

lemma vs_mult_assoc2 [simp]: 
 "[| is_vectorspace V; x:V |] ==> a [*] b [*] x = (a * b) [*] x";
  by (simp only: vs_mult_assoc);

lemma vs_mult_1 [simp]: 
  "[| is_vectorspace V; x:V |] ==> 1r [*] x = x"; 
  by (unfold is_vectorspace_def) simp;

lemma vs_diff_mult_distrib1: 
  "[| is_vectorspace V; x:V; y:V |] 
  ==> a [*] (x [-] y) = a [*] x [-] a [*] y";
  by (simp add: diff_def negate_def vs_add_mult_distrib1);

lemma vs_minus_eq: "[| is_vectorspace V; x:V |] 
  ==> - b [*] x = [-] (b [*] x)";
  by (simp add: negate_def);

lemma vs_diff_mult_distrib2: 
  "[| is_vectorspace V; x:V |] 
  ==> (a - b) [*] x = a [*] x [-] (b [*] x)";
proof -;
  assume "is_vectorspace V" "x:V";
  have " (a - b) [*] x = (a + - b ) [*] x"; 
    by (unfold real_diff_def, simp);
  also; have "... = a [*] x [+] (- b) [*] x"; 
    by (rule vs_add_mult_distrib2);
  also; have "... = a [*] x [+] [-] (b [*] x)"; 
    by (simp! add: vs_minus_eq);
  also; have "... = a [*] x [-] (b [*] x)"; by (unfold diff_def, simp);
  finally; show ?thesis; .;
qed;

lemma vs_mult_zero_left [simp]: 
  "[| is_vectorspace V; x: V|] ==> 0r [*] x = <0>";
proof -;
  assume "is_vectorspace V" "x:V";
  have  "0r [*] x = (1r - 1r) [*] x"; by (simp only: real_diff_self);
  also; have "... = (1r + - 1r) [*] x"; by simp;
  also; have "... =  1r [*] x [+] (- 1r) [*] x"; 
    by (rule vs_add_mult_distrib2);
  also; have "... = x [+] (- 1r) [*] x"; by (simp!);
  also; have "... = x [+] [-] x"; by (fold negate_def) simp;
  also; have "... = x [-] x"; by (fold diff_def) simp;
  also; have "... = <0>"; by (simp!);
  finally; show ?thesis; .;
qed;

lemma vs_mult_zero_right [simp]: 
  "[| is_vectorspace (V:: 'a set) |] ==> a [*] <0> = (<0>::'a)";
proof -;
  assume "is_vectorspace V";
  have "a [*] <0> = a [*] (<0> [-] (<0>::'a))"; by (simp!);
  also; have "... =  a [*] <0> [-] a [*] <0>";
     by (rule vs_diff_mult_distrib1) (simp!)+;
  also; have "... = <0>"; by (simp!);
  finally; show ?thesis; .;
qed;

lemma vs_minus_mult_cancel [simp]:  
  "[| is_vectorspace V; x:V |] ==> (- a) [*] [-] x = a [*] x";
  by (unfold negate_def) simp;

lemma vs_add_minus_left_eq_diff: 
  "[| is_vectorspace V; x:V; y:V |] ==> [-] x [+] y = y [-] x";
proof -; 
  assume "is_vectorspace V" "x:V" "y:V";
  have "[-] x [+] y = y [+] [-] x"; 
    by (simp! add: vs_add_commute [RS sym, of V "[-] x"]);
  also; have "... = y [-] x"; by (unfold diff_def) simp;
  finally; show ?thesis; .;
qed;

lemma vs_add_minus [simp]: 
  "[| is_vectorspace V; x:V|] ==> x [+] [-] x = <0>";
  by (fold diff_def) simp;

lemma vs_add_minus_left [simp]: 
  "[| is_vectorspace V; x:V |] ==> [-] x [+]  x = <0>";
  by (fold diff_def) simp;

lemma vs_minus_minus [simp]: 
  "[| is_vectorspace V; x:V|] ==> [-] [-] x = x";
  by (unfold negate_def) simp;

lemma vs_minus_zero [simp]: 
  "[| is_vectorspace (V::'a set)|] ==> [-] (<0>::'a) = <0>"; 
  by (unfold negate_def) simp;

lemma vs_minus_zero_iff [simp]:
  "[| is_vectorspace V; x:V|] ==> ([-] x = <0>) = (x = <0>)" 
  (concl is "?L = ?R");
proof -;
  assume vs: "is_vectorspace V" "x:V";
  show "?L = ?R";
  proof;
    assume l: ?L;
    have "x = [-] [-] x"; by (rule vs_minus_minus [RS sym]);
    also; have "... = [-] <0>"; by (simp only: l);
    also; have "... = <0>"; by (rule vs_minus_zero);
    finally; show ?R; .;
  next;
    assume ?R;
    with vs; show ?L; by simp;
  qed;
qed;

lemma vs_add_minus_cancel [simp]:  
  "[| is_vectorspace V; x:V; y:V|] ==>  x [+] ([-] x [+] y) = y"; 
  by (simp add: vs_add_assoc [RS sym] del: vs_add_commute); 

lemma vs_minus_add_cancel [simp]: 
  "[| is_vectorspace V; x:V; y:V |] ==>  [-] x [+] (x [+] y) = y"; 
  by (simp add: vs_add_assoc [RS sym] del: vs_add_commute); 

lemma vs_minus_add_distrib [simp]:  
  "[| is_vectorspace V; x:V; y:V|] 
  ==> [-] (x [+] y) = [-] x [+] [-] y";
  by (unfold negate_def, simp add: vs_add_mult_distrib1);

lemma vs_diff_zero [simp]: 
  "[| is_vectorspace V; x:V |] ==> x [-] <0> = x";
  by (unfold diff_def) simp;  

lemma vs_diff_zero_right [simp]: 
  "[| is_vectorspace V; x:V |] ==> <0> [-] x = [-] x";
  by (unfold diff_def) simp;

lemma vs_add_left_cancel:
  "[| is_vectorspace V; x:V; y:V; z:V|] 
   ==> (x [+] y = x [+] z) = (y = z)"  
  (concl is "?L = ?R");
proof;
  assume "is_vectorspace V" "x:V" "y:V" "z:V";
  assume l: ?L; 
  have "y = <0> [+] y"; by (simp!);
  also; have "... = [-] x [+] x [+] y"; by (simp!);
  also; have "... = [-] x [+] (x [+] y)"; 
    by (simp! only: vs_add_assoc vs_neg_closed);
  also; have "...  = [-] x [+] (x [+] z)"; by (simp only: l);
  also; have "... = [-] x [+] x [+] z"; 
    by (rule vs_add_assoc [RS sym]) (simp!)+;
  also; have "... = z"; by (simp!);
  finally; show ?R;.;
next;    
  assume ?R;
  thus ?L; by force;
qed;

lemma vs_add_right_cancel: 
  "[| is_vectorspace V; x:V; y:V; z:V |] 
  ==> (y [+] x = z [+] x) = (y = z)";  
  by (simp only: vs_add_commute vs_add_left_cancel);

lemma vs_add_assoc_cong [tag FIXME simp]: 
  "[| is_vectorspace V; x:V; y:V; x':V; y':V; z:V |] 
  ==> x [+] y = x' [+] y' ==> x [+] (y [+] z) = x' [+] (y' [+] z)"; 
  by (simp del: vs_add_commute vs_add_assoc add: vs_add_assoc [RS sym]); 

lemma vs_mult_left_commute: 
  "[| is_vectorspace V; x:V; y:V; z:V |] 
  ==> x [*] y [*] z = y [*] x [*] z";  
  by (simp add: real_mult_commute);

lemma vs_mult_zero_uniq :
  "[| is_vectorspace V; x:V; a [*] x = <0>; x ~= <0> |] ==> a = 0r";
proof (rule classical);
  assume "is_vectorspace V" "x:V" "a [*] x = <0>" "x ~= <0>";
  assume "a ~= 0r";
  have "x = (rinv a * a) [*] x"; by (simp!);
  also; have "... = (rinv a) [*] (a [*] x)"; by (rule vs_mult_assoc);
  also; have "... = (rinv a) [*] <0>"; by (simp!);
  also; have "... = <0>"; by (simp!);
  finally; have "x = <0>"; .;
  thus "a = 0r"; by contradiction; 
qed;

lemma vs_mult_left_cancel: 
  "[| is_vectorspace V; x:V; y:V; a ~= 0r |] ==> 
  (a [*] x = a [*] y) = (x = y)"
  (concl is "?L = ?R");
proof;
  assume "is_vectorspace V" "x:V" "y:V" "a ~= 0r";
  assume l: ?L;
  have "x = 1r [*] x"; by (simp!);
  also; have "... = (rinv a * a) [*] x"; by (simp!);
  also; have "... = rinv a [*] (a [*] x)"; 
    by (simp! only: vs_mult_assoc);
  also; have "... = rinv a [*] (a [*] y)"; by (simp only: l);
  also; have "... = y"; by (simp!);
  finally; show ?R;.;
next;
  assume ?R;
  thus ?L; by simp;
qed;

lemma vs_mult_right_cancel: (*** forward ***)
  "[| is_vectorspace V; x:V; x ~= <0> |] ==>  (a [*] x = b [*] x) = (a = b)"
  (concl is "?L = ?R");
proof;
  assume "is_vectorspace V" "x:V" "x ~= <0>";
  assume l: ?L;
  have "(a - b) [*] x = a [*] x [-] b [*] x"; by (simp! add: vs_diff_mult_distrib2);
  also; from l; have "a [*] x [-] b [*] x = <0>"; by (simp!);
  finally; have "(a - b) [*] x  = <0>"; .; 
  hence "a - b = 0r"; by (simp! add:  vs_mult_zero_uniq);
  thus "a = b"; by (rule real_add_minus_eq);
next;
  assume ?R;
  thus ?L; by simp;
qed; (*** backward :
lemma vs_mult_right_cancel: 
  "[| is_vectorspace V; x:V; x ~= <0> |] ==>  (a [*] x = b [*] x) = (a = b)"
  (concl is "?L = ?R");
proof;
  assume "is_vectorspace V" "x:V" "x ~= <0>";
  assume l: ?L; 
  show "a = b"; 
  proof (rule real_add_minus_eq);
    show "a - b = 0r"; 
    proof (rule vs_mult_zero_uniq);
      have "(a - b) [*] x = a [*] x [-] b [*] x"; by (simp! add: vs_diff_mult_distrib2);
      also; from l; have "a [*] x [-] b [*] x = <0>"; by (simp!);
      finally; show "(a - b) [*] x  = <0>"; .; 
    qed;
  qed;
next;
  assume ?R;
  thus ?L; by simp;
qed;
**)

lemma vs_eq_diff_eq: 
  "[| is_vectorspace V; x:V; y:V; z:V |] ==> 
  (x = z [-] y) = (x [+] y = z)"
   (concl is "?L = ?R" );  
proof -;
  assume vs: "is_vectorspace V" "x:V" "y:V" "z:V";
  show "?L = ?R";   
  proof;
    assume l: ?L;
    have "x [+] y = z [-] y [+] y"; by (simp add: l);
    also; have "... = z [+] [-] y [+] y"; by (unfold diff_def) simp;
    also; have "... = z [+] ([-] y [+] y)"; 
      by (rule vs_add_assoc) (simp!)+;
    also; from vs; have "... = z [+] <0>"; 
      by (simp only: vs_add_minus_left);
    also; from vs; have "... = z"; by (simp only: vs_add_zero_right);
    finally; show ?R;.;
  next;
    assume r: ?R;
    have "z [-] y = (x [+] y) [-] y"; by (simp only: r);
    also; from vs; have "... = x [+] y [+] [-] y"; 
      by (unfold diff_def) simp;
    also; have "... = x [+] (y [+] [-] y)"; 
      by (rule vs_add_assoc) (simp!)+;
    also; have "... = x"; by (simp!);
    finally; show ?L; by (rule sym);
  qed;
qed;

lemma vs_add_minus_eq_minus: 
  "[| is_vectorspace V; x:V; y:V; <0> = x [+] y|] ==> y = [-] x"; 
proof -;
  assume vs: "is_vectorspace V" "x:V" "y:V"; 
  assume "<0> = x [+] y";
  have "[-] x = [-] x [+] <0>"; by (simp!);
  also; have "... = [-] x [+] (x [+] y)";  by (simp!);
  also; have "... = [-] x [+] x [+] y"; 
    by (rule vs_add_assoc [RS sym]) (simp!)+;
  also; have "... = (x [+] [-] x) [+] y"; by (simp!);
  also; have "... = y"; by (simp!);
  finally; show ?thesis; by (rule sym);
qed;  

lemma vs_add_minus_eq: 
  "[| is_vectorspace V; x:V; y:V; x [-] y = <0> |] ==> x = y"; 
proof -;
  assume "is_vectorspace V" "x:V" "y:V" "x [-] y = <0>";
  have "x [+] [-] y = x [-] y"; by (unfold diff_def, simp);
  also; have "... = <0>"; .;
  finally; have e: "<0> = x [+] [-] y"; by (rule sym);
  have "x = [-] [-] x"; by (simp!);
  also; have "[-] x = [-] y"; 
    by (rule vs_add_minus_eq_minus [RS sym]) (simp! add: e)+;
  also; have "[-] ... = y"; by (simp!); 
  finally; show "x = y"; .;
qed;

lemma vs_add_diff_swap:
  "[| is_vectorspace V; a:V; b:V; c:V; d:V; a [+] b = c [+] d|] 
  ==> a [-] c = d [-] b";
proof -; 
  assume vs: "is_vectorspace V" "a:V" "b:V" "c:V" "d:V" 
  and eq: "a [+] b = c [+] d";
  have "[-] c [+] (a [+] b) = [-] c [+] (c [+] d)"; 
    by (simp! add: vs_add_left_cancel);
  also; have "... = d"; by (rule vs_minus_add_cancel);
  finally; have eq: "[-] c [+] (a [+] b) = d"; .;
  from vs; have "a [-] c = ([-] c [+] (a [+] b)) [+] [-] b"; 
    by (simp add: vs_add_ac diff_def);
  also; from eq; have "...  = d [+] [-] b"; 
    by (simp! add: vs_add_right_cancel);
  also; have "... = d [-] b"; by (simp add : diff_def);
  finally; show "a [-] c = d [-] b"; .;
qed;

lemma vs_add_cancel_21: 
  "[| is_vectorspace V; x:V; y:V; z:V; u:V|] 
  ==> (x [+] (y [+] z) = y [+] u) = ((x [+] z) = u)"
  (concl is "?L = ?R" ); 
proof -; 
  assume vs: "is_vectorspace V" "x:V" "y:V""z:V" "u:V";
  show "?L = ?R";
  proof;
    assume l: ?L;
    have "u = <0> [+] u"; by (simp!);
    also; have "... = [-] y [+] y [+] u"; by (simp!);
    also; have "... = [-] y [+] (y [+] u)"; 
      by (rule vs_add_assoc) (simp!)+;
    also; have "... = [-] y [+] (x [+] (y [+] z))"; by (simp only: l);
    also; have "... = [-] y [+] (y [+] (x [+] z))"; by (simp!);
    also; have "... = [-] y [+] y [+] (x [+] z)"; 
      by (rule vs_add_assoc [RS sym]) (simp!)+;
    also; have "... = (x [+] z)"; by (simp!);
    finally; show ?R; by (rule sym);
  next;
    assume r: ?R;
    have "x [+] (y [+] z) = y [+] (x [+] z)"; 
      by (simp! only: vs_add_left_commute [of V x]);
    also; have "... = y [+] u"; by (simp only: r);
    finally; show ?L; .;
  qed;
qed;

lemma vs_add_cancel_end: 
  "[| is_vectorspace V;  x:V; y:V; z:V |] 
  ==> (x [+] (y [+] z) = y) = (x = [-] z)"
  (concl is "?L = ?R" );
proof -;
  assume vs: "is_vectorspace V" "x:V" "y:V" "z:V";
  show "?L = ?R";
  proof;
    assume l: ?L;
    have "<0> = x [+] z";
    proof (rule vs_add_left_cancel [RS iffD1]);
      have "y [+] <0> = y"; by (simp! only: vs_add_zero_right); 
      also; have "... =  x [+] (y [+] z)"; by (simp only: l); 
      also; have "... = y [+] (x [+] z)"; 
        by (simp! only: vs_add_left_commute); 
      finally; show "y [+] <0> = y [+] (x [+] z)"; .;
  qed (simp!)+;
    hence "z = [-] x"; by (simp! only: vs_add_minus_eq_minus);
    then; show ?R; by (simp!); 
  next;
    assume r: ?R;
    have "x [+] (y [+] z) = [-] z [+] (y [+] z)"; by (simp only: r); 
    also; have "... = y [+] ([-] z [+] z)"; 
      by (simp! only: vs_add_left_commute);
    also; have "... = y [+] <0>";  by (simp!);
    also; have "... = y";  by (simp!);
    finally; show ?L; .;
  qed;
qed;

lemma it: "[| x = y; x' = y'|] ==> x [+] x' = y [+] y'";
  by simp; 

end;