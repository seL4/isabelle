(*  Title:      HOL/Real/HahnBanach/VectorSpace.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* Vector spaces *}

theory VectorSpace = Bounds + Aux:

subsection {* Signature *}

text {* For the definition of real vector spaces a type $\alpha$
of the sort $\{ \idt{plus}, \idt{minus}\}$ is considered, on which a
real scalar multiplication $\mult$, and a zero 
element $\zero$ is defined. *}

consts
  prod  :: "[real, 'a] => 'a"                       (infixr "'(*')" 70)
  zero  :: 'a                                       ("00")

syntax (symbols)
  prod  :: "[real, 'a] => 'a"                       (infixr "\<prod>" 70)
  zero  :: 'a                                       ("\<zero>")

(* text {* The unary and binary minus can be considered as 
abbreviations: *}
*)

(***
constdefs 
  negate :: "'a => 'a"                           ("- _" [100] 100)
  "- x == (- #1) ( * ) x"
  diff :: "'a => 'a => 'a"                       (infixl "-" 68)
  "x - y == x + - y";
***)

subsection {* Vector space laws *}

text {* A \emph{vector space} is a non-empty set $V$ of elements from
  $\alpha$ with the following vector space laws: The set $V$ is closed
  under addition and scalar multiplication, addition is associative
  and commutative; $\minus x$ is the inverse of $x$ w.~r.~t.~addition
  and $\zero$ is the neutral element of addition.  Addition and
  multiplication are distributive; scalar multiplication is
  associative and the real number $1$ is the neutral element of scalar
  multiplication.
*}

constdefs
  is_vectorspace :: "('a::{plus,minus}) set => bool"
  "is_vectorspace V == V ~= {} 
   & (ALL x:V. ALL y:V. ALL z:V. ALL a b.
        x + y : V                                 
      & a (*) x : V                                 
      & (x + y) + z = x + (y + z)             
      & x + y = y + x                           
      & x - x = 00                               
      & 00 + x = x                               
      & a (*) (x + y) = a (*) x + a (*) y       
      & (a + b) (*) x = a (*) x + b (*) x         
      & (a * b) (*) x = a (*) b (*) x               
      & #1 (*) x = x
      & - x = (- #1) (*) x
      & x - y = x + - y)"                             

text_raw {* \medskip *}
text {* The corresponding introduction rule is:*}

lemma vsI [intro]:
  "[| 00:V; 
  ALL x:V. ALL y:V. x + y : V; 
  ALL x:V. ALL a. a (*) x : V;  
  ALL x:V. ALL y:V. ALL z:V. (x + y) + z = x + (y + z);
  ALL x:V. ALL y:V. x + y = y + x;
  ALL x:V. x - x = 00;
  ALL x:V. 00 + x = x;
  ALL x:V. ALL y:V. ALL a. a (*) (x + y) = a (*) x + a (*) y;
  ALL x:V. ALL a b. (a + b) (*) x = a (*) x + b (*) x;
  ALL x:V. ALL a b. (a * b) (*) x = a (*) b (*) x; 
  ALL x:V. #1 (*) x = x; 
  ALL x:V. - x = (- #1) (*) x; 
  ALL x:V. ALL y:V. x - y = x + - y |] ==> is_vectorspace V"
proof (unfold is_vectorspace_def, intro conjI ballI allI)
  fix x y z 
  assume "x:V" "y:V" "z:V"
    "ALL x:V. ALL y:V. ALL z:V. x + y + z = x + (y + z)"
  thus "x + y + z =  x + (y + z)" by (elim bspec[elimify])
qed force+

text_raw {* \medskip *}
text {* The corresponding destruction rules are: *}

lemma negate_eq1: 
  "[| is_vectorspace V; x:V |] ==> - x = (- #1) (*) x"
  by (unfold is_vectorspace_def) simp

lemma diff_eq1: 
  "[| is_vectorspace V; x:V; y:V |] ==> x - y = x + - y"
  by (unfold is_vectorspace_def) simp 

lemma negate_eq2: 
  "[| is_vectorspace V; x:V |] ==> (- #1) (*) x = - x"
  by (unfold is_vectorspace_def) simp

lemma negate_eq2a: 
  "[| is_vectorspace V; x:V |] ==> #-1 (*) x = - x"
  by (unfold is_vectorspace_def) simp

lemma diff_eq2: 
  "[| is_vectorspace V; x:V; y:V |] ==> x + - y = x - y"
  by (unfold is_vectorspace_def) simp  

lemma vs_not_empty [intro??]: "is_vectorspace V ==> (V ~= {})" 
  by (unfold is_vectorspace_def) simp
 
lemma vs_add_closed [simp, intro??]: 
  "[| is_vectorspace V; x:V; y:V |] ==> x + y : V" 
  by (unfold is_vectorspace_def) simp

lemma vs_mult_closed [simp, intro??]: 
  "[| is_vectorspace V; x:V |] ==> a (*) x : V" 
  by (unfold is_vectorspace_def) simp

lemma vs_diff_closed [simp, intro??]: 
 "[| is_vectorspace V; x:V; y:V |] ==> x - y : V"
  by (simp add: diff_eq1 negate_eq1)

lemma vs_neg_closed  [simp, intro??]: 
  "[| is_vectorspace V; x:V |] ==> - x : V"
  by (simp add: negate_eq1)

lemma vs_add_assoc [simp]:  
  "[| is_vectorspace V; x:V; y:V; z:V |]
   ==> (x + y) + z = x + (y + z)"
  by (unfold is_vectorspace_def) fast

lemma vs_add_commute [simp]: 
  "[| is_vectorspace V; x:V; y:V |] ==> y + x = x + y"
  by (unfold is_vectorspace_def) simp

lemma vs_add_left_commute [simp]:
  "[| is_vectorspace V; x:V; y:V; z:V |] 
  ==> x + (y + z) = y + (x + z)"
proof -
  assume "is_vectorspace V" "x:V" "y:V" "z:V"
  hence "x + (y + z) = (x + y) + z" 
    by (simp only: vs_add_assoc)
  also have "... = (y + x) + z" by (simp! only: vs_add_commute)
  also have "... = y + (x + z)" by (simp! only: vs_add_assoc)
  finally show ?thesis .
qed

theorems vs_add_ac = vs_add_assoc vs_add_commute vs_add_left_commute

lemma vs_diff_self [simp]: 
  "[| is_vectorspace V; x:V |] ==>  x - x = 00" 
  by (unfold is_vectorspace_def) simp

text {* The existence of the zero element of a vector space
follows from the non-emptiness of carrier set. *}

lemma zero_in_vs [simp, intro]: "is_vectorspace V ==> 00:V"
proof - 
  assume "is_vectorspace V"
  have "V ~= {}" ..
  hence "EX x. x:V" by force
  thus ?thesis 
  proof 
    fix x assume "x:V" 
    have "00 = x - x" by (simp!)
    also have "... : V" by (simp! only: vs_diff_closed)
    finally show ?thesis .
  qed
qed

lemma vs_add_zero_left [simp]: 
  "[| is_vectorspace V; x:V |] ==>  00 + x = x"
  by (unfold is_vectorspace_def) simp

lemma vs_add_zero_right [simp]: 
  "[| is_vectorspace V; x:V |] ==>  x + 00 = x"
proof -
  assume "is_vectorspace V" "x:V"
  hence "x + 00 = 00 + x" by simp
  also have "... = x" by (simp!)
  finally show ?thesis .
qed

lemma vs_add_mult_distrib1: 
  "[| is_vectorspace V; x:V; y:V |] 
  ==> a (*) (x + y) = a (*) x + a (*) y"
  by (unfold is_vectorspace_def) simp

lemma vs_add_mult_distrib2: 
  "[| is_vectorspace V; x:V |] 
  ==> (a + b) (*) x = a (*) x + b (*) x" 
  by (unfold is_vectorspace_def) simp

lemma vs_mult_assoc: 
  "[| is_vectorspace V; x:V |] ==> (a * b) (*) x = a (*) (b (*) x)"
  by (unfold is_vectorspace_def) simp

lemma vs_mult_assoc2 [simp]: 
 "[| is_vectorspace V; x:V |] ==> a (*) b (*) x = (a * b) (*) x"
  by (simp only: vs_mult_assoc)

lemma vs_mult_1 [simp]: 
  "[| is_vectorspace V; x:V |] ==> #1 (*) x = x" 
  by (unfold is_vectorspace_def) simp

lemma vs_diff_mult_distrib1: 
  "[| is_vectorspace V; x:V; y:V |] 
  ==> a (*) (x - y) = a (*) x - a (*) y"
  by (simp add: diff_eq1 negate_eq1 vs_add_mult_distrib1)

lemma vs_diff_mult_distrib2: 
  "[| is_vectorspace V; x:V |] 
  ==> (a - b) (*) x = a (*) x - (b (*) x)"
proof -
  assume "is_vectorspace V" "x:V"
  have " (a - b) (*) x = (a + - b) (*) x" 
    by (unfold real_diff_def, simp)
  also have "... = a (*) x + (- b) (*) x" 
    by (rule vs_add_mult_distrib2)
  also have "... = a (*) x + - (b (*) x)" 
    by (simp! add: negate_eq1)
  also have "... = a (*) x - (b (*) x)" 
    by (simp! add: diff_eq1)
  finally show ?thesis .
qed

(*text_raw {* \paragraph {Further derived laws.} *}*)
text_raw {* \medskip *}
text{* Further derived laws: *}

lemma vs_mult_zero_left [simp]: 
  "[| is_vectorspace V; x:V |] ==> #0 (*) x = 00"
proof -
  assume "is_vectorspace V" "x:V"
  have  "#0 (*) x = (#1 - #1) (*) x" by simp
  also have "... = (#1 + - #1) (*) x" by simp
  also have "... =  #1 (*) x + (- #1) (*) x" 
    by (rule vs_add_mult_distrib2)
  also have "... = x + (- #1) (*) x" by (simp!)
  also have "... = x + - x" by (simp! add: negate_eq2a)
  also have "... = x - x" by (simp! add: diff_eq2)
  also have "... = 00" by (simp!)
  finally show ?thesis .
qed

lemma vs_mult_zero_right [simp]: 
  "[| is_vectorspace (V:: 'a::{plus, minus} set) |] 
  ==> a (*) 00 = (00::'a)"
proof -
  assume "is_vectorspace V"
  have "a (*) 00 = a (*) (00 - (00::'a))" by (simp!)
  also have "... =  a (*) 00 - a (*) 00"
     by (rule vs_diff_mult_distrib1) (simp!)+
  also have "... = 00" by (simp!)
  finally show ?thesis .
qed

lemma vs_minus_mult_cancel [simp]:  
  "[| is_vectorspace V; x:V |] ==> (- a) (*) - x = a (*) x"
  by (simp add: negate_eq1)

lemma vs_add_minus_left_eq_diff: 
  "[| is_vectorspace V; x:V; y:V |] ==> - x + y = y - x"
proof - 
  assume "is_vectorspace V" "x:V" "y:V"
  have "- x + y = y + - x" 
    by (simp! add: vs_add_commute [RS sym, of V "- x"])
  also have "... = y - x" by (simp! add: diff_eq1)
  finally show ?thesis .
qed

lemma vs_add_minus [simp]: 
  "[| is_vectorspace V; x:V |] ==> x + - x = 00"
  by (simp! add: diff_eq2)

lemma vs_add_minus_left [simp]: 
  "[| is_vectorspace V; x:V |] ==> - x + x = 00"
  by (simp! add: diff_eq2)

lemma vs_minus_minus [simp]: 
  "[| is_vectorspace V; x:V |] ==> - (- x) = x"
  by (simp add: negate_eq1)

lemma vs_minus_zero [simp]: 
  "is_vectorspace (V::'a::{minus, plus} set) ==> - (00::'a) = 00" 
  by (simp add: negate_eq1)

lemma vs_minus_zero_iff [simp]:
  "[| is_vectorspace V; x:V |] ==> (- x = 00) = (x = 00)" 
  (concl is "?L = ?R")
proof -
  assume "is_vectorspace V" "x:V"
  show "?L = ?R"
  proof
    have "x = - (- x)" by (rule vs_minus_minus [RS sym])
    also assume ?L
    also have "- ... = 00" by (rule vs_minus_zero)
    finally show ?R .
  qed (simp!)
qed

lemma vs_add_minus_cancel [simp]:  
  "[| is_vectorspace V; x:V; y:V |] ==> x + (- x + y) = y" 
  by (simp add: vs_add_assoc [RS sym] del: vs_add_commute) 

lemma vs_minus_add_cancel [simp]: 
  "[| is_vectorspace V; x:V; y:V |] ==> - x + (x + y) = y" 
  by (simp add: vs_add_assoc [RS sym] del: vs_add_commute) 

lemma vs_minus_add_distrib [simp]:  
  "[| is_vectorspace V; x:V; y:V |] 
  ==> - (x + y) = - x + - y"
  by (simp add: negate_eq1 vs_add_mult_distrib1)

lemma vs_diff_zero [simp]: 
  "[| is_vectorspace V; x:V |] ==> x - 00 = x"
  by (simp add: diff_eq1)  

lemma vs_diff_zero_right [simp]: 
  "[| is_vectorspace V; x:V |] ==> 00 - x = - x"
  by (simp add:diff_eq1)

lemma vs_add_left_cancel:
  "[| is_vectorspace V; x:V; y:V; z:V |] 
   ==> (x + y = x + z) = (y = z)"  
  (concl is "?L = ?R")
proof
  assume "is_vectorspace V" "x:V" "y:V" "z:V"
  have "y = 00 + y" by (simp!)
  also have "... = - x + x + y" by (simp!)
  also have "... = - x + (x + y)" 
    by (simp! only: vs_add_assoc vs_neg_closed)
  also assume ?L 
  also have "- x + ... = - x + x + z" 
    by (rule vs_add_assoc [RS sym]) (simp!)+
  also have "... = z" by (simp!)
  finally show ?R .
qed force

lemma vs_add_right_cancel: 
  "[| is_vectorspace V; x:V; y:V; z:V |] 
  ==> (y + x = z + x) = (y = z)"  
  by (simp only: vs_add_commute vs_add_left_cancel)

lemma vs_add_assoc_cong: 
  "[| is_vectorspace V; x:V; y:V; x':V; y':V; z:V |] 
  ==> x + y = x' + y' ==> x + (y + z) = x' + (y' + z)"
  by (simp only: vs_add_assoc [RS sym]) 

lemma vs_mult_left_commute: 
  "[| is_vectorspace V; x:V; y:V; z:V |] 
  ==> x (*) y (*) z = y (*) x (*) z"  
  by (simp add: real_mult_commute)

lemma vs_mult_zero_uniq :
  "[| is_vectorspace V; x:V; a (*) x = 00; x ~= 00 |] ==> a = #0"
proof (rule classical)
  assume "is_vectorspace V" "x:V" "a (*) x = 00" "x ~= 00"
  assume "a ~= #0"
  have "x = (rinv a * a) (*) x" by (simp!)
  also have "... = rinv a (*) (a (*) x)" by (rule vs_mult_assoc)
  also have "... = rinv a (*) 00" by (simp!)
  also have "... = 00" by (simp!)
  finally have "x = 00" .
  thus "a = #0" by contradiction 
qed

lemma vs_mult_left_cancel: 
  "[| is_vectorspace V; x:V; y:V; a ~= #0 |] ==> 
  (a (*) x = a (*) y) = (x = y)"
  (concl is "?L = ?R")
proof
  assume "is_vectorspace V" "x:V" "y:V" "a ~= #0"
  have "x = #1 (*) x" by (simp!)
  also have "... = (rinv a * a) (*) x" by (simp!)
  also have "... = rinv a (*) (a (*) x)" 
    by (simp! only: vs_mult_assoc)
  also assume ?L
  also have "rinv a (*) ... = y" by (simp!)
  finally show ?R .
qed simp

lemma vs_mult_right_cancel: (*** forward ***)
  "[| is_vectorspace V; x:V; x ~= 00 |] 
  ==> (a (*) x = b (*) x) = (a = b)" (concl is "?L = ?R")
proof
  assume "is_vectorspace V" "x:V" "x ~= 00"
  have "(a - b) (*) x = a (*) x - b (*) x" 
    by (simp! add: vs_diff_mult_distrib2)
  also assume ?L hence "a (*) x - b (*) x = 00" by (simp!)
  finally have "(a - b) (*) x = 00" . 
  hence "a - b = #0" by (simp! add: vs_mult_zero_uniq)
  thus "a = b" by (rule real_add_minus_eq)
qed simp (*** 

backward :
lemma vs_mult_right_cancel: 
  "[| is_vectorspace V; x:V; x ~= 00 |] ==>  
  (a ( * ) x = b ( * ) x) = (a = b)"
  (concl is "?L = ?R");
proof;
  assume "is_vectorspace V" "x:V" "x ~= 00";
  assume l: ?L; 
  show "a = b"; 
  proof (rule real_add_minus_eq);
    show "a - b = (#0::real)"; 
    proof (rule vs_mult_zero_uniq);
      have "(a - b) ( * ) x = a ( * ) x - b ( * ) x";
        by (simp! add: vs_diff_mult_distrib2);
      also; from l; have "a ( * ) x - b ( * ) x = 00"; by (simp!);
      finally; show "(a - b) ( * ) x  = 00"; .; 
    qed;
  qed;
next;
  assume ?R;
  thus ?L; by simp;
qed;
**)

lemma vs_eq_diff_eq: 
  "[| is_vectorspace V; x:V; y:V; z:V |] ==> 
  (x = z - y) = (x + y = z)"
  (concl is "?L = ?R" )  
proof -
  assume vs: "is_vectorspace V" "x:V" "y:V" "z:V"
  show "?L = ?R"   
  proof
    assume ?L
    hence "x + y = z - y + y" by simp
    also have "... = z + - y + y" by (simp! add: diff_eq1)
    also have "... = z + (- y + y)" 
      by (rule vs_add_assoc) (simp!)+
    also from vs have "... = z + 00" 
      by (simp only: vs_add_minus_left)
    also from vs have "... = z" by (simp only: vs_add_zero_right)
    finally show ?R .
  next
    assume ?R
    hence "z - y = (x + y) - y" by simp
    also from vs have "... = x + y + - y" 
      by (simp add: diff_eq1)
    also have "... = x + (y + - y)" 
      by (rule vs_add_assoc) (simp!)+
    also have "... = x" by (simp!)
    finally show ?L by (rule sym)
  qed
qed

lemma vs_add_minus_eq_minus: 
  "[| is_vectorspace V; x:V; y:V; x + y = 00 |] ==> x = - y" 
proof -
  assume "is_vectorspace V" "x:V" "y:V" 
  have "x = (- y + y) + x" by (simp!)
  also have "... = - y + (x + y)" by (simp!)
  also assume "x + y = 00"
  also have "- y + 00 = - y" by (simp!)
  finally show "x = - y" .
qed

lemma vs_add_minus_eq: 
  "[| is_vectorspace V; x:V; y:V; x - y = 00 |] ==> x = y" 
proof -
  assume "is_vectorspace V" "x:V" "y:V" "x - y = 00"
  assume "x - y = 00"
  hence e: "x + - y = 00" by (simp! add: diff_eq1)
  with _ _ _ have "x = - (- y)" 
    by (rule vs_add_minus_eq_minus) (simp!)+
  thus "x = y" by (simp!)
qed

lemma vs_add_diff_swap:
  "[| is_vectorspace V; a:V; b:V; c:V; d:V; a + b = c + d |] 
  ==> a - c = d - b"
proof - 
  assume vs: "is_vectorspace V" "a:V" "b:V" "c:V" "d:V" 
    and eq: "a + b = c + d"
  have "- c + (a + b) = - c + (c + d)" 
    by (simp! add: vs_add_left_cancel)
  also have "... = d" by (rule vs_minus_add_cancel)
  finally have eq: "- c + (a + b) = d" .
  from vs have "a - c = (- c + (a + b)) + - b" 
    by (simp add: vs_add_ac diff_eq1)
  also from eq have "...  = d + - b" 
    by (simp! add: vs_add_right_cancel)
  also have "... = d - b" by (simp! add : diff_eq2)
  finally show "a - c = d - b" .
qed

lemma vs_add_cancel_21: 
  "[| is_vectorspace V; x:V; y:V; z:V; u:V |] 
  ==> (x + (y + z) = y + u) = ((x + z) = u)"
  (concl is "?L = ?R") 
proof - 
  assume "is_vectorspace V" "x:V" "y:V""z:V" "u:V"
  show "?L = ?R"
  proof
    have "x + z = - y + y + (x + z)" by (simp!)
    also have "... = - y + (y + (x + z))"
      by (rule vs_add_assoc) (simp!)+
    also have "y + (x + z) = x + (y + z)" by (simp!)
    also assume ?L
    also have "- y + (y + u) = u" by (simp!)
    finally show ?R .
  qed (simp! only: vs_add_left_commute [of V x])
qed

lemma vs_add_cancel_end: 
  "[| is_vectorspace V;  x:V; y:V; z:V |] 
  ==> (x + (y + z) = y) = (x = - z)"
  (concl is "?L = ?R" )
proof -
  assume "is_vectorspace V" "x:V" "y:V" "z:V"
  show "?L = ?R"
  proof
    assume l: ?L
    have "x + z = 00" 
    proof (rule vs_add_left_cancel [RS iffD1])
      have "y + (x + z) = x + (y + z)" by (simp!)
      also note l
      also have "y = y + 00" by (simp!)
      finally show "y + (x + z) = y + 00" .
    qed (simp!)+
    thus "x = - z" by (simp! add: vs_add_minus_eq_minus)
  next
    assume r: ?R
    hence "x + (y + z) = - z + (y + z)" by simp 
    also have "... = y + (- z + z)" 
      by (simp! only: vs_add_left_commute)
    also have "... = y"  by (simp!)
    finally show ?L .
  qed
qed

end