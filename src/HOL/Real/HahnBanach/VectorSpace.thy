(*  Title:      HOL/Real/HahnBanach/VectorSpace.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* Vector spaces *}

theory VectorSpace = Bounds + Aux:

subsection {* Signature *}

text {* For the definition of real vector spaces a type $\alpha$
of the sort $\{ \idt{plus}, \idt{minus}, \idt{zero}\}$ is considered, on which a
real scalar multiplication $\mult$ is defined. *}

consts
  prod  :: "[real, 'a::{plus, minus, zero}] => 'a"     (infixr "'(*')" 70)

syntax (symbols)
  prod  :: "[real, 'a] => 'a"                          (infixr "\<cdot>" 70)


subsection {* Vector space laws *}

text {* A \emph{vector space} is a non-empty set $V$ of elements from
  $\alpha$ with the following vector space laws: The set $V$ is closed
  under addition and scalar multiplication, addition is associative
  and commutative; $\minus x$ is the inverse of $x$ w.~r.~t.~addition
  and $0$ is the neutral element of addition.  Addition and
  multiplication are distributive; scalar multiplication is
  associative and the real number $1$ is the neutral element of scalar
  multiplication.
*}

constdefs
  is_vectorspace :: "('a::{plus, minus, zero}) set => bool"
  "is_vectorspace V == V \<noteq> {}
   \<and> (\<forall>x \<in> V. \<forall>y \<in> V. \<forall>z \<in> V. \<forall>a b.
        x + y \<in> V                                 
      \<and> a \<cdot> x \<in> V                                 
      \<and> (x + y) + z = x + (y + z)             
      \<and> x + y = y + x                           
      \<and> x - x = 0                               
      \<and> 0 + x = x                               
      \<and> a \<cdot> (x + y) = a \<cdot> x + a \<cdot> y       
      \<and> (a + b) \<cdot> x = a \<cdot> x + b \<cdot> x         
      \<and> (a * b) \<cdot> x = a \<cdot> b \<cdot> x               
      \<and> #1 \<cdot> x = x
      \<and> - x = (- #1) \<cdot> x
      \<and> x - y = x + - y)"                             

text_raw {* \medskip *}
text {* The corresponding introduction rule is:*}

lemma vsI [intro]:
  "[| 0 \<in> V; 
  \<forall>x \<in> V. \<forall>y \<in> V. x + y \<in> V; 
  \<forall>x \<in> V. \<forall>a. a \<cdot> x \<in> V;  
  \<forall>x \<in> V. \<forall>y \<in> V. \<forall>z \<in> V. (x + y) + z = x + (y + z);
  \<forall>x \<in> V. \<forall>y \<in> V. x + y = y + x;
  \<forall>x \<in> V. x - x = 0;
  \<forall>x \<in> V. 0 + x = x;
  \<forall>x \<in> V. \<forall>y \<in> V. \<forall>a. a \<cdot> (x + y) = a \<cdot> x + a \<cdot> y;
  \<forall>x \<in> V. \<forall>a b. (a + b) \<cdot> x = a \<cdot> x + b \<cdot> x;
  \<forall>x \<in> V. \<forall>a b. (a * b) \<cdot> x = a \<cdot> b \<cdot> x; 
  \<forall>x \<in> V. #1 \<cdot> x = x; 
  \<forall>x \<in> V. - x = (- #1) \<cdot> x; 
  \<forall>x \<in> V. \<forall>y \<in> V. x - y = x + - y |] ==> is_vectorspace V"
proof (unfold is_vectorspace_def, intro conjI ballI allI)
  fix x y z 
  assume "x \<in> V" "y \<in> V" "z \<in> V"
    "\<forall>x \<in> V. \<forall>y \<in> V. \<forall>z \<in> V. x + y + z = x + (y + z)"
  thus "x + y + z =  x + (y + z)" by blast
qed force+

text_raw {* \medskip *}
text {* The corresponding destruction rules are: *}

lemma negate_eq1: 
  "[| is_vectorspace V; x \<in> V |] ==> - x = (- #1) \<cdot> x"
  by (unfold is_vectorspace_def) simp

lemma diff_eq1: 
  "[| is_vectorspace V; x \<in> V; y \<in> V |] ==> x - y = x + - y"
  by (unfold is_vectorspace_def) simp 

lemma negate_eq2: 
  "[| is_vectorspace V; x \<in> V |] ==> (- #1) \<cdot> x = - x"
  by (unfold is_vectorspace_def) simp

lemma negate_eq2a: 
  "[| is_vectorspace V; x \<in> V |] ==> #-1 \<cdot> x = - x"
  by (unfold is_vectorspace_def) simp

lemma diff_eq2: 
  "[| is_vectorspace V; x \<in> V; y \<in> V |] ==> x + - y = x - y"
  by (unfold is_vectorspace_def) simp  

lemma vs_not_empty [intro?]: "is_vectorspace V ==> (V \<noteq> {})" 
  by (unfold is_vectorspace_def) simp
 
lemma vs_add_closed [simp, intro?]: 
  "[| is_vectorspace V; x \<in> V; y \<in> V |] ==> x + y \<in> V" 
  by (unfold is_vectorspace_def) simp

lemma vs_mult_closed [simp, intro?]: 
  "[| is_vectorspace V; x \<in> V |] ==> a \<cdot> x \<in> V" 
  by (unfold is_vectorspace_def) simp

lemma vs_diff_closed [simp, intro?]: 
 "[| is_vectorspace V; x \<in> V; y \<in> V |] ==> x - y \<in> V"
  by (simp add: diff_eq1 negate_eq1)

lemma vs_neg_closed  [simp, intro?]: 
  "[| is_vectorspace V; x \<in> V |] ==> - x \<in> V"
  by (simp add: negate_eq1)

lemma vs_add_assoc [simp]:  
  "[| is_vectorspace V; x \<in> V; y \<in> V; z \<in> V |]
   ==> (x + y) + z = x + (y + z)"
  by (unfold is_vectorspace_def) fast

lemma vs_add_commute [simp]: 
  "[| is_vectorspace V; x \<in> V; y \<in> V |] ==> y + x = x + y"
  by (unfold is_vectorspace_def) simp

lemma vs_add_left_commute [simp]:
  "[| is_vectorspace V; x \<in> V; y \<in> V; z \<in> V |] 
  ==> x + (y + z) = y + (x + z)"
proof -
  assume "is_vectorspace V" "x \<in> V" "y \<in> V" "z \<in> V"
  hence "x + (y + z) = (x + y) + z" 
    by (simp only: vs_add_assoc)
  also have "... = (y + x) + z" by (simp! only: vs_add_commute)
  also have "... = y + (x + z)" by (simp! only: vs_add_assoc)
  finally show ?thesis .
qed

theorems vs_add_ac = vs_add_assoc vs_add_commute vs_add_left_commute

lemma vs_diff_self [simp]: 
  "[| is_vectorspace V; x \<in> V |] ==>  x - x = 0" 
  by (unfold is_vectorspace_def) simp

text {* The existence of the zero element of a vector space
follows from the non-emptiness of carrier set. *}

lemma zero_in_vs [simp, intro]: "is_vectorspace V ==> 0 \<in> V"
proof - 
  assume "is_vectorspace V"
  have "V \<noteq> {}" ..
  hence "\<exists>x. x \<in> V" by force
  thus ?thesis 
  proof 
    fix x assume "x \<in> V" 
    have "0 = x - x" by (simp!)
    also have "... \<in> V" by (simp! only: vs_diff_closed)
    finally show ?thesis .
  qed
qed

lemma vs_add_zero_left [simp]: 
  "[| is_vectorspace V; x \<in> V |] ==>  0 + x = x"
  by (unfold is_vectorspace_def) simp

lemma vs_add_zero_right [simp]: 
  "[| is_vectorspace V; x \<in> V |] ==>  x + 0 = x"
proof -
  assume "is_vectorspace V" "x \<in> V"
  hence "x + 0 = 0 + x" by simp
  also have "... = x" by (simp!)
  finally show ?thesis .
qed

lemma vs_add_mult_distrib1: 
  "[| is_vectorspace V; x \<in> V; y \<in> V |] 
  ==> a \<cdot> (x + y) = a \<cdot> x + a \<cdot> y"
  by (unfold is_vectorspace_def) simp

lemma vs_add_mult_distrib2: 
  "[| is_vectorspace V; x \<in> V |] 
  ==> (a + b) \<cdot> x = a \<cdot> x + b \<cdot> x" 
  by (unfold is_vectorspace_def) simp

lemma vs_mult_assoc: 
  "[| is_vectorspace V; x \<in> V |] ==> (a * b) \<cdot> x = a \<cdot> (b \<cdot> x)"
  by (unfold is_vectorspace_def) simp

lemma vs_mult_assoc2 [simp]: 
 "[| is_vectorspace V; x \<in> V |] ==> a \<cdot> b \<cdot> x = (a * b) \<cdot> x"
  by (simp only: vs_mult_assoc)

lemma vs_mult_1 [simp]: 
  "[| is_vectorspace V; x \<in> V |] ==> #1 \<cdot> x = x" 
  by (unfold is_vectorspace_def) simp

lemma vs_diff_mult_distrib1: 
  "[| is_vectorspace V; x \<in> V; y \<in> V |] 
  ==> a \<cdot> (x - y) = a \<cdot> x - a \<cdot> y"
  by (simp add: diff_eq1 negate_eq1 vs_add_mult_distrib1)

lemma vs_diff_mult_distrib2: 
  "[| is_vectorspace V; x \<in> V |] 
  ==> (a - b) \<cdot> x = a \<cdot> x - (b \<cdot> x)"
proof -
  assume "is_vectorspace V" "x \<in> V"
  have " (a - b) \<cdot> x = (a + - b) \<cdot> x" 
    by (unfold real_diff_def, simp)
  also have "... = a \<cdot> x + (- b) \<cdot> x" 
    by (rule vs_add_mult_distrib2)
  also have "... = a \<cdot> x + - (b \<cdot> x)" 
    by (simp! add: negate_eq1)
  also have "... = a \<cdot> x - (b \<cdot> x)" 
    by (simp! add: diff_eq1)
  finally show ?thesis .
qed

(*text_raw {* \paragraph {Further derived laws.} *}*)
text_raw {* \medskip *}
text{* Further derived laws: *}

lemma vs_mult_zero_left [simp]: 
  "[| is_vectorspace V; x \<in> V |] ==> #0 \<cdot> x = 0"
proof -
  assume "is_vectorspace V" "x \<in> V"
  have  "#0 \<cdot> x = (#1 - #1) \<cdot> x" by simp
  also have "... = (#1 + - #1) \<cdot> x" by simp
  also have "... =  #1 \<cdot> x + (- #1) \<cdot> x" 
    by (rule vs_add_mult_distrib2)
  also have "... = x + (- #1) \<cdot> x" by (simp!)
  also have "... = x + - x" by (simp! add: negate_eq2a)
  also have "... = x - x" by (simp! add: diff_eq2)
  also have "... = 0" by (simp!)
  finally show ?thesis .
qed

lemma vs_mult_zero_right [simp]: 
  "[| is_vectorspace (V:: 'a::{plus, minus, zero} set) |] 
  ==> a \<cdot> 0 = (0::'a)"
proof -
  assume "is_vectorspace V"
  have "a \<cdot> 0 = a \<cdot> (0 - (0::'a))" by (simp!)
  also have "... =  a \<cdot> 0 - a \<cdot> 0"
     by (rule vs_diff_mult_distrib1) (simp!)+
  also have "... = 0" by (simp!)
  finally show ?thesis .
qed

lemma vs_minus_mult_cancel [simp]:  
  "[| is_vectorspace V; x \<in> V |] ==> (- a) \<cdot> - x = a \<cdot> x"
  by (simp add: negate_eq1)

lemma vs_add_minus_left_eq_diff: 
  "[| is_vectorspace V; x \<in> V; y \<in> V |] ==> - x + y = y - x"
proof - 
  assume "is_vectorspace V" "x \<in> V" "y \<in> V"
  hence "- x + y = y + - x" 
    by (simp add: vs_add_commute)
  also have "... = y - x" by (simp! add: diff_eq1)
  finally show ?thesis .
qed

lemma vs_add_minus [simp]: 
  "[| is_vectorspace V; x \<in> V |] ==> x + - x = 0"
  by (simp! add: diff_eq2)

lemma vs_add_minus_left [simp]: 
  "[| is_vectorspace V; x \<in> V |] ==> - x + x = 0"
  by (simp! add: diff_eq2)

lemma vs_minus_minus [simp]: 
  "[| is_vectorspace V; x \<in> V |] ==> - (- x) = x"
  by (simp add: negate_eq1)

lemma vs_minus_zero [simp]: 
  "is_vectorspace (V::'a::{plus, minus, zero} set) ==> - (0::'a) = 0" 
  by (simp add: negate_eq1)

lemma vs_minus_zero_iff [simp]:
  "[| is_vectorspace V; x \<in> V |] ==> (- x = 0) = (x = 0)" 
  (concl is "?L = ?R")
proof -
  assume "is_vectorspace V" "x \<in> V"
  show "?L = ?R"
  proof
    have "x = - (- x)" by (simp! add: vs_minus_minus)
    also assume ?L
    also have "- ... = 0" by (rule vs_minus_zero)
    finally show ?R .
  qed (simp!)
qed

lemma vs_add_minus_cancel [simp]:  
  "[| is_vectorspace V; x \<in> V; y \<in> V |] ==> x + (- x + y) = y" 
  by (simp add: vs_add_assoc [symmetric] del: vs_add_commute) 

lemma vs_minus_add_cancel [simp]: 
  "[| is_vectorspace V; x \<in> V; y \<in> V |] ==> - x + (x + y) = y" 
  by (simp add: vs_add_assoc [symmetric] del: vs_add_commute) 

lemma vs_minus_add_distrib [simp]:  
  "[| is_vectorspace V; x \<in> V; y \<in> V |] 
  ==> - (x + y) = - x + - y"
  by (simp add: negate_eq1 vs_add_mult_distrib1)

lemma vs_diff_zero [simp]: 
  "[| is_vectorspace V; x \<in> V |] ==> x - 0 = x"
  by (simp add: diff_eq1)  

lemma vs_diff_zero_right [simp]: 
  "[| is_vectorspace V; x \<in> V |] ==> 0 - x = - x"
  by (simp add:diff_eq1)

lemma vs_add_left_cancel:
  "[| is_vectorspace V; x \<in> V; y \<in> V; z \<in> V |] 
   ==> (x + y = x + z) = (y = z)"  
  (concl is "?L = ?R")
proof
  assume "is_vectorspace V" "x \<in> V" "y \<in> V" "z \<in> V"
  have "y = 0 + y" by (simp!)
  also have "... = - x + x + y" by (simp!)
  also have "... = - x + (x + y)" 
    by (simp! only: vs_add_assoc vs_neg_closed)
  also assume "x + y = x + z"
  also have "- x + (x + z) = - x + x + z" 
    by (simp! only: vs_add_assoc [symmetric] vs_neg_closed)
  also have "... = z" by (simp!)
  finally show ?R .
qed force

lemma vs_add_right_cancel: 
  "[| is_vectorspace V; x \<in> V; y \<in> V; z \<in> V |] 
  ==> (y + x = z + x) = (y = z)"  
  by (simp only: vs_add_commute vs_add_left_cancel)

lemma vs_add_assoc_cong: 
  "[| is_vectorspace V; x \<in> V; y \<in> V; x' \<in> V; y' \<in> V; z \<in> V |] 
  ==> x + y = x' + y' ==> x + (y + z) = x' + (y' + z)"
  by (simp only: vs_add_assoc [symmetric]) 

lemma vs_mult_left_commute: 
  "[| is_vectorspace V; x \<in> V; y \<in> V; z \<in> V |] 
  ==> x \<cdot> y \<cdot> z = y \<cdot> x \<cdot> z"  
  by (simp add: real_mult_commute)

lemma vs_mult_zero_uniq:
  "[| is_vectorspace V; x \<in> V; a \<cdot> x = 0; x \<noteq> 0 |] ==> a = #0"
proof (rule classical)
  assume "is_vectorspace V" "x \<in> V" "a \<cdot> x = 0" "x \<noteq> 0"
  assume "a \<noteq> #0"
  have "x = (rinv a * a) \<cdot> x" by (simp!)
  also have "... = rinv a \<cdot> (a \<cdot> x)" by (rule vs_mult_assoc)
  also have "... = rinv a \<cdot> 0" by (simp!)
  also have "... = 0" by (simp!)
  finally have "x = 0" .
  thus "a = #0" by contradiction 
qed

lemma vs_mult_left_cancel: 
  "[| is_vectorspace V; x \<in> V; y \<in> V; a \<noteq> #0 |] ==> 
  (a \<cdot> x = a \<cdot> y) = (x = y)"
  (concl is "?L = ?R")
proof
  assume "is_vectorspace V" "x \<in> V" "y \<in> V" "a \<noteq> #0"
  have "x = #1 \<cdot> x" by (simp!)
  also have "... = (rinv a * a) \<cdot> x" by (simp!)
  also have "... = rinv a \<cdot> (a \<cdot> x)" 
    by (simp! only: vs_mult_assoc)
  also assume ?L
  also have "rinv a \<cdot> ... = y" by (simp!)
  finally show ?R .
qed simp

lemma vs_mult_right_cancel: (*** forward ***)
  "[| is_vectorspace V; x \<in> V; x \<noteq> 0 |] 
  ==> (a \<cdot> x = b \<cdot> x) = (a = b)" (concl is "?L = ?R")
proof
  assume "is_vectorspace V" "x \<in> V" "x \<noteq> 0"
  have "(a - b) \<cdot> x = a \<cdot> x - b \<cdot> x" 
    by (simp! add: vs_diff_mult_distrib2)
  also assume ?L hence "a \<cdot> x - b \<cdot> x = 0" by (simp!)
  finally have "(a - b) \<cdot> x = 0" . 
  hence "a - b = #0" by (simp! add: vs_mult_zero_uniq)
  thus "a = b" by (rule real_add_minus_eq)
qed simp (*** 

lemma vs_mult_right_cancel: 
  "[| is_vectorspace V; x:V; x \<noteq> 0 |] ==>  
  (a ( * ) x = b ( * ) x) = (a = b)"
  (concl is "?L = ?R");
proof;
  assume "is_vectorspace V" "x:V" "x \<noteq> 0";
  assume l: ?L; 
  show "a = b"; 
  proof (rule real_add_minus_eq);
    show "a - b = (#0::real)"; 
    proof (rule vs_mult_zero_uniq);
      have "(a - b) ( * ) x = a ( * ) x - b ( * ) x";
        by (simp! add: vs_diff_mult_distrib2);
      also; from l; have "a ( * ) x - b ( * ) x = 0"; by (simp!);
      finally; show "(a - b) ( * ) x  = 0"; .; 
    qed;
  qed;
next;
  assume ?R;
  thus ?L; by simp;
qed;
**)

lemma vs_eq_diff_eq: 
  "[| is_vectorspace V; x \<in> V; y \<in> V; z \<in> V |] ==> 
  (x = z - y) = (x + y = z)"
  (concl is "?L = ?R" )  
proof -
  assume vs: "is_vectorspace V" "x \<in> V" "y \<in> V" "z \<in> V"
  show "?L = ?R"   
  proof
    assume ?L
    hence "x + y = z - y + y" by simp
    also have "... = z + - y + y" by (simp! add: diff_eq1)
    also have "... = z + (- y + y)" 
      by (rule vs_add_assoc) (simp!)+
    also from vs have "... = z + 0" 
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
  "[| is_vectorspace V; x \<in> V; y \<in> V; x + y = 0 |] ==> x = - y" 
proof -
  assume "is_vectorspace V" "x \<in> V" "y \<in> V" 
  have "x = (- y + y) + x" by (simp!)
  also have "... = - y + (x + y)" by (simp!)
  also assume "x + y = 0"
  also have "- y + 0 = - y" by (simp!)
  finally show "x = - y" .
qed

lemma vs_add_minus_eq: 
  "[| is_vectorspace V; x \<in> V; y \<in> V; x - y = 0 |] ==> x = y" 
proof -
  assume "is_vectorspace V" "x \<in> V" "y \<in> V" "x - y = 0"
  assume "x - y = 0"
  hence e: "x + - y = 0" by (simp! add: diff_eq1)
  with _ _ _ have "x = - (- y)" 
    by (rule vs_add_minus_eq_minus) (simp!)+
  thus "x = y" by (simp!)
qed

lemma vs_add_diff_swap:
  "[| is_vectorspace V; a \<in> V; b \<in> V; c \<in> V; d \<in> V; a + b = c + d |] 
  ==> a - c = d - b"
proof - 
  assume vs: "is_vectorspace V" "a \<in> V" "b \<in> V" "c \<in> V" "d \<in> V" 
    and eq: "a + b = c + d"
  have "- c + (a + b) = - c + (c + d)" 
    by (simp! add: vs_add_left_cancel)
  also have "... = d" by (rule vs_minus_add_cancel)
  finally have eq: "- c + (a + b) = d" .
  from vs have "a - c = (- c + (a + b)) + - b" 
    by (simp add: vs_add_ac diff_eq1)
  also from eq have "...  = d + - b" 
    by (simp! add: vs_add_right_cancel)
  also have "... = d - b" by (simp! add: diff_eq2)
  finally show "a - c = d - b" .
qed

lemma vs_add_cancel_21: 
  "[| is_vectorspace V; x \<in> V; y \<in> V; z \<in> V; u \<in> V |] 
  ==> (x + (y + z) = y + u) = ((x + z) = u)"
  (concl is "?L = ?R") 
proof - 
  assume "is_vectorspace V" "x \<in> V" "y \<in> V" "z \<in> V" "u \<in> V"
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
  "[| is_vectorspace V; x \<in> V; y \<in> V; z \<in> V |] 
  ==> (x + (y + z) = y) = (x = - z)"
  (concl is "?L = ?R" )
proof -
  assume "is_vectorspace V" "x \<in> V" "y \<in> V" "z \<in> V"
  show "?L = ?R"
  proof
    assume l: ?L
    have "x + z = 0" 
    proof (rule vs_add_left_cancel [THEN iffD1])
      have "y + (x + z) = x + (y + z)" by (simp!)
      also note l
      also have "y = y + 0" by (simp!)
      finally show "y + (x + z) = y + 0" .
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