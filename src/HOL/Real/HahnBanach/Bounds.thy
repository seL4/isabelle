(*  Title:      HOL/Real/HahnBanach/Bounds.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* Bounds *}

theory Bounds = Main + Real:
(*<*)
subsection {* The sets of lower and upper bounds *}

constdefs
  is_LowerBound :: "('a::order) set => 'a set => 'a => bool"
  "is_LowerBound A B == \\<lambda>x. x \\<in> A \\<and> (\\<forall>y \\<in> B. x <= y)"
   
  LowerBounds :: "('a::order) set => 'a set => 'a set"
  "LowerBounds A B == Collect (is_LowerBound A B)"

  is_UpperBound :: "('a::order) set => 'a set => 'a => bool"
  "is_UpperBound A B == \\<lambda>x. x \\<in> A \\<and> (\\<forall>y \\<in> B. y <= x)"
 
  UpperBounds :: "('a::order) set => 'a set => 'a set"
  "UpperBounds A B == Collect (is_UpperBound A B)"

syntax
  "_UPPERS" :: "[pttrn, 'a set, 'a => bool] => 'a set"     
    ("(3UPPER'_BOUNDS _:_./ _)" 10)
  "_UPPERS_U" :: "[pttrn, 'a => bool] => 'a set"           
    ("(3UPPER'_BOUNDS _./ _)" 10)
  "_LOWERS" :: "[pttrn, 'a set, 'a => bool] => 'a set"     
    ("(3LOWER'_BOUNDS _:_./ _)" 10)
  "_LOWERS_U" :: "[pttrn, 'a => bool] => 'a set"           
    ("(3LOWER'_BOUNDS _./ _)" 10)

translations
  "UPPER_BOUNDS x:A. P" == "UpperBounds A (Collect (\\<lambda>x. P))"
  "UPPER_BOUNDS x. P" == "UPPER_BOUNDS x:UNIV. P"
  "LOWER_BOUNDS x:A. P" == "LowerBounds A (Collect (\\<lambda>x. P))"
  "LOWER_BOUNDS x. P" == "LOWER_BOUNDS x:UNIV. P"


subsection {* Least and greatest elements *}

constdefs
  is_Least :: "('a::order) set => 'a => bool"
  "is_Least B == is_LowerBound B B"

  Least :: "('a::order) set => 'a"
  "Least B == Eps (is_Least B)"

  is_Greatest :: "('a::order) set => 'a => bool"
  "is_Greatest B == is_UpperBound B B"

  Greatest :: "('a::order) set => 'a" 
  "Greatest B == Eps (is_Greatest B)"

syntax
  "_LEAST"    :: "[pttrn, 'a => bool] => 'a"  
    ("(3LLEAST _./ _)" 10)
  "_GREATEST" :: "[pttrn, 'a => bool] => 'a"  
    ("(3GREATEST _./ _)" 10)

translations
  "LLEAST x. P" == "Least {x. P}"
  "GREATEST x. P" == "Greatest {x. P}"


subsection {* Infimum and Supremum *}
(*>*)
text {*
 A supremum\footnote{The definition of the supremum is based on one in
 \url{http://isabelle.in.tum.de/library/HOL/HOL-Real/Lubs.html}}  of
 an ordered set $B$ w.~r.~t. $A$ is defined as a least upper bound of
 $B$, which lies in $A$.
*}
   
text{* If a supremum exists, then $\idt{Sup}\ap A\ap B$
is equal to the supremum. *}

constdefs
  is_Sup :: "('a::order) set => 'a set => 'a => bool"
  "is_Sup A B x == isLub A B x"

  Sup :: "('a::order) set => 'a set => 'a"
  "Sup A B == Eps (is_Sup A B)"
(*<*)
constdefs
  is_Inf :: "('a::order) set => 'a set => 'a => bool"
  "is_Inf A B x == x \\<in> A \\<and>  is_Greatest (LowerBounds A B) x"

  Inf :: "('a::order) set => 'a set => 'a"
  "Inf A B == Eps (is_Inf A B)"

syntax
  "_SUP" :: "[pttrn, 'a set, 'a => bool] => 'a set"
    ("(3SUP _:_./ _)" 10)
  "_SUP_U" :: "[pttrn, 'a => bool] => 'a set"
    ("(3SUP _./ _)" 10)
  "_INF" :: "[pttrn, 'a set, 'a => bool] => 'a set"
    ("(3INF _:_./ _)" 10)
  "_INF_U" :: "[pttrn, 'a => bool] => 'a set"
    ("(3INF _./ _)" 10)

translations
  "SUP x:A. P" == "Sup A (Collect (\\<lambda>x. P))"
  "SUP x. P" == "SUP x:UNIV. P"
  "INF x:A. P" == "Inf A (Collect (\\<lambda>x. P))"
  "INF x. P" == "INF x:UNIV. P"
(*>*)
text{* The supremum of $B$ is less than any upper bound
of $B$.*}

lemma sup_le_ub: "isUb A B y ==> is_Sup A B s ==> s <= y"
  by (unfold is_Sup_def, rule isLub_le_isUb)

text {* The supremum $B$ is an upper bound for $B$. *}

lemma sup_ub: "y \\<in> B ==> is_Sup A B s ==> y <= s"
  by (unfold is_Sup_def, rule isLubD2)

text{* The supremum of a non-empty set $B$ is greater
than a lower bound of $B$. *}

lemma sup_ub1: 
  "[| \\<forall>y \\<in> B. a <= y; is_Sup A B s; x \\<in> B |] ==> a <= s"
proof - 
  assume "\\<forall>y \\<in> B. a <= y" "is_Sup A B s" "x \\<in> B"
  have "a <= x" by (rule bspec)
  also have "x <= s" by (rule sup_ub)
  finally show "a <= s" .
qed
  
end