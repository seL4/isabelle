(*  Title:      HOL/GroupTheory/Ring
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson
    Copyright   1998-2001  University of Cambridge

Ring theory. Sigma version
*)

Ring = Coset +

record 'a ringtype = 'a grouptype +
  Rmult    :: "['a, 'a] => 'a"

syntax 
  "@Rmult"     :: "('a ringtype) => (['a, 'a] => 'a)"  ("_ .<m>"     [10] 10)

translations 
  "R.<m>"  == "Rmult R"

constdefs
  distr_l :: "['a set, ['a, 'a] => 'a, ['a, 'a] => 'a] => bool"
    "distr_l S f1 f2 == (\\<forall>x \\<in> S. \\<forall>y \\<in> S. \\<forall>z \\<in> S. 
                    (f1 x (f2 y z) = f2 (f1 x y) (f1 x z)))"
  distr_r       :: "['a set, ['a, 'a] => 'a, ['a, 'a] => 'a] => bool"
    "distr_r S f1 f2 == (\\<forall>x \\<in> S. \\<forall>y \\<in> S. \\<forall>z \\<in> S. 
                    (f1 (f2 y z) x = f2 (f1 y x) (f1 z x)))"

consts
  Ring :: "('a ringtype) set"

defs 
  Ring_def
    "Ring == 
       {R. (| carrier = (R.<cr>), bin_op = (R.<f>),
	      inverse = (R.<inv>), unit = (R.<e>) |) \\<in> AbelianGroup &
           (R.<m>) \\<in> (R.<cr>) \\<rightarrow> (R.<cr>) \\<rightarrow> (R.<cr>) & 
           (\\<forall>x \\<in> (R.<cr>). \\<forall>y \\<in> (R.<cr>). \\<forall>z \\<in> (R.<cr>). 
                        ((R.<m>) x ((R.<m>) y z) = (R.<m>) ((R.<m>) x y) z)) &
           distr_l (R.<cr>)(R.<m>)(R.<f>) &
	   distr_r (R.<cr>)(R.<m>)(R.<f>) }"


constdefs
  group_of :: "'a ringtype => 'a grouptype"
   "group_of == %R: Ring. (| carrier = (R.<cr>), bin_op = (R.<f>),
			        inverse = (R.<inv>), unit = (R.<e>) |)"

locale ring = group +
  fixes
    R     :: "'a ringtype"
    rmult :: "['a, 'a] => 'a" (infixr "**" 80)
  assumes
    Ring_R "R \\<in> Ring"
  defines
    rmult_def "op ** == (R.<m>)"
    R_id_G    "G == group_of R"

end


