(*  Title:      Test file for Stefan Berghofer's SML code generator
    Author:     Tobias Nipkow, TU Muenchen
*)

theory CodegenSML_Test
imports Executable_Set
begin

lemma "True : {False, True} & False ~: {True}"
by evaluation

lemma
"eq_set ({1::nat,2,3,2} \<union> {3,1,2,1}) {2,2,3,1} &
 eq_set ({1::nat,2,3,2} \<union> {4,1,5,1}) {4,4,5,1,2,3}"
by evaluation

lemma
"eq_set ({1::nat,2,3,2} \<inter> {3,1,2,1}) {2,2,3,1} & 
 eq_set ({1::nat,2,3,2} \<inter> {4,1,5,2}) {2,1,2}"
by evaluation

lemma
"eq_set ({1::nat,2,3,2} - {3,1,2,1}) {} & 
 eq_set ({1::nat,2,3,2} - {4,1,5,2}) {3}"
by evaluation

lemma
"eq_set (Union{{1::nat,2,3,2}, {3,1,2,1}}) {2,2,3,1} &
 eq_set (Union{{1::nat,2,3,2}, {4,1,5,1}}) {4,4,5,1,2,3}"
by evaluation

lemma
"eq_set (Inter{{1::nat,2,3,2}, {3,1,2,1}}) {2,2,3,1} & 
 eq_set (Inter{{1::nat,2,3,2}, {4,1,5,2}}) {2,1,2}"
by evaluation

lemma "eq_set ((%x. x+2) ` {1::nat,2,3,2}) {4,5,3,3}"
by evaluation

lemma
"(ALL x:{1::nat,2,3,2}. EX y : {4,5,2}. x < y) &
 (EX x:{1::nat,2,3,2}. ALL y : {4,5,6}. x < y)"
by evaluation

lemma
"eq_set {x : {4::nat,7,10}. 2 dvd x } {4,10}"
by evaluation

lemma
"fold (op +) (5::int) {3,7,9} = 24 &
 fold_image (op *) id (2::int) {3,4,5} = 120"
by evaluation

end
