(*  Title:      HOL/Hoare/HeapSyntax.thy
    Author:     Tobias Nipkow
    Copyright   2002 TUM
*)

section \<open>Heap syntax\<close>

theory HeapSyntax
  imports Hoare_Logic Heap
begin

subsection "Field access and update"

syntax
  "_refupdate" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a ref \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b)"
   ("_/'((_ \<rightarrow> _)')" [1000,0] 900)
  "_fassign"  :: "'a ref => id => 'v => 's com"
   ("(2_^._ :=/ _)" [70,1000,65] 61)
  "_faccess"  :: "'a ref => ('a ref \<Rightarrow> 'v) => 'v"
   ("_^._" [65,1000] 65)
translations
  "f(r \<rightarrow> v)" == "f(CONST addr r := v)"
  "p^.f := e" => "f := f(p \<rightarrow> e)"
  "p^.f" => "f(CONST addr p)"


declare fun_upd_apply[simp del] fun_upd_same[simp] fun_upd_other[simp]


text "An example due to Suzuki:"

lemma "VARS v n
  {w = Ref w0 & x = Ref x0 & y = Ref y0 & z = Ref z0 &
   distinct[w0,x0,y0,z0]}
  w^.v := (1::int); w^.n := x;
  x^.v := 2; x^.n := y;
  y^.v := 3; y^.n := z;
  z^.v := 4; x^.n := z
  {w^.n^.n^.v = 4}"
by vcg_simp

end
