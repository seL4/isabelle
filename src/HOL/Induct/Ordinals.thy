(*  Title:      HOL/Induct/Ordinals.thy
    Author:     Stefan Berghofer and Markus Wenzel, TU Muenchen
*)

header {* Ordinals *}

theory Ordinals
imports Main
begin

text {*
  Some basic definitions of ordinal numbers.  Draws an Agda
  development (in Martin-L\"of type theory) by Peter Hancock (see
  \url{http://www.dcs.ed.ac.uk/home/pgh/chat.html}).
*}

datatype ordinal =
    Zero
  | Succ ordinal
  | Limit "nat => ordinal"

primrec pred :: "ordinal => nat => ordinal option"
where
  "pred Zero n = None"
| "pred (Succ a) n = Some a"
| "pred (Limit f) n = Some (f n)"

abbreviation (input) iter :: "('a => 'a) => nat => ('a => 'a)"
  where "iter f n \<equiv> f ^^ n"

definition OpLim :: "(nat => (ordinal => ordinal)) => (ordinal => ordinal)"
  where "OpLim F a = Limit (\<lambda>n. F n a)"

definition OpItw :: "(ordinal => ordinal) => (ordinal => ordinal)"  ("\<Squnion>")
  where "\<Squnion>f = OpLim (iter f)"

primrec cantor :: "ordinal => ordinal => ordinal"
where
  "cantor a Zero = Succ a"
| "cantor a (Succ b) = \<Squnion>(\<lambda>x. cantor x b) a"
| "cantor a (Limit f) = Limit (\<lambda>n. cantor a (f n))"

primrec Nabla :: "(ordinal => ordinal) => (ordinal => ordinal)"  ("\<nabla>")
where
  "\<nabla>f Zero = f Zero"
| "\<nabla>f (Succ a) = f (Succ (\<nabla>f a))"
| "\<nabla>f (Limit h) = Limit (\<lambda>n. \<nabla>f (h n))"

definition deriv :: "(ordinal => ordinal) => (ordinal => ordinal)"
  where "deriv f = \<nabla>(\<Squnion>f)"

primrec veblen :: "ordinal => ordinal => ordinal"
where
  "veblen Zero = \<nabla>(OpLim (iter (cantor Zero)))"
| "veblen (Succ a) = \<nabla>(OpLim (iter (veblen a)))"
| "veblen (Limit f) = \<nabla>(OpLim (\<lambda>n. veblen (f n)))"

definition "veb a = veblen a Zero"
definition "\<epsilon>\<^isub>0 = veb Zero"
definition "\<Gamma>\<^isub>0 = Limit (\<lambda>n. iter veb n Zero)"

end
