(*  Title:      HOL/Induct/Ordinals.thy
    ID:         $Id$
    Author:     Stefan Berghofer and Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Ordinals *}

theory Ordinals = Main:

text {*
  Some basic definitions of ordinal numbers.  Draws an Agda
  development (in Martin-L\"of type theory) by Peter Hancock (see
  \url{http://www.dcs.ed.ac.uk/home/pgh/chat.html}).
*}

datatype ordinal =
    Zero
  | Succ ordinal
  | Limit "nat => ordinal"

consts
  pred :: "ordinal => nat => ordinal option"
primrec
  "pred Zero n = None"
  "pred (Succ a) n = Some a"
  "pred (Limit f) n = Some (f n)"

consts
  iter :: "('a => 'a) => nat => ('a => 'a)"
primrec
  "iter f 0 = id"
  "iter f (Suc n) = f \<circ> (iter f n)"

constdefs
  OpLim :: "(nat => (ordinal => ordinal)) => (ordinal => ordinal)"
  "OpLim F a == Limit (\<lambda>n. F n a)"
  OpItw :: "(ordinal => ordinal) => (ordinal => ordinal)"    ("\<Squnion>")
  "\<Squnion>f == OpLim (iter f)"

consts
  cantor :: "ordinal => ordinal => ordinal"
primrec
  "cantor a Zero = Succ a"
  "cantor a (Succ b) = \<Squnion>(\<lambda>x. cantor x b) a"
  "cantor a (Limit f) = Limit (\<lambda>n. cantor a (f n))"

consts
  Nabla :: "(ordinal => ordinal) => (ordinal => ordinal)"    ("\<nabla>")
primrec
  "\<nabla>f Zero = f Zero"
  "\<nabla>f (Succ a) = f (Succ (\<nabla>f a))"
  "\<nabla>f (Limit h) = Limit (\<lambda>n. \<nabla>f (h n))"

constdefs
  deriv :: "(ordinal => ordinal) => (ordinal => ordinal)"
  "deriv f == \<nabla>(\<Squnion>f)"

consts
  veblen :: "ordinal => ordinal => ordinal"
primrec
  "veblen Zero = \<nabla>(OpLim (iter (cantor Zero)))"
  "veblen (Succ a) = \<nabla>(OpLim (iter (veblen a)))"
  "veblen (Limit f) = \<nabla>(OpLim (\<lambda>n. veblen (f n)))"

constdefs
  veb :: "ordinal => ordinal"
  "veb a == veblen a Zero"

constdefs
  epsilon0 :: ordinal    ("\<epsilon>\<^sub>0")
  "\<epsilon>\<^sub>0 == veb Zero"
  Gamma0 :: ordinal    ("\<Gamma>\<^sub>0")
  "\<Gamma>\<^sub>0 == Limit (\<lambda>n. iter veb n Zero)"

end
