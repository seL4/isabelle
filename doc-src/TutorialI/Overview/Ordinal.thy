theory Ordinal = Main:

datatype ordinal = Zero | Succ ordinal | Limit "nat \<Rightarrow> ordinal"

consts
  pred :: "ordinal \<Rightarrow> nat \<Rightarrow> ordinal option"
primrec
  "pred Zero n = None"
  "pred (Succ a) n = Some a"
  "pred (Limit f) n = Some (f n)"

constdefs
  OpLim :: "(nat \<Rightarrow> (ordinal \<Rightarrow> ordinal)) \<Rightarrow> (ordinal \<Rightarrow> ordinal)"
  "OpLim F a \<equiv> Limit (\<lambda>n. F n a)"
  OpItw :: "(ordinal \<Rightarrow> ordinal) \<Rightarrow> (ordinal \<Rightarrow> ordinal)"    ("\<Squnion>")
  "\<Squnion>f \<equiv> OpLim (power f)"

consts
  cantor :: "ordinal \<Rightarrow> ordinal \<Rightarrow> ordinal"
primrec
  "cantor a Zero = Succ a"
  "cantor a (Succ b) = \<Squnion>(\<lambda>x. cantor x b) a"
  "cantor a (Limit f) = Limit (\<lambda>n. cantor a (f n))"

consts
  Nabla :: "(ordinal \<Rightarrow> ordinal) \<Rightarrow> (ordinal \<Rightarrow> ordinal)"    ("\<nabla>")
primrec
  "\<nabla>f Zero = f Zero"
  "\<nabla>f (Succ a) = f (Succ (\<nabla>f a))"
  "\<nabla>f (Limit h) = Limit (\<lambda>n. \<nabla>f (h n))"

constdefs
  deriv :: "(ordinal \<Rightarrow> ordinal) \<Rightarrow> (ordinal \<Rightarrow> ordinal)"
  "deriv f \<equiv> \<nabla>(\<Squnion>f)"

consts
  veblen :: "ordinal \<Rightarrow> ordinal \<Rightarrow> ordinal"
primrec
  "veblen Zero = \<nabla>(OpLim (power (cantor Zero)))"
  "veblen (Succ a) = \<nabla>(OpLim (power (veblen a)))"
  "veblen (Limit f) = \<nabla>(OpLim (\<lambda>n. veblen (f n)))"

constdefs
  veb :: "ordinal \<Rightarrow> ordinal"
  "veb a \<equiv> veblen a Zero"
  epsilon0 :: ordinal    ("\<epsilon>\<^sub>0")
  "\<epsilon>\<^sub>0 \<equiv> veb Zero"
  Gamma0 :: ordinal    ("\<Gamma>\<^sub>0")
  "\<Gamma>\<^sub>0 \<equiv> Limit (\<lambda>n. (veb^n) Zero)"
thm Gamma0_def

end
