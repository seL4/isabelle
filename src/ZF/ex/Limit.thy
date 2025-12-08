(*  Title:      ZF/ex/Limit.thy
    Author:     Sten Agerholm
    Author:     Lawrence C Paulson

A formalization of the inverse limit construction of domain theory.

The following paper comments on the formalization:

"A Comparison of HOL-ST and Isabelle/ZF" by Sten Agerholm
In Proceedings of the First Isabelle Users Workshop, Technical
Report No. 379, University of Cambridge Computer Laboratory, 1995.

This is a condensed version of:

"A Comparison of HOL-ST and Isabelle/ZF" by Sten Agerholm
Technical Report No. 369, University of Cambridge Computer
Laboratory, 1995.
*)

theory Limit  imports  ZF begin

definition
  rel :: "[i,i,i]\<Rightarrow>o"  where
    "rel(D,x,y) \<equiv> \<langle>x,y\<rangle>:snd(D)"

definition
  set :: "i\<Rightarrow>i"  where
    "set(D) \<equiv> fst(D)"

definition
  po  :: "i\<Rightarrow>o"  where
    "po(D) \<equiv>
     (\<forall>x \<in> set(D). rel(D,x,x)) \<and>
     (\<forall>x \<in> set(D). \<forall>y \<in> set(D). \<forall>z \<in> set(D).
       rel(D,x,y) \<longrightarrow> rel(D,y,z) \<longrightarrow> rel(D,x,z)) \<and>
     (\<forall>x \<in> set(D). \<forall>y \<in> set(D). rel(D,x,y) \<longrightarrow> rel(D,y,x) \<longrightarrow> x = y)"

definition
  chain :: "[i,i]\<Rightarrow>o"  where
    (* Chains are object level functions nat->set(D) *)
    "chain(D,X) \<equiv> X \<in> nat->set(D) \<and> (\<forall>n \<in> nat. rel(D,X`n,X`(succ(n))))"

definition
  isub :: "[i,i,i]\<Rightarrow>o"  where
    "isub(D,X,x) \<equiv> x \<in> set(D) \<and> (\<forall>n \<in> nat. rel(D,X`n,x))"

definition
  islub :: "[i,i,i]\<Rightarrow>o"  where
    "islub(D,X,x) \<equiv> isub(D,X,x) \<and> (\<forall>y. isub(D,X,y) \<longrightarrow> rel(D,x,y))"

definition
  lub :: "[i,i]\<Rightarrow>i"  where
    "lub(D,X) \<equiv> THE x. islub(D,X,x)"

definition
  cpo :: "i\<Rightarrow>o"  where
    "cpo(D) \<equiv> po(D) \<and> (\<forall>X. chain(D,X) \<longrightarrow> (\<exists>x. islub(D,X,x)))"

definition
  pcpo :: "i\<Rightarrow>o"  where
    "pcpo(D) \<equiv> cpo(D) \<and> (\<exists>x \<in> set(D). \<forall>y \<in> set(D). rel(D,x,y))"

definition
  bot :: "i\<Rightarrow>i"  where
    "bot(D) \<equiv> THE x. x \<in> set(D) \<and> (\<forall>y \<in> set(D). rel(D,x,y))"

definition
  mono :: "[i,i]\<Rightarrow>i"  where
    "mono(D,E) \<equiv>
     {f \<in> set(D)->set(E).
      \<forall>x \<in> set(D). \<forall>y \<in> set(D). rel(D,x,y) \<longrightarrow> rel(E,f`x,f`y)}"

definition
  cont :: "[i,i]\<Rightarrow>i"  where
    "cont(D,E) \<equiv>
     {f \<in> mono(D,E).
      \<forall>X. chain(D,X) \<longrightarrow> f`(lub(D,X)) = lub(E,\<lambda>n \<in> nat. f`(X`n))}"

definition
  cf :: "[i,i]\<Rightarrow>i"  where
    "cf(D,E) \<equiv>
     <cont(D,E),
      {y \<in> cont(D,E)*cont(D,E). \<forall>x \<in> set(D). rel(E,(fst(y))`x,(snd(y))`x)}>"

definition
  suffix :: "[i,i]\<Rightarrow>i"  where
    "suffix(X,n) \<equiv> \<lambda>m \<in> nat. X`(n #+ m)"

definition
  subchain :: "[i,i]\<Rightarrow>o"  where
    "subchain(X,Y) \<equiv> \<forall>m \<in> nat. \<exists>n \<in> nat. X`m = Y`(m #+ n)"

definition
  dominate :: "[i,i,i]\<Rightarrow>o"  where
    "dominate(D,X,Y) \<equiv> \<forall>m \<in> nat. \<exists>n \<in> nat. rel(D,X`m,Y`n)"

definition
  matrix :: "[i,i]\<Rightarrow>o"  where
    "matrix(D,M) \<equiv>
     M \<in> nat -> (nat -> set(D)) \<and>
     (\<forall>n \<in> nat. \<forall>m \<in> nat. rel(D,M`n`m,M`succ(n)`m)) \<and>
     (\<forall>n \<in> nat. \<forall>m \<in> nat. rel(D,M`n`m,M`n`succ(m))) \<and>
     (\<forall>n \<in> nat. \<forall>m \<in> nat. rel(D,M`n`m,M`succ(n)`succ(m)))"

definition
  projpair  :: "[i,i,i,i]\<Rightarrow>o"  where
    "projpair(D,E,e,p) \<equiv>
     e \<in> cont(D,E) \<and> p \<in> cont(E,D) \<and>
     p O e = id(set(D)) \<and> rel(cf(E,E),e O p,id(set(E)))"

definition
  emb       :: "[i,i,i]\<Rightarrow>o"  where
    "emb(D,E,e) \<equiv> \<exists>p. projpair(D,E,e,p)"

definition
  Rp        :: "[i,i,i]\<Rightarrow>i"  where
    "Rp(D,E,e) \<equiv> THE p. projpair(D,E,e,p)"

definition
  (* Twice, constructions on cpos are more difficult. *)
  iprod     :: "i\<Rightarrow>i"  where
    "iprod(DD) \<equiv>
     <(\<Prod>n \<in> nat. set(DD`n)),
      {x:(\<Prod>n \<in> nat. set(DD`n))*(\<Prod>n \<in> nat. set(DD`n)).
       \<forall>n \<in> nat. rel(DD`n,fst(x)`n,snd(x)`n)}>"

definition
  mkcpo     :: "[i,i\<Rightarrow>o]\<Rightarrow>i"  where
    (* Cannot use rel(D), is meta fun, need two more args *)
    "mkcpo(D,P) \<equiv>
     <{x \<in> set(D). P(x)},{x \<in> set(D)*set(D). rel(D,fst(x),snd(x))}>"

definition
  subcpo    :: "[i,i]\<Rightarrow>o"  where
    "subcpo(D,E) \<equiv>
     set(D) \<subseteq> set(E) \<and>
     (\<forall>x \<in> set(D). \<forall>y \<in> set(D). rel(D,x,y) \<longleftrightarrow> rel(E,x,y)) \<and>
     (\<forall>X. chain(D,X) \<longrightarrow> lub(E,X):set(D))"

definition
  subpcpo   :: "[i,i]\<Rightarrow>o"  where
    "subpcpo(D,E) \<equiv> subcpo(D,E) \<and> bot(E):set(D)"

definition
  emb_chain :: "[i,i]\<Rightarrow>o"  where
    "emb_chain(DD,ee) \<equiv>
     (\<forall>n \<in> nat. cpo(DD`n)) \<and> (\<forall>n \<in> nat. emb(DD`n,DD`succ(n),ee`n))"

definition
  Dinf      :: "[i,i]\<Rightarrow>i"  where
    "Dinf(DD,ee) \<equiv>
     mkcpo(iprod(DD))
     (\<lambda>x. \<forall>n \<in> nat. Rp(DD`n,DD`succ(n),ee`n)`(x`succ(n)) = x`n)"

definition
  e_less    :: "[i,i,i,i]\<Rightarrow>i"  where
  (* Valid for m \<le> n only. *)
    "e_less(DD,ee,m,n) \<equiv> rec(n#-m,id(set(DD`m)),\<lambda>x y. ee`(m#+x) O y)"


definition
  e_gr      :: "[i,i,i,i]\<Rightarrow>i"  where
  (* Valid for n \<le> m only. *)
    "e_gr(DD,ee,m,n) \<equiv>
     rec(m#-n,id(set(DD`n)),
         \<lambda>x y. y O Rp(DD`(n#+x),DD`(succ(n#+x)),ee`(n#+x)))"


definition
  eps       :: "[i,i,i,i]\<Rightarrow>i"  where
    "eps(DD,ee,m,n) \<equiv> if(m \<le> n,e_less(DD,ee,m,n),e_gr(DD,ee,m,n))"

definition
  rho_emb   :: "[i,i,i]\<Rightarrow>i"  where
    "rho_emb(DD,ee,n) \<equiv> \<lambda>x \<in> set(DD`n). \<lambda>m \<in> nat. eps(DD,ee,n,m)`x"

definition
  rho_proj  :: "[i,i,i]\<Rightarrow>i"  where
    "rho_proj(DD,ee,n) \<equiv> \<lambda>x \<in> set(Dinf(DD,ee)). x`n"

definition
  commute   :: "[i,i,i,i\<Rightarrow>i]\<Rightarrow>o"  where
    "commute(DD,ee,E,r) \<equiv>
     (\<forall>n \<in> nat. emb(DD`n,E,r(n))) \<and>
     (\<forall>m \<in> nat. \<forall>n \<in> nat. m \<le> n \<longrightarrow> r(n) O eps(DD,ee,m,n) = r(m))"

definition
  mediating :: "[i,i,i\<Rightarrow>i,i\<Rightarrow>i,i]\<Rightarrow>o"  where
    "mediating(E,G,r,f,t) \<equiv> emb(E,G,t) \<and> (\<forall>n \<in> nat. f(n) = t O r(n))"


lemmas nat_linear_le = Ord_linear_le [OF nat_into_Ord nat_into_Ord]


(*----------------------------------------------------------------------*)
(* Basic results.                                                       *)
(*----------------------------------------------------------------------*)

lemma set_I: "x \<in> fst(D) \<Longrightarrow> x \<in> set(D)"
by (simp add: set_def)

lemma rel_I: "\<langle>x,y\<rangle>:snd(D) \<Longrightarrow> rel(D,x,y)"
by (simp add: rel_def)

lemma rel_E: "rel(D,x,y) \<Longrightarrow> \<langle>x,y\<rangle>:snd(D)"
by (simp add: rel_def)

(*----------------------------------------------------------------------*)
(* I/E/D rules for po and cpo.                                          *)
(*----------------------------------------------------------------------*)

lemma po_refl: "\<lbrakk>po(D); x \<in> set(D)\<rbrakk> \<Longrightarrow> rel(D,x,x)"
by (unfold po_def, blast)

lemma po_trans: "\<lbrakk>po(D); rel(D,x,y); rel(D,y,z); x \<in> set(D);
                  y \<in> set(D); z \<in> set(D)\<rbrakk> \<Longrightarrow> rel(D,x,z)"
by (unfold po_def, blast)

lemma po_antisym:
    "\<lbrakk>po(D); rel(D,x,y); rel(D,y,x); x \<in> set(D); y \<in> set(D)\<rbrakk> \<Longrightarrow> x = y"
by (unfold po_def, blast)

lemma poI:
  "\<lbrakk>\<And>x. x \<in> set(D) \<Longrightarrow> rel(D,x,x);
      \<And>x y z. \<lbrakk>rel(D,x,y); rel(D,y,z); x \<in> set(D); y \<in> set(D); z \<in> set(D)\<rbrakk>
               \<Longrightarrow> rel(D,x,z);
      \<And>x y. \<lbrakk>rel(D,x,y); rel(D,y,x); x \<in> set(D); y \<in> set(D)\<rbrakk> \<Longrightarrow> x=y\<rbrakk>
   \<Longrightarrow> po(D)"
by (unfold po_def, blast)

lemma cpoI: "\<lbrakk>po(D); \<And>X. chain(D,X) \<Longrightarrow> islub(D,X,x(D,X))\<rbrakk> \<Longrightarrow> cpo(D)"
by (simp add: cpo_def, blast)

lemma cpo_po: "cpo(D) \<Longrightarrow> po(D)"
by (simp add: cpo_def)

lemma cpo_refl [simp,intro!,TC]: "\<lbrakk>cpo(D); x \<in> set(D)\<rbrakk> \<Longrightarrow> rel(D,x,x)"
by (blast intro: po_refl cpo_po)

lemma cpo_trans:
     "\<lbrakk>cpo(D); rel(D,x,y); rel(D,y,z); x \<in> set(D);
        y \<in> set(D); z \<in> set(D)\<rbrakk> \<Longrightarrow> rel(D,x,z)"
by (blast intro: cpo_po po_trans)

lemma cpo_antisym:
     "\<lbrakk>cpo(D); rel(D,x,y); rel(D,y,x); x \<in> set(D); y \<in> set(D)\<rbrakk> \<Longrightarrow> x = y"
by (blast intro: cpo_po po_antisym)

lemma cpo_islub: "\<lbrakk>cpo(D); chain(D,X);  \<And>x. islub(D,X,x) \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
by (simp add: cpo_def, blast)

(*----------------------------------------------------------------------*)
(* Theorems about isub and islub.                                       *)
(*----------------------------------------------------------------------*)

lemma islub_isub: "islub(D,X,x) \<Longrightarrow> isub(D,X,x)"
by (simp add: islub_def)

lemma islub_in: "islub(D,X,x) \<Longrightarrow> x \<in> set(D)"
by (simp add: islub_def isub_def)

lemma islub_ub: "\<lbrakk>islub(D,X,x); n \<in> nat\<rbrakk> \<Longrightarrow> rel(D,X`n,x)"
by (simp add: islub_def isub_def)

lemma islub_least: "\<lbrakk>islub(D,X,x); isub(D,X,y)\<rbrakk> \<Longrightarrow> rel(D,x,y)"
by (simp add: islub_def)

lemma islubI:
    "\<lbrakk>isub(D,X,x); \<And>y. isub(D,X,y) \<Longrightarrow> rel(D,x,y)\<rbrakk> \<Longrightarrow> islub(D,X,x)"
by (simp add: islub_def)

lemma isubI:
    "\<lbrakk>x \<in> set(D);  \<And>n. n \<in> nat \<Longrightarrow> rel(D,X`n,x)\<rbrakk> \<Longrightarrow> isub(D,X,x)"
by (simp add: isub_def)

lemma isubE:
    "\<lbrakk>isub(D,X,x); \<lbrakk>x \<in> set(D);  \<And>n. n \<in> nat\<Longrightarrow>rel(D,X`n,x)\<rbrakk> \<Longrightarrow> P
\<rbrakk> \<Longrightarrow> P"
by (simp add: isub_def)

lemma isubD1: "isub(D,X,x) \<Longrightarrow> x \<in> set(D)"
by (simp add: isub_def)

lemma isubD2: "\<lbrakk>isub(D,X,x); n \<in> nat\<rbrakk>\<Longrightarrow>rel(D,X`n,x)"
by (simp add: isub_def)

lemma islub_unique: "\<lbrakk>islub(D,X,x); islub(D,X,y); cpo(D)\<rbrakk> \<Longrightarrow> x = y"
by (blast intro: cpo_antisym islub_least islub_isub islub_in)

(*----------------------------------------------------------------------*)
(* lub gives the least upper bound of chains.                           *)
(*----------------------------------------------------------------------*)

lemma cpo_lub: "\<lbrakk>chain(D,X); cpo(D)\<rbrakk> \<Longrightarrow> islub(D,X,lub(D,X))"
apply (simp add: lub_def)
apply (best elim: cpo_islub intro: theI islub_unique)
done

(*----------------------------------------------------------------------*)
(* Theorems about chains.                                               *)
(*----------------------------------------------------------------------*)

lemma chainI:
  "\<lbrakk>X \<in> nat->set(D);  \<And>n. n \<in> nat \<Longrightarrow> rel(D,X`n,X`succ(n))\<rbrakk> \<Longrightarrow> chain(D,X)"
by (simp add: chain_def)

lemma chain_fun: "chain(D,X) \<Longrightarrow> X \<in> nat -> set(D)"
by (simp add: chain_def)

lemma chain_in [simp,TC]: "\<lbrakk>chain(D,X); n \<in> nat\<rbrakk> \<Longrightarrow> X`n \<in> set(D)"
apply (simp add: chain_def)
apply (blast dest: apply_type)
done

lemma chain_rel [simp,TC]:
     "\<lbrakk>chain(D,X); n \<in> nat\<rbrakk> \<Longrightarrow> rel(D, X ` n, X ` succ(n))"
by (simp add: chain_def)

lemma chain_rel_gen_add:
     "\<lbrakk>chain(D,X); cpo(D); n \<in> nat; m \<in> nat\<rbrakk> \<Longrightarrow> rel(D,X`n,(X`(m #+ n)))"
apply (induct_tac m)
apply (auto intro: cpo_trans)
done

lemma chain_rel_gen:
    "\<lbrakk>n \<le> m; chain(D,X); cpo(D); m \<in> nat\<rbrakk> \<Longrightarrow> rel(D,X`n,X`m)"
apply (frule lt_nat_in_nat, erule nat_succI)
apply (erule rev_mp) (*prepare the induction*)
apply (induct_tac m)
apply (auto intro: cpo_trans simp add: le_iff)
done

(*----------------------------------------------------------------------*)
(* Theorems about pcpos and bottom.                                     *)
(*----------------------------------------------------------------------*)

lemma pcpoI:
    "\<lbrakk>\<And>y. y \<in> set(D)\<Longrightarrow>rel(D,x,y); x \<in> set(D); cpo(D)\<rbrakk>\<Longrightarrow>pcpo(D)"
by (simp add: pcpo_def, auto)

lemma pcpo_cpo [TC]: "pcpo(D) \<Longrightarrow> cpo(D)"
by (simp add: pcpo_def)

lemma pcpo_bot_ex1:
    "pcpo(D) \<Longrightarrow> \<exists>! x. x \<in> set(D) \<and> (\<forall>y \<in> set(D). rel(D,x,y))"
apply (simp add: pcpo_def)
apply (blast intro: cpo_antisym)
done

lemma bot_least [TC]:
    "\<lbrakk>pcpo(D); y \<in> set(D)\<rbrakk> \<Longrightarrow> rel(D,bot(D),y)"
apply (simp add: bot_def)
apply (best intro: pcpo_bot_ex1 [THEN theI2])
done

lemma bot_in [TC]:
    "pcpo(D) \<Longrightarrow> bot(D):set(D)"
apply (simp add: bot_def)
apply (best intro: pcpo_bot_ex1 [THEN theI2])
done

lemma bot_unique:
    "\<lbrakk>pcpo(D); x \<in> set(D); \<And>y. y \<in> set(D) \<Longrightarrow> rel(D,x,y)\<rbrakk> \<Longrightarrow> x = bot(D)"
by (blast intro: cpo_antisym pcpo_cpo bot_in bot_least)

(*----------------------------------------------------------------------*)
(* Constant chains and lubs and cpos.                                   *)
(*----------------------------------------------------------------------*)

lemma chain_const: "\<lbrakk>x \<in> set(D); cpo(D)\<rbrakk> \<Longrightarrow> chain(D,(\<lambda>n \<in> nat. x))"
by (simp add: chain_def)

lemma islub_const:
   "\<lbrakk>x \<in> set(D); cpo(D)\<rbrakk> \<Longrightarrow> islub(D,(\<lambda>n \<in> nat. x),x)"
by (simp add: islub_def isub_def, blast)

lemma lub_const: "\<lbrakk>x \<in> set(D); cpo(D)\<rbrakk> \<Longrightarrow> lub(D,\<lambda>n \<in> nat. x) = x"
by (blast intro: islub_unique cpo_lub chain_const islub_const)

(*----------------------------------------------------------------------*)
(* Taking the suffix of chains has no effect on ub's.                   *)
(*----------------------------------------------------------------------*)

lemma isub_suffix:
    "\<lbrakk>chain(D,X); cpo(D)\<rbrakk> \<Longrightarrow> isub(D,suffix(X,n),x) \<longleftrightarrow> isub(D,X,x)"
apply (simp add: isub_def suffix_def, safe)
apply (drule_tac x = na in bspec)
apply (auto intro: cpo_trans chain_rel_gen_add)
done

lemma islub_suffix:
  "\<lbrakk>chain(D,X); cpo(D)\<rbrakk> \<Longrightarrow> islub(D,suffix(X,n),x) \<longleftrightarrow> islub(D,X,x)"
by (simp add: islub_def isub_suffix)

lemma lub_suffix:
    "\<lbrakk>chain(D,X); cpo(D)\<rbrakk> \<Longrightarrow> lub(D,suffix(X,n)) = lub(D,X)"
by (simp add: lub_def islub_suffix)

(*----------------------------------------------------------------------*)
(* Dominate and subchain.                                               *)
(*----------------------------------------------------------------------*)

lemma dominateI:
  "\<lbrakk>\<And>m. m \<in> nat \<Longrightarrow> n(m):nat; \<And>m. m \<in> nat \<Longrightarrow> rel(D,X`m,Y`n(m))\<rbrakk>
   \<Longrightarrow> dominate(D,X,Y)"
by (simp add: dominate_def, blast)

lemma dominate_isub:
  "\<lbrakk>dominate(D,X,Y); isub(D,Y,x); cpo(D);
     X \<in> nat->set(D); Y \<in> nat->set(D)\<rbrakk> \<Longrightarrow> isub(D,X,x)"
apply (simp add: isub_def dominate_def)
apply (blast intro: cpo_trans intro!: apply_funtype)
done

lemma dominate_islub:
  "\<lbrakk>dominate(D,X,Y); islub(D,X,x); islub(D,Y,y); cpo(D);
     X \<in> nat->set(D); Y \<in> nat->set(D)\<rbrakk> \<Longrightarrow> rel(D,x,y)"
apply (simp add: islub_def)
apply (blast intro: dominate_isub)
done

lemma subchain_isub:
     "\<lbrakk>subchain(Y,X); isub(D,X,x)\<rbrakk> \<Longrightarrow> isub(D,Y,x)"
by (simp add: isub_def subchain_def, force)

lemma dominate_islub_eq:
     "\<lbrakk>dominate(D,X,Y); subchain(Y,X); islub(D,X,x); islub(D,Y,y); cpo(D);
        X \<in> nat->set(D); Y \<in> nat->set(D)\<rbrakk> \<Longrightarrow> x = y"
by (blast intro: cpo_antisym dominate_islub islub_least subchain_isub
                 islub_isub islub_in)


(*----------------------------------------------------------------------*)
(* Matrix.                                                              *)
(*----------------------------------------------------------------------*)

lemma matrix_fun: "matrix(D,M) \<Longrightarrow> M \<in> nat -> (nat -> set(D))"
by (simp add: matrix_def)

lemma matrix_in_fun: "\<lbrakk>matrix(D,M); n \<in> nat\<rbrakk> \<Longrightarrow> M`n \<in> nat -> set(D)"
by (blast intro: apply_funtype matrix_fun)

lemma matrix_in: "\<lbrakk>matrix(D,M); n \<in> nat; m \<in> nat\<rbrakk> \<Longrightarrow> M`n`m \<in> set(D)"
by (blast intro: apply_funtype matrix_in_fun)

lemma matrix_rel_1_0:
    "\<lbrakk>matrix(D,M); n \<in> nat; m \<in> nat\<rbrakk> \<Longrightarrow> rel(D,M`n`m,M`succ(n)`m)"
by (simp add: matrix_def)

lemma matrix_rel_0_1:
    "\<lbrakk>matrix(D,M); n \<in> nat; m \<in> nat\<rbrakk> \<Longrightarrow> rel(D,M`n`m,M`n`succ(m))"
by (simp add: matrix_def)

lemma matrix_rel_1_1:
    "\<lbrakk>matrix(D,M); n \<in> nat; m \<in> nat\<rbrakk> \<Longrightarrow> rel(D,M`n`m,M`succ(n)`succ(m))"
by (simp add: matrix_def)

lemma fun_swap: "f \<in> X->Y->Z \<Longrightarrow> (\<lambda>y \<in> Y. \<lambda>x \<in> X. f`x`y):Y->X->Z"
by (blast intro: lam_type apply_funtype)

lemma matrix_sym_axis:
    "matrix(D,M) \<Longrightarrow> matrix(D,\<lambda>m \<in> nat. \<lambda>n \<in> nat. M`n`m)"
by (simp add: matrix_def fun_swap)

lemma matrix_chain_diag:
    "matrix(D,M) \<Longrightarrow> chain(D,\<lambda>n \<in> nat. M`n`n)"
apply (simp add: chain_def)
apply (auto intro: lam_type matrix_in matrix_rel_1_1)
done

lemma matrix_chain_left:
    "\<lbrakk>matrix(D,M); n \<in> nat\<rbrakk> \<Longrightarrow> chain(D,M`n)"
  unfolding chain_def
apply (auto intro: matrix_fun [THEN apply_type] matrix_in matrix_rel_0_1)
done

lemma matrix_chain_right:
    "\<lbrakk>matrix(D,M); m \<in> nat\<rbrakk> \<Longrightarrow> chain(D,\<lambda>n \<in> nat. M`n`m)"
apply (simp add: chain_def)
apply (auto intro: lam_type matrix_in matrix_rel_1_0)
done

lemma matrix_chainI:
  assumes xprem: "\<And>x. x \<in> nat\<Longrightarrow>chain(D,M`x)"
      and yprem: "\<And>y. y \<in> nat\<Longrightarrow>chain(D,\<lambda>x \<in> nat. M`x`y)"
      and Mfun:  "M \<in> nat->nat->set(D)"
      and cpoD:  "cpo(D)"
  shows "matrix(D,M)"
proof -
  have rel_succ: "rel(D, M ` n ` m, M ` succ(n) ` m)"
    if "n \<in> nat" "m \<in> nat" for n m
    using chain_rel [OF yprem] and that by simp
  show "matrix(D,M)"
  proof (simp add: matrix_def Mfun rel_succ, intro conjI ballI)
    fix n m assume n: "n \<in> nat" and m: "m \<in> nat"
    thus "rel(D, M ` n ` m, M ` n ` succ(m))"
      by (simp add: chain_rel xprem)
  next
    fix n m assume n: "n \<in> nat" and m: "m \<in> nat"
    thus "rel(D, M ` n ` m, M ` succ(n) ` succ(m))"
      by (rule cpo_trans [OF cpoD rel_succ],
          simp_all add: chain_fun [THEN apply_type] xprem)
  qed
qed

lemma lemma2:
     "\<lbrakk>x \<in> nat; m \<in> nat; rel(D,(\<lambda>n \<in> nat. M`n`m1)`x,(\<lambda>n \<in> nat. M`n`m1)`m)\<rbrakk>
      \<Longrightarrow> rel(D,M`x`m1,M`m`m1)"
by simp

lemma isub_lemma:
    "\<lbrakk>isub(D, \<lambda>n \<in> nat. M`n`n, y); matrix(D,M); cpo(D)\<rbrakk>
     \<Longrightarrow> isub(D, \<lambda>n \<in> nat. lub(D,\<lambda>m \<in> nat. M`n`m), y)"
proof (simp add: isub_def, safe)
  fix n
  assume DM: "matrix(D, M)" and D: "cpo(D)" and n: "n \<in> nat" and y: "y \<in> set(D)"
     and rel: "\<forall>n\<in>nat. rel(D, M ` n ` n, y)"
  have "rel(D, lub(D, M ` n), y)"
  proof (rule matrix_chain_left [THEN cpo_lub, THEN islub_least], simp_all add: n D DM)
    show "isub(D, M ` n, y)"
      proof (unfold isub_def, intro conjI ballI y)
        fix k assume k: "k \<in> nat"
        show "rel(D, M ` n ` k, y)"
          proof (cases "n \<le> k")
            case True
            hence yy: "rel(D, M`n`k, M`k`k)"
              by (blast intro: lemma2 n k y DM D chain_rel_gen matrix_chain_right)
            show "?thesis"
              by (rule cpo_trans [OF D yy],
                  simp_all add: k rel n y DM matrix_in)
          next
            case False
            hence le: "k \<le> n"
              by (blast intro: not_le_iff_lt [THEN iffD1, THEN leI] nat_into_Ord n k)
            show "?thesis"
              by (rule cpo_trans [OF D chain_rel_gen [OF le]],
                  simp_all add: n y k rel DM D matrix_chain_left)
          qed
        qed
  qed
  moreover
  have "M ` n \<in> nat \<rightarrow> set(D)" by (blast intro: DM n matrix_fun [THEN apply_type])
  ultimately show "rel(D, lub(D, Lambda(nat, (`)(M ` n))), y)"  by simp
qed

lemma matrix_chain_lub:
    "\<lbrakk>matrix(D,M); cpo(D)\<rbrakk> \<Longrightarrow> chain(D,\<lambda>n \<in> nat. lub(D,\<lambda>m \<in> nat. M`n`m))"
proof (simp add: chain_def, intro conjI ballI)
  assume "matrix(D, M)" "cpo(D)"
  thus "(\<lambda>x\<in>nat. lub(D, Lambda(nat, (`)(M ` x)))) \<in> nat \<rightarrow> set(D)"
    by (force intro: islub_in cpo_lub chainI lam_type matrix_in matrix_rel_0_1)
next
  fix n
  assume DD: "matrix(D, M)" "cpo(D)" "n \<in> nat"
  hence "dominate(D, M ` n, M ` succ(n))"
    by (force simp add: dominate_def intro: matrix_rel_1_0)
  with DD show "rel(D, lub(D, Lambda(nat, (`)(M ` n))),
               lub(D, Lambda(nat, (`)(M ` succ(n)))))"
    by (simp add: matrix_chain_left [THEN chain_fun, THEN eta]
      dominate_islub cpo_lub matrix_chain_left chain_fun)
qed

lemma isub_eq:
  assumes DM: "matrix(D, M)" and D: "cpo(D)"
  shows "isub(D,(\<lambda>n \<in> nat. lub(D,\<lambda>m \<in> nat. M`n`m)),y) \<longleftrightarrow> isub(D,(\<lambda>n \<in> nat. M`n`n),y)"
proof
  assume isub: "isub(D, \<lambda>n\<in>nat. lub(D, Lambda(nat, (`)(M ` n))), y)"
  hence dom: "dominate(D, \<lambda>n\<in>nat. M ` n ` n, \<lambda>n\<in>nat. lub(D, Lambda(nat, (`)(M ` n))))"
    using DM D
    by (simp add: dominate_def, intro ballI bexI,
        simp_all add: matrix_chain_left [THEN chain_fun, THEN eta] islub_ub cpo_lub matrix_chain_left)
  thus "isub(D, \<lambda>n\<in>nat. M ` n ` n, y)" using DM D
    by - (rule dominate_isub [OF dom isub],
          simp_all add: matrix_chain_diag chain_fun matrix_chain_lub)
next
  assume isub: "isub(D, \<lambda>n\<in>nat. M ` n ` n, y)"
  thus "isub(D, \<lambda>n\<in>nat. lub(D, Lambda(nat, (`)(M ` n))), y)"  using DM D
    by (simp add: isub_lemma)
qed

lemma lub_matrix_diag_aux1:
    "lub(D,(\<lambda>n \<in> nat. lub(D,\<lambda>m \<in> nat. M`n`m))) =
     (THE x. islub(D, (\<lambda>n \<in> nat. lub(D,\<lambda>m \<in> nat. M`n`m)), x))"
by (simp add: lub_def)

lemma lub_matrix_diag_aux2:
    "lub(D,(\<lambda>n \<in> nat. M`n`n)) =
     (THE x. islub(D, (\<lambda>n \<in> nat. M`n`n), x))"
by (simp add: lub_def)

lemma lub_matrix_diag:
    "\<lbrakk>matrix(D,M); cpo(D)\<rbrakk>
     \<Longrightarrow> lub(D,(\<lambda>n \<in> nat. lub(D,\<lambda>m \<in> nat. M`n`m))) =
         lub(D,(\<lambda>n \<in> nat. M`n`n))"
apply (simp (no_asm) add: lub_matrix_diag_aux1 lub_matrix_diag_aux2)
apply (simp add: islub_def isub_eq)
done

lemma lub_matrix_diag_sym:
    "\<lbrakk>matrix(D,M); cpo(D)\<rbrakk>
     \<Longrightarrow> lub(D,(\<lambda>m \<in> nat. lub(D,\<lambda>n \<in> nat. M`n`m))) =
         lub(D,(\<lambda>n \<in> nat. M`n`n))"
by (drule matrix_sym_axis [THEN lub_matrix_diag], auto)

(*----------------------------------------------------------------------*)
(* I/E/D rules for mono and cont.                                       *)
(*----------------------------------------------------------------------*)

lemma monoI:
    "\<lbrakk>f \<in> set(D)->set(E);
       \<And>x y. \<lbrakk>rel(D,x,y); x \<in> set(D); y \<in> set(D)\<rbrakk> \<Longrightarrow> rel(E,f`x,f`y)\<rbrakk>
     \<Longrightarrow> f \<in> mono(D,E)"
by (simp add: mono_def)

lemma mono_fun: "f \<in> mono(D,E) \<Longrightarrow> f \<in> set(D)->set(E)"
by (simp add: mono_def)

lemma mono_map: "\<lbrakk>f \<in> mono(D,E); x \<in> set(D)\<rbrakk> \<Longrightarrow> f`x \<in> set(E)"
by (blast intro!: mono_fun [THEN apply_type])

lemma mono_mono:
    "\<lbrakk>f \<in> mono(D,E); rel(D,x,y); x \<in> set(D); y \<in> set(D)\<rbrakk> \<Longrightarrow> rel(E,f`x,f`y)"
by (simp add: mono_def)

lemma contI:
    "\<lbrakk>f \<in> set(D)->set(E);
       \<And>x y. \<lbrakk>rel(D,x,y); x \<in> set(D); y \<in> set(D)\<rbrakk> \<Longrightarrow> rel(E,f`x,f`y);
       \<And>X. chain(D,X) \<Longrightarrow> f`lub(D,X) = lub(E,\<lambda>n \<in> nat. f`(X`n))\<rbrakk>
     \<Longrightarrow> f \<in> cont(D,E)"
by (simp add: cont_def mono_def)

lemma cont2mono: "f \<in> cont(D,E) \<Longrightarrow> f \<in> mono(D,E)"
by (simp add: cont_def)

lemma cont_fun [TC]: "f \<in> cont(D,E) \<Longrightarrow> f \<in> set(D)->set(E)"
apply (simp add: cont_def)
apply (rule mono_fun, blast)
done

lemma cont_map [TC]: "\<lbrakk>f \<in> cont(D,E); x \<in> set(D)\<rbrakk> \<Longrightarrow> f`x \<in> set(E)"
by (blast intro!: cont_fun [THEN apply_type])

declare comp_fun [TC]

lemma cont_mono:
    "\<lbrakk>f \<in> cont(D,E); rel(D,x,y); x \<in> set(D); y \<in> set(D)\<rbrakk> \<Longrightarrow> rel(E,f`x,f`y)"
apply (simp add: cont_def)
apply (blast intro!: mono_mono)
done

lemma cont_lub:
   "\<lbrakk>f \<in> cont(D,E); chain(D,X)\<rbrakk> \<Longrightarrow> f`(lub(D,X)) = lub(E,\<lambda>n \<in> nat. f`(X`n))"
by (simp add: cont_def)

(*----------------------------------------------------------------------*)
(* Continuity and chains.                                               *)
(*----------------------------------------------------------------------*)

lemma mono_chain:
     "\<lbrakk>f \<in> mono(D,E); chain(D,X)\<rbrakk> \<Longrightarrow> chain(E,\<lambda>n \<in> nat. f`(X`n))"
apply (simp (no_asm) add: chain_def)
apply (blast intro: lam_type mono_map chain_in mono_mono chain_rel)
done

lemma cont_chain:
     "\<lbrakk>f \<in> cont(D,E); chain(D,X)\<rbrakk> \<Longrightarrow> chain(E,\<lambda>n \<in> nat. f`(X`n))"
by (blast intro: mono_chain cont2mono)

(*----------------------------------------------------------------------*)
(* I/E/D rules about (set+rel) cf, the continuous function space.       *)
(*----------------------------------------------------------------------*)

(* The following development more difficult with cpo-as-relation approach. *)

lemma cf_cont: "f \<in> set(cf(D,E)) \<Longrightarrow> f \<in> cont(D,E)"
by (simp add: set_def cf_def)

lemma cont_cf: (* Non-trivial with relation *)
    "f \<in> cont(D,E) \<Longrightarrow> f \<in> set(cf(D,E))"
by (simp add: set_def cf_def)

(* rel_cf originally an equality. Now stated as two rules. Seemed easiest. *)

lemma rel_cfI:
    "\<lbrakk>\<And>x. x \<in> set(D) \<Longrightarrow> rel(E,f`x,g`x); f \<in> cont(D,E); g \<in> cont(D,E)\<rbrakk>
     \<Longrightarrow> rel(cf(D,E),f,g)"
by (simp add: rel_I cf_def)

lemma rel_cf: "\<lbrakk>rel(cf(D,E),f,g); x \<in> set(D)\<rbrakk> \<Longrightarrow> rel(E,f`x,g`x)"
by (simp add: rel_def cf_def)

(*----------------------------------------------------------------------*)
(* Theorems about the continuous function space.                        *)
(*----------------------------------------------------------------------*)

lemma chain_cf:
    "\<lbrakk>chain(cf(D,E),X); x \<in> set(D)\<rbrakk> \<Longrightarrow> chain(E,\<lambda>n \<in> nat. X`n`x)"
apply (rule chainI)
apply (blast intro: lam_type apply_funtype cont_fun cf_cont chain_in, simp)
apply (blast intro: rel_cf chain_rel)
done

lemma matrix_lemma:
    "\<lbrakk>chain(cf(D,E),X); chain(D,Xa); cpo(D); cpo(E)\<rbrakk>
     \<Longrightarrow> matrix(E,\<lambda>x \<in> nat. \<lambda>xa \<in> nat. X`x`(Xa`xa))"
apply (rule matrix_chainI, auto)
apply (force intro: chainI lam_type apply_funtype cont_fun cf_cont cont_mono)
apply (force intro: chainI lam_type apply_funtype cont_fun cf_cont rel_cf)
apply (blast intro: lam_type apply_funtype cont_fun cf_cont chain_in)
done

lemma chain_cf_lub_cont:
  assumes ch: "chain(cf(D,E),X)" and D: "cpo(D)" and E: "cpo(E)"
  shows   "(\<lambda>x \<in> set(D). lub(E, \<lambda>n \<in> nat. X ` n ` x)) \<in> cont(D, E)"
proof (rule contI)
  show "(\<lambda>x\<in>set(D). lub(E, \<lambda>n\<in>nat. X ` n ` x)) \<in> set(D) \<rightarrow> set(E)"
    by (blast intro: lam_type chain_cf [THEN cpo_lub, THEN islub_in] ch E)
next
  fix x y
  assume xy: "rel(D, x, y)" "x \<in> set(D)" "y \<in> set(D)"
  hence dom: "dominate(E, \<lambda>n\<in>nat. X ` n ` x, \<lambda>n\<in>nat. X ` n ` y)"
    by (force intro: dominateI  chain_in [OF ch, THEN cf_cont, THEN cont_mono])
  note chE = chain_cf [OF ch]
  from xy show "rel(E, (\<lambda>x\<in>set(D). lub(E, \<lambda>n\<in>nat. X ` n ` x)) ` x,
                       (\<lambda>x\<in>set(D). lub(E, \<lambda>n\<in>nat. X ` n ` x)) ` y)"
    by (simp add: dominate_islub [OF dom] cpo_lub [OF chE] E chain_fun [OF chE])
next
  fix Y
  assume chDY: "chain(D,Y)"
  have "lub(E, \<lambda>x\<in>nat. lub(E, \<lambda>y\<in>nat. X ` x ` (Y ` y))) =
        lub(E, \<lambda>x\<in>nat. X ` x ` (Y ` x))"
    using matrix_lemma [THEN lub_matrix_diag, OF ch chDY]
    by (simp add: D E)
   also have "... =  lub(E, \<lambda>x\<in>nat. lub(E, \<lambda>n\<in>nat. X ` n ` (Y ` x)))"
    using  matrix_lemma [THEN lub_matrix_diag_sym, OF ch chDY]
    by (simp add: D E)
  finally have "lub(E, \<lambda>x\<in>nat. lub(E, \<lambda>n\<in>nat. X ` x ` (Y ` n))) =
                lub(E, \<lambda>x\<in>nat. lub(E, \<lambda>n\<in>nat. X ` n ` (Y ` x)))" .
  thus "(\<lambda>x\<in>set(D). lub(E, \<lambda>n\<in>nat. X ` n ` x)) ` lub(D, Y) =
        lub(E, \<lambda>n\<in>nat. (\<lambda>x\<in>set(D). lub(E, \<lambda>n\<in>nat. X ` n ` x)) ` (Y ` n))"
    by (simp add: cpo_lub [THEN islub_in]  D chDY
                  chain_in [THEN cf_cont, THEN cont_lub, OF ch])
  qed

lemma islub_cf:
    "\<lbrakk>chain(cf(D,E),X); cpo(D); cpo(E)\<rbrakk>
     \<Longrightarrow> islub(cf(D,E), X, \<lambda>x \<in> set(D). lub(E,\<lambda>n \<in> nat. X`n`x))"
apply (rule islubI)
apply (rule isubI)
apply (rule chain_cf_lub_cont [THEN cont_cf], assumption+)
apply (rule rel_cfI)
apply (force dest!: chain_cf [THEN cpo_lub, THEN islub_ub])
apply (blast intro: cf_cont chain_in)
apply (blast intro: cont_cf chain_cf_lub_cont)
apply (rule rel_cfI, simp)
apply (force intro: chain_cf [THEN cpo_lub, THEN islub_least]
                   cf_cont [THEN cont_fun, THEN apply_type] isubI
            elim: isubD2 [THEN rel_cf] isubD1)
apply (blast intro: chain_cf_lub_cont isubD1 cf_cont)+
done

lemma cpo_cf [TC]:
    "\<lbrakk>cpo(D); cpo(E)\<rbrakk> \<Longrightarrow> cpo(cf(D,E))"
apply (rule poI [THEN cpoI])
apply (rule rel_cfI)
apply (assumption | rule cpo_refl cf_cont [THEN cont_fun, THEN apply_type]
                         cf_cont)+
apply (rule rel_cfI)
apply (rule cpo_trans, assumption)
apply (erule rel_cf, assumption)
apply (rule rel_cf, assumption)
apply (assumption | rule cf_cont [THEN cont_fun, THEN apply_type] cf_cont)+
apply (rule fun_extension)
apply (assumption | rule cf_cont [THEN cont_fun])+
apply (blast intro: cpo_antisym rel_cf
                    cf_cont [THEN cont_fun, THEN apply_type])
apply (fast intro: islub_cf)
done

lemma lub_cf:
     "\<lbrakk>chain(cf(D,E),X); cpo(D); cpo(E)\<rbrakk>
      \<Longrightarrow> lub(cf(D,E), X) = (\<lambda>x \<in> set(D). lub(E,\<lambda>n \<in> nat. X`n`x))"
by (blast intro: islub_unique cpo_lub islub_cf cpo_cf)


lemma const_cont [TC]:
     "\<lbrakk>y \<in> set(E); cpo(D); cpo(E)\<rbrakk> \<Longrightarrow> (\<lambda>x \<in> set(D).y) \<in> cont(D,E)"
apply (rule contI)
prefer 2 apply simp
apply (blast intro: lam_type)
apply (simp add: chain_in cpo_lub [THEN islub_in] lub_const)
done

lemma cf_least:
    "\<lbrakk>cpo(D); pcpo(E); y \<in> cont(D,E)\<rbrakk>\<Longrightarrow>rel(cf(D,E),(\<lambda>x \<in> set(D).bot(E)),y)"
apply (rule rel_cfI, simp, typecheck)
done

lemma pcpo_cf:
    "\<lbrakk>cpo(D); pcpo(E)\<rbrakk> \<Longrightarrow> pcpo(cf(D,E))"
apply (rule pcpoI)
apply (assumption |
       rule cf_least bot_in const_cont [THEN cont_cf] cf_cont cpo_cf pcpo_cpo)+
done

lemma bot_cf:
    "\<lbrakk>cpo(D); pcpo(E)\<rbrakk> \<Longrightarrow> bot(cf(D,E)) = (\<lambda>x \<in> set(D).bot(E))"
by (blast intro: bot_unique [symmetric] pcpo_cf cf_least
                 bot_in [THEN const_cont, THEN cont_cf] cf_cont pcpo_cpo)

(*----------------------------------------------------------------------*)
(* Identity and composition.                                            *)
(*----------------------------------------------------------------------*)

lemma id_cont [TC,intro!]:
    "cpo(D) \<Longrightarrow> id(set(D)) \<in> cont(D,D)"
by (simp add: id_type contI cpo_lub [THEN islub_in] chain_fun [THEN eta])

lemmas comp_cont_apply =  cont_fun [THEN comp_fun_apply]

lemma comp_pres_cont [TC]:
    "\<lbrakk>f \<in> cont(D',E); g \<in> cont(D,D'); cpo(D)\<rbrakk> \<Longrightarrow> f O g \<in> cont(D,E)"
apply (rule contI)
apply (rule_tac [2] comp_cont_apply [THEN ssubst])
apply (rule_tac [4] comp_cont_apply [THEN ssubst])
apply (rule_tac [6] cont_mono)
apply (rule_tac [7] cont_mono) (* 13 subgoals *)
apply typecheck (* proves all but the lub case *)
apply (subst comp_cont_apply)
apply (rule_tac [3] cont_lub [THEN ssubst])
apply (rule_tac [5] cont_lub [THEN ssubst])
prefer 7 apply (simp add: comp_cont_apply chain_in)
apply (auto intro: cpo_lub [THEN islub_in] cont_chain)
done


lemma comp_mono:
    "\<lbrakk>f \<in> cont(D',E); g \<in> cont(D,D'); f':cont(D',E); g':cont(D,D');
        rel(cf(D',E),f,f'); rel(cf(D,D'),g,g'); cpo(D); cpo(E)\<rbrakk>
     \<Longrightarrow> rel(cf(D,E),f O g,f' O g')"
apply (rule rel_cfI)
apply (subst comp_cont_apply)
apply (rule_tac [3] comp_cont_apply [THEN ssubst])
apply (rule_tac [5] cpo_trans)
apply (assumption | rule rel_cf cont_mono cont_map comp_pres_cont)+
done

lemma chain_cf_comp:
    "\<lbrakk>chain(cf(D',E),X); chain(cf(D,D'),Y); cpo(D); cpo(E)\<rbrakk>
     \<Longrightarrow> chain(cf(D,E),\<lambda>n \<in> nat. X`n O Y`n)"
apply (rule chainI)
defer 1
apply simp
apply (rule rel_cfI)
apply (rule comp_cont_apply [THEN ssubst])
apply (rule_tac [3] comp_cont_apply [THEN ssubst])
apply (rule_tac [5] cpo_trans)
apply (rule_tac [6] rel_cf)
apply (rule_tac [8] cont_mono)
apply (blast intro: lam_type comp_pres_cont cont_cf chain_in [THEN cf_cont]
                    cont_map chain_rel rel_cf)+
done

lemma comp_lubs:
    "\<lbrakk>chain(cf(D',E),X); chain(cf(D,D'),Y); cpo(D); cpo(D'); cpo(E)\<rbrakk>
     \<Longrightarrow> lub(cf(D',E),X) O lub(cf(D,D'),Y) = lub(cf(D,E),\<lambda>n \<in> nat. X`n O Y`n)"
apply (rule fun_extension)
apply (rule_tac [3] lub_cf [THEN ssubst])
apply (assumption |
       rule comp_fun cf_cont [THEN cont_fun]  cpo_lub [THEN islub_in]
            cpo_cf chain_cf_comp)+
apply (simp add: chain_in [THEN cf_cont, THEN comp_cont_apply])
apply (subst comp_cont_apply)
apply (assumption | rule cpo_lub [THEN islub_in, THEN cf_cont]  cpo_cf)+
apply (simp add: lub_cf chain_cf chain_in [THEN cf_cont, THEN cont_lub]
                 chain_cf [THEN cpo_lub, THEN islub_in])
apply (cut_tac M = "\<lambda>xa \<in> nat. \<lambda>xb \<in> nat. X`xa` (Y`xb`x)" in lub_matrix_diag)
prefer 3 apply simp
apply (rule matrix_chainI, simp_all)
apply (drule chain_in [THEN cf_cont], assumption)
apply (force dest: cont_chain [OF _ chain_cf])
apply (rule chain_cf)
apply (assumption |
       rule cont_fun [THEN apply_type] chain_in [THEN cf_cont] lam_type)+
done

(*----------------------------------------------------------------------*)
(* Theorems about projpair.                                             *)
(*----------------------------------------------------------------------*)

lemma projpairI:
    "\<lbrakk>e \<in> cont(D,E); p \<in> cont(E,D); p O e = id(set(D));
        rel(cf(E,E))(e O p)(id(set(E)))\<rbrakk> \<Longrightarrow> projpair(D,E,e,p)"
by (simp add: projpair_def)

lemma projpair_e_cont: "projpair(D,E,e,p) \<Longrightarrow> e \<in> cont(D,E)"
by (simp add: projpair_def)

lemma projpair_p_cont: "projpair(D,E,e,p) \<Longrightarrow> p \<in> cont(E,D)"
by (simp add: projpair_def)

lemma projpair_ep_cont: "projpair(D,E,e,p) \<Longrightarrow> e \<in> cont(D,E) \<and> p \<in> cont(E,D)"
by (simp add: projpair_def)

lemma projpair_eq: "projpair(D,E,e,p) \<Longrightarrow> p O e = id(set(D))"
by (simp add: projpair_def)

lemma projpair_rel: "projpair(D,E,e,p) \<Longrightarrow> rel(cf(E,E))(e O p)(id(set(E)))"
by (simp add: projpair_def)


(*----------------------------------------------------------------------*)
(* NB! projpair_e_cont and projpair_p_cont cannot be used repeatedly    *)
(*   at the same time since both match a goal of the form f \<in> cont(X,Y).*)
(*----------------------------------------------------------------------*)

(*----------------------------------------------------------------------*)
(* Uniqueness of embedding projection pairs.                            *)
(*----------------------------------------------------------------------*)

lemmas id_comp = fun_is_rel [THEN left_comp_id]
and    comp_id = fun_is_rel [THEN right_comp_id]

lemma projpair_unique_aux1:
    "\<lbrakk>cpo(D); cpo(E); projpair(D,E,e,p); projpair(D,E,e',p');
       rel(cf(D,E),e,e')\<rbrakk> \<Longrightarrow> rel(cf(E,D),p',p)"
apply (rule_tac b=p' in
       projpair_p_cont [THEN cont_fun, THEN id_comp, THEN subst], assumption)
apply (rule projpair_eq [THEN subst], assumption)
apply (rule cpo_trans)
apply (assumption | rule cpo_cf)+
(* The following corresponds to EXISTS_TAC, non-trivial instantiation. *)
apply (rule_tac [4] f = "p O (e' O p')" in cont_cf)
apply (subst comp_assoc)
apply (blast intro:  cpo_cf cont_cf comp_mono comp_pres_cont
             dest: projpair_ep_cont)
apply (rule_tac P = "\<lambda>x. rel (cf (E,D),p O e' O p',x)"
         in projpair_p_cont [THEN cont_fun, THEN comp_id, THEN subst],
       assumption)
apply (rule comp_mono)
apply (blast intro: cpo_cf cont_cf comp_pres_cont projpair_rel
             dest: projpair_ep_cont)+
done

text\<open>Proof's very like the previous one.  Is there a pattern that
      could be exploited?\<close>
lemma projpair_unique_aux2:
    "\<lbrakk>cpo(D); cpo(E); projpair(D,E,e,p); projpair(D,E,e',p');
       rel(cf(E,D),p',p)\<rbrakk> \<Longrightarrow> rel(cf(D,E),e,e')"
apply (rule_tac b=e
         in projpair_e_cont [THEN cont_fun, THEN comp_id, THEN subst],
       assumption)
apply (rule_tac e1=e' in projpair_eq [THEN subst], assumption)
apply (rule cpo_trans)
apply (assumption | rule cpo_cf)+
apply (rule_tac [4] f = "(e O p) O e'" in cont_cf)
apply (subst comp_assoc)
apply (blast intro:  cpo_cf cont_cf comp_mono comp_pres_cont
             dest: projpair_ep_cont)
apply (rule_tac P = "\<lambda>x. rel (cf (D,E), (e O p) O e',x)"
         in projpair_e_cont [THEN cont_fun, THEN id_comp, THEN subst],
       assumption)
apply (blast intro: cpo_cf cont_cf comp_pres_cont projpair_rel comp_mono
             dest: projpair_ep_cont)+
done


lemma projpair_unique:
    "\<lbrakk>cpo(D); cpo(E); projpair(D,E,e,p); projpair(D,E,e',p')\<rbrakk>
     \<Longrightarrow> (e=e')\<longleftrightarrow>(p=p')"
by (blast intro: cpo_antisym projpair_unique_aux1 projpair_unique_aux2 cpo_cf cont_cf
          dest: projpair_ep_cont)

(* Slightly different, more asms, since THE chooses the unique element. *)

lemma embRp:
    "\<lbrakk>emb(D,E,e); cpo(D); cpo(E)\<rbrakk> \<Longrightarrow> projpair(D,E,e,Rp(D,E,e))"
apply (simp add: emb_def Rp_def)
apply (blast intro: theI2 projpair_unique [THEN iffD1])
done

lemma embI: "projpair(D,E,e,p) \<Longrightarrow> emb(D,E,e)"
by (simp add: emb_def, auto)

lemma Rp_unique: "\<lbrakk>projpair(D,E,e,p); cpo(D); cpo(E)\<rbrakk> \<Longrightarrow> Rp(D,E,e) = p"
by (blast intro: embRp embI projpair_unique [THEN iffD1])

lemma emb_cont [TC]: "emb(D,E,e) \<Longrightarrow> e \<in> cont(D,E)"
apply (simp add: emb_def)
apply (blast intro: projpair_e_cont)
done

(* The following three theorems have cpo asms due to THE (uniqueness). *)

lemmas Rp_cont [TC] = embRp [THEN projpair_p_cont]
lemmas embRp_eq = embRp [THEN projpair_eq]
lemmas embRp_rel = embRp [THEN projpair_rel]


lemma embRp_eq_thm:
    "\<lbrakk>emb(D,E,e); x \<in> set(D); cpo(D); cpo(E)\<rbrakk> \<Longrightarrow> Rp(D,E,e)`(e`x) = x"
apply (rule comp_fun_apply [THEN subst])
apply (assumption | rule Rp_cont emb_cont cont_fun)+
apply (subst embRp_eq)
apply (auto intro: id_conv)
done


(*----------------------------------------------------------------------*)
(* The identity embedding.                                              *)
(*----------------------------------------------------------------------*)

lemma projpair_id:
    "cpo(D) \<Longrightarrow> projpair(D,D,id(set(D)),id(set(D)))"
apply (simp add: projpair_def)
apply (blast intro: cpo_cf cont_cf)
done

lemma emb_id:
    "cpo(D) \<Longrightarrow> emb(D,D,id(set(D)))"
by (auto intro: embI projpair_id)

lemma Rp_id:
    "cpo(D) \<Longrightarrow> Rp(D,D,id(set(D))) = id(set(D))"
by (auto intro: Rp_unique projpair_id)


(*----------------------------------------------------------------------*)
(* Composition preserves embeddings.                                    *)
(*----------------------------------------------------------------------*)

(* Considerably shorter, only partly due to a simpler comp_assoc. *)
(* Proof in HOL-ST: 70 lines (minus 14 due to comp_assoc complication). *)
(* Proof in Isa/ZF: 23 lines (compared to 56: 60% reduction). *)

lemma comp_lemma:
    "\<lbrakk>emb(D,D',e); emb(D',E,e'); cpo(D); cpo(D'); cpo(E)\<rbrakk>
     \<Longrightarrow> projpair(D,E,e' O e,(Rp(D,D',e)) O (Rp(D',E,e')))"
apply (simp add: projpair_def, safe)
apply (assumption | rule comp_pres_cont Rp_cont emb_cont)+
apply (rule comp_assoc [THEN subst])
apply (rule_tac t1 = e' in comp_assoc [THEN ssubst])
apply (subst embRp_eq) (* Matches everything due to subst/ssubst. *)
apply assumption+
apply (subst comp_id)
apply (assumption | rule cont_fun Rp_cont embRp_eq)+
apply (rule comp_assoc [THEN subst])
apply (rule_tac t1 = "Rp (D,D',e)" in comp_assoc [THEN ssubst])
apply (rule cpo_trans)
apply (assumption | rule cpo_cf)+
apply (rule comp_mono)
apply (rule_tac [6] cpo_refl)
apply (erule_tac [7] asm_rl | rule_tac [7] cont_cf Rp_cont)+
prefer 6 apply (blast intro: cpo_cf)
apply (rule_tac [5] comp_mono)
apply (rule_tac [10] embRp_rel)
apply (rule_tac [9] cpo_cf [THEN cpo_refl])
apply (simp_all add: comp_id embRp_rel comp_pres_cont Rp_cont
                     id_cont emb_cont cont_fun cont_cf)
done

(* The use of THEN is great in places like the following, both ugly in HOL. *)

lemmas emb_comp = comp_lemma [THEN embI]
lemmas Rp_comp = comp_lemma [THEN Rp_unique]

(*----------------------------------------------------------------------*)
(* Infinite cartesian product.                                          *)
(*----------------------------------------------------------------------*)

lemma iprodI:
    "x:(\<Prod>n \<in> nat. set(DD`n)) \<Longrightarrow> x \<in> set(iprod(DD))"
by (simp add: set_def iprod_def)

lemma iprodE:
    "x \<in> set(iprod(DD)) \<Longrightarrow> x:(\<Prod>n \<in> nat. set(DD`n))"
by (simp add: set_def iprod_def)

(* Contains typing conditions in contrast to HOL-ST *)

lemma rel_iprodI:
    "\<lbrakk>\<And>n. n \<in> nat \<Longrightarrow> rel(DD`n,f`n,g`n); f:(\<Prod>n \<in> nat. set(DD`n));
       g:(\<Prod>n \<in> nat. set(DD`n))\<rbrakk> \<Longrightarrow> rel(iprod(DD),f,g)"
by (simp add: iprod_def rel_I)

lemma rel_iprodE:
    "\<lbrakk>rel(iprod(DD),f,g); n \<in> nat\<rbrakk> \<Longrightarrow> rel(DD`n,f`n,g`n)"
by (simp add: iprod_def rel_def)

lemma chain_iprod:
    "\<lbrakk>chain(iprod(DD),X);  \<And>n. n \<in> nat \<Longrightarrow> cpo(DD`n); n \<in> nat\<rbrakk>
     \<Longrightarrow> chain(DD`n,\<lambda>m \<in> nat. X`m`n)"
apply (unfold chain_def, safe)
apply (rule lam_type)
apply (rule apply_type)
apply (rule iprodE)
apply (blast intro: apply_funtype, assumption)
apply (simp add: rel_iprodE)
done

lemma islub_iprod:
    "\<lbrakk>chain(iprod(DD),X);  \<And>n. n \<in> nat \<Longrightarrow> cpo(DD`n)\<rbrakk>
     \<Longrightarrow> islub(iprod(DD),X,\<lambda>n \<in> nat. lub(DD`n,\<lambda>m \<in> nat. X`m`n))"
apply (simp add: islub_def isub_def, safe)
apply (rule iprodI)
apply (blast intro: lam_type chain_iprod [THEN cpo_lub, THEN islub_in])
apply (rule rel_iprodI, simp)
(*looks like something should be inserted into the assumptions!*)
apply (rule_tac P = "\<lambda>t. rel (DD`na,t,lub (DD`na,\<lambda>x \<in> nat. X`x`na))"
            and b1 = "\<lambda>n. X`n`na" in beta [THEN subst])
apply (simp del: beta_if
            add: chain_iprod [THEN cpo_lub, THEN islub_ub] iprodE
                chain_in)+
apply (blast intro: iprodI lam_type chain_iprod [THEN cpo_lub, THEN islub_in])
apply (rule rel_iprodI)
apply (simp | rule islub_least chain_iprod [THEN cpo_lub])+
apply (simp add: isub_def, safe)
apply (erule iprodE [THEN apply_type])
apply (simp_all add: rel_iprodE lam_type iprodE
                     chain_iprod [THEN cpo_lub, THEN islub_in])
done

lemma cpo_iprod [TC]:
    "(\<And>n. n \<in> nat \<Longrightarrow> cpo(DD`n)) \<Longrightarrow> cpo(iprod(DD))"
apply (assumption | rule cpoI poI)+
apply (rule rel_iprodI) (*not repeated: want to solve 1, leave 2 unchanged *)
apply (simp | rule cpo_refl iprodE [THEN apply_type] iprodE)+
apply (rule rel_iprodI)
apply (drule rel_iprodE)
apply (drule_tac [2] rel_iprodE)
apply (simp | rule cpo_trans iprodE [THEN apply_type] iprodE)+
apply (rule fun_extension)
apply (blast intro: iprodE)
apply (blast intro: iprodE)
apply (blast intro: cpo_antisym rel_iprodE iprodE [THEN apply_type])+
apply (auto intro: islub_iprod)
done


lemma lub_iprod:
    "\<lbrakk>chain(iprod(DD),X);  \<And>n. n \<in> nat \<Longrightarrow> cpo(DD`n)\<rbrakk>
     \<Longrightarrow> lub(iprod(DD),X) = (\<lambda>n \<in> nat. lub(DD`n,\<lambda>m \<in> nat. X`m`n))"
by (blast intro: cpo_lub [THEN islub_unique] islub_iprod cpo_iprod)


(*----------------------------------------------------------------------*)
(* The notion of subcpo.                                                *)
(*----------------------------------------------------------------------*)

lemma subcpoI:
    "\<lbrakk>set(D)<=set(E);
       \<And>x y. \<lbrakk>x \<in> set(D); y \<in> set(D)\<rbrakk> \<Longrightarrow> rel(D,x,y)\<longleftrightarrow>rel(E,x,y);
       \<And>X. chain(D,X) \<Longrightarrow> lub(E,X) \<in> set(D)\<rbrakk> \<Longrightarrow> subcpo(D,E)"
by (simp add: subcpo_def)

lemma subcpo_subset: "subcpo(D,E) \<Longrightarrow> set(D)<=set(E)"
by (simp add: subcpo_def)

lemma subcpo_rel_eq:
    "\<lbrakk>subcpo(D,E); x \<in> set(D); y \<in> set(D)\<rbrakk> \<Longrightarrow> rel(D,x,y)\<longleftrightarrow>rel(E,x,y)"
by (simp add: subcpo_def)

lemmas subcpo_relD1 = subcpo_rel_eq [THEN iffD1]
lemmas subcpo_relD2 = subcpo_rel_eq [THEN iffD2]

lemma subcpo_lub: "\<lbrakk>subcpo(D,E); chain(D,X)\<rbrakk> \<Longrightarrow> lub(E,X) \<in> set(D)"
by (simp add: subcpo_def)

lemma chain_subcpo: "\<lbrakk>subcpo(D,E); chain(D,X)\<rbrakk> \<Longrightarrow> chain(E,X)"
by (blast intro: Pi_type [THEN chainI] chain_fun subcpo_relD1
                    subcpo_subset [THEN subsetD]
                    chain_in chain_rel)

lemma ub_subcpo: "\<lbrakk>subcpo(D,E); chain(D,X); isub(D,X,x)\<rbrakk> \<Longrightarrow> isub(E,X,x)"
by (blast intro: isubI subcpo_relD1 subcpo_relD1 chain_in isubD1 isubD2
                    subcpo_subset [THEN subsetD] chain_in chain_rel)

lemma islub_subcpo:
     "\<lbrakk>subcpo(D,E); cpo(E); chain(D,X)\<rbrakk> \<Longrightarrow> islub(D,X,lub(E,X))"
by (blast intro: islubI isubI subcpo_lub subcpo_relD2 chain_in islub_ub
                 islub_least cpo_lub chain_subcpo isubD1 ub_subcpo)

lemma subcpo_cpo: "\<lbrakk>subcpo(D,E); cpo(E)\<rbrakk> \<Longrightarrow> cpo(D)"
apply (assumption | rule cpoI poI)+
apply (simp add: subcpo_rel_eq)
apply (assumption | rule cpo_refl subcpo_subset [THEN subsetD])+
apply (simp add: subcpo_rel_eq)
apply (blast intro: subcpo_subset [THEN subsetD] cpo_trans)
apply (simp add: subcpo_rel_eq)
apply (blast intro: cpo_antisym subcpo_subset [THEN subsetD])
apply (fast intro: islub_subcpo)
done

lemma lub_subcpo: "\<lbrakk>subcpo(D,E); cpo(E); chain(D,X)\<rbrakk> \<Longrightarrow> lub(D,X) = lub(E,X)"
by (blast intro: cpo_lub [THEN islub_unique] islub_subcpo subcpo_cpo)

(*----------------------------------------------------------------------*)
(* Making subcpos using mkcpo.                                          *)
(*----------------------------------------------------------------------*)

lemma mkcpoI: "\<lbrakk>x \<in> set(D); P(x)\<rbrakk> \<Longrightarrow> x \<in> set(mkcpo(D,P))"
by (simp add: set_def mkcpo_def)

lemma mkcpoD1: "x \<in> set(mkcpo(D,P))\<Longrightarrow> x \<in> set(D)"
by (simp add: set_def mkcpo_def)

lemma mkcpoD2: "x \<in> set(mkcpo(D,P))\<Longrightarrow> P(x)"
by (simp add: set_def mkcpo_def)

lemma rel_mkcpoE: "rel(mkcpo(D,P),x,y) \<Longrightarrow> rel(D,x,y)"
by (simp add: rel_def mkcpo_def)

lemma rel_mkcpo:
    "\<lbrakk>x \<in> set(D); y \<in> set(D)\<rbrakk> \<Longrightarrow> rel(mkcpo(D,P),x,y) \<longleftrightarrow> rel(D,x,y)"
by (simp add: mkcpo_def rel_def set_def)

lemma chain_mkcpo:
    "chain(mkcpo(D,P),X) \<Longrightarrow> chain(D,X)"
apply (rule chainI)
apply (blast intro: Pi_type chain_fun chain_in [THEN mkcpoD1])
apply (blast intro: rel_mkcpo [THEN iffD1] chain_rel mkcpoD1 chain_in)
done

lemma subcpo_mkcpo:
     "\<lbrakk>\<And>X. chain(mkcpo(D,P),X) \<Longrightarrow> P(lub(D,X)); cpo(D)\<rbrakk>
      \<Longrightarrow> subcpo(mkcpo(D,P),D)"
apply (intro subcpoI subsetI rel_mkcpo)
apply (erule mkcpoD1)+
apply (blast intro: mkcpoI cpo_lub [THEN islub_in] chain_mkcpo)
done

(*----------------------------------------------------------------------*)
(* Embedding projection chains of cpos.                                 *)
(*----------------------------------------------------------------------*)

lemma emb_chainI:
    "\<lbrakk>\<And>n. n \<in> nat \<Longrightarrow> cpo(DD`n);
       \<And>n. n \<in> nat \<Longrightarrow> emb(DD`n,DD`succ(n),ee`n)\<rbrakk> \<Longrightarrow> emb_chain(DD,ee)"
by (simp add: emb_chain_def)

lemma emb_chain_cpo [TC]: "\<lbrakk>emb_chain(DD,ee); n \<in> nat\<rbrakk> \<Longrightarrow> cpo(DD`n)"
by (simp add: emb_chain_def)

lemma emb_chain_emb:
    "\<lbrakk>emb_chain(DD,ee); n \<in> nat\<rbrakk> \<Longrightarrow> emb(DD`n,DD`succ(n),ee`n)"
by (simp add: emb_chain_def)

(*----------------------------------------------------------------------*)
(* Dinf, the inverse Limit.                                             *)
(*----------------------------------------------------------------------*)

lemma DinfI:
    "\<lbrakk>x:(\<Prod>n \<in> nat. set(DD`n));
       \<And>n. n \<in> nat \<Longrightarrow> Rp(DD`n,DD`succ(n),ee`n)`(x`succ(n)) = x`n\<rbrakk>
     \<Longrightarrow> x \<in> set(Dinf(DD,ee))"
apply (simp add: Dinf_def)
apply (blast intro: mkcpoI iprodI)
done

lemma Dinf_prod: "x \<in> set(Dinf(DD,ee)) \<Longrightarrow> x:(\<Prod>n \<in> nat. set(DD`n))"
apply (simp add: Dinf_def)
apply (erule mkcpoD1 [THEN iprodE])
done

lemma Dinf_eq:
    "\<lbrakk>x \<in> set(Dinf(DD,ee)); n \<in> nat\<rbrakk>
     \<Longrightarrow> Rp(DD`n,DD`succ(n),ee`n)`(x`succ(n)) = x`n"
apply (simp add: Dinf_def)
apply (blast dest: mkcpoD2)
done

lemma rel_DinfI:
    "\<lbrakk>\<And>n. n \<in> nat \<Longrightarrow> rel(DD`n,x`n,y`n);
       x:(\<Prod>n \<in> nat. set(DD`n)); y:(\<Prod>n \<in> nat. set(DD`n))\<rbrakk>
     \<Longrightarrow> rel(Dinf(DD,ee),x,y)"
apply (simp add: Dinf_def)
apply (blast intro: rel_mkcpo [THEN iffD2] rel_iprodI iprodI)
done

lemma rel_Dinf: "\<lbrakk>rel(Dinf(DD,ee),x,y); n \<in> nat\<rbrakk> \<Longrightarrow> rel(DD`n,x`n,y`n)"
apply (simp add: Dinf_def)
apply (erule rel_mkcpoE [THEN rel_iprodE], assumption)
done

lemma chain_Dinf: "chain(Dinf(DD,ee),X) \<Longrightarrow> chain(iprod(DD),X)"
apply (simp add: Dinf_def)
apply (erule chain_mkcpo)
done

lemma subcpo_Dinf: "emb_chain(DD,ee) \<Longrightarrow> subcpo(Dinf(DD,ee),iprod(DD))"
apply (simp add: Dinf_def)
apply (rule subcpo_mkcpo)
apply (simp add: Dinf_def [symmetric])
apply (rule ballI)
apply (simplesubst lub_iprod)
  \<comment> \<open>Subst would rewrite the lhs. We want to change the rhs.\<close>
apply (assumption | rule chain_Dinf emb_chain_cpo)+
apply simp
apply (subst Rp_cont [THEN cont_lub])
apply (assumption |
       rule emb_chain_cpo emb_chain_emb nat_succI chain_iprod chain_Dinf)+
(* Useful simplification, ugly in HOL. *)
apply (simp add: Dinf_eq chain_in)
apply (auto intro: cpo_iprod emb_chain_cpo)
done

(* Simple example of existential reasoning in Isabelle versus HOL. *)

lemma cpo_Dinf: "emb_chain(DD,ee) \<Longrightarrow> cpo(Dinf(DD,ee))"
apply (rule subcpo_cpo)
apply (erule subcpo_Dinf)
apply (auto intro: cpo_iprod emb_chain_cpo)
done

(* Again and again the proofs are much easier to WRITE in Isabelle, but
  the proof steps are essentially the same (I think). *)

lemma lub_Dinf:
    "\<lbrakk>chain(Dinf(DD,ee),X); emb_chain(DD,ee)\<rbrakk>
     \<Longrightarrow> lub(Dinf(DD,ee),X) = (\<lambda>n \<in> nat. lub(DD`n,\<lambda>m \<in> nat. X`m`n))"
apply (subst subcpo_Dinf [THEN lub_subcpo])
apply (auto intro: cpo_iprod emb_chain_cpo lub_iprod chain_Dinf)
done

(*----------------------------------------------------------------------*)
(* Generalising embedddings D_m -> D_{m+1} to embeddings D_m -> D_n,    *)
(* defined as eps(DD,ee,m,n), via e_less and e_gr.                      *)
(*----------------------------------------------------------------------*)

lemma e_less_eq:
    "m \<in> nat \<Longrightarrow> e_less(DD,ee,m,m) = id(set(DD`m))"
by (simp add: e_less_def)

lemma lemma_succ_sub: "succ(m#+n)#-m = succ(natify(n))"
by simp

lemma e_less_add:
     "e_less(DD,ee,m,succ(m#+k)) = (ee`(m#+k))O(e_less(DD,ee,m,m#+k))"
by (simp add: e_less_def)

lemma le_exists:
    "\<lbrakk>m \<le> n;  \<And>x. \<lbrakk>n=m#+x; x \<in> nat\<rbrakk> \<Longrightarrow> Q;  n \<in> nat\<rbrakk> \<Longrightarrow> Q"
apply (drule less_imp_succ_add, auto)
done

lemma e_less_le: "\<lbrakk>m \<le> n;  n \<in> nat\<rbrakk>
     \<Longrightarrow> e_less(DD,ee,m,succ(n)) = ee`n O e_less(DD,ee,m,n)"
apply (rule le_exists, assumption)
apply (simp add: e_less_add, assumption)
done

(* All theorems assume variables m and n are natural numbers. *)

lemma e_less_succ:
     "m \<in> nat \<Longrightarrow> e_less(DD,ee,m,succ(m)) = ee`m O id(set(DD`m))"
by (simp add: e_less_le e_less_eq)

lemma e_less_succ_emb:
    "\<lbrakk>\<And>n. n \<in> nat \<Longrightarrow> emb(DD`n,DD`succ(n),ee`n); m \<in> nat\<rbrakk>
     \<Longrightarrow> e_less(DD,ee,m,succ(m)) = ee`m"
apply (simp add: e_less_succ)
apply (blast intro: emb_cont cont_fun comp_id)
done

(* Compare this proof with the HOL one, here we do type checking. *)
(* In any case the one below was very easy to write. *)

lemma emb_e_less_add:
     "\<lbrakk>emb_chain(DD,ee); m \<in> nat\<rbrakk>
      \<Longrightarrow> emb(DD`m, DD`(m#+k), e_less(DD,ee,m,m#+k))"
apply (subgoal_tac "emb (DD`m, DD` (m#+natify (k)),
                         e_less (DD,ee,m,m#+natify (k))) ")
apply (rule_tac [2] n = "natify (k) " in nat_induct)
apply (simp_all add: e_less_eq)
apply (assumption | rule emb_id emb_chain_cpo)+
apply (simp add: e_less_add)
apply (auto intro: emb_comp emb_chain_emb emb_chain_cpo)
done

lemma emb_e_less:
     "\<lbrakk>m \<le> n;  emb_chain(DD,ee);  n \<in> nat\<rbrakk>
      \<Longrightarrow> emb(DD`m, DD`n, e_less(DD,ee,m,n))"
apply (frule lt_nat_in_nat)
apply (erule nat_succI)
(* same proof as e_less_le *)
apply (rule le_exists, assumption)
apply (simp add: emb_e_less_add, assumption)
done

lemma comp_mono_eq: "\<lbrakk>f=f'; g=g'\<rbrakk> \<Longrightarrow> f O g = f' O g'"
by simp

(* Note the object-level implication for induction on k. This
   must be removed later to allow the theorems to be used for simp.
   Therefore this theorem is only a lemma. *)

lemma e_less_split_add_lemma [rule_format]:
    "\<lbrakk>emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat\<rbrakk>
     \<Longrightarrow> n \<le> k \<longrightarrow>
         e_less(DD,ee,m,m#+k) = e_less(DD,ee,m#+n,m#+k) O e_less(DD,ee,m,m#+n)"
apply (induct_tac k)
apply (simp add: e_less_eq id_type [THEN id_comp])
apply (simp add: le_succ_iff)
apply (rule impI)
apply (erule disjE)
apply (erule impE, assumption)
apply (simp add: e_less_add)
apply (subst e_less_le)
apply (assumption | rule add_le_mono nat_le_refl add_type nat_succI)+
apply (subst comp_assoc)
apply (assumption | rule comp_mono_eq refl)+
apply (simp del: add_succ_right add: add_succ_right [symmetric]
            add: e_less_eq add_type nat_succI)
apply (subst id_comp) (* simp cannot unify/inst right, use brr below (?) . *)
apply (assumption |
       rule emb_e_less_add [THEN emb_cont, THEN cont_fun] refl nat_succI)+
done

lemma e_less_split_add:
    "\<lbrakk>n \<le> k; emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat\<rbrakk>
     \<Longrightarrow> e_less(DD,ee,m,m#+k) = e_less(DD,ee,m#+n,m#+k) O e_less(DD,ee,m,m#+n)"
by (blast intro: e_less_split_add_lemma)

lemma e_gr_eq:
    "m \<in> nat \<Longrightarrow> e_gr(DD,ee,m,m) = id(set(DD`m))"
by (simp add: e_gr_def)

lemma e_gr_add:
    "\<lbrakk>n \<in> nat; k \<in> nat\<rbrakk>
     \<Longrightarrow> e_gr(DD,ee,succ(n#+k),n) =
         e_gr(DD,ee,n#+k,n) O Rp(DD`(n#+k),DD`succ(n#+k),ee`(n#+k))"
by (simp add: e_gr_def)

lemma e_gr_le:
     "\<lbrakk>n \<le> m; m \<in> nat; n \<in> nat\<rbrakk>
      \<Longrightarrow> e_gr(DD,ee,succ(m),n) = e_gr(DD,ee,m,n) O Rp(DD`m,DD`succ(m),ee`m)"
apply (erule le_exists)
apply (simp add: e_gr_add, assumption+)
done

lemma e_gr_succ:
 "m \<in> nat \<Longrightarrow> e_gr(DD,ee,succ(m),m) = id(set(DD`m)) O Rp(DD`m,DD`succ(m),ee`m)"
by (simp add: e_gr_le e_gr_eq)

(* Cpo asm's due to THE uniqueness. *)
lemma e_gr_succ_emb: "\<lbrakk>emb_chain(DD,ee); m \<in> nat\<rbrakk>
     \<Longrightarrow> e_gr(DD,ee,succ(m),m) = Rp(DD`m,DD`succ(m),ee`m)"
apply (simp add: e_gr_succ)
apply (blast intro: id_comp Rp_cont cont_fun emb_chain_cpo emb_chain_emb)
done

lemma e_gr_fun_add:
    "\<lbrakk>emb_chain(DD,ee); n \<in> nat; k \<in> nat\<rbrakk>
     \<Longrightarrow> e_gr(DD,ee,n#+k,n): set(DD`(n#+k))->set(DD`n)"
apply (induct_tac k)
apply (simp add: e_gr_eq id_type)
apply (simp add: e_gr_add)
apply (blast intro: comp_fun Rp_cont cont_fun emb_chain_emb emb_chain_cpo)
done

lemma e_gr_fun:
    "\<lbrakk>n \<le> m; emb_chain(DD,ee); m \<in> nat; n \<in> nat\<rbrakk>
     \<Longrightarrow> e_gr(DD,ee,m,n): set(DD`m)->set(DD`n)"
apply (rule le_exists, assumption)
apply (simp add: e_gr_fun_add, assumption+)
done

lemma e_gr_split_add_lemma:
    "\<lbrakk>emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat\<rbrakk>
     \<Longrightarrow> m \<le> k \<longrightarrow>
         e_gr(DD,ee,n#+k,n) = e_gr(DD,ee,n#+m,n) O e_gr(DD,ee,n#+k,n#+m)"
apply (induct_tac k)
apply (rule impI)
apply (simp add: le0_iff e_gr_eq id_type [THEN comp_id])
apply (simp add: le_succ_iff)
apply (rule impI)
apply (erule disjE)
apply (erule impE, assumption)
apply (simp add: e_gr_add)
apply (subst e_gr_le)
apply (assumption | rule add_le_mono nat_le_refl add_type nat_succI)+
apply (subst comp_assoc)
apply (assumption | rule comp_mono_eq refl)+
(* New direct subgoal *)
apply (simp del: add_succ_right add: add_succ_right [symmetric]
            add: e_gr_eq)
apply (subst comp_id) (* simp cannot unify/inst right, use brr below (?) . *)
apply (assumption | rule e_gr_fun add_type refl add_le_self nat_succI)+
done

lemma e_gr_split_add:
     "\<lbrakk>m \<le> k; emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat\<rbrakk>
      \<Longrightarrow> e_gr(DD,ee,n#+k,n) = e_gr(DD,ee,n#+m,n) O e_gr(DD,ee,n#+k,n#+m)"
apply (blast intro: e_gr_split_add_lemma [THEN mp])
done

lemma e_less_cont:
     "\<lbrakk>m \<le> n; emb_chain(DD,ee); m \<in> nat; n \<in> nat\<rbrakk>
      \<Longrightarrow> e_less(DD,ee,m,n):cont(DD`m,DD`n)"
apply (blast intro: emb_cont emb_e_less)
done

lemma e_gr_cont:
    "\<lbrakk>n \<le> m; emb_chain(DD,ee); m \<in> nat; n \<in> nat\<rbrakk>
     \<Longrightarrow> e_gr(DD,ee,m,n):cont(DD`m,DD`n)"
apply (erule rev_mp)
apply (induct_tac m)
apply (simp add: le0_iff e_gr_eq nat_0I)
apply (assumption | rule impI id_cont emb_chain_cpo nat_0I)+
apply (simp add: le_succ_iff)
apply (erule disjE)
apply (erule impE, assumption)
apply (simp add: e_gr_le)
apply (blast intro: comp_pres_cont Rp_cont emb_chain_cpo emb_chain_emb)
apply (simp add: e_gr_eq)
done

(* Considerably shorter.... 57 against 26 *)

lemma e_less_e_gr_split_add:
    "\<lbrakk>n \<le> k; emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat\<rbrakk>
     \<Longrightarrow> e_less(DD,ee,m,m#+n) = e_gr(DD,ee,m#+k,m#+n) O e_less(DD,ee,m,m#+k)"
(* Use mp to prepare for induction. *)
apply (erule rev_mp)
apply (induct_tac k)
apply (simp add: e_gr_eq e_less_eq id_type [THEN id_comp])
apply (simp add: le_succ_iff)
apply (rule impI)
apply (erule disjE)
apply (erule impE, assumption)
apply (simp add: e_gr_le e_less_le add_le_mono)
apply (subst comp_assoc)
apply (rule_tac s1 = "ee` (m#+x)" in comp_assoc [THEN subst])
apply (subst embRp_eq)
apply (assumption | rule emb_chain_emb add_type emb_chain_cpo nat_succI)+
apply (subst id_comp)
apply (blast intro: e_less_cont [THEN cont_fun] add_le_self)
apply (rule refl)
apply (simp del: add_succ_right add: add_succ_right [symmetric]
            add: e_gr_eq)
apply (blast intro: id_comp [symmetric] e_less_cont [THEN cont_fun]
                    add_le_self)
done

(* Again considerably shorter, and easy to obtain from the previous thm. *)

lemma e_gr_e_less_split_add:
    "\<lbrakk>m \<le> k; emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat\<rbrakk>
     \<Longrightarrow> e_gr(DD,ee,n#+m,n) = e_gr(DD,ee,n#+k,n) O e_less(DD,ee,n#+m,n#+k)"
(* Use mp to prepare for induction. *)
apply (erule rev_mp)
apply (induct_tac k)
apply (simp add: e_gr_eq e_less_eq id_type [THEN id_comp])
apply (simp add: le_succ_iff)
apply (rule impI)
apply (erule disjE)
apply (erule impE, assumption)
apply (simp add: e_gr_le e_less_le add_le_self nat_le_refl add_le_mono)
apply (subst comp_assoc)
apply (rule_tac s1 = "ee` (n#+x)" in comp_assoc [THEN subst])
apply (subst embRp_eq)
apply (assumption | rule emb_chain_emb add_type emb_chain_cpo nat_succI)+
apply (subst id_comp)
apply (blast intro!: e_less_cont [THEN cont_fun] add_le_mono nat_le_refl)
apply (rule refl)
apply (simp del: add_succ_right add: add_succ_right [symmetric]
            add: e_less_eq)
apply (blast intro: comp_id [symmetric] e_gr_cont [THEN cont_fun] add_le_self)
done


lemma emb_eps:
    "\<lbrakk>m \<le> n; emb_chain(DD,ee); m \<in> nat; n \<in> nat\<rbrakk>
     \<Longrightarrow> emb(DD`m,DD`n,eps(DD,ee,m,n))"
apply (simp add: eps_def)
apply (blast intro: emb_e_less)
done

lemma eps_fun:
    "\<lbrakk>emb_chain(DD,ee); m \<in> nat; n \<in> nat\<rbrakk>
     \<Longrightarrow> eps(DD,ee,m,n): set(DD`m)->set(DD`n)"
apply (simp add: eps_def)
apply (auto intro: e_less_cont [THEN cont_fun]
                   not_le_iff_lt [THEN iffD1, THEN leI]
                   e_gr_fun nat_into_Ord)
done

lemma eps_id: "n \<in> nat \<Longrightarrow> eps(DD,ee,n,n) = id(set(DD`n))"
by (simp add: eps_def e_less_eq)

lemma eps_e_less_add:
    "\<lbrakk>m \<in> nat; n \<in> nat\<rbrakk> \<Longrightarrow> eps(DD,ee,m,m#+n) = e_less(DD,ee,m,m#+n)"
by (simp add: eps_def add_le_self)

lemma eps_e_less:
    "\<lbrakk>m \<le> n; m \<in> nat; n \<in> nat\<rbrakk> \<Longrightarrow> eps(DD,ee,m,n) = e_less(DD,ee,m,n)"
by (simp add: eps_def)

lemma eps_e_gr_add:
    "\<lbrakk>n \<in> nat; k \<in> nat\<rbrakk> \<Longrightarrow> eps(DD,ee,n#+k,n) = e_gr(DD,ee,n#+k,n)"
by (simp add: eps_def e_less_eq e_gr_eq)

lemma eps_e_gr:
    "\<lbrakk>n \<le> m; m \<in> nat; n \<in> nat\<rbrakk> \<Longrightarrow> eps(DD,ee,m,n) = e_gr(DD,ee,m,n)"
apply (erule le_exists)
apply (simp_all add: eps_e_gr_add)
done

lemma eps_succ_ee:
    "\<lbrakk>\<And>n. n \<in> nat \<Longrightarrow> emb(DD`n,DD`succ(n),ee`n); m \<in> nat\<rbrakk>
     \<Longrightarrow> eps(DD,ee,m,succ(m)) = ee`m"
by (simp add: eps_e_less le_succ_iff e_less_succ_emb)

lemma eps_succ_Rp:
    "\<lbrakk>emb_chain(DD,ee); m \<in> nat\<rbrakk>
     \<Longrightarrow> eps(DD,ee,succ(m),m) = Rp(DD`m,DD`succ(m),ee`m)"
by (simp add: eps_e_gr le_succ_iff e_gr_succ_emb)

lemma eps_cont:
  "\<lbrakk>emb_chain(DD,ee); m \<in> nat; n \<in> nat\<rbrakk> \<Longrightarrow> eps(DD,ee,m,n): cont(DD`m,DD`n)"
apply (rule_tac i = m and j = n in nat_linear_le)
apply (simp_all add: eps_e_less e_less_cont eps_e_gr e_gr_cont)
done

(* Theorems about splitting. *)

lemma eps_split_add_left:
    "\<lbrakk>n \<le> k; emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat\<rbrakk>
     \<Longrightarrow> eps(DD,ee,m,m#+k) = eps(DD,ee,m#+n,m#+k) O eps(DD,ee,m,m#+n)"
apply (simp add: eps_e_less add_le_self add_le_mono)
apply (auto intro: e_less_split_add)
done

lemma eps_split_add_left_rev:
    "\<lbrakk>n \<le> k; emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat\<rbrakk>
     \<Longrightarrow> eps(DD,ee,m,m#+n) = eps(DD,ee,m#+k,m#+n) O eps(DD,ee,m,m#+k)"
apply (simp add: eps_e_less_add eps_e_gr add_le_self add_le_mono)
apply (auto intro: e_less_e_gr_split_add)
done

lemma eps_split_add_right:
    "\<lbrakk>m \<le> k; emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat\<rbrakk>
     \<Longrightarrow> eps(DD,ee,n#+k,n) = eps(DD,ee,n#+m,n) O eps(DD,ee,n#+k,n#+m)"
apply (simp add: eps_e_gr add_le_self add_le_mono)
apply (auto intro: e_gr_split_add)
done

lemma eps_split_add_right_rev:
    "\<lbrakk>m \<le> k; emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat\<rbrakk>
     \<Longrightarrow> eps(DD,ee,n#+m,n) = eps(DD,ee,n#+k,n) O eps(DD,ee,n#+m,n#+k)"
apply (simp add: eps_e_gr_add eps_e_less add_le_self add_le_mono)
apply (auto intro: e_gr_e_less_split_add)
done

(* Arithmetic *)

lemma le_exists_lemma:
    "\<lbrakk>n \<le> k; k \<le> m;
        \<And>p q. \<lbrakk>p \<le> q; k=n#+p; m=n#+q; p \<in> nat; q \<in> nat\<rbrakk> \<Longrightarrow> R;
        m \<in> nat\<rbrakk>\<Longrightarrow>R"
apply (rule le_exists, assumption)
prefer 2 apply (simp add: lt_nat_in_nat)
apply (rule le_trans [THEN le_exists], assumption+, force+)
done

lemma eps_split_left_le:
    "\<lbrakk>m \<le> k; k \<le> n; emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat\<rbrakk>
     \<Longrightarrow> eps(DD,ee,m,n) = eps(DD,ee,k,n) O eps(DD,ee,m,k)"
apply (rule le_exists_lemma, assumption+)
apply (auto intro: eps_split_add_left)
done

lemma eps_split_left_le_rev:
    "\<lbrakk>m \<le> n; n \<le> k; emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat\<rbrakk>
     \<Longrightarrow> eps(DD,ee,m,n) = eps(DD,ee,k,n) O eps(DD,ee,m,k)"
apply (rule le_exists_lemma, assumption+)
apply (auto intro: eps_split_add_left_rev)
done

lemma eps_split_right_le:
    "\<lbrakk>n \<le> k; k \<le> m; emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat\<rbrakk>
     \<Longrightarrow> eps(DD,ee,m,n) = eps(DD,ee,k,n) O eps(DD,ee,m,k)"
apply (rule le_exists_lemma, assumption+)
apply (auto intro: eps_split_add_right)
done

lemma eps_split_right_le_rev:
    "\<lbrakk>n \<le> m; m \<le> k; emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat\<rbrakk>
     \<Longrightarrow> eps(DD,ee,m,n) = eps(DD,ee,k,n) O eps(DD,ee,m,k)"
apply (rule le_exists_lemma, assumption+)
apply (auto intro: eps_split_add_right_rev)
done

(* The desired two theorems about `splitting'. *)

lemma eps_split_left:
    "\<lbrakk>m \<le> k; emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat\<rbrakk>
     \<Longrightarrow> eps(DD,ee,m,n) = eps(DD,ee,k,n) O eps(DD,ee,m,k)"
apply (rule nat_linear_le)
apply (rule_tac [4] eps_split_right_le_rev)
prefer 4 apply assumption
apply (rule_tac [3] nat_linear_le)
apply (rule_tac [5] eps_split_left_le)
prefer 6 apply assumption
apply (simp_all add: eps_split_left_le_rev)
done

lemma eps_split_right:
    "\<lbrakk>n \<le> k; emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat\<rbrakk>
     \<Longrightarrow> eps(DD,ee,m,n) = eps(DD,ee,k,n) O eps(DD,ee,m,k)"
apply (rule nat_linear_le)
apply (rule_tac [3] eps_split_left_le_rev)
prefer 3 apply assumption
apply (rule_tac [8] nat_linear_le)
apply (rule_tac [10] eps_split_right_le)
prefer 11 apply assumption
apply (simp_all add: eps_split_right_le_rev)
done

(*----------------------------------------------------------------------*)
(* That was eps: D_m -> D_n, NEXT rho_emb: D_n -> Dinf.                 *)
(*----------------------------------------------------------------------*)

(* Considerably shorter. *)

lemma rho_emb_fun:
    "\<lbrakk>emb_chain(DD,ee); n \<in> nat\<rbrakk>
     \<Longrightarrow> rho_emb(DD,ee,n): set(DD`n) -> set(Dinf(DD,ee))"
apply (simp add: rho_emb_def)
apply (assumption |
       rule lam_type DinfI eps_cont [THEN cont_fun, THEN apply_type])+
apply simp
apply (rule_tac i = "succ (na) " and j = n in nat_linear_le)
   apply blast
  apply assumption
 apply (simplesubst eps_split_right_le)
    \<comment> \<open>Subst would rewrite the lhs. We want to change the rhs.\<close>
       prefer 2 apply assumption
      apply simp
     apply (assumption | rule add_le_self nat_0I nat_succI)+
 apply (simp add: eps_succ_Rp)
 apply (subst comp_fun_apply)
    apply (assumption |
           rule eps_fun nat_succI Rp_cont [THEN cont_fun]
                emb_chain_emb emb_chain_cpo refl)+
(* Now the second part of the proof. Slightly different than HOL. *)
apply (simp add: eps_e_less nat_succI)
apply (erule le_iff [THEN iffD1, THEN disjE])
apply (simp add: e_less_le)
apply (subst comp_fun_apply)
apply (assumption | rule e_less_cont cont_fun emb_chain_emb emb_cont)+
apply (subst embRp_eq_thm)
apply (assumption |
       rule emb_chain_emb e_less_cont [THEN cont_fun, THEN apply_type]
            emb_chain_cpo nat_succI)+
 apply (simp add: eps_e_less)
apply (simp add: eps_succ_Rp e_less_eq id_conv nat_succI)
done

lemma rho_emb_apply1:
    "x \<in> set(DD`n) \<Longrightarrow> rho_emb(DD,ee,n)`x = (\<lambda>m \<in> nat. eps(DD,ee,n,m)`x)"
by (simp add: rho_emb_def)

lemma rho_emb_apply2:
    "\<lbrakk>x \<in> set(DD`n); m \<in> nat\<rbrakk> \<Longrightarrow> rho_emb(DD,ee,n)`x`m = eps(DD,ee,n,m)`x"
by (simp add: rho_emb_def)

lemma rho_emb_id: "\<lbrakk>x \<in> set(DD`n); n \<in> nat\<rbrakk> \<Longrightarrow> rho_emb(DD,ee,n)`x`n = x"
by (simp add: rho_emb_apply2 eps_id)

(* Shorter proof, 23 against 62. *)

lemma rho_emb_cont:
    "\<lbrakk>emb_chain(DD,ee); n \<in> nat\<rbrakk>
     \<Longrightarrow> rho_emb(DD,ee,n): cont(DD`n,Dinf(DD,ee))"
apply (rule contI)
apply (assumption | rule rho_emb_fun)+
apply (rule rel_DinfI)
apply (simp add: rho_emb_def)
apply (assumption |
       rule eps_cont [THEN cont_mono]  Dinf_prod apply_type rho_emb_fun)+
(* Continuity, different order, slightly different proofs. *)
apply (subst lub_Dinf)
apply (rule chainI)
apply (assumption | rule lam_type rho_emb_fun [THEN apply_type]  chain_in)+
apply simp
apply (rule rel_DinfI)
apply (simp add: rho_emb_apply2 chain_in)
apply (assumption |
       rule eps_cont [THEN cont_mono]  chain_rel Dinf_prod
            rho_emb_fun [THEN apply_type]  chain_in nat_succI)+
(* Now, back to the result of applying lub_Dinf *)
apply (simp add: rho_emb_apply2 chain_in)
apply (subst rho_emb_apply1)
apply (assumption | rule cpo_lub [THEN islub_in]  emb_chain_cpo)+
apply (rule fun_extension)
apply (assumption |
       rule lam_type eps_cont [THEN cont_fun, THEN apply_type]
            cpo_lub [THEN islub_in]  emb_chain_cpo)+
apply (assumption | rule cont_chain eps_cont emb_chain_cpo)+
apply simp
apply (simp add: eps_cont [THEN cont_lub])
done

(* 32 vs 61, using safe_tac with imp in asm would be unfortunate (5steps) *)

lemma eps1_aux1:
    "\<lbrakk>m \<le> n; emb_chain(DD,ee); x \<in> set(Dinf(DD,ee)); m \<in> nat; n \<in> nat\<rbrakk>
     \<Longrightarrow> rel(DD`n,e_less(DD,ee,m,n)`(x`m),x`n)"
apply (erule rev_mp) (* For induction proof *)
apply (induct_tac n)
apply (rule impI)
apply (simp add: e_less_eq)
apply (subst id_conv)
apply (assumption | rule apply_type Dinf_prod cpo_refl emb_chain_cpo nat_0I)+
apply (simp add: le_succ_iff)
apply (rule impI)
apply (erule disjE)
apply (drule mp, assumption)
apply (rule cpo_trans)
apply (rule_tac [2] e_less_le [THEN ssubst])
apply (assumption | rule emb_chain_cpo nat_succI)+
apply (subst comp_fun_apply)
apply (assumption |
       rule emb_chain_emb [THEN emb_cont]  e_less_cont cont_fun apply_type
            Dinf_prod)+
apply (rule_tac y = "x`xa" in emb_chain_emb [THEN emb_cont, THEN cont_mono])
apply (assumption | rule e_less_cont [THEN cont_fun]  apply_type Dinf_prod)+
apply (rule_tac x1 = x and n1 = xa in Dinf_eq [THEN subst])
apply (rule_tac [3] comp_fun_apply [THEN subst])
apply (rename_tac [5] y)
apply (rule_tac [5] P =
         "\<lambda>z. rel(DD`succ(y),
                  (ee`y O Rp(DD'(y)`y,DD'(y)`succ(y),ee'(y)`y)) ` (x`succ(y)),
                  z)" for DD' ee'
       in id_conv [THEN subst])
apply (rule_tac [6] rel_cf)
(* Dinf and cont_fun doesn't go well together, both Pi(_,\<lambda>x._). *)
(* solves 10 of 11 subgoals *)
apply (assumption |
       rule Dinf_prod [THEN apply_type] cont_fun Rp_cont e_less_cont
            emb_cont emb_chain_emb emb_chain_cpo apply_type embRp_rel
            disjI1 [THEN le_succ_iff [THEN iffD2]]  nat_succI)+
apply (simp add: e_less_eq)
apply (subst id_conv)
apply (auto intro: apply_type Dinf_prod emb_chain_cpo)
done

(* 18 vs 40 *)

lemma eps1_aux2:
    "\<lbrakk>n \<le> m; emb_chain(DD,ee); x \<in> set(Dinf(DD,ee)); m \<in> nat; n \<in> nat\<rbrakk>
     \<Longrightarrow> rel(DD`n,e_gr(DD,ee,m,n)`(x`m),x`n)"
apply (erule rev_mp) (* For induction proof *)
apply (induct_tac m)
apply (rule impI)
apply (simp add: e_gr_eq)
apply (subst id_conv)
apply (assumption | rule apply_type Dinf_prod cpo_refl emb_chain_cpo nat_0I)+
apply (simp add: le_succ_iff)
apply (rule impI)
apply (erule disjE)
apply (drule mp, assumption)
apply (subst e_gr_le)
apply (rule_tac [4] comp_fun_apply [THEN ssubst])
apply (rule_tac [6] Dinf_eq [THEN ssubst])
apply (assumption |
       rule emb_chain_emb emb_chain_cpo Rp_cont e_gr_cont cont_fun emb_cont
            apply_type Dinf_prod nat_succI)+
apply (simp add: e_gr_eq)
apply (subst id_conv)
apply (auto intro: apply_type Dinf_prod emb_chain_cpo)
done

lemma eps1:
    "\<lbrakk>emb_chain(DD,ee); x \<in> set(Dinf(DD,ee)); m \<in> nat; n \<in> nat\<rbrakk>
     \<Longrightarrow> rel(DD`n,eps(DD,ee,m,n)`(x`m),x`n)"
apply (simp add: eps_def)
apply (blast intro: eps1_aux1 not_le_iff_lt [THEN iffD1, THEN leI, THEN eps1_aux2]
                    nat_into_Ord)
done

(* The following theorem is needed/useful due to type check for rel_cfI,
   but also elsewhere.
   Look for occurrences of rel_cfI, rel_DinfI, etc to evaluate the problem. *)

lemma lam_Dinf_cont:
  "\<lbrakk>emb_chain(DD,ee); n \<in> nat\<rbrakk>
     \<Longrightarrow> (\<lambda>x \<in> set(Dinf(DD,ee)). x`n) \<in> cont(Dinf(DD,ee),DD`n)"
apply (rule contI)
apply (assumption | rule lam_type apply_type Dinf_prod)+
apply simp
apply (assumption | rule rel_Dinf)+
apply (subst beta)
apply (auto intro: cpo_Dinf islub_in cpo_lub)
apply (simp add: chain_in lub_Dinf)
done

lemma rho_projpair:
    "\<lbrakk>emb_chain(DD,ee); n \<in> nat\<rbrakk>
     \<Longrightarrow> projpair(DD`n,Dinf(DD,ee),rho_emb(DD,ee,n),rho_proj(DD,ee,n))"
apply (simp add: rho_proj_def)
apply (rule projpairI)
apply (assumption | rule rho_emb_cont)+
(* lemma used, introduced because same fact needed below due to rel_cfI. *)
apply (assumption | rule lam_Dinf_cont)+
(*-----------------------------------------------*)
(* This part is 7 lines, but 30 in HOL (75% reduction!) *)
apply (rule fun_extension)
apply (rule_tac [3] id_conv [THEN ssubst])
apply (rule_tac [4] comp_fun_apply [THEN ssubst])
apply (rule_tac [6] beta [THEN ssubst])
apply (rule_tac [7] rho_emb_id [THEN ssubst])
apply (assumption |
       rule comp_fun id_type lam_type rho_emb_fun Dinf_prod [THEN apply_type]
            apply_type refl)+
(*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
apply (rule rel_cfI) (* ----------------\<longrightarrow>>>Yields type cond, not in HOL *)
apply (subst id_conv)
apply (rule_tac [2] comp_fun_apply [THEN ssubst])
apply (rule_tac [4] beta [THEN ssubst])
apply (rule_tac [5] rho_emb_apply1 [THEN ssubst])
apply (rule_tac [6] rel_DinfI)
apply (rule_tac [6] beta [THEN ssubst])
(* Dinf_prod bad with lam_type *)
apply (assumption |
       rule eps1 lam_type rho_emb_fun eps_fun
            Dinf_prod [THEN apply_type] refl)+
apply (assumption |
       rule apply_type eps_fun Dinf_prod comp_pres_cont rho_emb_cont
            lam_Dinf_cont id_cont cpo_Dinf emb_chain_cpo)+
done

lemma emb_rho_emb:
  "\<lbrakk>emb_chain(DD,ee); n \<in> nat\<rbrakk> \<Longrightarrow> emb(DD`n,Dinf(DD,ee),rho_emb(DD,ee,n))"
by (auto simp add: emb_def intro: exI rho_projpair)

lemma rho_proj_cont: "\<lbrakk>emb_chain(DD,ee); n \<in> nat\<rbrakk>
     \<Longrightarrow> rho_proj(DD,ee,n) \<in> cont(Dinf(DD,ee),DD`n)"
by (auto intro: rho_projpair projpair_p_cont)

(*----------------------------------------------------------------------*)
(* Commutivity and universality.                                        *)
(*----------------------------------------------------------------------*)

lemma commuteI:
  "\<lbrakk>\<And>n. n \<in> nat \<Longrightarrow> emb(DD`n,E,r(n));
      \<And>m n. \<lbrakk>m \<le> n; m \<in> nat; n \<in> nat\<rbrakk> \<Longrightarrow> r(n) O eps(DD,ee,m,n) = r(m)\<rbrakk>
     \<Longrightarrow> commute(DD,ee,E,r)"
by (simp add: commute_def)

lemma commute_emb [TC]:
  "\<lbrakk>commute(DD,ee,E,r); n \<in> nat\<rbrakk> \<Longrightarrow> emb(DD`n,E,r(n))"
by (simp add: commute_def)

lemma commute_eq:
  "\<lbrakk>commute(DD,ee,E,r); m \<le> n; m \<in> nat; n \<in> nat\<rbrakk>
     \<Longrightarrow> r(n) O eps(DD,ee,m,n) = r(m) "
by (simp add: commute_def)

(* Shorter proof: 11 vs 46 lines. *)

lemma rho_emb_commute:
  "emb_chain(DD,ee) \<Longrightarrow> commute(DD,ee,Dinf(DD,ee),rho_emb(DD,ee))"
apply (rule commuteI)
apply (assumption | rule emb_rho_emb)+
apply (rule fun_extension) (* Manual instantiation in HOL. *)
apply (rule_tac [3] comp_fun_apply [THEN ssubst])
apply (rule_tac [5] fun_extension) (*Next, clean up and instantiate unknowns *)
apply (assumption | rule comp_fun rho_emb_fun eps_fun Dinf_prod apply_type)+
apply (simp add: rho_emb_apply2 eps_fun [THEN apply_type])
apply (rule comp_fun_apply [THEN subst])
apply (rule_tac [3] eps_split_left [THEN subst])
apply (auto intro: eps_fun)
done

lemma le_succ: "n \<in> nat \<Longrightarrow> n \<le> succ(n)"
by (simp add: le_succ_iff)

(* Shorter proof: 21 vs 83 (106 - 23, due to OAssoc complication) *)

lemma commute_chain:
    "\<lbrakk>commute(DD,ee,E,r); emb_chain(DD,ee); cpo(E)\<rbrakk>
     \<Longrightarrow> chain(cf(E,E),\<lambda>n \<in> nat. r(n) O Rp(DD`n,E,r(n)))"
apply (rule chainI)
apply (blast intro: lam_type cont_cf comp_pres_cont commute_emb Rp_cont
                    emb_cont emb_chain_cpo,
       simp)
apply (rule_tac r1 = r and m1 = n in commute_eq [THEN subst])
apply (assumption | rule le_succ nat_succI)+
apply (subst Rp_comp)
apply (assumption | rule emb_eps commute_emb emb_chain_cpo le_succ nat_succI)+
apply (rule comp_assoc [THEN subst]) (* comp_assoc is simpler in Isa *)
apply (rule_tac r1 = "r (succ (n))" in comp_assoc [THEN ssubst])
apply (rule comp_mono)
apply (blast intro: comp_pres_cont eps_cont emb_eps commute_emb Rp_cont
                    emb_cont emb_chain_cpo le_succ)+
apply (rule_tac b="r(succ(n))" in comp_id [THEN subst]) (* 1 subst too much *)
apply (rule_tac [2] comp_mono)
apply (blast intro: comp_pres_cont eps_cont emb_eps emb_id commute_emb
                    Rp_cont emb_cont cont_fun emb_chain_cpo le_succ)+
apply (subst comp_id) (* Undoes "1 subst too much", typing next anyway *)
apply (blast intro: cont_fun Rp_cont emb_cont commute_emb cont_cf cpo_cf
                    emb_chain_cpo embRp_rel emb_eps le_succ)+
done

lemma rho_emb_chain:
  "emb_chain(DD,ee) \<Longrightarrow>
   chain(cf(Dinf(DD,ee),Dinf(DD,ee)),
         \<lambda>n \<in> nat. rho_emb(DD,ee,n) O Rp(DD`n,Dinf(DD,ee),rho_emb(DD,ee,n)))"
by (auto intro: commute_chain rho_emb_commute cpo_Dinf)

lemma rho_emb_chain_apply1:
     "\<lbrakk>emb_chain(DD,ee); x \<in> set(Dinf(DD,ee))\<rbrakk>
      \<Longrightarrow> chain(Dinf(DD,ee),
                \<lambda>n \<in> nat.
                 (rho_emb(DD,ee,n) O Rp(DD`n,Dinf(DD,ee),rho_emb(DD,ee,n)))`x)"
by (drule rho_emb_chain [THEN chain_cf], assumption, simp)

lemma chain_iprod_emb_chain:
     "\<lbrakk>chain(iprod(DD),X); emb_chain(DD,ee); n \<in> nat\<rbrakk>
      \<Longrightarrow> chain(DD`n,\<lambda>m \<in> nat. X `m `n)"
by (auto intro: chain_iprod emb_chain_cpo)

lemma rho_emb_chain_apply2:
  "\<lbrakk>emb_chain(DD,ee); x \<in> set(Dinf(DD,ee)); n \<in> nat\<rbrakk> \<Longrightarrow>
   chain
    (DD`n,
     \<lambda>xa \<in> nat.
      (rho_emb(DD, ee, xa) O Rp(DD ` xa, Dinf(DD, ee),rho_emb(DD, ee, xa))) `
       x ` n)"
by (frule rho_emb_chain_apply1 [THEN chain_Dinf, THEN chain_iprod_emb_chain],
    auto)

(* Shorter proof: 32 vs 72 (roughly), Isabelle proof has lemmas. *)

lemma rho_emb_lub:
  "emb_chain(DD,ee) \<Longrightarrow>
   lub(cf(Dinf(DD,ee),Dinf(DD,ee)),
       \<lambda>n \<in> nat. rho_emb(DD,ee,n) O Rp(DD`n,Dinf(DD,ee),rho_emb(DD,ee,n))) =
   id(set(Dinf(DD,ee)))"
apply (rule cpo_antisym)
apply (rule cpo_cf) (*Instantiate variable, continued below (loops otherwise)*)
apply (assumption | rule cpo_Dinf)+
apply (rule islub_least)
apply (assumption |
       rule cpo_lub rho_emb_chain cpo_cf cpo_Dinf isubI cont_cf id_cont)+
apply simp
apply (assumption | rule embRp_rel emb_rho_emb emb_chain_cpo cpo_Dinf)+
apply (rule rel_cfI)
apply (simp add: lub_cf rho_emb_chain cpo_Dinf)
apply (rule rel_DinfI) (* Additional assumptions *)
apply (subst lub_Dinf)
apply (assumption | rule rho_emb_chain_apply1)+
defer 1
apply (assumption |
       rule Dinf_prod cpo_lub [THEN islub_in]  id_cont cpo_Dinf cpo_cf cf_cont
            rho_emb_chain rho_emb_chain_apply1 id_cont [THEN cont_cf])+
apply simp
apply (rule dominate_islub)
apply (rule_tac [3] cpo_lub)
apply (rule_tac [6] x1 = "x`n" in chain_const [THEN chain_fun])
defer 1
apply (assumption |
       rule rho_emb_chain_apply2 emb_chain_cpo islub_const apply_type
            Dinf_prod emb_chain_cpo chain_fun rho_emb_chain_apply2)+
apply (rule dominateI, assumption, simp)
apply (subst comp_fun_apply)
apply (assumption |
       rule cont_fun Rp_cont emb_cont emb_rho_emb cpo_Dinf emb_chain_cpo)+
apply (subst rho_projpair [THEN Rp_unique])
prefer 5
apply (simp add: rho_proj_def)
apply (rule rho_emb_id [THEN ssubst])
apply (auto intro: cpo_Dinf apply_type Dinf_prod emb_chain_cpo)
done

lemma theta_chain: (* almost same proof as commute_chain *)
    "\<lbrakk>commute(DD,ee,E,r); commute(DD,ee,G,f);
        emb_chain(DD,ee); cpo(E); cpo(G)\<rbrakk>
     \<Longrightarrow> chain(cf(E,G),\<lambda>n \<in> nat. f(n) O Rp(DD`n,E,r(n)))"
apply (rule chainI)
apply (blast intro: lam_type cont_cf comp_pres_cont commute_emb Rp_cont
                    emb_cont emb_chain_cpo,
       simp)
apply (rule_tac r1 = r and m1 = n in commute_eq [THEN subst])
apply (rule_tac [5] r1 = f and m1 = n in commute_eq [THEN subst])
apply (assumption | rule le_succ nat_succI)+
apply (subst Rp_comp)
apply (assumption | rule emb_eps commute_emb emb_chain_cpo le_succ nat_succI)+
apply (rule comp_assoc [THEN subst])
apply (rule_tac r1 = "f (succ (n))" in comp_assoc [THEN ssubst])
apply (rule comp_mono)
apply (blast intro: comp_pres_cont eps_cont emb_eps commute_emb Rp_cont
                     emb_cont emb_chain_cpo le_succ)+
apply (rule_tac b="f(succ(n))" in comp_id [THEN subst]) (* 1 subst too much *)
apply (rule_tac [2] comp_mono)
apply (blast intro: comp_pres_cont eps_cont emb_eps emb_id commute_emb
                    Rp_cont emb_cont cont_fun emb_chain_cpo le_succ)+
apply (subst comp_id) (* Undoes "1 subst too much", typing next anyway *)
apply (blast intro: cont_fun Rp_cont emb_cont commute_emb cont_cf cpo_cf
                    emb_chain_cpo embRp_rel emb_eps le_succ)+
done

lemma theta_proj_chain: (* similar proof to theta_chain *)
  "\<lbrakk>commute(DD,ee,E,r); commute(DD,ee,G,f);
      emb_chain(DD,ee); cpo(E); cpo(G)\<rbrakk>
     \<Longrightarrow> chain(cf(G,E),\<lambda>n \<in> nat. r(n) O Rp(DD`n,G,f(n)))"
apply (rule chainI)
apply (blast intro: lam_type cont_cf comp_pres_cont commute_emb Rp_cont
                    emb_cont emb_chain_cpo, simp)
apply (rule_tac r1 = r and m1 = n in commute_eq [THEN subst])
apply (rule_tac [5] r1 = f and m1 = n in commute_eq [THEN subst])
apply (assumption | rule le_succ nat_succI)+
apply (subst Rp_comp)
apply (assumption | rule emb_eps commute_emb emb_chain_cpo le_succ nat_succI)+
apply (rule comp_assoc [THEN subst]) (* comp_assoc is simpler in Isa *)
apply (rule_tac r1 = "r (succ (n))" in comp_assoc [THEN ssubst])
apply (rule comp_mono)
apply (blast intro: comp_pres_cont eps_cont emb_eps commute_emb Rp_cont
                    emb_cont emb_chain_cpo le_succ)+
apply (rule_tac b="r(succ(n))" in comp_id [THEN subst]) (* 1 subst too much *)
apply (rule_tac [2] comp_mono)
apply (blast intro: comp_pres_cont eps_cont emb_eps emb_id commute_emb
                    Rp_cont emb_cont cont_fun emb_chain_cpo le_succ)+
apply (subst comp_id) (* Undoes "1 subst too much", typing next anyway *)
apply (blast intro: cont_fun Rp_cont emb_cont commute_emb cont_cf cpo_cf
                    emb_chain_cpo embRp_rel emb_eps le_succ)+
done

(* Simplification with comp_assoc is possible inside a \<lambda>-abstraction,
   because it does not have assumptions. If it had, as the HOL-ST theorem
   too strongly has, we would be in deep trouble due to HOL's lack of proper
   conditional rewriting (a HOL contrib provides something that works). *)

(* Controlled simplification inside lambda: introduce lemmas *)

lemma commute_O_lemma:
     "\<lbrakk>commute(DD,ee,E,r); commute(DD,ee,G,f);
         emb_chain(DD,ee); cpo(E); cpo(G); x \<in> nat\<rbrakk>
      \<Longrightarrow> r(x) O Rp(DD ` x, G, f(x)) O f(x) O Rp(DD ` x, E, r(x)) =
          r(x) O Rp(DD ` x, E, r(x))"
apply (rule_tac s1 = "f (x) " in comp_assoc [THEN subst])
apply (subst embRp_eq)
apply (rule_tac [4] id_comp [THEN ssubst])
apply (auto intro: cont_fun Rp_cont commute_emb emb_chain_cpo)
done


(* Shorter proof (but lemmas): 19 vs 79 (103 - 24, due to OAssoc)  *)

lemma theta_projpair:
  "\<lbrakk>lub(cf(E,E), \<lambda>n \<in> nat. r(n) O Rp(DD`n,E,r(n))) = id(set(E));
      commute(DD,ee,E,r); commute(DD,ee,G,f);
      emb_chain(DD,ee); cpo(E); cpo(G)\<rbrakk>
   \<Longrightarrow> projpair
        (E,G,
         lub(cf(E,G), \<lambda>n \<in> nat. f(n) O Rp(DD`n,E,r(n))),
         lub(cf(G,E), \<lambda>n \<in> nat. r(n) O Rp(DD`n,G,f(n))))"
apply (simp add: projpair_def rho_proj_def, safe)
apply (rule_tac [3] comp_lubs [THEN ssubst])
(* The following one line is 15 lines in HOL, and includes existentials. *)
apply (assumption |
       rule cf_cont islub_in cpo_lub cpo_cf theta_chain theta_proj_chain)+
apply (simp (no_asm) add: comp_assoc)
apply (simp add: commute_O_lemma)
apply (subst comp_lubs)
apply (assumption |
       rule cf_cont islub_in cpo_lub cpo_cf theta_chain theta_proj_chain)+
apply (simp (no_asm) add: comp_assoc)
apply (simp add: commute_O_lemma)
apply (rule dominate_islub)
defer 1
apply (rule cpo_lub)
apply (assumption |
       rule commute_chain commute_emb islub_const cont_cf id_cont
    cpo_cf chain_fun chain_const)+
apply (rule dominateI, assumption, simp)
apply (blast intro: embRp_rel commute_emb emb_chain_cpo)
done

lemma emb_theta:
    "\<lbrakk>lub(cf(E,E), \<lambda>n \<in> nat. r(n) O Rp(DD`n,E,r(n))) = id(set(E));
        commute(DD,ee,E,r); commute(DD,ee,G,f);
        emb_chain(DD,ee); cpo(E); cpo(G)\<rbrakk>
     \<Longrightarrow> emb(E,G,lub(cf(E,G), \<lambda>n \<in> nat. f(n) O Rp(DD`n,E,r(n))))"
apply (simp add: emb_def)
apply (blast intro: theta_projpair)
done

lemma mono_lemma:
    "\<lbrakk>g \<in> cont(D,D'); cpo(D); cpo(D'); cpo(E)\<rbrakk>
     \<Longrightarrow> (\<lambda>f \<in> cont(D',E). f O g) \<in> mono(cf(D',E),cf(D,E))"
apply (rule monoI)
apply (simp add: set_def cf_def)
apply (drule cf_cont)+
apply simp
apply (blast intro: comp_mono lam_type comp_pres_cont cpo_cf cont_cf)
done

lemma commute_lam_lemma:
     "\<lbrakk>commute(DD,ee,E,r); commute(DD,ee,G,f);
         emb_chain(DD,ee); cpo(E); cpo(G); n \<in> nat\<rbrakk>
      \<Longrightarrow> (\<lambda>na \<in> nat. (\<lambda>f \<in> cont(E, G). f O r(n)) `
           ((\<lambda>n \<in> nat. f(n) O Rp(DD ` n, E, r(n))) ` na))  =
          (\<lambda>na \<in> nat. (f(na) O Rp(DD ` na, E, r(na))) O r(n))"
apply (rule fun_extension)
(*something wrong here*)
apply (auto simp del: beta_if simp add: beta intro: lam_type)
done

lemma chain_lemma:
     "\<lbrakk>commute(DD,ee,E,r); commute(DD,ee,G,f);
         emb_chain(DD,ee); cpo(E); cpo(G); n \<in> nat\<rbrakk>
      \<Longrightarrow> chain(cf(DD`n,G),\<lambda>x \<in> nat. (f(x) O Rp(DD ` x, E, r(x))) O r(n))"
apply (rule commute_lam_lemma [THEN subst])
apply (blast intro: theta_chain emb_chain_cpo
               commute_emb [THEN emb_cont, THEN mono_lemma, THEN mono_chain])+
done

lemma suffix_lemma:
    "\<lbrakk>commute(DD,ee,E,r); commute(DD,ee,G,f);
        emb_chain(DD,ee); cpo(E); cpo(G); cpo(DD`x); x \<in> nat\<rbrakk>
     \<Longrightarrow> suffix(\<lambda>n \<in> nat. (f(n) O Rp(DD`n,E,r(n))) O r(x),x) =
         (\<lambda>n \<in> nat. f(x))"
apply (simp add: suffix_def)
apply (rule lam_type [THEN fun_extension])
apply (blast intro: lam_type comp_fun cont_fun Rp_cont emb_cont
                    commute_emb emb_chain_cpo)+
apply simp
apply (rename_tac y)
apply (subgoal_tac
       "f(x#+y) O (Rp(DD`(x#+y), E, r(x#+y)) O r (x#+y)) O eps(DD, ee, x, x#+y)
        = f(x)")
apply (simp add: comp_assoc commute_eq add_le_self)
apply (simp add: embRp_eq eps_fun [THEN id_comp] commute_emb emb_chain_cpo)
apply (blast intro: commute_eq add_le_self)
done


lemma mediatingI:
  "\<lbrakk>emb(E,G,t);  \<And>n. n \<in> nat \<Longrightarrow> f(n) = t O r(n)\<rbrakk>\<Longrightarrow>mediating(E,G,r,f,t)"
by (simp add: mediating_def)

lemma mediating_emb: "mediating(E,G,r,f,t) \<Longrightarrow> emb(E,G,t)"
by (simp add: mediating_def)

lemma mediating_eq: "\<lbrakk>mediating(E,G,r,f,t); n \<in> nat\<rbrakk> \<Longrightarrow> f(n) = t O r(n)"
by (simp add: mediating_def)

lemma lub_universal_mediating:
  "\<lbrakk>lub(cf(E,E), \<lambda>n \<in> nat. r(n) O Rp(DD`n,E,r(n))) = id(set(E));
      commute(DD,ee,E,r); commute(DD,ee,G,f);
      emb_chain(DD,ee); cpo(E); cpo(G)\<rbrakk>
     \<Longrightarrow> mediating(E,G,r,f,lub(cf(E,G), \<lambda>n \<in> nat. f(n) O Rp(DD`n,E,r(n))))"
apply (assumption | rule mediatingI emb_theta)+
apply (rule_tac b = "r (n) " in lub_const [THEN subst])
apply (rule_tac [3] comp_lubs [THEN ssubst])
apply (blast intro: cont_cf emb_cont commute_emb cpo_cf theta_chain
                    chain_const emb_chain_cpo)+
apply (simp (no_asm))
apply (rule_tac n1 = n in lub_suffix [THEN subst])
apply (assumption | rule chain_lemma cpo_cf emb_chain_cpo)+
apply (simp add: suffix_lemma lub_const cont_cf emb_cont commute_emb cpo_cf
                 emb_chain_cpo)
done

lemma lub_universal_unique:
    "\<lbrakk>mediating(E,G,r,f,t);
        lub(cf(E,E), \<lambda>n \<in> nat. r(n) O Rp(DD`n,E,r(n))) = id(set(E));
        commute(DD,ee,E,r); commute(DD,ee,G,f);
        emb_chain(DD,ee); cpo(E); cpo(G)\<rbrakk>
     \<Longrightarrow> t = lub(cf(E,G), \<lambda>n \<in> nat. f(n) O Rp(DD`n,E,r(n)))"
apply (rule_tac b = t in comp_id [THEN subst])
apply (erule_tac [2] subst)
apply (rule_tac [2] b = t in lub_const [THEN subst])
apply (rule_tac [4] comp_lubs [THEN ssubst])
prefer 9 apply (simp add: comp_assoc mediating_eq)
apply (assumption |
       rule cont_fun emb_cont mediating_emb cont_cf cpo_cf chain_const
            commute_chain emb_chain_cpo)+
done

(*---------------------------------------------------------------------*)
(* Dinf yields the inverse_limit, stated as rho_emb_commute and        *)
(* Dinf_universal.                                                     *)
(*---------------------------------------------------------------------*)

theorem Dinf_universal:
  "\<lbrakk>commute(DD,ee,G,f); emb_chain(DD,ee); cpo(G)\<rbrakk> \<Longrightarrow>
   mediating
    (Dinf(DD,ee),G,rho_emb(DD,ee),f,
     lub(cf(Dinf(DD,ee),G),
         \<lambda>n \<in> nat. f(n) O Rp(DD`n,Dinf(DD,ee),rho_emb(DD,ee,n)))) \<and>
   (\<forall>t. mediating(Dinf(DD,ee),G,rho_emb(DD,ee),f,t) \<longrightarrow>
     t = lub(cf(Dinf(DD,ee),G),
         \<lambda>n \<in> nat. f(n) O Rp(DD`n,Dinf(DD,ee),rho_emb(DD,ee,n))))"
apply safe
apply (assumption |
       rule lub_universal_mediating rho_emb_commute rho_emb_lub cpo_Dinf)+
apply (auto intro: lub_universal_unique rho_emb_commute rho_emb_lub cpo_Dinf)
done

end
