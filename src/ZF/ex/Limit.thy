(*  Title:      ZF/ex/Limit
    ID:         $Id$
    Author:     Sten Agerholm

    A formalization of the inverse limit construction of domain theory.

    The following paper comments on the formalization:

    "A Comparison of HOL-ST and Isabelle/ZF" by Sten Agerholm
    In Proceedings of the First Isabelle Users Workshop, Technical 
    Report No. 379, University of Cambridge Computer Laboratory, 1995.

    This is a condensed version of:

    "A Comparison of HOL-ST and Isabelle/ZF" by Sten Agerholm
    Technical Report No. 369, University of Cambridge Computer 
    Laboratory, 1995.

(Proofs converted to Isar and tidied up considerably by lcp)
*)

theory Limit  =  Main:

constdefs

  rel :: "[i,i,i]=>o"
    "rel(D,x,y) == <x,y>:snd(D)"

  set :: "i=>i"
    "set(D) == fst(D)"

  po  :: "i=>o"
    "po(D) ==
     (\<forall>x \<in> set(D). rel(D,x,x)) &
     (\<forall>x \<in> set(D). \<forall>y \<in> set(D). \<forall>z \<in> set(D).
       rel(D,x,y) --> rel(D,y,z) --> rel(D,x,z)) &
     (\<forall>x \<in> set(D). \<forall>y \<in> set(D). rel(D,x,y) --> rel(D,y,x) --> x = y)"

  chain :: "[i,i]=>o"
    (* Chains are object level functions nat->set(D) *)
    "chain(D,X) == X \<in> nat->set(D) & (\<forall>n \<in> nat. rel(D,X`n,X`(succ(n))))"

  isub :: "[i,i,i]=>o"
    "isub(D,X,x) == x \<in> set(D) & (\<forall>n \<in> nat. rel(D,X`n,x))"

  islub :: "[i,i,i]=>o"
    "islub(D,X,x) == isub(D,X,x) & (\<forall>y. isub(D,X,y) --> rel(D,x,y))"

  lub :: "[i,i]=>i"
    "lub(D,X) == THE x. islub(D,X,x)"

  cpo :: "i=>o"
    "cpo(D) == po(D) & (\<forall>X. chain(D,X) --> (\<exists>x. islub(D,X,x)))"

  pcpo :: "i=>o"
    "pcpo(D) == cpo(D) & (\<exists>x \<in> set(D). \<forall>y \<in> set(D). rel(D,x,y))"

  bot :: "i=>i"
    "bot(D) == THE x. x \<in> set(D) & (\<forall>y \<in> set(D). rel(D,x,y))"

  mono :: "[i,i]=>i"
    "mono(D,E) ==
     {f \<in> set(D)->set(E).
      \<forall>x \<in> set(D). \<forall>y \<in> set(D). rel(D,x,y) --> rel(E,f`x,f`y)}"

  cont :: "[i,i]=>i"
    "cont(D,E) ==
     {f \<in> mono(D,E).
      \<forall>X. chain(D,X) --> f`(lub(D,X)) = lub(E,\<lambda>n \<in> nat. f`(X`n))}"

  cf :: "[i,i]=>i"
    "cf(D,E) ==
     <cont(D,E),
      {y \<in> cont(D,E)*cont(D,E). \<forall>x \<in> set(D). rel(E,(fst(y))`x,(snd(y))`x)}>"

  suffix :: "[i,i]=>i"
    "suffix(X,n) == \<lambda>m \<in> nat. X`(n #+ m)"

  subchain :: "[i,i]=>o"
    "subchain(X,Y) == \<forall>m \<in> nat. \<exists>n \<in> nat. X`m = Y`(m #+ n)"

  dominate :: "[i,i,i]=>o"
    "dominate(D,X,Y) == \<forall>m \<in> nat. \<exists>n \<in> nat. rel(D,X`m,Y`n)"

  matrix :: "[i,i]=>o"
    "matrix(D,M) ==
     M \<in> nat -> (nat -> set(D)) &
     (\<forall>n \<in> nat. \<forall>m \<in> nat. rel(D,M`n`m,M`succ(n)`m)) &
     (\<forall>n \<in> nat. \<forall>m \<in> nat. rel(D,M`n`m,M`n`succ(m))) &
     (\<forall>n \<in> nat. \<forall>m \<in> nat. rel(D,M`n`m,M`succ(n)`succ(m)))"

  projpair  :: "[i,i,i,i]=>o"
    "projpair(D,E,e,p) ==
     e \<in> cont(D,E) & p \<in> cont(E,D) &
     p O e = id(set(D)) & rel(cf(E,E),e O p,id(set(E)))"

  emb       :: "[i,i,i]=>o"
    "emb(D,E,e) == \<exists>p. projpair(D,E,e,p)"

  Rp        :: "[i,i,i]=>i"
    "Rp(D,E,e) == THE p. projpair(D,E,e,p)"

  (* Twice, constructions on cpos are more difficult. *)
  iprod     :: "i=>i"
    "iprod(DD) ==
     <(\<Pi>n \<in> nat. set(DD`n)),
      {x:(\<Pi>n \<in> nat. set(DD`n))*(\<Pi>n \<in> nat. set(DD`n)).
       \<forall>n \<in> nat. rel(DD`n,fst(x)`n,snd(x)`n)}>"

  mkcpo     :: "[i,i=>o]=>i"
    (* Cannot use rel(D), is meta fun, need two more args *)
    "mkcpo(D,P) ==
     <{x \<in> set(D). P(x)},{x \<in> set(D)*set(D). rel(D,fst(x),snd(x))}>"

  subcpo    :: "[i,i]=>o"
    "subcpo(D,E) ==
     set(D) \<subseteq> set(E) &
     (\<forall>x \<in> set(D). \<forall>y \<in> set(D). rel(D,x,y) <-> rel(E,x,y)) &
     (\<forall>X. chain(D,X) --> lub(E,X):set(D))"

  subpcpo   :: "[i,i]=>o"
    "subpcpo(D,E) == subcpo(D,E) & bot(E):set(D)"

  emb_chain :: "[i,i]=>o"
    "emb_chain(DD,ee) ==
     (\<forall>n \<in> nat. cpo(DD`n)) & (\<forall>n \<in> nat. emb(DD`n,DD`succ(n),ee`n))"

  Dinf      :: "[i,i]=>i"
    "Dinf(DD,ee) ==
     mkcpo(iprod(DD))
     (%x. \<forall>n \<in> nat. Rp(DD`n,DD`succ(n),ee`n)`(x`succ(n)) = x`n)"

consts
  e_less    :: "[i,i,i,i]=>i"
  e_gr      :: "[i,i,i,i]=>i"

defs  (*???NEEDS PRIMREC*)

  e_less_def: (* Valid for m le n only. *)
    "e_less(DD,ee,m,n) == rec(n#-m,id(set(DD`m)),%x y. ee`(m#+x) O y)"

  e_gr_def: (* Valid for n le m only. *)
    "e_gr(DD,ee,m,n) ==
     rec(m#-n,id(set(DD`n)),
         %x y. y O Rp(DD`(n#+x),DD`(succ(n#+x)),ee`(n#+x)))"


constdefs
  eps       :: "[i,i,i,i]=>i"
    "eps(DD,ee,m,n) == if(m le n,e_less(DD,ee,m,n),e_gr(DD,ee,m,n))"

  rho_emb   :: "[i,i,i]=>i"
    "rho_emb(DD,ee,n) == \<lambda>x \<in> set(DD`n). \<lambda>m \<in> nat. eps(DD,ee,n,m)`x"

  rho_proj  :: "[i,i,i]=>i"
    "rho_proj(DD,ee,n) == \<lambda>x \<in> set(Dinf(DD,ee)). x`n"

  commute   :: "[i,i,i,i=>i]=>o"
    "commute(DD,ee,E,r) ==
     (\<forall>n \<in> nat. emb(DD`n,E,r(n))) &
     (\<forall>m \<in> nat. \<forall>n \<in> nat. m le n --> r(n) O eps(DD,ee,m,n) = r(m))"

  mediating :: "[i,i,i=>i,i=>i,i]=>o"
    "mediating(E,G,r,f,t) == emb(E,G,t) & (\<forall>n \<in> nat. f(n) = t O r(n))"


lemmas nat_linear_le = Ord_linear_le [OF nat_into_Ord nat_into_Ord]


(*----------------------------------------------------------------------*)
(* Basic results.                                                       *)
(*----------------------------------------------------------------------*)

lemma set_I: "x \<in> fst(D) ==> x \<in> set(D)"
by (simp add: set_def)

lemma rel_I: "<x,y>:snd(D) ==> rel(D,x,y)"
by (simp add: rel_def)

lemma rel_E: "rel(D,x,y) ==> <x,y>:snd(D)"
by (simp add: rel_def)

(*----------------------------------------------------------------------*)
(* I/E/D rules for po and cpo.                                          *)
(*----------------------------------------------------------------------*)

lemma po_refl: "[|po(D); x \<in> set(D)|] ==> rel(D,x,x)"
by (unfold po_def, blast)

lemma po_trans: "[|po(D); rel(D,x,y); rel(D,y,z); x \<in> set(D);
                  y \<in> set(D); z \<in> set(D)|] ==> rel(D,x,z)"
by (unfold po_def, blast)

lemma po_antisym:
    "[|po(D); rel(D,x,y); rel(D,y,x); x \<in> set(D); y \<in> set(D)|] ==> x = y"
by (unfold po_def, blast)

lemma poI:
  "[| !!x. x \<in> set(D) ==> rel(D,x,x);
      !!x y z. [| rel(D,x,y); rel(D,y,z); x \<in> set(D); y \<in> set(D); z \<in> set(D)|]
               ==> rel(D,x,z);
      !!x y. [| rel(D,x,y); rel(D,y,x); x \<in> set(D); y \<in> set(D)|] ==> x=y |] 
   ==> po(D)"
by (unfold po_def, blast)

lemma cpoI: "[| po(D); !!X. chain(D,X) ==> islub(D,X,x(D,X))|] ==> cpo(D)"
by (simp add: cpo_def, blast)

lemma cpo_po: "cpo(D) ==> po(D)"
by (simp add: cpo_def)

lemma cpo_refl [simp,intro!,TC]: "[|cpo(D); x \<in> set(D)|] ==> rel(D,x,x)"
by (blast intro: po_refl cpo_po)

lemma cpo_trans:
     "[|cpo(D); rel(D,x,y); rel(D,y,z); x \<in> set(D);
        y \<in> set(D); z \<in> set(D)|] ==> rel(D,x,z)"
by (blast intro: cpo_po po_trans)

lemma cpo_antisym:
     "[|cpo(D); rel(D,x,y); rel(D,y,x); x \<in> set(D); y \<in> set(D)|] ==> x = y"
by (blast intro: cpo_po po_antisym)

lemma cpo_islub: "[|cpo(D); chain(D,X);  !!x. islub(D,X,x) ==> R|] ==> R"
by (simp add: cpo_def, blast)

(*----------------------------------------------------------------------*)
(* Theorems about isub and islub.                                       *)
(*----------------------------------------------------------------------*)

lemma islub_isub: "islub(D,X,x) ==> isub(D,X,x)"
by (simp add: islub_def)

lemma islub_in: "islub(D,X,x) ==> x \<in> set(D)"
by (simp add: islub_def isub_def)

lemma islub_ub: "[|islub(D,X,x); n \<in> nat|] ==> rel(D,X`n,x)"
by (simp add: islub_def isub_def)

lemma islub_least: "[|islub(D,X,x); isub(D,X,y)|] ==> rel(D,x,y)"
by (simp add: islub_def)

lemma islubI:
    "[|isub(D,X,x); !!y. isub(D,X,y) ==> rel(D,x,y)|] ==> islub(D,X,x)"
by (simp add: islub_def)

lemma isubI:
    "[|x \<in> set(D);  !!n. n \<in> nat ==> rel(D,X`n,x)|] ==> isub(D,X,x)"
by (simp add: isub_def)

lemma isubE:
    "[|isub(D,X,x); [|x \<in> set(D);  !!n. n \<in> nat==>rel(D,X`n,x)|] ==> P
     |] ==> P"
by (simp add: isub_def)

lemma isubD1: "isub(D,X,x) ==> x \<in> set(D)"
by (simp add: isub_def)

lemma isubD2: "[|isub(D,X,x); n \<in> nat|]==>rel(D,X`n,x)"
by (simp add: isub_def)

lemma islub_unique: "[|islub(D,X,x); islub(D,X,y); cpo(D)|] ==> x = y"
by (blast intro: cpo_antisym islub_least islub_isub islub_in)

(*----------------------------------------------------------------------*)
(* lub gives the least upper bound of chains.                           *)
(*----------------------------------------------------------------------*)

lemma cpo_lub: "[|chain(D,X); cpo(D)|] ==> islub(D,X,lub(D,X))"
apply (simp add: lub_def)
apply (best elim: cpo_islub intro: theI islub_unique)
done

(*----------------------------------------------------------------------*)
(* Theorems about chains.                                               *)
(*----------------------------------------------------------------------*)

lemma chainI:
  "[|X \<in> nat->set(D);  !!n. n \<in> nat ==> rel(D,X`n,X`succ(n))|] ==> chain(D,X)"
by (simp add: chain_def)

lemma chain_fun: "chain(D,X) ==> X \<in> nat -> set(D)"
by (simp add: chain_def)

lemma chain_in [simp,TC]: "[|chain(D,X); n \<in> nat|] ==> X`n \<in> set(D)"
apply (simp add: chain_def)
apply (blast dest: apply_type)
done

lemma chain_rel [simp,TC]:
     "[|chain(D,X); n \<in> nat|] ==> rel(D, X ` n, X ` succ(n))"
by (simp add: chain_def)

lemma chain_rel_gen_add:
     "[|chain(D,X); cpo(D); n \<in> nat; m \<in> nat|] ==> rel(D,X`n,(X`(m #+ n)))"
apply (induct_tac m)
apply (auto intro: cpo_trans)
done

lemma chain_rel_gen:
    "[|n le m; chain(D,X); cpo(D); m \<in> nat|] ==> rel(D,X`n,X`m)"
apply (frule lt_nat_in_nat, erule nat_succI)
apply (erule rev_mp) (*prepare the induction*)
apply (induct_tac m)
apply (auto intro: cpo_trans simp add: le_iff)
done

(*----------------------------------------------------------------------*)
(* Theorems about pcpos and bottom.                                     *)
(*----------------------------------------------------------------------*)

lemma pcpoI:
    "[|!!y. y \<in> set(D)==>rel(D,x,y); x \<in> set(D); cpo(D)|]==>pcpo(D)"
by (simp add: pcpo_def, auto)

lemma pcpo_cpo [TC]: "pcpo(D) ==> cpo(D)"
by (simp add: pcpo_def)

lemma pcpo_bot_ex1:
    "pcpo(D) ==> \<exists>! x. x \<in> set(D) & (\<forall>y \<in> set(D). rel(D,x,y))"
apply (simp add: pcpo_def)
apply (blast intro: cpo_antisym)
done

lemma bot_least [TC]:
    "[| pcpo(D); y \<in> set(D)|] ==> rel(D,bot(D),y)"
apply (simp add: bot_def)
apply (best intro: pcpo_bot_ex1 [THEN theI2])
done

lemma bot_in [TC]:
    "pcpo(D) ==> bot(D):set(D)"
apply (simp add: bot_def)
apply (best intro: pcpo_bot_ex1 [THEN theI2])
done

lemma bot_unique:
    "[| pcpo(D); x \<in> set(D); !!y. y \<in> set(D) ==> rel(D,x,y)|] ==> x = bot(D)"
by (blast intro: cpo_antisym pcpo_cpo bot_in bot_least)

(*----------------------------------------------------------------------*)
(* Constant chains and lubs and cpos.                                   *)
(*----------------------------------------------------------------------*)

lemma chain_const: "[|x \<in> set(D); cpo(D)|] ==> chain(D,(\<lambda>n \<in> nat. x))"
by (simp add: chain_def)

lemma islub_const:
   "[|x \<in> set(D); cpo(D)|] ==> islub(D,(\<lambda>n \<in> nat. x),x)"
by (simp add: islub_def isub_def, blast)

lemma lub_const: "[|x \<in> set(D); cpo(D)|] ==> lub(D,\<lambda>n \<in> nat. x) = x"
by (blast intro: islub_unique cpo_lub chain_const islub_const)

(*----------------------------------------------------------------------*)
(* Taking the suffix of chains has no effect on ub's.                   *)
(*----------------------------------------------------------------------*)

lemma isub_suffix:
    "[| chain(D,X); cpo(D) |] ==> isub(D,suffix(X,n),x) <-> isub(D,X,x)"
apply (simp add: isub_def suffix_def, safe)
apply (drule_tac x = na in bspec)
apply (auto intro: cpo_trans chain_rel_gen_add)
done

lemma islub_suffix:
  "[|chain(D,X); cpo(D)|] ==> islub(D,suffix(X,n),x) <-> islub(D,X,x)"
by (simp add: islub_def isub_suffix)

lemma lub_suffix:
    "[|chain(D,X); cpo(D)|] ==> lub(D,suffix(X,n)) = lub(D,X)"
by (simp add: lub_def islub_suffix)

(*----------------------------------------------------------------------*)
(* Dominate and subchain.                                               *)
(*----------------------------------------------------------------------*)

lemma dominateI:
  "[| !!m. m \<in> nat ==> n(m):nat; !!m. m \<in> nat ==> rel(D,X`m,Y`n(m))|] 
   ==> dominate(D,X,Y)"
by (simp add: dominate_def, blast)

lemma dominate_isub:
  "[|dominate(D,X,Y); isub(D,Y,x); cpo(D);
     X \<in> nat->set(D); Y \<in> nat->set(D)|] ==> isub(D,X,x)"
apply (simp add: isub_def dominate_def)
apply (blast intro: cpo_trans intro!: apply_funtype)
done

lemma dominate_islub:
  "[|dominate(D,X,Y); islub(D,X,x); islub(D,Y,y); cpo(D);
     X \<in> nat->set(D); Y \<in> nat->set(D)|] ==> rel(D,x,y)"
apply (simp add: islub_def)
apply (blast intro: dominate_isub)
done

lemma subchain_isub:
     "[|subchain(Y,X); isub(D,X,x)|] ==> isub(D,Y,x)"
by (simp add: isub_def subchain_def, force)

lemma dominate_islub_eq:
     "[|dominate(D,X,Y); subchain(Y,X); islub(D,X,x); islub(D,Y,y); cpo(D);
        X \<in> nat->set(D); Y \<in> nat->set(D)|] ==> x = y"
by (blast intro: cpo_antisym dominate_islub islub_least subchain_isub 
                 islub_isub islub_in)


(*----------------------------------------------------------------------*)
(* Matrix.                                                              *)
(*----------------------------------------------------------------------*)

lemma matrix_fun: "matrix(D,M) ==> M \<in> nat -> (nat -> set(D))"
by (simp add: matrix_def)

lemma matrix_in_fun: "[|matrix(D,M); n \<in> nat|] ==> M`n \<in> nat -> set(D)"
by (blast intro: apply_funtype matrix_fun)

lemma matrix_in: "[|matrix(D,M); n \<in> nat; m \<in> nat|] ==> M`n`m \<in> set(D)"
by (blast intro: apply_funtype matrix_in_fun)

lemma matrix_rel_1_0:
    "[|matrix(D,M); n \<in> nat; m \<in> nat|] ==> rel(D,M`n`m,M`succ(n)`m)"
by (simp add: matrix_def)

lemma matrix_rel_0_1:
    "[|matrix(D,M); n \<in> nat; m \<in> nat|] ==> rel(D,M`n`m,M`n`succ(m))"
by (simp add: matrix_def)

lemma matrix_rel_1_1:
    "[|matrix(D,M); n \<in> nat; m \<in> nat|] ==> rel(D,M`n`m,M`succ(n)`succ(m))"
by (simp add: matrix_def)

lemma fun_swap: "f \<in> X->Y->Z ==> (\<lambda>y \<in> Y. \<lambda>x \<in> X. f`x`y):Y->X->Z"
by (blast intro: lam_type apply_funtype)

lemma matrix_sym_axis:
    "matrix(D,M) ==> matrix(D,\<lambda>m \<in> nat. \<lambda>n \<in> nat. M`n`m)"
by (simp add: matrix_def fun_swap)

lemma matrix_chain_diag:
    "matrix(D,M) ==> chain(D,\<lambda>n \<in> nat. M`n`n)"
apply (simp add: chain_def)
apply (auto intro: lam_type matrix_in matrix_rel_1_1)
done

lemma matrix_chain_left:
    "[|matrix(D,M); n \<in> nat|] ==> chain(D,M`n)"
apply (unfold chain_def)
apply (auto intro: matrix_fun [THEN apply_type] matrix_in matrix_rel_0_1)
done

lemma matrix_chain_right:
    "[|matrix(D,M); m \<in> nat|] ==> chain(D,\<lambda>n \<in> nat. M`n`m)"
apply (simp add: chain_def)
apply (auto intro: lam_type matrix_in matrix_rel_1_0)
done

lemma matrix_chainI:
  assumes xprem: "!!x. x \<in> nat==>chain(D,M`x)"
      and yprem: "!!y. y \<in> nat==>chain(D,\<lambda>x \<in> nat. M`x`y)"
      and Mfun:  "M \<in> nat->nat->set(D)"
      and cpoD:  "cpo(D)"
  shows "matrix(D,M)"
apply (simp add: matrix_def, safe)
apply (rule Mfun)
apply (cut_tac y1 = m and n = n in yprem [THEN chain_rel], simp+)
apply (simp add: chain_rel xprem)
apply (rule cpo_trans [OF cpoD])
apply (cut_tac y1 = m and n = n in yprem [THEN chain_rel], simp+)
apply (simp_all add: chain_fun [THEN apply_type] xprem)
done

lemma lemma_rel_rel:
     "[|m \<in> nat; rel(D, (\<lambda>n \<in> nat. M`n`n)`m, y)|] ==> rel(D,M`m`m, y)"
by simp

lemma lemma2:
     "[|x \<in> nat; m \<in> nat; rel(D,(\<lambda>n \<in> nat. M`n`m1)`x,(\<lambda>n \<in> nat. M`n`m1)`m)|]
      ==> rel(D,M`x`m1,M`m`m1)"
by simp

lemma isub_lemma:
    "[|isub(D, \<lambda>n \<in> nat. M`n`n, y); matrix(D,M); cpo(D)|] 
     ==> isub(D, \<lambda>n \<in> nat. lub(D,\<lambda>m \<in> nat. M`n`m), y)"
apply (unfold isub_def, safe)
apply (simp (no_asm_simp))
apply (frule matrix_fun [THEN apply_type], assumption)
apply (simp (no_asm_simp))
apply (rule matrix_chain_left [THEN cpo_lub, THEN islub_least], assumption+)
apply (unfold isub_def, safe)
(*???VERY indirect proof: beta-redexes could be simplified now!*)
apply (rename_tac k n)
apply (case_tac "k le n")
apply (rule cpo_trans, assumption)
apply (rule lemma2)
apply (rule_tac [4] lemma_rel_rel)
prefer 5 apply blast
apply (assumption | rule chain_rel_gen matrix_chain_right matrix_in isubD1)+
txt{*opposite case*}
apply (rule cpo_trans, assumption)
apply (rule not_le_iff_lt [THEN iffD1, THEN leI, THEN chain_rel_gen])
prefer 3 apply assumption
apply (assumption | rule nat_into_Ord matrix_chain_left)+
apply (rule lemma_rel_rel)
apply (simp_all add: matrix_in)
done

lemma matrix_chain_lub:
    "[|matrix(D,M); cpo(D)|] ==> chain(D,\<lambda>n \<in> nat. lub(D,\<lambda>m \<in> nat. M`n`m))"
apply (simp add: chain_def, safe)
apply (rule lam_type)
apply (rule islub_in)
apply (rule cpo_lub)
prefer 2 apply assumption
apply (rule chainI)
apply (rule lam_type)
apply (simp_all add: matrix_in)
apply (rule matrix_rel_0_1, assumption+)
apply (simp add: matrix_chain_left [THEN chain_fun, THEN eta])
apply (rule dominate_islub)
apply (rule_tac [3] cpo_lub)
apply (rule_tac [2] cpo_lub)
apply (simp add: dominate_def)
apply (blast intro: matrix_rel_1_0)
apply (simp_all add: matrix_chain_left nat_succI chain_fun)
done

lemma isub_eq:
    "[|matrix(D,M); cpo(D)|] 
     ==> isub(D,(\<lambda>n \<in> nat. lub(D,\<lambda>m \<in> nat. M`n`m)),y) <->
         isub(D,(\<lambda>n \<in> nat. M`n`n),y)"
apply (rule iffI)
apply (rule dominate_isub)
prefer 2 apply assumption
apply (simp add: dominate_def)
apply (rule ballI)
apply (rule bexI, auto)
apply (simp add: matrix_chain_left [THEN chain_fun, THEN eta])
apply (rule islub_ub)
apply (rule cpo_lub)
apply (simp_all add: matrix_chain_left matrix_chain_diag chain_fun 
                     matrix_chain_lub isub_lemma)
done

lemma lemma1:
    "lub(D,(\<lambda>n \<in> nat. lub(D,\<lambda>m \<in> nat. M`n`m))) =
     (THE x. islub(D, (\<lambda>n \<in> nat. lub(D,\<lambda>m \<in> nat. M`n`m)), x))"
by (simp add: lub_def)

lemma lemma2:
    "lub(D,(\<lambda>n \<in> nat. M`n`n)) =
     (THE x. islub(D, (\<lambda>n \<in> nat. M`n`n), x))"
by (simp add: lub_def)

lemma lub_matrix_diag:
    "[|matrix(D,M); cpo(D)|] 
     ==> lub(D,(\<lambda>n \<in> nat. lub(D,\<lambda>m \<in> nat. M`n`m))) =
         lub(D,(\<lambda>n \<in> nat. M`n`n))"
apply (simp (no_asm) add: lemma1 lemma2)
apply (simp add: islub_def isub_eq)
done

lemma lub_matrix_diag_sym:
    "[|matrix(D,M); cpo(D)|] 
     ==> lub(D,(\<lambda>m \<in> nat. lub(D,\<lambda>n \<in> nat. M`n`m))) =
         lub(D,(\<lambda>n \<in> nat. M`n`n))"
by (drule matrix_sym_axis [THEN lub_matrix_diag], auto)

(*----------------------------------------------------------------------*)
(* I/E/D rules for mono and cont.                                       *)
(*----------------------------------------------------------------------*)

lemma monoI:
    "[|f \<in> set(D)->set(E);
       !!x y. [|rel(D,x,y); x \<in> set(D); y \<in> set(D)|] ==> rel(E,f`x,f`y)|] 
     ==> f \<in> mono(D,E)"
by (simp add: mono_def)

lemma mono_fun: "f \<in> mono(D,E) ==> f \<in> set(D)->set(E)"
by (simp add: mono_def)

lemma mono_map: "[|f \<in> mono(D,E); x \<in> set(D)|] ==> f`x \<in> set(E)"
by (blast intro!: mono_fun [THEN apply_type])

lemma mono_mono:
    "[|f \<in> mono(D,E); rel(D,x,y); x \<in> set(D); y \<in> set(D)|] ==> rel(E,f`x,f`y)"
by (simp add: mono_def)

lemma contI:
    "[|f \<in> set(D)->set(E);
       !!x y. [|rel(D,x,y); x \<in> set(D); y \<in> set(D)|] ==> rel(E,f`x,f`y);
       !!X. chain(D,X) ==> f`lub(D,X) = lub(E,\<lambda>n \<in> nat. f`(X`n))|] 
     ==> f \<in> cont(D,E)"
by (simp add: cont_def mono_def)

lemma cont2mono: "f \<in> cont(D,E) ==> f \<in> mono(D,E)"
by (simp add: cont_def)

lemma cont_fun [TC] : "f \<in> cont(D,E) ==> f \<in> set(D)->set(E)"
apply (simp add: cont_def)
apply (rule mono_fun, blast)
done

lemma cont_map [TC]: "[|f \<in> cont(D,E); x \<in> set(D)|] ==> f`x \<in> set(E)"
by (blast intro!: cont_fun [THEN apply_type])

declare comp_fun [TC]

lemma cont_mono:
    "[|f \<in> cont(D,E); rel(D,x,y); x \<in> set(D); y \<in> set(D)|] ==> rel(E,f`x,f`y)"
apply (simp add: cont_def)
apply (blast intro!: mono_mono)
done

lemma cont_lub:
   "[|f \<in> cont(D,E); chain(D,X)|] ==> f`(lub(D,X)) = lub(E,\<lambda>n \<in> nat. f`(X`n))"
by (simp add: cont_def)

(*----------------------------------------------------------------------*)
(* Continuity and chains.                                               *)
(*----------------------------------------------------------------------*)

lemma mono_chain:
     "[|f \<in> mono(D,E); chain(D,X)|] ==> chain(E,\<lambda>n \<in> nat. f`(X`n))"
apply (simp (no_asm) add: chain_def)
apply (blast intro: lam_type mono_map chain_in mono_mono chain_rel)
done

lemma cont_chain:
     "[|f \<in> cont(D,E); chain(D,X)|] ==> chain(E,\<lambda>n \<in> nat. f`(X`n))"
by (blast intro: mono_chain cont2mono)

(*----------------------------------------------------------------------*)
(* I/E/D rules about (set+rel) cf, the continuous function space.       *)
(*----------------------------------------------------------------------*)

(* The following development more difficult with cpo-as-relation approach. *)

lemma cf_cont: "f \<in> set(cf(D,E)) ==> f \<in> cont(D,E)"
by (simp add: set_def cf_def)

lemma cont_cf: (* Non-trivial with relation *)
    "f \<in> cont(D,E) ==> f \<in> set(cf(D,E))"
by (simp add: set_def cf_def)

(* rel_cf originally an equality. Now stated as two rules. Seemed easiest. *)

lemma rel_cfI:
    "[|!!x. x \<in> set(D) ==> rel(E,f`x,g`x); f \<in> cont(D,E); g \<in> cont(D,E)|] 
     ==> rel(cf(D,E),f,g)"
by (simp add: rel_I cf_def)

lemma rel_cf: "[|rel(cf(D,E),f,g); x \<in> set(D)|] ==> rel(E,f`x,g`x)"
by (simp add: rel_def cf_def)

(*----------------------------------------------------------------------*)
(* Theorems about the continuous function space.                        *)
(*----------------------------------------------------------------------*)

lemma chain_cf:
    "[| chain(cf(D,E),X); x \<in> set(D)|] ==> chain(E,\<lambda>n \<in> nat. X`n`x)"
apply (rule chainI)
apply (blast intro: lam_type apply_funtype cont_fun cf_cont chain_in, simp)
apply (blast intro: rel_cf chain_rel)
done

lemma matrix_lemma:
    "[|chain(cf(D,E),X); chain(D,Xa); cpo(D); cpo(E) |] 
     ==> matrix(E,\<lambda>x \<in> nat. \<lambda>xa \<in> nat. X`x`(Xa`xa))"
apply (rule matrix_chainI, auto)
apply (rule chainI)
apply (blast intro: lam_type apply_funtype cont_fun cf_cont chain_in, simp)
apply (blast intro: cont_mono nat_succI chain_rel cf_cont chain_in)
apply (rule chainI)
apply (blast intro: lam_type apply_funtype cont_fun cf_cont chain_in, simp)
apply (rule rel_cf)
apply (simp_all add: chain_in chain_rel)
apply (blast intro: lam_type apply_funtype cont_fun cf_cont chain_in)
done

lemma chain_cf_lub_cont:
    "[|chain(cf(D,E),X); cpo(D); cpo(E) |] 
     ==> (\<lambda>x \<in> set(D). lub(E, \<lambda>n \<in> nat. X ` n ` x)) \<in> cont(D, E)"
apply (rule contI)
apply (rule lam_type)
apply (assumption | rule chain_cf [THEN cpo_lub, THEN islub_in])+
apply simp
apply (rule dominate_islub)
apply (erule_tac [2] chain_cf [THEN cpo_lub], simp_all)+
apply (rule dominateI, assumption, simp)
apply (assumption | rule chain_in [THEN cf_cont, THEN cont_mono])+
apply (assumption | rule chain_cf [THEN chain_fun])+
apply (simp add: cpo_lub [THEN islub_in] 
                 chain_in [THEN cf_cont, THEN cont_lub])
apply (frule matrix_lemma [THEN lub_matrix_diag], assumption+)
apply (simp add: chain_in [THEN beta])
apply (drule matrix_lemma [THEN lub_matrix_diag_sym], auto)
done

lemma islub_cf:
    "[| chain(cf(D,E),X); cpo(D); cpo(E)|] 
     ==> islub(cf(D,E), X, \<lambda>x \<in> set(D). lub(E,\<lambda>n \<in> nat. X`n`x))"
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
    "[| cpo(D); cpo(E)|] ==> cpo(cf(D,E))"
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
     "[| chain(cf(D,E),X); cpo(D); cpo(E)|] 
      ==> lub(cf(D,E), X) = (\<lambda>x \<in> set(D). lub(E,\<lambda>n \<in> nat. X`n`x))"
by (blast intro: islub_unique cpo_lub islub_cf cpo_cf)


lemma const_cont [TC]:
     "[|y \<in> set(E); cpo(D); cpo(E)|] ==> (\<lambda>x \<in> set(D).y) \<in> cont(D,E)"
apply (rule contI)
prefer 2 apply simp
apply (blast intro: lam_type)
apply (simp add: chain_in cpo_lub [THEN islub_in] lub_const)
done

lemma cf_least:
    "[|cpo(D); pcpo(E); y \<in> cont(D,E)|]==>rel(cf(D,E),(\<lambda>x \<in> set(D).bot(E)),y)"
apply (rule rel_cfI, simp, typecheck)
done

lemma pcpo_cf:
    "[|cpo(D); pcpo(E)|] ==> pcpo(cf(D,E))"
apply (rule pcpoI)
apply (assumption | 
       rule cf_least bot_in const_cont [THEN cont_cf] cf_cont cpo_cf pcpo_cpo)+
done

lemma bot_cf:
    "[|cpo(D); pcpo(E)|] ==> bot(cf(D,E)) = (\<lambda>x \<in> set(D).bot(E))"
by (blast intro: bot_unique [symmetric] pcpo_cf cf_least 
                 bot_in [THEN const_cont, THEN cont_cf] cf_cont pcpo_cpo)

(*----------------------------------------------------------------------*)
(* Identity and composition.                                            *)
(*----------------------------------------------------------------------*)

lemma id_cont [TC,intro!]:
    "cpo(D) ==> id(set(D)) \<in> cont(D,D)"
by (simp add: id_type contI cpo_lub [THEN islub_in] chain_fun [THEN eta])

lemmas comp_cont_apply =  cont_fun [THEN comp_fun_apply]

lemma comp_pres_cont [TC]:
    "[| f \<in> cont(D',E); g \<in> cont(D,D'); cpo(D)|] ==> f O g \<in> cont(D,E)"
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
    "[| f \<in> cont(D',E); g \<in> cont(D,D'); f':cont(D',E); g':cont(D,D');
        rel(cf(D',E),f,f'); rel(cf(D,D'),g,g'); cpo(D); cpo(E) |] 
     ==> rel(cf(D,E),f O g,f' O g')"
apply (rule rel_cfI) 
apply (subst comp_cont_apply)
apply (rule_tac [3] comp_cont_apply [THEN ssubst])
apply (rule_tac [5] cpo_trans)
apply (assumption | rule rel_cf cont_mono cont_map comp_pres_cont)+
done

lemma chain_cf_comp:
    "[| chain(cf(D',E),X); chain(cf(D,D'),Y); cpo(D); cpo(E)|] 
     ==> chain(cf(D,E),\<lambda>n \<in> nat. X`n O Y`n)"
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
    "[| chain(cf(D',E),X); chain(cf(D,D'),Y); cpo(D); cpo(D'); cpo(E)|] 
     ==> lub(cf(D',E),X) O lub(cf(D,D'),Y) = lub(cf(D,E),\<lambda>n \<in> nat. X`n O Y`n)"
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
    "[| e \<in> cont(D,E); p \<in> cont(E,D); p O e = id(set(D));
        rel(cf(E,E))(e O p)(id(set(E)))|] ==> projpair(D,E,e,p)"
by (simp add: projpair_def)

lemma projpair_e_cont: "projpair(D,E,e,p) ==> e \<in> cont(D,E)"
by (simp add: projpair_def)

lemma projpair_p_cont: "projpair(D,E,e,p) ==> p \<in> cont(E,D)"
by (simp add: projpair_def)

lemma projpair_ep_cont: "projpair(D,E,e,p) ==> e \<in> cont(D,E) & p \<in> cont(E,D)"
by (simp add: projpair_def)

lemma projpair_eq: "projpair(D,E,e,p) ==> p O e = id(set(D))"
by (simp add: projpair_def)

lemma projpair_rel: "projpair(D,E,e,p) ==> rel(cf(E,E))(e O p)(id(set(E)))"
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

lemma lemma1:
    "[|cpo(D); cpo(E); projpair(D,E,e,p); projpair(D,E,e',p');
       rel(cf(D,E),e,e')|] ==> rel(cf(E,D),p',p)"
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
apply (rule_tac P = "%x. rel (cf (E,D),p O e' O p',x)"
         in projpair_p_cont [THEN cont_fun, THEN comp_id, THEN subst],
       assumption)
apply (rule comp_mono)
apply (blast intro: cpo_cf cont_cf comp_pres_cont projpair_rel
             dest: projpair_ep_cont)+
done

text{*Proof's very like the previous one.  Is there a pattern that
      could be exploited?*}
lemma lemma2:
    "[|cpo(D); cpo(E); projpair(D,E,e,p); projpair(D,E,e',p');
       rel(cf(E,D),p',p)|] ==> rel(cf(D,E),e,e')"
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
apply (rule_tac P = "%x. rel (cf (D,E), (e O p) O e',x)"
         in projpair_e_cont [THEN cont_fun, THEN id_comp, THEN subst],
       assumption)
apply (blast intro: cpo_cf cont_cf comp_pres_cont projpair_rel comp_mono
             dest: projpair_ep_cont)+
done


lemma projpair_unique:
    "[|cpo(D); cpo(E); projpair(D,E,e,p); projpair(D,E,e',p')|] 
     ==> (e=e')<->(p=p')"
by (blast intro: cpo_antisym lemma1 lemma2 cpo_cf cont_cf
          dest: projpair_ep_cont)

(* Slightly different, more asms, since THE chooses the unique element. *)

lemma embRp:
    "[|emb(D,E,e); cpo(D); cpo(E)|] ==> projpair(D,E,e,Rp(D,E,e))"
apply (simp add: emb_def Rp_def)
apply (blast intro: theI2 projpair_unique [THEN iffD1])
done

lemma embI: "projpair(D,E,e,p) ==> emb(D,E,e)"
by (simp add: emb_def, auto)

lemma Rp_unique: "[|projpair(D,E,e,p); cpo(D); cpo(E)|] ==> Rp(D,E,e) = p"
by (blast intro: embRp embI projpair_unique [THEN iffD1])

lemma emb_cont [TC]: "emb(D,E,e) ==> e \<in> cont(D,E)"
apply (simp add: emb_def)
apply (blast intro: projpair_e_cont)
done

(* The following three theorems have cpo asms due to THE (uniqueness). *)

lemmas Rp_cont [TC] = embRp [THEN projpair_p_cont, standard]
lemmas embRp_eq = embRp [THEN projpair_eq, standard]
lemmas embRp_rel = embRp [THEN projpair_rel, standard]


lemma embRp_eq_thm:
    "[|emb(D,E,e); x \<in> set(D); cpo(D); cpo(E)|] ==> Rp(D,E,e)`(e`x) = x"
apply (rule comp_fun_apply [THEN subst])
apply (assumption | rule Rp_cont emb_cont cont_fun)+
apply (subst embRp_eq)
apply (auto intro: id_conv)
done


(*----------------------------------------------------------------------*)
(* The identity embedding.                                              *)
(*----------------------------------------------------------------------*)

lemma projpair_id:
    "cpo(D) ==> projpair(D,D,id(set(D)),id(set(D)))"
apply (simp add: projpair_def)
apply (blast intro: cpo_cf cont_cf)
done

lemma emb_id:
    "cpo(D) ==> emb(D,D,id(set(D)))"
by (auto intro: embI projpair_id)

lemma Rp_id:
    "cpo(D) ==> Rp(D,D,id(set(D))) = id(set(D))"
by (auto intro: Rp_unique projpair_id)


(*----------------------------------------------------------------------*)
(* Composition preserves embeddings.                                    *)
(*----------------------------------------------------------------------*)

(* Considerably shorter, only partly due to a simpler comp_assoc. *)
(* Proof in HOL-ST: 70 lines (minus 14 due to comp_assoc complication). *)
(* Proof in Isa/ZF: 23 lines (compared to 56: 60% reduction). *)

lemma comp_lemma:
    "[|emb(D,D',e); emb(D',E,e'); cpo(D); cpo(D'); cpo(E)|] 
     ==> projpair(D,E,e' O e,(Rp(D,D',e)) O (Rp(D',E,e')))"
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
    "x:(\<Pi>n \<in> nat. set(DD`n)) ==> x \<in> set(iprod(DD))"
by (simp add: set_def iprod_def)

lemma iprodE:
    "x \<in> set(iprod(DD)) ==> x:(\<Pi>n \<in> nat. set(DD`n))"
by (simp add: set_def iprod_def)

(* Contains typing conditions in contrast to HOL-ST *)

lemma rel_iprodI:
    "[|!!n. n \<in> nat ==> rel(DD`n,f`n,g`n); f:(\<Pi>n \<in> nat. set(DD`n));
       g:(\<Pi>n \<in> nat. set(DD`n))|] ==> rel(iprod(DD),f,g)"
by (simp add: iprod_def rel_I)

lemma rel_iprodE:
    "[|rel(iprod(DD),f,g); n \<in> nat|] ==> rel(DD`n,f`n,g`n)"
by (simp add: iprod_def rel_def)

lemma chain_iprod:
    "[|chain(iprod(DD),X);  !!n. n \<in> nat ==> cpo(DD`n); n \<in> nat|] 
     ==> chain(DD`n,\<lambda>m \<in> nat. X`m`n)"
apply (unfold chain_def, safe)
apply (rule lam_type)
apply (rule apply_type)
apply (rule iprodE)
apply (blast intro: apply_funtype, assumption)
apply (simp add: rel_iprodE)
done

lemma islub_iprod:
    "[|chain(iprod(DD),X);  !!n. n \<in> nat ==> cpo(DD`n)|] 
     ==> islub(iprod(DD),X,\<lambda>n \<in> nat. lub(DD`n,\<lambda>m \<in> nat. X`m`n))"
apply (simp add: islub_def isub_def, safe)
apply (rule iprodI)
apply (blast intro: lam_type chain_iprod [THEN cpo_lub, THEN islub_in])
apply (rule rel_iprodI, simp)
(*looks like something should be inserted into the assumptions!*)
apply (rule_tac P = "%t. rel (DD`na,t,lub (DD`na,\<lambda>x \<in> nat. X`x`na))"
            and b1 = "%n. X`n`na" in beta [THEN subst])
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
    "(!!n. n \<in> nat ==> cpo(DD`n)) ==> cpo(iprod(DD))"
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
    "[|chain(iprod(DD),X);  !!n. n \<in> nat ==> cpo(DD`n)|]
     ==> lub(iprod(DD),X) = (\<lambda>n \<in> nat. lub(DD`n,\<lambda>m \<in> nat. X`m`n))"
by (blast intro: cpo_lub [THEN islub_unique] islub_iprod cpo_iprod)


(*----------------------------------------------------------------------*)
(* The notion of subcpo.                                                *)
(*----------------------------------------------------------------------*)

lemma subcpoI:
    "[|set(D)<=set(E);
       !!x y. [|x \<in> set(D); y \<in> set(D)|] ==> rel(D,x,y)<->rel(E,x,y);
       !!X. chain(D,X) ==> lub(E,X) \<in> set(D)|] ==> subcpo(D,E)"
by (simp add: subcpo_def)

lemma subcpo_subset: "subcpo(D,E) ==> set(D)<=set(E)"
by (simp add: subcpo_def)

lemma subcpo_rel_eq:
    "[|subcpo(D,E); x \<in> set(D); y \<in> set(D)|] ==> rel(D,x,y)<->rel(E,x,y)"
by (simp add: subcpo_def)

lemmas subcpo_relD1 = subcpo_rel_eq [THEN iffD1]
lemmas subcpo_relD2 = subcpo_rel_eq [THEN iffD2]

lemma subcpo_lub: "[|subcpo(D,E); chain(D,X)|] ==> lub(E,X) \<in> set(D)"
by (simp add: subcpo_def)

lemma chain_subcpo: "[|subcpo(D,E); chain(D,X)|] ==> chain(E,X)"
by (blast intro: Pi_type [THEN chainI] chain_fun subcpo_relD1
                    subcpo_subset [THEN subsetD]
                    chain_in chain_rel)

lemma ub_subcpo: "[|subcpo(D,E); chain(D,X); isub(D,X,x)|] ==> isub(E,X,x)"
by (blast intro: isubI subcpo_relD1 subcpo_relD1 chain_in isubD1 isubD2
                    subcpo_subset [THEN subsetD] chain_in chain_rel)

lemma islub_subcpo:
     "[|subcpo(D,E); cpo(E); chain(D,X)|] ==> islub(D,X,lub(E,X))"
by (blast intro: islubI isubI subcpo_lub subcpo_relD2 chain_in islub_ub
                 islub_least cpo_lub chain_subcpo isubD1 ub_subcpo)

lemma subcpo_cpo: "[|subcpo(D,E); cpo(E)|] ==> cpo(D)"
apply (assumption | rule cpoI poI)+
apply (simp add: subcpo_rel_eq)
apply (assumption | rule cpo_refl subcpo_subset [THEN subsetD])+
apply (rotate_tac -3)
apply (simp add: subcpo_rel_eq)
apply (blast intro: subcpo_subset [THEN subsetD] cpo_trans)
(* Changing the order of the assumptions, otherwise simp doesn't work. *)
apply (rotate_tac -2)
apply (simp add: subcpo_rel_eq)
apply (blast intro: cpo_antisym subcpo_subset [THEN subsetD])
apply (fast intro: islub_subcpo)
done

lemma lub_subcpo: "[|subcpo(D,E); cpo(E); chain(D,X)|] ==> lub(D,X) = lub(E,X)"
by (blast intro: cpo_lub [THEN islub_unique] islub_subcpo subcpo_cpo)

(*----------------------------------------------------------------------*)
(* Making subcpos using mkcpo.                                          *)
(*----------------------------------------------------------------------*)

lemma mkcpoI: "[|x \<in> set(D); P(x)|] ==> x \<in> set(mkcpo(D,P))"
by (simp add: set_def mkcpo_def)

lemma mkcpoD1: "x \<in> set(mkcpo(D,P))==> x \<in> set(D)"
by (simp add: set_def mkcpo_def)

lemma mkcpoD2: "x \<in> set(mkcpo(D,P))==> P(x)"
by (simp add: set_def mkcpo_def)

lemma rel_mkcpoE: "rel(mkcpo(D,P),x,y) ==> rel(D,x,y)"
by (simp add: rel_def mkcpo_def)

lemma rel_mkcpo:
    "[|x \<in> set(D); y \<in> set(D)|] ==> rel(mkcpo(D,P),x,y) <-> rel(D,x,y)"
by (simp add: mkcpo_def rel_def set_def)

lemma chain_mkcpo:
    "chain(mkcpo(D,P),X) ==> chain(D,X)"
apply (rule chainI)
apply (blast intro: Pi_type chain_fun chain_in [THEN mkcpoD1])
apply (blast intro: rel_mkcpo [THEN iffD1] chain_rel mkcpoD1 chain_in)
done

lemma subcpo_mkcpo:
     "[|!!X. chain(mkcpo(D,P),X) ==> P(lub(D,X)); cpo(D)|]
      ==> subcpo(mkcpo(D,P),D)"
apply (intro subcpoI subsetI rel_mkcpo)
apply (erule mkcpoD1)+
apply (blast intro: mkcpoI cpo_lub [THEN islub_in] chain_mkcpo)
done

(*----------------------------------------------------------------------*)
(* Embedding projection chains of cpos.                                 *)
(*----------------------------------------------------------------------*)

lemma emb_chainI:
    "[|!!n. n \<in> nat ==> cpo(DD`n);
       !!n. n \<in> nat ==> emb(DD`n,DD`succ(n),ee`n)|] ==> emb_chain(DD,ee)"
by (simp add: emb_chain_def)

lemma emb_chain_cpo [TC]: "[|emb_chain(DD,ee); n \<in> nat|] ==> cpo(DD`n)"
by (simp add: emb_chain_def)

lemma emb_chain_emb:
    "[|emb_chain(DD,ee); n \<in> nat|] ==> emb(DD`n,DD`succ(n),ee`n)"
by (simp add: emb_chain_def)

(*----------------------------------------------------------------------*)
(* Dinf, the inverse Limit.                                             *)
(*----------------------------------------------------------------------*)

lemma DinfI:
    "[|x:(\<Pi>n \<in> nat. set(DD`n));
       !!n. n \<in> nat ==> Rp(DD`n,DD`succ(n),ee`n)`(x`succ(n)) = x`n|]
     ==> x \<in> set(Dinf(DD,ee))"
apply (simp add: Dinf_def)
apply (blast intro: mkcpoI iprodI)
done

lemma Dinf_prod: "x \<in> set(Dinf(DD,ee)) ==> x:(\<Pi>n \<in> nat. set(DD`n))"
apply (simp add: Dinf_def)
apply (erule mkcpoD1 [THEN iprodE])
done

lemma Dinf_eq:
    "[|x \<in> set(Dinf(DD,ee)); n \<in> nat|]
     ==> Rp(DD`n,DD`succ(n),ee`n)`(x`succ(n)) = x`n"
apply (simp add: Dinf_def)
apply (blast dest: mkcpoD2)
done

lemma rel_DinfI:
    "[|!!n. n \<in> nat ==> rel(DD`n,x`n,y`n);
       x:(\<Pi>n \<in> nat. set(DD`n)); y:(\<Pi>n \<in> nat. set(DD`n))|] 
     ==> rel(Dinf(DD,ee),x,y)"
apply (simp add: Dinf_def)
apply (blast intro: rel_mkcpo [THEN iffD2] rel_iprodI iprodI)
done

lemma rel_Dinf: "[|rel(Dinf(DD,ee),x,y); n \<in> nat|] ==> rel(DD`n,x`n,y`n)"
apply (simp add: Dinf_def)
apply (erule rel_mkcpoE [THEN rel_iprodE], assumption)
done

lemma chain_Dinf: "chain(Dinf(DD,ee),X) ==> chain(iprod(DD),X)"
apply (simp add: Dinf_def)
apply (erule chain_mkcpo)
done

lemma subcpo_Dinf:
    "emb_chain(DD,ee) ==> subcpo(Dinf(DD,ee),iprod(DD))"
apply (simp add: Dinf_def)
apply (rule subcpo_mkcpo)
apply (simp add: Dinf_def [symmetric])
apply (rule ballI)
apply (subst lub_iprod)
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

lemma cpo_Dinf: "emb_chain(DD,ee) ==> cpo(Dinf(DD,ee))"
apply (rule subcpo_cpo)
apply (erule subcpo_Dinf)
apply (auto intro: cpo_iprod emb_chain_cpo)
done

(* Again and again the proofs are much easier to WRITE in Isabelle, but
  the proof steps are essentially the same (I think). *)

lemma lub_Dinf:
    "[|chain(Dinf(DD,ee),X); emb_chain(DD,ee)|]
     ==> lub(Dinf(DD,ee),X) = (\<lambda>n \<in> nat. lub(DD`n,\<lambda>m \<in> nat. X`m`n))"
apply (subst subcpo_Dinf [THEN lub_subcpo])
apply (auto intro: cpo_iprod emb_chain_cpo lub_iprod chain_Dinf)
done

(*----------------------------------------------------------------------*)
(* Generalising embedddings D_m -> D_{m+1} to embeddings D_m -> D_n,    *)
(* defined as eps(DD,ee,m,n), via e_less and e_gr.                      *)
(*----------------------------------------------------------------------*)

lemma e_less_eq:
    "m \<in> nat ==> e_less(DD,ee,m,m) = id(set(DD`m))"
by (simp add: e_less_def diff_self_eq_0)

lemma lemma_succ_sub: "succ(m#+n)#-m = succ(natify(n))"
by simp

lemma e_less_add:
     "e_less(DD,ee,m,succ(m#+k)) = (ee`(m#+k))O(e_less(DD,ee,m,m#+k))"
by (simp add: e_less_def)

lemma le_exists:
    "[| m le n;  !!x. [|n=m#+x; x \<in> nat|] ==> Q;  n \<in> nat |] ==> Q"
apply (drule less_imp_succ_add, auto)
done

lemma e_less_le: "[| m le n;  n \<in> nat |] 
     ==> e_less(DD,ee,m,succ(n)) = ee`n O e_less(DD,ee,m,n)"
apply (rule le_exists, assumption)
apply (simp add: e_less_add, assumption)
done

(* All theorems assume variables m and n are natural numbers. *)

lemma e_less_succ:
     "m \<in> nat ==> e_less(DD,ee,m,succ(m)) = ee`m O id(set(DD`m))"
by (simp add: e_less_le e_less_eq)

lemma e_less_succ_emb:
    "[|!!n. n \<in> nat ==> emb(DD`n,DD`succ(n),ee`n); m \<in> nat|] 
     ==> e_less(DD,ee,m,succ(m)) = ee`m"
apply (simp add: e_less_succ)
apply (blast intro: emb_cont cont_fun comp_id)
done

(* Compare this proof with the HOL one, here we do type checking. *)
(* In any case the one below was very easy to write. *)

lemma emb_e_less_add:
     "[| emb_chain(DD,ee); m \<in> nat |]
      ==> emb(DD`m, DD`(m#+k), e_less(DD,ee,m,m#+k))"
apply (subgoal_tac "emb (DD`m, DD` (m#+natify (k)), 
                         e_less (DD,ee,m,m#+natify (k))) ")
apply (rule_tac [2] n = "natify (k) " in nat_induct)
apply (simp_all add: e_less_eq)
apply (assumption | rule emb_id emb_chain_cpo)+
apply (simp add: e_less_add)
apply (auto intro: emb_comp emb_chain_emb emb_chain_cpo)
done

lemma emb_e_less:
     "[| m le n;  emb_chain(DD,ee);  n \<in> nat |] 
      ==> emb(DD`m, DD`n, e_less(DD,ee,m,n))"
apply (frule lt_nat_in_nat)
apply (erule nat_succI)
(* same proof as e_less_le *)
apply (rule le_exists, assumption)
apply (simp add: emb_e_less_add, assumption)
done

lemma comp_mono_eq: "[|f=f'; g=g'|] ==> f O g = f' O g'"
by simp

(* Note the object-level implication for induction on k. This
   must be removed later to allow the theorems to be used for simp.
   Therefore this theorem is only a lemma. *)

lemma e_less_split_add_lemma [rule_format]:
    "[| emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat|] 
     ==> n le k -->
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
    "[| n le k; emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat|] 
     ==> e_less(DD,ee,m,m#+k) = e_less(DD,ee,m#+n,m#+k) O e_less(DD,ee,m,m#+n)"
by (blast intro: e_less_split_add_lemma)

lemma e_gr_eq:
    "m \<in> nat ==> e_gr(DD,ee,m,m) = id(set(DD`m))"
apply (simp add: e_gr_def)
apply (simp add: diff_self_eq_0)
done

lemma e_gr_add:
    "[|n \<in> nat; k \<in> nat|] 
     ==> e_gr(DD,ee,succ(n#+k),n) =
         e_gr(DD,ee,n#+k,n) O Rp(DD`(n#+k),DD`succ(n#+k),ee`(n#+k))"
by (simp add: e_gr_def)

lemma e_gr_le:
     "[|n le m; m \<in> nat; n \<in> nat|]
      ==> e_gr(DD,ee,succ(m),n) = e_gr(DD,ee,m,n) O Rp(DD`m,DD`succ(m),ee`m)"
apply (erule le_exists)
apply (simp add: e_gr_add, assumption+)
done

lemma e_gr_succ:
 "m \<in> nat ==> e_gr(DD,ee,succ(m),m) = id(set(DD`m)) O Rp(DD`m,DD`succ(m),ee`m)"
by (simp add: e_gr_le e_gr_eq)

(* Cpo asm's due to THE uniqueness. *)
lemma e_gr_succ_emb: "[|emb_chain(DD,ee); m \<in> nat|] 
     ==> e_gr(DD,ee,succ(m),m) = Rp(DD`m,DD`succ(m),ee`m)"
apply (simp add: e_gr_succ)
apply (blast intro: id_comp Rp_cont cont_fun emb_chain_cpo emb_chain_emb)
done

lemma e_gr_fun_add:
    "[|emb_chain(DD,ee); n \<in> nat; k \<in> nat|] 
     ==> e_gr(DD,ee,n#+k,n): set(DD`(n#+k))->set(DD`n)"
apply (induct_tac k)
apply (simp add: e_gr_eq id_type)
apply (simp add: e_gr_add)
apply (blast intro: comp_fun Rp_cont cont_fun emb_chain_emb emb_chain_cpo)
done

lemma e_gr_fun:
    "[|n le m; emb_chain(DD,ee); m \<in> nat; n \<in> nat|] 
     ==> e_gr(DD,ee,m,n): set(DD`m)->set(DD`n)"
apply (rule le_exists, assumption)
apply (simp add: e_gr_fun_add, assumption+)
done

lemma e_gr_split_add_lemma:
    "[| emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat|] 
     ==> m le k -->
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
     "[| m le k; emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat|] 
      ==> e_gr(DD,ee,n#+k,n) = e_gr(DD,ee,n#+m,n) O e_gr(DD,ee,n#+k,n#+m)"
apply (blast intro: e_gr_split_add_lemma [THEN mp])
done

lemma e_less_cont:
     "[|m le n; emb_chain(DD,ee); m \<in> nat; n \<in> nat|] 
      ==> e_less(DD,ee,m,n):cont(DD`m,DD`n)"
apply (blast intro: emb_cont emb_e_less)
done

lemma e_gr_cont:
    "[|n le m; emb_chain(DD,ee); m \<in> nat; n \<in> nat|] 
     ==> e_gr(DD,ee,m,n):cont(DD`m,DD`n)"
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
    "[|n le k; emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat|] 
     ==> e_less(DD,ee,m,m#+n) = e_gr(DD,ee,m#+k,m#+n) O e_less(DD,ee,m,m#+k)"
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
    "[|m le k; emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat|] 
     ==> e_gr(DD,ee,n#+m,n) = e_gr(DD,ee,n#+k,n) O e_less(DD,ee,n#+m,n#+k)"
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
    "[|m le n; emb_chain(DD,ee); m \<in> nat; n \<in> nat|]
     ==> emb(DD`m,DD`n,eps(DD,ee,m,n))"
apply (simp add: eps_def)
apply (blast intro: emb_e_less)
done

lemma eps_fun:
    "[|emb_chain(DD,ee); m \<in> nat; n \<in> nat|]
     ==> eps(DD,ee,m,n): set(DD`m)->set(DD`n)"
apply (simp add: eps_def)
apply (auto intro: e_less_cont [THEN cont_fun]
                   not_le_iff_lt [THEN iffD1, THEN leI]
                   e_gr_fun nat_into_Ord)
done

lemma eps_id: "n \<in> nat ==> eps(DD,ee,n,n) = id(set(DD`n))"
by (simp add: eps_def e_less_eq)

lemma eps_e_less_add:
    "[|m \<in> nat; n \<in> nat|] ==> eps(DD,ee,m,m#+n) = e_less(DD,ee,m,m#+n)"
by (simp add: eps_def add_le_self)

lemma eps_e_less:
    "[|m le n; m \<in> nat; n \<in> nat|] ==> eps(DD,ee,m,n) = e_less(DD,ee,m,n)"
by (simp add: eps_def)

lemma eps_e_gr_add:
    "[|n \<in> nat; k \<in> nat|] ==> eps(DD,ee,n#+k,n) = e_gr(DD,ee,n#+k,n)"
by (simp add: eps_def e_less_eq e_gr_eq)

lemma eps_e_gr:
    "[|n le m; m \<in> nat; n \<in> nat|] ==> eps(DD,ee,m,n) = e_gr(DD,ee,m,n)"
apply (erule le_exists)
apply (simp_all add: eps_e_gr_add)
done

lemma eps_succ_ee:
    "[|!!n. n \<in> nat ==> emb(DD`n,DD`succ(n),ee`n); m \<in> nat|]
     ==> eps(DD,ee,m,succ(m)) = ee`m"
by (simp add: eps_e_less le_succ_iff e_less_succ_emb)

lemma eps_succ_Rp:
    "[|emb_chain(DD,ee); m \<in> nat|]
     ==> eps(DD,ee,succ(m),m) = Rp(DD`m,DD`succ(m),ee`m)"
by (simp add: eps_e_gr le_succ_iff e_gr_succ_emb)

lemma eps_cont:
  "[|emb_chain(DD,ee); m \<in> nat; n \<in> nat|] ==> eps(DD,ee,m,n): cont(DD`m,DD`n)"
apply (rule_tac i = m and j = n in nat_linear_le)
apply (simp_all add: eps_e_less e_less_cont eps_e_gr e_gr_cont)
done

(* Theorems about splitting. *)

lemma eps_split_add_left:
    "[|n le k; emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat|] 
     ==> eps(DD,ee,m,m#+k) = eps(DD,ee,m#+n,m#+k) O eps(DD,ee,m,m#+n)"
apply (simp add: eps_e_less add_le_self add_le_mono)
apply (auto intro: e_less_split_add)
done

lemma eps_split_add_left_rev:
    "[|n le k; emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat|] 
     ==> eps(DD,ee,m,m#+n) = eps(DD,ee,m#+k,m#+n) O eps(DD,ee,m,m#+k)"
apply (simp add: eps_e_less_add eps_e_gr add_le_self add_le_mono)
apply (auto intro: e_less_e_gr_split_add)
done

lemma eps_split_add_right:
    "[|m le k; emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat|] 
     ==> eps(DD,ee,n#+k,n) = eps(DD,ee,n#+m,n) O eps(DD,ee,n#+k,n#+m)"
apply (simp add: eps_e_gr add_le_self add_le_mono)
apply (auto intro: e_gr_split_add)
done

lemma eps_split_add_right_rev:
    "[|m le k; emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat|] 
     ==> eps(DD,ee,n#+m,n) = eps(DD,ee,n#+k,n) O eps(DD,ee,n#+m,n#+k)"
apply (simp add: eps_e_gr_add eps_e_less add_le_self add_le_mono)
apply (auto intro: e_gr_e_less_split_add)
done

(* Arithmetic *)

lemma le_exists_lemma:
    "[| n le k; k le m;
        !!p q. [|p le q; k=n#+p; m=n#+q; p \<in> nat; q \<in> nat|] ==> R;
        m \<in> nat |]==>R"
apply (rule le_exists, assumption)
prefer 2 apply (simp add: lt_nat_in_nat)
apply (rule le_trans [THEN le_exists], assumption+, auto)
done

lemma eps_split_left_le:
    "[|m le k; k le n; emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat|] 
     ==> eps(DD,ee,m,n) = eps(DD,ee,k,n) O eps(DD,ee,m,k)"
apply (rule le_exists_lemma, assumption+)
apply (auto intro: eps_split_add_left)
done

lemma eps_split_left_le_rev:
    "[|m le n; n le k; emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat|] 
     ==> eps(DD,ee,m,n) = eps(DD,ee,k,n) O eps(DD,ee,m,k)"
apply (rule le_exists_lemma, assumption+)
apply (auto intro: eps_split_add_left_rev)
done

lemma eps_split_right_le:
    "[|n le k; k le m; emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat|] 
     ==> eps(DD,ee,m,n) = eps(DD,ee,k,n) O eps(DD,ee,m,k)"
apply (rule le_exists_lemma, assumption+)
apply (auto intro: eps_split_add_right)
done

lemma eps_split_right_le_rev:
    "[|n le m; m le k; emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat|] 
     ==> eps(DD,ee,m,n) = eps(DD,ee,k,n) O eps(DD,ee,m,k)"
apply (rule le_exists_lemma, assumption+)
apply (auto intro: eps_split_add_right_rev)
done

(* The desired two theorems about `splitting'. *)

lemma eps_split_left:
    "[|m le k; emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat|] 
     ==> eps(DD,ee,m,n) = eps(DD,ee,k,n) O eps(DD,ee,m,k)"
apply (rule nat_linear_le)
apply (rule_tac [4] eps_split_right_le_rev)
prefer 4 apply assumption
apply (rule_tac [3] nat_linear_le)
apply (rule_tac [5] eps_split_left_le)
prefer 6 apply assumption
apply (simp_all add: eps_split_left_le_rev)
done

lemma eps_split_right:
    "[|n le k; emb_chain(DD,ee); m \<in> nat; n \<in> nat; k \<in> nat|] 
     ==> eps(DD,ee,m,n) = eps(DD,ee,k,n) O eps(DD,ee,m,k)"
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
    "[|emb_chain(DD,ee); n \<in> nat|] 
     ==> rho_emb(DD,ee,n): set(DD`n) -> set(Dinf(DD,ee))"
apply (simp add: rho_emb_def)
apply (assumption |
       rule lam_type DinfI eps_cont [THEN cont_fun, THEN apply_type])+
apply simp
apply (rule_tac i = "succ (na) " and j = n in nat_linear_le)
   apply blast
  apply assumption
 apply (subst eps_split_right_le)
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
    "x \<in> set(DD`n) ==> rho_emb(DD,ee,n)`x = (\<lambda>m \<in> nat. eps(DD,ee,n,m)`x)"
by (simp add: rho_emb_def)

lemma rho_emb_apply2:
    "[|x \<in> set(DD`n); m \<in> nat|] ==> rho_emb(DD,ee,n)`x`m = eps(DD,ee,n,m)`x"
by (simp add: rho_emb_def)

lemma rho_emb_id: "[| x \<in> set(DD`n); n \<in> nat|] ==> rho_emb(DD,ee,n)`x`n = x"
by (simp add: rho_emb_apply2 eps_id)

(* Shorter proof, 23 against 62. *)

lemma rho_emb_cont:
    "[|emb_chain(DD,ee); n \<in> nat|] 
     ==> rho_emb(DD,ee,n): cont(DD`n,Dinf(DD,ee))"
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

lemma lemma1:
    "[|m le n; emb_chain(DD,ee); x \<in> set(Dinf(DD,ee)); m \<in> nat; n \<in> nat|] 
     ==> rel(DD`n,e_less(DD,ee,m,n)`(x`m),x`n)"
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
         "%z. rel(DD`succ(y), 
                  (ee`y O Rp(?DD(y)`y,?DD(y)`succ(y),?ee(y)`y)) ` (x`succ(y)),
                  z)"
       in id_conv [THEN subst])
apply (rule_tac [6] rel_cf)
(* Dinf and cont_fun doesn't go well together, both Pi(_,%x._). *)
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

lemma lemma2:
    "[|n le m; emb_chain(DD,ee); x \<in> set(Dinf(DD,ee)); m \<in> nat; n \<in> nat|] 
     ==> rel(DD`n,e_gr(DD,ee,m,n)`(x`m),x`n)"
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
    "[|emb_chain(DD,ee); x \<in> set(Dinf(DD,ee)); m \<in> nat; n \<in> nat|] 
     ==> rel(DD`n,eps(DD,ee,m,n)`(x`m),x`n)"
apply (simp add: eps_def)
apply (blast intro: lemma1 not_le_iff_lt [THEN iffD1, THEN leI, THEN lemma2]  
                    nat_into_Ord)
done

(* The following theorem is needed/useful due to type check for rel_cfI,
   but also elsewhere.
   Look for occurences of rel_cfI, rel_DinfI, etc to evaluate the problem. *)

lemma lam_Dinf_cont:
  "[| emb_chain(DD,ee); n \<in> nat |] 
     ==> (\<lambda>x \<in> set(Dinf(DD,ee)). x`n) \<in> cont(Dinf(DD,ee),DD`n)"
apply (rule contI)
apply (assumption | rule lam_type apply_type Dinf_prod)+
apply simp
apply (assumption | rule rel_Dinf)+
apply (subst beta)
apply (auto intro: cpo_Dinf islub_in cpo_lub)
apply (simp add: chain_in lub_Dinf)
done

lemma rho_projpair:
    "[| emb_chain(DD,ee); n \<in> nat |] 
     ==> projpair(DD`n,Dinf(DD,ee),rho_emb(DD,ee,n),rho_proj(DD,ee,n))"
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
apply (rule rel_cfI) (* ------------------>>>Yields type cond, not in HOL *)
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
  "[| emb_chain(DD,ee); n \<in> nat |] ==> emb(DD`n,Dinf(DD,ee),rho_emb(DD,ee,n))"
by (auto simp add: emb_def intro: exI rho_projpair)

lemma commuteI: "[| emb_chain(DD,ee); n \<in> nat |] 
     ==> rho_proj(DD,ee,n) \<in> cont(Dinf(DD,ee),DD`n)"
by (auto intro: rho_projpair projpair_p_cont)

(*----------------------------------------------------------------------*)
(* Commutivity and universality.                                        *)
(*----------------------------------------------------------------------*)

lemma commuteI:
  "[| !!n. n \<in> nat ==> emb(DD`n,E,r(n));
      !!m n. [|m le n; m \<in> nat; n \<in> nat|] ==> r(n) O eps(DD,ee,m,n) = r(m) |] 
     ==> commute(DD,ee,E,r)"
by (simp add: commute_def)

lemma commute_emb [TC]:
  "[| commute(DD,ee,E,r); n \<in> nat |] ==> emb(DD`n,E,r(n))"
by (simp add: commute_def)

lemma commute_eq:
  "[| commute(DD,ee,E,r); m le n; m \<in> nat; n \<in> nat |] 
     ==> r(n) O eps(DD,ee,m,n) = r(m) "
by (simp add: commute_def)

(* Shorter proof: 11 vs 46 lines. *)

lemma rho_emb_commute:
  "emb_chain(DD,ee) ==> commute(DD,ee,Dinf(DD,ee),rho_emb(DD,ee))"
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

lemma le_succ: "n \<in> nat ==> n le succ(n)"
by (simp add: le_succ_iff)

(* Shorter proof: 21 vs 83 (106 - 23, due to OAssoc complication) *)

lemma commute_chain:
    "[| commute(DD,ee,E,r); emb_chain(DD,ee); cpo(E) |] 
     ==> chain(cf(E,E),\<lambda>n \<in> nat. r(n) O Rp(DD`n,E,r(n)))"
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
  "emb_chain(DD,ee) ==>
   chain(cf(Dinf(DD,ee),Dinf(DD,ee)),
         \<lambda>n \<in> nat. rho_emb(DD,ee,n) O Rp(DD`n,Dinf(DD,ee),rho_emb(DD,ee,n)))"
by (auto intro: commute_chain rho_emb_commute cpo_Dinf)

lemma rho_emb_chain_apply1:
     "[| emb_chain(DD,ee); x \<in> set(Dinf(DD,ee)) |] 
      ==> chain(Dinf(DD,ee),
                \<lambda>n \<in> nat.
                 (rho_emb(DD,ee,n) O Rp(DD`n,Dinf(DD,ee),rho_emb(DD,ee,n)))`x)"
by (drule rho_emb_chain [THEN chain_cf], assumption, simp)

lemma chain_iprod_emb_chain:
     "[| chain(iprod(DD),X); emb_chain(DD,ee); n \<in> nat |] 
      ==> chain(DD`n,\<lambda>m \<in> nat. X `m `n)"
by (auto intro: chain_iprod emb_chain_cpo)

lemma rho_emb_chain_apply2:
  "[| emb_chain(DD,ee); x \<in> set(Dinf(DD,ee)); n \<in> nat |] ==>
   chain
    (DD`n,
     \<lambda>xa \<in> nat.
      (rho_emb(DD, ee, xa) O Rp(DD ` xa, Dinf(DD, ee),rho_emb(DD, ee, xa))) `
       x ` n)"
by (frule rho_emb_chain_apply1 [THEN chain_Dinf, THEN chain_iprod_emb_chain], 
    auto)

(* Shorter proof: 32 vs 72 (roughly), Isabelle proof has lemmas. *)

lemma rho_emb_lub:
  "emb_chain(DD,ee) ==>
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
    "[| commute(DD,ee,E,r); commute(DD,ee,G,f);
        emb_chain(DD,ee); cpo(E); cpo(G) |] 
     ==> chain(cf(E,G),\<lambda>n \<in> nat. f(n) O Rp(DD`n,E,r(n)))"
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
  "[| commute(DD,ee,E,r); commute(DD,ee,G,f);
      emb_chain(DD,ee); cpo(E); cpo(G) |]
     ==> chain(cf(G,E),\<lambda>n \<in> nat. r(n) O Rp(DD`n,G,f(n)))"
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
     "[| commute(DD,ee,E,r); commute(DD,ee,G,f);
         emb_chain(DD,ee); cpo(E); cpo(G); x \<in> nat |] 
      ==> r(x) O Rp(DD ` x, G, f(x)) O f(x) O Rp(DD ` x, E, r(x)) =
          r(x) O Rp(DD ` x, E, r(x))"
apply (rule_tac s1 = "f (x) " in comp_assoc [THEN subst])
apply (subst embRp_eq)
apply (rule_tac [4] id_comp [THEN ssubst])
apply (auto intro: cont_fun Rp_cont commute_emb emb_chain_cpo)
done


(* Shorter proof (but lemmas): 19 vs 79 (103 - 24, due to OAssoc)  *)

lemma theta_projpair:
  "[| lub(cf(E,E), \<lambda>n \<in> nat. r(n) O Rp(DD`n,E,r(n))) = id(set(E));
      commute(DD,ee,E,r); commute(DD,ee,G,f);
      emb_chain(DD,ee); cpo(E); cpo(G) |]
   ==> projpair
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
    "[| lub(cf(E,E), \<lambda>n \<in> nat. r(n) O Rp(DD`n,E,r(n))) = id(set(E));
	commute(DD,ee,E,r); commute(DD,ee,G,f);
	emb_chain(DD,ee); cpo(E); cpo(G) |] 
     ==> emb(E,G,lub(cf(E,G), \<lambda>n \<in> nat. f(n) O Rp(DD`n,E,r(n))))"
apply (simp add: emb_def)
apply (blast intro: theta_projpair)
done

lemma mono_lemma:
    "[| g \<in> cont(D,D'); cpo(D); cpo(D'); cpo(E) |] 
     ==> (\<lambda>f \<in> cont(D',E). f O g) \<in> mono(cf(D',E),cf(D,E))"
apply (rule monoI)
apply (simp add: set_def cf_def)
apply (drule cf_cont)+
apply simp
apply (blast intro: comp_mono lam_type comp_pres_cont cpo_cf cont_cf)
done

lemma commute_lam_lemma:
     "[| commute(DD,ee,E,r); commute(DD,ee,G,f);
         emb_chain(DD,ee); cpo(E); cpo(G); n \<in> nat |]
      ==> (\<lambda>na \<in> nat. (\<lambda>f \<in> cont(E, G). f O r(n)) `
           ((\<lambda>n \<in> nat. f(n) O Rp(DD ` n, E, r(n))) ` na))  =
          (\<lambda>na \<in> nat. (f(na) O Rp(DD ` na, E, r(na))) O r(n))"
apply (rule fun_extension)
(*something wrong here*) 
apply (auto simp del: beta_if simp add: beta intro: lam_type)
done

lemma chain_lemma:
     "[| commute(DD,ee,E,r); commute(DD,ee,G,f);
         emb_chain(DD,ee); cpo(E); cpo(G); n \<in> nat |] 
      ==> chain(cf(DD`n,G),\<lambda>x \<in> nat. (f(x) O Rp(DD ` x, E, r(x))) O r(n))"
apply (rule commute_lam_lemma [THEN subst])
apply (blast intro: theta_chain emb_chain_cpo 
               commute_emb [THEN emb_cont, THEN mono_lemma, THEN mono_chain])+
done

lemma suffix_lemma:
    "[| commute(DD,ee,E,r); commute(DD,ee,G,f);
        emb_chain(DD,ee); cpo(E); cpo(G); cpo(DD`x); x \<in> nat |] 
     ==> suffix(\<lambda>n \<in> nat. (f(n) O Rp(DD`n,E,r(n))) O r(x),x) = 
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
  "[|emb(E,G,t);  !!n. n \<in> nat ==> f(n) = t O r(n) |]==>mediating(E,G,r,f,t)"
by (simp add: mediating_def)

lemma mediating_emb: "mediating(E,G,r,f,t) ==> emb(E,G,t)"
by (simp add: mediating_def)

lemma mediating_eq: "[| mediating(E,G,r,f,t); n \<in> nat |] ==> f(n) = t O r(n)"
by (simp add: mediating_def)

lemma lub_universal_mediating:
  "[| lub(cf(E,E), \<lambda>n \<in> nat. r(n) O Rp(DD`n,E,r(n))) = id(set(E));
      commute(DD,ee,E,r); commute(DD,ee,G,f);
      emb_chain(DD,ee); cpo(E); cpo(G) |]
     ==> mediating(E,G,r,f,lub(cf(E,G), \<lambda>n \<in> nat. f(n) O Rp(DD`n,E,r(n))))"
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
    "[| mediating(E,G,r,f,t);
	lub(cf(E,E), \<lambda>n \<in> nat. r(n) O Rp(DD`n,E,r(n))) = id(set(E));
	commute(DD,ee,E,r); commute(DD,ee,G,f);
	emb_chain(DD,ee); cpo(E); cpo(G) |] 
     ==> t = lub(cf(E,G), \<lambda>n \<in> nat. f(n) O Rp(DD`n,E,r(n)))"
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
  "[| commute(DD,ee,G,f); emb_chain(DD,ee); cpo(G) |] ==>
   mediating
    (Dinf(DD,ee),G,rho_emb(DD,ee),f,
     lub(cf(Dinf(DD,ee),G),
         \<lambda>n \<in> nat. f(n) O Rp(DD`n,Dinf(DD,ee),rho_emb(DD,ee,n)))) &
   (\<forall>t. mediating(Dinf(DD,ee),G,rho_emb(DD,ee),f,t) -->
     t = lub(cf(Dinf(DD,ee),G),
         \<lambda>n \<in> nat. f(n) O Rp(DD`n,Dinf(DD,ee),rho_emb(DD,ee,n))))"
apply safe
apply (assumption | 
       rule lub_universal_mediating rho_emb_commute rho_emb_lub cpo_Dinf)+
apply (auto intro: lub_universal_unique rho_emb_commute rho_emb_lub cpo_Dinf)
done

end
