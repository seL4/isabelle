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
*)

Limit  =  Main +

consts

  "rel" :: [i,i,i]=>o                 (* rel(D,x,y) *)
  "set" :: i=>i                       (* set(D) *)
  "po"  :: i=>o                       (* po(D) *)
  "chain" :: [i,i]=>o                 (* chain(D,X) *)
  "isub" :: [i,i,i]=>o                (* isub(D,X,x) *)
  "islub" :: [i,i,i]=>o               (* islub(D,X,x) *)
  "lub" :: [i,i]=>i                   (* lub(D,X) *)
  "cpo" :: i=>o                       (* cpo(D) *)
  "pcpo" :: i=>o                      (* pcpo(D) *)
  "bot" :: i=>i                       (* bot(D) *)
  "mono" :: [i,i]=>i                  (* mono(D,E) *)
  "cont" :: [i,i]=>i                  (* cont(D,E) *)
  "cf" :: [i,i]=>i                    (* cf(D,E) *)

  "suffix" :: [i,i]=>i                (* suffix(X,n) *)
  "subchain" :: [i,i]=>o              (* subchain(X,Y) *)
  "dominate" :: [i,i,i]=>o            (* dominate(D,X,Y) *)
  "matrix" :: [i,i]=>o                (* matrix(D,M) *)

  "projpair"  :: [i,i,i,i]=>o         (* projpair(D,E,e,p) *)
  "emb"       :: [i,i,i]=>o           (* emb(D,E,e) *)
  "Rp"        :: [i,i,i]=>i           (* Rp(D,E,e) *)
  "iprod"     :: i=>i                 (* iprod(DD) *)
  "mkcpo"     :: [i,i=>o]=>i          (* mkcpo(D,P) *)
  "subcpo"    :: [i,i]=>o             (* subcpo(D,E) *)
  "subpcpo"   :: [i,i]=>o             (* subpcpo(D,E) *)

  "emb_chain" :: [i,i]=>o             (* emb_chain(DD,ee) *)
  "Dinf"      :: [i,i]=>i             (* Dinf(DD,ee) *)

  "e_less"    :: [i,i,i,i]=>i         (* e_less(DD,ee,m,n) *)
  "e_gr"      :: [i,i,i,i]=>i         (* e_gr(DD,ee,m,n) *)
  "eps"       :: [i,i,i,i]=>i         (* eps(DD,ee,m,n) *)
  "rho_emb"   :: [i,i,i]=>i           (* rho_emb(DD,ee,n) *)
  "rho_proj"  :: [i,i,i]=>i           (* rho_proj(DD,ee,n) *)
  "commute"   :: [i,i,i,i=>i]=>o      (* commute(DD,ee,E,r) *)
  "mediating" :: [i,i,i=>i,i=>i,i]=>o (* mediating(E,G,r,f,t) *)

rules

  set_def
    "set(D) == fst(D)"

  rel_def
    "rel(D,x,y) == <x,y>:snd(D)" 
  
  po_def
    "po(D) ==   \
\    (\\<forall>x \\<in> set(D). rel(D,x,x)) &   \
\    (\\<forall>x \\<in> set(D). \\<forall>y \\<in> set(D). \\<forall>z \\<in> set(D).   \
\      rel(D,x,y) --> rel(D,y,z) --> rel(D,x,z)) &   \
\    (\\<forall>x \\<in> set(D). \\<forall>y \\<in> set(D). rel(D,x,y) --> rel(D,y,x) --> x = y)"

    (* Chains are object level functions nat->set(D) *)

  chain_def
    "chain(D,X) == X \\<in> nat->set(D) & (\\<forall>n \\<in> nat. rel(D,X`n,X`(succ(n))))"

  isub_def
    "isub(D,X,x) == x \\<in> set(D) & (\\<forall>n \\<in> nat. rel(D,X`n,x))"

  islub_def
    "islub(D,X,x) == isub(D,X,x) & (\\<forall>y. isub(D,X,y) --> rel(D,x,y))"

  lub_def
    "lub(D,X) == THE x. islub(D,X,x)"

  cpo_def
    "cpo(D) == po(D) & (\\<forall>X. chain(D,X) --> (\\<exists>x. islub(D,X,x)))"

  pcpo_def
    "pcpo(D) == cpo(D) & (\\<exists>x \\<in> set(D). \\<forall>y \\<in> set(D). rel(D,x,y))"
  
  bot_def
    "bot(D) == THE x. x \\<in> set(D) & (\\<forall>y \\<in> set(D). rel(D,x,y))"

  
  mono_def
    "mono(D,E) ==   \
\    {f \\<in> set(D)->set(E).   \
\     \\<forall>x \\<in> set(D). \\<forall>y \\<in> set(D). rel(D,x,y) --> rel(E,f`x,f`y)}"

  cont_def
    "cont(D,E) ==   \
\    {f \\<in> mono(D,E).   \
\     \\<forall>X. chain(D,X) --> f`(lub(D,X)) = lub(E,\\<lambda>n \\<in> nat. f`(X`n))}" 
  
  cf_def
    "cf(D,E) ==   \
\    <cont(D,E),   \
\     {y \\<in> cont(D,E)*cont(D,E). \\<forall>x \\<in> set(D). rel(E,(fst(y))`x,(snd(y))`x)}>"

  suffix_def
    "suffix(X,n) == \\<lambda>m \\<in> nat. X`(n #+ m)"

  subchain_def
    "subchain(X,Y) == \\<forall>m \\<in> nat. \\<exists>n \\<in> nat. X`m = Y`(m #+ n)"

  dominate_def
    "dominate(D,X,Y) == \\<forall>m \\<in> nat. \\<exists>n \\<in> nat. rel(D,X`m,Y`n)"

  matrix_def
    "matrix(D,M) ==   \
\    M \\<in> nat -> (nat -> set(D)) &   \
\    (\\<forall>n \\<in> nat. \\<forall>m \\<in> nat. rel(D,M`n`m,M`succ(n)`m)) &   \
\    (\\<forall>n \\<in> nat. \\<forall>m \\<in> nat. rel(D,M`n`m,M`n`succ(m))) &   \
\    (\\<forall>n \\<in> nat. \\<forall>m \\<in> nat. rel(D,M`n`m,M`succ(n)`succ(m)))"

  projpair_def
    "projpair(D,E,e,p) ==   \
\    e \\<in> cont(D,E) & p \\<in> cont(E,D) &   \
\    p O e = id(set(D)) & rel(cf(E,E),e O p,id(set(E)))"

  emb_def
    "emb(D,E,e) == \\<exists>p. projpair(D,E,e,p)"

  Rp_def
    "Rp(D,E,e) == THE p. projpair(D,E,e,p)"

(* Twice, constructions on cpos are more difficult. *)

  iprod_def
    "iprod(DD) ==   \
\    <(\\<Pi>n \\<in> nat. set(DD`n)),  \
\     {x:(\\<Pi>n \\<in> nat. set(DD`n))*(\\<Pi>n \\<in> nat. set(DD`n)).   \
\      \\<forall>n \\<in> nat. rel(DD`n,fst(x)`n,snd(x)`n)}>"

  mkcpo_def   (* Cannot use rel(D), is meta fun, need two more args *)
    "mkcpo(D,P) ==   \
\    <{x \\<in> set(D). P(x)},{x \\<in> set(D)*set(D). rel(D,fst(x),snd(x))}>"


  subcpo_def
    "subcpo(D,E) ==   \
\    set(D) \\<subseteq> set(E) &   \
\    (\\<forall>x \\<in> set(D). \\<forall>y \\<in> set(D). rel(D,x,y) <-> rel(E,x,y)) &   \
\    (\\<forall>X. chain(D,X) --> lub(E,X):set(D))"

  subpcpo_def
    "subpcpo(D,E) == subcpo(D,E) & bot(E):set(D)"

  emb_chain_def
    "emb_chain(DD,ee) ==   \
\    (\\<forall>n \\<in> nat. cpo(DD`n)) & (\\<forall>n \\<in> nat. emb(DD`n,DD`succ(n),ee`n))"

  Dinf_def
    "Dinf(DD,ee) ==   \
\    mkcpo(iprod(DD))   \
\    (%x. \\<forall>n \\<in> nat. Rp(DD`n,DD`succ(n),ee`n)`(x`succ(n)) = x`n)"

  e_less_def (* Valid for m le n only. *)
    "e_less(DD,ee,m,n) == rec(n#-m,id(set(DD`m)),%x y. ee`(m#+x) O y)"

  e_gr_def (* Valid for n le m only. *)
    "e_gr(DD,ee,m,n) ==   \
\    rec(m#-n,id(set(DD`n)),   \
\        %x y. y O Rp(DD`(n#+x),DD`(succ(n#+x)),ee`(n#+x)))"

  eps_def
    "eps(DD,ee,m,n) == if(m le n,e_less(DD,ee,m,n),e_gr(DD,ee,m,n))"

  rho_emb_def
    "rho_emb(DD,ee,n) == \\<lambda>x \\<in> set(DD`n). \\<lambda>m \\<in> nat. eps(DD,ee,n,m)`x"

  rho_proj_def
    "rho_proj(DD,ee,n) == \\<lambda>x \\<in> set(Dinf(DD,ee)). x`n"
  
  commute_def
    "commute(DD,ee,E,r) ==   \
\    (\\<forall>n \\<in> nat. emb(DD`n,E,r(n))) &   \
\    (\\<forall>m \\<in> nat. \\<forall>n \\<in> nat. m le n --> r(n) O eps(DD,ee,m,n) = r(m))"

  mediating_def
    "mediating(E,G,r,f,t) == emb(E,G,t) & (\\<forall>n \\<in> nat. f(n) = t O r(n))"

end
