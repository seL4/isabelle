(*  Title:      ZF/IMP/Denotation.thy
    ID:         $Id$
    Author:     Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM

Denotational semantics of expressions & commands
*)

theory Denotation = Com:


consts
  A     :: "i => i => i"
  B     :: "i => i => i"
  C     :: "i => i"

constdefs
  Gamma :: "[i,i,i] => i"
    "Gamma(b,cden) == (%phi.{io \<in> (phi O cden). B(b,fst(io))=1} Un 
                         {io \<in> id(loc->nat). B(b,fst(io))=0})"

primrec
    "A(N(n), sigma) = n"
    "A(X(x), sigma) = sigma`x" 
    "A(Op1(f,a), sigma) = f`A(a,sigma)"
    "A(Op2(f,a0,a1), sigma) = f`<A(a0,sigma),A(a1,sigma)>"


primrec
    "B(true, sigma) = 1"
    "B(false, sigma) = 0"
    "B(ROp(f,a0,a1), sigma) = f`<A(a0,sigma),A(a1,sigma)>" 
    "B(noti(b), sigma) = not(B(b,sigma))"
    "B(b0 andi b1, sigma) = B(b0,sigma) and B(b1,sigma)"
    "B(b0 ori b1, sigma) = B(b0,sigma) or B(b1,sigma)"


primrec
    "C(skip) = id(loc->nat)"

    "C(x asgt a) = {io:(loc->nat)*(loc->nat). 
                    snd(io) = fst(io)(x := A(a,fst(io)))}"

    "C(c0 ; c1) = C(c1) O C(c0)"

    "C(ifc b then c0 else c1) = {io \<in> C(c0). B(b,fst(io))=1} Un 
                                             {io \<in> C(c1). B(b,fst(io))=0}"

    "C(while b do c) = lfp((loc->nat)*(loc->nat), Gamma(b,C(c)))"


(** Type_intr for A **)

lemma A_type [TC]: "[|a \<in> aexp; sigma \<in> loc->nat|] ==> A(a,sigma) \<in> nat"
by (erule aexp.induct, simp_all)


(** Type_intr for B **)

lemma B_type [TC]: "[|b \<in> bexp; sigma \<in> loc->nat|] ==> B(b,sigma) \<in> bool"
by (erule bexp.induct, simp_all)

(** C_subset **)

lemma C_subset: "c \<in> com ==> C(c) \<subseteq> (loc->nat)*(loc->nat)"
apply (erule com.induct)
apply simp_all
apply (blast dest: lfp_subset [THEN subsetD])+
done

(** Type_elims for C **)

lemma C_type_D [dest]:
     "[| <x,y> \<in> C(c); c \<in> com |] ==> x \<in> loc->nat & y \<in> loc->nat"
by (blast dest: C_subset [THEN subsetD])

lemma C_type_fst [dest]: "[| x \<in> C(c); c \<in> com |] ==> fst(x) \<in> loc->nat"
by (auto dest!: C_subset [THEN subsetD])

(** bnd_mono (nat->nat*nat->nat,Gamma(b,c) **)

lemma Gamma_bnd_mono: 
     "cden <= (loc->nat)*(loc->nat) 
      ==> bnd_mono ((loc->nat)*(loc->nat),Gamma(b,cden))"
by (unfold bnd_mono_def Gamma_def, blast)

end
