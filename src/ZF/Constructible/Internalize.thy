(*  Title:      ZF/Constructible/Internalize.thy
    ID: $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2002  University of Cambridge
*)

theory Internalize = L_axioms + Datatype_absolute:

subsection{*Internalized Forms of Data Structuring Operators*}

subsubsection{*The Formula @{term is_Inl}, Internalized*}

(*  is_Inl(M,a,z) == \<exists>zero[M]. empty(M,zero) & pair(M,zero,a,z) *)
constdefs Inl_fm :: "[i,i]=>i"
    "Inl_fm(a,z) == Exists(And(empty_fm(0), pair_fm(0,succ(a),succ(z))))"

lemma Inl_type [TC]:
     "[| x \<in> nat; z \<in> nat |] ==> Inl_fm(x,z) \<in> formula"
by (simp add: Inl_fm_def)

lemma sats_Inl_fm [simp]:
   "[| x \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, Inl_fm(x,z), env) <-> is_Inl(**A, nth(x,env), nth(z,env))"
by (simp add: Inl_fm_def is_Inl_def)

lemma Inl_iff_sats:
      "[| nth(i,env) = x; nth(k,env) = z;
          i \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> is_Inl(**A, x, z) <-> sats(A, Inl_fm(i,k), env)"
by simp

theorem Inl_reflection:
     "REFLECTS[\<lambda>x. is_Inl(L,f(x),h(x)),
               \<lambda>i x. is_Inl(**Lset(i),f(x),h(x))]"
apply (simp only: is_Inl_def setclass_simps)
apply (intro FOL_reflections function_reflections)
done


subsubsection{*The Formula @{term is_Inr}, Internalized*}

(*  is_Inr(M,a,z) == \<exists>n1[M]. number1(M,n1) & pair(M,n1,a,z) *)
constdefs Inr_fm :: "[i,i]=>i"
    "Inr_fm(a,z) == Exists(And(number1_fm(0), pair_fm(0,succ(a),succ(z))))"

lemma Inr_type [TC]:
     "[| x \<in> nat; z \<in> nat |] ==> Inr_fm(x,z) \<in> formula"
by (simp add: Inr_fm_def)

lemma sats_Inr_fm [simp]:
   "[| x \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, Inr_fm(x,z), env) <-> is_Inr(**A, nth(x,env), nth(z,env))"
by (simp add: Inr_fm_def is_Inr_def)

lemma Inr_iff_sats:
      "[| nth(i,env) = x; nth(k,env) = z;
          i \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> is_Inr(**A, x, z) <-> sats(A, Inr_fm(i,k), env)"
by simp

theorem Inr_reflection:
     "REFLECTS[\<lambda>x. is_Inr(L,f(x),h(x)),
               \<lambda>i x. is_Inr(**Lset(i),f(x),h(x))]"
apply (simp only: is_Inr_def setclass_simps)
apply (intro FOL_reflections function_reflections)
done


subsubsection{*The Formula @{term is_Nil}, Internalized*}

(* is_Nil(M,xs) == \<exists>zero[M]. empty(M,zero) & is_Inl(M,zero,xs) *)

constdefs Nil_fm :: "i=>i"
    "Nil_fm(x) == Exists(And(empty_fm(0), Inl_fm(0,succ(x))))"

lemma Nil_type [TC]: "x \<in> nat ==> Nil_fm(x) \<in> formula"
by (simp add: Nil_fm_def)

lemma sats_Nil_fm [simp]:
   "[| x \<in> nat; env \<in> list(A)|]
    ==> sats(A, Nil_fm(x), env) <-> is_Nil(**A, nth(x,env))"
by (simp add: Nil_fm_def is_Nil_def)

lemma Nil_iff_sats:
      "[| nth(i,env) = x; i \<in> nat; env \<in> list(A)|]
       ==> is_Nil(**A, x) <-> sats(A, Nil_fm(i), env)"
by simp

theorem Nil_reflection:
     "REFLECTS[\<lambda>x. is_Nil(L,f(x)),
               \<lambda>i x. is_Nil(**Lset(i),f(x))]"
apply (simp only: is_Nil_def setclass_simps)
apply (intro FOL_reflections function_reflections Inl_reflection)
done


subsubsection{*The Formula @{term is_Cons}, Internalized*}


(*  "is_Cons(M,a,l,Z) == \<exists>p[M]. pair(M,a,l,p) & is_Inr(M,p,Z)" *)
constdefs Cons_fm :: "[i,i,i]=>i"
    "Cons_fm(a,l,Z) ==
       Exists(And(pair_fm(succ(a),succ(l),0), Inr_fm(0,succ(Z))))"

lemma Cons_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> Cons_fm(x,y,z) \<in> formula"
by (simp add: Cons_fm_def)

lemma sats_Cons_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, Cons_fm(x,y,z), env) <->
       is_Cons(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: Cons_fm_def is_Cons_def)

lemma Cons_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==>is_Cons(**A, x, y, z) <-> sats(A, Cons_fm(i,j,k), env)"
by simp

theorem Cons_reflection:
     "REFLECTS[\<lambda>x. is_Cons(L,f(x),g(x),h(x)),
               \<lambda>i x. is_Cons(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: is_Cons_def setclass_simps)
apply (intro FOL_reflections pair_reflection Inr_reflection)
done

subsubsection{*The Formula @{term is_quasilist}, Internalized*}

(* is_quasilist(M,xs) == is_Nil(M,z) | (\<exists>x[M]. \<exists>l[M]. is_Cons(M,x,l,z))" *)

constdefs quasilist_fm :: "i=>i"
    "quasilist_fm(x) ==
       Or(Nil_fm(x), Exists(Exists(Cons_fm(1,0,succ(succ(x))))))"

lemma quasilist_type [TC]: "x \<in> nat ==> quasilist_fm(x) \<in> formula"
by (simp add: quasilist_fm_def)

lemma sats_quasilist_fm [simp]:
   "[| x \<in> nat; env \<in> list(A)|]
    ==> sats(A, quasilist_fm(x), env) <-> is_quasilist(**A, nth(x,env))"
by (simp add: quasilist_fm_def is_quasilist_def)

lemma quasilist_iff_sats:
      "[| nth(i,env) = x; i \<in> nat; env \<in> list(A)|]
       ==> is_quasilist(**A, x) <-> sats(A, quasilist_fm(i), env)"
by simp

theorem quasilist_reflection:
     "REFLECTS[\<lambda>x. is_quasilist(L,f(x)),
               \<lambda>i x. is_quasilist(**Lset(i),f(x))]"
apply (simp only: is_quasilist_def setclass_simps)
apply (intro FOL_reflections Nil_reflection Cons_reflection)
done


subsection{*Absoluteness for the Function @{term nth}*}


subsubsection{*The Formula @{term is_hd}, Internalized*}

(*   "is_hd(M,xs,H) == 
       (is_Nil(M,xs) --> empty(M,H)) &
       (\<forall>x[M]. \<forall>l[M]. ~ is_Cons(M,x,l,xs) | H=x) &
       (is_quasilist(M,xs) | empty(M,H))" *)
constdefs hd_fm :: "[i,i]=>i"
    "hd_fm(xs,H) == 
       And(Implies(Nil_fm(xs), empty_fm(H)),
           And(Forall(Forall(Or(Neg(Cons_fm(1,0,xs#+2)), Equal(H#+2,1)))),
               Or(quasilist_fm(xs), empty_fm(H))))"

lemma hd_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> hd_fm(x,y) \<in> formula"
by (simp add: hd_fm_def) 

lemma sats_hd_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, hd_fm(x,y), env) <-> is_hd(**A, nth(x,env), nth(y,env))"
by (simp add: hd_fm_def is_hd_def)

lemma hd_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> is_hd(**A, x, y) <-> sats(A, hd_fm(i,j), env)"
by simp

theorem hd_reflection:
     "REFLECTS[\<lambda>x. is_hd(L,f(x),g(x)), 
               \<lambda>i x. is_hd(**Lset(i),f(x),g(x))]"
apply (simp only: is_hd_def setclass_simps)
apply (intro FOL_reflections Nil_reflection Cons_reflection
             quasilist_reflection empty_reflection)  
done


subsubsection{*The Formula @{term is_tl}, Internalized*}

(*     "is_tl(M,xs,T) ==
       (is_Nil(M,xs) --> T=xs) &
       (\<forall>x[M]. \<forall>l[M]. ~ is_Cons(M,x,l,xs) | T=l) &
       (is_quasilist(M,xs) | empty(M,T))" *)
constdefs tl_fm :: "[i,i]=>i"
    "tl_fm(xs,T) ==
       And(Implies(Nil_fm(xs), Equal(T,xs)),
           And(Forall(Forall(Or(Neg(Cons_fm(1,0,xs#+2)), Equal(T#+2,0)))),
               Or(quasilist_fm(xs), empty_fm(T))))"

lemma tl_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> tl_fm(x,y) \<in> formula"
by (simp add: tl_fm_def)

lemma sats_tl_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, tl_fm(x,y), env) <-> is_tl(**A, nth(x,env), nth(y,env))"
by (simp add: tl_fm_def is_tl_def)

lemma tl_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> is_tl(**A, x, y) <-> sats(A, tl_fm(i,j), env)"
by simp

theorem tl_reflection:
     "REFLECTS[\<lambda>x. is_tl(L,f(x),g(x)),
               \<lambda>i x. is_tl(**Lset(i),f(x),g(x))]"
apply (simp only: is_tl_def setclass_simps)
apply (intro FOL_reflections Nil_reflection Cons_reflection
             quasilist_reflection empty_reflection)
done


subsubsection{*The Operator @{term is_bool_of_o}*}

(*   is_bool_of_o :: "[i=>o, o, i] => o"
   "is_bool_of_o(M,P,z) == (P & number1(M,z)) | (~P & empty(M,z))" *)

text{*The formula @{term p} has no free variables.*}
constdefs bool_of_o_fm :: "[i, i]=>i"
 "bool_of_o_fm(p,z) == 
    Or(And(p,number1_fm(z)),
       And(Neg(p),empty_fm(z)))"

lemma is_bool_of_o_type [TC]:
     "[| p \<in> formula; z \<in> nat |] ==> bool_of_o_fm(p,z) \<in> formula"
by (simp add: bool_of_o_fm_def)

lemma sats_bool_of_o_fm:
  assumes p_iff_sats: "P <-> sats(A, p, env)"
  shows 
      "[|z \<in> nat; env \<in> list(A)|]
       ==> sats(A, bool_of_o_fm(p,z), env) <->
           is_bool_of_o(**A, P, nth(z,env))"
by (simp add: bool_of_o_fm_def is_bool_of_o_def p_iff_sats [THEN iff_sym])

lemma is_bool_of_o_iff_sats:
  "[| P <-> sats(A, p, env); nth(k,env) = z; k \<in> nat; env \<in> list(A)|]
   ==> is_bool_of_o(**A, P, z) <-> sats(A, bool_of_o_fm(p,k), env)"
by (simp add: sats_bool_of_o_fm)

theorem bool_of_o_reflection:
     "REFLECTS [P(L), \<lambda>i. P(**Lset(i))] ==>
      REFLECTS[\<lambda>x. is_bool_of_o(L, P(L,x), f(x)),  
               \<lambda>i x. is_bool_of_o(**Lset(i), P(**Lset(i),x), f(x))]"
apply (simp (no_asm) only: is_bool_of_o_def setclass_simps)
apply (intro FOL_reflections function_reflections, assumption+)
done


subsection{*More Internalizations*}

subsubsection{*The Operator @{term is_lambda}*}

text{*The two arguments of @{term p} are always 1, 0. Remember that
 @{term p} will be enclosed by three quantifiers.*}

(* is_lambda :: "[i=>o, i, [i,i]=>o, i] => o"
    "is_lambda(M, A, is_b, z) == 
       \<forall>p[M]. p \<in> z <->
        (\<exists>u[M]. \<exists>v[M]. u\<in>A & pair(M,u,v,p) & is_b(u,v))" *)
constdefs lambda_fm :: "[i, i, i]=>i"
 "lambda_fm(p,A,z) == 
    Forall(Iff(Member(0,succ(z)),
            Exists(Exists(And(Member(1,A#+3),
                           And(pair_fm(1,0,2), p))))))"

text{*We call @{term p} with arguments x, y by equating them with 
  the corresponding quantified variables with de Bruijn indices 1, 0.*}

lemma is_lambda_type [TC]:
     "[| p \<in> formula; x \<in> nat; y \<in> nat |] 
      ==> lambda_fm(p,x,y) \<in> formula"
by (simp add: lambda_fm_def) 

lemma sats_lambda_fm:
  assumes is_b_iff_sats: 
      "!!a0 a1 a2. 
        [|a0\<in>A; a1\<in>A; a2\<in>A|] 
        ==> is_b(a1, a0) <-> sats(A, p, Cons(a0,Cons(a1,Cons(a2,env))))"
  shows 
      "[|x \<in> nat; y \<in> nat; env \<in> list(A)|]
       ==> sats(A, lambda_fm(p,x,y), env) <-> 
           is_lambda(**A, nth(x,env), is_b, nth(y,env))"
by (simp add: lambda_fm_def is_lambda_def is_b_iff_sats [THEN iff_sym]) 

lemma is_lambda_iff_sats:
  assumes is_b_iff_sats: 
      "!!a0 a1 a2. 
        [|a0\<in>A; a1\<in>A; a2\<in>A|] 
        ==> is_b(a1, a0) <-> sats(A, p, Cons(a0,Cons(a1,Cons(a2,env))))"
  shows
  "[|nth(i,env) = x; nth(j,env) = y; 
      i \<in> nat; j \<in> nat; env \<in> list(A)|]
   ==> is_lambda(**A, x, is_b, y) <-> sats(A, lambda_fm(p,i,j), env)" 
by (simp add: sats_lambda_fm [OF is_b_iff_sats])

theorem is_lambda_reflection:
  assumes is_b_reflection:
    "!!f' f g h. REFLECTS[\<lambda>x. is_b(L, f'(x), f(x), g(x)), 
                     \<lambda>i x. is_b(**Lset(i), f'(x), f(x), g(x))]"
  shows "REFLECTS[\<lambda>x. is_lambda(L, A(x), is_b(L,x), f(x)), 
               \<lambda>i x. is_lambda(**Lset(i), A(x), is_b(**Lset(i),x), f(x))]"
apply (simp (no_asm_use) only: is_lambda_def setclass_simps)
apply (intro FOL_reflections is_b_reflection pair_reflection)
done

subsubsection{*The Operator @{term is_Member}, Internalized*}

(*    "is_Member(M,x,y,Z) ==
	\<exists>p[M]. \<exists>u[M]. pair(M,x,y,p) & is_Inl(M,p,u) & is_Inl(M,u,Z)" *)
constdefs Member_fm :: "[i,i,i]=>i"
    "Member_fm(x,y,Z) ==
       Exists(Exists(And(pair_fm(x#+2,y#+2,1), 
                      And(Inl_fm(1,0), Inl_fm(0,Z#+2)))))"

lemma is_Member_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> Member_fm(x,y,z) \<in> formula"
by (simp add: Member_fm_def)

lemma sats_Member_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, Member_fm(x,y,z), env) <->
        is_Member(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: Member_fm_def is_Member_def)

lemma Member_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> is_Member(**A, x, y, z) <-> sats(A, Member_fm(i,j,k), env)"
by (simp add: sats_Member_fm)

theorem Member_reflection:
     "REFLECTS[\<lambda>x. is_Member(L,f(x),g(x),h(x)),
               \<lambda>i x. is_Member(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: is_Member_def setclass_simps)
apply (intro FOL_reflections pair_reflection Inl_reflection)
done

subsubsection{*The Operator @{term is_Equal}, Internalized*}

(*    "is_Equal(M,x,y,Z) ==
	\<exists>p[M]. \<exists>u[M]. pair(M,x,y,p) & is_Inr(M,p,u) & is_Inl(M,u,Z)" *)
constdefs Equal_fm :: "[i,i,i]=>i"
    "Equal_fm(x,y,Z) ==
       Exists(Exists(And(pair_fm(x#+2,y#+2,1), 
                      And(Inr_fm(1,0), Inl_fm(0,Z#+2)))))"

lemma is_Equal_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> Equal_fm(x,y,z) \<in> formula"
by (simp add: Equal_fm_def)

lemma sats_Equal_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, Equal_fm(x,y,z), env) <->
        is_Equal(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: Equal_fm_def is_Equal_def)

lemma Equal_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> is_Equal(**A, x, y, z) <-> sats(A, Equal_fm(i,j,k), env)"
by (simp add: sats_Equal_fm)

theorem Equal_reflection:
     "REFLECTS[\<lambda>x. is_Equal(L,f(x),g(x),h(x)),
               \<lambda>i x. is_Equal(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: is_Equal_def setclass_simps)
apply (intro FOL_reflections pair_reflection Inl_reflection Inr_reflection)
done

subsubsection{*The Operator @{term is_Nand}, Internalized*}

(*    "is_Nand(M,x,y,Z) ==
	\<exists>p[M]. \<exists>u[M]. pair(M,x,y,p) & is_Inl(M,p,u) & is_Inr(M,u,Z)" *)
constdefs Nand_fm :: "[i,i,i]=>i"
    "Nand_fm(x,y,Z) ==
       Exists(Exists(And(pair_fm(x#+2,y#+2,1), 
                      And(Inl_fm(1,0), Inr_fm(0,Z#+2)))))"

lemma is_Nand_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> Nand_fm(x,y,z) \<in> formula"
by (simp add: Nand_fm_def)

lemma sats_Nand_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, Nand_fm(x,y,z), env) <->
        is_Nand(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: Nand_fm_def is_Nand_def)

lemma Nand_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> is_Nand(**A, x, y, z) <-> sats(A, Nand_fm(i,j,k), env)"
by (simp add: sats_Nand_fm)

theorem Nand_reflection:
     "REFLECTS[\<lambda>x. is_Nand(L,f(x),g(x),h(x)),
               \<lambda>i x. is_Nand(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: is_Nand_def setclass_simps)
apply (intro FOL_reflections pair_reflection Inl_reflection Inr_reflection)
done

subsubsection{*The Operator @{term is_Forall}, Internalized*}

(* "is_Forall(M,p,Z) == \<exists>u[M]. is_Inr(M,p,u) & is_Inr(M,u,Z)" *)
constdefs Forall_fm :: "[i,i]=>i"
    "Forall_fm(x,Z) ==
       Exists(And(Inr_fm(succ(x),0), Inr_fm(0,succ(Z))))"

lemma is_Forall_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> Forall_fm(x,y) \<in> formula"
by (simp add: Forall_fm_def)

lemma sats_Forall_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, Forall_fm(x,y), env) <->
        is_Forall(**A, nth(x,env), nth(y,env))"
by (simp add: Forall_fm_def is_Forall_def)

lemma Forall_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; 
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> is_Forall(**A, x, y) <-> sats(A, Forall_fm(i,j), env)"
by (simp add: sats_Forall_fm)

theorem Forall_reflection:
     "REFLECTS[\<lambda>x. is_Forall(L,f(x),g(x)),
               \<lambda>i x. is_Forall(**Lset(i),f(x),g(x))]"
apply (simp only: is_Forall_def setclass_simps)
apply (intro FOL_reflections pair_reflection Inr_reflection)
done


subsubsection{*The Operator @{term is_and}, Internalized*}

(* is_and(M,a,b,z) == (number1(M,a)  & z=b) | 
                       (~number1(M,a) & empty(M,z)) *)
constdefs and_fm :: "[i,i,i]=>i"
    "and_fm(a,b,z) ==
       Or(And(number1_fm(a), Equal(z,b)),
          And(Neg(number1_fm(a)),empty_fm(z)))"

lemma is_and_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> and_fm(x,y,z) \<in> formula"
by (simp add: and_fm_def)

lemma sats_and_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, and_fm(x,y,z), env) <->
        is_and(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: and_fm_def is_and_def)

lemma is_and_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> is_and(**A, x, y, z) <-> sats(A, and_fm(i,j,k), env)"
by simp

theorem is_and_reflection:
     "REFLECTS[\<lambda>x. is_and(L,f(x),g(x),h(x)),
               \<lambda>i x. is_and(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: is_and_def setclass_simps)
apply (intro FOL_reflections function_reflections)
done


subsubsection{*The Operator @{term is_or}, Internalized*}

(* is_or(M,a,b,z) == (number1(M,a)  & number1(M,z)) | 
                     (~number1(M,a) & z=b) *)

constdefs or_fm :: "[i,i,i]=>i"
    "or_fm(a,b,z) ==
       Or(And(number1_fm(a), number1_fm(z)),
          And(Neg(number1_fm(a)), Equal(z,b)))"

lemma is_or_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> or_fm(x,y,z) \<in> formula"
by (simp add: or_fm_def)

lemma sats_or_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, or_fm(x,y,z), env) <->
        is_or(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: or_fm_def is_or_def)

lemma is_or_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> is_or(**A, x, y, z) <-> sats(A, or_fm(i,j,k), env)"
by simp

theorem is_or_reflection:
     "REFLECTS[\<lambda>x. is_or(L,f(x),g(x),h(x)),
               \<lambda>i x. is_or(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: is_or_def setclass_simps)
apply (intro FOL_reflections function_reflections)
done



subsubsection{*The Operator @{term is_not}, Internalized*}

(* is_not(M,a,z) == (number1(M,a)  & empty(M,z)) | 
                     (~number1(M,a) & number1(M,z)) *)
constdefs not_fm :: "[i,i]=>i"
    "not_fm(a,z) ==
       Or(And(number1_fm(a), empty_fm(z)),
          And(Neg(number1_fm(a)), number1_fm(z)))"

lemma is_not_type [TC]:
     "[| x \<in> nat; z \<in> nat |] ==> not_fm(x,z) \<in> formula"
by (simp add: not_fm_def)

lemma sats_is_not_fm [simp]:
   "[| x \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, not_fm(x,z), env) <-> is_not(**A, nth(x,env), nth(z,env))"
by (simp add: not_fm_def is_not_def)

lemma is_not_iff_sats:
      "[| nth(i,env) = x; nth(k,env) = z;
          i \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> is_not(**A, x, z) <-> sats(A, not_fm(i,k), env)"
by simp

theorem is_not_reflection:
     "REFLECTS[\<lambda>x. is_not(L,f(x),g(x)),
               \<lambda>i x. is_not(**Lset(i),f(x),g(x))]"
apply (simp only: is_not_def setclass_simps)
apply (intro FOL_reflections function_reflections)
done


lemmas extra_reflections = 
    Inl_reflection Inr_reflection Nil_reflection Cons_reflection
    quasilist_reflection hd_reflection tl_reflection bool_of_o_reflection
    is_lambda_reflection Member_reflection Equal_reflection Nand_reflection
    Forall_reflection is_and_reflection is_or_reflection is_not_reflection

lemmas extra_iff_sats =
    Inl_iff_sats Inr_iff_sats Nil_iff_sats Cons_iff_sats quasilist_iff_sats
    hd_iff_sats tl_iff_sats is_bool_of_o_iff_sats is_lambda_iff_sats
    Member_iff_sats Equal_iff_sats Nand_iff_sats Forall_iff_sats 
    is_and_iff_sats is_or_iff_sats is_not_iff_sats


subsection{*Well-Founded Recursion!*}


text{*Alternative definition, minimizing nesting of quantifiers around MH*}
lemma M_is_recfun_iff:
   "M_is_recfun(M,MH,r,a,f) <->
    (\<forall>z[M]. z \<in> f <-> 
     (\<exists>x[M]. \<exists>f_r_sx[M]. \<exists>y[M]. 
             MH(x, f_r_sx, y) & pair(M,x,y,z) &
             (\<exists>xa[M]. \<exists>sx[M]. \<exists>r_sx[M]. 
                pair(M,x,a,xa) & upair(M,x,x,sx) &
               pre_image(M,r,sx,r_sx) & restriction(M,f,r_sx,f_r_sx) &
               xa \<in> r)))"
apply (simp add: M_is_recfun_def)
apply (rule rall_cong, blast) 
done


(* M_is_recfun :: "[i=>o, [i,i,i]=>o, i, i, i] => o"
   "M_is_recfun(M,MH,r,a,f) ==
     \<forall>z[M]. z \<in> f <->
               2      1           0
new def     (\<exists>x[M]. \<exists>f_r_sx[M]. \<exists>y[M]. 
             MH(x, f_r_sx, y) & pair(M,x,y,z) &
             (\<exists>xa[M]. \<exists>sx[M]. \<exists>r_sx[M]. 
                pair(M,x,a,xa) & upair(M,x,x,sx) &
               pre_image(M,r,sx,r_sx) & restriction(M,f,r_sx,f_r_sx) &
               xa \<in> r)"
*)

text{*The three arguments of @{term p} are always 2, 1, 0 and z*}
constdefs is_recfun_fm :: "[i, i, i, i]=>i"
 "is_recfun_fm(p,r,a,f) == 
   Forall(Iff(Member(0,succ(f)),
    Exists(Exists(Exists(
     And(p, 
      And(pair_fm(2,0,3),
       Exists(Exists(Exists(
	And(pair_fm(5,a#+7,2),
	 And(upair_fm(5,5,1),
	  And(pre_image_fm(r#+7,1,0),
	   And(restriction_fm(f#+7,0,4), Member(2,r#+7)))))))))))))))"

lemma is_recfun_type [TC]:
     "[| p \<in> formula; x \<in> nat; y \<in> nat; z \<in> nat |] 
      ==> is_recfun_fm(p,x,y,z) \<in> formula"
by (simp add: is_recfun_fm_def)


lemma sats_is_recfun_fm:
  assumes MH_iff_sats: 
      "!!a0 a1 a2 a3. 
        [|a0\<in>A; a1\<in>A; a2\<in>A; a3\<in>A|] 
        ==> MH(a2, a1, a0) <-> sats(A, p, Cons(a0,Cons(a1,Cons(a2,Cons(a3,env)))))"
  shows 
      "[|x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
       ==> sats(A, is_recfun_fm(p,x,y,z), env) <->
           M_is_recfun(**A, MH, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: is_recfun_fm_def M_is_recfun_iff MH_iff_sats [THEN iff_sym])

lemma is_recfun_iff_sats:
  assumes MH_iff_sats: 
      "!!a0 a1 a2 a3. 
        [|a0\<in>A; a1\<in>A; a2\<in>A; a3\<in>A|] 
        ==> MH(a2, a1, a0) <-> sats(A, p, Cons(a0,Cons(a1,Cons(a2,Cons(a3,env)))))"
  shows
  "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
      i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
   ==> M_is_recfun(**A, MH, x, y, z) <-> sats(A, is_recfun_fm(p,i,j,k), env)"
by (simp add: sats_is_recfun_fm [OF MH_iff_sats]) 

text{*The additional variable in the premise, namely @{term f'}, is essential.
It lets @{term MH} depend upon @{term x}, which seems often necessary.
The same thing occurs in @{text is_wfrec_reflection}.*}
theorem is_recfun_reflection:
  assumes MH_reflection:
    "!!f' f g h. REFLECTS[\<lambda>x. MH(L, f'(x), f(x), g(x), h(x)), 
                     \<lambda>i x. MH(**Lset(i), f'(x), f(x), g(x), h(x))]"
  shows "REFLECTS[\<lambda>x. M_is_recfun(L, MH(L,x), f(x), g(x), h(x)), 
             \<lambda>i x. M_is_recfun(**Lset(i), MH(**Lset(i),x), f(x), g(x), h(x))]"
apply (simp (no_asm_use) only: M_is_recfun_def setclass_simps)
apply (intro FOL_reflections function_reflections
             restriction_reflection MH_reflection)
done

subsubsection{*The Operator @{term is_wfrec}*}

text{*The three arguments of @{term p} are always 2, 1, 0*}

(* is_wfrec :: "[i=>o, i, [i,i,i]=>o, i, i] => o"
    "is_wfrec(M,MH,r,a,z) == 
      \<exists>f[M]. M_is_recfun(M,MH,r,a,f) & MH(a,f,z)" *)
constdefs is_wfrec_fm :: "[i, i, i, i]=>i"
 "is_wfrec_fm(p,r,a,z) == 
    Exists(And(is_recfun_fm(p, succ(r), succ(a), 0),
           Exists(Exists(Exists(Exists(
             And(Equal(2,a#+5), And(Equal(1,4), And(Equal(0,z#+5), p)))))))))"

text{*We call @{term p} with arguments a, f, z by equating them with 
  the corresponding quantified variables with de Bruijn indices 2, 1, 0.*}

text{*There's an additional existential quantifier to ensure that the
      environments in both calls to MH have the same length.*}

lemma is_wfrec_type [TC]:
     "[| p \<in> formula; x \<in> nat; y \<in> nat; z \<in> nat |] 
      ==> is_wfrec_fm(p,x,y,z) \<in> formula"
by (simp add: is_wfrec_fm_def) 

lemma sats_is_wfrec_fm:
  assumes MH_iff_sats: 
      "!!a0 a1 a2 a3 a4. 
        [|a0\<in>A; a1\<in>A; a2\<in>A; a3\<in>A; a4\<in>A|] 
        ==> MH(a2, a1, a0) <-> sats(A, p, Cons(a0,Cons(a1,Cons(a2,Cons(a3,Cons(a4,env))))))"
  shows 
      "[|x \<in> nat; y < length(env); z < length(env); env \<in> list(A)|]
       ==> sats(A, is_wfrec_fm(p,x,y,z), env) <-> 
           is_wfrec(**A, MH, nth(x,env), nth(y,env), nth(z,env))"
apply (frule_tac x=z in lt_length_in_nat, assumption)  
apply (frule lt_length_in_nat, assumption)  
apply (simp add: is_wfrec_fm_def sats_is_recfun_fm is_wfrec_def MH_iff_sats [THEN iff_sym], blast) 
done


lemma is_wfrec_iff_sats:
  assumes MH_iff_sats: 
      "!!a0 a1 a2 a3 a4. 
        [|a0\<in>A; a1\<in>A; a2\<in>A; a3\<in>A; a4\<in>A|] 
        ==> MH(a2, a1, a0) <-> sats(A, p, Cons(a0,Cons(a1,Cons(a2,Cons(a3,Cons(a4,env))))))"
  shows
  "[|nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
      i \<in> nat; j < length(env); k < length(env); env \<in> list(A)|]
   ==> is_wfrec(**A, MH, x, y, z) <-> sats(A, is_wfrec_fm(p,i,j,k), env)" 
by (simp add: sats_is_wfrec_fm [OF MH_iff_sats])

theorem is_wfrec_reflection:
  assumes MH_reflection:
    "!!f' f g h. REFLECTS[\<lambda>x. MH(L, f'(x), f(x), g(x), h(x)), 
                     \<lambda>i x. MH(**Lset(i), f'(x), f(x), g(x), h(x))]"
  shows "REFLECTS[\<lambda>x. is_wfrec(L, MH(L,x), f(x), g(x), h(x)), 
               \<lambda>i x. is_wfrec(**Lset(i), MH(**Lset(i),x), f(x), g(x), h(x))]"
apply (simp (no_asm_use) only: is_wfrec_def setclass_simps)
apply (intro FOL_reflections MH_reflection is_recfun_reflection)
done


subsection{*For Datatypes*}

subsubsection{*Binary Products, Internalized*}

constdefs cartprod_fm :: "[i,i,i]=>i"
(* "cartprod(M,A,B,z) ==
        \<forall>u[M]. u \<in> z <-> (\<exists>x[M]. x\<in>A & (\<exists>y[M]. y\<in>B & pair(M,x,y,u)))" *)
    "cartprod_fm(A,B,z) ==
       Forall(Iff(Member(0,succ(z)),
                  Exists(And(Member(0,succ(succ(A))),
                         Exists(And(Member(0,succ(succ(succ(B)))),
                                    pair_fm(1,0,2)))))))"

lemma cartprod_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> cartprod_fm(x,y,z) \<in> formula"
by (simp add: cartprod_fm_def)

lemma arity_cartprod_fm [simp]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |]
      ==> arity(cartprod_fm(x,y,z)) = succ(x) \<union> succ(y) \<union> succ(z)"
by (simp add: cartprod_fm_def succ_Un_distrib [symmetric] Un_ac)

lemma sats_cartprod_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, cartprod_fm(x,y,z), env) <->
        cartprod(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: cartprod_fm_def cartprod_def)

lemma cartprod_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> cartprod(**A, x, y, z) <-> sats(A, cartprod_fm(i,j,k), env)"
by (simp add: sats_cartprod_fm)

theorem cartprod_reflection:
     "REFLECTS[\<lambda>x. cartprod(L,f(x),g(x),h(x)),
               \<lambda>i x. cartprod(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: cartprod_def setclass_simps)
apply (intro FOL_reflections pair_reflection)
done


subsubsection{*Binary Sums, Internalized*}

(* "is_sum(M,A,B,Z) ==
       \<exists>A0[M]. \<exists>n1[M]. \<exists>s1[M]. \<exists>B1[M].
         3      2       1        0
       number1(M,n1) & cartprod(M,n1,A,A0) & upair(M,n1,n1,s1) &
       cartprod(M,s1,B,B1) & union(M,A0,B1,Z)"  *)
constdefs sum_fm :: "[i,i,i]=>i"
    "sum_fm(A,B,Z) ==
       Exists(Exists(Exists(Exists(
        And(number1_fm(2),
            And(cartprod_fm(2,A#+4,3),
                And(upair_fm(2,2,1),
                    And(cartprod_fm(1,B#+4,0), union_fm(3,0,Z#+4)))))))))"

lemma sum_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> sum_fm(x,y,z) \<in> formula"
by (simp add: sum_fm_def)

lemma arity_sum_fm [simp]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |]
      ==> arity(sum_fm(x,y,z)) = succ(x) \<union> succ(y) \<union> succ(z)"
by (simp add: sum_fm_def succ_Un_distrib [symmetric] Un_ac)

lemma sats_sum_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, sum_fm(x,y,z), env) <->
        is_sum(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: sum_fm_def is_sum_def)

lemma sum_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> is_sum(**A, x, y, z) <-> sats(A, sum_fm(i,j,k), env)"
by simp

theorem sum_reflection:
     "REFLECTS[\<lambda>x. is_sum(L,f(x),g(x),h(x)),
               \<lambda>i x. is_sum(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: is_sum_def setclass_simps)
apply (intro FOL_reflections function_reflections cartprod_reflection)
done


subsubsection{*The Operator @{term quasinat}*}

(* "is_quasinat(M,z) == empty(M,z) | (\<exists>m[M]. successor(M,m,z))" *)
constdefs quasinat_fm :: "i=>i"
    "quasinat_fm(z) == Or(empty_fm(z), Exists(succ_fm(0,succ(z))))"

lemma quasinat_type [TC]:
     "x \<in> nat ==> quasinat_fm(x) \<in> formula"
by (simp add: quasinat_fm_def)

lemma arity_quasinat_fm [simp]:
     "x \<in> nat ==> arity(quasinat_fm(x)) = succ(x)"
by (simp add: quasinat_fm_def succ_Un_distrib [symmetric] Un_ac)

lemma sats_quasinat_fm [simp]:
   "[| x \<in> nat; env \<in> list(A)|]
    ==> sats(A, quasinat_fm(x), env) <-> is_quasinat(**A, nth(x,env))"
by (simp add: quasinat_fm_def is_quasinat_def)

lemma quasinat_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; env \<in> list(A)|]
       ==> is_quasinat(**A, x) <-> sats(A, quasinat_fm(i), env)"
by simp

theorem quasinat_reflection:
     "REFLECTS[\<lambda>x. is_quasinat(L,f(x)),
               \<lambda>i x. is_quasinat(**Lset(i),f(x))]"
apply (simp only: is_quasinat_def setclass_simps)
apply (intro FOL_reflections function_reflections)
done


subsubsection{*The Operator @{term is_nat_case}*}
text{*I could not get it to work with the more natural assumption that 
 @{term is_b} takes two arguments.  Instead it must be a formula where 1 and 0
 stand for @{term m} and @{term b}, respectively.*}

(* is_nat_case :: "[i=>o, i, [i,i]=>o, i, i] => o"
    "is_nat_case(M, a, is_b, k, z) ==
       (empty(M,k) --> z=a) &
       (\<forall>m[M]. successor(M,m,k) --> is_b(m,z)) &
       (is_quasinat(M,k) | empty(M,z))" *)
text{*The formula @{term is_b} has free variables 1 and 0.*}
constdefs is_nat_case_fm :: "[i, i, i, i]=>i"
 "is_nat_case_fm(a,is_b,k,z) == 
    And(Implies(empty_fm(k), Equal(z,a)),
        And(Forall(Implies(succ_fm(0,succ(k)), 
                   Forall(Implies(Equal(0,succ(succ(z))), is_b)))),
            Or(quasinat_fm(k), empty_fm(z))))"

lemma is_nat_case_type [TC]:
     "[| is_b \<in> formula;  
         x \<in> nat; y \<in> nat; z \<in> nat |] 
      ==> is_nat_case_fm(x,is_b,y,z) \<in> formula"
by (simp add: is_nat_case_fm_def)

lemma sats_is_nat_case_fm:
  assumes is_b_iff_sats: 
      "!!a. a \<in> A ==> is_b(a,nth(z, env)) <-> 
                      sats(A, p, Cons(nth(z,env), Cons(a, env)))"
  shows 
      "[|x \<in> nat; y \<in> nat; z < length(env); env \<in> list(A)|]
       ==> sats(A, is_nat_case_fm(x,p,y,z), env) <->
           is_nat_case(**A, nth(x,env), is_b, nth(y,env), nth(z,env))"
apply (frule lt_length_in_nat, assumption)
apply (simp add: is_nat_case_fm_def is_nat_case_def is_b_iff_sats [THEN iff_sym])
done

lemma is_nat_case_iff_sats:
  "[| (!!a. a \<in> A ==> is_b(a,z) <->
                      sats(A, p, Cons(z, Cons(a,env))));
      nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
      i \<in> nat; j \<in> nat; k < length(env); env \<in> list(A)|]
   ==> is_nat_case(**A, x, is_b, y, z) <-> sats(A, is_nat_case_fm(i,p,j,k), env)"
by (simp add: sats_is_nat_case_fm [of A is_b])


text{*The second argument of @{term is_b} gives it direct access to @{term x},
  which is essential for handling free variable references.  Without this
  argument, we cannot prove reflection for @{term iterates_MH}.*}
theorem is_nat_case_reflection:
  assumes is_b_reflection:
    "!!h f g. REFLECTS[\<lambda>x. is_b(L, h(x), f(x), g(x)),
                     \<lambda>i x. is_b(**Lset(i), h(x), f(x), g(x))]"
  shows "REFLECTS[\<lambda>x. is_nat_case(L, f(x), is_b(L,x), g(x), h(x)),
               \<lambda>i x. is_nat_case(**Lset(i), f(x), is_b(**Lset(i), x), g(x), h(x))]"
apply (simp (no_asm_use) only: is_nat_case_def setclass_simps)
apply (intro FOL_reflections function_reflections
             restriction_reflection is_b_reflection quasinat_reflection)
done


subsection{*The Operator @{term iterates_MH}, Needed for Iteration*}

(*  iterates_MH :: "[i=>o, [i,i]=>o, i, i, i, i] => o"
   "iterates_MH(M,isF,v,n,g,z) ==
        is_nat_case(M, v, \<lambda>m u. \<exists>gm[M]. fun_apply(M,g,m,gm) & isF(gm,u),
                    n, z)" *)
constdefs iterates_MH_fm :: "[i, i, i, i, i]=>i"
 "iterates_MH_fm(isF,v,n,g,z) == 
    is_nat_case_fm(v, 
      Exists(And(fun_apply_fm(succ(succ(succ(g))),2,0), 
                     Forall(Implies(Equal(0,2), isF)))), 
      n, z)"

lemma iterates_MH_type [TC]:
     "[| p \<in> formula;  
         v \<in> nat; x \<in> nat; y \<in> nat; z \<in> nat |] 
      ==> iterates_MH_fm(p,v,x,y,z) \<in> formula"
by (simp add: iterates_MH_fm_def)

lemma sats_iterates_MH_fm:
  assumes is_F_iff_sats:
      "!!a b c d. [| a \<in> A; b \<in> A; c \<in> A; d \<in> A|]
              ==> is_F(a,b) <->
                  sats(A, p, Cons(b, Cons(a, Cons(c, Cons(d,env)))))"
  shows 
      "[|v \<in> nat; x \<in> nat; y \<in> nat; z < length(env); env \<in> list(A)|]
       ==> sats(A, iterates_MH_fm(p,v,x,y,z), env) <->
           iterates_MH(**A, is_F, nth(v,env), nth(x,env), nth(y,env), nth(z,env))"
apply (frule lt_length_in_nat, assumption)  
apply (simp add: iterates_MH_fm_def iterates_MH_def sats_is_nat_case_fm 
              is_F_iff_sats [symmetric])
apply (rule is_nat_case_cong) 
apply (simp_all add: setclass_def)
done

lemma iterates_MH_iff_sats:
  assumes is_F_iff_sats:
      "!!a b c d. [| a \<in> A; b \<in> A; c \<in> A; d \<in> A|]
              ==> is_F(a,b) <->
                  sats(A, p, Cons(b, Cons(a, Cons(c, Cons(d,env)))))"
  shows 
  "[| nth(i',env) = v; nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
      i' \<in> nat; i \<in> nat; j \<in> nat; k < length(env); env \<in> list(A)|]
   ==> iterates_MH(**A, is_F, v, x, y, z) <->
       sats(A, iterates_MH_fm(p,i',i,j,k), env)"
by (simp add: sats_iterates_MH_fm [OF is_F_iff_sats]) 

text{*The second argument of @{term p} gives it direct access to @{term x},
  which is essential for handling free variable references.  Without this
  argument, we cannot prove reflection for @{term list_N}.*}
theorem iterates_MH_reflection:
  assumes p_reflection:
    "!!f g h. REFLECTS[\<lambda>x. p(L, h(x), f(x), g(x)),
                     \<lambda>i x. p(**Lset(i), h(x), f(x), g(x))]"
 shows "REFLECTS[\<lambda>x. iterates_MH(L, p(L,x), e(x), f(x), g(x), h(x)),
               \<lambda>i x. iterates_MH(**Lset(i), p(**Lset(i),x), e(x), f(x), g(x), h(x))]"
apply (simp (no_asm_use) only: iterates_MH_def)
txt{*Must be careful: simplifying with @{text setclass_simps} above would
     change @{text "\<exists>gm[**Lset(i)]"} into @{text "\<exists>gm \<in> Lset(i)"}, when
     it would no longer match rule @{text is_nat_case_reflection}. *}
apply (rule is_nat_case_reflection)
apply (simp (no_asm_use) only: setclass_simps)
apply (intro FOL_reflections function_reflections is_nat_case_reflection
             restriction_reflection p_reflection)
done



subsubsection{*The Formula @{term is_eclose_n}, Internalized*}

(* is_eclose_n(M,A,n,Z) == 
      \<exists>sn[M]. \<exists>msn[M]. 
       1       0
       successor(M,n,sn) & membership(M,sn,msn) &
       is_wfrec(M, iterates_MH(M, big_union(M), A), msn, n, Z) *)

constdefs eclose_n_fm :: "[i,i,i]=>i"
  "eclose_n_fm(A,n,Z) == 
     Exists(Exists(
      And(succ_fm(n#+2,1),
       And(Memrel_fm(1,0),
              is_wfrec_fm(iterates_MH_fm(big_union_fm(1,0),
                                         A#+7, 2, 1, 0), 
                           0, n#+2, Z#+2)))))"

lemma eclose_n_fm_type [TC]:
 "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> eclose_n_fm(x,y,z) \<in> formula"
by (simp add: eclose_n_fm_def)

lemma sats_eclose_n_fm [simp]:
   "[| x \<in> nat; y < length(env); z < length(env); env \<in> list(A)|]
    ==> sats(A, eclose_n_fm(x,y,z), env) <->
        is_eclose_n(**A, nth(x,env), nth(y,env), nth(z,env))"
apply (frule_tac x=z in lt_length_in_nat, assumption)  
apply (frule_tac x=y in lt_length_in_nat, assumption)  
apply (simp add: eclose_n_fm_def is_eclose_n_def sats_is_wfrec_fm 
                 sats_iterates_MH_fm) 
done

lemma eclose_n_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j < length(env); k < length(env); env \<in> list(A)|]
       ==> is_eclose_n(**A, x, y, z) <-> sats(A, eclose_n_fm(i,j,k), env)"
by (simp add: sats_eclose_n_fm)

theorem eclose_n_reflection:
     "REFLECTS[\<lambda>x. is_eclose_n(L, f(x), g(x), h(x)),  
               \<lambda>i x. is_eclose_n(**Lset(i), f(x), g(x), h(x))]"
apply (simp only: is_eclose_n_def setclass_simps)
apply (intro FOL_reflections function_reflections is_wfrec_reflection 
             iterates_MH_reflection) 
done


subsubsection{*Membership in @{term "eclose(A)"}*}

(* mem_eclose(M,A,l) == 
      \<exists>n[M]. \<exists>eclosen[M]. 
       finite_ordinal(M,n) & is_eclose_n(M,A,n,eclosen) & l \<in> eclosen *)
constdefs mem_eclose_fm :: "[i,i]=>i"
    "mem_eclose_fm(x,y) ==
       Exists(Exists(
         And(finite_ordinal_fm(1),
           And(eclose_n_fm(x#+2,1,0), Member(y#+2,0)))))"

lemma mem_eclose_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> mem_eclose_fm(x,y) \<in> formula"
by (simp add: mem_eclose_fm_def)

lemma sats_mem_eclose_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, mem_eclose_fm(x,y), env) <-> mem_eclose(**A, nth(x,env), nth(y,env))"
by (simp add: mem_eclose_fm_def mem_eclose_def)

lemma mem_eclose_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> mem_eclose(**A, x, y) <-> sats(A, mem_eclose_fm(i,j), env)"
by simp

theorem mem_eclose_reflection:
     "REFLECTS[\<lambda>x. mem_eclose(L,f(x),g(x)),
               \<lambda>i x. mem_eclose(**Lset(i),f(x),g(x))]"
apply (simp only: mem_eclose_def setclass_simps)
apply (intro FOL_reflections finite_ordinal_reflection eclose_n_reflection)
done


subsubsection{*The Predicate ``Is @{term "eclose(A)"}''*}

(* is_eclose(M,A,Z) == \<forall>l[M]. l \<in> Z <-> mem_eclose(M,A,l) *)
constdefs is_eclose_fm :: "[i,i]=>i"
    "is_eclose_fm(A,Z) ==
       Forall(Iff(Member(0,succ(Z)), mem_eclose_fm(succ(A),0)))"

lemma is_eclose_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> is_eclose_fm(x,y) \<in> formula"
by (simp add: is_eclose_fm_def)

lemma sats_is_eclose_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, is_eclose_fm(x,y), env) <-> is_eclose(**A, nth(x,env), nth(y,env))"
by (simp add: is_eclose_fm_def is_eclose_def)

lemma is_eclose_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> is_eclose(**A, x, y) <-> sats(A, is_eclose_fm(i,j), env)"
by simp

theorem is_eclose_reflection:
     "REFLECTS[\<lambda>x. is_eclose(L,f(x),g(x)),
               \<lambda>i x. is_eclose(**Lset(i),f(x),g(x))]"
apply (simp only: is_eclose_def setclass_simps)
apply (intro FOL_reflections mem_eclose_reflection)
done


subsubsection{*The List Functor, Internalized*}

constdefs list_functor_fm :: "[i,i,i]=>i"
(* "is_list_functor(M,A,X,Z) ==
        \<exists>n1[M]. \<exists>AX[M].
         number1(M,n1) & cartprod(M,A,X,AX) & is_sum(M,n1,AX,Z)" *)
    "list_functor_fm(A,X,Z) ==
       Exists(Exists(
        And(number1_fm(1),
            And(cartprod_fm(A#+2,X#+2,0), sum_fm(1,0,Z#+2)))))"

lemma list_functor_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> list_functor_fm(x,y,z) \<in> formula"
by (simp add: list_functor_fm_def)

lemma arity_list_functor_fm [simp]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |]
      ==> arity(list_functor_fm(x,y,z)) = succ(x) \<union> succ(y) \<union> succ(z)"
by (simp add: list_functor_fm_def succ_Un_distrib [symmetric] Un_ac)

lemma sats_list_functor_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, list_functor_fm(x,y,z), env) <->
        is_list_functor(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: list_functor_fm_def is_list_functor_def)

lemma list_functor_iff_sats:
  "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
      i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
   ==> is_list_functor(**A, x, y, z) <-> sats(A, list_functor_fm(i,j,k), env)"
by simp

theorem list_functor_reflection:
     "REFLECTS[\<lambda>x. is_list_functor(L,f(x),g(x),h(x)),
               \<lambda>i x. is_list_functor(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: is_list_functor_def setclass_simps)
apply (intro FOL_reflections number1_reflection
             cartprod_reflection sum_reflection)
done


subsubsection{*The Formula @{term is_list_N}, Internalized*}

(* "is_list_N(M,A,n,Z) == 
      \<exists>zero[M]. \<exists>sn[M]. \<exists>msn[M]. 
       empty(M,zero) & 
       successor(M,n,sn) & membership(M,sn,msn) &
       is_wfrec(M, iterates_MH(M, is_list_functor(M,A),zero), msn, n, Z)" *)
  
constdefs list_N_fm :: "[i,i,i]=>i"
  "list_N_fm(A,n,Z) == 
     Exists(Exists(Exists(
       And(empty_fm(2),
         And(succ_fm(n#+3,1),
          And(Memrel_fm(1,0),
              is_wfrec_fm(iterates_MH_fm(list_functor_fm(A#+9#+3,1,0),
                                         7,2,1,0), 
                           0, n#+3, Z#+3)))))))"

lemma list_N_fm_type [TC]:
 "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> list_N_fm(x,y,z) \<in> formula"
by (simp add: list_N_fm_def)

lemma sats_list_N_fm [simp]:
   "[| x \<in> nat; y < length(env); z < length(env); env \<in> list(A)|]
    ==> sats(A, list_N_fm(x,y,z), env) <->
        is_list_N(**A, nth(x,env), nth(y,env), nth(z,env))"
apply (frule_tac x=z in lt_length_in_nat, assumption)  
apply (frule_tac x=y in lt_length_in_nat, assumption)  
apply (simp add: list_N_fm_def is_list_N_def sats_is_wfrec_fm 
                 sats_iterates_MH_fm) 
done

lemma list_N_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j < length(env); k < length(env); env \<in> list(A)|]
       ==> is_list_N(**A, x, y, z) <-> sats(A, list_N_fm(i,j,k), env)"
by (simp add: sats_list_N_fm)

theorem list_N_reflection:
     "REFLECTS[\<lambda>x. is_list_N(L, f(x), g(x), h(x)),  
               \<lambda>i x. is_list_N(**Lset(i), f(x), g(x), h(x))]"
apply (simp only: is_list_N_def setclass_simps)
apply (intro FOL_reflections function_reflections is_wfrec_reflection 
             iterates_MH_reflection list_functor_reflection) 
done



subsubsection{*The Predicate ``Is A List''*}

(* mem_list(M,A,l) == 
      \<exists>n[M]. \<exists>listn[M]. 
       finite_ordinal(M,n) & is_list_N(M,A,n,listn) & l \<in> listn *)
constdefs mem_list_fm :: "[i,i]=>i"
    "mem_list_fm(x,y) ==
       Exists(Exists(
         And(finite_ordinal_fm(1),
           And(list_N_fm(x#+2,1,0), Member(y#+2,0)))))"

lemma mem_list_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> mem_list_fm(x,y) \<in> formula"
by (simp add: mem_list_fm_def)

lemma sats_mem_list_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, mem_list_fm(x,y), env) <-> mem_list(**A, nth(x,env), nth(y,env))"
by (simp add: mem_list_fm_def mem_list_def)

lemma mem_list_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> mem_list(**A, x, y) <-> sats(A, mem_list_fm(i,j), env)"
by simp

theorem mem_list_reflection:
     "REFLECTS[\<lambda>x. mem_list(L,f(x),g(x)),
               \<lambda>i x. mem_list(**Lset(i),f(x),g(x))]"
apply (simp only: mem_list_def setclass_simps)
apply (intro FOL_reflections finite_ordinal_reflection list_N_reflection)
done


subsubsection{*The Predicate ``Is @{term "list(A)"}''*}

(* is_list(M,A,Z) == \<forall>l[M]. l \<in> Z <-> mem_list(M,A,l) *)
constdefs is_list_fm :: "[i,i]=>i"
    "is_list_fm(A,Z) ==
       Forall(Iff(Member(0,succ(Z)), mem_list_fm(succ(A),0)))"

lemma is_list_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> is_list_fm(x,y) \<in> formula"
by (simp add: is_list_fm_def)

lemma sats_is_list_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, is_list_fm(x,y), env) <-> is_list(**A, nth(x,env), nth(y,env))"
by (simp add: is_list_fm_def is_list_def)

lemma is_list_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> is_list(**A, x, y) <-> sats(A, is_list_fm(i,j), env)"
by simp

theorem is_list_reflection:
     "REFLECTS[\<lambda>x. is_list(L,f(x),g(x)),
               \<lambda>i x. is_list(**Lset(i),f(x),g(x))]"
apply (simp only: is_list_def setclass_simps)
apply (intro FOL_reflections mem_list_reflection)
done


subsubsection{*The Formula Functor, Internalized*}

constdefs formula_functor_fm :: "[i,i]=>i"
(*     "is_formula_functor(M,X,Z) ==
        \<exists>nat'[M]. \<exists>natnat[M]. \<exists>natnatsum[M]. \<exists>XX[M]. \<exists>X3[M].
           4           3               2       1       0
          omega(M,nat') & cartprod(M,nat',nat',natnat) &
          is_sum(M,natnat,natnat,natnatsum) &
          cartprod(M,X,X,XX) & is_sum(M,XX,X,X3) &
          is_sum(M,natnatsum,X3,Z)" *)
    "formula_functor_fm(X,Z) ==
       Exists(Exists(Exists(Exists(Exists(
        And(omega_fm(4),
         And(cartprod_fm(4,4,3),
          And(sum_fm(3,3,2),
           And(cartprod_fm(X#+5,X#+5,1),
            And(sum_fm(1,X#+5,0), sum_fm(2,0,Z#+5)))))))))))"

lemma formula_functor_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> formula_functor_fm(x,y) \<in> formula"
by (simp add: formula_functor_fm_def)

lemma sats_formula_functor_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, formula_functor_fm(x,y), env) <->
        is_formula_functor(**A, nth(x,env), nth(y,env))"
by (simp add: formula_functor_fm_def is_formula_functor_def)

lemma formula_functor_iff_sats:
  "[| nth(i,env) = x; nth(j,env) = y;
      i \<in> nat; j \<in> nat; env \<in> list(A)|]
   ==> is_formula_functor(**A, x, y) <-> sats(A, formula_functor_fm(i,j), env)"
by simp

theorem formula_functor_reflection:
     "REFLECTS[\<lambda>x. is_formula_functor(L,f(x),g(x)),
               \<lambda>i x. is_formula_functor(**Lset(i),f(x),g(x))]"
apply (simp only: is_formula_functor_def setclass_simps)
apply (intro FOL_reflections omega_reflection
             cartprod_reflection sum_reflection)
done


subsubsection{*The Formula @{term is_formula_N}, Internalized*}

(* "is_formula_N(M,n,Z) == 
      \<exists>zero[M]. \<exists>sn[M]. \<exists>msn[M]. 
          2       1       0
       empty(M,zero) & 
       successor(M,n,sn) & membership(M,sn,msn) &
       is_wfrec(M, iterates_MH(M, is_formula_functor(M),zero), msn, n, Z)" *) 
constdefs formula_N_fm :: "[i,i]=>i"
  "formula_N_fm(n,Z) == 
     Exists(Exists(Exists(
       And(empty_fm(2),
         And(succ_fm(n#+3,1),
          And(Memrel_fm(1,0),
              is_wfrec_fm(iterates_MH_fm(formula_functor_fm(1,0),7,2,1,0), 
                           0, n#+3, Z#+3)))))))"

lemma formula_N_fm_type [TC]:
 "[| x \<in> nat; y \<in> nat |] ==> formula_N_fm(x,y) \<in> formula"
by (simp add: formula_N_fm_def)

lemma sats_formula_N_fm [simp]:
   "[| x < length(env); y < length(env); env \<in> list(A)|]
    ==> sats(A, formula_N_fm(x,y), env) <->
        is_formula_N(**A, nth(x,env), nth(y,env))"
apply (frule_tac x=y in lt_length_in_nat, assumption)  
apply (frule lt_length_in_nat, assumption)  
apply (simp add: formula_N_fm_def is_formula_N_def sats_is_wfrec_fm sats_iterates_MH_fm) 
done

lemma formula_N_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; 
          i < length(env); j < length(env); env \<in> list(A)|]
       ==> is_formula_N(**A, x, y) <-> sats(A, formula_N_fm(i,j), env)"
by (simp add: sats_formula_N_fm)

theorem formula_N_reflection:
     "REFLECTS[\<lambda>x. is_formula_N(L, f(x), g(x)),  
               \<lambda>i x. is_formula_N(**Lset(i), f(x), g(x))]"
apply (simp only: is_formula_N_def setclass_simps)
apply (intro FOL_reflections function_reflections is_wfrec_reflection 
             iterates_MH_reflection formula_functor_reflection) 
done



subsubsection{*The Predicate ``Is A Formula''*}

(*  mem_formula(M,p) == 
      \<exists>n[M]. \<exists>formn[M]. 
       finite_ordinal(M,n) & is_formula_N(M,n,formn) & p \<in> formn *)
constdefs mem_formula_fm :: "i=>i"
    "mem_formula_fm(x) ==
       Exists(Exists(
         And(finite_ordinal_fm(1),
           And(formula_N_fm(1,0), Member(x#+2,0)))))"

lemma mem_formula_type [TC]:
     "x \<in> nat ==> mem_formula_fm(x) \<in> formula"
by (simp add: mem_formula_fm_def)

lemma sats_mem_formula_fm [simp]:
   "[| x \<in> nat; env \<in> list(A)|]
    ==> sats(A, mem_formula_fm(x), env) <-> mem_formula(**A, nth(x,env))"
by (simp add: mem_formula_fm_def mem_formula_def)

lemma mem_formula_iff_sats:
      "[| nth(i,env) = x; i \<in> nat; env \<in> list(A)|]
       ==> mem_formula(**A, x) <-> sats(A, mem_formula_fm(i), env)"
by simp

theorem mem_formula_reflection:
     "REFLECTS[\<lambda>x. mem_formula(L,f(x)),
               \<lambda>i x. mem_formula(**Lset(i),f(x))]"
apply (simp only: mem_formula_def setclass_simps)
apply (intro FOL_reflections finite_ordinal_reflection formula_N_reflection)
done



subsubsection{*The Predicate ``Is @{term "formula"}''*}

(* is_formula(M,Z) == \<forall>p[M]. p \<in> Z <-> mem_formula(M,p) *)
constdefs is_formula_fm :: "i=>i"
    "is_formula_fm(Z) == Forall(Iff(Member(0,succ(Z)), mem_formula_fm(0)))"

lemma is_formula_type [TC]:
     "x \<in> nat ==> is_formula_fm(x) \<in> formula"
by (simp add: is_formula_fm_def)

lemma sats_is_formula_fm [simp]:
   "[| x \<in> nat; env \<in> list(A)|]
    ==> sats(A, is_formula_fm(x), env) <-> is_formula(**A, nth(x,env))"
by (simp add: is_formula_fm_def is_formula_def)

lemma is_formula_iff_sats:
      "[| nth(i,env) = x; i \<in> nat; env \<in> list(A)|]
       ==> is_formula(**A, x) <-> sats(A, is_formula_fm(i), env)"
by simp

theorem is_formula_reflection:
     "REFLECTS[\<lambda>x. is_formula(L,f(x)),
               \<lambda>i x. is_formula(**Lset(i),f(x))]"
apply (simp only: is_formula_def setclass_simps)
apply (intro FOL_reflections mem_formula_reflection)
done


subsubsection{*The Operator @{term is_transrec}*}

text{*The three arguments of @{term p} are always 2, 1, 0.  It is buried
   within eight quantifiers!
   We call @{term p} with arguments a, f, z by equating them with 
  the corresponding quantified variables with de Bruijn indices 2, 1, 0.*}

(* is_transrec :: "[i=>o, [i,i,i]=>o, i, i] => o"
   "is_transrec(M,MH,a,z) == 
      \<exists>sa[M]. \<exists>esa[M]. \<exists>mesa[M]. 
       2       1         0
       upair(M,a,a,sa) & is_eclose(M,sa,esa) & membership(M,esa,mesa) &
       is_wfrec(M,MH,mesa,a,z)" *)
constdefs is_transrec_fm :: "[i, i, i]=>i"
 "is_transrec_fm(p,a,z) == 
    Exists(Exists(Exists(
      And(upair_fm(a#+3,a#+3,2),
       And(is_eclose_fm(2,1),
        And(Memrel_fm(1,0), is_wfrec_fm(p,0,a#+3,z#+3)))))))"


lemma is_transrec_type [TC]:
     "[| p \<in> formula; x \<in> nat; z \<in> nat |] 
      ==> is_transrec_fm(p,x,z) \<in> formula"
by (simp add: is_transrec_fm_def) 

lemma sats_is_transrec_fm:
  assumes MH_iff_sats: 
      "!!a0 a1 a2 a3 a4 a5 a6 a7. 
        [|a0\<in>A; a1\<in>A; a2\<in>A; a3\<in>A; a4\<in>A; a5\<in>A; a6\<in>A; a7\<in>A|] 
        ==> MH(a2, a1, a0) <-> 
            sats(A, p, Cons(a0,Cons(a1,Cons(a2,Cons(a3,
                          Cons(a4,Cons(a5,Cons(a6,Cons(a7,env)))))))))"
  shows 
      "[|x < length(env); z < length(env); env \<in> list(A)|]
       ==> sats(A, is_transrec_fm(p,x,z), env) <-> 
           is_transrec(**A, MH, nth(x,env), nth(z,env))"
apply (frule_tac x=z in lt_length_in_nat, assumption)  
apply (frule_tac x=x in lt_length_in_nat, assumption)  
apply (simp add: is_transrec_fm_def sats_is_wfrec_fm is_transrec_def MH_iff_sats [THEN iff_sym]) 
done


lemma is_transrec_iff_sats:
  assumes MH_iff_sats: 
      "!!a0 a1 a2 a3 a4 a5 a6 a7. 
        [|a0\<in>A; a1\<in>A; a2\<in>A; a3\<in>A; a4\<in>A; a5\<in>A; a6\<in>A; a7\<in>A|] 
        ==> MH(a2, a1, a0) <-> 
            sats(A, p, Cons(a0,Cons(a1,Cons(a2,Cons(a3,
                          Cons(a4,Cons(a5,Cons(a6,Cons(a7,env)))))))))"
  shows
  "[|nth(i,env) = x; nth(k,env) = z; 
      i < length(env); k < length(env); env \<in> list(A)|]
   ==> is_transrec(**A, MH, x, z) <-> sats(A, is_transrec_fm(p,i,k), env)" 
by (simp add: sats_is_transrec_fm [OF MH_iff_sats])

theorem is_transrec_reflection:
  assumes MH_reflection:
    "!!f' f g h. REFLECTS[\<lambda>x. MH(L, f'(x), f(x), g(x), h(x)), 
                     \<lambda>i x. MH(**Lset(i), f'(x), f(x), g(x), h(x))]"
  shows "REFLECTS[\<lambda>x. is_transrec(L, MH(L,x), f(x), h(x)), 
               \<lambda>i x. is_transrec(**Lset(i), MH(**Lset(i),x), f(x), h(x))]"
apply (simp (no_asm_use) only: is_transrec_def setclass_simps)
apply (intro FOL_reflections function_reflections MH_reflection 
             is_wfrec_reflection is_eclose_reflection)
done

end
