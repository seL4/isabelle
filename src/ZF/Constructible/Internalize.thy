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

end
