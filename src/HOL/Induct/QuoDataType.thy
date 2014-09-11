(*  Title:      HOL/Induct/QuoDataType.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2004  University of Cambridge
*)

header{*Defining an Initial Algebra by Quotienting a Free Algebra*}

theory QuoDataType imports Main begin

subsection{*Defining the Free Algebra*}

text{*Messages with encryption and decryption as free constructors.*}
datatype
     freemsg = NONCE  nat
             | MPAIR  freemsg freemsg
             | CRYPT  nat freemsg  
             | DECRYPT  nat freemsg

text{*The equivalence relation, which makes encryption and decryption inverses
provided the keys are the same.

The first two rules are the desired equations. The next four rules
make the equations applicable to subterms. The last two rules are symmetry
and transitivity.*}

inductive_set
  msgrel :: "(freemsg * freemsg) set"
  and msg_rel :: "[freemsg, freemsg] => bool"  (infixl "\<sim>" 50)
  where
    "X \<sim> Y == (X,Y) \<in> msgrel"
  | CD:    "CRYPT K (DECRYPT K X) \<sim> X"
  | DC:    "DECRYPT K (CRYPT K X) \<sim> X"
  | NONCE: "NONCE N \<sim> NONCE N"
  | MPAIR: "\<lbrakk>X \<sim> X'; Y \<sim> Y'\<rbrakk> \<Longrightarrow> MPAIR X Y \<sim> MPAIR X' Y'"
  | CRYPT: "X \<sim> X' \<Longrightarrow> CRYPT K X \<sim> CRYPT K X'"
  | DECRYPT: "X \<sim> X' \<Longrightarrow> DECRYPT K X \<sim> DECRYPT K X'"
  | SYM:   "X \<sim> Y \<Longrightarrow> Y \<sim> X"
  | TRANS: "\<lbrakk>X \<sim> Y; Y \<sim> Z\<rbrakk> \<Longrightarrow> X \<sim> Z"


text{*Proving that it is an equivalence relation*}

lemma msgrel_refl: "X \<sim> X"
  by (induct X) (blast intro: msgrel.intros)+

theorem equiv_msgrel: "equiv UNIV msgrel"
proof -
  have "refl msgrel" by (simp add: refl_on_def msgrel_refl)
  moreover have "sym msgrel" by (simp add: sym_def, blast intro: msgrel.SYM)
  moreover have "trans msgrel" by (simp add: trans_def, blast intro: msgrel.TRANS)
  ultimately show ?thesis by (simp add: equiv_def)
qed


subsection{*Some Functions on the Free Algebra*}

subsubsection{*The Set of Nonces*}

text{*A function to return the set of nonces present in a message.  It will
be lifted to the initial algrebra, to serve as an example of that process.*}
primrec freenonces :: "freemsg \<Rightarrow> nat set" where
  "freenonces (NONCE N) = {N}"
| "freenonces (MPAIR X Y) = freenonces X \<union> freenonces Y"
| "freenonces (CRYPT K X) = freenonces X"
| "freenonces (DECRYPT K X) = freenonces X"

text{*This theorem lets us prove that the nonces function respects the
equivalence relation.  It also helps us prove that Nonce
  (the abstract constructor) is injective*}
theorem msgrel_imp_eq_freenonces: "U \<sim> V \<Longrightarrow> freenonces U = freenonces V"
  by (induct set: msgrel) auto


subsubsection{*The Left Projection*}

text{*A function to return the left part of the top pair in a message.  It will
be lifted to the initial algrebra, to serve as an example of that process.*}
primrec freeleft :: "freemsg \<Rightarrow> freemsg" where
  "freeleft (NONCE N) = NONCE N"
| "freeleft (MPAIR X Y) = X"
| "freeleft (CRYPT K X) = freeleft X"
| "freeleft (DECRYPT K X) = freeleft X"

text{*This theorem lets us prove that the left function respects the
equivalence relation.  It also helps us prove that MPair
  (the abstract constructor) is injective*}
theorem msgrel_imp_eqv_freeleft:
     "U \<sim> V \<Longrightarrow> freeleft U \<sim> freeleft V"
  by (induct set: msgrel) (auto intro: msgrel.intros)


subsubsection{*The Right Projection*}

text{*A function to return the right part of the top pair in a message.*}
primrec freeright :: "freemsg \<Rightarrow> freemsg" where
  "freeright (NONCE N) = NONCE N"
| "freeright (MPAIR X Y) = Y"
| "freeright (CRYPT K X) = freeright X"
| "freeright (DECRYPT K X) = freeright X"

text{*This theorem lets us prove that the right function respects the
equivalence relation.  It also helps us prove that MPair
  (the abstract constructor) is injective*}
theorem msgrel_imp_eqv_freeright:
     "U \<sim> V \<Longrightarrow> freeright U \<sim> freeright V"
  by (induct set: msgrel) (auto intro: msgrel.intros)


subsubsection{*The Discriminator for Constructors*}

text{*A function to distinguish nonces, mpairs and encryptions*}
primrec freediscrim :: "freemsg \<Rightarrow> int" where
  "freediscrim (NONCE N) = 0"
| "freediscrim (MPAIR X Y) = 1"
| "freediscrim (CRYPT K X) = freediscrim X + 2"
| "freediscrim (DECRYPT K X) = freediscrim X - 2"

text{*This theorem helps us prove @{term "Nonce N \<noteq> MPair X Y"}*}
theorem msgrel_imp_eq_freediscrim:
     "U \<sim> V \<Longrightarrow> freediscrim U = freediscrim V"
  by (induct set: msgrel) auto


subsection{*The Initial Algebra: A Quotiented Message Type*}

definition "Msg = UNIV//msgrel"

typedef msg = Msg
  morphisms Rep_Msg Abs_Msg
  unfolding Msg_def by (auto simp add: quotient_def)


text{*The abstract message constructors*}
definition
  Nonce :: "nat \<Rightarrow> msg" where
  "Nonce N = Abs_Msg(msgrel``{NONCE N})"

definition
  MPair :: "[msg,msg] \<Rightarrow> msg" where
   "MPair X Y =
       Abs_Msg (\<Union>U \<in> Rep_Msg X. \<Union>V \<in> Rep_Msg Y. msgrel``{MPAIR U V})"

definition
  Crypt :: "[nat,msg] \<Rightarrow> msg" where
   "Crypt K X =
       Abs_Msg (\<Union>U \<in> Rep_Msg X. msgrel``{CRYPT K U})"

definition
  Decrypt :: "[nat,msg] \<Rightarrow> msg" where
   "Decrypt K X =
       Abs_Msg (\<Union>U \<in> Rep_Msg X. msgrel``{DECRYPT K U})"


text{*Reduces equality of equivalence classes to the @{term msgrel} relation:
  @{term "(msgrel `` {x} = msgrel `` {y}) = ((x,y) \<in> msgrel)"} *}
lemmas equiv_msgrel_iff = eq_equiv_class_iff [OF equiv_msgrel UNIV_I UNIV_I]

declare equiv_msgrel_iff [simp]


text{*All equivalence classes belong to set of representatives*}
lemma [simp]: "msgrel``{U} \<in> Msg"
by (auto simp add: Msg_def quotient_def intro: msgrel_refl)

lemma inj_on_Abs_Msg: "inj_on Abs_Msg Msg"
apply (rule inj_on_inverseI)
apply (erule Abs_Msg_inverse)
done

text{*Reduces equality on abstractions to equality on representatives*}
declare inj_on_Abs_Msg [THEN inj_on_iff, simp]

declare Abs_Msg_inverse [simp]


subsubsection{*Characteristic Equations for the Abstract Constructors*}

lemma MPair: "MPair (Abs_Msg(msgrel``{U})) (Abs_Msg(msgrel``{V})) = 
              Abs_Msg (msgrel``{MPAIR U V})"
proof -
  have "(\<lambda>U V. msgrel `` {MPAIR U V}) respects2 msgrel"
    by (auto simp add: congruent2_def msgrel.MPAIR)
  thus ?thesis
    by (simp add: MPair_def UN_equiv_class2 [OF equiv_msgrel equiv_msgrel])
qed

lemma Crypt: "Crypt K (Abs_Msg(msgrel``{U})) = Abs_Msg (msgrel``{CRYPT K U})"
proof -
  have "(\<lambda>U. msgrel `` {CRYPT K U}) respects msgrel"
    by (auto simp add: congruent_def msgrel.CRYPT)
  thus ?thesis
    by (simp add: Crypt_def UN_equiv_class [OF equiv_msgrel])
qed

lemma Decrypt:
     "Decrypt K (Abs_Msg(msgrel``{U})) = Abs_Msg (msgrel``{DECRYPT K U})"
proof -
  have "(\<lambda>U. msgrel `` {DECRYPT K U}) respects msgrel"
    by (auto simp add: congruent_def msgrel.DECRYPT)
  thus ?thesis
    by (simp add: Decrypt_def UN_equiv_class [OF equiv_msgrel])
qed

text{*Case analysis on the representation of a msg as an equivalence class.*}
lemma eq_Abs_Msg [case_names Abs_Msg, cases type: msg]:
     "(!!U. z = Abs_Msg(msgrel``{U}) ==> P) ==> P"
apply (rule Rep_Msg [of z, unfolded Msg_def, THEN quotientE])
apply (drule arg_cong [where f=Abs_Msg])
apply (auto simp add: Rep_Msg_inverse intro: msgrel_refl)
done

text{*Establishing these two equations is the point of the whole exercise*}
theorem CD_eq [simp]: "Crypt K (Decrypt K X) = X"
by (cases X, simp add: Crypt Decrypt CD)

theorem DC_eq [simp]: "Decrypt K (Crypt K X) = X"
by (cases X, simp add: Crypt Decrypt DC)


subsection{*The Abstract Function to Return the Set of Nonces*}

definition
  nonces :: "msg \<Rightarrow> nat set" where
   "nonces X = (\<Union>U \<in> Rep_Msg X. freenonces U)"

lemma nonces_congruent: "freenonces respects msgrel"
by (auto simp add: congruent_def msgrel_imp_eq_freenonces) 


text{*Now prove the four equations for @{term nonces}*}

lemma nonces_Nonce [simp]: "nonces (Nonce N) = {N}"
by (simp add: nonces_def Nonce_def 
              UN_equiv_class [OF equiv_msgrel nonces_congruent]) 
 
lemma nonces_MPair [simp]: "nonces (MPair X Y) = nonces X \<union> nonces Y"
apply (cases X, cases Y) 
apply (simp add: nonces_def MPair 
                 UN_equiv_class [OF equiv_msgrel nonces_congruent]) 
done

lemma nonces_Crypt [simp]: "nonces (Crypt K X) = nonces X"
apply (cases X) 
apply (simp add: nonces_def Crypt
                 UN_equiv_class [OF equiv_msgrel nonces_congruent]) 
done

lemma nonces_Decrypt [simp]: "nonces (Decrypt K X) = nonces X"
apply (cases X) 
apply (simp add: nonces_def Decrypt
                 UN_equiv_class [OF equiv_msgrel nonces_congruent]) 
done


subsection{*The Abstract Function to Return the Left Part*}

definition
  left :: "msg \<Rightarrow> msg" where
   "left X = Abs_Msg (\<Union>U \<in> Rep_Msg X. msgrel``{freeleft U})"

lemma left_congruent: "(\<lambda>U. msgrel `` {freeleft U}) respects msgrel"
by (auto simp add: congruent_def msgrel_imp_eqv_freeleft) 

text{*Now prove the four equations for @{term left}*}

lemma left_Nonce [simp]: "left (Nonce N) = Nonce N"
by (simp add: left_def Nonce_def 
              UN_equiv_class [OF equiv_msgrel left_congruent]) 

lemma left_MPair [simp]: "left (MPair X Y) = X"
apply (cases X, cases Y) 
apply (simp add: left_def MPair 
                 UN_equiv_class [OF equiv_msgrel left_congruent]) 
done

lemma left_Crypt [simp]: "left (Crypt K X) = left X"
apply (cases X) 
apply (simp add: left_def Crypt
                 UN_equiv_class [OF equiv_msgrel left_congruent]) 
done

lemma left_Decrypt [simp]: "left (Decrypt K X) = left X"
apply (cases X) 
apply (simp add: left_def Decrypt
                 UN_equiv_class [OF equiv_msgrel left_congruent]) 
done


subsection{*The Abstract Function to Return the Right Part*}

definition
  right :: "msg \<Rightarrow> msg" where
   "right X = Abs_Msg (\<Union>U \<in> Rep_Msg X. msgrel``{freeright U})"

lemma right_congruent: "(\<lambda>U. msgrel `` {freeright U}) respects msgrel"
by (auto simp add: congruent_def msgrel_imp_eqv_freeright) 

text{*Now prove the four equations for @{term right}*}

lemma right_Nonce [simp]: "right (Nonce N) = Nonce N"
by (simp add: right_def Nonce_def 
              UN_equiv_class [OF equiv_msgrel right_congruent]) 

lemma right_MPair [simp]: "right (MPair X Y) = Y"
apply (cases X, cases Y) 
apply (simp add: right_def MPair 
                 UN_equiv_class [OF equiv_msgrel right_congruent]) 
done

lemma right_Crypt [simp]: "right (Crypt K X) = right X"
apply (cases X) 
apply (simp add: right_def Crypt
                 UN_equiv_class [OF equiv_msgrel right_congruent]) 
done

lemma right_Decrypt [simp]: "right (Decrypt K X) = right X"
apply (cases X) 
apply (simp add: right_def Decrypt
                 UN_equiv_class [OF equiv_msgrel right_congruent]) 
done


subsection{*Injectivity Properties of Some Constructors*}

lemma NONCE_imp_eq: "NONCE m \<sim> NONCE n \<Longrightarrow> m = n"
by (drule msgrel_imp_eq_freenonces, simp)

text{*Can also be proved using the function @{term nonces}*}
lemma Nonce_Nonce_eq [iff]: "(Nonce m = Nonce n) = (m = n)"
by (auto simp add: Nonce_def msgrel_refl dest: NONCE_imp_eq)

lemma MPAIR_imp_eqv_left: "MPAIR X Y \<sim> MPAIR X' Y' \<Longrightarrow> X \<sim> X'"
by (drule msgrel_imp_eqv_freeleft, simp)

lemma MPair_imp_eq_left: 
  assumes eq: "MPair X Y = MPair X' Y'" shows "X = X'"
proof -
  from eq
  have "left (MPair X Y) = left (MPair X' Y')" by simp
  thus ?thesis by simp
qed

lemma MPAIR_imp_eqv_right: "MPAIR X Y \<sim> MPAIR X' Y' \<Longrightarrow> Y \<sim> Y'"
by (drule msgrel_imp_eqv_freeright, simp)

lemma MPair_imp_eq_right: "MPair X Y = MPair X' Y' \<Longrightarrow> Y = Y'" 
apply (cases X, cases X', cases Y, cases Y') 
apply (simp add: MPair)
apply (erule MPAIR_imp_eqv_right)  
done

theorem MPair_MPair_eq [iff]: "(MPair X Y = MPair X' Y') = (X=X' & Y=Y')" 
by (blast dest: MPair_imp_eq_left MPair_imp_eq_right)

lemma NONCE_neqv_MPAIR: "NONCE m \<sim> MPAIR X Y \<Longrightarrow> False"
by (drule msgrel_imp_eq_freediscrim, simp)

theorem Nonce_neq_MPair [iff]: "Nonce N \<noteq> MPair X Y"
apply (cases X, cases Y) 
apply (simp add: Nonce_def MPair) 
apply (blast dest: NONCE_neqv_MPAIR) 
done

text{*Example suggested by a referee*}
theorem Crypt_Nonce_neq_Nonce: "Crypt K (Nonce M) \<noteq> Nonce N" 
by (auto simp add: Nonce_def Crypt dest: msgrel_imp_eq_freediscrim)  

text{*...and many similar results*}
theorem Crypt2_Nonce_neq_Nonce: "Crypt K (Crypt K' (Nonce M)) \<noteq> Nonce N" 
by (auto simp add: Nonce_def Crypt dest: msgrel_imp_eq_freediscrim)  

theorem Crypt_Crypt_eq [iff]: "(Crypt K X = Crypt K X') = (X=X')" 
proof
  assume "Crypt K X = Crypt K X'"
  hence "Decrypt K (Crypt K X) = Decrypt K (Crypt K X')" by simp
  thus "X = X'" by simp
next
  assume "X = X'"
  thus "Crypt K X = Crypt K X'" by simp
qed

theorem Decrypt_Decrypt_eq [iff]: "(Decrypt K X = Decrypt K X') = (X=X')" 
proof
  assume "Decrypt K X = Decrypt K X'"
  hence "Crypt K (Decrypt K X) = Crypt K (Decrypt K X')" by simp
  thus "X = X'" by simp
next
  assume "X = X'"
  thus "Decrypt K X = Decrypt K X'" by simp
qed

lemma msg_induct [case_names Nonce MPair Crypt Decrypt, cases type: msg]:
  assumes N: "\<And>N. P (Nonce N)"
      and M: "\<And>X Y. \<lbrakk>P X; P Y\<rbrakk> \<Longrightarrow> P (MPair X Y)"
      and C: "\<And>K X. P X \<Longrightarrow> P (Crypt K X)"
      and D: "\<And>K X. P X \<Longrightarrow> P (Decrypt K X)"
  shows "P msg"
proof (cases msg)
  case (Abs_Msg U)
  have "P (Abs_Msg (msgrel `` {U}))"
  proof (induct U)
    case (NONCE N) 
    with N show ?case by (simp add: Nonce_def) 
  next
    case (MPAIR X Y)
    with M [of "Abs_Msg (msgrel `` {X})" "Abs_Msg (msgrel `` {Y})"]
    show ?case by (simp add: MPair) 
  next
    case (CRYPT K X)
    with C [of "Abs_Msg (msgrel `` {X})"]
    show ?case by (simp add: Crypt) 
  next
    case (DECRYPT K X)
    with D [of "Abs_Msg (msgrel `` {X})"]
    show ?case by (simp add: Decrypt)
  qed
  with Abs_Msg show ?thesis by (simp only:)
qed


subsection{*The Abstract Discriminator*}

text{*However, as @{text Crypt_Nonce_neq_Nonce} above illustrates, we don't
need this function in order to prove discrimination theorems.*}

definition
  discrim :: "msg \<Rightarrow> int" where
   "discrim X = the_elem (\<Union>U \<in> Rep_Msg X. {freediscrim U})"

lemma discrim_congruent: "(\<lambda>U. {freediscrim U}) respects msgrel"
by (auto simp add: congruent_def msgrel_imp_eq_freediscrim) 

text{*Now prove the four equations for @{term discrim}*}

lemma discrim_Nonce [simp]: "discrim (Nonce N) = 0"
by (simp add: discrim_def Nonce_def 
              UN_equiv_class [OF equiv_msgrel discrim_congruent]) 

lemma discrim_MPair [simp]: "discrim (MPair X Y) = 1"
apply (cases X, cases Y) 
apply (simp add: discrim_def MPair 
                 UN_equiv_class [OF equiv_msgrel discrim_congruent]) 
done

lemma discrim_Crypt [simp]: "discrim (Crypt K X) = discrim X + 2"
apply (cases X) 
apply (simp add: discrim_def Crypt
                 UN_equiv_class [OF equiv_msgrel discrim_congruent]) 
done

lemma discrim_Decrypt [simp]: "discrim (Decrypt K X) = discrim X - 2"
apply (cases X) 
apply (simp add: discrim_def Decrypt
                 UN_equiv_class [OF equiv_msgrel discrim_congruent]) 
done


end

