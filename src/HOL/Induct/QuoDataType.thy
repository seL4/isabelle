(*  Title:      HOL/Induct/QuoDataType
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2004  University of Cambridge

*)

header{*Defining an Initial Algebra by Quotienting a Free Algebra*}

theory QuoDataType = Main:

subsection{*Defining the Free Algebra*}

text{*Messages with encryption and decryption as free constructors.*}
datatype
     freemsg = NONCE  nat
	     | MPAIR  freemsg freemsg
	     | CRYPT  nat freemsg  
	     | DECRYPT  nat freemsg

text{*The equivalence relation, which makes encryption and decryption inverses
provided the keys are the same.*}
consts  msgrel :: "(freemsg * freemsg) set"

syntax
  "_msgrel" :: "[freemsg, freemsg] => bool"  (infixl "~~" 50)
syntax (xsymbols)
  "_msgrel" :: "[freemsg, freemsg] => bool"  (infixl "\<sim>" 50)
translations
  "X \<sim> Y" == "(X,Y) \<in> msgrel"

text{*The first two rules are the desired equations. The next four rules
make the equations applicable to subterms. The last two rules are symmetry
and transitivity.*}
inductive "msgrel"
  intros 
    CD:    "CRYPT K (DECRYPT K X) \<sim> X"
    DC:    "DECRYPT K (CRYPT K X) \<sim> X"
    NONCE: "NONCE N \<sim> NONCE N"
    MPAIR: "\<lbrakk>X \<sim> X'; Y \<sim> Y'\<rbrakk> \<Longrightarrow> MPAIR X Y \<sim> MPAIR X' Y'"
    CRYPT: "X \<sim> X' \<Longrightarrow> CRYPT K X \<sim> CRYPT K X'"
    DECRYPT: "X \<sim> X' \<Longrightarrow> DECRYPT K X \<sim> DECRYPT K X'"
    SYM:   "X \<sim> Y \<Longrightarrow> Y \<sim> X"
    TRANS: "\<lbrakk>X \<sim> Y; Y \<sim> Z\<rbrakk> \<Longrightarrow> X \<sim> Z"


text{*Proving that it is an equivalence relation*}

lemma msgrel_refl: "X \<sim> X"
by (induct X, (blast intro: msgrel.intros)+)

theorem equiv_msgrel: "equiv UNIV msgrel"
proof (simp add: equiv_def, intro conjI)
  show "reflexive msgrel" by (simp add: refl_def msgrel_refl)
  show "sym msgrel" by (simp add: sym_def, blast intro: msgrel.SYM)
  show "trans msgrel" by (simp add: trans_def, blast intro: msgrel.TRANS)
qed


subsection{*Some Functions on the Free Algebra*}

subsubsection{*The Set of Nonces*}

text{*A function to return the set of nonces present in a message.  It will
be lifted to the initial algrebra, to serve as an example of that process.*}
consts
  freenonces :: "freemsg \<Rightarrow> nat set"

primrec
   "freenonces (NONCE N) = {N}"
   "freenonces (MPAIR X Y) = freenonces X \<union> freenonces Y"
   "freenonces (CRYPT K X) = freenonces X"
   "freenonces (DECRYPT K X) = freenonces X"

text{*This theorem lets us prove that the nonces function respects the
equivalence relation.  It also helps us prove that Nonce
  (the abstract constructor) is injective*}
theorem msgrel_imp_eq_freenonces: "U \<sim> V \<Longrightarrow> freenonces U = freenonces V"
by (erule msgrel.induct, auto) 


subsubsection{*The Left Projection*}

text{*A function to return the left part of the top pair in a message.  It will
be lifted to the initial algrebra, to serve as an example of that process.*}
consts free_left :: "freemsg \<Rightarrow> freemsg"
primrec
   "free_left (NONCE N) = NONCE N"
   "free_left (MPAIR X Y) = X"
   "free_left (CRYPT K X) = free_left X"
   "free_left (DECRYPT K X) = free_left X"

text{*This theorem lets us prove that the left function respects the
equivalence relation.  It also helps us prove that MPair
  (the abstract constructor) is injective*}
theorem msgrel_imp_eqv_free_left:
     "U \<sim> V \<Longrightarrow> free_left U \<sim> free_left V"
by (erule msgrel.induct, auto intro: msgrel.intros)


subsubsection{*The Right Projection*}

text{*A function to return the right part of the top pair in a message.*}
consts free_right :: "freemsg \<Rightarrow> freemsg"
primrec
   "free_right (NONCE N) = NONCE N"
   "free_right (MPAIR X Y) = Y"
   "free_right (CRYPT K X) = free_right X"
   "free_right (DECRYPT K X) = free_right X"

text{*This theorem lets us prove that the right function respects the
equivalence relation.  It also helps us prove that MPair
  (the abstract constructor) is injective*}
theorem msgrel_imp_eqv_free_right:
     "U \<sim> V \<Longrightarrow> free_right U \<sim> free_right V"
by (erule msgrel.induct, auto intro: msgrel.intros)


subsubsection{*The Discriminator for Nonces*}

text{*A function to identify nonces*}
consts isNONCE :: "freemsg \<Rightarrow> bool"
primrec
   "isNONCE (NONCE N) = True"
   "isNONCE (MPAIR X Y) = False"
   "isNONCE (CRYPT K X) = isNONCE X"
   "isNONCE (DECRYPT K X) = isNONCE X"

text{*This theorem helps us prove @{term "Nonce N \<noteq> MPair X Y"}*}
theorem msgrel_imp_eq_isNONCE:
     "U \<sim> V \<Longrightarrow> isNONCE U = isNONCE V"
by (erule msgrel.induct, auto)


subsection{*The Initial Algebra: A Quotiented Message Type*}

typedef (Msg)  msg = "UNIV//msgrel"
    by (auto simp add: quotient_def)


text{*The abstract message constructors*}
constdefs
  Nonce :: "nat \<Rightarrow> msg"
  "Nonce N == Abs_Msg(msgrel``{NONCE N})"

  MPair :: "[msg,msg] \<Rightarrow> msg"
   "MPair X Y ==
       Abs_Msg (\<Union>U \<in> Rep_Msg X. \<Union>V \<in> Rep_Msg Y. msgrel``{MPAIR U V})"

  Crypt :: "[nat,msg] \<Rightarrow> msg"
   "Crypt K X ==
       Abs_Msg (\<Union>U \<in> Rep_Msg X. msgrel``{CRYPT K U})"

  Decrypt :: "[nat,msg] \<Rightarrow> msg"
   "Decrypt K X ==
       Abs_Msg (\<Union>U \<in> Rep_Msg X. msgrel``{DECRYPT K U})"


text{*Reduces equality of equivalence classes to the @{term msgrel} relation:
  @{term "(msgrel `` {x} = msgrel `` {y}) = ((x,y) \<in> msgrel)"} *}
lemmas equiv_msgrel_iff = eq_equiv_class_iff [OF equiv_msgrel UNIV_I UNIV_I]

declare equiv_msgrel_iff [simp]


text{*All equivalence classes belong to set of representatives*}
lemma msgrel_in_integ [simp]: "msgrel``{U} \<in> Msg"
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
  have "congruent2 msgrel (\<lambda>U V. msgrel `` {MPAIR U V})"
    by (simp add: congruent2_def msgrel.MPAIR)
  thus ?thesis
    by (simp add: MPair_def UN_equiv_class2 [OF equiv_msgrel])
qed

lemma Crypt: "Crypt K (Abs_Msg(msgrel``{U})) = Abs_Msg (msgrel``{CRYPT K U})"
proof -
  have "congruent msgrel (\<lambda>U. msgrel `` {CRYPT K U})"
    by (simp add: congruent_def msgrel.CRYPT)
  thus ?thesis
    by (simp add: Crypt_def UN_equiv_class [OF equiv_msgrel])
qed

lemma Decrypt:
     "Decrypt K (Abs_Msg(msgrel``{U})) = Abs_Msg (msgrel``{DECRYPT K U})"
proof -
  have "congruent msgrel (\<lambda>U. msgrel `` {DECRYPT K U})"
    by (simp add: congruent_def msgrel.DECRYPT)
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

constdefs
  nonces :: "msg \<Rightarrow> nat set"
   "nonces X == \<Union>U \<in> Rep_Msg X. freenonces U"

lemma nonces_congruent: "congruent msgrel freenonces"
by (simp add: congruent_def msgrel_imp_eq_freenonces) 


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

constdefs
  left :: "msg \<Rightarrow> msg"
   "left X == Abs_Msg (\<Union>U \<in> Rep_Msg X. msgrel``{free_left U})"

lemma left_congruent: "congruent msgrel (\<lambda>U. msgrel `` {free_left U})"
by (simp add: congruent_def msgrel_imp_eqv_free_left) 

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

constdefs
  right :: "msg \<Rightarrow> msg"
   "right X == Abs_Msg (\<Union>U \<in> Rep_Msg X. msgrel``{free_right U})"

lemma right_congruent: "congruent msgrel (\<lambda>U. msgrel `` {free_right U})"
by (simp add: congruent_def msgrel_imp_eqv_free_right) 

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
by (drule msgrel_imp_eqv_free_left, simp)

lemma MPair_imp_eq_left: 
  assumes eq: "MPair X Y = MPair X' Y'" shows "X = X'"
proof -
  from eq
  have "left (MPair X Y) = left (MPair X' Y')" by simp
  thus ?thesis by simp
qed

lemma MPAIR_imp_eqv_right: "MPAIR X Y \<sim> MPAIR X' Y' \<Longrightarrow> Y \<sim> Y'"
by (drule msgrel_imp_eqv_free_right, simp)

lemma MPair_imp_eq_right: "MPair X Y = MPair X' Y' \<Longrightarrow> Y = Y'" 
apply (cases X, cases X', cases Y, cases Y') 
apply (simp add: MPair)
apply (erule MPAIR_imp_eqv_right)  
done

theorem MPair_MPair_eq [iff]: "(MPair X Y = MPair X' Y') = (X=X' & Y=Y')" 
by (blast dest: MPair_imp_eq_left MPair_imp_eq_right)

lemma NONCE_neqv_MPAIR: "NONCE m \<sim> MPAIR X Y \<Longrightarrow> False"
by (drule msgrel_imp_eq_isNONCE, simp)

theorem Nonce_neq_MPair [iff]: "Nonce N \<noteq> MPair X Y"
apply (cases X, cases Y) 
apply (simp add: Nonce_def MPair) 
apply (blast dest: NONCE_neqv_MPAIR) 
done

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
proof (cases msg, erule ssubst)  
  fix U::freemsg
  show "P (Abs_Msg (msgrel `` {U}))"
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
qed

end

