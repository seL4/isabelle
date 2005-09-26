(* AUTOMATICALLY GENERATED, DO NOT EDIT! *)

theory HOL4Vec imports HOL4Base begin

;setup_theory res_quan

lemma RES_FORALL_CONJ_DIST: "ALL (P::'a::type => bool) (Q::'a::type => bool) R::'a::type => bool.
   RES_FORALL P (%i::'a::type. Q i & R i) =
   (RES_FORALL P Q & RES_FORALL P R)"
  by (import res_quan RES_FORALL_CONJ_DIST)

lemma RES_FORALL_DISJ_DIST: "ALL (P::'a::type => bool) (Q::'a::type => bool) R::'a::type => bool.
   RES_FORALL (%j::'a::type. P j | Q j) R =
   (RES_FORALL P R & RES_FORALL Q R)"
  by (import res_quan RES_FORALL_DISJ_DIST)

lemma RES_FORALL_UNIQUE: "ALL (x::'a::type => bool) xa::'a::type. RES_FORALL (op = xa) x = x xa"
  by (import res_quan RES_FORALL_UNIQUE)

lemma RES_FORALL_FORALL: "ALL (P::'a::type => bool) (R::'a::type => 'b::type => bool) x::'b::type.
   (ALL x::'b::type. RES_FORALL P (%i::'a::type. R i x)) =
   RES_FORALL P (%i::'a::type. All (R i))"
  by (import res_quan RES_FORALL_FORALL)

lemma RES_FORALL_REORDER: "ALL (P::'a::type => bool) (Q::'b::type => bool)
   R::'a::type => 'b::type => bool.
   RES_FORALL P (%i::'a::type. RES_FORALL Q (R i)) =
   RES_FORALL Q (%j::'b::type. RES_FORALL P (%i::'a::type. R i j))"
  by (import res_quan RES_FORALL_REORDER)

lemma RES_FORALL_EMPTY: "All (RES_FORALL EMPTY)"
  by (import res_quan RES_FORALL_EMPTY)

lemma RES_FORALL_UNIV: "ALL p::'a::type => bool. RES_FORALL pred_set.UNIV p = All p"
  by (import res_quan RES_FORALL_UNIV)

lemma RES_FORALL_NULL: "ALL (p::'a::type => bool) m::bool.
   RES_FORALL p (%x::'a::type. m) = (p = EMPTY | m)"
  by (import res_quan RES_FORALL_NULL)

lemma RES_EXISTS_DISJ_DIST: "ALL (P::'a::type => bool) (Q::'a::type => bool) R::'a::type => bool.
   RES_EXISTS P (%i::'a::type. Q i | R i) =
   (RES_EXISTS P Q | RES_EXISTS P R)"
  by (import res_quan RES_EXISTS_DISJ_DIST)

lemma RES_DISJ_EXISTS_DIST: "ALL (P::'a::type => bool) (Q::'a::type => bool) R::'a::type => bool.
   RES_EXISTS (%i::'a::type. P i | Q i) R =
   (RES_EXISTS P R | RES_EXISTS Q R)"
  by (import res_quan RES_DISJ_EXISTS_DIST)

lemma RES_EXISTS_EQUAL: "ALL (x::'a::type => bool) xa::'a::type. RES_EXISTS (op = xa) x = x xa"
  by (import res_quan RES_EXISTS_EQUAL)

lemma RES_EXISTS_REORDER: "ALL (P::'a::type => bool) (Q::'b::type => bool)
   R::'a::type => 'b::type => bool.
   RES_EXISTS P (%i::'a::type. RES_EXISTS Q (R i)) =
   RES_EXISTS Q (%j::'b::type. RES_EXISTS P (%i::'a::type. R i j))"
  by (import res_quan RES_EXISTS_REORDER)

lemma RES_EXISTS_EMPTY: "ALL p::'a::type => bool. ~ RES_EXISTS EMPTY p"
  by (import res_quan RES_EXISTS_EMPTY)

lemma RES_EXISTS_UNIV: "ALL p::'a::type => bool. RES_EXISTS pred_set.UNIV p = Ex p"
  by (import res_quan RES_EXISTS_UNIV)

lemma RES_EXISTS_NULL: "ALL (p::'a::type => bool) m::bool.
   RES_EXISTS p (%x::'a::type. m) = (p ~= EMPTY & m)"
  by (import res_quan RES_EXISTS_NULL)

lemma RES_EXISTS_ALT: "ALL (p::'a::type => bool) m::'a::type => bool.
   RES_EXISTS p m = (IN (RES_SELECT p m) p & m (RES_SELECT p m))"
  by (import res_quan RES_EXISTS_ALT)

lemma RES_EXISTS_UNIQUE_EMPTY: "ALL p::'a::type => bool. ~ RES_EXISTS_UNIQUE EMPTY p"
  by (import res_quan RES_EXISTS_UNIQUE_EMPTY)

lemma RES_EXISTS_UNIQUE_UNIV: "ALL p::'a::type => bool. RES_EXISTS_UNIQUE pred_set.UNIV p = Ex1 p"
  by (import res_quan RES_EXISTS_UNIQUE_UNIV)

lemma RES_EXISTS_UNIQUE_NULL: "ALL (p::'a::type => bool) m::bool.
   RES_EXISTS_UNIQUE p (%x::'a::type. m) =
   ((EX x::'a::type. p = INSERT x EMPTY) & m)"
  by (import res_quan RES_EXISTS_UNIQUE_NULL)

lemma RES_EXISTS_UNIQUE_ALT: "ALL (p::'a::type => bool) m::'a::type => bool.
   RES_EXISTS_UNIQUE p m =
   RES_EXISTS p
    (%x::'a::type. m x & RES_FORALL p (%y::'a::type. m y --> y = x))"
  by (import res_quan RES_EXISTS_UNIQUE_ALT)

lemma RES_SELECT_EMPTY: "ALL p::'a::type => bool. RES_SELECT EMPTY p = (SOME x::'a::type. False)"
  by (import res_quan RES_SELECT_EMPTY)

lemma RES_SELECT_UNIV: "ALL p::'a::type => bool. RES_SELECT pred_set.UNIV p = Eps p"
  by (import res_quan RES_SELECT_UNIV)

lemma RES_ABSTRACT: "ALL (p::'a::type => bool) (m::'a::type => 'b::type) x::'a::type.
   IN x p --> RES_ABSTRACT p m x = m x"
  by (import res_quan RES_ABSTRACT)

lemma RES_ABSTRACT_EQUAL: "ALL (p::'a::type => bool) (m1::'a::type => 'b::type)
   m2::'a::type => 'b::type.
   (ALL x::'a::type. IN x p --> m1 x = m2 x) -->
   RES_ABSTRACT p m1 = RES_ABSTRACT p m2"
  by (import res_quan RES_ABSTRACT_EQUAL)

lemma RES_ABSTRACT_IDEMPOT: "ALL (p::'a::type => bool) m::'a::type => 'b::type.
   RES_ABSTRACT p (RES_ABSTRACT p m) = RES_ABSTRACT p m"
  by (import res_quan RES_ABSTRACT_IDEMPOT)

lemma RES_ABSTRACT_EQUAL_EQ: "ALL (p::'a::type => bool) (m1::'a::type => 'b::type)
   m2::'a::type => 'b::type.
   (RES_ABSTRACT p m1 = RES_ABSTRACT p m2) =
   (ALL x::'a::type. IN x p --> m1 x = m2 x)"
  by (import res_quan RES_ABSTRACT_EQUAL_EQ)

;end_setup

;setup_theory word_base

typedef (open) ('a) word = "(Collect::('a::type list recspace => bool) => 'a::type list recspace set)
 (%x::'a::type list recspace.
     (All::(('a::type list recspace => bool) => bool) => bool)
      (%word::'a::type list recspace => bool.
          (op -->::bool => bool => bool)
           ((All::('a::type list recspace => bool) => bool)
             (%a0::'a::type list recspace.
                 (op -->::bool => bool => bool)
                  ((Ex::('a::type list => bool) => bool)
                    (%a::'a::type list.
                        (op =::'a::type list recspace
                               => 'a::type list recspace => bool)
                         a0 ((CONSTR::nat
=> 'a::type list
   => (nat => 'a::type list recspace) => 'a::type list recspace)
                              (0::nat) a
                              (%n::nat. BOTTOM::'a::type list recspace))))
                  (word a0)))
           (word x)))" 
  by (rule typedef_helper,import word_base word_TY_DEF)

lemmas word_TY_DEF = typedef_hol2hol4 [OF type_definition_word]

consts
  mk_word :: "'a::type list recspace => 'a::type word" 
  dest_word :: "'a::type word => 'a::type list recspace" 

specification (dest_word mk_word) word_repfns: "(ALL a::'a::type word. mk_word (dest_word a) = a) &
(ALL r::'a::type list recspace.
    (ALL word::'a::type list recspace => bool.
        (ALL a0::'a::type list recspace.
            (EX a::'a::type list.
                a0 = CONSTR (0::nat) a (%n::nat. BOTTOM)) -->
            word a0) -->
        word r) =
    (dest_word (mk_word r) = r))"
  by (import word_base word_repfns)

consts
  word_base0 :: "'a::type list => 'a::type word" 

defs
  word_base0_primdef: "word_base0 ==
%a::'a::type list. mk_word (CONSTR (0::nat) a (%n::nat. BOTTOM))"

lemma word_base0_def: "word_base0 =
(%a::'a::type list. mk_word (CONSTR (0::nat) a (%n::nat. BOTTOM)))"
  by (import word_base word_base0_def)

constdefs
  WORD :: "'a::type list => 'a::type word" 
  "WORD == word_base0"

lemma WORD: "WORD = word_base0"
  by (import word_base WORD)

consts
  word_case :: "('a::type list => 'b::type) => 'a::type word => 'b::type" 

specification (word_case_primdef: word_case) word_case_def: "ALL (f::'a::type list => 'b::type) a::'a::type list.
   word_case f (WORD a) = f a"
  by (import word_base word_case_def)

consts
  word_size :: "('a::type => nat) => 'a::type word => nat" 

specification (word_size_primdef: word_size) word_size_def: "ALL (f::'a::type => nat) a::'a::type list.
   word_size f (WORD a) = (1::nat) + list_size f a"
  by (import word_base word_size_def)

lemma word_11: "ALL (a::'a::type list) a'::'a::type list. (WORD a = WORD a') = (a = a')"
  by (import word_base word_11)

lemma word_case_cong: "ALL (M::'a::type word) (M'::'a::type word) f::'a::type list => 'b::type.
   M = M' &
   (ALL a::'a::type list.
       M' = WORD a --> f a = (f'::'a::type list => 'b::type) a) -->
   word_case f M = word_case f' M'"
  by (import word_base word_case_cong)

lemma word_nchotomy: "ALL x::'a::type word. EX l::'a::type list. x = WORD l"
  by (import word_base word_nchotomy)

lemma word_Axiom: "ALL f::'a::type list => 'b::type.
   EX fn::'a::type word => 'b::type. ALL a::'a::type list. fn (WORD a) = f a"
  by (import word_base word_Axiom)

lemma word_induction: "ALL P::'a::type word => bool. (ALL a::'a::type list. P (WORD a)) --> All P"
  by (import word_base word_induction)

lemma word_Ax: "ALL f::'a::type list => 'b::type.
   EX fn::'a::type word => 'b::type. ALL a::'a::type list. fn (WORD a) = f a"
  by (import word_base word_Ax)

lemma WORD_11: "ALL (x::'a::type list) xa::'a::type list. (WORD x = WORD xa) = (x = xa)"
  by (import word_base WORD_11)

lemma word_induct: "ALL x::'a::type word => bool. (ALL l::'a::type list. x (WORD l)) --> All x"
  by (import word_base word_induct)

lemma word_cases: "ALL x::'a::type word. EX l::'a::type list. x = WORD l"
  by (import word_base word_cases)

consts
  WORDLEN :: "'a::type word => nat" 

specification (WORDLEN) WORDLEN_DEF: "ALL l::'a::type list. WORDLEN (WORD l) = length l"
  by (import word_base WORDLEN_DEF)

consts
  PWORDLEN :: "nat => 'a::type word => bool" 

defs
  PWORDLEN_primdef: "PWORDLEN == %n::nat. GSPEC (%w::'a::type word. (w, WORDLEN w = n))"

lemma PWORDLEN_def: "ALL n::nat. PWORDLEN n = GSPEC (%w::'a::type word. (w, WORDLEN w = n))"
  by (import word_base PWORDLEN_def)

lemma IN_PWORDLEN: "ALL (n::nat) l::'a::type list. IN (WORD l) (PWORDLEN n) = (length l = n)"
  by (import word_base IN_PWORDLEN)

lemma PWORDLEN: "ALL (n::nat) w::'a::type word. IN w (PWORDLEN n) = (WORDLEN w = n)"
  by (import word_base PWORDLEN)

lemma PWORDLEN0: "ALL w::'a::type word. IN w (PWORDLEN (0::nat)) --> w = WORD []"
  by (import word_base PWORDLEN0)

lemma PWORDLEN1: "ALL x::'a::type. IN (WORD [x]) (PWORDLEN (1::nat))"
  by (import word_base PWORDLEN1)

consts
  WSEG :: "nat => nat => 'a::type word => 'a::type word" 

specification (WSEG) WSEG_DEF: "ALL (m::nat) (k::nat) l::'a::type list.
   WSEG m k (WORD l) = WORD (LASTN m (BUTLASTN k l))"
  by (import word_base WSEG_DEF)

lemma WSEG0: "ALL (k::nat) w::'a::type word. WSEG (0::nat) k w = WORD []"
  by (import word_base WSEG0)

lemma WSEG_PWORDLEN: "ALL n::nat.
   RES_FORALL (PWORDLEN n)
    (%w::'a::type word.
        ALL (m::nat) k::nat. m + k <= n --> IN (WSEG m k w) (PWORDLEN m))"
  by (import word_base WSEG_PWORDLEN)

lemma WSEG_WORDLEN: "ALL x::nat.
   RES_FORALL (PWORDLEN x)
    (%xa::'a::type word.
        ALL (xb::nat) xc::nat.
           xb + xc <= x --> WORDLEN (WSEG xb xc xa) = xb)"
  by (import word_base WSEG_WORDLEN)

lemma WSEG_WORD_LENGTH: "ALL n::nat.
   RES_FORALL (PWORDLEN n) (%w::'a::type word. WSEG n (0::nat) w = w)"
  by (import word_base WSEG_WORD_LENGTH)

consts
  bit :: "nat => 'a::type word => 'a::type" 

specification (bit) BIT_DEF: "ALL (k::nat) l::'a::type list. bit k (WORD l) = ELL k l"
  by (import word_base BIT_DEF)

lemma BIT0: "ALL x::'a::type. bit (0::nat) (WORD [x]) = x"
  by (import word_base BIT0)

lemma WSEG_BIT: "(All::(nat => bool) => bool)
 (%n::nat.
     (RES_FORALL::('a::type word => bool)
                  => ('a::type word => bool) => bool)
      ((PWORDLEN::nat => 'a::type word => bool) n)
      (%w::'a::type word.
          (All::(nat => bool) => bool)
           (%k::nat.
               (op -->::bool => bool => bool)
                ((op <::nat => nat => bool) k n)
                ((op =::'a::type word => 'a::type word => bool)
                  ((WSEG::nat => nat => 'a::type word => 'a::type word)
                    (1::nat) k w)
                  ((WORD::'a::type list => 'a::type word)
                    ((op #::'a::type => 'a::type list => 'a::type list)
                      ((bit::nat => 'a::type word => 'a::type) k w)
                      ([]::'a::type list)))))))"
  by (import word_base WSEG_BIT)

lemma BIT_WSEG: "ALL n::nat.
   RES_FORALL (PWORDLEN n)
    (%w::'a::type word.
        ALL (m::nat) (k::nat) j::nat.
           m + k <= n --> j < m --> bit j (WSEG m k w) = bit (j + k) w)"
  by (import word_base BIT_WSEG)

consts
  MSB :: "'a::type word => 'a::type" 

specification (MSB) MSB_DEF: "ALL l::'a::type list. MSB (WORD l) = hd l"
  by (import word_base MSB_DEF)

lemma MSB: "ALL n::nat.
   RES_FORALL (PWORDLEN n)
    (%w::'a::type word. (0::nat) < n --> MSB w = bit (PRE n) w)"
  by (import word_base MSB)

consts
  LSB :: "'a::type word => 'a::type" 

specification (LSB) LSB_DEF: "ALL l::'a::type list. LSB (WORD l) = last l"
  by (import word_base LSB_DEF)

lemma LSB: "ALL n::nat.
   RES_FORALL (PWORDLEN n)
    (%w::'a::type word. (0::nat) < n --> LSB w = bit (0::nat) w)"
  by (import word_base LSB)

consts
  WSPLIT :: "nat => 'a::type word => 'a::type word * 'a::type word" 

specification (WSPLIT) WSPLIT_DEF: "ALL (m::nat) l::'a::type list.
   WSPLIT m (WORD l) = (WORD (BUTLASTN m l), WORD (LASTN m l))"
  by (import word_base WSPLIT_DEF)

consts
  WCAT :: "'a::type word * 'a::type word => 'a::type word" 

specification (WCAT) WCAT_DEF: "ALL (l1::'a::type list) l2::'a::type list.
   WCAT (WORD l1, WORD l2) = WORD (l1 @ l2)"
  by (import word_base WCAT_DEF)

lemma WORD_PARTITION: "(op &::bool => bool => bool)
 ((All::(nat => bool) => bool)
   (%n::nat.
       (RES_FORALL::('a::type word => bool)
                    => ('a::type word => bool) => bool)
        ((PWORDLEN::nat => 'a::type word => bool) n)
        (%w::'a::type word.
            (All::(nat => bool) => bool)
             (%m::nat.
                 (op -->::bool => bool => bool)
                  ((op <=::nat => nat => bool) m n)
                  ((op =::'a::type word => 'a::type word => bool)
                    ((WCAT::'a::type word * 'a::type word => 'a::type word)
                      ((WSPLIT::nat
                                => 'a::type word
                                   => 'a::type word * 'a::type word)
                        m w))
                    w)))))
 ((All::(nat => bool) => bool)
   (%n::nat.
       (All::(nat => bool) => bool)
        (%m::nat.
            (RES_FORALL::('a::type word => bool)
                         => ('a::type word => bool) => bool)
             ((PWORDLEN::nat => 'a::type word => bool) n)
             (%w1::'a::type word.
                 (RES_FORALL::('a::type word => bool)
                              => ('a::type word => bool) => bool)
                  ((PWORDLEN::nat => 'a::type word => bool) m)
                  (%w2::'a::type word.
                      (op =::'a::type word * 'a::type word
                             => 'a::type word * 'a::type word => bool)
                       ((WSPLIT::nat
                                 => 'a::type word
                                    => 'a::type word * 'a::type word)
                         m ((WCAT::'a::type word * 'a::type word
                                   => 'a::type word)
                             ((Pair::'a::type word
                                     => 'a::type word
  => 'a::type word * 'a::type word)
                               w1 w2)))
                       ((Pair::'a::type word
                               => 'a::type word
                                  => 'a::type word * 'a::type word)
                         w1 w2))))))"
  by (import word_base WORD_PARTITION)

lemma WCAT_ASSOC: "ALL (w1::'a::type word) (w2::'a::type word) w3::'a::type word.
   WCAT (w1, WCAT (w2, w3)) = WCAT (WCAT (w1, w2), w3)"
  by (import word_base WCAT_ASSOC)

lemma WCAT0: "ALL w::'a::type word. WCAT (WORD [], w) = w & WCAT (w, WORD []) = w"
  by (import word_base WCAT0)

lemma WCAT_11: "ALL (m::nat) n::nat.
   RES_FORALL (PWORDLEN m)
    (%wm1::'a::type word.
        RES_FORALL (PWORDLEN m)
         (%wm2::'a::type word.
             RES_FORALL (PWORDLEN n)
              (%wn1::'a::type word.
                  RES_FORALL (PWORDLEN n)
                   (%wn2::'a::type word.
                       (WCAT (wm1, wn1) = WCAT (wm2, wn2)) =
                       (wm1 = wm2 & wn1 = wn2)))))"
  by (import word_base WCAT_11)

lemma WSPLIT_PWORDLEN: "(All::(nat => bool) => bool)
 (%n::nat.
     (RES_FORALL::('a::type word => bool)
                  => ('a::type word => bool) => bool)
      ((PWORDLEN::nat => 'a::type word => bool) n)
      (%w::'a::type word.
          (All::(nat => bool) => bool)
           (%m::nat.
               (op -->::bool => bool => bool)
                ((op <=::nat => nat => bool) m n)
                ((op &::bool => bool => bool)
                  ((IN::'a::type word => ('a::type word => bool) => bool)
                    ((fst::'a::type word * 'a::type word => 'a::type word)
                      ((WSPLIT::nat
                                => 'a::type word
                                   => 'a::type word * 'a::type word)
                        m w))
                    ((PWORDLEN::nat => 'a::type word => bool)
                      ((op -::nat => nat => nat) n m)))
                  ((IN::'a::type word => ('a::type word => bool) => bool)
                    ((snd::'a::type word * 'a::type word => 'a::type word)
                      ((WSPLIT::nat
                                => 'a::type word
                                   => 'a::type word * 'a::type word)
                        m w))
                    ((PWORDLEN::nat => 'a::type word => bool) m))))))"
  by (import word_base WSPLIT_PWORDLEN)

lemma WCAT_PWORDLEN: "ALL n1::nat.
   RES_FORALL (PWORDLEN n1)
    (%w1::'a::type word.
        ALL n2::nat.
           RES_FORALL (PWORDLEN n2)
            (%w2::'a::type word. IN (WCAT (w1, w2)) (PWORDLEN (n1 + n2))))"
  by (import word_base WCAT_PWORDLEN)

lemma WORDLEN_SUC_WCAT: "ALL (n::nat) w::'a::type word.
   IN w (PWORDLEN (Suc n)) -->
   RES_EXISTS (PWORDLEN (1::nat))
    (%b::'a::type word.
        RES_EXISTS (PWORDLEN n) (%w'::'a::type word. w = WCAT (b, w')))"
  by (import word_base WORDLEN_SUC_WCAT)

lemma WSEG_WSEG: "ALL n::nat.
   RES_FORALL (PWORDLEN n)
    (%w::'a::type word.
        ALL (m1::nat) (k1::nat) (m2::nat) k2::nat.
           m1 + k1 <= n & m2 + k2 <= m1 -->
           WSEG m2 k2 (WSEG m1 k1 w) = WSEG m2 (k1 + k2) w)"
  by (import word_base WSEG_WSEG)

lemma WSPLIT_WSEG: "(All::(nat => bool) => bool)
 (%n::nat.
     (RES_FORALL::('a::type word => bool)
                  => ('a::type word => bool) => bool)
      ((PWORDLEN::nat => 'a::type word => bool) n)
      (%w::'a::type word.
          (All::(nat => bool) => bool)
           (%k::nat.
               (op -->::bool => bool => bool)
                ((op <=::nat => nat => bool) k n)
                ((op =::'a::type word * 'a::type word
                        => 'a::type word * 'a::type word => bool)
                  ((WSPLIT::nat
                            => 'a::type word
                               => 'a::type word * 'a::type word)
                    k w)
                  ((Pair::'a::type word
                          => 'a::type word => 'a::type word * 'a::type word)
                    ((WSEG::nat => nat => 'a::type word => 'a::type word)
                      ((op -::nat => nat => nat) n k) k w)
                    ((WSEG::nat => nat => 'a::type word => 'a::type word) k
                      (0::nat) w))))))"
  by (import word_base WSPLIT_WSEG)

lemma WSPLIT_WSEG1: "(All::(nat => bool) => bool)
 (%n::nat.
     (RES_FORALL::('a::type word => bool)
                  => ('a::type word => bool) => bool)
      ((PWORDLEN::nat => 'a::type word => bool) n)
      (%w::'a::type word.
          (All::(nat => bool) => bool)
           (%k::nat.
               (op -->::bool => bool => bool)
                ((op <=::nat => nat => bool) k n)
                ((op =::'a::type word => 'a::type word => bool)
                  ((fst::'a::type word * 'a::type word => 'a::type word)
                    ((WSPLIT::nat
                              => 'a::type word
                                 => 'a::type word * 'a::type word)
                      k w))
                  ((WSEG::nat => nat => 'a::type word => 'a::type word)
                    ((op -::nat => nat => nat) n k) k w)))))"
  by (import word_base WSPLIT_WSEG1)

lemma WSPLIT_WSEG2: "(All::(nat => bool) => bool)
 (%n::nat.
     (RES_FORALL::('a::type word => bool)
                  => ('a::type word => bool) => bool)
      ((PWORDLEN::nat => 'a::type word => bool) n)
      (%w::'a::type word.
          (All::(nat => bool) => bool)
           (%k::nat.
               (op -->::bool => bool => bool)
                ((op <=::nat => nat => bool) k n)
                ((op =::'a::type word => 'a::type word => bool)
                  ((snd::'a::type word * 'a::type word => 'a::type word)
                    ((WSPLIT::nat
                              => 'a::type word
                                 => 'a::type word * 'a::type word)
                      k w))
                  ((WSEG::nat => nat => 'a::type word => 'a::type word) k
                    (0::nat) w)))))"
  by (import word_base WSPLIT_WSEG2)

lemma WCAT_WSEG_WSEG: "ALL n::nat.
   RES_FORALL (PWORDLEN n)
    (%w::'a::type word.
        ALL (m1::nat) (m2::nat) k::nat.
           m1 + (m2 + k) <= n -->
           WCAT (WSEG m2 (m1 + k) w, WSEG m1 k w) = WSEG (m1 + m2) k w)"
  by (import word_base WCAT_WSEG_WSEG)

lemma WORD_SPLIT: "ALL (x::nat) xa::nat.
   RES_FORALL (PWORDLEN (x + xa))
    (%w::'a::type word. w = WCAT (WSEG x xa w, WSEG xa (0::nat) w))"
  by (import word_base WORD_SPLIT)

lemma WORDLEN_SUC_WCAT_WSEG_WSEG: "RES_FORALL (PWORDLEN (Suc (n::nat)))
 (%w::'a::type word. w = WCAT (WSEG (1::nat) n w, WSEG n (0::nat) w))"
  by (import word_base WORDLEN_SUC_WCAT_WSEG_WSEG)

lemma WORDLEN_SUC_WCAT_WSEG_WSEG_RIGHT: "RES_FORALL (PWORDLEN (Suc (n::nat)))
 (%w::'a::type word. w = WCAT (WSEG n (1::nat) w, WSEG (1::nat) (0::nat) w))"
  by (import word_base WORDLEN_SUC_WCAT_WSEG_WSEG_RIGHT)

lemma WORDLEN_SUC_WCAT_BIT_WSEG: "ALL n::nat.
   RES_FORALL (PWORDLEN (Suc n))
    (%w::'a::type word. w = WCAT (WORD [bit n w], WSEG n (0::nat) w))"
  by (import word_base WORDLEN_SUC_WCAT_BIT_WSEG)

lemma WORDLEN_SUC_WCAT_BIT_WSEG_RIGHT: "ALL n::nat.
   RES_FORALL (PWORDLEN (Suc n))
    (%w::'a::type word. w = WCAT (WSEG n (1::nat) w, WORD [bit (0::nat) w]))"
  by (import word_base WORDLEN_SUC_WCAT_BIT_WSEG_RIGHT)

lemma WSEG_WCAT1: "ALL (n1::nat) n2::nat.
   RES_FORALL (PWORDLEN n1)
    (%w1::'a::type word.
        RES_FORALL (PWORDLEN n2)
         (%w2::'a::type word. WSEG n1 n2 (WCAT (w1, w2)) = w1))"
  by (import word_base WSEG_WCAT1)

lemma WSEG_WCAT2: "ALL (n1::nat) n2::nat.
   RES_FORALL (PWORDLEN n1)
    (%w1::'a::type word.
        RES_FORALL (PWORDLEN n2)
         (%w2::'a::type word. WSEG n2 (0::nat) (WCAT (w1, w2)) = w2))"
  by (import word_base WSEG_WCAT2)

lemma WSEG_SUC: "ALL n::nat.
   RES_FORALL (PWORDLEN n)
    (%w::'a::type word.
        ALL (k::nat) m1::nat.
           k + Suc m1 < n -->
           WSEG (Suc m1) k w = WCAT (WSEG (1::nat) (k + m1) w, WSEG m1 k w))"
  by (import word_base WSEG_SUC)

lemma WORD_CONS_WCAT: "ALL (x::'a::type) l::'a::type list. WORD (x # l) = WCAT (WORD [x], WORD l)"
  by (import word_base WORD_CONS_WCAT)

lemma WORD_SNOC_WCAT: "ALL (l::'a::type list) x::'a::type.
   WORD (SNOC x l) = WCAT (WORD l, WORD [x])"
  by (import word_base WORD_SNOC_WCAT)

lemma BIT_WCAT_FST: "ALL (n1::nat) n2::nat.
   RES_FORALL (PWORDLEN n1)
    (%w1::'a::type word.
        RES_FORALL (PWORDLEN n2)
         (%w2::'a::type word.
             ALL k::nat.
                n2 <= k & k < n1 + n2 -->
                bit k (WCAT (w1, w2)) = bit (k - n2) w1))"
  by (import word_base BIT_WCAT_FST)

lemma BIT_WCAT_SND: "(All::(nat => bool) => bool)
 (%n1::nat.
     (All::(nat => bool) => bool)
      (%n2::nat.
          (RES_FORALL::('a::type word => bool)
                       => ('a::type word => bool) => bool)
           ((PWORDLEN::nat => 'a::type word => bool) n1)
           (%w1::'a::type word.
               (RES_FORALL::('a::type word => bool)
                            => ('a::type word => bool) => bool)
                ((PWORDLEN::nat => 'a::type word => bool) n2)
                (%w2::'a::type word.
                    (All::(nat => bool) => bool)
                     (%k::nat.
                         (op -->::bool => bool => bool)
                          ((op <::nat => nat => bool) k n2)
                          ((op =::'a::type => 'a::type => bool)
                            ((bit::nat => 'a::type word => 'a::type) k
                              ((WCAT::'a::type word * 'a::type word
=> 'a::type word)
                                ((Pair::'a::type word
  => 'a::type word => 'a::type word * 'a::type word)
                                  w1 w2)))
                            ((bit::nat => 'a::type word => 'a::type) k
                              w2)))))))"
  by (import word_base BIT_WCAT_SND)

lemma BIT_WCAT1: "ALL n::nat.
   RES_FORALL (PWORDLEN n)
    (%w::'a::type word. ALL b::'a::type. bit n (WCAT (WORD [b], w)) = b)"
  by (import word_base BIT_WCAT1)

lemma WSEG_WCAT_WSEG1: "ALL (n1::nat) n2::nat.
   RES_FORALL (PWORDLEN n1)
    (%w1::'a::type word.
        RES_FORALL (PWORDLEN n2)
         (%w2::'a::type word.
             ALL (m::nat) k::nat.
                m <= n1 & n2 <= k -->
                WSEG m k (WCAT (w1, w2)) = WSEG m (k - n2) w1))"
  by (import word_base WSEG_WCAT_WSEG1)

lemma WSEG_WCAT_WSEG2: "ALL (n1::nat) n2::nat.
   RES_FORALL (PWORDLEN n1)
    (%w1::'a::type word.
        RES_FORALL (PWORDLEN n2)
         (%w2::'a::type word.
             ALL (m::nat) k::nat.
                m + k <= n2 --> WSEG m k (WCAT (w1, w2)) = WSEG m k w2))"
  by (import word_base WSEG_WCAT_WSEG2)

lemma WSEG_WCAT_WSEG: "ALL (n1::nat) n2::nat.
   RES_FORALL (PWORDLEN n1)
    (%w1::'a::type word.
        RES_FORALL (PWORDLEN n2)
         (%w2::'a::type word.
             ALL (m::nat) k::nat.
                m + k <= n1 + n2 & k < n2 & n2 <= m + k -->
                WSEG m k (WCAT (w1, w2)) =
                WCAT (WSEG (m + k - n2) (0::nat) w1, WSEG (n2 - k) k w2)))"
  by (import word_base WSEG_WCAT_WSEG)

lemma BIT_EQ_IMP_WORD_EQ: "(All::(nat => bool) => bool)
 (%n::nat.
     (RES_FORALL::('a::type word => bool)
                  => ('a::type word => bool) => bool)
      ((PWORDLEN::nat => 'a::type word => bool) n)
      (%w1::'a::type word.
          (RES_FORALL::('a::type word => bool)
                       => ('a::type word => bool) => bool)
           ((PWORDLEN::nat => 'a::type word => bool) n)
           (%w2::'a::type word.
               (op -->::bool => bool => bool)
                ((All::(nat => bool) => bool)
                  (%k::nat.
                      (op -->::bool => bool => bool)
                       ((op <::nat => nat => bool) k n)
                       ((op =::'a::type => 'a::type => bool)
                         ((bit::nat => 'a::type word => 'a::type) k w1)
                         ((bit::nat => 'a::type word => 'a::type) k w2))))
                ((op =::'a::type word => 'a::type word => bool) w1 w2))))"
  by (import word_base BIT_EQ_IMP_WORD_EQ)

;end_setup

;setup_theory word_num

constdefs
  LVAL :: "('a::type => nat) => nat => 'a::type list => nat" 
  "LVAL ==
%(f::'a::type => nat) b::nat.
   foldl (%(e::nat) x::'a::type. b * e + f x) (0::nat)"

lemma LVAL_DEF: "ALL (f::'a::type => nat) (b::nat) l::'a::type list.
   LVAL f b l = foldl (%(e::nat) x::'a::type. b * e + f x) (0::nat) l"
  by (import word_num LVAL_DEF)

consts
  NVAL :: "('a::type => nat) => nat => 'a::type word => nat" 

specification (NVAL) NVAL_DEF: "ALL (f::'a::type => nat) (b::nat) l::'a::type list.
   NVAL f b (WORD l) = LVAL f b l"
  by (import word_num NVAL_DEF)

lemma LVAL: "(ALL (x::'a::type => nat) xa::nat. LVAL x xa [] = (0::nat)) &
(ALL (x::'a::type list) (xa::'a::type => nat) (xb::nat) xc::'a::type.
    LVAL xa xb (xc # x) = xa xc * xb ^ length x + LVAL xa xb x)"
  by (import word_num LVAL)

lemma LVAL_SNOC: "ALL (l::'a::type list) (h::'a::type) (f::'a::type => nat) b::nat.
   LVAL f b (SNOC h l) = LVAL f b l * b + f h"
  by (import word_num LVAL_SNOC)

lemma LVAL_MAX: "ALL (l::'a::type list) (f::'a::type => nat) b::nat.
   (ALL x::'a::type. f x < b) --> LVAL f b l < b ^ length l"
  by (import word_num LVAL_MAX)

lemma NVAL_MAX: "ALL (f::'a::type => nat) b::nat.
   (ALL x::'a::type. f x < b) -->
   (ALL n::nat.
       RES_FORALL (PWORDLEN n) (%w::'a::type word. NVAL f b w < b ^ n))"
  by (import word_num NVAL_MAX)

lemma NVAL0: "ALL (x::'a::type => nat) xa::nat. NVAL x xa (WORD []) = (0::nat)"
  by (import word_num NVAL0)

lemma NVAL1: "ALL (x::'a::type => nat) (xa::nat) xb::'a::type.
   NVAL x xa (WORD [xb]) = x xb"
  by (import word_num NVAL1)

lemma NVAL_WORDLEN_0: "RES_FORALL (PWORDLEN (0::nat))
 (%w::'a::type word.
     ALL (fv::'a::type => nat) r::nat. NVAL fv r w = (0::nat))"
  by (import word_num NVAL_WORDLEN_0)

lemma NVAL_WCAT1: "ALL (w::'a::type word) (f::'a::type => nat) (b::nat) x::'a::type.
   NVAL f b (WCAT (w, WORD [x])) = NVAL f b w * b + f x"
  by (import word_num NVAL_WCAT1)

lemma NVAL_WCAT2: "ALL n::nat.
   RES_FORALL (PWORDLEN n)
    (%w::'a::type word.
        ALL (f::'a::type => nat) (b::nat) x::'a::type.
           NVAL f b (WCAT (WORD [x], w)) = f x * b ^ n + NVAL f b w)"
  by (import word_num NVAL_WCAT2)

lemma NVAL_WCAT: "ALL (n::nat) m::nat.
   RES_FORALL (PWORDLEN n)
    (%w1::'a::type word.
        RES_FORALL (PWORDLEN m)
         (%w2::'a::type word.
             ALL (f::'a::type => nat) b::nat.
                NVAL f b (WCAT (w1, w2)) =
                NVAL f b w1 * b ^ m + NVAL f b w2))"
  by (import word_num NVAL_WCAT)

consts
  NLIST :: "nat => (nat => 'a::type) => nat => nat => 'a::type list" 

specification (NLIST) NLIST_DEF: "(ALL (frep::nat => 'a::type) (b::nat) m::nat.
    NLIST (0::nat) frep b m = []) &
(ALL (n::nat) (frep::nat => 'a::type) (b::nat) m::nat.
    NLIST (Suc n) frep b m =
    SNOC (frep (m mod b)) (NLIST n frep b (m div b)))"
  by (import word_num NLIST_DEF)

constdefs
  NWORD :: "nat => (nat => 'a::type) => nat => nat => 'a::type word" 
  "NWORD ==
%(n::nat) (frep::nat => 'a::type) (b::nat) m::nat. WORD (NLIST n frep b m)"

lemma NWORD_DEF: "ALL (n::nat) (frep::nat => 'a::type) (b::nat) m::nat.
   NWORD n frep b m = WORD (NLIST n frep b m)"
  by (import word_num NWORD_DEF)

lemma NWORD_LENGTH: "ALL (x::nat) (xa::nat => 'a::type) (xb::nat) xc::nat.
   WORDLEN (NWORD x xa xb xc) = x"
  by (import word_num NWORD_LENGTH)

lemma NWORD_PWORDLEN: "ALL (x::nat) (xa::nat => 'a::type) (xb::nat) xc::nat.
   IN (NWORD x xa xb xc) (PWORDLEN x)"
  by (import word_num NWORD_PWORDLEN)

;end_setup

;setup_theory word_bitop

consts
  PBITOP :: "('a::type word => 'b::type word) => bool" 

defs
  PBITOP_primdef: "PBITOP ==
GSPEC
 (%oper::'a::type word => 'b::type word.
     (oper,
      ALL n::nat.
         RES_FORALL (PWORDLEN n)
          (%w::'a::type word.
              IN (oper w) (PWORDLEN n) &
              (ALL (m::nat) k::nat.
                  m + k <= n --> oper (WSEG m k w) = WSEG m k (oper w)))))"

lemma PBITOP_def: "PBITOP =
GSPEC
 (%oper::'a::type word => 'b::type word.
     (oper,
      ALL n::nat.
         RES_FORALL (PWORDLEN n)
          (%w::'a::type word.
              IN (oper w) (PWORDLEN n) &
              (ALL (m::nat) k::nat.
                  m + k <= n --> oper (WSEG m k w) = WSEG m k (oper w)))))"
  by (import word_bitop PBITOP_def)

lemma IN_PBITOP: "ALL oper::'a::type word => 'b::type word.
   IN oper PBITOP =
   (ALL n::nat.
       RES_FORALL (PWORDLEN n)
        (%w::'a::type word.
            IN (oper w) (PWORDLEN n) &
            (ALL (m::nat) k::nat.
                m + k <= n --> oper (WSEG m k w) = WSEG m k (oper w))))"
  by (import word_bitop IN_PBITOP)

lemma PBITOP_PWORDLEN: "RES_FORALL PBITOP
 (%oper::'a::type word => 'b::type word.
     ALL n::nat.
        RES_FORALL (PWORDLEN n)
         (%w::'a::type word. IN (oper w) (PWORDLEN n)))"
  by (import word_bitop PBITOP_PWORDLEN)

lemma PBITOP_WSEG: "RES_FORALL PBITOP
 (%oper::'a::type word => 'b::type word.
     ALL n::nat.
        RES_FORALL (PWORDLEN n)
         (%w::'a::type word.
             ALL (m::nat) k::nat.
                m + k <= n --> oper (WSEG m k w) = WSEG m k (oper w)))"
  by (import word_bitop PBITOP_WSEG)

lemma PBITOP_BIT: "(RES_FORALL::(('a::type word => 'b::type word) => bool)
             => (('a::type word => 'b::type word) => bool) => bool)
 (PBITOP::('a::type word => 'b::type word) => bool)
 (%oper::'a::type word => 'b::type word.
     (All::(nat => bool) => bool)
      (%n::nat.
          (RES_FORALL::('a::type word => bool)
                       => ('a::type word => bool) => bool)
           ((PWORDLEN::nat => 'a::type word => bool) n)
           (%w::'a::type word.
               (All::(nat => bool) => bool)
                (%k::nat.
                    (op -->::bool => bool => bool)
                     ((op <::nat => nat => bool) k n)
                     ((op =::'b::type word => 'b::type word => bool)
                       (oper
                         ((WORD::'a::type list => 'a::type word)
                           ((op #::'a::type
                                   => 'a::type list => 'a::type list)
                             ((bit::nat => 'a::type word => 'a::type) k w)
                             ([]::'a::type list))))
                       ((WORD::'b::type list => 'b::type word)
                         ((op #::'b::type => 'b::type list => 'b::type list)
                           ((bit::nat => 'b::type word => 'b::type) k
                             (oper w))
                           ([]::'b::type list))))))))"
  by (import word_bitop PBITOP_BIT)

consts
  PBITBOP :: "('a::type word => 'b::type word => 'c::type word) => bool" 

defs
  PBITBOP_primdef: "PBITBOP ==
GSPEC
 (%oper::'a::type word => 'b::type word => 'c::type word.
     (oper,
      ALL n::nat.
         RES_FORALL (PWORDLEN n)
          (%w1::'a::type word.
              RES_FORALL (PWORDLEN n)
               (%w2::'b::type word.
                   IN (oper w1 w2) (PWORDLEN n) &
                   (ALL (m::nat) k::nat.
                       m + k <= n -->
                       oper (WSEG m k w1) (WSEG m k w2) =
                       WSEG m k (oper w1 w2))))))"

lemma PBITBOP_def: "PBITBOP =
GSPEC
 (%oper::'a::type word => 'b::type word => 'c::type word.
     (oper,
      ALL n::nat.
         RES_FORALL (PWORDLEN n)
          (%w1::'a::type word.
              RES_FORALL (PWORDLEN n)
               (%w2::'b::type word.
                   IN (oper w1 w2) (PWORDLEN n) &
                   (ALL (m::nat) k::nat.
                       m + k <= n -->
                       oper (WSEG m k w1) (WSEG m k w2) =
                       WSEG m k (oper w1 w2))))))"
  by (import word_bitop PBITBOP_def)

lemma IN_PBITBOP: "ALL oper::'a::type word => 'b::type word => 'c::type word.
   IN oper PBITBOP =
   (ALL n::nat.
       RES_FORALL (PWORDLEN n)
        (%w1::'a::type word.
            RES_FORALL (PWORDLEN n)
             (%w2::'b::type word.
                 IN (oper w1 w2) (PWORDLEN n) &
                 (ALL (m::nat) k::nat.
                     m + k <= n -->
                     oper (WSEG m k w1) (WSEG m k w2) =
                     WSEG m k (oper w1 w2)))))"
  by (import word_bitop IN_PBITBOP)

lemma PBITBOP_PWORDLEN: "RES_FORALL PBITBOP
 (%oper::'a::type word => 'b::type word => 'c::type word.
     ALL n::nat.
        RES_FORALL (PWORDLEN n)
         (%w1::'a::type word.
             RES_FORALL (PWORDLEN n)
              (%w2::'b::type word. IN (oper w1 w2) (PWORDLEN n))))"
  by (import word_bitop PBITBOP_PWORDLEN)

lemma PBITBOP_WSEG: "RES_FORALL PBITBOP
 (%oper::'a::type word => 'b::type word => 'c::type word.
     ALL n::nat.
        RES_FORALL (PWORDLEN n)
         (%w1::'a::type word.
             RES_FORALL (PWORDLEN n)
              (%w2::'b::type word.
                  ALL (m::nat) k::nat.
                     m + k <= n -->
                     oper (WSEG m k w1) (WSEG m k w2) =
                     WSEG m k (oper w1 w2))))"
  by (import word_bitop PBITBOP_WSEG)

lemma PBITBOP_EXISTS: "ALL f::'a::type => 'b::type => 'c::type.
   EX x::'a::type word => 'b::type word => 'c::type word.
      ALL (l1::'a::type list) l2::'b::type list.
         x (WORD l1) (WORD l2) = WORD (map2 f l1 l2)"
  by (import word_bitop PBITBOP_EXISTS)

consts
  WMAP :: "('a::type => 'b::type) => 'a::type word => 'b::type word" 

specification (WMAP) WMAP_DEF: "ALL (f::'a::type => 'b::type) l::'a::type list.
   WMAP f (WORD l) = WORD (map f l)"
  by (import word_bitop WMAP_DEF)

lemma WMAP_PWORDLEN: "RES_FORALL (PWORDLEN (n::nat))
 (%w::'a::type word.
     ALL f::'a::type => 'b::type. IN (WMAP f w) (PWORDLEN n))"
  by (import word_bitop WMAP_PWORDLEN)

lemma WMAP_0: "ALL x::'a::type => 'b::type. WMAP x (WORD []) = WORD []"
  by (import word_bitop WMAP_0)

lemma WMAP_BIT: "(All::(nat => bool) => bool)
 (%n::nat.
     (RES_FORALL::('a::type word => bool)
                  => ('a::type word => bool) => bool)
      ((PWORDLEN::nat => 'a::type word => bool) n)
      (%w::'a::type word.
          (All::(nat => bool) => bool)
           (%k::nat.
               (op -->::bool => bool => bool)
                ((op <::nat => nat => bool) k n)
                ((All::(('a::type => 'b::type) => bool) => bool)
                  (%f::'a::type => 'b::type.
                      (op =::'b::type => 'b::type => bool)
                       ((bit::nat => 'b::type word => 'b::type) k
                         ((WMAP::('a::type => 'b::type)
                                 => 'a::type word => 'b::type word)
                           f w))
                       (f ((bit::nat => 'a::type word => 'a::type) k
                            w)))))))"
  by (import word_bitop WMAP_BIT)

lemma WMAP_WSEG: "ALL n::nat.
   RES_FORALL (PWORDLEN n)
    (%w::'a::type word.
        ALL (m::nat) k::nat.
           m + k <= n -->
           (ALL f::'a::type => 'b::type.
               WMAP f (WSEG m k w) = WSEG m k (WMAP f w)))"
  by (import word_bitop WMAP_WSEG)

lemma WMAP_PBITOP: "ALL f::'a::type => 'b::type. IN (WMAP f) PBITOP"
  by (import word_bitop WMAP_PBITOP)

lemma WMAP_WCAT: "ALL (w1::'a::type word) (w2::'a::type word) f::'a::type => 'b::type.
   WMAP f (WCAT (w1, w2)) = WCAT (WMAP f w1, WMAP f w2)"
  by (import word_bitop WMAP_WCAT)

lemma WMAP_o: "ALL (w::'a::type word) (f::'a::type => 'b::type) g::'b::type => 'c::type.
   WMAP g (WMAP f w) = WMAP (g o f) w"
  by (import word_bitop WMAP_o)

consts
  FORALLBITS :: "('a::type => bool) => 'a::type word => bool" 

specification (FORALLBITS) FORALLBITS_DEF: "ALL (P::'a::type => bool) l::'a::type list.
   FORALLBITS P (WORD l) = list_all P l"
  by (import word_bitop FORALLBITS_DEF)

lemma FORALLBITS: "(All::(nat => bool) => bool)
 (%n::nat.
     (RES_FORALL::('a::type word => bool)
                  => ('a::type word => bool) => bool)
      ((PWORDLEN::nat => 'a::type word => bool) n)
      (%w::'a::type word.
          (All::(('a::type => bool) => bool) => bool)
           (%P::'a::type => bool.
               (op =::bool => bool => bool)
                ((FORALLBITS::('a::type => bool) => 'a::type word => bool) P
                  w)
                ((All::(nat => bool) => bool)
                  (%k::nat.
                      (op -->::bool => bool => bool)
                       ((op <::nat => nat => bool) k n)
                       (P ((bit::nat => 'a::type word => 'a::type) k
                            w)))))))"
  by (import word_bitop FORALLBITS)

lemma FORALLBITS_WSEG: "ALL n::nat.
   RES_FORALL (PWORDLEN n)
    (%w::'a::type word.
        ALL P::'a::type => bool.
           FORALLBITS P w -->
           (ALL (m::nat) k::nat. m + k <= n --> FORALLBITS P (WSEG m k w)))"
  by (import word_bitop FORALLBITS_WSEG)

lemma FORALLBITS_WCAT: "ALL (w1::'a::type word) (w2::'a::type word) P::'a::type => bool.
   FORALLBITS P (WCAT (w1, w2)) = (FORALLBITS P w1 & FORALLBITS P w2)"
  by (import word_bitop FORALLBITS_WCAT)

consts
  EXISTSABIT :: "('a::type => bool) => 'a::type word => bool" 

specification (EXISTSABIT) EXISTSABIT_DEF: "ALL (P::'a::type => bool) l::'a::type list.
   EXISTSABIT P (WORD l) = list_exists P l"
  by (import word_bitop EXISTSABIT_DEF)

lemma NOT_EXISTSABIT: "ALL (P::'a::type => bool) w::'a::type word.
   (~ EXISTSABIT P w) = FORALLBITS (Not o P) w"
  by (import word_bitop NOT_EXISTSABIT)

lemma NOT_FORALLBITS: "ALL (P::'a::type => bool) w::'a::type word.
   (~ FORALLBITS P w) = EXISTSABIT (Not o P) w"
  by (import word_bitop NOT_FORALLBITS)

lemma EXISTSABIT: "(All::(nat => bool) => bool)
 (%n::nat.
     (RES_FORALL::('a::type word => bool)
                  => ('a::type word => bool) => bool)
      ((PWORDLEN::nat => 'a::type word => bool) n)
      (%w::'a::type word.
          (All::(('a::type => bool) => bool) => bool)
           (%P::'a::type => bool.
               (op =::bool => bool => bool)
                ((EXISTSABIT::('a::type => bool) => 'a::type word => bool) P
                  w)
                ((Ex::(nat => bool) => bool)
                  (%k::nat.
                      (op &::bool => bool => bool)
                       ((op <::nat => nat => bool) k n)
                       (P ((bit::nat => 'a::type word => 'a::type) k
                            w)))))))"
  by (import word_bitop EXISTSABIT)

lemma EXISTSABIT_WSEG: "ALL n::nat.
   RES_FORALL (PWORDLEN n)
    (%w::'a::type word.
        ALL (m::nat) k::nat.
           m + k <= n -->
           (ALL P::'a::type => bool.
               EXISTSABIT P (WSEG m k w) --> EXISTSABIT P w))"
  by (import word_bitop EXISTSABIT_WSEG)

lemma EXISTSABIT_WCAT: "ALL (w1::'a::type word) (w2::'a::type word) P::'a::type => bool.
   EXISTSABIT P (WCAT (w1, w2)) = (EXISTSABIT P w1 | EXISTSABIT P w2)"
  by (import word_bitop EXISTSABIT_WCAT)

constdefs
  SHR :: "bool => 'a::type => 'a::type word => 'a::type word * 'a::type" 
  "SHR ==
%(f::bool) (b::'a::type) w::'a::type word.
   (WCAT
     (if f then WSEG (1::nat) (PRE (WORDLEN w)) w else WORD [b],
      WSEG (PRE (WORDLEN w)) (1::nat) w),
    bit (0::nat) w)"

lemma SHR_DEF: "ALL (f::bool) (b::'a::type) w::'a::type word.
   SHR f b w =
   (WCAT
     (if f then WSEG (1::nat) (PRE (WORDLEN w)) w else WORD [b],
      WSEG (PRE (WORDLEN w)) (1::nat) w),
    bit (0::nat) w)"
  by (import word_bitop SHR_DEF)

constdefs
  SHL :: "bool => 'a::type word => 'a::type => 'a::type * 'a::type word" 
  "SHL ==
%(f::bool) (w::'a::type word) b::'a::type.
   (bit (PRE (WORDLEN w)) w,
    WCAT
     (WSEG (PRE (WORDLEN w)) (0::nat) w,
      if f then WSEG (1::nat) (0::nat) w else WORD [b]))"

lemma SHL_DEF: "ALL (f::bool) (w::'a::type word) b::'a::type.
   SHL f w b =
   (bit (PRE (WORDLEN w)) w,
    WCAT
     (WSEG (PRE (WORDLEN w)) (0::nat) w,
      if f then WSEG (1::nat) (0::nat) w else WORD [b]))"
  by (import word_bitop SHL_DEF)

lemma SHR_WSEG: "ALL n::nat.
   RES_FORALL (PWORDLEN n)
    (%w::'a::type word.
        ALL (m::nat) k::nat.
           m + k <= n -->
           (0::nat) < m -->
           (ALL (f::bool) b::'a::type.
               SHR f b (WSEG m k w) =
               (if f
                then WCAT
                      (WSEG (1::nat) (k + (m - (1::nat))) w,
                       WSEG (m - (1::nat)) (k + (1::nat)) w)
                else WCAT (WORD [b], WSEG (m - (1::nat)) (k + (1::nat)) w),
                bit k w)))"
  by (import word_bitop SHR_WSEG)

lemma SHR_WSEG_1F: "ALL n::nat.
   RES_FORALL (PWORDLEN n)
    (%w::'a::type word.
        ALL (b::'a::type) (m::nat) k::nat.
           m + k <= n -->
           (0::nat) < m -->
           SHR False b (WSEG m k w) =
           (WCAT (WORD [b], WSEG (m - (1::nat)) (k + (1::nat)) w), bit k w))"
  by (import word_bitop SHR_WSEG_1F)

lemma SHR_WSEG_NF: "ALL n::nat.
   RES_FORALL (PWORDLEN n)
    (%w::'a::type word.
        ALL (m::nat) k::nat.
           m + k < n -->
           (0::nat) < m -->
           SHR False (bit (m + k) w) (WSEG m k w) =
           (WSEG m (k + (1::nat)) w, bit k w))"
  by (import word_bitop SHR_WSEG_NF)

lemma SHL_WSEG: "ALL n::nat.
   RES_FORALL (PWORDLEN n)
    (%w::'a::type word.
        ALL (m::nat) k::nat.
           m + k <= n -->
           (0::nat) < m -->
           (ALL (f::bool) b::'a::type.
               SHL f (WSEG m k w) b =
               (bit (k + (m - (1::nat))) w,
                if f then WCAT (WSEG (m - (1::nat)) k w, WSEG (1::nat) k w)
                else WCAT (WSEG (m - (1::nat)) k w, WORD [b]))))"
  by (import word_bitop SHL_WSEG)

lemma SHL_WSEG_1F: "ALL n::nat.
   RES_FORALL (PWORDLEN n)
    (%w::'a::type word.
        ALL (b::'a::type) (m::nat) k::nat.
           m + k <= n -->
           (0::nat) < m -->
           SHL False (WSEG m k w) b =
           (bit (k + (m - (1::nat))) w,
            WCAT (WSEG (m - (1::nat)) k w, WORD [b])))"
  by (import word_bitop SHL_WSEG_1F)

lemma SHL_WSEG_NF: "ALL n::nat.
   RES_FORALL (PWORDLEN n)
    (%w::'a::type word.
        ALL (m::nat) k::nat.
           m + k <= n -->
           (0::nat) < m -->
           (0::nat) < k -->
           SHL False (WSEG m k w) (bit (k - (1::nat)) w) =
           (bit (k + (m - (1::nat))) w, WSEG m (k - (1::nat)) w))"
  by (import word_bitop SHL_WSEG_NF)

lemma WSEG_SHL: "ALL n::nat.
   RES_FORALL (PWORDLEN (Suc n))
    (%w::'a::type word.
        ALL (m::nat) k::nat.
           (0::nat) < k & m + k <= Suc n -->
           (ALL b::'a::type.
               WSEG m k (snd (SHL (f::bool) w b)) =
               WSEG m (k - (1::nat)) w))"
  by (import word_bitop WSEG_SHL)

lemma WSEG_SHL_0: "ALL n::nat.
   RES_FORALL (PWORDLEN (Suc n))
    (%w::'a::type word.
        ALL (m::nat) b::'a::type.
           (0::nat) < m & m <= Suc n -->
           WSEG m (0::nat) (snd (SHL (f::bool) w b)) =
           WCAT
            (WSEG (m - (1::nat)) (0::nat) w,
             if f then WSEG (1::nat) (0::nat) w else WORD [b]))"
  by (import word_bitop WSEG_SHL_0)

;end_setup

;setup_theory bword_num

constdefs
  BV :: "bool => nat" 
  "(BV == (%(b::bool). (if b then (Suc (0::nat)) else (0::nat))))"

lemma BV_DEF: "(ALL (b::bool). ((BV b) = (if b then (Suc (0::nat)) else (0::nat))))"
  by (import bword_num BV_DEF)

consts
  BNVAL :: "bool word => nat" 

specification (BNVAL) BNVAL_DEF: "ALL l::bool list. BNVAL (WORD l) = LVAL BV (2::nat) l"
  by (import bword_num BNVAL_DEF)

lemma BV_LESS_2: "ALL x::bool. BV x < (2::nat)"
  by (import bword_num BV_LESS_2)

lemma BNVAL_NVAL: "ALL w::bool word. BNVAL w = NVAL BV (2::nat) w"
  by (import bword_num BNVAL_NVAL)

lemma BNVAL0: "BNVAL (WORD []) = (0::nat)"
  by (import bword_num BNVAL0)

lemma BNVAL_11: "ALL (w1::bool word) w2::bool word.
   WORDLEN w1 = WORDLEN w2 --> BNVAL w1 = BNVAL w2 --> w1 = w2"
  by (import bword_num BNVAL_11)

lemma BNVAL_ONTO: "ALL w::bool word. Ex (op = (BNVAL w))"
  by (import bword_num BNVAL_ONTO)

lemma BNVAL_MAX: "ALL n::nat. RES_FORALL (PWORDLEN n) (%w::bool word. BNVAL w < (2::nat) ^ n)"
  by (import bword_num BNVAL_MAX)

lemma BNVAL_WCAT1: "ALL n::nat.
   RES_FORALL (PWORDLEN n)
    (%w::bool word.
        ALL x::bool. BNVAL (WCAT (w, WORD [x])) = BNVAL w * (2::nat) + BV x)"
  by (import bword_num BNVAL_WCAT1)

lemma BNVAL_WCAT2: "ALL n::nat.
   RES_FORALL (PWORDLEN n)
    (%w::bool word.
        ALL x::bool.
           BNVAL (WCAT (WORD [x], w)) = BV x * (2::nat) ^ n + BNVAL w)"
  by (import bword_num BNVAL_WCAT2)

lemma BNVAL_WCAT: "ALL (n::nat) m::nat.
   RES_FORALL (PWORDLEN n)
    (%w1::bool word.
        RES_FORALL (PWORDLEN m)
         (%w2::bool word.
             BNVAL (WCAT (w1, w2)) = BNVAL w1 * (2::nat) ^ m + BNVAL w2))"
  by (import bword_num BNVAL_WCAT)

constdefs
  VB :: "nat => bool" 
  "VB == %n::nat. n mod (2::nat) ~= (0::nat)"

lemma VB_DEF: "ALL n::nat. VB n = (n mod (2::nat) ~= (0::nat))"
  by (import bword_num VB_DEF)

constdefs
  NBWORD :: "nat => nat => bool word" 
  "NBWORD == %(n::nat) m::nat. WORD (NLIST n VB (2::nat) m)"

lemma NBWORD_DEF: "ALL (n::nat) m::nat. NBWORD n m = WORD (NLIST n VB (2::nat) m)"
  by (import bword_num NBWORD_DEF)

lemma NBWORD0: "ALL x::nat. NBWORD (0::nat) x = WORD []"
  by (import bword_num NBWORD0)

lemma WORDLEN_NBWORD: "ALL (x::nat) xa::nat. WORDLEN (NBWORD x xa) = x"
  by (import bword_num WORDLEN_NBWORD)

lemma PWORDLEN_NBWORD: "ALL (x::nat) xa::nat. IN (NBWORD x xa) (PWORDLEN x)"
  by (import bword_num PWORDLEN_NBWORD)

lemma NBWORD_SUC: "ALL (n::nat) m::nat.
   NBWORD (Suc n) m =
   WCAT (NBWORD n (m div (2::nat)), WORD [VB (m mod (2::nat))])"
  by (import bword_num NBWORD_SUC)

lemma VB_BV: "ALL x::bool. VB (BV x) = x"
  by (import bword_num VB_BV)

lemma BV_VB: "(All::(nat => bool) => bool)
 (%x::nat.
     (op -->::bool => bool => bool)
      ((op <::nat => nat => bool) x
        ((number_of::bin => nat)
          ((op BIT::bin => bit => bin)
            ((op BIT::bin => bit => bin) (Numeral.Pls::bin) (bit.B1::bit))
            (bit.B0::bit))))
      ((op =::nat => nat => bool) ((BV::bool => nat) ((VB::nat => bool) x))
        x))"
  by (import bword_num BV_VB)

lemma NBWORD_BNVAL: "ALL n::nat. RES_FORALL (PWORDLEN n) (%w::bool word. NBWORD n (BNVAL w) = w)"
  by (import bword_num NBWORD_BNVAL)

lemma BNVAL_NBWORD: "ALL (n::nat) m::nat. m < (2::nat) ^ n --> BNVAL (NBWORD n m) = m"
  by (import bword_num BNVAL_NBWORD)

lemma ZERO_WORD_VAL: "RES_FORALL (PWORDLEN (n::nat))
 (%w::bool word. (w = NBWORD n (0::nat)) = (BNVAL w = (0::nat)))"
  by (import bword_num ZERO_WORD_VAL)

lemma WCAT_NBWORD_0: "ALL (n1::nat) n2::nat.
   WCAT (NBWORD n1 (0::nat), NBWORD n2 (0::nat)) = NBWORD (n1 + n2) (0::nat)"
  by (import bword_num WCAT_NBWORD_0)

lemma WSPLIT_NBWORD_0: "ALL (n::nat) m::nat.
   m <= n -->
   WSPLIT m (NBWORD n (0::nat)) =
   (NBWORD (n - m) (0::nat), NBWORD m (0::nat))"
  by (import bword_num WSPLIT_NBWORD_0)

lemma EQ_NBWORD0_SPLIT: "(All::(nat => bool) => bool)
 (%n::nat.
     (RES_FORALL::(bool word => bool) => (bool word => bool) => bool)
      ((PWORDLEN::nat => bool word => bool) n)
      (%w::bool word.
          (All::(nat => bool) => bool)
           (%m::nat.
               (op -->::bool => bool => bool)
                ((op <=::nat => nat => bool) m n)
                ((op =::bool => bool => bool)
                  ((op =::bool word => bool word => bool) w
                    ((NBWORD::nat => nat => bool word) n (0::nat)))
                  ((op &::bool => bool => bool)
                    ((op =::bool word => bool word => bool)
                      ((WSEG::nat => nat => bool word => bool word)
                        ((op -::nat => nat => nat) n m) m w)
                      ((NBWORD::nat => nat => bool word)
                        ((op -::nat => nat => nat) n m) (0::nat)))
                    ((op =::bool word => bool word => bool)
                      ((WSEG::nat => nat => bool word => bool word) m
                        (0::nat) w)
                      ((NBWORD::nat => nat => bool word) m (0::nat))))))))"
  by (import bword_num EQ_NBWORD0_SPLIT)

lemma NBWORD_MOD: "ALL (n::nat) m::nat. NBWORD n (m mod (2::nat) ^ n) = NBWORD n m"
  by (import bword_num NBWORD_MOD)

lemma WSEG_NBWORD_SUC: "ALL (n::nat) m::nat. WSEG n (0::nat) (NBWORD (Suc n) m) = NBWORD n m"
  by (import bword_num WSEG_NBWORD_SUC)

lemma NBWORD_SUC_WSEG: "ALL n::nat.
   RES_FORALL (PWORDLEN (Suc n))
    (%w::bool word. NBWORD n (BNVAL w) = WSEG n (0::nat) w)"
  by (import bword_num NBWORD_SUC_WSEG)

lemma DOUBL_EQ_SHL: "ALL x>0::nat.
   RES_FORALL (PWORDLEN x)
    (%xa::bool word.
        ALL xb::bool.
           NBWORD x (BNVAL xa + BNVAL xa + BV xb) = snd (SHL False xa xb))"
  by (import bword_num DOUBL_EQ_SHL)

lemma MSB_NBWORD: "ALL (n::nat) m::nat.
   bit n (NBWORD (Suc n) m) = VB (m div (2::nat) ^ n mod (2::nat))"
  by (import bword_num MSB_NBWORD)

lemma NBWORD_SPLIT: "ALL (n1::nat) (n2::nat) m::nat.
   NBWORD (n1 + n2) m = WCAT (NBWORD n1 (m div (2::nat) ^ n2), NBWORD n2 m)"
  by (import bword_num NBWORD_SPLIT)

lemma WSEG_NBWORD: "ALL (m::nat) (k::nat) n::nat.
   m + k <= n -->
   (ALL l::nat. WSEG m k (NBWORD n l) = NBWORD m (l div (2::nat) ^ k))"
  by (import bword_num WSEG_NBWORD)

lemma NBWORD_SUC_FST: "ALL (n::nat) x::nat.
   NBWORD (Suc n) x =
   WCAT (WORD [VB (x div (2::nat) ^ n mod (2::nat))], NBWORD n x)"
  by (import bword_num NBWORD_SUC_FST)

lemma BIT_NBWORD0: "ALL (k::nat) n::nat. k < n --> bit k (NBWORD n (0::nat)) = False"
  by (import bword_num BIT_NBWORD0)

lemma ADD_BNVAL_LEFT: "ALL n::nat.
   RES_FORALL (PWORDLEN (Suc n))
    (%w1::bool word.
        RES_FORALL (PWORDLEN (Suc n))
         (%w2::bool word.
             BNVAL w1 + BNVAL w2 =
             (BV (bit n w1) + BV (bit n w2)) * (2::nat) ^ n +
             (BNVAL (WSEG n (0::nat) w1) + BNVAL (WSEG n (0::nat) w2))))"
  by (import bword_num ADD_BNVAL_LEFT)

lemma ADD_BNVAL_RIGHT: "ALL n::nat.
   RES_FORALL (PWORDLEN (Suc n))
    (%w1::bool word.
        RES_FORALL (PWORDLEN (Suc n))
         (%w2::bool word.
             BNVAL w1 + BNVAL w2 =
             (BNVAL (WSEG n (1::nat) w1) + BNVAL (WSEG n (1::nat) w2)) *
             (2::nat) +
             (BV (bit (0::nat) w1) + BV (bit (0::nat) w2))))"
  by (import bword_num ADD_BNVAL_RIGHT)

lemma ADD_BNVAL_SPLIT: "ALL (n1::nat) n2::nat.
   RES_FORALL (PWORDLEN (n1 + n2))
    (%w1::bool word.
        RES_FORALL (PWORDLEN (n1 + n2))
         (%w2::bool word.
             BNVAL w1 + BNVAL w2 =
             (BNVAL (WSEG n1 n2 w1) + BNVAL (WSEG n1 n2 w2)) *
             (2::nat) ^ n2 +
             (BNVAL (WSEG n2 (0::nat) w1) + BNVAL (WSEG n2 (0::nat) w2))))"
  by (import bword_num ADD_BNVAL_SPLIT)

;end_setup

;setup_theory bword_arith

consts
  ACARRY :: "nat => bool word => bool word => bool => bool" 

specification (ACARRY) ACARRY_DEF: "(ALL (w1::bool word) (w2::bool word) cin::bool.
    ACARRY (0::nat) w1 w2 cin = cin) &
(ALL (n::nat) (w1::bool word) (w2::bool word) cin::bool.
    ACARRY (Suc n) w1 w2 cin =
    VB ((BV (bit n w1) + BV (bit n w2) + BV (ACARRY n w1 w2 cin)) div
        (2::nat)))"
  by (import bword_arith ACARRY_DEF)

consts
  ICARRY :: "nat => bool word => bool word => bool => bool" 

specification (ICARRY) ICARRY_DEF: "(ALL (w1::bool word) (w2::bool word) cin::bool.
    ICARRY (0::nat) w1 w2 cin = cin) &
(ALL (n::nat) (w1::bool word) (w2::bool word) cin::bool.
    ICARRY (Suc n) w1 w2 cin =
    (bit n w1 & bit n w2 | (bit n w1 | bit n w2) & ICARRY n w1 w2 cin))"
  by (import bword_arith ICARRY_DEF)

lemma ACARRY_EQ_ICARRY: "ALL n::nat.
   RES_FORALL (PWORDLEN n)
    (%w1::bool word.
        RES_FORALL (PWORDLEN n)
         (%w2::bool word.
             ALL (cin::bool) k::nat.
                k <= n --> ACARRY k w1 w2 cin = ICARRY k w1 w2 cin))"
  by (import bword_arith ACARRY_EQ_ICARRY)

lemma BNVAL_LESS_EQ: "ALL n::nat.
   RES_FORALL (PWORDLEN n)
    (%w::bool word. BNVAL w <= (2::nat) ^ n - (1::nat))"
  by (import bword_arith BNVAL_LESS_EQ)

lemma ADD_BNVAL_LESS_EQ1: "ALL (n::nat) cin::bool.
   RES_FORALL (PWORDLEN n)
    (%w1::bool word.
        RES_FORALL (PWORDLEN n)
         (%w2::bool word.
             (BNVAL w1 + (BNVAL w2 + BV cin)) div (2::nat) ^ n
             <= Suc (0::nat)))"
  by (import bword_arith ADD_BNVAL_LESS_EQ1)

lemma ADD_BV_BNVAL_DIV_LESS_EQ1: "ALL (n::nat) (x1::bool) (x2::bool) cin::bool.
   RES_FORALL (PWORDLEN n)
    (%w1::bool word.
        RES_FORALL (PWORDLEN n)
         (%w2::bool word.
             (BV x1 + BV x2 +
              (BNVAL w1 + (BNVAL w2 + BV cin)) div (2::nat) ^ n) div
             (2::nat)
             <= (1::nat)))"
  by (import bword_arith ADD_BV_BNVAL_DIV_LESS_EQ1)

lemma ADD_BV_BNVAL_LESS_EQ: "ALL (n::nat) (x1::bool) (x2::bool) cin::bool.
   RES_FORALL (PWORDLEN n)
    (%w1::bool word.
        RES_FORALL (PWORDLEN n)
         (%w2::bool word.
             BV x1 + BV x2 + (BNVAL w1 + (BNVAL w2 + BV cin))
             <= Suc ((2::nat) ^ Suc n)))"
  by (import bword_arith ADD_BV_BNVAL_LESS_EQ)

lemma ADD_BV_BNVAL_LESS_EQ1: "ALL (n::nat) (x1::bool) (x2::bool) cin::bool.
   RES_FORALL (PWORDLEN n)
    (%w1::bool word.
        RES_FORALL (PWORDLEN n)
         (%w2::bool word.
             (BV x1 + BV x2 + (BNVAL w1 + (BNVAL w2 + BV cin))) div
             (2::nat) ^ Suc n
             <= (1::nat)))"
  by (import bword_arith ADD_BV_BNVAL_LESS_EQ1)

lemma ACARRY_EQ_ADD_DIV: "(All::(nat => bool) => bool)
 (%n::nat.
     (RES_FORALL::(bool word => bool) => (bool word => bool) => bool)
      ((PWORDLEN::nat => bool word => bool) n)
      (%w1::bool word.
          (RES_FORALL::(bool word => bool) => (bool word => bool) => bool)
           ((PWORDLEN::nat => bool word => bool) n)
           (%w2::bool word.
               (All::(nat => bool) => bool)
                (%k::nat.
                    (op -->::bool => bool => bool)
                     ((op <::nat => nat => bool) k n)
                     ((op =::nat => nat => bool)
                       ((BV::bool => nat)
                         ((ACARRY::nat
                                   => bool word
=> bool word => bool => bool)
                           k w1 w2 (cin::bool)))
                       ((op div::nat => nat => nat)
                         ((op +::nat => nat => nat)
                           ((op +::nat => nat => nat)
                             ((BNVAL::bool word => nat)
                               ((WSEG::nat => nat => bool word => bool word)
                                 k (0::nat) w1))
                             ((BNVAL::bool word => nat)
                               ((WSEG::nat => nat => bool word => bool word)
                                 k (0::nat) w2)))
                           ((BV::bool => nat) cin))
                         ((op ^::nat => nat => nat)
                           ((number_of::bin => nat)
                             ((op BIT::bin => bit => bin)
                               ((op BIT::bin => bit => bin)
                                 (Numeral.Pls::bin) (bit.B1::bit))
                               (bit.B0::bit)))
                           k)))))))"
  by (import bword_arith ACARRY_EQ_ADD_DIV)

lemma ADD_WORD_SPLIT: "ALL (n1::nat) n2::nat.
   RES_FORALL (PWORDLEN (n1 + n2))
    (%w1::bool word.
        RES_FORALL (PWORDLEN (n1 + n2))
         (%w2::bool word.
             ALL cin::bool.
                NBWORD (n1 + n2) (BNVAL w1 + BNVAL w2 + BV cin) =
                WCAT
                 (NBWORD n1
                   (BNVAL (WSEG n1 n2 w1) + BNVAL (WSEG n1 n2 w2) +
                    BV (ACARRY n2 w1 w2 cin)),
                  NBWORD n2
                   (BNVAL (WSEG n2 (0::nat) w1) +
                    BNVAL (WSEG n2 (0::nat) w2) +
                    BV cin))))"
  by (import bword_arith ADD_WORD_SPLIT)

lemma WSEG_NBWORD_ADD: "ALL n::nat.
   RES_FORALL (PWORDLEN n)
    (%w1::bool word.
        RES_FORALL (PWORDLEN n)
         (%w2::bool word.
             ALL (m::nat) (k::nat) cin::bool.
                m + k <= n -->
                WSEG m k (NBWORD n (BNVAL w1 + BNVAL w2 + BV cin)) =
                NBWORD m
                 (BNVAL (WSEG m k w1) + BNVAL (WSEG m k w2) +
                  BV (ACARRY k w1 w2 cin))))"
  by (import bword_arith WSEG_NBWORD_ADD)

lemma ADD_NBWORD_EQ0_SPLIT: "ALL (n1::nat) n2::nat.
   RES_FORALL (PWORDLEN (n1 + n2))
    (%w1::bool word.
        RES_FORALL (PWORDLEN (n1 + n2))
         (%w2::bool word.
             ALL cin::bool.
                (NBWORD (n1 + n2) (BNVAL w1 + BNVAL w2 + BV cin) =
                 NBWORD (n1 + n2) (0::nat)) =
                (NBWORD n1
                  (BNVAL (WSEG n1 n2 w1) + BNVAL (WSEG n1 n2 w2) +
                   BV (ACARRY n2 w1 w2 cin)) =
                 NBWORD n1 (0::nat) &
                 NBWORD n2
                  (BNVAL (WSEG n2 (0::nat) w1) +
                   BNVAL (WSEG n2 (0::nat) w2) +
                   BV cin) =
                 NBWORD n2 (0::nat))))"
  by (import bword_arith ADD_NBWORD_EQ0_SPLIT)

lemma ACARRY_MSB: "ALL n::nat.
   RES_FORALL (PWORDLEN n)
    (%w1::bool word.
        RES_FORALL (PWORDLEN n)
         (%w2::bool word.
             ALL cin::bool.
                ACARRY n w1 w2 cin =
                bit n (NBWORD (Suc n) (BNVAL w1 + BNVAL w2 + BV cin))))"
  by (import bword_arith ACARRY_MSB)

lemma ACARRY_WSEG: "ALL n::nat.
   RES_FORALL (PWORDLEN n)
    (%w1::bool word.
        RES_FORALL (PWORDLEN n)
         (%w2::bool word.
             ALL (cin::bool) (k::nat) m::nat.
                k < m & m <= n -->
                ACARRY k (WSEG m (0::nat) w1) (WSEG m (0::nat) w2) cin =
                ACARRY k w1 w2 cin))"
  by (import bword_arith ACARRY_WSEG)

lemma ICARRY_WSEG: "ALL n::nat.
   RES_FORALL (PWORDLEN n)
    (%w1::bool word.
        RES_FORALL (PWORDLEN n)
         (%w2::bool word.
             ALL (cin::bool) (k::nat) m::nat.
                k < m & m <= n -->
                ICARRY k (WSEG m (0::nat) w1) (WSEG m (0::nat) w2) cin =
                ICARRY k w1 w2 cin))"
  by (import bword_arith ICARRY_WSEG)

lemma ACARRY_ACARRY_WSEG: "ALL n::nat.
   RES_FORALL (PWORDLEN n)
    (%w1::bool word.
        RES_FORALL (PWORDLEN n)
         (%w2::bool word.
             ALL (cin::bool) (m::nat) (k1::nat) k2::nat.
                k1 < m & k2 < n & m + k2 <= n -->
                ACARRY k1 (WSEG m k2 w1) (WSEG m k2 w2)
                 (ACARRY k2 w1 w2 cin) =
                ACARRY (k1 + k2) w1 w2 cin))"
  by (import bword_arith ACARRY_ACARRY_WSEG)

;end_setup

;setup_theory bword_bitop

consts
  WNOT :: "bool word => bool word" 

specification (WNOT) WNOT_DEF: "ALL l::bool list. WNOT (WORD l) = WORD (map Not l)"
  by (import bword_bitop WNOT_DEF)

lemma PBITOP_WNOT: "IN WNOT PBITOP"
  by (import bword_bitop PBITOP_WNOT)

lemma WNOT_WNOT: "ALL w::bool word. WNOT (WNOT w) = w"
  by (import bword_bitop WNOT_WNOT)

lemma WCAT_WNOT: "ALL (n1::nat) n2::nat.
   RES_FORALL (PWORDLEN n1)
    (%w1::bool word.
        RES_FORALL (PWORDLEN n2)
         (%w2::bool word. WCAT (WNOT w1, WNOT w2) = WNOT (WCAT (w1, w2))))"
  by (import bword_bitop WCAT_WNOT)

consts
  WAND :: "bool word => bool word => bool word" 

specification (WAND) WAND_DEF: "ALL (l1::bool list) l2::bool list.
   WAND (WORD l1) (WORD l2) = WORD (map2 op & l1 l2)"
  by (import bword_bitop WAND_DEF)

lemma PBITBOP_WAND: "IN WAND PBITBOP"
  by (import bword_bitop PBITBOP_WAND)

consts
  WOR :: "bool word => bool word => bool word" 

specification (WOR) WOR_DEF: "ALL (l1::bool list) l2::bool list.
   WOR (WORD l1) (WORD l2) = WORD (map2 op | l1 l2)"
  by (import bword_bitop WOR_DEF)

lemma PBITBOP_WOR: "IN WOR PBITBOP"
  by (import bword_bitop PBITBOP_WOR)

consts
  WXOR :: "bool word => bool word => bool word" 

specification (WXOR) WXOR_DEF: "ALL (l1::bool list) l2::bool list.
   WXOR (WORD l1) (WORD l2) = WORD (map2 (%(x::bool) y::bool. x ~= y) l1 l2)"
  by (import bword_bitop WXOR_DEF)

lemma PBITBOP_WXOR: "IN WXOR PBITBOP"
  by (import bword_bitop PBITBOP_WXOR)

;end_setup

end

