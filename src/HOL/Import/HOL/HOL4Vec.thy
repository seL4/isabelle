theory HOL4Vec = HOL4Base:

;setup_theory res_quan

lemma RES_FORALL_CONJ_DIST: "ALL P Q R. RES_FORALL P (%i. Q i & R i) = (RES_FORALL P Q & RES_FORALL P R)"
  by (import res_quan RES_FORALL_CONJ_DIST)

lemma RES_FORALL_DISJ_DIST: "ALL P Q R. RES_FORALL (%j. P j | Q j) R = (RES_FORALL P R & RES_FORALL Q R)"
  by (import res_quan RES_FORALL_DISJ_DIST)

lemma RES_FORALL_UNIQUE: "ALL x xa. RES_FORALL (op = xa) x = x xa"
  by (import res_quan RES_FORALL_UNIQUE)

lemma RES_FORALL_FORALL: "ALL (P::'a => bool) (R::'a => 'b => bool) x::'b.
   (ALL x::'b. RES_FORALL P (%i::'a. R i x)) =
   RES_FORALL P (%i::'a. All (R i))"
  by (import res_quan RES_FORALL_FORALL)

lemma RES_FORALL_REORDER: "ALL P Q R.
   RES_FORALL P (%i. RES_FORALL Q (R i)) =
   RES_FORALL Q (%j. RES_FORALL P (%i. R i j))"
  by (import res_quan RES_FORALL_REORDER)

lemma RES_FORALL_EMPTY: "All (RES_FORALL EMPTY)"
  by (import res_quan RES_FORALL_EMPTY)

lemma RES_FORALL_UNIV: "ALL p. RES_FORALL pred_set.UNIV p = All p"
  by (import res_quan RES_FORALL_UNIV)

lemma RES_FORALL_NULL: "ALL p m. RES_FORALL p (%x. m) = (p = EMPTY | m)"
  by (import res_quan RES_FORALL_NULL)

lemma RES_EXISTS_DISJ_DIST: "(All::(('a => bool) => bool) => bool)
 (%P::'a => bool.
     (All::(('a => bool) => bool) => bool)
      (%Q::'a => bool.
          (All::(('a => bool) => bool) => bool)
           (%R::'a => bool.
               (op =::bool => bool => bool)
                ((RES_EXISTS::('a => bool) => ('a => bool) => bool) P
                  (%i::'a. (op |::bool => bool => bool) (Q i) (R i)))
                ((op |::bool => bool => bool)
                  ((RES_EXISTS::('a => bool) => ('a => bool) => bool) P Q)
                  ((RES_EXISTS::('a => bool) => ('a => bool) => bool) P
                    R)))))"
  by (import res_quan RES_EXISTS_DISJ_DIST)

lemma RES_DISJ_EXISTS_DIST: "ALL P Q R. RES_EXISTS (%i. P i | Q i) R = (RES_EXISTS P R | RES_EXISTS Q R)"
  by (import res_quan RES_DISJ_EXISTS_DIST)

lemma RES_EXISTS_EQUAL: "ALL x xa. RES_EXISTS (op = xa) x = x xa"
  by (import res_quan RES_EXISTS_EQUAL)

lemma RES_EXISTS_REORDER: "ALL P Q R.
   RES_EXISTS P (%i. RES_EXISTS Q (R i)) =
   RES_EXISTS Q (%j. RES_EXISTS P (%i. R i j))"
  by (import res_quan RES_EXISTS_REORDER)

lemma RES_EXISTS_EMPTY: "ALL p. ~ RES_EXISTS EMPTY p"
  by (import res_quan RES_EXISTS_EMPTY)

lemma RES_EXISTS_UNIV: "ALL p. RES_EXISTS pred_set.UNIV p = Ex p"
  by (import res_quan RES_EXISTS_UNIV)

lemma RES_EXISTS_NULL: "ALL p m. RES_EXISTS p (%x. m) = (p ~= EMPTY & m)"
  by (import res_quan RES_EXISTS_NULL)

lemma RES_EXISTS_ALT: "ALL p m. RES_EXISTS p m = (IN (RES_SELECT p m) p & m (RES_SELECT p m))"
  by (import res_quan RES_EXISTS_ALT)

lemma RES_EXISTS_UNIQUE_EMPTY: "ALL p. ~ RES_EXISTS_UNIQUE EMPTY p"
  by (import res_quan RES_EXISTS_UNIQUE_EMPTY)

lemma RES_EXISTS_UNIQUE_UNIV: "ALL p. RES_EXISTS_UNIQUE pred_set.UNIV p = Ex1 p"
  by (import res_quan RES_EXISTS_UNIQUE_UNIV)

lemma RES_EXISTS_UNIQUE_NULL: "ALL p m. RES_EXISTS_UNIQUE p (%x. m) = ((EX x. p = INSERT x EMPTY) & m)"
  by (import res_quan RES_EXISTS_UNIQUE_NULL)

lemma RES_EXISTS_UNIQUE_ALT: "ALL p m.
   RES_EXISTS_UNIQUE p m =
   RES_EXISTS p (%x. m x & RES_FORALL p (%y. m y --> y = x))"
  by (import res_quan RES_EXISTS_UNIQUE_ALT)

lemma RES_SELECT_EMPTY: "ALL p. RES_SELECT EMPTY p = (SOME x. False)"
  by (import res_quan RES_SELECT_EMPTY)

lemma RES_SELECT_UNIV: "ALL p. RES_SELECT pred_set.UNIV p = Eps p"
  by (import res_quan RES_SELECT_UNIV)

lemma RES_ABSTRACT: "ALL p m x. IN x p --> RES_ABSTRACT p m x = m x"
  by (import res_quan RES_ABSTRACT)

lemma RES_ABSTRACT_EQUAL: "ALL p m1 m2.
   (ALL x. IN x p --> m1 x = m2 x) --> RES_ABSTRACT p m1 = RES_ABSTRACT p m2"
  by (import res_quan RES_ABSTRACT_EQUAL)

lemma RES_ABSTRACT_IDEMPOT: "ALL p m. RES_ABSTRACT p (RES_ABSTRACT p m) = RES_ABSTRACT p m"
  by (import res_quan RES_ABSTRACT_IDEMPOT)

lemma RES_ABSTRACT_EQUAL_EQ: "ALL p m1 m2.
   (RES_ABSTRACT p m1 = RES_ABSTRACT p m2) = (ALL x. IN x p --> m1 x = m2 x)"
  by (import res_quan RES_ABSTRACT_EQUAL_EQ)

;end_setup

;setup_theory word_base

typedef (open) ('a) word = "(Collect::('a list recspace => bool) => 'a list recspace set)
 (%x::'a list recspace.
     (All::(('a list recspace => bool) => bool) => bool)
      (%word::'a list recspace => bool.
          (op -->::bool => bool => bool)
           ((All::('a list recspace => bool) => bool)
             (%a0::'a list recspace.
                 (op -->::bool => bool => bool)
                  ((Ex::('a list => bool) => bool)
                    (%a::'a list.
                        (op =::'a list recspace => 'a list recspace => bool)
                         a0 ((CONSTR::nat
=> 'a list => (nat => 'a list recspace) => 'a list recspace)
                              (0::nat) a
                              (%n::nat. BOTTOM::'a list recspace))))
                  (word a0)))
           (word x)))" 
  by (rule typedef_helper,import word_base word_TY_DEF)

lemmas word_TY_DEF = typedef_hol2hol4 [OF type_definition_word]

consts
  mk_word :: "'a list recspace => 'a word" 
  dest_word :: "'a word => 'a list recspace" 

specification (dest_word mk_word) word_repfns: "(ALL a::'a word. mk_word (dest_word a) = a) &
(ALL r::'a list recspace.
    (ALL word::'a list recspace => bool.
        (ALL a0::'a list recspace.
            (EX a::'a list. a0 = CONSTR (0::nat) a (%n::nat. BOTTOM)) -->
            word a0) -->
        word r) =
    (dest_word (mk_word r) = r))"
  by (import word_base word_repfns)

consts
  word_base0 :: "'a list => 'a word" 

defs
  word_base0_primdef: "word_base0 == %a. mk_word (CONSTR 0 a (%n. BOTTOM))"

lemma word_base0_def: "word_base0 = (%a. mk_word (CONSTR 0 a (%n. BOTTOM)))"
  by (import word_base word_base0_def)

constdefs
  WORD :: "'a list => 'a word" 
  "WORD == word_base0"

lemma WORD: "WORD = word_base0"
  by (import word_base WORD)

consts
  word_case :: "('a list => 'b) => 'a word => 'b" 

specification (word_case_primdef: word_case) word_case_def: "ALL f a. word_case f (WORD a) = f a"
  by (import word_base word_case_def)

consts
  word_size :: "('a => nat) => 'a word => nat" 

specification (word_size_primdef: word_size) word_size_def: "ALL f a. word_size f (WORD a) = 1 + list_size f a"
  by (import word_base word_size_def)

lemma word_11: "ALL a a'. (WORD a = WORD a') = (a = a')"
  by (import word_base word_11)

lemma word_case_cong: "ALL M M' f.
   M = M' & (ALL a. M' = WORD a --> f a = f' a) -->
   word_case f M = word_case f' M'"
  by (import word_base word_case_cong)

lemma word_nchotomy: "ALL x. EX l. x = WORD l"
  by (import word_base word_nchotomy)

lemma word_Axiom: "ALL f. EX fn. ALL a. fn (WORD a) = f a"
  by (import word_base word_Axiom)

lemma word_induction: "ALL P. (ALL a. P (WORD a)) --> All P"
  by (import word_base word_induction)

lemma word_Ax: "ALL f. EX fn. ALL a. fn (WORD a) = f a"
  by (import word_base word_Ax)

lemma WORD_11: "ALL x xa. (WORD x = WORD xa) = (x = xa)"
  by (import word_base WORD_11)

lemma word_induct: "ALL x. (ALL l. x (WORD l)) --> All x"
  by (import word_base word_induct)

lemma word_cases: "ALL x. EX l. x = WORD l"
  by (import word_base word_cases)

consts
  WORDLEN :: "'a word => nat" 

specification (WORDLEN) WORDLEN_DEF: "ALL l. WORDLEN (WORD l) = length l"
  by (import word_base WORDLEN_DEF)

consts
  PWORDLEN :: "nat => 'a word => bool" 

defs
  PWORDLEN_primdef: "PWORDLEN == %n. GSPEC (%w. (w, WORDLEN w = n))"

lemma PWORDLEN_def: "ALL n. PWORDLEN n = GSPEC (%w. (w, WORDLEN w = n))"
  by (import word_base PWORDLEN_def)

lemma IN_PWORDLEN: "ALL n l. IN (WORD l) (PWORDLEN n) = (length l = n)"
  by (import word_base IN_PWORDLEN)

lemma PWORDLEN: "ALL n w. IN w (PWORDLEN n) = (WORDLEN w = n)"
  by (import word_base PWORDLEN)

lemma PWORDLEN0: "ALL w. IN w (PWORDLEN 0) --> w = WORD []"
  by (import word_base PWORDLEN0)

lemma PWORDLEN1: "ALL x. IN (WORD [x]) (PWORDLEN 1)"
  by (import word_base PWORDLEN1)

consts
  WSEG :: "nat => nat => 'a word => 'a word" 

specification (WSEG) WSEG_DEF: "ALL m k l. WSEG m k (WORD l) = WORD (LASTN m (BUTLASTN k l))"
  by (import word_base WSEG_DEF)

lemma WSEG0: "ALL k w. WSEG 0 k w = WORD []"
  by (import word_base WSEG0)

lemma WSEG_PWORDLEN: "ALL n.
   RES_FORALL (PWORDLEN n)
    (%w. ALL m k. m + k <= n --> IN (WSEG m k w) (PWORDLEN m))"
  by (import word_base WSEG_PWORDLEN)

lemma WSEG_WORDLEN: "ALL x.
   RES_FORALL (PWORDLEN x)
    (%xa. ALL xb xc. xb + xc <= x --> WORDLEN (WSEG xb xc xa) = xb)"
  by (import word_base WSEG_WORDLEN)

lemma WSEG_WORD_LENGTH: "ALL n. RES_FORALL (PWORDLEN n) (%w. WSEG n 0 w = w)"
  by (import word_base WSEG_WORD_LENGTH)

consts
  bit :: "nat => 'a word => 'a" 

specification (bit) BIT_DEF: "ALL k l. bit k (WORD l) = ELL k l"
  by (import word_base BIT_DEF)

lemma BIT0: "ALL x. bit 0 (WORD [x]) = x"
  by (import word_base BIT0)

lemma WSEG_BIT: "(All::(nat => bool) => bool)
 (%n::nat.
     (RES_FORALL::('a word => bool) => ('a word => bool) => bool)
      ((PWORDLEN::nat => 'a word => bool) n)
      (%w::'a word.
          (All::(nat => bool) => bool)
           (%k::nat.
               (op -->::bool => bool => bool)
                ((op <::nat => nat => bool) k n)
                ((op =::'a word => 'a word => bool)
                  ((WSEG::nat => nat => 'a word => 'a word) (1::nat) k w)
                  ((WORD::'a list => 'a word)
                    ((op #::'a => 'a list => 'a list)
                      ((bit::nat => 'a word => 'a) k w) ([]::'a list)))))))"
  by (import word_base WSEG_BIT)

lemma BIT_WSEG: "ALL n.
   RES_FORALL (PWORDLEN n)
    (%w. ALL m k j.
            m + k <= n --> j < m --> bit j (WSEG m k w) = bit (j + k) w)"
  by (import word_base BIT_WSEG)

consts
  MSB :: "'a word => 'a" 

specification (MSB) MSB_DEF: "ALL l. MSB (WORD l) = hd l"
  by (import word_base MSB_DEF)

lemma MSB: "ALL n. RES_FORALL (PWORDLEN n) (%w. 0 < n --> MSB w = bit (PRE n) w)"
  by (import word_base MSB)

consts
  LSB :: "'a word => 'a" 

specification (LSB) LSB_DEF: "ALL l. LSB (WORD l) = last l"
  by (import word_base LSB_DEF)

lemma LSB: "ALL n. RES_FORALL (PWORDLEN n) (%w. 0 < n --> LSB w = bit 0 w)"
  by (import word_base LSB)

consts
  WSPLIT :: "nat => 'a word => 'a word * 'a word" 

specification (WSPLIT) WSPLIT_DEF: "ALL m l. WSPLIT m (WORD l) = (WORD (BUTLASTN m l), WORD (LASTN m l))"
  by (import word_base WSPLIT_DEF)

consts
  WCAT :: "'a word * 'a word => 'a word" 

specification (WCAT) WCAT_DEF: "ALL l1 l2. WCAT (WORD l1, WORD l2) = WORD (l1 @ l2)"
  by (import word_base WCAT_DEF)

lemma WORD_PARTITION: "(op &::bool => bool => bool)
 ((All::(nat => bool) => bool)
   (%n::nat.
       (RES_FORALL::('a word => bool) => ('a word => bool) => bool)
        ((PWORDLEN::nat => 'a word => bool) n)
        (%w::'a word.
            (All::(nat => bool) => bool)
             (%m::nat.
                 (op -->::bool => bool => bool)
                  ((op <=::nat => nat => bool) m n)
                  ((op =::'a word => 'a word => bool)
                    ((WCAT::'a word * 'a word => 'a word)
                      ((WSPLIT::nat => 'a word => 'a word * 'a word) m w))
                    w)))))
 ((All::(nat => bool) => bool)
   (%n::nat.
       (All::(nat => bool) => bool)
        (%m::nat.
            (RES_FORALL::('a word => bool) => ('a word => bool) => bool)
             ((PWORDLEN::nat => 'a word => bool) n)
             (%w1::'a word.
                 (RES_FORALL::('a word => bool)
                              => ('a word => bool) => bool)
                  ((PWORDLEN::nat => 'a word => bool) m)
                  (%w2::'a word.
                      (op =::'a word * 'a word => 'a word * 'a word => bool)
                       ((WSPLIT::nat => 'a word => 'a word * 'a word) m
                         ((WCAT::'a word * 'a word => 'a word)
                           ((Pair::'a word => 'a word => 'a word * 'a word)
                             w1 w2)))
                       ((Pair::'a word => 'a word => 'a word * 'a word) w1
                         w2))))))"
  by (import word_base WORD_PARTITION)

lemma WCAT_ASSOC: "ALL w1 w2 w3. WCAT (w1, WCAT (w2, w3)) = WCAT (WCAT (w1, w2), w3)"
  by (import word_base WCAT_ASSOC)

lemma WCAT0: "ALL w. WCAT (WORD [], w) = w & WCAT (w, WORD []) = w"
  by (import word_base WCAT0)

lemma WCAT_11: "ALL m n.
   RES_FORALL (PWORDLEN m)
    (%wm1. RES_FORALL (PWORDLEN m)
            (%wm2. RES_FORALL (PWORDLEN n)
                    (%wn1. RES_FORALL (PWORDLEN n)
                            (%wn2. (WCAT (wm1, wn1) = WCAT (wm2, wn2)) =
                                   (wm1 = wm2 & wn1 = wn2)))))"
  by (import word_base WCAT_11)

lemma WSPLIT_PWORDLEN: "(All::(nat => bool) => bool)
 (%n::nat.
     (RES_FORALL::('a word => bool) => ('a word => bool) => bool)
      ((PWORDLEN::nat => 'a word => bool) n)
      (%w::'a word.
          (All::(nat => bool) => bool)
           (%m::nat.
               (op -->::bool => bool => bool)
                ((op <=::nat => nat => bool) m n)
                ((op &::bool => bool => bool)
                  ((IN::'a word => ('a word => bool) => bool)
                    ((fst::'a word * 'a word => 'a word)
                      ((WSPLIT::nat => 'a word => 'a word * 'a word) m w))
                    ((PWORDLEN::nat => 'a word => bool)
                      ((op -::nat => nat => nat) n m)))
                  ((IN::'a word => ('a word => bool) => bool)
                    ((snd::'a word * 'a word => 'a word)
                      ((WSPLIT::nat => 'a word => 'a word * 'a word) m w))
                    ((PWORDLEN::nat => 'a word => bool) m))))))"
  by (import word_base WSPLIT_PWORDLEN)

lemma WCAT_PWORDLEN: "ALL n1.
   RES_FORALL (PWORDLEN n1)
    (%w1. ALL n2.
             RES_FORALL (PWORDLEN n2)
              (%w2. IN (WCAT (w1, w2)) (PWORDLEN (n1 + n2))))"
  by (import word_base WCAT_PWORDLEN)

lemma WORDLEN_SUC_WCAT: "ALL n w.
   IN w (PWORDLEN (Suc n)) -->
   RES_EXISTS (PWORDLEN 1)
    (%b. RES_EXISTS (PWORDLEN n) (%w'. w = WCAT (b, w')))"
  by (import word_base WORDLEN_SUC_WCAT)

lemma WSEG_WSEG: "ALL n.
   RES_FORALL (PWORDLEN n)
    (%w. ALL m1 k1 m2 k2.
            m1 + k1 <= n & m2 + k2 <= m1 -->
            WSEG m2 k2 (WSEG m1 k1 w) = WSEG m2 (k1 + k2) w)"
  by (import word_base WSEG_WSEG)

lemma WSPLIT_WSEG: "(All::(nat => bool) => bool)
 (%n::nat.
     (RES_FORALL::('a word => bool) => ('a word => bool) => bool)
      ((PWORDLEN::nat => 'a word => bool) n)
      (%w::'a word.
          (All::(nat => bool) => bool)
           (%k::nat.
               (op -->::bool => bool => bool)
                ((op <=::nat => nat => bool) k n)
                ((op =::'a word * 'a word => 'a word * 'a word => bool)
                  ((WSPLIT::nat => 'a word => 'a word * 'a word) k w)
                  ((Pair::'a word => 'a word => 'a word * 'a word)
                    ((WSEG::nat => nat => 'a word => 'a word)
                      ((op -::nat => nat => nat) n k) k w)
                    ((WSEG::nat => nat => 'a word => 'a word) k (0::nat)
                      w))))))"
  by (import word_base WSPLIT_WSEG)

lemma WSPLIT_WSEG1: "(All::(nat => bool) => bool)
 (%n::nat.
     (RES_FORALL::('a word => bool) => ('a word => bool) => bool)
      ((PWORDLEN::nat => 'a word => bool) n)
      (%w::'a word.
          (All::(nat => bool) => bool)
           (%k::nat.
               (op -->::bool => bool => bool)
                ((op <=::nat => nat => bool) k n)
                ((op =::'a word => 'a word => bool)
                  ((fst::'a word * 'a word => 'a word)
                    ((WSPLIT::nat => 'a word => 'a word * 'a word) k w))
                  ((WSEG::nat => nat => 'a word => 'a word)
                    ((op -::nat => nat => nat) n k) k w)))))"
  by (import word_base WSPLIT_WSEG1)

lemma WSPLIT_WSEG2: "(All::(nat => bool) => bool)
 (%n::nat.
     (RES_FORALL::('a word => bool) => ('a word => bool) => bool)
      ((PWORDLEN::nat => 'a word => bool) n)
      (%w::'a word.
          (All::(nat => bool) => bool)
           (%k::nat.
               (op -->::bool => bool => bool)
                ((op <=::nat => nat => bool) k n)
                ((op =::'a word => 'a word => bool)
                  ((snd::'a word * 'a word => 'a word)
                    ((WSPLIT::nat => 'a word => 'a word * 'a word) k w))
                  ((WSEG::nat => nat => 'a word => 'a word) k (0::nat)
                    w)))))"
  by (import word_base WSPLIT_WSEG2)

lemma WCAT_WSEG_WSEG: "ALL n.
   RES_FORALL (PWORDLEN n)
    (%w. ALL m1 m2 k.
            m1 + (m2 + k) <= n -->
            WCAT (WSEG m2 (m1 + k) w, WSEG m1 k w) = WSEG (m1 + m2) k w)"
  by (import word_base WCAT_WSEG_WSEG)

lemma WORD_SPLIT: "ALL x xa.
   RES_FORALL (PWORDLEN (x + xa)) (%w. w = WCAT (WSEG x xa w, WSEG xa 0 w))"
  by (import word_base WORD_SPLIT)

lemma WORDLEN_SUC_WCAT_WSEG_WSEG: "RES_FORALL (PWORDLEN (Suc n)) (%w. w = WCAT (WSEG 1 n w, WSEG n 0 w))"
  by (import word_base WORDLEN_SUC_WCAT_WSEG_WSEG)

lemma WORDLEN_SUC_WCAT_WSEG_WSEG_RIGHT: "RES_FORALL (PWORDLEN (Suc n)) (%w. w = WCAT (WSEG n 1 w, WSEG 1 0 w))"
  by (import word_base WORDLEN_SUC_WCAT_WSEG_WSEG_RIGHT)

lemma WORDLEN_SUC_WCAT_BIT_WSEG: "ALL n.
   RES_FORALL (PWORDLEN (Suc n)) (%w. w = WCAT (WORD [bit n w], WSEG n 0 w))"
  by (import word_base WORDLEN_SUC_WCAT_BIT_WSEG)

lemma WORDLEN_SUC_WCAT_BIT_WSEG_RIGHT: "ALL n.
   RES_FORALL (PWORDLEN (Suc n)) (%w. w = WCAT (WSEG n 1 w, WORD [bit 0 w]))"
  by (import word_base WORDLEN_SUC_WCAT_BIT_WSEG_RIGHT)

lemma WSEG_WCAT1: "ALL n1 n2.
   RES_FORALL (PWORDLEN n1)
    (%w1. RES_FORALL (PWORDLEN n2) (%w2. WSEG n1 n2 (WCAT (w1, w2)) = w1))"
  by (import word_base WSEG_WCAT1)

lemma WSEG_WCAT2: "ALL n1 n2.
   RES_FORALL (PWORDLEN n1)
    (%w1. RES_FORALL (PWORDLEN n2) (%w2. WSEG n2 0 (WCAT (w1, w2)) = w2))"
  by (import word_base WSEG_WCAT2)

lemma WSEG_SUC: "ALL n.
   RES_FORALL (PWORDLEN n)
    (%w. ALL k m1.
            k + Suc m1 < n -->
            WSEG (Suc m1) k w = WCAT (WSEG 1 (k + m1) w, WSEG m1 k w))"
  by (import word_base WSEG_SUC)

lemma WORD_CONS_WCAT: "ALL x l. WORD (x # l) = WCAT (WORD [x], WORD l)"
  by (import word_base WORD_CONS_WCAT)

lemma WORD_SNOC_WCAT: "ALL l x. WORD (SNOC x l) = WCAT (WORD l, WORD [x])"
  by (import word_base WORD_SNOC_WCAT)

lemma BIT_WCAT_FST: "ALL n1 n2.
   RES_FORALL (PWORDLEN n1)
    (%w1. RES_FORALL (PWORDLEN n2)
           (%w2. ALL k.
                    n2 <= k & k < n1 + n2 -->
                    bit k (WCAT (w1, w2)) = bit (k - n2) w1))"
  by (import word_base BIT_WCAT_FST)

lemma BIT_WCAT_SND: "(All::(nat => bool) => bool)
 (%n1::nat.
     (All::(nat => bool) => bool)
      (%n2::nat.
          (RES_FORALL::('a word => bool) => ('a word => bool) => bool)
           ((PWORDLEN::nat => 'a word => bool) n1)
           (%w1::'a word.
               (RES_FORALL::('a word => bool) => ('a word => bool) => bool)
                ((PWORDLEN::nat => 'a word => bool) n2)
                (%w2::'a word.
                    (All::(nat => bool) => bool)
                     (%k::nat.
                         (op -->::bool => bool => bool)
                          ((op <::nat => nat => bool) k n2)
                          ((op =::'a => 'a => bool)
                            ((bit::nat => 'a word => 'a) k
                              ((WCAT::'a word * 'a word => 'a word)
                                ((Pair::'a word
  => 'a word => 'a word * 'a word)
                                  w1 w2)))
                            ((bit::nat => 'a word => 'a) k w2)))))))"
  by (import word_base BIT_WCAT_SND)

lemma BIT_WCAT1: "ALL n. RES_FORALL (PWORDLEN n) (%w. ALL b. bit n (WCAT (WORD [b], w)) = b)"
  by (import word_base BIT_WCAT1)

lemma WSEG_WCAT_WSEG1: "ALL n1 n2.
   RES_FORALL (PWORDLEN n1)
    (%w1. RES_FORALL (PWORDLEN n2)
           (%w2. ALL m k.
                    m <= n1 & n2 <= k -->
                    WSEG m k (WCAT (w1, w2)) = WSEG m (k - n2) w1))"
  by (import word_base WSEG_WCAT_WSEG1)

lemma WSEG_WCAT_WSEG2: "ALL n1 n2.
   RES_FORALL (PWORDLEN n1)
    (%w1. RES_FORALL (PWORDLEN n2)
           (%w2. ALL m k.
                    m + k <= n2 --> WSEG m k (WCAT (w1, w2)) = WSEG m k w2))"
  by (import word_base WSEG_WCAT_WSEG2)

lemma WSEG_WCAT_WSEG: "ALL n1 n2.
   RES_FORALL (PWORDLEN n1)
    (%w1. RES_FORALL (PWORDLEN n2)
           (%w2. ALL m k.
                    m + k <= n1 + n2 & k < n2 & n2 <= m + k -->
                    WSEG m k (WCAT (w1, w2)) =
                    WCAT (WSEG (m + k - n2) 0 w1, WSEG (n2 - k) k w2)))"
  by (import word_base WSEG_WCAT_WSEG)

lemma BIT_EQ_IMP_WORD_EQ: "(All::(nat => bool) => bool)
 (%n::nat.
     (RES_FORALL::('a word => bool) => ('a word => bool) => bool)
      ((PWORDLEN::nat => 'a word => bool) n)
      (%w1::'a word.
          (RES_FORALL::('a word => bool) => ('a word => bool) => bool)
           ((PWORDLEN::nat => 'a word => bool) n)
           (%w2::'a word.
               (op -->::bool => bool => bool)
                ((All::(nat => bool) => bool)
                  (%k::nat.
                      (op -->::bool => bool => bool)
                       ((op <::nat => nat => bool) k n)
                       ((op =::'a => 'a => bool)
                         ((bit::nat => 'a word => 'a) k w1)
                         ((bit::nat => 'a word => 'a) k w2))))
                ((op =::'a word => 'a word => bool) w1 w2))))"
  by (import word_base BIT_EQ_IMP_WORD_EQ)

;end_setup

;setup_theory word_num

constdefs
  LVAL :: "('a => nat) => nat => 'a list => nat" 
  "LVAL == %f b. foldl (%e x. b * e + f x) 0"

lemma LVAL_DEF: "ALL f b l. LVAL f b l = foldl (%e x. b * e + f x) 0 l"
  by (import word_num LVAL_DEF)

consts
  NVAL :: "('a => nat) => nat => 'a word => nat" 

specification (NVAL) NVAL_DEF: "ALL f b l. NVAL f b (WORD l) = LVAL f b l"
  by (import word_num NVAL_DEF)

lemma LVAL: "(ALL (x::'a => nat) xa::nat. LVAL x xa [] = (0::nat)) &
(ALL (x::'a list) (xa::'a => nat) (xb::nat) xc::'a.
    LVAL xa xb (xc # x) = xa xc * xb ^ length x + LVAL xa xb x)"
  by (import word_num LVAL)

lemma LVAL_SNOC: "ALL l h f b. LVAL f b (SNOC h l) = LVAL f b l * b + f h"
  by (import word_num LVAL_SNOC)

lemma LVAL_MAX: "ALL l f b. (ALL x. f x < b) --> LVAL f b l < b ^ length l"
  by (import word_num LVAL_MAX)

lemma NVAL_MAX: "ALL f b.
   (ALL x. f x < b) -->
   (ALL n. RES_FORALL (PWORDLEN n) (%w. NVAL f b w < b ^ n))"
  by (import word_num NVAL_MAX)

lemma NVAL0: "ALL x xa. NVAL x xa (WORD []) = 0"
  by (import word_num NVAL0)

lemma NVAL1: "ALL x xa xb. NVAL x xa (WORD [xb]) = x xb"
  by (import word_num NVAL1)

lemma NVAL_WORDLEN_0: "RES_FORALL (PWORDLEN 0) (%w. ALL fv r. NVAL fv r w = 0)"
  by (import word_num NVAL_WORDLEN_0)

lemma NVAL_WCAT1: "ALL w f b x. NVAL f b (WCAT (w, WORD [x])) = NVAL f b w * b + f x"
  by (import word_num NVAL_WCAT1)

lemma NVAL_WCAT2: "ALL n.
   RES_FORALL (PWORDLEN n)
    (%w. ALL f b x.
            NVAL f b (WCAT (WORD [x], w)) = f x * b ^ n + NVAL f b w)"
  by (import word_num NVAL_WCAT2)

lemma NVAL_WCAT: "ALL n m.
   RES_FORALL (PWORDLEN n)
    (%w1. RES_FORALL (PWORDLEN m)
           (%w2. ALL f b.
                    NVAL f b (WCAT (w1, w2)) =
                    NVAL f b w1 * b ^ m + NVAL f b w2))"
  by (import word_num NVAL_WCAT)

consts
  NLIST :: "nat => (nat => 'a) => nat => nat => 'a list" 

specification (NLIST) NLIST_DEF: "(ALL (frep::nat => 'a) (b::nat) m::nat. NLIST (0::nat) frep b m = []) &
(ALL (n::nat) (frep::nat => 'a) (b::nat) m::nat.
    NLIST (Suc n) frep b m =
    SNOC (frep (m mod b)) (NLIST n frep b (m div b)))"
  by (import word_num NLIST_DEF)

constdefs
  NWORD :: "nat => (nat => 'a) => nat => nat => 'a word" 
  "NWORD == %n frep b m. WORD (NLIST n frep b m)"

lemma NWORD_DEF: "ALL n frep b m. NWORD n frep b m = WORD (NLIST n frep b m)"
  by (import word_num NWORD_DEF)

lemma NWORD_LENGTH: "ALL x xa xb xc. WORDLEN (NWORD x xa xb xc) = x"
  by (import word_num NWORD_LENGTH)

lemma NWORD_PWORDLEN: "ALL x xa xb xc. IN (NWORD x xa xb xc) (PWORDLEN x)"
  by (import word_num NWORD_PWORDLEN)

;end_setup

;setup_theory word_bitop

consts
  PBITOP :: "('a word => 'b word) => bool" 

defs
  PBITOP_primdef: "PBITOP ==
GSPEC
 (%oper.
     (oper,
      ALL n.
         RES_FORALL (PWORDLEN n)
          (%w. IN (oper w) (PWORDLEN n) &
               (ALL m k.
                   m + k <= n --> oper (WSEG m k w) = WSEG m k (oper w)))))"

lemma PBITOP_def: "PBITOP =
GSPEC
 (%oper.
     (oper,
      ALL n.
         RES_FORALL (PWORDLEN n)
          (%w. IN (oper w) (PWORDLEN n) &
               (ALL m k.
                   m + k <= n --> oper (WSEG m k w) = WSEG m k (oper w)))))"
  by (import word_bitop PBITOP_def)

lemma IN_PBITOP: "ALL oper.
   IN oper PBITOP =
   (ALL n.
       RES_FORALL (PWORDLEN n)
        (%w. IN (oper w) (PWORDLEN n) &
             (ALL m k.
                 m + k <= n --> oper (WSEG m k w) = WSEG m k (oper w))))"
  by (import word_bitop IN_PBITOP)

lemma PBITOP_PWORDLEN: "RES_FORALL PBITOP
 (%oper. ALL n. RES_FORALL (PWORDLEN n) (%w. IN (oper w) (PWORDLEN n)))"
  by (import word_bitop PBITOP_PWORDLEN)

lemma PBITOP_WSEG: "RES_FORALL PBITOP
 (%oper.
     ALL n.
        RES_FORALL (PWORDLEN n)
         (%w. ALL m k.
                 m + k <= n --> oper (WSEG m k w) = WSEG m k (oper w)))"
  by (import word_bitop PBITOP_WSEG)

lemma PBITOP_BIT: "(RES_FORALL::(('a word => 'b word) => bool)
             => (('a word => 'b word) => bool) => bool)
 (PBITOP::('a word => 'b word) => bool)
 (%oper::'a word => 'b word.
     (All::(nat => bool) => bool)
      (%n::nat.
          (RES_FORALL::('a word => bool) => ('a word => bool) => bool)
           ((PWORDLEN::nat => 'a word => bool) n)
           (%w::'a word.
               (All::(nat => bool) => bool)
                (%k::nat.
                    (op -->::bool => bool => bool)
                     ((op <::nat => nat => bool) k n)
                     ((op =::'b word => 'b word => bool)
                       (oper
                         ((WORD::'a list => 'a word)
                           ((op #::'a => 'a list => 'a list)
                             ((bit::nat => 'a word => 'a) k w)
                             ([]::'a list))))
                       ((WORD::'b list => 'b word)
                         ((op #::'b => 'b list => 'b list)
                           ((bit::nat => 'b word => 'b) k (oper w))
                           ([]::'b list))))))))"
  by (import word_bitop PBITOP_BIT)

consts
  PBITBOP :: "('a word => 'b word => 'c word) => bool" 

defs
  PBITBOP_primdef: "PBITBOP ==
GSPEC
 (%oper.
     (oper,
      ALL n.
         RES_FORALL (PWORDLEN n)
          (%w1. RES_FORALL (PWORDLEN n)
                 (%w2. IN (oper w1 w2) (PWORDLEN n) &
                       (ALL m k.
                           m + k <= n -->
                           oper (WSEG m k w1) (WSEG m k w2) =
                           WSEG m k (oper w1 w2))))))"

lemma PBITBOP_def: "PBITBOP =
GSPEC
 (%oper.
     (oper,
      ALL n.
         RES_FORALL (PWORDLEN n)
          (%w1. RES_FORALL (PWORDLEN n)
                 (%w2. IN (oper w1 w2) (PWORDLEN n) &
                       (ALL m k.
                           m + k <= n -->
                           oper (WSEG m k w1) (WSEG m k w2) =
                           WSEG m k (oper w1 w2))))))"
  by (import word_bitop PBITBOP_def)

lemma IN_PBITBOP: "ALL oper.
   IN oper PBITBOP =
   (ALL n.
       RES_FORALL (PWORDLEN n)
        (%w1. RES_FORALL (PWORDLEN n)
               (%w2. IN (oper w1 w2) (PWORDLEN n) &
                     (ALL m k.
                         m + k <= n -->
                         oper (WSEG m k w1) (WSEG m k w2) =
                         WSEG m k (oper w1 w2)))))"
  by (import word_bitop IN_PBITBOP)

lemma PBITBOP_PWORDLEN: "RES_FORALL PBITBOP
 (%oper.
     ALL n.
        RES_FORALL (PWORDLEN n)
         (%w1. RES_FORALL (PWORDLEN n) (%w2. IN (oper w1 w2) (PWORDLEN n))))"
  by (import word_bitop PBITBOP_PWORDLEN)

lemma PBITBOP_WSEG: "RES_FORALL PBITBOP
 (%oper.
     ALL n.
        RES_FORALL (PWORDLEN n)
         (%w1. RES_FORALL (PWORDLEN n)
                (%w2. ALL m k.
                         m + k <= n -->
                         oper (WSEG m k w1) (WSEG m k w2) =
                         WSEG m k (oper w1 w2))))"
  by (import word_bitop PBITBOP_WSEG)

lemma PBITBOP_EXISTS: "ALL f. EX x. ALL l1 l2. x (WORD l1) (WORD l2) = WORD (map2 f l1 l2)"
  by (import word_bitop PBITBOP_EXISTS)

consts
  WMAP :: "('a => 'b) => 'a word => 'b word" 

specification (WMAP) WMAP_DEF: "ALL f l. WMAP f (WORD l) = WORD (map f l)"
  by (import word_bitop WMAP_DEF)

lemma WMAP_PWORDLEN: "RES_FORALL (PWORDLEN n) (%w. ALL f. IN (WMAP f w) (PWORDLEN n))"
  by (import word_bitop WMAP_PWORDLEN)

lemma WMAP_0: "ALL x. WMAP x (WORD []) = WORD []"
  by (import word_bitop WMAP_0)

lemma WMAP_BIT: "(All::(nat => bool) => bool)
 (%n::nat.
     (RES_FORALL::('a word => bool) => ('a word => bool) => bool)
      ((PWORDLEN::nat => 'a word => bool) n)
      (%w::'a word.
          (All::(nat => bool) => bool)
           (%k::nat.
               (op -->::bool => bool => bool)
                ((op <::nat => nat => bool) k n)
                ((All::(('a => 'b) => bool) => bool)
                  (%f::'a => 'b.
                      (op =::'b => 'b => bool)
                       ((bit::nat => 'b word => 'b) k
                         ((WMAP::('a => 'b) => 'a word => 'b word) f w))
                       (f ((bit::nat => 'a word => 'a) k w)))))))"
  by (import word_bitop WMAP_BIT)

lemma WMAP_WSEG: "ALL n.
   RES_FORALL (PWORDLEN n)
    (%w. ALL m k.
            m + k <= n -->
            (ALL f. WMAP f (WSEG m k w) = WSEG m k (WMAP f w)))"
  by (import word_bitop WMAP_WSEG)

lemma WMAP_PBITOP: "ALL f. IN (WMAP f) PBITOP"
  by (import word_bitop WMAP_PBITOP)

lemma WMAP_WCAT: "ALL w1 w2 f. WMAP f (WCAT (w1, w2)) = WCAT (WMAP f w1, WMAP f w2)"
  by (import word_bitop WMAP_WCAT)

lemma WMAP_o: "ALL w f g. WMAP g (WMAP f w) = WMAP (g o f) w"
  by (import word_bitop WMAP_o)

consts
  FORALLBITS :: "('a => bool) => 'a word => bool" 

specification (FORALLBITS) FORALLBITS_DEF: "ALL P l. FORALLBITS P (WORD l) = list_all P l"
  by (import word_bitop FORALLBITS_DEF)

lemma FORALLBITS: "(All::(nat => bool) => bool)
 (%n::nat.
     (RES_FORALL::('a word => bool) => ('a word => bool) => bool)
      ((PWORDLEN::nat => 'a word => bool) n)
      (%w::'a word.
          (All::(('a => bool) => bool) => bool)
           (%P::'a => bool.
               (op =::bool => bool => bool)
                ((FORALLBITS::('a => bool) => 'a word => bool) P w)
                ((All::(nat => bool) => bool)
                  (%k::nat.
                      (op -->::bool => bool => bool)
                       ((op <::nat => nat => bool) k n)
                       (P ((bit::nat => 'a word => 'a) k w)))))))"
  by (import word_bitop FORALLBITS)

lemma FORALLBITS_WSEG: "ALL n.
   RES_FORALL (PWORDLEN n)
    (%w. ALL P.
            FORALLBITS P w -->
            (ALL m k. m + k <= n --> FORALLBITS P (WSEG m k w)))"
  by (import word_bitop FORALLBITS_WSEG)

lemma FORALLBITS_WCAT: "ALL w1 w2 P.
   FORALLBITS P (WCAT (w1, w2)) = (FORALLBITS P w1 & FORALLBITS P w2)"
  by (import word_bitop FORALLBITS_WCAT)

consts
  EXISTSABIT :: "('a => bool) => 'a word => bool" 

specification (EXISTSABIT) EXISTSABIT_DEF: "ALL P l. EXISTSABIT P (WORD l) = list_exists P l"
  by (import word_bitop EXISTSABIT_DEF)

lemma NOT_EXISTSABIT: "ALL P w. (~ EXISTSABIT P w) = FORALLBITS (Not o P) w"
  by (import word_bitop NOT_EXISTSABIT)

lemma NOT_FORALLBITS: "ALL P w. (~ FORALLBITS P w) = EXISTSABIT (Not o P) w"
  by (import word_bitop NOT_FORALLBITS)

lemma EXISTSABIT: "(All::(nat => bool) => bool)
 (%n::nat.
     (RES_FORALL::('a word => bool) => ('a word => bool) => bool)
      ((PWORDLEN::nat => 'a word => bool) n)
      (%w::'a word.
          (All::(('a => bool) => bool) => bool)
           (%P::'a => bool.
               (op =::bool => bool => bool)
                ((EXISTSABIT::('a => bool) => 'a word => bool) P w)
                ((Ex::(nat => bool) => bool)
                  (%k::nat.
                      (op &::bool => bool => bool)
                       ((op <::nat => nat => bool) k n)
                       (P ((bit::nat => 'a word => 'a) k w)))))))"
  by (import word_bitop EXISTSABIT)

lemma EXISTSABIT_WSEG: "ALL n.
   RES_FORALL (PWORDLEN n)
    (%w. ALL m k.
            m + k <= n -->
            (ALL P. EXISTSABIT P (WSEG m k w) --> EXISTSABIT P w))"
  by (import word_bitop EXISTSABIT_WSEG)

lemma EXISTSABIT_WCAT: "ALL w1 w2 P.
   EXISTSABIT P (WCAT (w1, w2)) = (EXISTSABIT P w1 | EXISTSABIT P w2)"
  by (import word_bitop EXISTSABIT_WCAT)

constdefs
  SHR :: "bool => 'a => 'a word => 'a word * 'a" 
  "SHR ==
%f b w.
   (WCAT
     (if f then WSEG 1 (PRE (WORDLEN w)) w else WORD [b],
      WSEG (PRE (WORDLEN w)) 1 w),
    bit 0 w)"

lemma SHR_DEF: "ALL f b w.
   SHR f b w =
   (WCAT
     (if f then WSEG 1 (PRE (WORDLEN w)) w else WORD [b],
      WSEG (PRE (WORDLEN w)) 1 w),
    bit 0 w)"
  by (import word_bitop SHR_DEF)

constdefs
  SHL :: "bool => 'a word => 'a => 'a * 'a word" 
  "SHL ==
%f w b.
   (bit (PRE (WORDLEN w)) w,
    WCAT (WSEG (PRE (WORDLEN w)) 0 w, if f then WSEG 1 0 w else WORD [b]))"

lemma SHL_DEF: "ALL f w b.
   SHL f w b =
   (bit (PRE (WORDLEN w)) w,
    WCAT (WSEG (PRE (WORDLEN w)) 0 w, if f then WSEG 1 0 w else WORD [b]))"
  by (import word_bitop SHL_DEF)

lemma SHR_WSEG: "ALL n.
   RES_FORALL (PWORDLEN n)
    (%w. ALL m k.
            m + k <= n -->
            0 < m -->
            (ALL f b.
                SHR f b (WSEG m k w) =
                (if f
                 then WCAT (WSEG 1 (k + (m - 1)) w, WSEG (m - 1) (k + 1) w)
                 else WCAT (WORD [b], WSEG (m - 1) (k + 1) w),
                 bit k w)))"
  by (import word_bitop SHR_WSEG)

lemma SHR_WSEG_1F: "ALL n.
   RES_FORALL (PWORDLEN n)
    (%w. ALL b m k.
            m + k <= n -->
            0 < m -->
            SHR False b (WSEG m k w) =
            (WCAT (WORD [b], WSEG (m - 1) (k + 1) w), bit k w))"
  by (import word_bitop SHR_WSEG_1F)

lemma SHR_WSEG_NF: "ALL n.
   RES_FORALL (PWORDLEN n)
    (%w. ALL m k.
            m + k < n -->
            0 < m -->
            SHR False (bit (m + k) w) (WSEG m k w) =
            (WSEG m (k + 1) w, bit k w))"
  by (import word_bitop SHR_WSEG_NF)

lemma SHL_WSEG: "ALL n.
   RES_FORALL (PWORDLEN n)
    (%w. ALL m k.
            m + k <= n -->
            0 < m -->
            (ALL f b.
                SHL f (WSEG m k w) b =
                (bit (k + (m - 1)) w,
                 if f then WCAT (WSEG (m - 1) k w, WSEG 1 k w)
                 else WCAT (WSEG (m - 1) k w, WORD [b]))))"
  by (import word_bitop SHL_WSEG)

lemma SHL_WSEG_1F: "ALL n.
   RES_FORALL (PWORDLEN n)
    (%w. ALL b m k.
            m + k <= n -->
            0 < m -->
            SHL False (WSEG m k w) b =
            (bit (k + (m - 1)) w, WCAT (WSEG (m - 1) k w, WORD [b])))"
  by (import word_bitop SHL_WSEG_1F)

lemma SHL_WSEG_NF: "ALL n.
   RES_FORALL (PWORDLEN n)
    (%w. ALL m k.
            m + k <= n -->
            0 < m -->
            0 < k -->
            SHL False (WSEG m k w) (bit (k - 1) w) =
            (bit (k + (m - 1)) w, WSEG m (k - 1) w))"
  by (import word_bitop SHL_WSEG_NF)

lemma WSEG_SHL: "ALL n.
   RES_FORALL (PWORDLEN (Suc n))
    (%w. ALL m k.
            0 < k & m + k <= Suc n -->
            (ALL b. WSEG m k (snd (SHL f w b)) = WSEG m (k - 1) w))"
  by (import word_bitop WSEG_SHL)

lemma WSEG_SHL_0: "ALL n.
   RES_FORALL (PWORDLEN (Suc n))
    (%w. ALL m b.
            0 < m & m <= Suc n -->
            WSEG m 0 (snd (SHL f w b)) =
            WCAT (WSEG (m - 1) 0 w, if f then WSEG 1 0 w else WORD [b]))"
  by (import word_bitop WSEG_SHL_0)

;end_setup

;setup_theory bword_num

constdefs
  BV :: "bool => nat" 
  "BV == %b. if b then Suc 0 else 0"

lemma BV_DEF: "ALL b. BV b = (if b then Suc 0 else 0)"
  by (import bword_num BV_DEF)

consts
  BNVAL :: "bool word => nat" 

specification (BNVAL) BNVAL_DEF: "ALL l. BNVAL (WORD l) = LVAL BV 2 l"
  by (import bword_num BNVAL_DEF)

lemma BV_LESS_2: "ALL x. BV x < 2"
  by (import bword_num BV_LESS_2)

lemma BNVAL_NVAL: "ALL w. BNVAL w = NVAL BV 2 w"
  by (import bword_num BNVAL_NVAL)

lemma BNVAL0: "BNVAL (WORD []) = 0"
  by (import bword_num BNVAL0)

lemma BNVAL_11: "ALL w1 w2. WORDLEN w1 = WORDLEN w2 --> BNVAL w1 = BNVAL w2 --> w1 = w2"
  by (import bword_num BNVAL_11)

lemma BNVAL_ONTO: "ALL w. Ex (op = (BNVAL w))"
  by (import bword_num BNVAL_ONTO)

lemma BNVAL_MAX: "ALL n. RES_FORALL (PWORDLEN n) (%w. BNVAL w < 2 ^ n)"
  by (import bword_num BNVAL_MAX)

lemma BNVAL_WCAT1: "ALL n.
   RES_FORALL (PWORDLEN n)
    (%w. ALL x. BNVAL (WCAT (w, WORD [x])) = BNVAL w * 2 + BV x)"
  by (import bword_num BNVAL_WCAT1)

lemma BNVAL_WCAT2: "ALL n.
   RES_FORALL (PWORDLEN n)
    (%w. ALL x. BNVAL (WCAT (WORD [x], w)) = BV x * 2 ^ n + BNVAL w)"
  by (import bword_num BNVAL_WCAT2)

lemma BNVAL_WCAT: "ALL n m.
   RES_FORALL (PWORDLEN n)
    (%w1. RES_FORALL (PWORDLEN m)
           (%w2. BNVAL (WCAT (w1, w2)) = BNVAL w1 * 2 ^ m + BNVAL w2))"
  by (import bword_num BNVAL_WCAT)

constdefs
  VB :: "nat => bool" 
  "VB == %n. n mod 2 ~= 0"

lemma VB_DEF: "ALL n. VB n = (n mod 2 ~= 0)"
  by (import bword_num VB_DEF)

constdefs
  NBWORD :: "nat => nat => bool word" 
  "NBWORD == %n m. WORD (NLIST n VB 2 m)"

lemma NBWORD_DEF: "ALL n m. NBWORD n m = WORD (NLIST n VB 2 m)"
  by (import bword_num NBWORD_DEF)

lemma NBWORD0: "ALL x. NBWORD 0 x = WORD []"
  by (import bword_num NBWORD0)

lemma WORDLEN_NBWORD: "ALL x xa. WORDLEN (NBWORD x xa) = x"
  by (import bword_num WORDLEN_NBWORD)

lemma PWORDLEN_NBWORD: "ALL x xa. IN (NBWORD x xa) (PWORDLEN x)"
  by (import bword_num PWORDLEN_NBWORD)

lemma NBWORD_SUC: "ALL n m. NBWORD (Suc n) m = WCAT (NBWORD n (m div 2), WORD [VB (m mod 2)])"
  by (import bword_num NBWORD_SUC)

lemma VB_BV: "ALL x. VB (BV x) = x"
  by (import bword_num VB_BV)

lemma BV_VB: "(All::(nat => bool) => bool)
 (%x::nat.
     (op -->::bool => bool => bool)
      ((op <::nat => nat => bool) x
        ((number_of::bin => nat)
          ((op BIT::bin => bool => bin)
            ((op BIT::bin => bool => bin) (bin.Pls::bin) (True::bool))
            (False::bool))))
      ((op =::nat => nat => bool) ((BV::bool => nat) ((VB::nat => bool) x))
        x))"
  by (import bword_num BV_VB)

lemma NBWORD_BNVAL: "ALL n. RES_FORALL (PWORDLEN n) (%w. NBWORD n (BNVAL w) = w)"
  by (import bword_num NBWORD_BNVAL)

lemma BNVAL_NBWORD: "ALL n m. m < 2 ^ n --> BNVAL (NBWORD n m) = m"
  by (import bword_num BNVAL_NBWORD)

lemma ZERO_WORD_VAL: "RES_FORALL (PWORDLEN n) (%w. (w = NBWORD n 0) = (BNVAL w = 0))"
  by (import bword_num ZERO_WORD_VAL)

lemma WCAT_NBWORD_0: "ALL n1 n2. WCAT (NBWORD n1 0, NBWORD n2 0) = NBWORD (n1 + n2) 0"
  by (import bword_num WCAT_NBWORD_0)

lemma WSPLIT_NBWORD_0: "ALL n m. m <= n --> WSPLIT m (NBWORD n 0) = (NBWORD (n - m) 0, NBWORD m 0)"
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

lemma NBWORD_MOD: "ALL n m. NBWORD n (m mod 2 ^ n) = NBWORD n m"
  by (import bword_num NBWORD_MOD)

lemma WSEG_NBWORD_SUC: "ALL n m. WSEG n 0 (NBWORD (Suc n) m) = NBWORD n m"
  by (import bword_num WSEG_NBWORD_SUC)

lemma NBWORD_SUC_WSEG: "ALL n. RES_FORALL (PWORDLEN (Suc n)) (%w. NBWORD n (BNVAL w) = WSEG n 0 w)"
  by (import bword_num NBWORD_SUC_WSEG)

lemma DOUBL_EQ_SHL: "ALL x.
   0 < x -->
   RES_FORALL (PWORDLEN x)
    (%xa. ALL xb.
             NBWORD x (BNVAL xa + BNVAL xa + BV xb) = snd (SHL False xa xb))"
  by (import bword_num DOUBL_EQ_SHL)

lemma MSB_NBWORD: "ALL n m. bit n (NBWORD (Suc n) m) = VB (m div 2 ^ n mod 2)"
  by (import bword_num MSB_NBWORD)

lemma NBWORD_SPLIT: "ALL n1 n2 m.
   NBWORD (n1 + n2) m = WCAT (NBWORD n1 (m div 2 ^ n2), NBWORD n2 m)"
  by (import bword_num NBWORD_SPLIT)

lemma WSEG_NBWORD: "ALL m k n.
   m + k <= n --> (ALL l. WSEG m k (NBWORD n l) = NBWORD m (l div 2 ^ k))"
  by (import bword_num WSEG_NBWORD)

lemma NBWORD_SUC_FST: "ALL n x. NBWORD (Suc n) x = WCAT (WORD [VB (x div 2 ^ n mod 2)], NBWORD n x)"
  by (import bword_num NBWORD_SUC_FST)

lemma BIT_NBWORD0: "ALL k n. k < n --> bit k (NBWORD n 0) = False"
  by (import bword_num BIT_NBWORD0)

lemma ADD_BNVAL_LEFT: "ALL n.
   RES_FORALL (PWORDLEN (Suc n))
    (%w1. RES_FORALL (PWORDLEN (Suc n))
           (%w2. BNVAL w1 + BNVAL w2 =
                 (BV (bit n w1) + BV (bit n w2)) * 2 ^ n +
                 (BNVAL (WSEG n 0 w1) + BNVAL (WSEG n 0 w2))))"
  by (import bword_num ADD_BNVAL_LEFT)

lemma ADD_BNVAL_RIGHT: "ALL n.
   RES_FORALL (PWORDLEN (Suc n))
    (%w1. RES_FORALL (PWORDLEN (Suc n))
           (%w2. BNVAL w1 + BNVAL w2 =
                 (BNVAL (WSEG n 1 w1) + BNVAL (WSEG n 1 w2)) * 2 +
                 (BV (bit 0 w1) + BV (bit 0 w2))))"
  by (import bword_num ADD_BNVAL_RIGHT)

lemma ADD_BNVAL_SPLIT: "ALL n1 n2.
   RES_FORALL (PWORDLEN (n1 + n2))
    (%w1. RES_FORALL (PWORDLEN (n1 + n2))
           (%w2. BNVAL w1 + BNVAL w2 =
                 (BNVAL (WSEG n1 n2 w1) + BNVAL (WSEG n1 n2 w2)) * 2 ^ n2 +
                 (BNVAL (WSEG n2 0 w1) + BNVAL (WSEG n2 0 w2))))"
  by (import bword_num ADD_BNVAL_SPLIT)

;end_setup

;setup_theory bword_arith

consts
  ACARRY :: "nat => bool word => bool word => bool => bool" 

specification (ACARRY) ACARRY_DEF: "(ALL w1 w2 cin. ACARRY 0 w1 w2 cin = cin) &
(ALL n w1 w2 cin.
    ACARRY (Suc n) w1 w2 cin =
    VB ((BV (bit n w1) + BV (bit n w2) + BV (ACARRY n w1 w2 cin)) div 2))"
  by (import bword_arith ACARRY_DEF)

consts
  ICARRY :: "nat => bool word => bool word => bool => bool" 

specification (ICARRY) ICARRY_DEF: "(ALL w1 w2 cin. ICARRY 0 w1 w2 cin = cin) &
(ALL n w1 w2 cin.
    ICARRY (Suc n) w1 w2 cin =
    (bit n w1 & bit n w2 | (bit n w1 | bit n w2) & ICARRY n w1 w2 cin))"
  by (import bword_arith ICARRY_DEF)

lemma ACARRY_EQ_ICARRY: "ALL n.
   RES_FORALL (PWORDLEN n)
    (%w1. RES_FORALL (PWORDLEN n)
           (%w2. ALL cin k.
                    k <= n --> ACARRY k w1 w2 cin = ICARRY k w1 w2 cin))"
  by (import bword_arith ACARRY_EQ_ICARRY)

lemma BNVAL_LESS_EQ: "ALL n. RES_FORALL (PWORDLEN n) (%w. BNVAL w <= 2 ^ n - 1)"
  by (import bword_arith BNVAL_LESS_EQ)

lemma ADD_BNVAL_LESS_EQ1: "ALL n cin.
   RES_FORALL (PWORDLEN n)
    (%w1. RES_FORALL (PWORDLEN n)
           (%w2. (BNVAL w1 + (BNVAL w2 + BV cin)) div 2 ^ n <= Suc 0))"
  by (import bword_arith ADD_BNVAL_LESS_EQ1)

lemma ADD_BV_BNVAL_DIV_LESS_EQ1: "ALL n x1 x2 cin.
   RES_FORALL (PWORDLEN n)
    (%w1. RES_FORALL (PWORDLEN n)
           (%w2. (BV x1 + BV x2 +
                  (BNVAL w1 + (BNVAL w2 + BV cin)) div 2 ^ n) div
                 2
                 <= 1))"
  by (import bword_arith ADD_BV_BNVAL_DIV_LESS_EQ1)

lemma ADD_BV_BNVAL_LESS_EQ: "ALL n x1 x2 cin.
   RES_FORALL (PWORDLEN n)
    (%w1. RES_FORALL (PWORDLEN n)
           (%w2. BV x1 + BV x2 + (BNVAL w1 + (BNVAL w2 + BV cin))
                 <= Suc (2 ^ Suc n)))"
  by (import bword_arith ADD_BV_BNVAL_LESS_EQ)

lemma ADD_BV_BNVAL_LESS_EQ1: "ALL n x1 x2 cin.
   RES_FORALL (PWORDLEN n)
    (%w1. RES_FORALL (PWORDLEN n)
           (%w2. (BV x1 + BV x2 + (BNVAL w1 + (BNVAL w2 + BV cin))) div
                 2 ^ Suc n
                 <= 1))"
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
                             ((op BIT::bin => bool => bin)
                               ((op BIT::bin => bool => bin) (bin.Pls::bin)
                                 (True::bool))
                               (False::bool)))
                           k)))))))"
  by (import bword_arith ACARRY_EQ_ADD_DIV)

lemma ADD_WORD_SPLIT: "ALL n1 n2.
   RES_FORALL (PWORDLEN (n1 + n2))
    (%w1. RES_FORALL (PWORDLEN (n1 + n2))
           (%w2. ALL cin.
                    NBWORD (n1 + n2) (BNVAL w1 + BNVAL w2 + BV cin) =
                    WCAT
                     (NBWORD n1
                       (BNVAL (WSEG n1 n2 w1) + BNVAL (WSEG n1 n2 w2) +
                        BV (ACARRY n2 w1 w2 cin)),
                      NBWORD n2
                       (BNVAL (WSEG n2 0 w1) + BNVAL (WSEG n2 0 w2) +
                        BV cin))))"
  by (import bword_arith ADD_WORD_SPLIT)

lemma WSEG_NBWORD_ADD: "ALL n.
   RES_FORALL (PWORDLEN n)
    (%w1. RES_FORALL (PWORDLEN n)
           (%w2. ALL m k cin.
                    m + k <= n -->
                    WSEG m k (NBWORD n (BNVAL w1 + BNVAL w2 + BV cin)) =
                    NBWORD m
                     (BNVAL (WSEG m k w1) + BNVAL (WSEG m k w2) +
                      BV (ACARRY k w1 w2 cin))))"
  by (import bword_arith WSEG_NBWORD_ADD)

lemma ADD_NBWORD_EQ0_SPLIT: "ALL n1 n2.
   RES_FORALL (PWORDLEN (n1 + n2))
    (%w1. RES_FORALL (PWORDLEN (n1 + n2))
           (%w2. ALL cin.
                    (NBWORD (n1 + n2) (BNVAL w1 + BNVAL w2 + BV cin) =
                     NBWORD (n1 + n2) 0) =
                    (NBWORD n1
                      (BNVAL (WSEG n1 n2 w1) + BNVAL (WSEG n1 n2 w2) +
                       BV (ACARRY n2 w1 w2 cin)) =
                     NBWORD n1 0 &
                     NBWORD n2
                      (BNVAL (WSEG n2 0 w1) + BNVAL (WSEG n2 0 w2) +
                       BV cin) =
                     NBWORD n2 0)))"
  by (import bword_arith ADD_NBWORD_EQ0_SPLIT)

lemma ACARRY_MSB: "ALL n.
   RES_FORALL (PWORDLEN n)
    (%w1. RES_FORALL (PWORDLEN n)
           (%w2. ALL cin.
                    ACARRY n w1 w2 cin =
                    bit n (NBWORD (Suc n) (BNVAL w1 + BNVAL w2 + BV cin))))"
  by (import bword_arith ACARRY_MSB)

lemma ACARRY_WSEG: "ALL n.
   RES_FORALL (PWORDLEN n)
    (%w1. RES_FORALL (PWORDLEN n)
           (%w2. ALL cin k m.
                    k < m & m <= n -->
                    ACARRY k (WSEG m 0 w1) (WSEG m 0 w2) cin =
                    ACARRY k w1 w2 cin))"
  by (import bword_arith ACARRY_WSEG)

lemma ICARRY_WSEG: "ALL n.
   RES_FORALL (PWORDLEN n)
    (%w1. RES_FORALL (PWORDLEN n)
           (%w2. ALL cin k m.
                    k < m & m <= n -->
                    ICARRY k (WSEG m 0 w1) (WSEG m 0 w2) cin =
                    ICARRY k w1 w2 cin))"
  by (import bword_arith ICARRY_WSEG)

lemma ACARRY_ACARRY_WSEG: "ALL n.
   RES_FORALL (PWORDLEN n)
    (%w1. RES_FORALL (PWORDLEN n)
           (%w2. ALL cin m k1 k2.
                    k1 < m & k2 < n & m + k2 <= n -->
                    ACARRY k1 (WSEG m k2 w1) (WSEG m k2 w2)
                     (ACARRY k2 w1 w2 cin) =
                    ACARRY (k1 + k2) w1 w2 cin))"
  by (import bword_arith ACARRY_ACARRY_WSEG)

;end_setup

;setup_theory bword_bitop

consts
  WNOT :: "bool word => bool word" 

specification (WNOT) WNOT_DEF: "ALL l. WNOT (WORD l) = WORD (map Not l)"
  by (import bword_bitop WNOT_DEF)

lemma PBITOP_WNOT: "IN WNOT PBITOP"
  by (import bword_bitop PBITOP_WNOT)

lemma WNOT_WNOT: "ALL w. WNOT (WNOT w) = w"
  by (import bword_bitop WNOT_WNOT)

lemma WCAT_WNOT: "ALL n1 n2.
   RES_FORALL (PWORDLEN n1)
    (%w1. RES_FORALL (PWORDLEN n2)
           (%w2. WCAT (WNOT w1, WNOT w2) = WNOT (WCAT (w1, w2))))"
  by (import bword_bitop WCAT_WNOT)

consts
  WAND :: "bool word => bool word => bool word" 

specification (WAND) WAND_DEF: "ALL l1 l2. WAND (WORD l1) (WORD l2) = WORD (map2 op & l1 l2)"
  by (import bword_bitop WAND_DEF)

lemma PBITBOP_WAND: "IN WAND PBITBOP"
  by (import bword_bitop PBITBOP_WAND)

consts
  WOR :: "bool word => bool word => bool word" 

specification (WOR) WOR_DEF: "ALL l1 l2. WOR (WORD l1) (WORD l2) = WORD (map2 op | l1 l2)"
  by (import bword_bitop WOR_DEF)

lemma PBITBOP_WOR: "IN WOR PBITBOP"
  by (import bword_bitop PBITBOP_WOR)

consts
  WXOR :: "bool word => bool word => bool word" 

specification (WXOR) WXOR_DEF: "ALL l1 l2. WXOR (WORD l1) (WORD l2) = WORD (map2 (%x y. x ~= y) l1 l2)"
  by (import bword_bitop WXOR_DEF)

lemma PBITBOP_WXOR: "IN WXOR PBITBOP"
  by (import bword_bitop PBITBOP_WXOR)

;end_setup

end

