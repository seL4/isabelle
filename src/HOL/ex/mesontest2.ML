(*  Title:      HOL/ex/mesontest2
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

MORE and MUCH HARDER test data for the MESON proof procedure

Courtesy John Harrison 

WARNING: there are many potential conflicts between variables used below
and constants declared in HOL!
*)

(*All but the fastest are ignored to reduce build time*)
val even_hard_ones = false;

fun prove (s,tac) = prove_goal (the_context ()) s (fn [] => [tac]);

fun prove_hard arg = if even_hard_ones then prove arg else TrueI;

set timing;

context Main.thy;

(* ========================================================================= *)
(* 100 problems selected from the TPTP library                               *)
(* ========================================================================= *)

(*
 * Original timings for John Harrison's MESON_TAC.
 * Timings below on a 600MHz Pentium III (perch)
 * 
 * A few variable names have been primed to avoid clashing with constants.
 *
 * Changed numeric constants e.g. 0, 1, 2... to num0, num1, num2...
 *
 * Here's a list giving typical CPU times, as well as common names and
 * literature references.
 *
 * BOO003-1     34.6    B2 part 1 [McCharen, et al., 1976]; Lemma proved [Overbeek, et al., 1976]; prob2_part1.ver1.in [ANL]
 * BOO004-1     36.7    B2 part 2 [McCharen, et al., 1976]; Lemma proved [Overbeek, et al., 1976]; prob2_part2.ver1 [ANL]
 * BOO005-1     47.4    B3 part 1 [McCharen, et al., 1976]; B5 [McCharen, et al., 1976]; Lemma proved [Overbeek, et al., 1976]; prob3_part1.ver1.in [ANL]
 * BOO006-1     48.4    B3 part 2 [McCharen, et al., 1976]; B6 [McCharen, et al., 1976]; Lemma proved [Overbeek, et al., 1976]; prob3_part2.ver1 [ANL]
 * BOO011-1     19.0    B7 [McCharen, et al., 1976]; prob7.ver1 [ANL]
 * CAT001-3     45.2    C1 [McCharen, et al., 1976]; p1.ver3.in [ANL]
 * CAT003-3     10.5    C3 [McCharen, et al., 1976]; p3.ver3.in [ANL]
 * CAT005-1    480.1    C5 [McCharen, et al., 1976]; p5.ver1.in [ANL]
 * CAT007-1     11.9    C7 [McCharen, et al., 1976]; p7.ver1.in [ANL]
 * CAT018-1     81.3    p18.ver1.in [ANL]
 * COL001-2     16.0    C1 [Wos & McCune, 1988]
 * COL023-1      5.1    [McCune & Wos, 1988]
 * COL032-1     15.8    [McCune & Wos, 1988]
 * COL052-2     13.2    bird4.ver2.in [ANL]
 * COL075-2    116.9    [Jech, 1994]
 * COM001-1      1.7    shortburst [Wilson & Minker, 1976]
 * COM002-1      4.4    burstall [Wilson & Minker, 1976]
 * COM002-2      7.4
 * COM003-2     22.1    [Brushi, 1991]
 * COM004-1     45.1
 * GEO003-1     71.7    T3 [McCharen, et al., 1976]; t3.ver1.in [ANL]
 * GEO017-2     78.8    D4.1 [Quaife, 1989]
 * GEO027-3    181.5    D10.1 [Quaife, 1989]
 * GEO058-2    104.0    R4 [Quaife, 1989]
 * GEO079-1      2.4    GEOMETRY THEOREM [Slagle, 1967]
 * GRP001-1     47.8    CADE-11 Competition 1 [Overbeek, 1990]; G1 [McCharen, et al., 1976]; THEOREM 1 [Lusk & McCune, 1993]; wos10 [Wilson & Minker, 1976]; xsquared.ver1.in [ANL]; [Robinson, 1963]
 * GRP008-1     50.4    Problem 4 [Wos, 1965]; wos4 [Wilson & Minker, 1976]
 * GRP013-1     40.2    Problem 11 [Wos, 1965]; wos11 [Wilson & Minker, 1976]
 * GRP037-3     43.8    Problem 17 [Wos, 1965]; wos17 [Wilson & Minker, 1976]
 * GRP031-2      3.2    ls23 [Lawrence & Starkey, 1974]; ls23 [Wilson & Minker, 1976]
 * GRP034-4      2.5    ls26 [Lawrence & Starkey, 1974]; ls26 [Wilson & Minker, 1976]
 * GRP047-2     11.7    [Veroff, 1992]
 * GRP130-1    170.6    Bennett QG8 [TPTP]; QG8 [Slaney, 1993]
 * GRP156-1     48.7    ax_mono1c [Schulz, 1995]
 * GRP168-1    159.1    p01a [Schulz, 1995]
 * HEN003-3     39.9    HP3 [McCharen, et al., 1976]
 * HEN007-2    125.7    H7 [McCharen, et al., 1976]
 * HEN008-4     62.0    H8 [McCharen, et al., 1976]
 * HEN009-5    136.3    H9 [McCharen, et al., 1976]; hp9.ver3.in [ANL]
 * HEN012-3     48.5    new.ver2.in [ANL]
 * LCL010-1    370.9    EC-73 [McCune & Wos, 1992]; ec_yq.in [OTTER]
 * LCL077-2     51.6    morgan.two.ver1.in [ANL]
 * LCL082-1     14.6    IC-1.1 [Wos, et al., 1990]; IC-65 [McCune & Wos, 1992]; ls2 [SETHEO]; S1 [Pfenning, 1988]
 * LCL111-1    585.6    CADE-11 Competition 6 [Overbeek, 1990]; mv25.in [OTTER]; MV-57 [McCune & Wos, 1992]; mv.in part 2 [OTTER]; ovb6 [SETHEO]; THEOREM 6 [Lusk & McCune, 1993]
 * LCL143-1     10.9    Lattice structure theorem 2 [Bonacina, 1991]
 * LCL182-1    271.6    Problem 2.16 [Whitehead & Russell, 1927]
 * LCL200-1     12.0    Problem 2.46 [Whitehead & Russell, 1927]
 * LCL215-1    214.4    Problem 2.62 [Whitehead & Russell, 1927]; Problem 2.63 [Whitehead & Russell, 1927]
 * LCL230-2      0.2    Pelletier 5 [Pelletier, 1986]
 * LDA003-1     68.5    Problem 3 [Jech, 1993]
 * MSC002-1      9.2    DBABHP [Michie, et al., 1972]; DBABHP [Wilson & Minker, 1976]
 * MSC003-1      3.2    HASPARTS-T1 [Wilson & Minker, 1976]
 * MSC004-1      9.3    HASPARTS-T2 [Wilson & Minker, 1976]
 * MSC005-1      1.8    Problem 5.1 [Plaisted, 1982]
 * MSC006-1     39.0    nonob.lop [SETHEO]
 * NUM001-1     14.0    Chang-Lee-10a [Chang, 1970]; ls28 [Lawrence & Starkey, 1974]; ls28 [Wilson & Minker, 1976]
 * NUM021-1     52.3    ls65 [Lawrence & Starkey, 1974]; ls65 [Wilson & Minker, 1976]
 * NUM024-1     64.6    ls75 [Lawrence & Starkey, 1974]; ls75 [Wilson & Minker, 1976]
 * NUM180-1    621.2    LIM2.1 [Quaife]
 * NUM228-1    575.9    TRECDEF4 cor. [Quaife]
 * PLA002-1     37.4    Problem 5.7 [Plaisted, 1982]
 * PLA006-1      7.2    [Segre & Elkan, 1994]
 * PLA017-1    484.8    [Segre & Elkan, 1994]
 * PLA022-1     19.1    [Segre & Elkan, 1994]
 * PLA022-2     19.7    [Segre & Elkan, 1994]
 * PRV001-1     10.3    PV1 [McCharen, et al., 1976]
 * PRV003-1      3.9    E2 [McCharen, et al., 1976]; v2.lop [SETHEO]
 * PRV005-1      4.3    E4 [McCharen, et al., 1976]; v4.lop [SETHEO]
 * PRV006-1      6.0    E5 [McCharen, et al., 1976]; v5.lop [SETHEO]
 * PRV009-1      2.2    Hoares FIND [Bledsoe, 1977]; Problem 5.5 [Plaisted, 1982]
 * PUZ012-1      3.5    Boxes-of-fruit [Wos, 1988]; Boxes-of-fruit [Wos, et al., 1992]; boxes.ver1.in [ANL]
 * PUZ020-1     56.6    knightknave.in [ANL]
 * PUZ025-1     58.4    Problem 35 [Smullyan, 1978]; tandl35.ver1.in [ANL]
 * PUZ029-1      5.1    pigs.ver1.in [ANL]
 * RNG001-3     82.4    EX6-T? [Wilson & Minker, 1976]; ex6.lop [SETHEO]; Example 6a [Fleisig, et al., 1974]; FEX6T1 [SPRFN]; FEX6T2 [SPRFN]
 * RNG001-5    399.8    Problem 21 [Wos, 1965]; wos21 [Wilson & Minker, 1976]
 * RNG011-5      8.4    CADE-11 Competition Eq-10 [Overbeek, 1990]; PROBLEM 10 [Zhang, 1993]; THEOREM EQ-10 [Lusk & McCune, 1993]
 * RNG023-6      9.1    [Stevens, 1987]
 * RNG028-2      9.3    PROOF III [Anantharaman & Hsiang, 1990]
 * RNG038-2     16.2    Problem 27 [Wos, 1965]; wos27 [Wilson & Minker, 1976]
 * RNG040-2    180.5    Problem 29 [Wos, 1965]; wos29 [Wilson & Minker, 1976]
 * RNG041-1     35.8    Problem 30 [Wos, 1965]; wos30 [Wilson & Minker, 1976]
 * ROB010-1    205.0    Lemma 3.3 [Winker, 1990]; RA2 [Lusk & Wos, 1992]
 * ROB013-1     23.6    Lemma 3.5 [Winker, 1990]
 * ROB016-1     15.2    Corollary 3.7 [Winker, 1990]
 * ROB021-1    230.4    [McCune, 1992]
 * SET005-1    192.2    ls108 [Lawrence & Starkey, 1974]; ls108 [Wilson & Minker, 1976]
 * SET009-1     10.5    ls116 [Lawrence & Starkey, 1974]; ls116 [Wilson & Minker, 1976]
 * SET025-4    694.7    Lemma 10 [Boyer, et al, 1986]
 * SET046-5      2.3    p42.in [ANL]; Pelletier 42 [Pelletier, 1986]
 * SET047-5      3.7    p43.in [ANL]; Pelletier 43 [Pelletier, 1986]
 * SYN034-1      2.8    QW [Michie, et al., 1972]; QW [Wilson & Minker, 1976]
 * SYN071-1      1.9    Pelletier 48 [Pelletier, 1986]
 * SYN349-1     61.7    Ch17N5 [Tammet, 1994]
 * SYN352-1      5.5    Ch18N4 [Tammet, 1994]
 * TOP001-2     61.1    Lemma 1a [Wick & McCune, 1989]
 * TOP002-2      0.4    Lemma 1b [Wick & McCune, 1989]
 * TOP004-1    181.6    Lemma 1d [Wick & McCune, 1989]
 * TOP004-2      9.0    Lemma 1d [Wick & McCune, 1989]
 * TOP005-2    139.8    Lemma 1e [Wick & McCune, 1989]
 *)

(*51194 inferences so far.  Searching to depth 13.  232.9 secs*)
val BOO003_1 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X Y. sum(X::'a,Y,add(X::'a,Y))) & \
\  (\\<forall>X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (\\<forall>Y X Z. sum(X::'a,Y,Z) --> sum(Y::'a,X,Z)) &       \
\  (\\<forall>Y X Z. product(X::'a,Y,Z) --> product(Y::'a,X,Z)) &       \
\  (\\<forall>X. sum(additive_identity::'a,X,X)) &  \
\  (\\<forall>X. sum(X::'a,additive_identity,X)) &  \
\  (\\<forall>X. product(multiplicative_identity::'a,X,X)) &        \
\  (\\<forall>X. product(X::'a,multiplicative_identity,X)) &        \
\  (\\<forall>Y Z X V3 V1 V2 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & product(X::'a,V3,V4) --> sum(V1::'a,V2,V4)) &        \
\  (\\<forall>Y Z V1 V2 X V3 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(X::'a,V3,V4)) &        \
\  (\\<forall>Y Z V3 X V1 V2 V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & product(V3::'a,X,V4) --> sum(V1::'a,V2,V4)) &        \
\  (\\<forall>Y Z V1 V2 V3 X V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(V3::'a,X,V4)) &        \
\  (\\<forall>Y Z X V3 V1 V2 V4. sum(X::'a,Y,V1) & sum(X::'a,Z,V2) & product(Y::'a,Z,V3) & sum(X::'a,V3,V4) --> product(V1::'a,V2,V4)) &    \
\  (\\<forall>Y Z V1 V2 X V3 V4. sum(X::'a,Y,V1) & sum(X::'a,Z,V2) & product(Y::'a,Z,V3) & product(V1::'a,V2,V4) --> sum(X::'a,V3,V4)) &    \
\  (\\<forall>Y Z V3 X V1 V2 V4. sum(Y::'a,X,V1) & sum(Z::'a,X,V2) & product(Y::'a,Z,V3) & sum(V3::'a,X,V4) --> product(V1::'a,V2,V4)) &    \
\  (\\<forall>Y Z V1 V2 V3 X V4. sum(Y::'a,X,V1) & sum(Z::'a,X,V2) & product(Y::'a,Z,V3) & product(V1::'a,V2,V4) --> sum(V3::'a,X,V4)) &    \
\  (\\<forall>X. sum(INVERSE(X),X,multiplicative_identity)) &   \
\  (\\<forall>X. sum(X::'a,INVERSE(X),multiplicative_identity)) &   \
\  (\\<forall>X. product(INVERSE(X),X,additive_identity)) &     \
\  (\\<forall>X. product(X::'a,INVERSE(X),additive_identity)) &     \
\  (\\<forall>X Y U V. sum(X::'a,Y,U) & sum(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (\\<forall>X Y U V. product(X::'a,Y,U) & product(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (\\<forall>X Y W Z. equal(X::'a,Y) & sum(X::'a,W,Z) --> sum(Y::'a,W,Z)) &        \
\  (\\<forall>X W Y Z. equal(X::'a,Y) & sum(W::'a,X,Z) --> sum(W::'a,Y,Z)) &        \
\  (\\<forall>X W Z Y. equal(X::'a,Y) & sum(W::'a,Z,X) --> sum(W::'a,Z,Y)) &        \
\  (\\<forall>X Y W Z. equal(X::'a,Y) & product(X::'a,W,Z) --> product(Y::'a,W,Z)) &        \
\  (\\<forall>X W Y Z. equal(X::'a,Y) & product(W::'a,X,Z) --> product(W::'a,Y,Z)) &        \
\  (\\<forall>X W Z Y. equal(X::'a,Y) & product(W::'a,Z,X) --> product(W::'a,Z,Y)) &        \
\  (\\<forall>X Y W. equal(X::'a,Y) --> equal(add(X::'a,W),add(Y::'a,W))) & \
\  (\\<forall>X W Y. equal(X::'a,Y) --> equal(add(W::'a,X),add(W::'a,Y))) & \
\  (\\<forall>X Y W. equal(X::'a,Y) --> equal(multiply(X::'a,W),multiply(Y::'a,W))) &       \
\  (\\<forall>X W Y. equal(X::'a,Y) --> equal(multiply(W::'a,X),multiply(W::'a,Y))) &       \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(INVERSE(X),INVERSE(Y))) &       \
\  (~product(x::'a,x,x)) --> False",
  meson_tac 1);

(*51194 inferences so far.  Searching to depth 13. 204.6 secs
  Strange\\<forall> The previous problem also has 51194 inferences at depth 13.  They
   must be very similar!*)
val BOO004_1 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X Y. sum(X::'a,Y,add(X::'a,Y))) & \
\  (\\<forall>X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (\\<forall>Y X Z. sum(X::'a,Y,Z) --> sum(Y::'a,X,Z)) &       \
\  (\\<forall>Y X Z. product(X::'a,Y,Z) --> product(Y::'a,X,Z)) &       \
\  (\\<forall>X. sum(additive_identity::'a,X,X)) &  \
\  (\\<forall>X. sum(X::'a,additive_identity,X)) &  \
\  (\\<forall>X. product(multiplicative_identity::'a,X,X)) &        \
\  (\\<forall>X. product(X::'a,multiplicative_identity,X)) &        \
\  (\\<forall>Y Z X V3 V1 V2 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & product(X::'a,V3,V4) --> sum(V1::'a,V2,V4)) &        \
\  (\\<forall>Y Z V1 V2 X V3 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(X::'a,V3,V4)) &        \
\  (\\<forall>Y Z V3 X V1 V2 V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & product(V3::'a,X,V4) --> sum(V1::'a,V2,V4)) &        \
\  (\\<forall>Y Z V1 V2 V3 X V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(V3::'a,X,V4)) &        \
\  (\\<forall>Y Z X V3 V1 V2 V4. sum(X::'a,Y,V1) & sum(X::'a,Z,V2) & product(Y::'a,Z,V3) & sum(X::'a,V3,V4) --> product(V1::'a,V2,V4)) &    \
\  (\\<forall>Y Z V1 V2 X V3 V4. sum(X::'a,Y,V1) & sum(X::'a,Z,V2) & product(Y::'a,Z,V3) & product(V1::'a,V2,V4) --> sum(X::'a,V3,V4)) &    \
\  (\\<forall>Y Z V3 X V1 V2 V4. sum(Y::'a,X,V1) & sum(Z::'a,X,V2) & product(Y::'a,Z,V3) & sum(V3::'a,X,V4) --> product(V1::'a,V2,V4)) &    \
\  (\\<forall>Y Z V1 V2 V3 X V4. sum(Y::'a,X,V1) & sum(Z::'a,X,V2) & product(Y::'a,Z,V3) & product(V1::'a,V2,V4) --> sum(V3::'a,X,V4)) &    \
\  (\\<forall>X. sum(INVERSE(X),X,multiplicative_identity)) &   \
\  (\\<forall>X. sum(X::'a,INVERSE(X),multiplicative_identity)) &   \
\  (\\<forall>X. product(INVERSE(X),X,additive_identity)) &     \
\  (\\<forall>X. product(X::'a,INVERSE(X),additive_identity)) &     \
\  (\\<forall>X Y U V. sum(X::'a,Y,U) & sum(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (\\<forall>X Y U V. product(X::'a,Y,U) & product(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (\\<forall>X Y W Z. equal(X::'a,Y) & sum(X::'a,W,Z) --> sum(Y::'a,W,Z)) &        \
\  (\\<forall>X W Y Z. equal(X::'a,Y) & sum(W::'a,X,Z) --> sum(W::'a,Y,Z)) &        \
\  (\\<forall>X W Z Y. equal(X::'a,Y) & sum(W::'a,Z,X) --> sum(W::'a,Z,Y)) &        \
\  (\\<forall>X Y W Z. equal(X::'a,Y) & product(X::'a,W,Z) --> product(Y::'a,W,Z)) &        \
\  (\\<forall>X W Y Z. equal(X::'a,Y) & product(W::'a,X,Z) --> product(W::'a,Y,Z)) &        \
\  (\\<forall>X W Z Y. equal(X::'a,Y) & product(W::'a,Z,X) --> product(W::'a,Z,Y)) &        \
\  (\\<forall>X Y W. equal(X::'a,Y) --> equal(add(X::'a,W),add(Y::'a,W))) & \
\  (\\<forall>X W Y. equal(X::'a,Y) --> equal(add(W::'a,X),add(W::'a,Y))) & \
\  (\\<forall>X Y W. equal(X::'a,Y) --> equal(multiply(X::'a,W),multiply(Y::'a,W))) &       \
\  (\\<forall>X W Y. equal(X::'a,Y) --> equal(multiply(W::'a,X),multiply(W::'a,Y))) &       \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(INVERSE(X),INVERSE(Y))) &       \
\  (~sum(x::'a,x,x)) --> False",
  meson_tac 1);

(*74799 inferences so far.  Searching to depth 13.  290.0 secs*)
val BOO005_1 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X Y. sum(X::'a,Y,add(X::'a,Y))) & \
\  (\\<forall>X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (\\<forall>Y X Z. sum(X::'a,Y,Z) --> sum(Y::'a,X,Z)) &       \
\  (\\<forall>Y X Z. product(X::'a,Y,Z) --> product(Y::'a,X,Z)) &       \
\  (\\<forall>X. sum(additive_identity::'a,X,X)) &  \
\  (\\<forall>X. sum(X::'a,additive_identity,X)) &  \
\  (\\<forall>X. product(multiplicative_identity::'a,X,X)) &        \
\  (\\<forall>X. product(X::'a,multiplicative_identity,X)) &        \
\  (\\<forall>Y Z X V3 V1 V2 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & product(X::'a,V3,V4) --> sum(V1::'a,V2,V4)) &        \
\  (\\<forall>Y Z V1 V2 X V3 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(X::'a,V3,V4)) &        \
\  (\\<forall>Y Z V3 X V1 V2 V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & product(V3::'a,X,V4) --> sum(V1::'a,V2,V4)) &        \
\  (\\<forall>Y Z V1 V2 V3 X V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(V3::'a,X,V4)) &        \
\  (\\<forall>Y Z X V3 V1 V2 V4. sum(X::'a,Y,V1) & sum(X::'a,Z,V2) & product(Y::'a,Z,V3) & sum(X::'a,V3,V4) --> product(V1::'a,V2,V4)) &    \
\  (\\<forall>Y Z V1 V2 X V3 V4. sum(X::'a,Y,V1) & sum(X::'a,Z,V2) & product(Y::'a,Z,V3) & product(V1::'a,V2,V4) --> sum(X::'a,V3,V4)) &    \
\  (\\<forall>Y Z V3 X V1 V2 V4. sum(Y::'a,X,V1) & sum(Z::'a,X,V2) & product(Y::'a,Z,V3) & sum(V3::'a,X,V4) --> product(V1::'a,V2,V4)) &    \
\  (\\<forall>Y Z V1 V2 V3 X V4. sum(Y::'a,X,V1) & sum(Z::'a,X,V2) & product(Y::'a,Z,V3) & product(V1::'a,V2,V4) --> sum(V3::'a,X,V4)) &    \
\  (\\<forall>X. sum(INVERSE(X),X,multiplicative_identity)) &   \
\  (\\<forall>X. sum(X::'a,INVERSE(X),multiplicative_identity)) &   \
\  (\\<forall>X. product(INVERSE(X),X,additive_identity)) &     \
\  (\\<forall>X. product(X::'a,INVERSE(X),additive_identity)) &     \
\  (\\<forall>X Y U V. sum(X::'a,Y,U) & sum(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (\\<forall>X Y U V. product(X::'a,Y,U) & product(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (\\<forall>X Y W Z. equal(X::'a,Y) & sum(X::'a,W,Z) --> sum(Y::'a,W,Z)) &        \
\  (\\<forall>X W Y Z. equal(X::'a,Y) & sum(W::'a,X,Z) --> sum(W::'a,Y,Z)) &        \
\  (\\<forall>X W Z Y. equal(X::'a,Y) & sum(W::'a,Z,X) --> sum(W::'a,Z,Y)) &        \
\  (\\<forall>X Y W Z. equal(X::'a,Y) & product(X::'a,W,Z) --> product(Y::'a,W,Z)) &        \
\  (\\<forall>X W Y Z. equal(X::'a,Y) & product(W::'a,X,Z) --> product(W::'a,Y,Z)) &        \
\  (\\<forall>X W Z Y. equal(X::'a,Y) & product(W::'a,Z,X) --> product(W::'a,Z,Y)) &        \
\  (\\<forall>X Y W. equal(X::'a,Y) --> equal(add(X::'a,W),add(Y::'a,W))) & \
\  (\\<forall>X W Y. equal(X::'a,Y) --> equal(add(W::'a,X),add(W::'a,Y))) & \
\  (\\<forall>X Y W. equal(X::'a,Y) --> equal(multiply(X::'a,W),multiply(Y::'a,W))) &       \
\  (\\<forall>X W Y. equal(X::'a,Y) --> equal(multiply(W::'a,X),multiply(W::'a,Y))) &       \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(INVERSE(X),INVERSE(Y))) &       \
\  (~sum(x::'a,multiplicative_identity,multiplicative_identity)) --> False",
  meson_tac 1);

(*74799 inferences so far.  Searching to depth 13.  314.6 secs*)
val BOO006_1 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X Y. sum(X::'a,Y,add(X::'a,Y))) & \
\  (\\<forall>X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (\\<forall>Y X Z. sum(X::'a,Y,Z) --> sum(Y::'a,X,Z)) &       \
\  (\\<forall>Y X Z. product(X::'a,Y,Z) --> product(Y::'a,X,Z)) &       \
\  (\\<forall>X. sum(additive_identity::'a,X,X)) &  \
\  (\\<forall>X. sum(X::'a,additive_identity,X)) &  \
\  (\\<forall>X. product(multiplicative_identity::'a,X,X)) &        \
\  (\\<forall>X. product(X::'a,multiplicative_identity,X)) &        \
\  (\\<forall>Y Z X V3 V1 V2 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & product(X::'a,V3,V4) --> sum(V1::'a,V2,V4)) &        \
\  (\\<forall>Y Z V1 V2 X V3 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(X::'a,V3,V4)) &        \
\  (\\<forall>Y Z V3 X V1 V2 V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & product(V3::'a,X,V4) --> sum(V1::'a,V2,V4)) &        \
\  (\\<forall>Y Z V1 V2 V3 X V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(V3::'a,X,V4)) &        \
\  (\\<forall>Y Z X V3 V1 V2 V4. sum(X::'a,Y,V1) & sum(X::'a,Z,V2) & product(Y::'a,Z,V3) & sum(X::'a,V3,V4) --> product(V1::'a,V2,V4)) &    \
\  (\\<forall>Y Z V1 V2 X V3 V4. sum(X::'a,Y,V1) & sum(X::'a,Z,V2) & product(Y::'a,Z,V3) & product(V1::'a,V2,V4) --> sum(X::'a,V3,V4)) &    \
\  (\\<forall>Y Z V3 X V1 V2 V4. sum(Y::'a,X,V1) & sum(Z::'a,X,V2) & product(Y::'a,Z,V3) & sum(V3::'a,X,V4) --> product(V1::'a,V2,V4)) &    \
\  (\\<forall>Y Z V1 V2 V3 X V4. sum(Y::'a,X,V1) & sum(Z::'a,X,V2) & product(Y::'a,Z,V3) & product(V1::'a,V2,V4) --> sum(V3::'a,X,V4)) &    \
\  (\\<forall>X. sum(INVERSE(X),X,multiplicative_identity)) &   \
\  (\\<forall>X. sum(X::'a,INVERSE(X),multiplicative_identity)) &   \
\  (\\<forall>X. product(INVERSE(X),X,additive_identity)) &     \
\  (\\<forall>X. product(X::'a,INVERSE(X),additive_identity)) &     \
\  (\\<forall>X Y U V. sum(X::'a,Y,U) & sum(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (\\<forall>X Y U V. product(X::'a,Y,U) & product(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (\\<forall>X Y W Z. equal(X::'a,Y) & sum(X::'a,W,Z) --> sum(Y::'a,W,Z)) &        \
\  (\\<forall>X W Y Z. equal(X::'a,Y) & sum(W::'a,X,Z) --> sum(W::'a,Y,Z)) &        \
\  (\\<forall>X W Z Y. equal(X::'a,Y) & sum(W::'a,Z,X) --> sum(W::'a,Z,Y)) &        \
\  (\\<forall>X Y W Z. equal(X::'a,Y) & product(X::'a,W,Z) --> product(Y::'a,W,Z)) &        \
\  (\\<forall>X W Y Z. equal(X::'a,Y) & product(W::'a,X,Z) --> product(W::'a,Y,Z)) &        \
\  (\\<forall>X W Z Y. equal(X::'a,Y) & product(W::'a,Z,X) --> product(W::'a,Z,Y)) &        \
\  (\\<forall>X Y W. equal(X::'a,Y) --> equal(add(X::'a,W),add(Y::'a,W))) & \
\  (\\<forall>X W Y. equal(X::'a,Y) --> equal(add(W::'a,X),add(W::'a,Y))) & \
\  (\\<forall>X Y W. equal(X::'a,Y) --> equal(multiply(X::'a,W),multiply(Y::'a,W))) &       \
\  (\\<forall>X W Y. equal(X::'a,Y) --> equal(multiply(W::'a,X),multiply(W::'a,Y))) &       \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(INVERSE(X),INVERSE(Y))) &       \
\  (~product(x::'a,additive_identity,additive_identity)) --> False",
  meson_tac 1);

(*5 inferences so far.  Searching to depth 5.  1.3 secs*)
val BOO011_1 = prove
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X Y. sum(X::'a,Y,add(X::'a,Y))) & \
\  (\\<forall>X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (\\<forall>Y X Z. sum(X::'a,Y,Z) --> sum(Y::'a,X,Z)) &       \
\  (\\<forall>Y X Z. product(X::'a,Y,Z) --> product(Y::'a,X,Z)) &       \
\  (\\<forall>X. sum(additive_identity::'a,X,X)) &  \
\  (\\<forall>X. sum(X::'a,additive_identity,X)) &  \
\  (\\<forall>X. product(multiplicative_identity::'a,X,X)) &        \
\  (\\<forall>X. product(X::'a,multiplicative_identity,X)) &        \
\  (\\<forall>Y Z X V3 V1 V2 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & product(X::'a,V3,V4) --> sum(V1::'a,V2,V4)) &        \
\  (\\<forall>Y Z V1 V2 X V3 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(X::'a,V3,V4)) &        \
\  (\\<forall>Y Z V3 X V1 V2 V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & product(V3::'a,X,V4) --> sum(V1::'a,V2,V4)) &        \
\  (\\<forall>Y Z V1 V2 V3 X V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(V3::'a,X,V4)) &        \
\  (\\<forall>Y Z X V3 V1 V2 V4. sum(X::'a,Y,V1) & sum(X::'a,Z,V2) & product(Y::'a,Z,V3) & sum(X::'a,V3,V4) --> product(V1::'a,V2,V4)) &    \
\  (\\<forall>Y Z V1 V2 X V3 V4. sum(X::'a,Y,V1) & sum(X::'a,Z,V2) & product(Y::'a,Z,V3) & product(V1::'a,V2,V4) --> sum(X::'a,V3,V4)) &    \
\  (\\<forall>Y Z V3 X V1 V2 V4. sum(Y::'a,X,V1) & sum(Z::'a,X,V2) & product(Y::'a,Z,V3) & sum(V3::'a,X,V4) --> product(V1::'a,V2,V4)) &    \
\  (\\<forall>Y Z V1 V2 V3 X V4. sum(Y::'a,X,V1) & sum(Z::'a,X,V2) & product(Y::'a,Z,V3) & product(V1::'a,V2,V4) --> sum(V3::'a,X,V4)) &    \
\  (\\<forall>X. sum(INVERSE(X),X,multiplicative_identity)) &   \
\  (\\<forall>X. sum(X::'a,INVERSE(X),multiplicative_identity)) &   \
\  (\\<forall>X. product(INVERSE(X),X,additive_identity)) &     \
\  (\\<forall>X. product(X::'a,INVERSE(X),additive_identity)) &     \
\  (\\<forall>X Y U V. sum(X::'a,Y,U) & sum(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (\\<forall>X Y U V. product(X::'a,Y,U) & product(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (\\<forall>X Y W Z. equal(X::'a,Y) & sum(X::'a,W,Z) --> sum(Y::'a,W,Z)) &        \
\  (\\<forall>X W Y Z. equal(X::'a,Y) & sum(W::'a,X,Z) --> sum(W::'a,Y,Z)) &        \
\  (\\<forall>X W Z Y. equal(X::'a,Y) & sum(W::'a,Z,X) --> sum(W::'a,Z,Y)) &        \
\  (\\<forall>X Y W Z. equal(X::'a,Y) & product(X::'a,W,Z) --> product(Y::'a,W,Z)) &        \
\  (\\<forall>X W Y Z. equal(X::'a,Y) & product(W::'a,X,Z) --> product(W::'a,Y,Z)) &        \
\  (\\<forall>X W Z Y. equal(X::'a,Y) & product(W::'a,Z,X) --> product(W::'a,Z,Y)) &        \
\  (\\<forall>X Y W. equal(X::'a,Y) --> equal(add(X::'a,W),add(Y::'a,W))) & \
\  (\\<forall>X W Y. equal(X::'a,Y) --> equal(add(W::'a,X),add(W::'a,Y))) & \
\  (\\<forall>X Y W. equal(X::'a,Y) --> equal(multiply(X::'a,W),multiply(Y::'a,W))) &       \
\  (\\<forall>X W Y. equal(X::'a,Y) --> equal(multiply(W::'a,X),multiply(W::'a,Y))) &       \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(INVERSE(X),INVERSE(Y))) &       \
\  (~equal(INVERSE(additive_identity),multiplicative_identity)) --> False",
  meson_tac 1);

(*4007 inferences so far.  Searching to depth 9.  13 secs*)
val CAT001_3 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>Y X. equivalent(X::'a,Y) --> there_exists(X)) &       \
\  (\\<forall>X Y. equivalent(X::'a,Y) --> equal(X::'a,Y)) &    \
\  (\\<forall>X Y. there_exists(X) & equal(X::'a,Y) --> equivalent(X::'a,Y)) &  \
\  (\\<forall>X. there_exists(domain(X)) --> there_exists(X)) & \
\  (\\<forall>X. there_exists(codomain(X)) --> there_exists(X)) &       \
\  (\\<forall>Y X. there_exists(compos(X::'a,Y)) --> there_exists(domain(X))) &    \
\  (\\<forall>X Y. there_exists(compos(X::'a,Y)) --> equal(domain(X),codomain(Y))) &       \
\  (\\<forall>X Y. there_exists(domain(X)) & equal(domain(X),codomain(Y)) --> there_exists(compos(X::'a,Y))) &     \
\  (\\<forall>X Y Z. equal(compos(X::'a,compos(Y::'a,Z)),compos(compos(X::'a,Y),Z))) &  \
\  (\\<forall>X. equal(compos(X::'a,domain(X)),X)) &       \
\  (\\<forall>X. equal(compos(codomain(X),X),X)) &     \
\  (\\<forall>X Y. equivalent(X::'a,Y) --> there_exists(Y)) &       \
\  (\\<forall>X Y. there_exists(X) & there_exists(Y) & equal(X::'a,Y) --> equivalent(X::'a,Y)) &        \
\  (\\<forall>Y X. there_exists(compos(X::'a,Y)) --> there_exists(codomain(X))) &  \
\  (\\<forall>X Y. there_exists(f1(X::'a,Y)) | equal(X::'a,Y)) &       \
\  (\\<forall>X Y. equal(X::'a,f1(X::'a,Y)) | equal(Y::'a,f1(X::'a,Y)) | equal(X::'a,Y)) &        \
\  (\\<forall>X Y. equal(X::'a,f1(X::'a,Y)) & equal(Y::'a,f1(X::'a,Y)) --> equal(X::'a,Y)) &        \
\  (\\<forall>X Y. equal(X::'a,Y) & there_exists(X) --> there_exists(Y)) &  \
\  (\\<forall>X Y Z. equal(X::'a,Y) & equivalent(X::'a,Z) --> equivalent(Y::'a,Z)) &        \
\  (\\<forall>X Z Y. equal(X::'a,Y) & equivalent(Z::'a,X) --> equivalent(Z::'a,Y)) &        \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(domain(X),domain(Y))) & \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(codomain(X),codomain(Y))) &     \
\  (\\<forall>X Y Z. equal(X::'a,Y) --> equal(compos(X::'a,Z),compos(Y::'a,Z))) & \
\  (\\<forall>X Z Y. equal(X::'a,Y) --> equal(compos(Z::'a,X),compos(Z::'a,Y))) & \
\  (\\<forall>A B C. equal(A::'a,B) --> equal(f1(A::'a,C),f1(B::'a,C))) &   \
\  (\\<forall>D F' E. equal(D::'a,E) --> equal(f1(F'::'a,D),f1(F'::'a,E))) &        \
\  (there_exists(compos(a::'a,b))) &       \
\  (\\<forall>Y X Z. equal(compos(compos(a::'a,b),X),Y) & equal(compos(compos(a::'a,b),Z),Y) --> equal(X::'a,Z)) &      \
\  (there_exists(compos(b::'a,h))) &       \
\  (equal(compos(b::'a,h),compos(b::'a,g))) & \
\  (~equal(h::'a,g)) --> False",
  meson_tac 1);

(*245 inferences so far.  Searching to depth 7.  1.0 secs*)
val CAT003_3 = prove
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>Y X. equivalent(X::'a,Y) --> there_exists(X)) &       \
\  (\\<forall>X Y. equivalent(X::'a,Y) --> equal(X::'a,Y)) &    \
\  (\\<forall>X Y. there_exists(X) & equal(X::'a,Y) --> equivalent(X::'a,Y)) &  \
\  (\\<forall>X. there_exists(domain(X)) --> there_exists(X)) & \
\  (\\<forall>X. there_exists(codomain(X)) --> there_exists(X)) &       \
\  (\\<forall>Y X. there_exists(compos(X::'a,Y)) --> there_exists(domain(X))) &    \
\  (\\<forall>X Y. there_exists(compos(X::'a,Y)) --> equal(domain(X),codomain(Y))) &       \
\  (\\<forall>X Y. there_exists(domain(X)) & equal(domain(X),codomain(Y)) --> there_exists(compos(X::'a,Y))) &     \
\  (\\<forall>X Y Z. equal(compos(X::'a,compos(Y::'a,Z)),compos(compos(X::'a,Y),Z))) &  \
\  (\\<forall>X. equal(compos(X::'a,domain(X)),X)) &       \
\  (\\<forall>X. equal(compos(codomain(X),X),X)) &     \
\  (\\<forall>X Y. equivalent(X::'a,Y) --> there_exists(Y)) &       \
\  (\\<forall>X Y. there_exists(X) & there_exists(Y) & equal(X::'a,Y) --> equivalent(X::'a,Y)) &        \
\  (\\<forall>Y X. there_exists(compos(X::'a,Y)) --> there_exists(codomain(X))) &  \
\  (\\<forall>X Y. there_exists(f1(X::'a,Y)) | equal(X::'a,Y)) &       \
\  (\\<forall>X Y. equal(X::'a,f1(X::'a,Y)) | equal(Y::'a,f1(X::'a,Y)) | equal(X::'a,Y)) &        \
\  (\\<forall>X Y. equal(X::'a,f1(X::'a,Y)) & equal(Y::'a,f1(X::'a,Y)) --> equal(X::'a,Y)) &        \
\  (\\<forall>X Y. equal(X::'a,Y) & there_exists(X) --> there_exists(Y)) &  \
\  (\\<forall>X Y Z. equal(X::'a,Y) & equivalent(X::'a,Z) --> equivalent(Y::'a,Z)) &        \
\  (\\<forall>X Z Y. equal(X::'a,Y) & equivalent(Z::'a,X) --> equivalent(Z::'a,Y)) &        \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(domain(X),domain(Y))) & \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(codomain(X),codomain(Y))) &     \
\  (\\<forall>X Y Z. equal(X::'a,Y) --> equal(compos(X::'a,Z),compos(Y::'a,Z))) & \
\  (\\<forall>X Z Y. equal(X::'a,Y) --> equal(compos(Z::'a,X),compos(Z::'a,Y))) & \
\  (\\<forall>A B C. equal(A::'a,B) --> equal(f1(A::'a,C),f1(B::'a,C))) &   \
\  (\\<forall>D F' E. equal(D::'a,E) --> equal(f1(F'::'a,D),f1(F'::'a,E))) &        \
\  (there_exists(compos(a::'a,b))) &       \
\  (\\<forall>Y X Z. equal(compos(X::'a,compos(a::'a,b)),Y) & equal(compos(Z::'a,compos(a::'a,b)),Y) --> equal(X::'a,Z)) &      \
\  (there_exists(h)) &  \
\  (equal(compos(h::'a,a),compos(g::'a,a))) & \
\  (~equal(g::'a,h)) --> False",
  meson_tac 1);

(*54288 inferences so far.  Searching to depth 14.  118.0 secs*)
val CAT005_1 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X Y. defined(X::'a,Y) --> product(X::'a,Y,compos(X::'a,Y))) &        \
\  (\\<forall>Z X Y. product(X::'a,Y,Z) --> defined(X::'a,Y)) & \
\  (\\<forall>X Xy Y Z. product(X::'a,Y,Xy) & defined(Xy::'a,Z) --> defined(Y::'a,Z)) &     \
\  (\\<forall>Y Xy Z X Yz. product(X::'a,Y,Xy) & product(Y::'a,Z,Yz) & defined(Xy::'a,Z) --> defined(X::'a,Yz)) &       \
\  (\\<forall>Xy Y Z X Yz Xyz. product(X::'a,Y,Xy) & product(Xy::'a,Z,Xyz) & product(Y::'a,Z,Yz) --> product(X::'a,Yz,Xyz)) &   \
\  (\\<forall>Z Yz X Y. product(Y::'a,Z,Yz) & defined(X::'a,Yz) --> defined(X::'a,Y)) &     \
\  (\\<forall>Y X Yz Xy Z. product(Y::'a,Z,Yz) & product(X::'a,Y,Xy) & defined(X::'a,Yz) --> defined(Xy::'a,Z)) &       \
\  (\\<forall>Yz X Y Xy Z Xyz. product(Y::'a,Z,Yz) & product(X::'a,Yz,Xyz) & product(X::'a,Y,Xy) --> product(Xy::'a,Z,Xyz)) &   \
\  (\\<forall>Y X Z. defined(X::'a,Y) & defined(Y::'a,Z) & identity_map(Y) --> defined(X::'a,Z)) &  \
\  (\\<forall>X. identity_map(domain(X))) &     \
\  (\\<forall>X. identity_map(codomain(X))) &   \
\  (\\<forall>X. defined(X::'a,domain(X))) &        \
\  (\\<forall>X. defined(codomain(X),X)) &      \
\  (\\<forall>X. product(X::'a,domain(X),X)) &      \
\  (\\<forall>X. product(codomain(X),X,X)) &    \
\  (\\<forall>X Y. defined(X::'a,Y) & identity_map(X) --> product(X::'a,Y,Y)) & \
\  (\\<forall>Y X. defined(X::'a,Y) & identity_map(Y) --> product(X::'a,Y,X)) & \
\  (\\<forall>X Y Z W. product(X::'a,Y,Z) & product(X::'a,Y,W) --> equal(Z::'a,W)) &        \
\  (\\<forall>X Y Z W. equal(X::'a,Y) & product(X::'a,Z,W) --> product(Y::'a,Z,W)) &        \
\  (\\<forall>X Z Y W. equal(X::'a,Y) & product(Z::'a,X,W) --> product(Z::'a,Y,W)) &        \
\  (\\<forall>X Z W Y. equal(X::'a,Y) & product(Z::'a,W,X) --> product(Z::'a,W,Y)) &        \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(domain(X),domain(Y))) & \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(codomain(X),codomain(Y))) &     \
\  (\\<forall>X Y. equal(X::'a,Y) & identity_map(X) --> identity_map(Y)) &  \
\  (\\<forall>X Y Z. equal(X::'a,Y) & defined(X::'a,Z) --> defined(Y::'a,Z)) &      \
\  (\\<forall>X Z Y. equal(X::'a,Y) & defined(Z::'a,X) --> defined(Z::'a,Y)) &      \
\  (\\<forall>X Z Y. equal(X::'a,Y) --> equal(compos(Z::'a,X),compos(Z::'a,Y))) & \
\  (\\<forall>X Y Z. equal(X::'a,Y) --> equal(compos(X::'a,Z),compos(Y::'a,Z))) & \
\  (defined(a::'a,d)) &     \
\  (identity_map(d)) &  \
\  (~equal(domain(a),d)) --> False",
  meson_tac 1);


(*1728 inferences so far.  Searching to depth 10.  5.8 secs*)
val CAT007_1 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X Y. defined(X::'a,Y) --> product(X::'a,Y,compos(X::'a,Y))) &        \
\  (\\<forall>Z X Y. product(X::'a,Y,Z) --> defined(X::'a,Y)) & \
\  (\\<forall>X Xy Y Z. product(X::'a,Y,Xy) & defined(Xy::'a,Z) --> defined(Y::'a,Z)) &     \
\  (\\<forall>Y Xy Z X Yz. product(X::'a,Y,Xy) & product(Y::'a,Z,Yz) & defined(Xy::'a,Z) --> defined(X::'a,Yz)) &       \
\  (\\<forall>Xy Y Z X Yz Xyz. product(X::'a,Y,Xy) & product(Xy::'a,Z,Xyz) & product(Y::'a,Z,Yz) --> product(X::'a,Yz,Xyz)) &   \
\  (\\<forall>Z Yz X Y. product(Y::'a,Z,Yz) & defined(X::'a,Yz) --> defined(X::'a,Y)) &     \
\  (\\<forall>Y X Yz Xy Z. product(Y::'a,Z,Yz) & product(X::'a,Y,Xy) & defined(X::'a,Yz) --> defined(Xy::'a,Z)) &       \
\  (\\<forall>Yz X Y Xy Z Xyz. product(Y::'a,Z,Yz) & product(X::'a,Yz,Xyz) & product(X::'a,Y,Xy) --> product(Xy::'a,Z,Xyz)) &   \
\  (\\<forall>Y X Z. defined(X::'a,Y) & defined(Y::'a,Z) & identity_map(Y) --> defined(X::'a,Z)) &  \
\  (\\<forall>X. identity_map(domain(X))) &     \
\  (\\<forall>X. identity_map(codomain(X))) &   \
\  (\\<forall>X. defined(X::'a,domain(X))) &        \
\  (\\<forall>X. defined(codomain(X),X)) &      \
\  (\\<forall>X. product(X::'a,domain(X),X)) &      \
\  (\\<forall>X. product(codomain(X),X,X)) &    \
\  (\\<forall>X Y. defined(X::'a,Y) & identity_map(X) --> product(X::'a,Y,Y)) & \
\  (\\<forall>Y X. defined(X::'a,Y) & identity_map(Y) --> product(X::'a,Y,X)) & \
\  (\\<forall>X Y Z W. product(X::'a,Y,Z) & product(X::'a,Y,W) --> equal(Z::'a,W)) &        \
\  (\\<forall>X Y Z W. equal(X::'a,Y) & product(X::'a,Z,W) --> product(Y::'a,Z,W)) &        \
\  (\\<forall>X Z Y W. equal(X::'a,Y) & product(Z::'a,X,W) --> product(Z::'a,Y,W)) &        \
\  (\\<forall>X Z W Y. equal(X::'a,Y) & product(Z::'a,W,X) --> product(Z::'a,W,Y)) &        \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(domain(X),domain(Y))) & \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(codomain(X),codomain(Y))) &     \
\  (\\<forall>X Y. equal(X::'a,Y) & identity_map(X) --> identity_map(Y)) &  \
\  (\\<forall>X Y Z. equal(X::'a,Y) & defined(X::'a,Z) --> defined(Y::'a,Z)) &      \
\  (\\<forall>X Z Y. equal(X::'a,Y) & defined(Z::'a,X) --> defined(Z::'a,Y)) &      \
\  (\\<forall>X Z Y. equal(X::'a,Y) --> equal(compos(Z::'a,X),compos(Z::'a,Y))) & \
\  (\\<forall>X Y Z. equal(X::'a,Y) --> equal(compos(X::'a,Z),compos(Y::'a,Z))) & \
\  (equal(domain(a),codomain(b))) &     \
\  (~defined(a::'a,b)) --> False",
  meson_tac 1);

(*82895 inferences so far.  Searching to depth 13.  355 secs*)
val CAT018_1 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X Y. defined(X::'a,Y) --> product(X::'a,Y,compos(X::'a,Y))) &        \
\  (\\<forall>Z X Y. product(X::'a,Y,Z) --> defined(X::'a,Y)) & \
\  (\\<forall>X Xy Y Z. product(X::'a,Y,Xy) & defined(Xy::'a,Z) --> defined(Y::'a,Z)) &     \
\  (\\<forall>Y Xy Z X Yz. product(X::'a,Y,Xy) & product(Y::'a,Z,Yz) & defined(Xy::'a,Z) --> defined(X::'a,Yz)) &       \
\  (\\<forall>Xy Y Z X Yz Xyz. product(X::'a,Y,Xy) & product(Xy::'a,Z,Xyz) & product(Y::'a,Z,Yz) --> product(X::'a,Yz,Xyz)) &   \
\  (\\<forall>Z Yz X Y. product(Y::'a,Z,Yz) & defined(X::'a,Yz) --> defined(X::'a,Y)) &     \
\  (\\<forall>Y X Yz Xy Z. product(Y::'a,Z,Yz) & product(X::'a,Y,Xy) & defined(X::'a,Yz) --> defined(Xy::'a,Z)) &       \
\  (\\<forall>Yz X Y Xy Z Xyz. product(Y::'a,Z,Yz) & product(X::'a,Yz,Xyz) & product(X::'a,Y,Xy) --> product(Xy::'a,Z,Xyz)) &   \
\  (\\<forall>Y X Z. defined(X::'a,Y) & defined(Y::'a,Z) & identity_map(Y) --> defined(X::'a,Z)) &  \
\  (\\<forall>X. identity_map(domain(X))) &     \
\  (\\<forall>X. identity_map(codomain(X))) &   \
\  (\\<forall>X. defined(X::'a,domain(X))) &        \
\  (\\<forall>X. defined(codomain(X),X)) &      \
\  (\\<forall>X. product(X::'a,domain(X),X)) &      \
\  (\\<forall>X. product(codomain(X),X,X)) &    \
\  (\\<forall>X Y. defined(X::'a,Y) & identity_map(X) --> product(X::'a,Y,Y)) & \
\  (\\<forall>Y X. defined(X::'a,Y) & identity_map(Y) --> product(X::'a,Y,X)) & \
\  (\\<forall>X Y Z W. product(X::'a,Y,Z) & product(X::'a,Y,W) --> equal(Z::'a,W)) &        \
\  (\\<forall>X Y Z W. equal(X::'a,Y) & product(X::'a,Z,W) --> product(Y::'a,Z,W)) &        \
\  (\\<forall>X Z Y W. equal(X::'a,Y) & product(Z::'a,X,W) --> product(Z::'a,Y,W)) &        \
\  (\\<forall>X Z W Y. equal(X::'a,Y) & product(Z::'a,W,X) --> product(Z::'a,W,Y)) &        \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(domain(X),domain(Y))) & \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(codomain(X),codomain(Y))) &     \
\  (\\<forall>X Y. equal(X::'a,Y) & identity_map(X) --> identity_map(Y)) &  \
\  (\\<forall>X Y Z. equal(X::'a,Y) & defined(X::'a,Z) --> defined(Y::'a,Z)) &      \
\  (\\<forall>X Z Y. equal(X::'a,Y) & defined(Z::'a,X) --> defined(Z::'a,Y)) &      \
\  (\\<forall>X Z Y. equal(X::'a,Y) --> equal(compos(Z::'a,X),compos(Z::'a,Y))) & \
\  (\\<forall>X Y Z. equal(X::'a,Y) --> equal(compos(X::'a,Z),compos(Y::'a,Z))) & \
\  (defined(a::'a,b)) &     \
\  (defined(b::'a,c)) &     \
\  (~defined(a::'a,compos(b::'a,c))) --> False",
  meson_tac 1);

(*1118 inferences so far.  Searching to depth 8.  2.3 secs*)
val COL001_2 = prove
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X Y Z. equal(apply(apply(apply(s::'a,X),Y),Z),apply(apply(X::'a,Z),apply(Y::'a,Z)))) &        \
\  (\\<forall>Y X. equal(apply(apply(k::'a,X),Y),X)) &      \
\  (\\<forall>X Y Z. equal(apply(apply(apply(b::'a,X),Y),Z),apply(X::'a,apply(Y::'a,Z)))) & \
\  (\\<forall>X. equal(apply(i::'a,X),X)) & \
\  (\\<forall>A B C. equal(A::'a,B) --> equal(apply(A::'a,C),apply(B::'a,C))) &     \
\  (\\<forall>D F' E. equal(D::'a,E) --> equal(apply(F'::'a,D),apply(F'::'a,E))) &  \
\  (\\<forall>X. equal(apply(apply(apply(s::'a,apply(b::'a,X)),i),apply(apply(s::'a,apply(b::'a,X)),i)),apply(x::'a,apply(apply(apply(s::'a,apply(b::'a,X)),i),apply(apply(s::'a,apply(b::'a,X)),i))))) &   \
\  (\\<forall>Y. ~equal(Y::'a,apply(combinator::'a,Y))) --> False",
  meson_tac 1);

(*500 inferences so far.  Searching to depth 8.  0.9 secs*)
val COL023_1 = prove
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X Y Z. equal(apply(apply(apply(b::'a,X),Y),Z),apply(X::'a,apply(Y::'a,Z)))) & \
\  (\\<forall>X Y Z. equal(apply(apply(apply(n::'a,X),Y),Z),apply(apply(apply(X::'a,Z),Y),Z))) &        \
\  (\\<forall>A B C. equal(A::'a,B) --> equal(apply(A::'a,C),apply(B::'a,C))) &     \
\  (\\<forall>D F' E. equal(D::'a,E) --> equal(apply(F'::'a,D),apply(F'::'a,E))) &  \
\  (\\<forall>Y. ~equal(Y::'a,apply(combinator::'a,Y))) --> False",
  meson_tac 1);

(*3018 inferences so far.  Searching to depth 10.  4.3 secs*)
val COL032_1 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X. equal(apply(m::'a,X),apply(X::'a,X))) &        \
\  (\\<forall>Y X Z. equal(apply(apply(apply(q::'a,X),Y),Z),apply(Y::'a,apply(X::'a,Z)))) & \
\  (\\<forall>A B C. equal(A::'a,B) --> equal(apply(A::'a,C),apply(B::'a,C))) &     \
\  (\\<forall>D F' E. equal(D::'a,E) --> equal(apply(F'::'a,D),apply(F'::'a,E))) &  \
\  (\\<forall>G H. equal(G::'a,H) --> equal(f(G),f(H))) &   \
\  (\\<forall>Y. ~equal(apply(Y::'a,f(Y)),apply(f(Y),apply(Y::'a,f(Y))))) --> False",
  meson_tac 1);

(*381878 inferences so far.  Searching to depth 13.  670.4 secs*)
val COL052_2 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X Y W. equal(response(compos(X::'a,Y),W),response(X::'a,response(Y::'a,W)))) &       \
\  (\\<forall>X Y. agreeable(X) --> equal(response(X::'a,common_bird(Y)),response(Y::'a,common_bird(Y)))) &     \
\  (\\<forall>Z X. equal(response(X::'a,Z),response(compatible(X),Z)) --> agreeable(X)) &   \
\  (\\<forall>A B. equal(A::'a,B) --> equal(common_bird(A),common_bird(B))) &       \
\  (\\<forall>C D. equal(C::'a,D) --> equal(compatible(C),compatible(D))) & \
\  (\\<forall>Q R. equal(Q::'a,R) & agreeable(Q) --> agreeable(R)) &        \
\  (\\<forall>A B C. equal(A::'a,B) --> equal(compos(A::'a,C),compos(B::'a,C))) & \
\  (\\<forall>D F' E. equal(D::'a,E) --> equal(compos(F'::'a,D),compos(F'::'a,E))) &      \
\  (\\<forall>G H I'. equal(G::'a,H) --> equal(response(G::'a,I'),response(H::'a,I'))) &    \
\  (\\<forall>J L K'. equal(J::'a,K') --> equal(response(L::'a,J),response(L::'a,K'))) &    \
\  (agreeable(c)) &     \
\  (~agreeable(a)) &    \
\  (equal(c::'a,compos(a::'a,b))) --> False",
  meson_tac 1);

(*13201 inferences so far.  Searching to depth 11.  31.9 secs*)
val COL075_2 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>Y X. equal(apply(apply(k::'a,X),Y),X)) &      \
\  (\\<forall>X Y Z. equal(apply(apply(apply(abstraction::'a,X),Y),Z),apply(apply(X::'a,apply(k::'a,Z)),apply(Y::'a,Z)))) &     \
\  (\\<forall>D E F'. equal(D::'a,E) --> equal(apply(D::'a,F'),apply(E::'a,F'))) &  \
\  (\\<forall>G I' H. equal(G::'a,H) --> equal(apply(I'::'a,G),apply(I'::'a,H))) &  \
\  (\\<forall>A B. equal(A::'a,B) --> equal(b(A),b(B))) &   \
\  (\\<forall>C D. equal(C::'a,D) --> equal(c(C),c(D))) &   \
\  (\\<forall>Y. ~equal(apply(apply(Y::'a,b(Y)),c(Y)),apply(b(Y),b(Y)))) --> False",
  meson_tac 1);

(*33 inferences so far.  Searching to depth 7.  0.1 secs*)
val COM001_1 = prove
 ("(\\<forall>Goal_state Start_state. follows(Goal_state::'a,Start_state) --> succeeds(Goal_state::'a,Start_state)) &   \
\  (\\<forall>Goal_state Intermediate_state Start_state. succeeds(Goal_state::'a,Intermediate_state) & succeeds(Intermediate_state::'a,Start_state) --> succeeds(Goal_state::'a,Start_state)) &     \
\  (\\<forall>Start_state Label Goal_state. has(Start_state::'a,goto(Label)) & labels(Label::'a,Goal_state) --> succeeds(Goal_state::'a,Start_state)) &     \
\  (\\<forall>Start_state Condition Goal_state. has(Start_state::'a,ifthen(Condition::'a,Goal_state)) --> succeeds(Goal_state::'a,Start_state)) &   \
\  (labels(loop::'a,p3)) &  \
\  (has(p3::'a,ifthen(equal(register_j::'a,n),p4))) &   \
\  (has(p4::'a,goto(out))) &        \
\  (follows(p5::'a,p4)) &   \
\  (follows(p8::'a,p3)) &   \
\  (has(p8::'a,goto(loop))) &       \
\  (~succeeds(p3::'a,p3)) --> False",
  meson_tac 1);

(*533 inferences so far.  Searching to depth 13.  0.3 secs*)
val COM002_1 = prove
 ("(\\<forall>Goal_state Start_state. follows(Goal_state::'a,Start_state) --> succeeds(Goal_state::'a,Start_state)) &   \
\  (\\<forall>Goal_state Intermediate_state Start_state. succeeds(Goal_state::'a,Intermediate_state) & succeeds(Intermediate_state::'a,Start_state) --> succeeds(Goal_state::'a,Start_state)) &     \
\  (\\<forall>Start_state Label Goal_state. has(Start_state::'a,goto(Label)) & labels(Label::'a,Goal_state) --> succeeds(Goal_state::'a,Start_state)) &     \
\  (\\<forall>Start_state Condition Goal_state. has(Start_state::'a,ifthen(Condition::'a,Goal_state)) --> succeeds(Goal_state::'a,Start_state)) &   \
\  (has(p1::'a,assign(register_j::'a,num0))) &     \
\  (follows(p2::'a,p1)) &   \
\  (has(p2::'a,assign(register_k::'a,num1))) &     \
\  (labels(loop::'a,p3)) &  \
\  (follows(p3::'a,p2)) &   \
\  (has(p3::'a,ifthen(equal(register_j::'a,n),p4))) &   \
\  (has(p4::'a,goto(out))) &        \
\  (follows(p5::'a,p4)) &   \
\  (follows(p6::'a,p3)) &   \
\  (has(p6::'a,assign(register_k::'a,times(num2::'a,register_k)))) &   \
\  (follows(p7::'a,p6)) &   \
\  (has(p7::'a,assign(register_j::'a,plus(register_j::'a,num1)))) &    \
\  (follows(p8::'a,p7)) &   \
\  (has(p8::'a,goto(loop))) &       \
\  (~succeeds(p3::'a,p3)) --> False",
  meson_tac 1);

(*4821 inferences so far.  Searching to depth 14.  1.3 secs*)
val COM002_2 = prove
 ("(\\<forall>Goal_state Start_state. ~(fails(Goal_state::'a,Start_state) & follows(Goal_state::'a,Start_state))) &     \
\  (\\<forall>Goal_state Intermediate_state Start_state. fails(Goal_state::'a,Start_state) --> fails(Goal_state::'a,Intermediate_state) | fails(Intermediate_state::'a,Start_state)) &     \
\  (\\<forall>Start_state Label Goal_state. ~(fails(Goal_state::'a,Start_state) & has(Start_state::'a,goto(Label)) & labels(Label::'a,Goal_state))) &       \
\  (\\<forall>Start_state Condition Goal_state. ~(fails(Goal_state::'a,Start_state) & has(Start_state::'a,ifthen(Condition::'a,Goal_state)))) &     \
\  (has(p1::'a,assign(register_j::'a,num0))) &     \
\  (follows(p2::'a,p1)) &   \
\  (has(p2::'a,assign(register_k::'a,num1))) &     \
\  (labels(loop::'a,p3)) &  \
\  (follows(p3::'a,p2)) &   \
\  (has(p3::'a,ifthen(equal(register_j::'a,n),p4))) &   \
\  (has(p4::'a,goto(out))) &        \
\  (follows(p5::'a,p4)) &   \
\  (follows(p6::'a,p3)) &   \
\  (has(p6::'a,assign(register_k::'a,times(num2::'a,register_k)))) &   \
\  (follows(p7::'a,p6)) &   \
\  (has(p7::'a,assign(register_j::'a,plus(register_j::'a,num1)))) &    \
\  (follows(p8::'a,p7)) &   \
\  (has(p8::'a,goto(loop))) &       \
\  (fails(p3::'a,p3)) --> False",
  meson_tac 1);

(*98 inferences so far.  Searching to depth 10.  1.1 secs*)
val COM003_2 = prove
 ("(\\<forall>X Y Z. program_decides(X) & program(Y) --> decides(X::'a,Y,Z)) &      \
\  (\\<forall>X. program_decides(X) | program(f2(X))) &        \
\  (\\<forall>X. decides(X::'a,f2(X),f1(X)) --> program_decides(X)) &       \
\  (\\<forall>X. program_program_decides(X) --> program(X)) &   \
\  (\\<forall>X. program_program_decides(X) --> program_decides(X)) &   \
\  (\\<forall>X. program(X) & program_decides(X) --> program_program_decides(X)) &      \
\  (\\<forall>X. algorithm_program_decides(X) --> algorithm(X)) &       \
\  (\\<forall>X. algorithm_program_decides(X) --> program_decides(X)) & \
\  (\\<forall>X. algorithm(X) & program_decides(X) --> algorithm_program_decides(X)) &  \
\  (\\<forall>Y X. program_halts2(X::'a,Y) --> program(X)) &        \
\  (\\<forall>X Y. program_halts2(X::'a,Y) --> halts2(X::'a,Y)) &       \
\  (\\<forall>X Y. program(X) & halts2(X::'a,Y) --> program_halts2(X::'a,Y)) &  \
\  (\\<forall>W X Y Z. halts3_outputs(X::'a,Y,Z,W) --> halts3(X::'a,Y,Z)) &     \
\  (\\<forall>Y Z X W. halts3_outputs(X::'a,Y,Z,W) --> outputs(X::'a,W)) &      \
\  (\\<forall>Y Z X W. halts3(X::'a,Y,Z) & outputs(X::'a,W) --> halts3_outputs(X::'a,Y,Z,W)) &      \
\  (\\<forall>Y X. program_not_halts2(X::'a,Y) --> program(X)) &    \
\  (\\<forall>X Y. ~(program_not_halts2(X::'a,Y) & halts2(X::'a,Y))) &  \
\  (\\<forall>X Y. program(X) --> program_not_halts2(X::'a,Y) | halts2(X::'a,Y)) &     \
\  (\\<forall>W X Y. halts2_outputs(X::'a,Y,W) --> halts2(X::'a,Y)) &   \
\  (\\<forall>Y X W. halts2_outputs(X::'a,Y,W) --> outputs(X::'a,W)) &  \
\  (\\<forall>Y X W. halts2(X::'a,Y) & outputs(X::'a,W) --> halts2_outputs(X::'a,Y,W)) &    \
\  (\\<forall>X W Y Z. program_halts2_halts3_outputs(X::'a,Y,Z,W) --> program_halts2(Y::'a,Z)) &        \
\  (\\<forall>X Y Z W. program_halts2_halts3_outputs(X::'a,Y,Z,W) --> halts3_outputs(X::'a,Y,Z,W)) &    \
\  (\\<forall>X Y Z W. program_halts2(Y::'a,Z) & halts3_outputs(X::'a,Y,Z,W) --> program_halts2_halts3_outputs(X::'a,Y,Z,W)) &      \
\  (\\<forall>X W Y Z. program_not_halts2_halts3_outputs(X::'a,Y,Z,W) --> program_not_halts2(Y::'a,Z)) &        \
\  (\\<forall>X Y Z W. program_not_halts2_halts3_outputs(X::'a,Y,Z,W) --> halts3_outputs(X::'a,Y,Z,W)) &        \
\  (\\<forall>X Y Z W. program_not_halts2(Y::'a,Z) & halts3_outputs(X::'a,Y,Z,W) --> program_not_halts2_halts3_outputs(X::'a,Y,Z,W)) &      \
\  (\\<forall>X W Y. program_halts2_halts2_outputs(X::'a,Y,W) --> program_halts2(Y::'a,Y)) &    \
\  (\\<forall>X Y W. program_halts2_halts2_outputs(X::'a,Y,W) --> halts2_outputs(X::'a,Y,W)) &  \
\  (\\<forall>X Y W. program_halts2(Y::'a,Y) & halts2_outputs(X::'a,Y,W) --> program_halts2_halts2_outputs(X::'a,Y,W)) &    \
\  (\\<forall>X W Y. program_not_halts2_halts2_outputs(X::'a,Y,W) --> program_not_halts2(Y::'a,Y)) &    \
\  (\\<forall>X Y W. program_not_halts2_halts2_outputs(X::'a,Y,W) --> halts2_outputs(X::'a,Y,W)) &      \
\  (\\<forall>X Y W. program_not_halts2(Y::'a,Y) & halts2_outputs(X::'a,Y,W) --> program_not_halts2_halts2_outputs(X::'a,Y,W)) &    \
\  (\\<forall>X. algorithm_program_decides(X) --> program_program_decides(c1)) &        \
\  (\\<forall>W Y Z. program_program_decides(W) --> program_halts2_halts3_outputs(W::'a,Y,Z,good)) &        \
\  (\\<forall>W Y Z. program_program_decides(W) --> program_not_halts2_halts3_outputs(W::'a,Y,Z,bad)) &     \
\  (\\<forall>W. program(W) & program_halts2_halts3_outputs(W::'a,f3(W),f3(W),good) & program_not_halts2_halts3_outputs(W::'a,f3(W),f3(W),bad) --> program(c2)) &       \
\  (\\<forall>W Y. program(W) & program_halts2_halts3_outputs(W::'a,f3(W),f3(W),good) & program_not_halts2_halts3_outputs(W::'a,f3(W),f3(W),bad) --> program_halts2_halts2_outputs(c2::'a,Y,good)) &        \
\  (\\<forall>W Y. program(W) & program_halts2_halts3_outputs(W::'a,f3(W),f3(W),good) & program_not_halts2_halts3_outputs(W::'a,f3(W),f3(W),bad) --> program_not_halts2_halts2_outputs(c2::'a,Y,bad)) &     \
\  (\\<forall>V. program(V) & program_halts2_halts2_outputs(V::'a,f4(V),good) & program_not_halts2_halts2_outputs(V::'a,f4(V),bad) --> program(c3)) &   \
\  (\\<forall>V Y. program(V) & program_halts2_halts2_outputs(V::'a,f4(V),good) & program_not_halts2_halts2_outputs(V::'a,f4(V),bad) & program_halts2(Y::'a,Y) --> halts2(c3::'a,Y)) &  \
\  (\\<forall>V Y. program(V) & program_halts2_halts2_outputs(V::'a,f4(V),good) & program_not_halts2_halts2_outputs(V::'a,f4(V),bad) --> program_not_halts2_halts2_outputs(c3::'a,Y,bad)) & \
\  (algorithm_program_decides(c4)) --> False",
  meson_tac 1);

(****************SLOW
2100398 inferences so far.  Searching to depth 12.  No proof after 30 mins.
val COM004_1 = prove
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>C D P Q X Y. failure_node(X::'a,or(C::'a,P)) & failure_node(Y::'a,or(D::'a,Q)) & contradictory(P::'a,Q) & siblings(X::'a,Y) --> failure_node(parent_of(X::'a,Y),or(C::'a,D))) &   \
\  (\\<forall>X. contradictory(negate(X),X)) &  \
\  (\\<forall>X. contradictory(X::'a,negate(X))) &  \
\  (\\<forall>X. siblings(left_child_of(X),right_child_of(X))) &        \
\  (\\<forall>D E. equal(D::'a,E) --> equal(left_child_of(D),left_child_of(E))) &   \
\  (\\<forall>F' G. equal(F'::'a,G) --> equal(negate(F'),negate(G))) &      \
\  (\\<forall>H I' J. equal(H::'a,I') --> equal(or(H::'a,J),or(I'::'a,J))) &        \
\  (\\<forall>K' M L. equal(K'::'a,L) --> equal(or(M::'a,K'),or(M::'a,L))) &        \
\  (\\<forall>N O_ P. equal(N::'a,O_) --> equal(parent_of(N::'a,P),parent_of(O_::'a,P))) &     \
\  (\\<forall>Q S' R. equal(Q::'a,R) --> equal(parent_of(S'::'a,Q),parent_of(S'::'a,R))) &  \
\  (\\<forall>T' U. equal(T'::'a,U) --> equal(right_child_of(T'),right_child_of(U))) &      \
\  (\\<forall>V W X. equal(V::'a,W) & contradictory(V::'a,X) --> contradictory(W::'a,X)) &  \
\  (\\<forall>Y A1 Z. equal(Y::'a,Z) & contradictory(A1::'a,Y) --> contradictory(A1::'a,Z)) &       \
\  (\\<forall>B1 C1 D1. equal(B1::'a,C1) & failure_node(B1::'a,D1) --> failure_node(C1::'a,D1)) &   \
\  (\\<forall>E1 G1 F1. equal(E1::'a,F1) & failure_node(G1::'a,E1) --> failure_node(G1::'a,F1)) &   \
\  (\\<forall>H1 I1 J1. equal(H1::'a,I1) & siblings(H1::'a,J1) --> siblings(I1::'a,J1)) &   \
\  (\\<forall>K1 M1 L1. equal(K1::'a,L1) & siblings(M1::'a,K1) --> siblings(M1::'a,L1)) &   \
\  (failure_node(n_left::'a,or(EMPTY::'a,atom))) &      \
\  (failure_node(n_right::'a,or(EMPTY::'a,negate(atom)))) &     \
\  (equal(n_left::'a,left_child_of(n))) &   \
\  (equal(n_right::'a,right_child_of(n))) & \
\  (\\<forall>Z. ~failure_node(Z::'a,or(EMPTY::'a,EMPTY))) --> False",
  meson_tac 1);
****************)

(*179 inferences so far.  Searching to depth 7.  3.9 secs*)
val GEO003_1 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X Y. between(X::'a,Y,X) --> equal(X::'a,Y)) &     \
\  (\\<forall>V X Y Z. between(X::'a,Y,V) & between(Y::'a,Z,V) --> between(X::'a,Y,Z)) &    \
\  (\\<forall>Y X V Z. between(X::'a,Y,Z) & between(X::'a,Y,V) --> equal(X::'a,Y) | between(X::'a,Z,V) | between(X::'a,V,Z)) &    \
\  (\\<forall>Y X. equidistant(X::'a,Y,Y,X)) &      \
\  (\\<forall>Z X Y. equidistant(X::'a,Y,Z,Z) --> equal(X::'a,Y)) &     \
\  (\\<forall>X Y Z V V2 W. equidistant(X::'a,Y,Z,V) & equidistant(X::'a,Y,V2,W) --> equidistant(Z::'a,V,V2,W)) &   \
\  (\\<forall>W X Z V Y. between(X::'a,W,V) & between(Y::'a,V,Z) --> between(X::'a,outer_pasch(W::'a,X,Y,Z,V),Y)) &     \
\  (\\<forall>W X Y Z V. between(X::'a,W,V) & between(Y::'a,V,Z) --> between(Z::'a,W,outer_pasch(W::'a,X,Y,Z,V))) &     \
\  (\\<forall>W X Y Z V. between(X::'a,V,W) & between(Y::'a,V,Z) --> equal(X::'a,V) | between(X::'a,Z,euclid1(W::'a,X,Y,Z,V))) &   \
\  (\\<forall>W X Y Z V. between(X::'a,V,W) & between(Y::'a,V,Z) --> equal(X::'a,V) | between(X::'a,Y,euclid2(W::'a,X,Y,Z,V))) &   \
\  (\\<forall>W X Y Z V. between(X::'a,V,W) & between(Y::'a,V,Z) --> equal(X::'a,V) | between(euclid1(W::'a,X,Y,Z,V),W,euclid2(W::'a,X,Y,Z,V))) &  \
\  (\\<forall>X1 Y1 X Y Z V Z1 V1. equidistant(X::'a,Y,X1,Y1) & equidistant(Y::'a,Z,Y1,Z1) & equidistant(X::'a,V,X1,V1) & equidistant(Y::'a,V,Y1,V1) & between(X::'a,Y,Z) & between(X1::'a,Y1,Z1) --> equal(X::'a,Y) | equidistant(Z::'a,V,Z1,V1)) &   \
\  (\\<forall>X Y W V. between(X::'a,Y,extension(X::'a,Y,W,V))) &       \
\  (\\<forall>X Y W V. equidistant(Y::'a,extension(X::'a,Y,W,V),W,V)) & \
\  (~between(lower_dimension_point_1::'a,lower_dimension_point_2,lower_dimension_point_3)) &        \
\  (~between(lower_dimension_point_2::'a,lower_dimension_point_3,lower_dimension_point_1)) &        \
\  (~between(lower_dimension_point_3::'a,lower_dimension_point_1,lower_dimension_point_2)) &        \
\  (\\<forall>Z X Y W V. equidistant(X::'a,W,X,V) & equidistant(Y::'a,W,Y,V) & equidistant(Z::'a,W,Z,V) --> between(X::'a,Y,Z) | between(Y::'a,Z,X) | between(Z::'a,X,Y) | equal(W::'a,V)) &     \
\  (\\<forall>X Y Z X1 Z1 V. equidistant(V::'a,X,V,X1) & equidistant(V::'a,Z,V,Z1) & between(V::'a,X,Z) & between(X::'a,Y,Z) --> equidistant(V::'a,Y,Z,continuous(X::'a,Y,Z,X1,Z1,V))) &        \
\  (\\<forall>X Y Z X1 V Z1. equidistant(V::'a,X,V,X1) & equidistant(V::'a,Z,V,Z1) & between(V::'a,X,Z) & between(X::'a,Y,Z) --> between(X1::'a,continuous(X::'a,Y,Z,X1,Z1,V),Z1)) &    \
\  (\\<forall>X Y W Z. equal(X::'a,Y) & between(X::'a,W,Z) --> between(Y::'a,W,Z)) &        \
\  (\\<forall>X W Y Z. equal(X::'a,Y) & between(W::'a,X,Z) --> between(W::'a,Y,Z)) &        \
\  (\\<forall>X W Z Y. equal(X::'a,Y) & between(W::'a,Z,X) --> between(W::'a,Z,Y)) &        \
\  (\\<forall>X Y V W Z. equal(X::'a,Y) & equidistant(X::'a,V,W,Z) --> equidistant(Y::'a,V,W,Z)) &  \
\  (\\<forall>X V Y W Z. equal(X::'a,Y) & equidistant(V::'a,X,W,Z) --> equidistant(V::'a,Y,W,Z)) &  \
\  (\\<forall>X V W Y Z. equal(X::'a,Y) & equidistant(V::'a,W,X,Z) --> equidistant(V::'a,W,Y,Z)) &  \
\  (\\<forall>X V W Z Y. equal(X::'a,Y) & equidistant(V::'a,W,Z,X) --> equidistant(V::'a,W,Z,Y)) &  \
\  (\\<forall>X Y V1 V2 V3 V4. equal(X::'a,Y) --> equal(outer_pasch(X::'a,V1,V2,V3,V4),outer_pasch(Y::'a,V1,V2,V3,V4))) &   \
\  (\\<forall>X V1 Y V2 V3 V4. equal(X::'a,Y) --> equal(outer_pasch(V1::'a,X,V2,V3,V4),outer_pasch(V1::'a,Y,V2,V3,V4))) &   \
\  (\\<forall>X V1 V2 Y V3 V4. equal(X::'a,Y) --> equal(outer_pasch(V1::'a,V2,X,V3,V4),outer_pasch(V1::'a,V2,Y,V3,V4))) &   \
\  (\\<forall>X V1 V2 V3 Y V4. equal(X::'a,Y) --> equal(outer_pasch(V1::'a,V2,V3,X,V4),outer_pasch(V1::'a,V2,V3,Y,V4))) &   \
\  (\\<forall>X V1 V2 V3 V4 Y. equal(X::'a,Y) --> equal(outer_pasch(V1::'a,V2,V3,V4,X),outer_pasch(V1::'a,V2,V3,V4,Y))) &   \
\  (\\<forall>A B C D E F'. equal(A::'a,B) --> equal(euclid1(A::'a,C,D,E,F'),euclid1(B::'a,C,D,E,F'))) &    \
\  (\\<forall>G I' H J K' L. equal(G::'a,H) --> equal(euclid1(I'::'a,G,J,K',L),euclid1(I'::'a,H,J,K',L))) & \
\  (\\<forall>M O_ P N Q R. equal(M::'a,N) --> equal(euclid1(O_::'a,P,M,Q,R),euclid1(O_::'a,P,N,Q,R))) &       \
\  (\\<forall>S' U V W T' X. equal(S'::'a,T') --> equal(euclid1(U::'a,V,W,S',X),euclid1(U::'a,V,W,T',X))) & \
\  (\\<forall>Y A1 B1 C1 D1 Z. equal(Y::'a,Z) --> equal(euclid1(A1::'a,B1,C1,D1,Y),euclid1(A1::'a,B1,C1,D1,Z))) &   \
\  (\\<forall>E1 F1 G1 H1 I1 J1. equal(E1::'a,F1) --> equal(euclid2(E1::'a,G1,H1,I1,J1),euclid2(F1::'a,G1,H1,I1,J1))) &     \
\  (\\<forall>K1 M1 L1 N1 O1 P1. equal(K1::'a,L1) --> equal(euclid2(M1::'a,K1,N1,O1,P1),euclid2(M1::'a,L1,N1,O1,P1))) &     \
\  (\\<forall>Q1 S1 T1 R1 U1 V1. equal(Q1::'a,R1) --> equal(euclid2(S1::'a,T1,Q1,U1,V1),euclid2(S1::'a,T1,R1,U1,V1))) &     \
\  (\\<forall>W1 Y1 Z1 A2 X1 B2. equal(W1::'a,X1) --> equal(euclid2(Y1::'a,Z1,A2,W1,B2),euclid2(Y1::'a,Z1,A2,X1,B2))) &     \
\  (\\<forall>C2 E2 F2 G2 H2 D2. equal(C2::'a,D2) --> equal(euclid2(E2::'a,F2,G2,H2,C2),euclid2(E2::'a,F2,G2,H2,D2))) &     \
\  (\\<forall>X Y V1 V2 V3. equal(X::'a,Y) --> equal(extension(X::'a,V1,V2,V3),extension(Y::'a,V1,V2,V3))) &        \
\  (\\<forall>X V1 Y V2 V3. equal(X::'a,Y) --> equal(extension(V1::'a,X,V2,V3),extension(V1::'a,Y,V2,V3))) &        \
\  (\\<forall>X V1 V2 Y V3. equal(X::'a,Y) --> equal(extension(V1::'a,V2,X,V3),extension(V1::'a,V2,Y,V3))) &        \
\  (\\<forall>X V1 V2 V3 Y. equal(X::'a,Y) --> equal(extension(V1::'a,V2,V3,X),extension(V1::'a,V2,V3,Y))) &        \
\  (\\<forall>X Y V1 V2 V3 V4 V5. equal(X::'a,Y) --> equal(continuous(X::'a,V1,V2,V3,V4,V5),continuous(Y::'a,V1,V2,V3,V4,V5))) &    \
\  (\\<forall>X V1 Y V2 V3 V4 V5. equal(X::'a,Y) --> equal(continuous(V1::'a,X,V2,V3,V4,V5),continuous(V1::'a,Y,V2,V3,V4,V5))) &    \
\  (\\<forall>X V1 V2 Y V3 V4 V5. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,X,V3,V4,V5),continuous(V1::'a,V2,Y,V3,V4,V5))) &    \
\  (\\<forall>X V1 V2 V3 Y V4 V5. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,V3,X,V4,V5),continuous(V1::'a,V2,V3,Y,V4,V5))) &    \
\  (\\<forall>X V1 V2 V3 V4 Y V5. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,V3,V4,X,V5),continuous(V1::'a,V2,V3,V4,Y,V5))) &    \
\  (\\<forall>X V1 V2 V3 V4 V5 Y. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,V3,V4,V5,X),continuous(V1::'a,V2,V3,V4,V5,Y))) &    \
\  (~between(a::'a,b,b)) --> False",
  meson_tac 1);

(*4272 inferences so far.  Searching to depth 10.  29.4 secs*)
val GEO017_2 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>Y X. equidistant(X::'a,Y,Y,X)) &      \
\  (\\<forall>X Y Z V V2 W. equidistant(X::'a,Y,Z,V) & equidistant(X::'a,Y,V2,W) --> equidistant(Z::'a,V,V2,W)) &   \
\  (\\<forall>Z X Y. equidistant(X::'a,Y,Z,Z) --> equal(X::'a,Y)) &     \
\  (\\<forall>X Y W V. between(X::'a,Y,extension(X::'a,Y,W,V))) &       \
\  (\\<forall>X Y W V. equidistant(Y::'a,extension(X::'a,Y,W,V),W,V)) & \
\  (\\<forall>X1 Y1 X Y Z V Z1 V1. equidistant(X::'a,Y,X1,Y1) & equidistant(Y::'a,Z,Y1,Z1) & equidistant(X::'a,V,X1,V1) & equidistant(Y::'a,V,Y1,V1) & between(X::'a,Y,Z) & between(X1::'a,Y1,Z1) --> equal(X::'a,Y) | equidistant(Z::'a,V,Z1,V1)) &   \
\  (\\<forall>X Y. between(X::'a,Y,X) --> equal(X::'a,Y)) &     \
\  (\\<forall>U V W X Y. between(U::'a,V,W) & between(Y::'a,X,W) --> between(V::'a,inner_pasch(U::'a,V,W,X,Y),Y)) &     \
\  (\\<forall>V W X Y U. between(U::'a,V,W) & between(Y::'a,X,W) --> between(X::'a,inner_pasch(U::'a,V,W,X,Y),U)) &     \
\  (~between(lower_dimension_point_1::'a,lower_dimension_point_2,lower_dimension_point_3)) &        \
\  (~between(lower_dimension_point_2::'a,lower_dimension_point_3,lower_dimension_point_1)) &        \
\  (~between(lower_dimension_point_3::'a,lower_dimension_point_1,lower_dimension_point_2)) &        \
\  (\\<forall>Z X Y W V. equidistant(X::'a,W,X,V) & equidistant(Y::'a,W,Y,V) & equidistant(Z::'a,W,Z,V) --> between(X::'a,Y,Z) | between(Y::'a,Z,X) | between(Z::'a,X,Y) | equal(W::'a,V)) &     \
\  (\\<forall>U V W X Y. between(U::'a,W,Y) & between(V::'a,W,X) --> equal(U::'a,W) | between(U::'a,V,euclid1(U::'a,V,W,X,Y))) &   \
\  (\\<forall>U V W X Y. between(U::'a,W,Y) & between(V::'a,W,X) --> equal(U::'a,W) | between(U::'a,X,euclid2(U::'a,V,W,X,Y))) &   \
\  (\\<forall>U V W X Y. between(U::'a,W,Y) & between(V::'a,W,X) --> equal(U::'a,W) | between(euclid1(U::'a,V,W,X,Y),Y,euclid2(U::'a,V,W,X,Y))) &  \
\  (\\<forall>U V V1 W X X1. equidistant(U::'a,V,U,V1) & equidistant(U::'a,X,U,X1) & between(U::'a,V,X) & between(V::'a,W,X) --> between(V1::'a,continuous(U::'a,V,V1,W,X,X1),X1)) &    \
\  (\\<forall>U V V1 W X X1. equidistant(U::'a,V,U,V1) & equidistant(U::'a,X,U,X1) & between(U::'a,V,X) & between(V::'a,W,X) --> equidistant(U::'a,W,U,continuous(U::'a,V,V1,W,X,X1))) &        \
\  (\\<forall>X Y W Z. equal(X::'a,Y) & between(X::'a,W,Z) --> between(Y::'a,W,Z)) &        \
\  (\\<forall>X W Y Z. equal(X::'a,Y) & between(W::'a,X,Z) --> between(W::'a,Y,Z)) &        \
\  (\\<forall>X W Z Y. equal(X::'a,Y) & between(W::'a,Z,X) --> between(W::'a,Z,Y)) &        \
\  (\\<forall>X Y V W Z. equal(X::'a,Y) & equidistant(X::'a,V,W,Z) --> equidistant(Y::'a,V,W,Z)) &  \
\  (\\<forall>X V Y W Z. equal(X::'a,Y) & equidistant(V::'a,X,W,Z) --> equidistant(V::'a,Y,W,Z)) &  \
\  (\\<forall>X V W Y Z. equal(X::'a,Y) & equidistant(V::'a,W,X,Z) --> equidistant(V::'a,W,Y,Z)) &  \
\  (\\<forall>X V W Z Y. equal(X::'a,Y) & equidistant(V::'a,W,Z,X) --> equidistant(V::'a,W,Z,Y)) &  \
\  (\\<forall>X Y V1 V2 V3 V4. equal(X::'a,Y) --> equal(inner_pasch(X::'a,V1,V2,V3,V4),inner_pasch(Y::'a,V1,V2,V3,V4))) &   \
\  (\\<forall>X V1 Y V2 V3 V4. equal(X::'a,Y) --> equal(inner_pasch(V1::'a,X,V2,V3,V4),inner_pasch(V1::'a,Y,V2,V3,V4))) &   \
\  (\\<forall>X V1 V2 Y V3 V4. equal(X::'a,Y) --> equal(inner_pasch(V1::'a,V2,X,V3,V4),inner_pasch(V1::'a,V2,Y,V3,V4))) &   \
\  (\\<forall>X V1 V2 V3 Y V4. equal(X::'a,Y) --> equal(inner_pasch(V1::'a,V2,V3,X,V4),inner_pasch(V1::'a,V2,V3,Y,V4))) &   \
\  (\\<forall>X V1 V2 V3 V4 Y. equal(X::'a,Y) --> equal(inner_pasch(V1::'a,V2,V3,V4,X),inner_pasch(V1::'a,V2,V3,V4,Y))) &   \
\  (\\<forall>A B C D E F'. equal(A::'a,B) --> equal(euclid1(A::'a,C,D,E,F'),euclid1(B::'a,C,D,E,F'))) &    \
\  (\\<forall>G I' H J K' L. equal(G::'a,H) --> equal(euclid1(I'::'a,G,J,K',L),euclid1(I'::'a,H,J,K',L))) & \
\  (\\<forall>M O_ P N Q R. equal(M::'a,N) --> equal(euclid1(O_::'a,P,M,Q,R),euclid1(O_::'a,P,N,Q,R))) &       \
\  (\\<forall>S' U V W T' X. equal(S'::'a,T') --> equal(euclid1(U::'a,V,W,S',X),euclid1(U::'a,V,W,T',X))) & \
\  (\\<forall>Y A1 B1 C1 D1 Z. equal(Y::'a,Z) --> equal(euclid1(A1::'a,B1,C1,D1,Y),euclid1(A1::'a,B1,C1,D1,Z))) &   \
\  (\\<forall>E1 F1 G1 H1 I1 J1. equal(E1::'a,F1) --> equal(euclid2(E1::'a,G1,H1,I1,J1),euclid2(F1::'a,G1,H1,I1,J1))) &     \
\  (\\<forall>K1 M1 L1 N1 O1 P1. equal(K1::'a,L1) --> equal(euclid2(M1::'a,K1,N1,O1,P1),euclid2(M1::'a,L1,N1,O1,P1))) &     \
\  (\\<forall>Q1 S1 T1 R1 U1 V1. equal(Q1::'a,R1) --> equal(euclid2(S1::'a,T1,Q1,U1,V1),euclid2(S1::'a,T1,R1,U1,V1))) &     \
\  (\\<forall>W1 Y1 Z1 A2 X1 B2. equal(W1::'a,X1) --> equal(euclid2(Y1::'a,Z1,A2,W1,B2),euclid2(Y1::'a,Z1,A2,X1,B2))) &     \
\  (\\<forall>C2 E2 F2 G2 H2 D2. equal(C2::'a,D2) --> equal(euclid2(E2::'a,F2,G2,H2,C2),euclid2(E2::'a,F2,G2,H2,D2))) &     \
\  (\\<forall>X Y V1 V2 V3. equal(X::'a,Y) --> equal(extension(X::'a,V1,V2,V3),extension(Y::'a,V1,V2,V3))) &        \
\  (\\<forall>X V1 Y V2 V3. equal(X::'a,Y) --> equal(extension(V1::'a,X,V2,V3),extension(V1::'a,Y,V2,V3))) &        \
\  (\\<forall>X V1 V2 Y V3. equal(X::'a,Y) --> equal(extension(V1::'a,V2,X,V3),extension(V1::'a,V2,Y,V3))) &        \
\  (\\<forall>X V1 V2 V3 Y. equal(X::'a,Y) --> equal(extension(V1::'a,V2,V3,X),extension(V1::'a,V2,V3,Y))) &        \
\  (\\<forall>X Y V1 V2 V3 V4 V5. equal(X::'a,Y) --> equal(continuous(X::'a,V1,V2,V3,V4,V5),continuous(Y::'a,V1,V2,V3,V4,V5))) &    \
\  (\\<forall>X V1 Y V2 V3 V4 V5. equal(X::'a,Y) --> equal(continuous(V1::'a,X,V2,V3,V4,V5),continuous(V1::'a,Y,V2,V3,V4,V5))) &    \
\  (\\<forall>X V1 V2 Y V3 V4 V5. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,X,V3,V4,V5),continuous(V1::'a,V2,Y,V3,V4,V5))) &    \
\  (\\<forall>X V1 V2 V3 Y V4 V5. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,V3,X,V4,V5),continuous(V1::'a,V2,V3,Y,V4,V5))) &    \
\  (\\<forall>X V1 V2 V3 V4 Y V5. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,V3,V4,X,V5),continuous(V1::'a,V2,V3,V4,Y,V5))) &    \
\  (\\<forall>X V1 V2 V3 V4 V5 Y. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,V3,V4,V5,X),continuous(V1::'a,V2,V3,V4,V5,Y))) &    \
\  (equidistant(u::'a,v,w,x)) &     \
\  (~equidistant(u::'a,v,x,w)) --> False",
  meson_tac 1);

(****************SLOW
382903 inferences so far.  Searching to depth 9.  No proof after 35 minutes.
val GEO027_3 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>Y X. equidistant(X::'a,Y,Y,X)) &      \
\  (\\<forall>X Y Z V V2 W. equidistant(X::'a,Y,Z,V) & equidistant(X::'a,Y,V2,W) --> equidistant(Z::'a,V,V2,W)) &   \
\  (\\<forall>Z X Y. equidistant(X::'a,Y,Z,Z) --> equal(X::'a,Y)) &     \
\  (\\<forall>X Y W V. between(X::'a,Y,extension(X::'a,Y,W,V))) &       \
\  (\\<forall>X Y W V. equidistant(Y::'a,extension(X::'a,Y,W,V),W,V)) & \
\  (\\<forall>X1 Y1 X Y Z V Z1 V1. equidistant(X::'a,Y,X1,Y1) & equidistant(Y::'a,Z,Y1,Z1) & equidistant(X::'a,V,X1,V1) & equidistant(Y::'a,V,Y1,V1) & between(X::'a,Y,Z) & between(X1::'a,Y1,Z1) --> equal(X::'a,Y) | equidistant(Z::'a,V,Z1,V1)) &   \
\  (\\<forall>X Y. between(X::'a,Y,X) --> equal(X::'a,Y)) &     \
\  (\\<forall>U V W X Y. between(U::'a,V,W) & between(Y::'a,X,W) --> between(V::'a,inner_pasch(U::'a,V,W,X,Y),Y)) &     \
\  (\\<forall>V W X Y U. between(U::'a,V,W) & between(Y::'a,X,W) --> between(X::'a,inner_pasch(U::'a,V,W,X,Y),U)) &     \
\  (~between(lower_dimension_point_1::'a,lower_dimension_point_2,lower_dimension_point_3)) &        \
\  (~between(lower_dimension_point_2::'a,lower_dimension_point_3,lower_dimension_point_1)) &        \
\  (~between(lower_dimension_point_3::'a,lower_dimension_point_1,lower_dimension_point_2)) &        \
\  (\\<forall>Z X Y W V. equidistant(X::'a,W,X,V) & equidistant(Y::'a,W,Y,V) & equidistant(Z::'a,W,Z,V) --> between(X::'a,Y,Z) | between(Y::'a,Z,X) | between(Z::'a,X,Y) | equal(W::'a,V)) &     \
\  (\\<forall>U V W X Y. between(U::'a,W,Y) & between(V::'a,W,X) --> equal(U::'a,W) | between(U::'a,V,euclid1(U::'a,V,W,X,Y))) &   \
\  (\\<forall>U V W X Y. between(U::'a,W,Y) & between(V::'a,W,X) --> equal(U::'a,W) | between(U::'a,X,euclid2(U::'a,V,W,X,Y))) &   \
\  (\\<forall>U V W X Y. between(U::'a,W,Y) & between(V::'a,W,X) --> equal(U::'a,W) | between(euclid1(U::'a,V,W,X,Y),Y,euclid2(U::'a,V,W,X,Y))) &  \
\  (\\<forall>U V V1 W X X1. equidistant(U::'a,V,U,V1) & equidistant(U::'a,X,U,X1) & between(U::'a,V,X) & between(V::'a,W,X) --> between(V1::'a,continuous(U::'a,V,V1,W,X,X1),X1)) &    \
\  (\\<forall>U V V1 W X X1. equidistant(U::'a,V,U,V1) & equidistant(U::'a,X,U,X1) & between(U::'a,V,X) & between(V::'a,W,X) --> equidistant(U::'a,W,U,continuous(U::'a,V,V1,W,X,X1))) &        \
\  (\\<forall>X Y W Z. equal(X::'a,Y) & between(X::'a,W,Z) --> between(Y::'a,W,Z)) &        \
\  (\\<forall>X W Y Z. equal(X::'a,Y) & between(W::'a,X,Z) --> between(W::'a,Y,Z)) &        \
\  (\\<forall>X W Z Y. equal(X::'a,Y) & between(W::'a,Z,X) --> between(W::'a,Z,Y)) &        \
\  (\\<forall>X Y V W Z. equal(X::'a,Y) & equidistant(X::'a,V,W,Z) --> equidistant(Y::'a,V,W,Z)) &  \
\  (\\<forall>X V Y W Z. equal(X::'a,Y) & equidistant(V::'a,X,W,Z) --> equidistant(V::'a,Y,W,Z)) &  \
\  (\\<forall>X V W Y Z. equal(X::'a,Y) & equidistant(V::'a,W,X,Z) --> equidistant(V::'a,W,Y,Z)) &  \
\  (\\<forall>X V W Z Y. equal(X::'a,Y) & equidistant(V::'a,W,Z,X) --> equidistant(V::'a,W,Z,Y)) &  \
\  (\\<forall>X Y V1 V2 V3 V4. equal(X::'a,Y) --> equal(inner_pasch(X::'a,V1,V2,V3,V4),inner_pasch(Y::'a,V1,V2,V3,V4))) &   \
\  (\\<forall>X V1 Y V2 V3 V4. equal(X::'a,Y) --> equal(inner_pasch(V1::'a,X,V2,V3,V4),inner_pasch(V1::'a,Y,V2,V3,V4))) &   \
\  (\\<forall>X V1 V2 Y V3 V4. equal(X::'a,Y) --> equal(inner_pasch(V1::'a,V2,X,V3,V4),inner_pasch(V1::'a,V2,Y,V3,V4))) &   \
\  (\\<forall>X V1 V2 V3 Y V4. equal(X::'a,Y) --> equal(inner_pasch(V1::'a,V2,V3,X,V4),inner_pasch(V1::'a,V2,V3,Y,V4))) &   \
\  (\\<forall>X V1 V2 V3 V4 Y. equal(X::'a,Y) --> equal(inner_pasch(V1::'a,V2,V3,V4,X),inner_pasch(V1::'a,V2,V3,V4,Y))) &   \
\  (\\<forall>A B C D E F'. equal(A::'a,B) --> equal(euclid1(A::'a,C,D,E,F'),euclid1(B::'a,C,D,E,F'))) &    \
\  (\\<forall>G I' H J K' L. equal(G::'a,H) --> equal(euclid1(I'::'a,G,J,K',L),euclid1(I'::'a,H,J,K',L))) & \
\  (\\<forall>M O_ P N Q R. equal(M::'a,N) --> equal(euclid1(O_::'a,P,M,Q,R),euclid1(O_::'a,P,N,Q,R))) &       \
\  (\\<forall>S' U V W T' X. equal(S'::'a,T') --> equal(euclid1(U::'a,V,W,S',X),euclid1(U::'a,V,W,T',X))) & \
\  (\\<forall>Y A1 B1 C1 D1 Z. equal(Y::'a,Z) --> equal(euclid1(A1::'a,B1,C1,D1,Y),euclid1(A1::'a,B1,C1,D1,Z))) &   \
\  (\\<forall>E1 F1 G1 H1 I1 J1. equal(E1::'a,F1) --> equal(euclid2(E1::'a,G1,H1,I1,J1),euclid2(F1::'a,G1,H1,I1,J1))) &     \
\  (\\<forall>K1 M1 L1 N1 O1 P1. equal(K1::'a,L1) --> equal(euclid2(M1::'a,K1,N1,O1,P1),euclid2(M1::'a,L1,N1,O1,P1))) &     \
\  (\\<forall>Q1 S1 T1 R1 U1 V1. equal(Q1::'a,R1) --> equal(euclid2(S1::'a,T1,Q1,U1,V1),euclid2(S1::'a,T1,R1,U1,V1))) &     \
\  (\\<forall>W1 Y1 Z1 A2 X1 B2. equal(W1::'a,X1) --> equal(euclid2(Y1::'a,Z1,A2,W1,B2),euclid2(Y1::'a,Z1,A2,X1,B2))) &     \
\  (\\<forall>C2 E2 F2 G2 H2 D2. equal(C2::'a,D2) --> equal(euclid2(E2::'a,F2,G2,H2,C2),euclid2(E2::'a,F2,G2,H2,D2))) &     \
\  (\\<forall>X Y V1 V2 V3. equal(X::'a,Y) --> equal(extension(X::'a,V1,V2,V3),extension(Y::'a,V1,V2,V3))) &        \
\  (\\<forall>X V1 Y V2 V3. equal(X::'a,Y) --> equal(extension(V1::'a,X,V2,V3),extension(V1::'a,Y,V2,V3))) &        \
\  (\\<forall>X V1 V2 Y V3. equal(X::'a,Y) --> equal(extension(V1::'a,V2,X,V3),extension(V1::'a,V2,Y,V3))) &        \
\  (\\<forall>X V1 V2 V3 Y. equal(X::'a,Y) --> equal(extension(V1::'a,V2,V3,X),extension(V1::'a,V2,V3,Y))) &        \
\  (\\<forall>X Y V1 V2 V3 V4 V5. equal(X::'a,Y) --> equal(continuous(X::'a,V1,V2,V3,V4,V5),continuous(Y::'a,V1,V2,V3,V4,V5))) &    \
\  (\\<forall>X V1 Y V2 V3 V4 V5. equal(X::'a,Y) --> equal(continuous(V1::'a,X,V2,V3,V4,V5),continuous(V1::'a,Y,V2,V3,V4,V5))) &    \
\  (\\<forall>X V1 V2 Y V3 V4 V5. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,X,V3,V4,V5),continuous(V1::'a,V2,Y,V3,V4,V5))) &    \
\  (\\<forall>X V1 V2 V3 Y V4 V5. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,V3,X,V4,V5),continuous(V1::'a,V2,V3,Y,V4,V5))) &    \
\  (\\<forall>X V1 V2 V3 V4 Y V5. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,V3,V4,X,V5),continuous(V1::'a,V2,V3,V4,Y,V5))) &    \
\  (\\<forall>X V1 V2 V3 V4 V5 Y. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,V3,V4,V5,X),continuous(V1::'a,V2,V3,V4,V5,Y))) &    \
\  (\\<forall>U V. equal(reflection(U::'a,V),extension(U::'a,V,U,V))) & \
\  (\\<forall>X Y Z. equal(X::'a,Y) --> equal(reflection(X::'a,Z),reflection(Y::'a,Z))) &   \
\  (\\<forall>A1 C1 B1. equal(A1::'a,B1) --> equal(reflection(C1::'a,A1),reflection(C1::'a,B1))) &  \
\  (\\<forall>U V. equidistant(U::'a,V,U,V)) &      \
\  (\\<forall>W X U V. equidistant(U::'a,V,W,X) --> equidistant(W::'a,X,U,V)) & \
\  (\\<forall>V U W X. equidistant(U::'a,V,W,X) --> equidistant(V::'a,U,W,X)) & \
\  (\\<forall>U V X W. equidistant(U::'a,V,W,X) --> equidistant(U::'a,V,X,W)) & \
\  (\\<forall>V U X W. equidistant(U::'a,V,W,X) --> equidistant(V::'a,U,X,W)) & \
\  (\\<forall>W X V U. equidistant(U::'a,V,W,X) --> equidistant(W::'a,X,V,U)) & \
\  (\\<forall>X W U V. equidistant(U::'a,V,W,X) --> equidistant(X::'a,W,U,V)) & \
\  (\\<forall>X W V U. equidistant(U::'a,V,W,X) --> equidistant(X::'a,W,V,U)) & \
\  (\\<forall>W X U V Y Z. equidistant(U::'a,V,W,X) & equidistant(W::'a,X,Y,Z) --> equidistant(U::'a,V,Y,Z)) &      \
\  (\\<forall>U V W. equal(V::'a,extension(U::'a,V,W,W))) &     \
\  (\\<forall>W X U V Y. equal(Y::'a,extension(U::'a,V,W,X)) --> between(U::'a,V,Y)) &      \
\  (\\<forall>U V. between(U::'a,V,reflection(U::'a,V))) &      \
\  (\\<forall>U V. equidistant(V::'a,reflection(U::'a,V),U,V)) &        \
\  (\\<forall>U V. equal(U::'a,V) --> equal(V::'a,reflection(U::'a,V))) &   \
\  (\\<forall>U. equal(U::'a,reflection(U::'a,U))) &    \
\  (\\<forall>U V. equal(V::'a,reflection(U::'a,V)) --> equal(U::'a,V)) &   \
\  (\\<forall>U V. equidistant(U::'a,U,V,V)) &      \
\  (\\<forall>V V1 U W U1 W1. equidistant(U::'a,V,U1,V1) & equidistant(V::'a,W,V1,W1) & between(U::'a,V,W) & between(U1::'a,V1,W1) --> equidistant(U::'a,W,U1,W1)) &        \
\  (\\<forall>U V W X. between(U::'a,V,W) & between(U::'a,V,X) & equidistant(V::'a,W,V,X) --> equal(U::'a,V) | equal(W::'a,X)) &   \
\  (between(u::'a,v,w)) &   \
\  (~equal(u::'a,v)) &      \
\  (~equal(w::'a,extension(u::'a,v,v,w))) --> False",
  meson_tac 1);
****************)

(*313884 inferences so far.  Searching to depth 10.  887 secs: 15 mins.*)
val GEO058_2 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>Y X. equidistant(X::'a,Y,Y,X)) &      \
\  (\\<forall>X Y Z V V2 W. equidistant(X::'a,Y,Z,V) & equidistant(X::'a,Y,V2,W) --> equidistant(Z::'a,V,V2,W)) &   \
\  (\\<forall>Z X Y. equidistant(X::'a,Y,Z,Z) --> equal(X::'a,Y)) &     \
\  (\\<forall>X Y W V. between(X::'a,Y,extension(X::'a,Y,W,V))) &       \
\  (\\<forall>X Y W V. equidistant(Y::'a,extension(X::'a,Y,W,V),W,V)) & \
\  (\\<forall>X1 Y1 X Y Z V Z1 V1. equidistant(X::'a,Y,X1,Y1) & equidistant(Y::'a,Z,Y1,Z1) & equidistant(X::'a,V,X1,V1) & equidistant(Y::'a,V,Y1,V1) & between(X::'a,Y,Z) & between(X1::'a,Y1,Z1) --> equal(X::'a,Y) | equidistant(Z::'a,V,Z1,V1)) &   \
\  (\\<forall>X Y. between(X::'a,Y,X) --> equal(X::'a,Y)) &     \
\  (\\<forall>U V W X Y. between(U::'a,V,W) & between(Y::'a,X,W) --> between(V::'a,inner_pasch(U::'a,V,W,X,Y),Y)) &     \
\  (\\<forall>V W X Y U. between(U::'a,V,W) & between(Y::'a,X,W) --> between(X::'a,inner_pasch(U::'a,V,W,X,Y),U)) &     \
\  (~between(lower_dimension_point_1::'a,lower_dimension_point_2,lower_dimension_point_3)) &        \
\  (~between(lower_dimension_point_2::'a,lower_dimension_point_3,lower_dimension_point_1)) &        \
\  (~between(lower_dimension_point_3::'a,lower_dimension_point_1,lower_dimension_point_2)) &        \
\  (\\<forall>Z X Y W V. equidistant(X::'a,W,X,V) & equidistant(Y::'a,W,Y,V) & equidistant(Z::'a,W,Z,V) --> between(X::'a,Y,Z) | between(Y::'a,Z,X) | between(Z::'a,X,Y) | equal(W::'a,V)) &     \
\  (\\<forall>U V W X Y. between(U::'a,W,Y) & between(V::'a,W,X) --> equal(U::'a,W) | between(U::'a,V,euclid1(U::'a,V,W,X,Y))) &   \
\  (\\<forall>U V W X Y. between(U::'a,W,Y) & between(V::'a,W,X) --> equal(U::'a,W) | between(U::'a,X,euclid2(U::'a,V,W,X,Y))) &   \
\  (\\<forall>U V W X Y. between(U::'a,W,Y) & between(V::'a,W,X) --> equal(U::'a,W) | between(euclid1(U::'a,V,W,X,Y),Y,euclid2(U::'a,V,W,X,Y))) &  \
\  (\\<forall>U V V1 W X X1. equidistant(U::'a,V,U,V1) & equidistant(U::'a,X,U,X1) & between(U::'a,V,X) & between(V::'a,W,X) --> between(V1::'a,continuous(U::'a,V,V1,W,X,X1),X1)) &    \
\  (\\<forall>U V V1 W X X1. equidistant(U::'a,V,U,V1) & equidistant(U::'a,X,U,X1) & between(U::'a,V,X) & between(V::'a,W,X) --> equidistant(U::'a,W,U,continuous(U::'a,V,V1,W,X,X1))) &        \
\  (\\<forall>X Y W Z. equal(X::'a,Y) & between(X::'a,W,Z) --> between(Y::'a,W,Z)) &        \
\  (\\<forall>X W Y Z. equal(X::'a,Y) & between(W::'a,X,Z) --> between(W::'a,Y,Z)) &        \
\  (\\<forall>X W Z Y. equal(X::'a,Y) & between(W::'a,Z,X) --> between(W::'a,Z,Y)) &        \
\  (\\<forall>X Y V W Z. equal(X::'a,Y) & equidistant(X::'a,V,W,Z) --> equidistant(Y::'a,V,W,Z)) &  \
\  (\\<forall>X V Y W Z. equal(X::'a,Y) & equidistant(V::'a,X,W,Z) --> equidistant(V::'a,Y,W,Z)) &  \
\  (\\<forall>X V W Y Z. equal(X::'a,Y) & equidistant(V::'a,W,X,Z) --> equidistant(V::'a,W,Y,Z)) &  \
\  (\\<forall>X V W Z Y. equal(X::'a,Y) & equidistant(V::'a,W,Z,X) --> equidistant(V::'a,W,Z,Y)) &  \
\  (\\<forall>X Y V1 V2 V3 V4. equal(X::'a,Y) --> equal(inner_pasch(X::'a,V1,V2,V3,V4),inner_pasch(Y::'a,V1,V2,V3,V4))) &   \
\  (\\<forall>X V1 Y V2 V3 V4. equal(X::'a,Y) --> equal(inner_pasch(V1::'a,X,V2,V3,V4),inner_pasch(V1::'a,Y,V2,V3,V4))) &   \
\  (\\<forall>X V1 V2 Y V3 V4. equal(X::'a,Y) --> equal(inner_pasch(V1::'a,V2,X,V3,V4),inner_pasch(V1::'a,V2,Y,V3,V4))) &   \
\  (\\<forall>X V1 V2 V3 Y V4. equal(X::'a,Y) --> equal(inner_pasch(V1::'a,V2,V3,X,V4),inner_pasch(V1::'a,V2,V3,Y,V4))) &   \
\  (\\<forall>X V1 V2 V3 V4 Y. equal(X::'a,Y) --> equal(inner_pasch(V1::'a,V2,V3,V4,X),inner_pasch(V1::'a,V2,V3,V4,Y))) &   \
\  (\\<forall>A B C D E F'. equal(A::'a,B) --> equal(euclid1(A::'a,C,D,E,F'),euclid1(B::'a,C,D,E,F'))) &    \
\  (\\<forall>G I' H J K' L. equal(G::'a,H) --> equal(euclid1(I'::'a,G,J,K',L),euclid1(I'::'a,H,J,K',L))) & \
\  (\\<forall>M O_ P N Q R. equal(M::'a,N) --> equal(euclid1(O_::'a,P,M,Q,R),euclid1(O_::'a,P,N,Q,R))) &       \
\  (\\<forall>S' U V W T' X. equal(S'::'a,T') --> equal(euclid1(U::'a,V,W,S',X),euclid1(U::'a,V,W,T',X))) & \
\  (\\<forall>Y A1 B1 C1 D1 Z. equal(Y::'a,Z) --> equal(euclid1(A1::'a,B1,C1,D1,Y),euclid1(A1::'a,B1,C1,D1,Z))) &   \
\  (\\<forall>E1 F1 G1 H1 I1 J1. equal(E1::'a,F1) --> equal(euclid2(E1::'a,G1,H1,I1,J1),euclid2(F1::'a,G1,H1,I1,J1))) &     \
\  (\\<forall>K1 M1 L1 N1 O1 P1. equal(K1::'a,L1) --> equal(euclid2(M1::'a,K1,N1,O1,P1),euclid2(M1::'a,L1,N1,O1,P1))) &     \
\  (\\<forall>Q1 S1 T1 R1 U1 V1. equal(Q1::'a,R1) --> equal(euclid2(S1::'a,T1,Q1,U1,V1),euclid2(S1::'a,T1,R1,U1,V1))) &     \
\  (\\<forall>W1 Y1 Z1 A2 X1 B2. equal(W1::'a,X1) --> equal(euclid2(Y1::'a,Z1,A2,W1,B2),euclid2(Y1::'a,Z1,A2,X1,B2))) &     \
\  (\\<forall>C2 E2 F2 G2 H2 D2. equal(C2::'a,D2) --> equal(euclid2(E2::'a,F2,G2,H2,C2),euclid2(E2::'a,F2,G2,H2,D2))) &     \
\  (\\<forall>X Y V1 V2 V3. equal(X::'a,Y) --> equal(extension(X::'a,V1,V2,V3),extension(Y::'a,V1,V2,V3))) &        \
\  (\\<forall>X V1 Y V2 V3. equal(X::'a,Y) --> equal(extension(V1::'a,X,V2,V3),extension(V1::'a,Y,V2,V3))) &        \
\  (\\<forall>X V1 V2 Y V3. equal(X::'a,Y) --> equal(extension(V1::'a,V2,X,V3),extension(V1::'a,V2,Y,V3))) &        \
\  (\\<forall>X V1 V2 V3 Y. equal(X::'a,Y) --> equal(extension(V1::'a,V2,V3,X),extension(V1::'a,V2,V3,Y))) &        \
\  (\\<forall>X Y V1 V2 V3 V4 V5. equal(X::'a,Y) --> equal(continuous(X::'a,V1,V2,V3,V4,V5),continuous(Y::'a,V1,V2,V3,V4,V5))) &    \
\  (\\<forall>X V1 Y V2 V3 V4 V5. equal(X::'a,Y) --> equal(continuous(V1::'a,X,V2,V3,V4,V5),continuous(V1::'a,Y,V2,V3,V4,V5))) &    \
\  (\\<forall>X V1 V2 Y V3 V4 V5. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,X,V3,V4,V5),continuous(V1::'a,V2,Y,V3,V4,V5))) &    \
\  (\\<forall>X V1 V2 V3 Y V4 V5. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,V3,X,V4,V5),continuous(V1::'a,V2,V3,Y,V4,V5))) &    \
\  (\\<forall>X V1 V2 V3 V4 Y V5. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,V3,V4,X,V5),continuous(V1::'a,V2,V3,V4,Y,V5))) &    \
\  (\\<forall>X V1 V2 V3 V4 V5 Y. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,V3,V4,V5,X),continuous(V1::'a,V2,V3,V4,V5,Y))) &    \
\  (\\<forall>U V. equal(reflection(U::'a,V),extension(U::'a,V,U,V))) & \
\  (\\<forall>X Y Z. equal(X::'a,Y) --> equal(reflection(X::'a,Z),reflection(Y::'a,Z))) &   \
\  (\\<forall>A1 C1 B1. equal(A1::'a,B1) --> equal(reflection(C1::'a,A1),reflection(C1::'a,B1))) &  \
\  (equal(v::'a,reflection(u::'a,v))) & \
\  (~equal(u::'a,v)) --> False",
  meson_tac 1);

(*0 inferences so far.  Searching to depth 0.  0.2 secs*)
val GEO079_1 = prove
 ("(\\<forall>U V W X Y Z. right_angle(U::'a,V,W) & right_angle(X::'a,Y,Z) --> eq(U::'a,V,W,X,Y,Z)) &       \
\  (\\<forall>U V W X Y Z. CONGRUENT(U::'a,V,W,X,Y,Z) --> eq(U::'a,V,W,X,Y,Z)) &        \
\  (\\<forall>V W U X. trapezoid(U::'a,V,W,X) --> parallel(V::'a,W,U,X)) &      \
\  (\\<forall>U V X Y. parallel(U::'a,V,X,Y) --> eq(X::'a,V,U,V,X,Y)) & \
\  (trapezoid(a::'a,b,c,d)) &       \
\  (~eq(a::'a,c,b,c,a,d)) --> False",
  meson_tac 1);

(****************SLOW
2032008 inferences so far.  Searching to depth 16.  No proof after 30 minutes.
val GRP001_1 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X. product(identity::'a,X,X)) &       \
\  (\\<forall>X. product(X::'a,identity,X)) &       \
\  (\\<forall>X. product(INVERSE(X),X,identity)) &      \
\  (\\<forall>X. product(X::'a,INVERSE(X),identity)) &      \
\  (\\<forall>X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (\\<forall>X Y Z W. product(X::'a,Y,Z) & product(X::'a,Y,W) --> equal(Z::'a,W)) &        \
\  (\\<forall>Y U Z X V W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(U::'a,Z,W) --> product(X::'a,V,W)) &       \
\  (\\<forall>Y X V U Z W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(X::'a,V,W) --> product(U::'a,Z,W)) &       \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(INVERSE(X),INVERSE(Y))) &       \
\  (\\<forall>X Y W. equal(X::'a,Y) --> equal(multiply(X::'a,W),multiply(Y::'a,W))) &       \
\  (\\<forall>X W Y. equal(X::'a,Y) --> equal(multiply(W::'a,X),multiply(W::'a,Y))) &       \
\  (\\<forall>X Y W Z. equal(X::'a,Y) & product(X::'a,W,Z) --> product(Y::'a,W,Z)) &        \
\  (\\<forall>X W Y Z. equal(X::'a,Y) & product(W::'a,X,Z) --> product(W::'a,Y,Z)) &        \
\  (\\<forall>X W Z Y. equal(X::'a,Y) & product(W::'a,Z,X) --> product(W::'a,Z,Y)) &        \
\  (\\<forall>X. product(X::'a,X,identity)) &       \
\  (product(a::'a,b,c)) &   \
\  (~product(b::'a,a,c)) --> False",
  meson_tac 1);
****************)

(*2386 inferences so far.  Searching to depth 11.  8.7 secs*)
val GRP008_1 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X. product(identity::'a,X,X)) &       \
\  (\\<forall>X. product(X::'a,identity,X)) &       \
\  (\\<forall>X. product(INVERSE(X),X,identity)) &      \
\  (\\<forall>X. product(X::'a,INVERSE(X),identity)) &      \
\  (\\<forall>X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (\\<forall>X Y Z W. product(X::'a,Y,Z) & product(X::'a,Y,W) --> equal(Z::'a,W)) &        \
\  (\\<forall>Y U Z X V W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(U::'a,Z,W) --> product(X::'a,V,W)) &       \
\  (\\<forall>Y X V U Z W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(X::'a,V,W) --> product(U::'a,Z,W)) &       \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(INVERSE(X),INVERSE(Y))) &       \
\  (\\<forall>X Y W. equal(X::'a,Y) --> equal(multiply(X::'a,W),multiply(Y::'a,W))) &       \
\  (\\<forall>X W Y. equal(X::'a,Y) --> equal(multiply(W::'a,X),multiply(W::'a,Y))) &       \
\  (\\<forall>X Y W Z. equal(X::'a,Y) & product(X::'a,W,Z) --> product(Y::'a,W,Z)) &        \
\  (\\<forall>X W Y Z. equal(X::'a,Y) & product(W::'a,X,Z) --> product(W::'a,Y,Z)) &        \
\  (\\<forall>X W Z Y. equal(X::'a,Y) & product(W::'a,Z,X) --> product(W::'a,Z,Y)) &        \
\  (\\<forall>A B. equal(A::'a,B) --> equal(h(A),h(B))) &   \
\  (\\<forall>C D. equal(C::'a,D) --> equal(j(C),j(D))) &   \
\  (\\<forall>A B. equal(A::'a,B) & q(A) --> q(B)) &        \
\  (\\<forall>B A C. q(A) & product(A::'a,B,C) --> product(B::'a,A,C)) &        \
\  (\\<forall>A. product(j(A),A,h(A)) | product(A::'a,j(A),h(A)) | q(A)) &        \
\  (\\<forall>A. product(j(A),A,h(A)) & product(A::'a,j(A),h(A)) --> q(A)) &        \
\  (~q(identity)) --> False",
  meson_tac 1);

(*8625 inferences so far.  Searching to depth 11.  20 secs*)
val GRP013_1 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X. product(identity::'a,X,X)) &       \
\  (\\<forall>X. product(X::'a,identity,X)) &       \
\  (\\<forall>X. product(INVERSE(X),X,identity)) &      \
\  (\\<forall>X. product(X::'a,INVERSE(X),identity)) &      \
\  (\\<forall>X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (\\<forall>X Y Z W. product(X::'a,Y,Z) & product(X::'a,Y,W) --> equal(Z::'a,W)) &        \
\  (\\<forall>Y U Z X V W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(U::'a,Z,W) --> product(X::'a,V,W)) &       \
\  (\\<forall>Y X V U Z W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(X::'a,V,W) --> product(U::'a,Z,W)) &       \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(INVERSE(X),INVERSE(Y))) &       \
\  (\\<forall>X Y W. equal(X::'a,Y) --> equal(multiply(X::'a,W),multiply(Y::'a,W))) &       \
\  (\\<forall>X W Y. equal(X::'a,Y) --> equal(multiply(W::'a,X),multiply(W::'a,Y))) &       \
\  (\\<forall>X Y W Z. equal(X::'a,Y) & product(X::'a,W,Z) --> product(Y::'a,W,Z)) &        \
\  (\\<forall>X W Y Z. equal(X::'a,Y) & product(W::'a,X,Z) --> product(W::'a,Y,Z)) &        \
\  (\\<forall>X W Z Y. equal(X::'a,Y) & product(W::'a,Z,X) --> product(W::'a,Z,Y)) &        \
\  (\\<forall>A. product(A::'a,A,identity)) &       \
\  (product(a::'a,b,c)) &   \
\  (product(INVERSE(a),INVERSE(b),d)) & \
\  (\\<forall>A C B. product(INVERSE(A),INVERSE(B),C) --> product(A::'a,C,B)) &     \
\  (~product(c::'a,d,identity)) --> False",
  meson_tac 1);

(*2448 inferences so far.  Searching to depth 10.  7.2 secs*)
val GRP037_3 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X. product(identity::'a,X,X)) &       \
\  (\\<forall>X. product(X::'a,identity,X)) &       \
\  (\\<forall>X. product(INVERSE(X),X,identity)) &      \
\  (\\<forall>X. product(X::'a,INVERSE(X),identity)) &      \
\  (\\<forall>X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (\\<forall>X Y Z W. product(X::'a,Y,Z) & product(X::'a,Y,W) --> equal(Z::'a,W)) &        \
\  (\\<forall>Y U Z X V W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(U::'a,Z,W) --> product(X::'a,V,W)) &       \
\  (\\<forall>Y X V U Z W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(X::'a,V,W) --> product(U::'a,Z,W)) &       \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(INVERSE(X),INVERSE(Y))) &       \
\  (\\<forall>X Y W. equal(X::'a,Y) --> equal(multiply(X::'a,W),multiply(Y::'a,W))) &       \
\  (\\<forall>X W Y. equal(X::'a,Y) --> equal(multiply(W::'a,X),multiply(W::'a,Y))) &       \
\  (\\<forall>X Y W Z. equal(X::'a,Y) & product(X::'a,W,Z) --> product(Y::'a,W,Z)) &        \
\  (\\<forall>X W Y Z. equal(X::'a,Y) & product(W::'a,X,Z) --> product(W::'a,Y,Z)) &        \
\  (\\<forall>X W Z Y. equal(X::'a,Y) & product(W::'a,Z,X) --> product(W::'a,Z,Y)) &        \
\  (\\<forall>A B C. subgroup_member(A) & subgroup_member(B) & product(A::'a,INVERSE(B),C) --> subgroup_member(C)) &        \
\  (\\<forall>A B. equal(A::'a,B) & subgroup_member(A) --> subgroup_member(B)) &    \
\  (\\<forall>A. subgroup_member(A) --> product(another_identity::'a,A,A)) &        \
\  (\\<forall>A. subgroup_member(A) --> product(A::'a,another_identity,A)) &        \
\  (\\<forall>A. subgroup_member(A) --> product(A::'a,another_inverse(A),another_identity)) &       \
\  (\\<forall>A. subgroup_member(A) --> product(another_inverse(A),A,another_identity)) &       \
\  (\\<forall>A. subgroup_member(A) --> subgroup_member(another_inverse(A))) &  \
\  (\\<forall>A B. equal(A::'a,B) --> equal(another_inverse(A),another_inverse(B))) &       \
\  (\\<forall>A C D B. product(A::'a,B,C) & product(A::'a,D,C) --> equal(D::'a,B)) &        \
\  (\\<forall>B C D A. product(A::'a,B,C) & product(D::'a,B,C) --> equal(D::'a,A)) &        \
\  (subgroup_member(a)) &       \
\  (subgroup_member(another_identity)) &        \
\  (~equal(INVERSE(a),another_inverse(a))) --> False",
  meson_tac 1);

(*163 inferences so far.  Searching to depth 11.  0.3 secs*)
val GRP031_2 = prove
 ("(\\<forall>X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (\\<forall>X Y Z W. product(X::'a,Y,Z) & product(X::'a,Y,W) --> equal(Z::'a,W)) &        \
\  (\\<forall>Y U Z X V W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(U::'a,Z,W) --> product(X::'a,V,W)) &       \
\  (\\<forall>Y X V U Z W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(X::'a,V,W) --> product(U::'a,Z,W)) &       \
\  (\\<forall>A. product(A::'a,INVERSE(A),identity)) &      \
\  (\\<forall>A. product(A::'a,identity,A)) &       \
\  (\\<forall>A. ~product(A::'a,a,identity)) --> False",
  meson_tac 1);

(*47 inferences so far.  Searching to depth 11.   0.2 secs*)
val GRP034_4 = prove
 ("(\\<forall>X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (\\<forall>X. product(identity::'a,X,X)) &       \
\  (\\<forall>X. product(X::'a,identity,X)) &       \
\  (\\<forall>X. product(X::'a,INVERSE(X),identity)) &      \
\  (\\<forall>Y U Z X V W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(U::'a,Z,W) --> product(X::'a,V,W)) &       \
\  (\\<forall>Y X V U Z W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(X::'a,V,W) --> product(U::'a,Z,W)) &       \
\  (\\<forall>B A C. subgroup_member(A) & subgroup_member(B) & product(B::'a,INVERSE(A),C) --> subgroup_member(C)) &        \
\  (subgroup_member(a)) &       \
\  (~subgroup_member(INVERSE(a))) --> False",
  meson_tac 1);

(*3287 inferences so far.  Searching to depth 14.  3.5 secs*)
val GRP047_2 = prove_hard
 ("(\\<forall>X. product(identity::'a,X,X)) &       \
\  (\\<forall>X. product(INVERSE(X),X,identity)) &      \
\  (\\<forall>X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (\\<forall>X Y Z W. product(X::'a,Y,Z) & product(X::'a,Y,W) --> equal(Z::'a,W)) &        \
\  (\\<forall>Y U Z X V W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(U::'a,Z,W) --> product(X::'a,V,W)) &       \
\  (\\<forall>Y X V U Z W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(X::'a,V,W) --> product(U::'a,Z,W)) &       \
\  (\\<forall>X W Z Y. equal(X::'a,Y) & product(W::'a,Z,X) --> product(W::'a,Z,Y)) &        \
\  (equal(a::'a,b)) &       \
\  (~equal(multiply(c::'a,a),multiply(c::'a,b))) --> False",
  meson_tac 1);

(*25559 inferences so far.  Searching to depth 19.  16.9 secs*)
val GRP130_1_002 = prove_hard
 ("(group_element(e_1)) &       \
\  (group_element(e_2)) &       \
\  (~equal(e_1::'a,e_2)) &  \
\  (~equal(e_2::'a,e_1)) &  \
\  (\\<forall>X Y. group_element(X) & group_element(Y) --> product(X::'a,Y,e_1) | product(X::'a,Y,e_2)) &      \
\  (\\<forall>X Y W Z. product(X::'a,Y,W) & product(X::'a,Y,Z) --> equal(W::'a,Z)) &        \
\  (\\<forall>X Y W Z. product(X::'a,W,Y) & product(X::'a,Z,Y) --> equal(W::'a,Z)) &        \
\  (\\<forall>Y X W Z. product(W::'a,Y,X) & product(Z::'a,Y,X) --> equal(W::'a,Z)) &        \
\  (\\<forall>Z1 Z2 Y X. product(X::'a,Y,Z1) & product(X::'a,Z1,Z2) --> product(Z2::'a,Y,X)) --> False",
  meson_tac 1);

(*3468 inferences so far.  Searching to depth 10.  9.1 secs*)
val GRP156_1 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X. equal(multiply(identity::'a,X),X)) &       \
\  (\\<forall>X. equal(multiply(INVERSE(X),X),identity)) &      \
\  (\\<forall>X Y Z. equal(multiply(multiply(X::'a,Y),Z),multiply(X::'a,multiply(Y::'a,Z)))) &      \
\  (\\<forall>A B. equal(A::'a,B) --> equal(INVERSE(A),INVERSE(B))) &       \
\  (\\<forall>C D E. equal(C::'a,D) --> equal(multiply(C::'a,E),multiply(D::'a,E))) &       \
\  (\\<forall>F' H G. equal(F'::'a,G) --> equal(multiply(H::'a,F'),multiply(H::'a,G))) &    \
\  (\\<forall>Y X. equal(greatest_lower_bound(X::'a,Y),greatest_lower_bound(Y::'a,X))) &        \
\  (\\<forall>Y X. equal(least_upper_bound(X::'a,Y),least_upper_bound(Y::'a,X))) &      \
\  (\\<forall>X Y Z. equal(greatest_lower_bound(X::'a,greatest_lower_bound(Y::'a,Z)),greatest_lower_bound(greatest_lower_bound(X::'a,Y),Z))) &      \
\  (\\<forall>X Y Z. equal(least_upper_bound(X::'a,least_upper_bound(Y::'a,Z)),least_upper_bound(least_upper_bound(X::'a,Y),Z))) &  \
\  (\\<forall>X. equal(least_upper_bound(X::'a,X),X)) &     \
\  (\\<forall>X. equal(greatest_lower_bound(X::'a,X),X)) &  \
\  (\\<forall>Y X. equal(least_upper_bound(X::'a,greatest_lower_bound(X::'a,Y)),X)) &   \
\  (\\<forall>Y X. equal(greatest_lower_bound(X::'a,least_upper_bound(X::'a,Y)),X)) &   \
\  (\\<forall>Y X Z. equal(multiply(X::'a,least_upper_bound(Y::'a,Z)),least_upper_bound(multiply(X::'a,Y),multiply(X::'a,Z)))) &        \
\  (\\<forall>Y X Z. equal(multiply(X::'a,greatest_lower_bound(Y::'a,Z)),greatest_lower_bound(multiply(X::'a,Y),multiply(X::'a,Z)))) &  \
\  (\\<forall>Y Z X. equal(multiply(least_upper_bound(Y::'a,Z),X),least_upper_bound(multiply(Y::'a,X),multiply(Z::'a,X)))) &        \
\  (\\<forall>Y Z X. equal(multiply(greatest_lower_bound(Y::'a,Z),X),greatest_lower_bound(multiply(Y::'a,X),multiply(Z::'a,X)))) &  \
\  (\\<forall>A B C. equal(A::'a,B) --> equal(greatest_lower_bound(A::'a,C),greatest_lower_bound(B::'a,C))) &       \
\  (\\<forall>A C B. equal(A::'a,B) --> equal(greatest_lower_bound(C::'a,A),greatest_lower_bound(C::'a,B))) &       \
\  (\\<forall>A B C. equal(A::'a,B) --> equal(least_upper_bound(A::'a,C),least_upper_bound(B::'a,C))) &     \
\  (\\<forall>A C B. equal(A::'a,B) --> equal(least_upper_bound(C::'a,A),least_upper_bound(C::'a,B))) &     \
\  (\\<forall>A B C. equal(A::'a,B) --> equal(multiply(A::'a,C),multiply(B::'a,C))) &       \
\  (\\<forall>A C B. equal(A::'a,B) --> equal(multiply(C::'a,A),multiply(C::'a,B))) &       \
\  (equal(least_upper_bound(a::'a,b),b)) &  \
\  (~equal(greatest_lower_bound(multiply(a::'a,c),multiply(b::'a,c)),multiply(a::'a,c))) --> False",
  meson_tac 1);

(*4394 inferences so far.  Searching to depth 10.  8.2 secs*)
val GRP168_1 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X. equal(multiply(identity::'a,X),X)) &       \
\  (\\<forall>X. equal(multiply(INVERSE(X),X),identity)) &      \
\  (\\<forall>X Y Z. equal(multiply(multiply(X::'a,Y),Z),multiply(X::'a,multiply(Y::'a,Z)))) &      \
\  (\\<forall>A B. equal(A::'a,B) --> equal(INVERSE(A),INVERSE(B))) &       \
\  (\\<forall>C D E. equal(C::'a,D) --> equal(multiply(C::'a,E),multiply(D::'a,E))) &       \
\  (\\<forall>F' H G. equal(F'::'a,G) --> equal(multiply(H::'a,F'),multiply(H::'a,G))) &    \
\  (\\<forall>Y X. equal(greatest_lower_bound(X::'a,Y),greatest_lower_bound(Y::'a,X))) &        \
\  (\\<forall>Y X. equal(least_upper_bound(X::'a,Y),least_upper_bound(Y::'a,X))) &      \
\  (\\<forall>X Y Z. equal(greatest_lower_bound(X::'a,greatest_lower_bound(Y::'a,Z)),greatest_lower_bound(greatest_lower_bound(X::'a,Y),Z))) &      \
\  (\\<forall>X Y Z. equal(least_upper_bound(X::'a,least_upper_bound(Y::'a,Z)),least_upper_bound(least_upper_bound(X::'a,Y),Z))) &  \
\  (\\<forall>X. equal(least_upper_bound(X::'a,X),X)) &     \
\  (\\<forall>X. equal(greatest_lower_bound(X::'a,X),X)) &  \
\  (\\<forall>Y X. equal(least_upper_bound(X::'a,greatest_lower_bound(X::'a,Y)),X)) &   \
\  (\\<forall>Y X. equal(greatest_lower_bound(X::'a,least_upper_bound(X::'a,Y)),X)) &   \
\  (\\<forall>Y X Z. equal(multiply(X::'a,least_upper_bound(Y::'a,Z)),least_upper_bound(multiply(X::'a,Y),multiply(X::'a,Z)))) &        \
\  (\\<forall>Y X Z. equal(multiply(X::'a,greatest_lower_bound(Y::'a,Z)),greatest_lower_bound(multiply(X::'a,Y),multiply(X::'a,Z)))) &  \
\  (\\<forall>Y Z X. equal(multiply(least_upper_bound(Y::'a,Z),X),least_upper_bound(multiply(Y::'a,X),multiply(Z::'a,X)))) &        \
\  (\\<forall>Y Z X. equal(multiply(greatest_lower_bound(Y::'a,Z),X),greatest_lower_bound(multiply(Y::'a,X),multiply(Z::'a,X)))) &  \
\  (\\<forall>A B C. equal(A::'a,B) --> equal(greatest_lower_bound(A::'a,C),greatest_lower_bound(B::'a,C))) &       \
\  (\\<forall>A C B. equal(A::'a,B) --> equal(greatest_lower_bound(C::'a,A),greatest_lower_bound(C::'a,B))) &       \
\  (\\<forall>A B C. equal(A::'a,B) --> equal(least_upper_bound(A::'a,C),least_upper_bound(B::'a,C))) &     \
\  (\\<forall>A C B. equal(A::'a,B) --> equal(least_upper_bound(C::'a,A),least_upper_bound(C::'a,B))) &     \
\  (\\<forall>A B C. equal(A::'a,B) --> equal(multiply(A::'a,C),multiply(B::'a,C))) &       \
\  (\\<forall>A C B. equal(A::'a,B) --> equal(multiply(C::'a,A),multiply(C::'a,B))) &       \
\  (equal(least_upper_bound(a::'a,b),b)) &  \
\  (~equal(least_upper_bound(multiply(INVERSE(c),multiply(a::'a,c)),multiply(INVERSE(c),multiply(b::'a,c))),multiply(INVERSE(c),multiply(b::'a,c)))) --> False",
  meson_tac 1);

(*250258 inferences so far.  Searching to depth 16.  406.2 secs*)
val HEN003_3 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X Y. less_equal(X::'a,Y) --> equal(divide(X::'a,Y),zero)) &       \
\  (\\<forall>X Y. equal(divide(X::'a,Y),zero) --> less_equal(X::'a,Y)) &       \
\  (\\<forall>Y X. less_equal(divide(X::'a,Y),X)) & \
\  (\\<forall>X Y Z. less_equal(divide(divide(X::'a,Z),divide(Y::'a,Z)),divide(divide(X::'a,Y),Z))) &       \
\  (\\<forall>X. less_equal(zero::'a,X)) &  \
\  (\\<forall>X Y. less_equal(X::'a,Y) & less_equal(Y::'a,X) --> equal(X::'a,Y)) &  \
\  (\\<forall>X. less_equal(X::'a,identity)) &      \
\  (\\<forall>A B C. equal(A::'a,B) --> equal(divide(A::'a,C),divide(B::'a,C))) &   \
\  (\\<forall>D F' E. equal(D::'a,E) --> equal(divide(F'::'a,D),divide(F'::'a,E))) &        \
\  (\\<forall>G H I'. equal(G::'a,H) & less_equal(G::'a,I') --> less_equal(H::'a,I')) &     \
\  (\\<forall>J L K'. equal(J::'a,K') & less_equal(L::'a,J) --> less_equal(L::'a,K')) &     \
\  (~equal(divide(a::'a,a),zero)) --> False",
  meson_tac 1);


(*202177 inferences so far.  Searching to depth 14.  451 secs*)
val HEN007_2 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X Y. less_equal(X::'a,Y) --> quotient(X::'a,Y,zero)) &    \
\  (\\<forall>X Y. quotient(X::'a,Y,zero) --> less_equal(X::'a,Y)) &    \
\  (\\<forall>Y Z X. quotient(X::'a,Y,Z) --> less_equal(Z::'a,X)) &     \
\  (\\<forall>Y X V3 V2 V1 Z V4 V5. quotient(X::'a,Y,V1) & quotient(Y::'a,Z,V2) & quotient(X::'a,Z,V3) & quotient(V3::'a,V2,V4) & quotient(V1::'a,Z,V5) --> less_equal(V4::'a,V5)) &    \
\  (\\<forall>X. less_equal(zero::'a,X)) &  \
\  (\\<forall>X Y. less_equal(X::'a,Y) & less_equal(Y::'a,X) --> equal(X::'a,Y)) &  \
\  (\\<forall>X. less_equal(X::'a,identity)) &      \
\  (\\<forall>X Y. quotient(X::'a,Y,divide(X::'a,Y))) & \
\  (\\<forall>X Y Z W. quotient(X::'a,Y,Z) & quotient(X::'a,Y,W) --> equal(Z::'a,W)) &      \
\  (\\<forall>X Y W Z. equal(X::'a,Y) & quotient(X::'a,W,Z) --> quotient(Y::'a,W,Z)) &      \
\  (\\<forall>X W Y Z. equal(X::'a,Y) & quotient(W::'a,X,Z) --> quotient(W::'a,Y,Z)) &      \
\  (\\<forall>X W Z Y. equal(X::'a,Y) & quotient(W::'a,Z,X) --> quotient(W::'a,Z,Y)) &      \
\  (\\<forall>X Z Y. equal(X::'a,Y) & less_equal(Z::'a,X) --> less_equal(Z::'a,Y)) &        \
\  (\\<forall>X Y Z. equal(X::'a,Y) & less_equal(X::'a,Z) --> less_equal(Y::'a,Z)) &        \
\  (\\<forall>X Y W. equal(X::'a,Y) --> equal(divide(X::'a,W),divide(Y::'a,W))) &   \
\  (\\<forall>X W Y. equal(X::'a,Y) --> equal(divide(W::'a,X),divide(W::'a,Y))) &   \
\  (\\<forall>X. quotient(X::'a,identity,zero)) &   \
\  (\\<forall>X. quotient(zero::'a,X,zero)) &       \
\  (\\<forall>X. quotient(X::'a,X,zero)) &  \
\  (\\<forall>X. quotient(X::'a,zero,X)) &  \
\  (\\<forall>Y X Z. less_equal(X::'a,Y) & less_equal(Y::'a,Z) --> less_equal(X::'a,Z)) &   \
\  (\\<forall>W1 X Z W2 Y. quotient(X::'a,Y,W1) & less_equal(W1::'a,Z) & quotient(X::'a,Z,W2) --> less_equal(W2::'a,Y)) &       \
\  (less_equal(x::'a,y)) &  \
\  (quotient(z::'a,y,zQy)) &        \
\  (quotient(z::'a,x,zQx)) &        \
\  (~less_equal(zQy::'a,zQx)) --> False",
  meson_tac 1);

(*60026 inferences so far.  Searching to depth 12.  42.2 secs*)
val HEN008_4 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X Y. less_equal(X::'a,Y) --> equal(divide(X::'a,Y),zero)) &       \
\  (\\<forall>X Y. equal(divide(X::'a,Y),zero) --> less_equal(X::'a,Y)) &       \
\  (\\<forall>Y X. less_equal(divide(X::'a,Y),X)) & \
\  (\\<forall>X Y Z. less_equal(divide(divide(X::'a,Z),divide(Y::'a,Z)),divide(divide(X::'a,Y),Z))) &       \
\  (\\<forall>X. less_equal(zero::'a,X)) &  \
\  (\\<forall>X Y. less_equal(X::'a,Y) & less_equal(Y::'a,X) --> equal(X::'a,Y)) &  \
\  (\\<forall>X. less_equal(X::'a,identity)) &      \
\  (\\<forall>A B C. equal(A::'a,B) --> equal(divide(A::'a,C),divide(B::'a,C))) &   \
\  (\\<forall>D F' E. equal(D::'a,E) --> equal(divide(F'::'a,D),divide(F'::'a,E))) &        \
\  (\\<forall>G H I'. equal(G::'a,H) & less_equal(G::'a,I') --> less_equal(H::'a,I')) &     \
\  (\\<forall>J L K'. equal(J::'a,K') & less_equal(L::'a,J) --> less_equal(L::'a,K')) &     \
\  (\\<forall>X. equal(divide(X::'a,identity),zero)) &      \
\  (\\<forall>X. equal(divide(zero::'a,X),zero)) &  \
\  (\\<forall>X. equal(divide(X::'a,X),zero)) &     \
\  (equal(divide(a::'a,zero),a)) &  \
\  (\\<forall>Y X Z. less_equal(X::'a,Y) & less_equal(Y::'a,Z) --> less_equal(X::'a,Z)) &   \
\  (\\<forall>X Z Y. less_equal(divide(X::'a,Y),Z) --> less_equal(divide(X::'a,Z),Y)) & \
\  (\\<forall>Y Z X. less_equal(X::'a,Y) --> less_equal(divide(Z::'a,Y),divide(Z::'a,X))) & \
\  (less_equal(a::'a,b)) &  \
\  (~less_equal(divide(a::'a,c),divide(b::'a,c))) --> False",
  meson_tac 1);


(*3160 inferences so far.  Searching to depth 11.  3.5 secs*)
val HEN009_5 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>Y X. equal(divide(divide(X::'a,Y),X),zero)) & \
\  (\\<forall>X Y Z. equal(divide(divide(divide(X::'a,Z),divide(Y::'a,Z)),divide(divide(X::'a,Y),Z)),zero)) &       \
\  (\\<forall>X. equal(divide(zero::'a,X),zero)) &  \
\  (\\<forall>X Y. equal(divide(X::'a,Y),zero) & equal(divide(Y::'a,X),zero) --> equal(X::'a,Y)) &  \
\  (\\<forall>X. equal(divide(X::'a,identity),zero)) &      \
\  (\\<forall>A B C. equal(A::'a,B) --> equal(divide(A::'a,C),divide(B::'a,C))) &   \
\  (\\<forall>D F' E. equal(D::'a,E) --> equal(divide(F'::'a,D),divide(F'::'a,E))) &        \
\  (\\<forall>Y X Z. equal(divide(X::'a,Y),zero) & equal(divide(Y::'a,Z),zero) --> equal(divide(X::'a,Z),zero)) &   \
\  (\\<forall>X Z Y. equal(divide(divide(X::'a,Y),Z),zero) --> equal(divide(divide(X::'a,Z),Y),zero)) & \
\  (\\<forall>Y Z X. equal(divide(X::'a,Y),zero) --> equal(divide(divide(Z::'a,Y),divide(Z::'a,X)),zero)) & \
\  (~equal(divide(identity::'a,a),divide(identity::'a,divide(identity::'a,divide(identity::'a,a))))) &  \
\  (equal(divide(identity::'a,a),b)) &      \
\  (equal(divide(identity::'a,b),c)) &      \
\  (equal(divide(identity::'a,c),d)) &      \
\  (~equal(b::'a,d)) --> False",
  meson_tac 1);

(*970373 inferences so far.  Searching to depth 17.  890.0 secs*)
val HEN012_3 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X Y. less_equal(X::'a,Y) --> equal(divide(X::'a,Y),zero)) &       \
\  (\\<forall>X Y. equal(divide(X::'a,Y),zero) --> less_equal(X::'a,Y)) &       \
\  (\\<forall>Y X. less_equal(divide(X::'a,Y),X)) & \
\  (\\<forall>X Y Z. less_equal(divide(divide(X::'a,Z),divide(Y::'a,Z)),divide(divide(X::'a,Y),Z))) &       \
\  (\\<forall>X. less_equal(zero::'a,X)) &  \
\  (\\<forall>X Y. less_equal(X::'a,Y) & less_equal(Y::'a,X) --> equal(X::'a,Y)) &  \
\  (\\<forall>X. less_equal(X::'a,identity)) &      \
\  (\\<forall>A B C. equal(A::'a,B) --> equal(divide(A::'a,C),divide(B::'a,C))) &   \
\  (\\<forall>D F' E. equal(D::'a,E) --> equal(divide(F'::'a,D),divide(F'::'a,E))) &        \
\  (\\<forall>G H I'. equal(G::'a,H) & less_equal(G::'a,I') --> less_equal(H::'a,I')) &     \
\  (\\<forall>J L K'. equal(J::'a,K') & less_equal(L::'a,J) --> less_equal(L::'a,K')) &     \
\  (~less_equal(a::'a,a)) --> False",
  meson_tac 1);


(*1063 inferences so far.  Searching to depth 20.  1.0 secs*)
val LCL010_1 = prove
 ("(\\<forall>X Y. is_a_theorem(equivalent(X::'a,Y)) & is_a_theorem(X) --> is_a_theorem(Y)) &       \
\  (\\<forall>X Z Y. is_a_theorem(equivalent(equivalent(X::'a,Y),equivalent(equivalent(X::'a,Z),equivalent(Z::'a,Y))))) &   \
\  (~is_a_theorem(equivalent(equivalent(a::'a,b),equivalent(equivalent(c::'a,b),equivalent(a::'a,c))))) --> False",
  meson_tac 1);

(*2549 inferences so far.  Searching to depth 12.  1.4 secs*)
val LCL077_2 = prove
 ("(\\<forall>X Y. is_a_theorem(implies(X,Y)) & is_a_theorem(X) --> is_a_theorem(Y)) &  \
\  (\\<forall>Y X. is_a_theorem(implies(X,implies(Y,X)))) &     \
\  (\\<forall>Y X Z. is_a_theorem(implies(implies(X,implies(Y,Z)),implies(implies(X,Y),implies(X,Z))))) &       \
\  (\\<forall>Y X. is_a_theorem(implies(implies(not(X),not(Y)),implies(Y,X)))) &        \
\  (\\<forall>X2 X1 X3. is_a_theorem(implies(X1,X2)) & is_a_theorem(implies(X2,X3)) --> is_a_theorem(implies(X1,X3))) & \
\  (~is_a_theorem(implies(not(not(a)),a))) --> False",
  meson_tac 1);

(*2036 inferences so far.  Searching to depth 20.  1.5 secs*)
val LCL082_1 = prove
 ("(\\<forall>X Y. is_a_theorem(implies(X::'a,Y)) & is_a_theorem(X) --> is_a_theorem(Y)) &  \
\  (\\<forall>Y Z U X. is_a_theorem(implies(implies(implies(X::'a,Y),Z),implies(implies(Z::'a,X),implies(U::'a,X))))) &     \
\  (~is_a_theorem(implies(a::'a,implies(b::'a,a)))) --> False",
  meson_tac 1);

(*1100 inferences so far.  Searching to depth 13.  1.0 secs*)
val LCL111_1 = prove
 ("(\\<forall>X Y. is_a_theorem(implies(X,Y)) & is_a_theorem(X) --> is_a_theorem(Y)) &  \
\  (\\<forall>Y X. is_a_theorem(implies(X,implies(Y,X)))) &     \
\  (\\<forall>Y X Z. is_a_theorem(implies(implies(X,Y),implies(implies(Y,Z),implies(X,Z))))) &  \
\  (\\<forall>Y X. is_a_theorem(implies(implies(implies(X,Y),Y),implies(implies(Y,X),X)))) &    \
\  (\\<forall>Y X. is_a_theorem(implies(implies(not(X),not(Y)),implies(Y,X)))) &        \
\  (~is_a_theorem(implies(implies(a,b),implies(implies(c,a),implies(c,b))))) --> False",
  meson_tac 1);

(*667 inferences so far.  Searching to depth 9.  1.4 secs*)
val LCL143_1 = prove
 ("(\\<forall>X. equal(X,X)) &  \
\  (\\<forall>Y X. equal(X,Y) --> equal(Y,X)) & \
\  (\\<forall>Y X Z. equal(X,Y) & equal(Y,Z) --> equal(X,Z)) &  \
\  (\\<forall>X. equal(implies(true,X),X)) &    \
\  (\\<forall>Y X Z. equal(implies(implies(X,Y),implies(implies(Y,Z),implies(X,Z))),true)) &    \
\  (\\<forall>Y X. equal(implies(implies(X,Y),Y),implies(implies(Y,X),X))) &    \
\  (\\<forall>Y X. equal(implies(implies(not(X),not(Y)),implies(Y,X)),true)) &  \
\  (\\<forall>A B C. equal(A,B) --> equal(implies(A,C),implies(B,C))) & \
\  (\\<forall>D F' E. equal(D,E) --> equal(implies(F',D),implies(F',E))) &      \
\  (\\<forall>G H. equal(G,H) --> equal(not(G),not(H))) &       \
\  (\\<forall>X Y. equal(big_V(X,Y),implies(implies(X,Y),Y))) & \
\  (\\<forall>X Y. equal(big_hat(X,Y),not(big_V(not(X),not(Y))))) &     \
\  (\\<forall>X Y. ordered(X,Y) --> equal(implies(X,Y),true)) & \
\  (\\<forall>X Y. equal(implies(X,Y),true) --> ordered(X,Y)) & \
\  (\\<forall>A B C. equal(A,B) --> equal(big_V(A,C),big_V(B,C))) &     \
\  (\\<forall>D F' E. equal(D,E) --> equal(big_V(F',D),big_V(F',E))) &  \
\  (\\<forall>G H I'. equal(G,H) --> equal(big_hat(G,I'),big_hat(H,I'))) &      \
\  (\\<forall>J L K'. equal(J,K') --> equal(big_hat(L,J),big_hat(L,K'))) &      \
\  (\\<forall>M N O_. equal(M,N) & ordered(M,O_) --> ordered(N,O_)) &      \
\  (\\<forall>P R Q. equal(P,Q) & ordered(R,P) --> ordered(R,Q)) &      \
\  (ordered(x,y)) &     \
\  (~ordered(implies(z,x),implies(z,y))) --> False",
  meson_tac 1);

(*5245 inferences so far.  Searching to depth 12.  4.6 secs*)
val LCL182_1 = prove_hard
 ("(\\<forall>A. axiom(or(not(or(A,A)),A))) &   \
\  (\\<forall>B A. axiom(or(not(A),or(B,A)))) & \
\  (\\<forall>B A. axiom(or(not(or(A,B)),or(B,A)))) &   \
\  (\\<forall>B A C. axiom(or(not(or(A,or(B,C))),or(B,or(A,C))))) &     \
\  (\\<forall>A C B. axiom(or(not(or(not(A),B)),or(not(or(C,A)),or(C,B))))) &   \
\  (\\<forall>X. axiom(X) --> theorem(X)) &     \
\  (\\<forall>X Y. axiom(or(not(Y),X)) & theorem(Y) --> theorem(X)) &   \
\  (\\<forall>X Y Z. axiom(or(not(X),Y)) & theorem(or(not(Y),Z)) --> theorem(or(not(X),Z))) &   \
\  (~theorem(or(not(or(not(p),q)),or(not(not(q)),not(p))))) --> False",
  meson_tac 1);

(*410 inferences so far.  Searching to depth 10.  0.3 secs*)
val LCL200_1 = prove
 ("(\\<forall>A. axiom(or(not(or(A,A)),A))) &   \
\  (\\<forall>B A. axiom(or(not(A),or(B,A)))) & \
\  (\\<forall>B A. axiom(or(not(or(A,B)),or(B,A)))) &   \
\  (\\<forall>B A C. axiom(or(not(or(A,or(B,C))),or(B,or(A,C))))) &     \
\  (\\<forall>A C B. axiom(or(not(or(not(A),B)),or(not(or(C,A)),or(C,B))))) &   \
\  (\\<forall>X. axiom(X) --> theorem(X)) &     \
\  (\\<forall>X Y. axiom(or(not(Y),X)) & theorem(Y) --> theorem(X)) &   \
\  (\\<forall>X Y Z. axiom(or(not(X),Y)) & theorem(or(not(Y),Z)) --> theorem(or(not(X),Z))) &   \
\  (~theorem(or(not(not(or(p,q))),not(q)))) --> False",
  meson_tac 1);

(*5849 inferences so far.  Searching to depth 12.  5.6 secs*)
val LCL215_1 = prove_hard
 ("(\\<forall>A. axiom(or(not(or(A,A)),A))) &   \
\  (\\<forall>B A. axiom(or(not(A),or(B,A)))) & \
\  (\\<forall>B A. axiom(or(not(or(A,B)),or(B,A)))) &   \
\  (\\<forall>B A C. axiom(or(not(or(A,or(B,C))),or(B,or(A,C))))) &     \
\  (\\<forall>A C B. axiom(or(not(or(not(A),B)),or(not(or(C,A)),or(C,B))))) &   \
\  (\\<forall>X. axiom(X) --> theorem(X)) &     \
\  (\\<forall>X Y. axiom(or(not(Y),X)) & theorem(Y) --> theorem(X)) &   \
\  (\\<forall>X Y Z. axiom(or(not(X),Y)) & theorem(or(not(Y),Z)) --> theorem(or(not(X),Z))) &   \
\  (~theorem(or(not(or(not(p),q)),or(not(or(p,q)),q)))) --> False",
  meson_tac 1);

(*0 secs.  Not sure that a search even starts!*)
val LCL230_2 = prove
 ("(q --> p | r) &     \
\  (~p) &       \
\  (q) &        \
\  (~r) --> False",
  meson_tac 1);

(*119585 inferences so far.  Searching to depth 14.  262.4 secs*)
val LDA003_1 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>Y X Z. equal(f(X::'a,f(Y::'a,Z)),f(f(X::'a,Y),f(X::'a,Z)))) &     \
\  (\\<forall>X Y. left(X::'a,f(X::'a,Y))) &    \
\  (\\<forall>Y X Z. left(X::'a,Y) & left(Y::'a,Z) --> left(X::'a,Z)) &     \
\  (equal(num2::'a,f(num1::'a,num1))) &  \
\  (equal(num3::'a,f(num2::'a,num1))) &  \
\  (equal(u::'a,f(num2::'a,num2))) &  \
\  (\\<forall>A B C. equal(A::'a,B) --> equal(f(A::'a,C),f(B::'a,C))) &     \
\  (\\<forall>D F' E. equal(D::'a,E) --> equal(f(F'::'a,D),f(F'::'a,E))) &  \
\  (\\<forall>G H I'. equal(G::'a,H) & left(G::'a,I') --> left(H::'a,I')) & \
\  (\\<forall>J L K'. equal(J::'a,K') & left(L::'a,J) --> left(L::'a,K')) & \
\  (~left(num3::'a,u)) --> False",
  meson_tac 1);


(*2392 inferences so far.  Searching to depth 12.  2.2 secs*)
val MSC002_1 = prove
 ("(at(something::'a,here,now)) &   \
\  (\\<forall>Place Situation. hand_at(Place::'a,Situation) --> hand_at(Place::'a,let_go(Situation))) & \
\  (\\<forall>Place Another_place Situation. hand_at(Place::'a,Situation) --> hand_at(Another_place::'a,go(Another_place::'a,Situation))) & \
\  (\\<forall>Thing Situation. ~held(Thing::'a,let_go(Situation))) &        \
\  (\\<forall>Situation Thing. at(Thing::'a,here,Situation) --> red(Thing)) &       \
\  (\\<forall>Thing Place Situation. at(Thing::'a,Place,Situation) --> at(Thing::'a,Place,let_go(Situation))) & \
\  (\\<forall>Thing Place Situation. at(Thing::'a,Place,Situation) --> at(Thing::'a,Place,pick_up(Situation))) &        \
\  (\\<forall>Thing Place Situation. at(Thing::'a,Place,Situation) --> grabbed(Thing::'a,pick_up(go(Place::'a,let_go(Situation))))) &       \
\  (\\<forall>Thing Situation. red(Thing) & put(Thing::'a,there,Situation) --> answer(Situation)) & \
\  (\\<forall>Place Thing Another_place Situation. at(Thing::'a,Place,Situation) & grabbed(Thing::'a,Situation) --> put(Thing::'a,Another_place,go(Another_place::'a,Situation))) &     \
\  (\\<forall>Thing Place Another_place Situation. at(Thing::'a,Place,Situation) --> held(Thing::'a,Situation) | at(Thing::'a,Place,go(Another_place::'a,Situation))) &        \
\  (\\<forall>One_place Thing Place Situation. hand_at(One_place::'a,Situation) & held(Thing::'a,Situation) --> at(Thing::'a,Place,go(Place::'a,Situation))) &  \
\  (\\<forall>Place Thing Situation. hand_at(Place::'a,Situation) & at(Thing::'a,Place,Situation) --> held(Thing::'a,pick_up(Situation))) & \
\  (\\<forall>Situation. ~answer(Situation)) --> False",
  meson_tac 1);

(*73 inferences so far.  Searching to depth 10.  0.2 secs*)
val MSC003_1 = prove
 ("(\\<forall>Number_of_small_parts Small_part Big_part Number_of_mid_parts Mid_part. has_parts(Big_part::'a,Number_of_mid_parts,Mid_part) --> in'(object_in(Big_part::'a,Mid_part,Small_part,Number_of_mid_parts,Number_of_small_parts),Mid_part) | has_parts(Big_part::'a,times(Number_of_mid_parts::'a,Number_of_small_parts),Small_part)) &        \
\  (\\<forall>Big_part Mid_part Number_of_mid_parts Number_of_small_parts Small_part. has_parts(Big_part::'a,Number_of_mid_parts,Mid_part) & has_parts(object_in(Big_part::'a,Mid_part,Small_part,Number_of_mid_parts,Number_of_small_parts),Number_of_small_parts,Small_part) --> has_parts(Big_part::'a,times(Number_of_mid_parts::'a,Number_of_small_parts),Small_part)) &   \
\  (in'(john::'a,boy)) &    \
\  (\\<forall>X. in'(X::'a,boy) --> in'(X::'a,human)) & \
\  (\\<forall>X. in'(X::'a,hand) --> has_parts(X::'a,num5,fingers)) &      \
\  (\\<forall>X. in'(X::'a,human) --> has_parts(X::'a,num2,arm)) & \
\  (\\<forall>X. in'(X::'a,arm) --> has_parts(X::'a,num1,hand)) &  \
\  (~has_parts(john::'a,times(num2::'a,num1),hand)) --> False",
  meson_tac 1);

(*1486 inferences so far.  Searching to depth 20.  1.2 secs*)
val MSC004_1 = prove
 ("(\\<forall>Number_of_small_parts Small_part Big_part Number_of_mid_parts Mid_part. has_parts(Big_part::'a,Number_of_mid_parts,Mid_part) --> in'(object_in(Big_part::'a,Mid_part,Small_part,Number_of_mid_parts,Number_of_small_parts),Mid_part) | has_parts(Big_part::'a,times(Number_of_mid_parts::'a,Number_of_small_parts),Small_part)) &        \
\  (\\<forall>Big_part Mid_part Number_of_mid_parts Number_of_small_parts Small_part. has_parts(Big_part::'a,Number_of_mid_parts,Mid_part) & has_parts(object_in(Big_part::'a,Mid_part,Small_part,Number_of_mid_parts,Number_of_small_parts),Number_of_small_parts,Small_part) --> has_parts(Big_part::'a,times(Number_of_mid_parts::'a,Number_of_small_parts),Small_part)) &   \
\  (in'(john::'a,boy)) &    \
\  (\\<forall>X. in'(X::'a,boy) --> in'(X::'a,human)) & \
\  (\\<forall>X. in'(X::'a,hand) --> has_parts(X::'a,num5,fingers)) &      \
\  (\\<forall>X. in'(X::'a,human) --> has_parts(X::'a,num2,arm)) & \
\  (\\<forall>X. in'(X::'a,arm) --> has_parts(X::'a,num1,hand)) &  \
\  (~has_parts(john::'a,times(times(num2::'a,num1),num5),fingers)) --> False",
  meson_tac 1);

(*100 inferences so far.  Searching to depth 12.  0.1 secs*)
val MSC005_1 = prove
 ("(value(truth::'a,truth)) &       \
\  (value(falsity::'a,falsity)) &   \
\  (\\<forall>X Y. value(X::'a,truth) & value(Y::'a,truth) --> value(xor(X::'a,Y),falsity)) &       \
\  (\\<forall>X Y. value(X::'a,truth) & value(Y::'a,falsity) --> value(xor(X::'a,Y),truth)) &       \
\  (\\<forall>X Y. value(X::'a,falsity) & value(Y::'a,truth) --> value(xor(X::'a,Y),truth)) &       \
\  (\\<forall>X Y. value(X::'a,falsity) & value(Y::'a,falsity) --> value(xor(X::'a,Y),falsity)) &   \
\  (\\<forall>Value. ~value(xor(xor(xor(xor(truth::'a,falsity),falsity),truth),falsity),Value)) --> False",
  meson_tac 1);

(*19116 inferences so far.  Searching to depth 16.  15.9 secs*)
val MSC006_1 = prove_hard
 ("(\\<forall>Y X Z. p(X::'a,Y) & p(Y::'a,Z) --> p(X::'a,Z)) &      \
\  (\\<forall>Y X Z. q(X::'a,Y) & q(Y::'a,Z) --> q(X::'a,Z)) &      \
\  (\\<forall>Y X. q(X::'a,Y) --> q(Y::'a,X)) & \
\  (\\<forall>X Y. p(X::'a,Y) | q(X::'a,Y)) &  \
\  (~p(a::'a,b)) &  \
\  (~q(c::'a,d)) --> False",
  meson_tac 1);

(*1713 inferences so far.  Searching to depth 10.  2.8 secs*)
val NUM001_1 = prove
 ("(\\<forall>A. equal(A::'a,A)) &                                                \
\  (\\<forall>B A C. equal(A::'a,B) & equal(B::'a,C) --> equal(A::'a,C)) &        \
\  (\\<forall>B A. equal(add(A::'a,B),add(B::'a,A))) &                            \
\  (\\<forall>A B C. equal(add(A::'a,add(B::'a,C)),add(add(A::'a,B),C))) &        \
\  (\\<forall>B A. equal(subtract(add(A::'a,B),B),A)) &                           \
\  (\\<forall>A B. equal(A::'a,subtract(add(A::'a,B),B))) &                       \
\  (\\<forall>A C B. equal(add(subtract(A::'a,B),C),subtract(add(A::'a,C),B))) &  \
\  (\\<forall>A C B. equal(subtract(add(A::'a,B),C),add(subtract(A::'a,C),B))) &  \
\  (\\<forall>A C B D. equal(A::'a,B) & equal(C::'a,add(A::'a,D)) --> equal(C::'a,add(B::'a,D))) &  \
\  (\\<forall>A C D B. equal(A::'a,B) & equal(C::'a,add(D::'a,A)) --> equal(C::'a,add(D::'a,B))) &  \
\  (\\<forall>A C B D. equal(A::'a,B) & equal(C::'a,subtract(A::'a,D)) --> equal(C::'a,subtract(B::'a,D))) &        \
\  (\\<forall>A C D B. equal(A::'a,B) & equal(C::'a,subtract(D::'a,A)) --> equal(C::'a,subtract(D::'a,B))) &        \
\  (~equal(add(add(a::'a,b),c),add(a::'a,add(b::'a,c)))) --> False",
  meson_tac 1);

(*20717 inferences so far.  Searching to depth 11.  13.7 secs*)
val NUM021_1 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>A. equal(add(A::'a,num0),A)) &   \
\  (\\<forall>A B. equal(add(A::'a,successor(B)),successor(add(A::'a,B)))) &    \
\  (\\<forall>A. equal(multiply(A::'a,num0),num0)) &      \
\  (\\<forall>B A. equal(multiply(A::'a,successor(B)),add(multiply(A::'a,B),A))) &      \
\  (\\<forall>A B. equal(successor(A),successor(B)) --> equal(A::'a,B)) &   \
\  (\\<forall>A B. equal(A::'a,B) --> equal(successor(A),successor(B))) &   \
\  (\\<forall>A C B. less(A::'a,B) & less(C::'a,A) --> less(C::'a,B)) &     \
\  (\\<forall>A B C. equal(add(successor(A),B),C) --> less(B::'a,C)) &      \
\  (\\<forall>A B. less(A::'a,B) --> equal(add(successor(predecessor_of_1st_minus_2nd(B::'a,A)),A),B)) &        \
\  (\\<forall>A B. divides(A::'a,B) --> less(A::'a,B) | equal(A::'a,B)) &  \
\  (\\<forall>A B. less(A::'a,B) --> divides(A::'a,B)) &        \
\  (\\<forall>A B. equal(A::'a,B) --> divides(A::'a,B)) &       \
\  (less(b::'a,c)) &        \
\  (~less(b::'a,a)) &       \
\  (divides(c::'a,a)) &     \
\  (\\<forall>A. ~equal(successor(A),num0)) --> False",
  meson_tac 1);

(*26320 inferences so far.  Searching to depth 10.  26.4 secs*)
val NUM024_1 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>A. equal(add(A::'a,num0),A)) &   \
\  (\\<forall>A B. equal(add(A::'a,successor(B)),successor(add(A::'a,B)))) &    \
\  (\\<forall>A. equal(multiply(A::'a,num0),num0)) &      \
\  (\\<forall>B A. equal(multiply(A::'a,successor(B)),add(multiply(A::'a,B),A))) &      \
\  (\\<forall>A B. equal(successor(A),successor(B)) --> equal(A::'a,B)) &   \
\  (\\<forall>A B. equal(A::'a,B) --> equal(successor(A),successor(B))) &   \
\  (\\<forall>A C B. less(A::'a,B) & less(C::'a,A) --> less(C::'a,B)) &     \
\  (\\<forall>A B C. equal(add(successor(A),B),C) --> less(B::'a,C)) &      \
\  (\\<forall>A B. less(A::'a,B) --> equal(add(successor(predecessor_of_1st_minus_2nd(B::'a,A)),A),B)) &        \
\  (\\<forall>B A. equal(add(A::'a,B),add(B::'a,A))) &  \
\  (\\<forall>B A C. equal(add(A::'a,B),add(C::'a,B)) --> equal(A::'a,C)) & \
\  (less(a::'a,a)) &        \
\  (\\<forall>A. ~equal(successor(A),num0)) --> False",
  meson_tac 1);


(*1345 inferences so far.  Searching to depth 7.  23.3 secs.  BIG*)
val NUM180_1 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X U Y. subclass(X::'a,Y) & member(U::'a,X) --> member(U::'a,Y)) &     \
\  (\\<forall>X Y. member(not_subclass_element(X::'a,Y),X) | subclass(X::'a,Y)) &      \
\  (\\<forall>X Y. member(not_subclass_element(X::'a,Y),Y) --> subclass(X::'a,Y)) &     \
\  (\\<forall>X. subclass(X::'a,universal_class)) & \
\  (\\<forall>X Y. equal(X::'a,Y) --> subclass(X::'a,Y)) &      \
\  (\\<forall>Y X. equal(X::'a,Y) --> subclass(Y::'a,X)) &      \
\  (\\<forall>X Y. subclass(X::'a,Y) & subclass(Y::'a,X) --> equal(X::'a,Y)) &      \
\  (\\<forall>X U Y. member(U::'a,unordered_pair(X::'a,Y)) --> equal(U::'a,X) | equal(U::'a,Y)) &      \
\  (\\<forall>X Y. member(X::'a,universal_class) --> member(X::'a,unordered_pair(X::'a,Y))) &       \
\  (\\<forall>X Y. member(Y::'a,universal_class) --> member(Y::'a,unordered_pair(X::'a,Y))) &       \
\  (\\<forall>X Y. member(unordered_pair(X::'a,Y),universal_class)) &       \
\  (\\<forall>X. equal(unordered_pair(X::'a,X),singleton(X))) &     \
\  (\\<forall>X Y. equal(unordered_pair(singleton(X),unordered_pair(X::'a,singleton(Y))),ordered_pair(X::'a,Y))) &      \
\  (\\<forall>V Y U X. member(ordered_pair(U::'a,V),cross_product(X::'a,Y)) --> member(U::'a,X)) &  \
\  (\\<forall>U X V Y. member(ordered_pair(U::'a,V),cross_product(X::'a,Y)) --> member(V::'a,Y)) &  \
\  (\\<forall>U V X Y. member(U::'a,X) & member(V::'a,Y) --> member(ordered_pair(U::'a,V),cross_product(X::'a,Y))) &    \
\  (\\<forall>X Y Z. member(Z::'a,cross_product(X::'a,Y)) --> equal(ordered_pair(first(Z),second(Z)),Z)) &      \
\  (subclass(element_relation::'a,cross_product(universal_class::'a,universal_class))) &        \
\  (\\<forall>X Y. member(ordered_pair(X::'a,Y),element_relation) --> member(X::'a,Y)) &        \
\  (\\<forall>X Y. member(ordered_pair(X::'a,Y),cross_product(universal_class::'a,universal_class)) & member(X::'a,Y) --> member(ordered_pair(X::'a,Y),element_relation)) &     \
\  (\\<forall>Y Z X. member(Z::'a,intersection(X::'a,Y)) --> member(Z::'a,X)) &     \
\  (\\<forall>X Z Y. member(Z::'a,intersection(X::'a,Y)) --> member(Z::'a,Y)) &     \
\  (\\<forall>Z X Y. member(Z::'a,X) & member(Z::'a,Y) --> member(Z::'a,intersection(X::'a,Y))) &       \
\  (\\<forall>Z X. ~(member(Z::'a,complement(X)) & member(Z::'a,X))) &  \
\  (\\<forall>Z X. member(Z::'a,universal_class) --> member(Z::'a,complement(X)) | member(Z::'a,X)) &      \
\  (\\<forall>X Y. equal(complement(intersection(complement(X),complement(Y))),union(X::'a,Y))) &   \
\  (\\<forall>X Y. equal(intersection(complement(intersection(X::'a,Y)),complement(intersection(complement(X),complement(Y)))),difference(X::'a,Y))) &  \
\  (\\<forall>Xr X Y. equal(intersection(Xr::'a,cross_product(X::'a,Y)),restrct(Xr::'a,X,Y))) &    \
\  (\\<forall>Xr X Y. equal(intersection(cross_product(X::'a,Y),Xr),restrct(Xr::'a,X,Y))) &    \
\  (\\<forall>Z X. ~(equal(restrct(X::'a,singleton(Z),universal_class),null_class) & member(Z::'a,domain_of(X)))) &    \
\  (\\<forall>Z X. member(Z::'a,universal_class) --> equal(restrct(X::'a,singleton(Z),universal_class),null_class) | member(Z::'a,domain_of(X))) &        \
\  (\\<forall>X. subclass(rotate(X),cross_product(cross_product(universal_class::'a,universal_class),universal_class))) &   \
\  (\\<forall>V W U X. member(ordered_pair(ordered_pair(U::'a,V),W),rotate(X)) --> member(ordered_pair(ordered_pair(V::'a,W),U),X)) &   \
\  (\\<forall>U V W X. member(ordered_pair(ordered_pair(V::'a,W),U),X) & member(ordered_pair(ordered_pair(U::'a,V),W),cross_product(cross_product(universal_class::'a,universal_class),universal_class)) --> member(ordered_pair(ordered_pair(U::'a,V),W),rotate(X))) & \
\  (\\<forall>X. subclass(flip(X),cross_product(cross_product(universal_class::'a,universal_class),universal_class))) &     \
\  (\\<forall>V U W X. member(ordered_pair(ordered_pair(U::'a,V),W),flip(X)) --> member(ordered_pair(ordered_pair(V::'a,U),W),X)) &     \
\  (\\<forall>U V W X. member(ordered_pair(ordered_pair(V::'a,U),W),X) & member(ordered_pair(ordered_pair(U::'a,V),W),cross_product(cross_product(universal_class::'a,universal_class),universal_class)) --> member(ordered_pair(ordered_pair(U::'a,V),W),flip(X))) &   \
\  (\\<forall>Y. equal(domain_of(flip(cross_product(Y::'a,universal_class))),INVERSE(Y))) & \
\  (\\<forall>Z. equal(domain_of(INVERSE(Z)),range_of(Z))) &    \
\  (\\<forall>Z X Y. equal(first(not_subclass_element(restrct(Z::'a,X,singleton(Y)),null_class)),domain(Z::'a,X,Y))) & \
\  (\\<forall>Z X Y. equal(second(not_subclass_element(restrct(Z::'a,singleton(X),Y),null_class)),rng(Z::'a,X,Y))) & \
\  (\\<forall>Xr X. equal(range_of(restrct(Xr::'a,X,universal_class)),image_(Xr::'a,X))) &      \
\  (\\<forall>X. equal(union(X::'a,singleton(X)),successor(X))) &   \
\  (subclass(successor_relation::'a,cross_product(universal_class::'a,universal_class))) &      \
\  (\\<forall>X Y. member(ordered_pair(X::'a,Y),successor_relation) --> equal(successor(X),Y)) &    \
\  (\\<forall>X Y. equal(successor(X),Y) & member(ordered_pair(X::'a,Y),cross_product(universal_class::'a,universal_class)) --> member(ordered_pair(X::'a,Y),successor_relation)) & \
\  (\\<forall>X. inductive(X) --> member(null_class::'a,X)) &       \
\  (\\<forall>X. inductive(X) --> subclass(image_(successor_relation::'a,X),X)) &    \
\  (\\<forall>X. member(null_class::'a,X) & subclass(image_(successor_relation::'a,X),X) --> inductive(X)) &     \
\  (inductive(omega)) & \
\  (\\<forall>Y. inductive(Y) --> subclass(omega::'a,Y)) &  \
\  (member(omega::'a,universal_class)) &    \
\  (\\<forall>X. equal(domain_of(restrct(element_relation::'a,universal_class,X)),sum_class(X))) & \
\  (\\<forall>X. member(X::'a,universal_class) --> member(sum_class(X),universal_class)) &  \
\  (\\<forall>X. equal(complement(image_(element_relation::'a,complement(X))),powerClass(X))) &     \
\  (\\<forall>U. member(U::'a,universal_class) --> member(powerClass(U),universal_class)) &        \
\  (\\<forall>Yr Xr. subclass(compos(Yr::'a,Xr),cross_product(universal_class::'a,universal_class))) & \
\  (\\<forall>Z Yr Xr Y. member(ordered_pair(Y::'a,Z),compos(Yr::'a,Xr)) --> member(Z::'a,image_(Yr::'a,image_(Xr::'a,singleton(Y))))) &     \
\  (\\<forall>Y Z Yr Xr. member(Z::'a,image_(Yr::'a,image_(Xr::'a,singleton(Y)))) & member(ordered_pair(Y::'a,Z),cross_product(universal_class::'a,universal_class)) --> member(ordered_pair(Y::'a,Z),compos(Yr::'a,Xr))) &  \
\  (\\<forall>X. single_valued_class(X) --> subclass(compos(X::'a,INVERSE(X)),identity_relation)) &        \
\  (\\<forall>X. subclass(compos(X::'a,INVERSE(X)),identity_relation) --> single_valued_class(X)) &        \
\  (\\<forall>Xf. function(Xf) --> subclass(Xf::'a,cross_product(universal_class::'a,universal_class))) &       \
\  (\\<forall>Xf. function(Xf) --> subclass(compos(Xf::'a,INVERSE(Xf)),identity_relation)) &       \
\  (\\<forall>Xf. subclass(Xf::'a,cross_product(universal_class::'a,universal_class)) & subclass(compos(Xf::'a,INVERSE(Xf)),identity_relation) --> function(Xf)) & \
\  (\\<forall>Xf X. function(Xf) & member(X::'a,universal_class) --> member(image_(Xf::'a,X),universal_class)) & \
\  (\\<forall>X. equal(X::'a,null_class) | member(regular(X),X)) & \
\  (\\<forall>X. equal(X::'a,null_class) | equal(intersection(X::'a,regular(X)),null_class)) & \
\  (\\<forall>Xf Y. equal(sum_class(image_(Xf::'a,singleton(Y))),apply(Xf::'a,Y))) &     \
\  (function(choice)) & \
\  (\\<forall>Y. member(Y::'a,universal_class) --> equal(Y::'a,null_class) | member(apply(choice::'a,Y),Y)) &      \
\  (\\<forall>Xf. one_to_one(Xf) --> function(Xf)) &    \
\  (\\<forall>Xf. one_to_one(Xf) --> function(INVERSE(Xf))) &   \
\  (\\<forall>Xf. function(INVERSE(Xf)) & function(Xf) --> one_to_one(Xf)) &    \
\  (equal(intersection(cross_product(universal_class::'a,universal_class),intersection(cross_product(universal_class::'a,universal_class),complement(compos(complement(element_relation),INVERSE(element_relation))))),subset_relation)) &     \
\  (equal(intersection(INVERSE(subset_relation),subset_relation),identity_relation)) &  \
\  (\\<forall>Xr. equal(complement(domain_of(intersection(Xr::'a,identity_relation))),diagonalise(Xr))) &   \
\  (\\<forall>X. equal(intersection(domain_of(X),diagonalise(compos(INVERSE(element_relation),X))),cantor(X))) &       \
\  (\\<forall>Xf. operation(Xf) --> function(Xf)) &     \
\  (\\<forall>Xf. operation(Xf) --> equal(cross_product(domain_of(domain_of(Xf)),domain_of(domain_of(Xf))),domain_of(Xf))) &    \
\  (\\<forall>Xf. operation(Xf) --> subclass(range_of(Xf),domain_of(domain_of(Xf)))) &  \
\  (\\<forall>Xf. function(Xf) & equal(cross_product(domain_of(domain_of(Xf)),domain_of(domain_of(Xf))),domain_of(Xf)) & subclass(range_of(Xf),domain_of(domain_of(Xf))) --> operation(Xf)) &   \
\  (\\<forall>Xf1 Xf2 Xh. compatible(Xh::'a,Xf1,Xf2) --> function(Xh)) &    \
\  (\\<forall>Xf2 Xf1 Xh. compatible(Xh::'a,Xf1,Xf2) --> equal(domain_of(domain_of(Xf1)),domain_of(Xh))) &  \
\  (\\<forall>Xf1 Xh Xf2. compatible(Xh::'a,Xf1,Xf2) --> subclass(range_of(Xh),domain_of(domain_of(Xf2)))) &        \
\  (\\<forall>Xh Xh1 Xf1 Xf2. function(Xh) & equal(domain_of(domain_of(Xf1)),domain_of(Xh)) & subclass(range_of(Xh),domain_of(domain_of(Xf2))) --> compatible(Xh1::'a,Xf1,Xf2)) &   \
\  (\\<forall>Xh Xf2 Xf1. homomorphism(Xh::'a,Xf1,Xf2) --> operation(Xf1)) &        \
\  (\\<forall>Xh Xf1 Xf2. homomorphism(Xh::'a,Xf1,Xf2) --> operation(Xf2)) &        \
\  (\\<forall>Xh Xf1 Xf2. homomorphism(Xh::'a,Xf1,Xf2) --> compatible(Xh::'a,Xf1,Xf2)) &        \
\  (\\<forall>Xf2 Xh Xf1 X Y. homomorphism(Xh::'a,Xf1,Xf2) & member(ordered_pair(X::'a,Y),domain_of(Xf1)) --> equal(apply(Xf2::'a,ordered_pair(apply(Xh::'a,X),apply(Xh::'a,Y))),apply(Xh::'a,apply(Xf1::'a,ordered_pair(X::'a,Y))))) & \
\  (\\<forall>Xh Xf1 Xf2. operation(Xf1) & operation(Xf2) & compatible(Xh::'a,Xf1,Xf2) --> member(ordered_pair(not_homomorphism1(Xh::'a,Xf1,Xf2),not_homomorphism2(Xh::'a,Xf1,Xf2)),domain_of(Xf1)) | homomorphism(Xh::'a,Xf1,Xf2)) &  \
\  (\\<forall>Xh Xf1 Xf2. operation(Xf1) & operation(Xf2) & compatible(Xh::'a,Xf1,Xf2) & equal(apply(Xf2::'a,ordered_pair(apply(Xh::'a,not_homomorphism1(Xh::'a,Xf1,Xf2)),apply(Xh::'a,not_homomorphism2(Xh::'a,Xf1,Xf2)))),apply(Xh::'a,apply(Xf1::'a,ordered_pair(not_homomorphism1(Xh::'a,Xf1,Xf2),not_homomorphism2(Xh::'a,Xf1,Xf2))))) --> homomorphism(Xh::'a,Xf1,Xf2)) &     \
\  (\\<forall>D E F'. equal(D::'a,E) --> equal(apply(D::'a,F'),apply(E::'a,F'))) &  \
\  (\\<forall>G I' H. equal(G::'a,H) --> equal(apply(I'::'a,G),apply(I'::'a,H))) &  \
\  (\\<forall>J K'. equal(J::'a,K') --> equal(cantor(J),cantor(K'))) &      \
\  (\\<forall>L M. equal(L::'a,M) --> equal(complement(L),complement(M))) & \
\  (\\<forall>N O_ P. equal(N::'a,O_) --> equal(compos(N::'a,P),compos(O_::'a,P))) & \
\  (\\<forall>Q S' R. equal(Q::'a,R) --> equal(compos(S'::'a,Q),compos(S'::'a,R))) &      \
\  (\\<forall>T' U V. equal(T'::'a,U) --> equal(cross_product(T'::'a,V),cross_product(U::'a,V))) &  \
\  (\\<forall>W Y X. equal(W::'a,X) --> equal(cross_product(Y::'a,W),cross_product(Y::'a,X))) &     \
\  (\\<forall>Z A1. equal(Z::'a,A1) --> equal(diagonalise(Z),diagonalise(A1))) &    \
\  (\\<forall>B1 C1 D1. equal(B1::'a,C1) --> equal(difference(B1::'a,D1),difference(C1::'a,D1))) &  \
\  (\\<forall>E1 G1 F1. equal(E1::'a,F1) --> equal(difference(G1::'a,E1),difference(G1::'a,F1))) &  \
\  (\\<forall>H1 I1 J1 K1. equal(H1::'a,I1) --> equal(domain(H1::'a,J1,K1),domain(I1::'a,J1,K1))) & \
\  (\\<forall>L1 N1 M1 O1. equal(L1::'a,M1) --> equal(domain(N1::'a,L1,O1),domain(N1::'a,M1,O1))) & \
\  (\\<forall>P1 R1 S1 Q1. equal(P1::'a,Q1) --> equal(domain(R1::'a,S1,P1),domain(R1::'a,S1,Q1))) & \
\  (\\<forall>T1 U1. equal(T1::'a,U1) --> equal(domain_of(T1),domain_of(U1))) &     \
\  (\\<forall>V1 W1. equal(V1::'a,W1) --> equal(first(V1),first(W1))) &     \
\  (\\<forall>X1 Y1. equal(X1::'a,Y1) --> equal(flip(X1),flip(Y1))) &       \
\  (\\<forall>Z1 A2 B2. equal(Z1::'a,A2) --> equal(image_(Z1::'a,B2),image_(A2::'a,B2))) &    \
\  (\\<forall>C2 E2 D2. equal(C2::'a,D2) --> equal(image_(E2::'a,C2),image_(E2::'a,D2))) &    \
\  (\\<forall>F2 G2 H2. equal(F2::'a,G2) --> equal(intersection(F2::'a,H2),intersection(G2::'a,H2))) &      \
\  (\\<forall>I2 K2 J2. equal(I2::'a,J2) --> equal(intersection(K2::'a,I2),intersection(K2::'a,J2))) &      \
\  (\\<forall>L2 M2. equal(L2::'a,M2) --> equal(INVERSE(L2),INVERSE(M2))) & \
\  (\\<forall>N2 O2 P2 Q2. equal(N2::'a,O2) --> equal(not_homomorphism1(N2::'a,P2,Q2),not_homomorphism1(O2::'a,P2,Q2))) &   \
\  (\\<forall>R2 T2 S2 U2. equal(R2::'a,S2) --> equal(not_homomorphism1(T2::'a,R2,U2),not_homomorphism1(T2::'a,S2,U2))) &   \
\  (\\<forall>V2 X2 Y2 W2. equal(V2::'a,W2) --> equal(not_homomorphism1(X2::'a,Y2,V2),not_homomorphism1(X2::'a,Y2,W2))) &   \
\  (\\<forall>Z2 A3 B3 C3. equal(Z2::'a,A3) --> equal(not_homomorphism2(Z2::'a,B3,C3),not_homomorphism2(A3::'a,B3,C3))) &   \
\  (\\<forall>D3 F3 E3 G3. equal(D3::'a,E3) --> equal(not_homomorphism2(F3::'a,D3,G3),not_homomorphism2(F3::'a,E3,G3))) &   \
\  (\\<forall>H3 J3 K3 I3. equal(H3::'a,I3) --> equal(not_homomorphism2(J3::'a,K3,H3),not_homomorphism2(J3::'a,K3,I3))) &   \
\  (\\<forall>L3 M3 N3. equal(L3::'a,M3) --> equal(not_subclass_element(L3::'a,N3),not_subclass_element(M3::'a,N3))) &      \
\  (\\<forall>O3 Q3 P3. equal(O3::'a,P3) --> equal(not_subclass_element(Q3::'a,O3),not_subclass_element(Q3::'a,P3))) &      \
\  (\\<forall>R3 S3 T3. equal(R3::'a,S3) --> equal(ordered_pair(R3::'a,T3),ordered_pair(S3::'a,T3))) &      \
\  (\\<forall>U3 W3 V3. equal(U3::'a,V3) --> equal(ordered_pair(W3::'a,U3),ordered_pair(W3::'a,V3))) &      \
\  (\\<forall>X3 Y3. equal(X3::'a,Y3) --> equal(powerClass(X3),powerClass(Y3))) & \
\  (\\<forall>Z3 A4 B4 C4. equal(Z3::'a,A4) --> equal(rng(Z3::'a,B4,C4),rng(A4::'a,B4,C4))) &   \
\  (\\<forall>D4 F4 E4 G4. equal(D4::'a,E4) --> equal(rng(F4::'a,D4,G4),rng(F4::'a,E4,G4))) &   \
\  (\\<forall>H4 J4 K4 I4. equal(H4::'a,I4) --> equal(rng(J4::'a,K4,H4),rng(J4::'a,K4,I4))) &   \
\  (\\<forall>L4 M4. equal(L4::'a,M4) --> equal(range_of(L4),range_of(M4))) &       \
\  (\\<forall>N4 O4. equal(N4::'a,O4) --> equal(regular(N4),regular(O4))) & \
\  (\\<forall>P4 Q4 R4 S4. equal(P4::'a,Q4) --> equal(restrct(P4::'a,R4,S4),restrct(Q4::'a,R4,S4))) &     \
\  (\\<forall>T4 V4 U4 W4. equal(T4::'a,U4) --> equal(restrct(V4::'a,T4,W4),restrct(V4::'a,U4,W4))) &     \
\  (\\<forall>X4 Z4 A5 Y4. equal(X4::'a,Y4) --> equal(restrct(Z4::'a,A5,X4),restrct(Z4::'a,A5,Y4))) &     \
\  (\\<forall>B5 C5. equal(B5::'a,C5) --> equal(rotate(B5),rotate(C5))) &   \
\  (\\<forall>D5 E5. equal(D5::'a,E5) --> equal(second(D5),second(E5))) &   \
\  (\\<forall>F5 G5. equal(F5::'a,G5) --> equal(singleton(F5),singleton(G5))) &     \
\  (\\<forall>H5 I5. equal(H5::'a,I5) --> equal(successor(H5),successor(I5))) &     \
\  (\\<forall>J5 K5. equal(J5::'a,K5) --> equal(sum_class(J5),sum_class(K5))) &     \
\  (\\<forall>L5 M5 N5. equal(L5::'a,M5) --> equal(union(L5::'a,N5),union(M5::'a,N5))) &    \
\  (\\<forall>O5 Q5 P5. equal(O5::'a,P5) --> equal(union(Q5::'a,O5),union(Q5::'a,P5))) &    \
\  (\\<forall>R5 S5 T5. equal(R5::'a,S5) --> equal(unordered_pair(R5::'a,T5),unordered_pair(S5::'a,T5))) &  \
\  (\\<forall>U5 W5 V5. equal(U5::'a,V5) --> equal(unordered_pair(W5::'a,U5),unordered_pair(W5::'a,V5))) &  \
\  (\\<forall>X5 Y5 Z5 A6. equal(X5::'a,Y5) & compatible(X5::'a,Z5,A6) --> compatible(Y5::'a,Z5,A6)) &      \
\  (\\<forall>B6 D6 C6 E6. equal(B6::'a,C6) & compatible(D6::'a,B6,E6) --> compatible(D6::'a,C6,E6)) &      \
\  (\\<forall>F6 H6 I6 G6. equal(F6::'a,G6) & compatible(H6::'a,I6,F6) --> compatible(H6::'a,I6,G6)) &      \
\  (\\<forall>J6 K6. equal(J6::'a,K6) & function(J6) --> function(K6)) &    \
\  (\\<forall>L6 M6 N6 O6. equal(L6::'a,M6) & homomorphism(L6::'a,N6,O6) --> homomorphism(M6::'a,N6,O6)) &  \
\  (\\<forall>P6 R6 Q6 S6. equal(P6::'a,Q6) & homomorphism(R6::'a,P6,S6) --> homomorphism(R6::'a,Q6,S6)) &  \
\  (\\<forall>T6 V6 W6 U6. equal(T6::'a,U6) & homomorphism(V6::'a,W6,T6) --> homomorphism(V6::'a,W6,U6)) &  \
\  (\\<forall>X6 Y6. equal(X6::'a,Y6) & inductive(X6) --> inductive(Y6)) &  \
\  (\\<forall>Z6 A7 B7. equal(Z6::'a,A7) & member(Z6::'a,B7) --> member(A7::'a,B7)) &       \
\  (\\<forall>C7 E7 D7. equal(C7::'a,D7) & member(E7::'a,C7) --> member(E7::'a,D7)) &       \
\  (\\<forall>F7 G7. equal(F7::'a,G7) & one_to_one(F7) --> one_to_one(G7)) &        \
\  (\\<forall>H7 I7. equal(H7::'a,I7) & operation(H7) --> operation(I7)) &  \
\  (\\<forall>J7 K7. equal(J7::'a,K7) & single_valued_class(J7) --> single_valued_class(K7)) &      \
\  (\\<forall>L7 M7 N7. equal(L7::'a,M7) & subclass(L7::'a,N7) --> subclass(M7::'a,N7)) &   \
\  (\\<forall>O7 Q7 P7. equal(O7::'a,P7) & subclass(Q7::'a,O7) --> subclass(Q7::'a,P7)) &   \
\  (\\<forall>X. subclass(compose_class(X),cross_product(universal_class::'a,universal_class))) &   \
\  (\\<forall>X Y Z. member(ordered_pair(Y::'a,Z),compose_class(X)) --> equal(compos(X::'a,Y),Z)) &    \
\  (\\<forall>Y Z X. member(ordered_pair(Y::'a,Z),cross_product(universal_class::'a,universal_class)) & equal(compos(X::'a,Y),Z) --> member(ordered_pair(Y::'a,Z),compose_class(X))) & \
\  (subclass(composition_function::'a,cross_product(universal_class::'a,cross_product(universal_class::'a,universal_class)))) &     \
\  (\\<forall>X Y Z. member(ordered_pair(X::'a,ordered_pair(Y::'a,Z)),composition_function) --> equal(compos(X::'a,Y),Z)) &        \
\  (\\<forall>X Y. member(ordered_pair(X::'a,Y),cross_product(universal_class::'a,universal_class)) --> member(ordered_pair(X::'a,ordered_pair(Y::'a,compos(X::'a,Y))),composition_function)) &    \
\  (subclass(domain_relation::'a,cross_product(universal_class::'a,universal_class))) & \
\  (\\<forall>X Y. member(ordered_pair(X::'a,Y),domain_relation) --> equal(domain_of(X),Y)) &       \
\  (\\<forall>X. member(X::'a,universal_class) --> member(ordered_pair(X::'a,domain_of(X)),domain_relation)) &  \
\  (\\<forall>X. equal(first(not_subclass_element(compos(X::'a,INVERSE(X)),identity_relation)),single_valued1(X))) &       \
\  (\\<forall>X. equal(second(not_subclass_element(compos(X::'a,INVERSE(X)),identity_relation)),single_valued2(X))) &      \
\  (\\<forall>X. equal(domain(X::'a,image_(INVERSE(X),singleton(single_valued1(X))),single_valued2(X)),single_valued3(X))) & \
\  (equal(intersection(complement(compos(element_relation::'a,complement(identity_relation))),element_relation),singleton_relation)) &     \
\  (subclass(application_function::'a,cross_product(universal_class::'a,cross_product(universal_class::'a,universal_class)))) &     \
\  (\\<forall>Z Y X. member(ordered_pair(X::'a,ordered_pair(Y::'a,Z)),application_function) --> member(Y::'a,domain_of(X))) &       \
\  (\\<forall>X Y Z. member(ordered_pair(X::'a,ordered_pair(Y::'a,Z)),application_function) --> equal(apply(X::'a,Y),Z)) &  \
\  (\\<forall>Z X Y. member(ordered_pair(X::'a,ordered_pair(Y::'a,Z)),cross_product(universal_class::'a,cross_product(universal_class::'a,universal_class))) & member(Y::'a,domain_of(X)) --> member(ordered_pair(X::'a,ordered_pair(Y::'a,apply(X::'a,Y))),application_function)) &    \
\  (\\<forall>X Y Xf. maps(Xf::'a,X,Y) --> function(Xf)) &  \
\  (\\<forall>Y Xf X. maps(Xf::'a,X,Y) --> equal(domain_of(Xf),X)) &        \
\  (\\<forall>X Xf Y. maps(Xf::'a,X,Y) --> subclass(range_of(Xf),Y)) &      \
\  (\\<forall>Xf Y. function(Xf) & subclass(range_of(Xf),Y) --> maps(Xf::'a,domain_of(Xf),Y)) &     \
\  (\\<forall>L M. equal(L::'a,M) --> equal(compose_class(L),compose_class(M))) &   \
\  (\\<forall>N2 O2. equal(N2::'a,O2) --> equal(single_valued1(N2),single_valued1(O2))) &   \
\  (\\<forall>P2 Q2. equal(P2::'a,Q2) --> equal(single_valued2(P2),single_valued2(Q2))) &   \
\  (\\<forall>R2 S2. equal(R2::'a,S2) --> equal(single_valued3(R2),single_valued3(S2))) &   \
\  (\\<forall>X2 Y2 Z2 A3. equal(X2::'a,Y2) & maps(X2::'a,Z2,A3) --> maps(Y2::'a,Z2,A3)) &  \
\  (\\<forall>B3 D3 C3 E3. equal(B3::'a,C3) & maps(D3::'a,B3,E3) --> maps(D3::'a,C3,E3)) &  \
\  (\\<forall>F3 H3 I3 G3. equal(F3::'a,G3) & maps(H3::'a,I3,F3) --> maps(H3::'a,I3,G3)) &  \
\  (\\<forall>X. equal(union(X::'a,INVERSE(X)),symmetrization_of(X))) &     \
\  (\\<forall>X Y. irreflexive(X::'a,Y) --> subclass(restrct(X::'a,Y,Y),complement(identity_relation))) &      \
\  (\\<forall>X Y. subclass(restrct(X::'a,Y,Y),complement(identity_relation)) --> irreflexive(X::'a,Y)) &      \
\  (\\<forall>Y X. connected(X::'a,Y) --> subclass(cross_product(Y::'a,Y),union(identity_relation::'a,symmetrization_of(X)))) &     \
\  (\\<forall>X Y. subclass(cross_product(Y::'a,Y),union(identity_relation::'a,symmetrization_of(X))) --> connected(X::'a,Y)) &     \
\  (\\<forall>Xr Y. transitive(Xr::'a,Y) --> subclass(compos(restrct(Xr::'a,Y,Y),restrct(Xr::'a,Y,Y)),restrct(Xr::'a,Y,Y))) &       \
\  (\\<forall>Xr Y. subclass(compos(restrct(Xr::'a,Y,Y),restrct(Xr::'a,Y,Y)),restrct(Xr::'a,Y,Y)) --> transitive(Xr::'a,Y)) &       \
\  (\\<forall>Xr Y. asymmetric(Xr::'a,Y) --> equal(restrct(intersection(Xr::'a,INVERSE(Xr)),Y,Y),null_class)) &        \
\  (\\<forall>Xr Y. equal(restrct(intersection(Xr::'a,INVERSE(Xr)),Y,Y),null_class) --> asymmetric(Xr::'a,Y)) &        \
\  (\\<forall>Xr Y Z. equal(segment(Xr::'a,Y,Z),domain_of(restrct(Xr::'a,Y,singleton(Z))))) &  \
\  (\\<forall>X Y. well_ordering(X::'a,Y) --> connected(X::'a,Y)) &     \
\  (\\<forall>Y Xr U. well_ordering(Xr::'a,Y) & subclass(U::'a,Y) --> equal(U::'a,null_class) | member(least(Xr::'a,U),U)) &   \
\  (\\<forall>Y V Xr U. well_ordering(Xr::'a,Y) & subclass(U::'a,Y) & member(V::'a,U) --> member(least(Xr::'a,U),U)) &  \
\  (\\<forall>Y Xr U. well_ordering(Xr::'a,Y) & subclass(U::'a,Y) --> equal(segment(Xr::'a,U,least(Xr::'a,U)),null_class)) &    \
\  (\\<forall>Y V U Xr. ~(well_ordering(Xr::'a,Y) & subclass(U::'a,Y) & member(V::'a,U) & member(ordered_pair(V::'a,least(Xr::'a,U)),Xr))) &        \
\  (\\<forall>Xr Y. connected(Xr::'a,Y) & equal(not_well_ordering(Xr::'a,Y),null_class) --> well_ordering(Xr::'a,Y)) &      \
\  (\\<forall>Xr Y. connected(Xr::'a,Y) --> subclass(not_well_ordering(Xr::'a,Y),Y) | well_ordering(Xr::'a,Y)) &   \
\  (\\<forall>V Xr Y. member(V::'a,not_well_ordering(Xr::'a,Y)) & equal(segment(Xr::'a,not_well_ordering(Xr::'a,Y),V),null_class) & connected(Xr::'a,Y) --> well_ordering(Xr::'a,Y)) &  \
\  (\\<forall>Xr Y Z. section(Xr::'a,Y,Z) --> subclass(Y::'a,Z)) &      \
\  (\\<forall>Xr Z Y. section(Xr::'a,Y,Z) --> subclass(domain_of(restrct(Xr::'a,Z,Y)),Y)) &    \
\  (\\<forall>Xr Y Z. subclass(Y::'a,Z) & subclass(domain_of(restrct(Xr::'a,Z,Y)),Y) --> section(Xr::'a,Y,Z)) &    \
\  (\\<forall>X. member(X::'a,ordinal_numbers) --> well_ordering(element_relation::'a,X)) &     \
\  (\\<forall>X. member(X::'a,ordinal_numbers) --> subclass(sum_class(X),X)) &      \
\  (\\<forall>X. well_ordering(element_relation::'a,X) & subclass(sum_class(X),X) & member(X::'a,universal_class) --> member(X::'a,ordinal_numbers)) &      \
\  (\\<forall>X. well_ordering(element_relation::'a,X) & subclass(sum_class(X),X) --> member(X::'a,ordinal_numbers) | equal(X::'a,ordinal_numbers)) &      \
\  (equal(union(singleton(null_class),image_(successor_relation::'a,ordinal_numbers)),kind_1_ordinals)) &    \
\  (equal(intersection(complement(kind_1_ordinals),ordinal_numbers),limit_ordinals)) &  \
\  (\\<forall>X. subclass(rest_of(X),cross_product(universal_class::'a,universal_class))) & \
\  (\\<forall>V U X. member(ordered_pair(U::'a,V),rest_of(X)) --> member(U::'a,domain_of(X))) & \
\  (\\<forall>X U V. member(ordered_pair(U::'a,V),rest_of(X)) --> equal(restrct(X::'a,U,universal_class),V)) & \
\  (\\<forall>U V X. member(U::'a,domain_of(X)) & equal(restrct(X::'a,U,universal_class),V) --> member(ordered_pair(U::'a,V),rest_of(X))) &        \
\  (subclass(rest_relation::'a,cross_product(universal_class::'a,universal_class))) &   \
\  (\\<forall>X Y. member(ordered_pair(X::'a,Y),rest_relation) --> equal(rest_of(X),Y)) &   \
\  (\\<forall>X. member(X::'a,universal_class) --> member(ordered_pair(X::'a,rest_of(X)),rest_relation)) &      \
\  (\\<forall>X Z. member(X::'a,recursion_equation_functions(Z)) --> function(Z)) & \
\  (\\<forall>Z X. member(X::'a,recursion_equation_functions(Z)) --> function(X)) & \
\  (\\<forall>Z X. member(X::'a,recursion_equation_functions(Z)) --> member(domain_of(X),ordinal_numbers)) &        \
\  (\\<forall>Z X. member(X::'a,recursion_equation_functions(Z)) --> equal(compos(Z::'a,rest_of(X)),X)) &      \
\  (\\<forall>X Z. function(Z) & function(X) & member(domain_of(X),ordinal_numbers) & equal(compos(Z::'a,rest_of(X)),X) --> member(X::'a,recursion_equation_functions(Z))) &   \
\  (subclass(union_of_range_map::'a,cross_product(universal_class::'a,universal_class))) &      \
\  (\\<forall>X Y. member(ordered_pair(X::'a,Y),union_of_range_map) --> equal(sum_class(range_of(X)),Y)) &  \
\  (\\<forall>X Y. member(ordered_pair(X::'a,Y),cross_product(universal_class::'a,universal_class)) & equal(sum_class(range_of(X)),Y) --> member(ordered_pair(X::'a,Y),union_of_range_map)) &       \
\  (\\<forall>X Y. equal(apply(recursion(X::'a,successor_relation,union_of_range_map),Y),ordinal_add(X::'a,Y))) &       \
\  (\\<forall>X Y. equal(recursion(null_class::'a,apply(add_relation::'a,X),union_of_range_map),ordinal_multiply(X::'a,Y))) &       \
\  (\\<forall>X. member(X::'a,omega) --> equal(integer_of(X),X)) &  \
\  (\\<forall>X. member(X::'a,omega) | equal(integer_of(X),null_class)) &  \
\  (\\<forall>D E. equal(D::'a,E) --> equal(integer_of(D),integer_of(E))) & \
\  (\\<forall>F' G H. equal(F'::'a,G) --> equal(least(F'::'a,H),least(G::'a,H))) &  \
\  (\\<forall>I' K' J. equal(I'::'a,J) --> equal(least(K'::'a,I'),least(K'::'a,J))) &       \
\  (\\<forall>L M N. equal(L::'a,M) --> equal(not_well_ordering(L::'a,N),not_well_ordering(M::'a,N))) &     \
\  (\\<forall>O_ Q P. equal(O_::'a,P) --> equal(not_well_ordering(Q::'a,O_),not_well_ordering(Q::'a,P))) &     \
\  (\\<forall>R S' T'. equal(R::'a,S') --> equal(ordinal_add(R::'a,T'),ordinal_add(S'::'a,T'))) &   \
\  (\\<forall>U W V. equal(U::'a,V) --> equal(ordinal_add(W::'a,U),ordinal_add(W::'a,V))) & \
\  (\\<forall>X Y Z. equal(X::'a,Y) --> equal(ordinal_multiply(X::'a,Z),ordinal_multiply(Y::'a,Z))) &       \
\  (\\<forall>A1 C1 B1. equal(A1::'a,B1) --> equal(ordinal_multiply(C1::'a,A1),ordinal_multiply(C1::'a,B1))) &      \
\  (\\<forall>F1 G1 H1 I1. equal(F1::'a,G1) --> equal(recursion(F1::'a,H1,I1),recursion(G1::'a,H1,I1))) &   \
\  (\\<forall>J1 L1 K1 M1. equal(J1::'a,K1) --> equal(recursion(L1::'a,J1,M1),recursion(L1::'a,K1,M1))) &   \
\  (\\<forall>N1 P1 Q1 O1. equal(N1::'a,O1) --> equal(recursion(P1::'a,Q1,N1),recursion(P1::'a,Q1,O1))) &   \
\  (\\<forall>R1 S1. equal(R1::'a,S1) --> equal(recursion_equation_functions(R1),recursion_equation_functions(S1))) &       \
\  (\\<forall>T1 U1. equal(T1::'a,U1) --> equal(rest_of(T1),rest_of(U1))) & \
\  (\\<forall>V1 W1 X1 Y1. equal(V1::'a,W1) --> equal(segment(V1::'a,X1,Y1),segment(W1::'a,X1,Y1))) &       \
\  (\\<forall>Z1 B2 A2 C2. equal(Z1::'a,A2) --> equal(segment(B2::'a,Z1,C2),segment(B2::'a,A2,C2))) &       \
\  (\\<forall>D2 F2 G2 E2. equal(D2::'a,E2) --> equal(segment(F2::'a,G2,D2),segment(F2::'a,G2,E2))) &       \
\  (\\<forall>H2 I2. equal(H2::'a,I2) --> equal(symmetrization_of(H2),symmetrization_of(I2))) &     \
\  (\\<forall>J2 K2 L2. equal(J2::'a,K2) & asymmetric(J2::'a,L2) --> asymmetric(K2::'a,L2)) &       \
\  (\\<forall>M2 O2 N2. equal(M2::'a,N2) & asymmetric(O2::'a,M2) --> asymmetric(O2::'a,N2)) &       \
\  (\\<forall>P2 Q2 R2. equal(P2::'a,Q2) & connected(P2::'a,R2) --> connected(Q2::'a,R2)) & \
\  (\\<forall>S2 U2 T2. equal(S2::'a,T2) & connected(U2::'a,S2) --> connected(U2::'a,T2)) & \
\  (\\<forall>V2 W2 X2. equal(V2::'a,W2) & irreflexive(V2::'a,X2) --> irreflexive(W2::'a,X2)) &     \
\  (\\<forall>Y2 A3 Z2. equal(Y2::'a,Z2) & irreflexive(A3::'a,Y2) --> irreflexive(A3::'a,Z2)) &     \
\  (\\<forall>B3 C3 D3 E3. equal(B3::'a,C3) & section(B3::'a,D3,E3) --> section(C3::'a,D3,E3)) &    \
\  (\\<forall>F3 H3 G3 I3. equal(F3::'a,G3) & section(H3::'a,F3,I3) --> section(H3::'a,G3,I3)) &    \
\  (\\<forall>J3 L3 M3 K3. equal(J3::'a,K3) & section(L3::'a,M3,J3) --> section(L3::'a,M3,K3)) &    \
\  (\\<forall>N3 O3 P3. equal(N3::'a,O3) & transitive(N3::'a,P3) --> transitive(O3::'a,P3)) &       \
\  (\\<forall>Q3 S3 R3. equal(Q3::'a,R3) & transitive(S3::'a,Q3) --> transitive(S3::'a,R3)) &       \
\  (\\<forall>T3 U3 V3. equal(T3::'a,U3) & well_ordering(T3::'a,V3) --> well_ordering(U3::'a,V3)) & \
\  (\\<forall>W3 Y3 X3. equal(W3::'a,X3) & well_ordering(Y3::'a,W3) --> well_ordering(Y3::'a,X3)) & \
\  (~subclass(limit_ordinals::'a,ordinal_numbers)) --> False",
  meson_tac 1);


(*0 inferences so far.  Searching to depth 0.  16.8 secs.  BIG*)
val NUM228_1 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X U Y. subclass(X::'a,Y) & member(U::'a,X) --> member(U::'a,Y)) &     \
\  (\\<forall>X Y. member(not_subclass_element(X::'a,Y),X) | subclass(X::'a,Y)) &      \
\  (\\<forall>X Y. member(not_subclass_element(X::'a,Y),Y) --> subclass(X::'a,Y)) &     \
\  (\\<forall>X. subclass(X::'a,universal_class)) & \
\  (\\<forall>X Y. equal(X::'a,Y) --> subclass(X::'a,Y)) &      \
\  (\\<forall>Y X. equal(X::'a,Y) --> subclass(Y::'a,X)) &      \
\  (\\<forall>X Y. subclass(X::'a,Y) & subclass(Y::'a,X) --> equal(X::'a,Y)) &      \
\  (\\<forall>X U Y. member(U::'a,unordered_pair(X::'a,Y)) --> equal(U::'a,X) | equal(U::'a,Y)) &      \
\  (\\<forall>X Y. member(X::'a,universal_class) --> member(X::'a,unordered_pair(X::'a,Y))) &       \
\  (\\<forall>X Y. member(Y::'a,universal_class) --> member(Y::'a,unordered_pair(X::'a,Y))) &       \
\  (\\<forall>X Y. member(unordered_pair(X::'a,Y),universal_class)) &       \
\  (\\<forall>X. equal(unordered_pair(X::'a,X),singleton(X))) &     \
\  (\\<forall>X Y. equal(unordered_pair(singleton(X),unordered_pair(X::'a,singleton(Y))),ordered_pair(X::'a,Y))) &      \
\  (\\<forall>V Y U X. member(ordered_pair(U::'a,V),cross_product(X::'a,Y)) --> member(U::'a,X)) &  \
\  (\\<forall>U X V Y. member(ordered_pair(U::'a,V),cross_product(X::'a,Y)) --> member(V::'a,Y)) &  \
\  (\\<forall>U V X Y. member(U::'a,X) & member(V::'a,Y) --> member(ordered_pair(U::'a,V),cross_product(X::'a,Y))) &    \
\  (\\<forall>X Y Z. member(Z::'a,cross_product(X::'a,Y)) --> equal(ordered_pair(first(Z),second(Z)),Z)) &      \
\  (subclass(element_relation::'a,cross_product(universal_class::'a,universal_class))) &        \
\  (\\<forall>X Y. member(ordered_pair(X::'a,Y),element_relation) --> member(X::'a,Y)) &        \
\  (\\<forall>X Y. member(ordered_pair(X::'a,Y),cross_product(universal_class::'a,universal_class)) & member(X::'a,Y) --> member(ordered_pair(X::'a,Y),element_relation)) &     \
\  (\\<forall>Y Z X. member(Z::'a,intersection(X::'a,Y)) --> member(Z::'a,X)) &     \
\  (\\<forall>X Z Y. member(Z::'a,intersection(X::'a,Y)) --> member(Z::'a,Y)) &     \
\  (\\<forall>Z X Y. member(Z::'a,X) & member(Z::'a,Y) --> member(Z::'a,intersection(X::'a,Y))) &       \
\  (\\<forall>Z X. ~(member(Z::'a,complement(X)) & member(Z::'a,X))) &  \
\  (\\<forall>Z X. member(Z::'a,universal_class) --> member(Z::'a,complement(X)) | member(Z::'a,X)) &      \
\  (\\<forall>X Y. equal(complement(intersection(complement(X),complement(Y))),union(X::'a,Y))) &   \
\  (\\<forall>X Y. equal(intersection(complement(intersection(X::'a,Y)),complement(intersection(complement(X),complement(Y)))),difference(X::'a,Y))) &  \
\  (\\<forall>Xr X Y. equal(intersection(Xr::'a,cross_product(X::'a,Y)),restrct(Xr::'a,X,Y))) &    \
\  (\\<forall>Xr X Y. equal(intersection(cross_product(X::'a,Y),Xr),restrct(Xr::'a,X,Y))) &    \
\  (\\<forall>Z X. ~(equal(restrct(X::'a,singleton(Z),universal_class),null_class) & member(Z::'a,domain_of(X)))) &    \
\  (\\<forall>Z X. member(Z::'a,universal_class) --> equal(restrct(X::'a,singleton(Z),universal_class),null_class) | member(Z::'a,domain_of(X))) &        \
\  (\\<forall>X. subclass(rotate(X),cross_product(cross_product(universal_class::'a,universal_class),universal_class))) &   \
\  (\\<forall>V W U X. member(ordered_pair(ordered_pair(U::'a,V),W),rotate(X)) --> member(ordered_pair(ordered_pair(V::'a,W),U),X)) &   \
\  (\\<forall>U V W X. member(ordered_pair(ordered_pair(V::'a,W),U),X) & member(ordered_pair(ordered_pair(U::'a,V),W),cross_product(cross_product(universal_class::'a,universal_class),universal_class)) --> member(ordered_pair(ordered_pair(U::'a,V),W),rotate(X))) & \
\  (\\<forall>X. subclass(flip(X),cross_product(cross_product(universal_class::'a,universal_class),universal_class))) &     \
\  (\\<forall>V U W X. member(ordered_pair(ordered_pair(U::'a,V),W),flip(X)) --> member(ordered_pair(ordered_pair(V::'a,U),W),X)) &     \
\  (\\<forall>U V W X. member(ordered_pair(ordered_pair(V::'a,U),W),X) & member(ordered_pair(ordered_pair(U::'a,V),W),cross_product(cross_product(universal_class::'a,universal_class),universal_class)) --> member(ordered_pair(ordered_pair(U::'a,V),W),flip(X))) &   \
\  (\\<forall>Y. equal(domain_of(flip(cross_product(Y::'a,universal_class))),INVERSE(Y))) & \
\  (\\<forall>Z. equal(domain_of(INVERSE(Z)),range_of(Z))) &    \
\  (\\<forall>Z X Y. equal(first(not_subclass_element(restrct(Z::'a,X,singleton(Y)),null_class)),domain(Z::'a,X,Y))) & \
\  (\\<forall>Z X Y. equal(second(not_subclass_element(restrct(Z::'a,singleton(X),Y),null_class)),rng(Z::'a,X,Y))) & \
\  (\\<forall>Xr X. equal(range_of(restrct(Xr::'a,X,universal_class)),image_(Xr::'a,X))) &      \
\  (\\<forall>X. equal(union(X::'a,singleton(X)),successor(X))) &   \
\  (subclass(successor_relation::'a,cross_product(universal_class::'a,universal_class))) &      \
\  (\\<forall>X Y. member(ordered_pair(X::'a,Y),successor_relation) --> equal(successor(X),Y)) &    \
\  (\\<forall>X Y. equal(successor(X),Y) & member(ordered_pair(X::'a,Y),cross_product(universal_class::'a,universal_class)) --> member(ordered_pair(X::'a,Y),successor_relation)) & \
\  (\\<forall>X. inductive(X) --> member(null_class::'a,X)) &       \
\  (\\<forall>X. inductive(X) --> subclass(image_(successor_relation::'a,X),X)) &    \
\  (\\<forall>X. member(null_class::'a,X) & subclass(image_(successor_relation::'a,X),X) --> inductive(X)) &     \
\  (inductive(omega)) & \
\  (\\<forall>Y. inductive(Y) --> subclass(omega::'a,Y)) &  \
\  (member(omega::'a,universal_class)) &    \
\  (\\<forall>X. equal(domain_of(restrct(element_relation::'a,universal_class,X)),sum_class(X))) & \
\  (\\<forall>X. member(X::'a,universal_class) --> member(sum_class(X),universal_class)) &  \
\  (\\<forall>X. equal(complement(image_(element_relation::'a,complement(X))),powerClass(X))) &     \
\  (\\<forall>U. member(U::'a,universal_class) --> member(powerClass(U),universal_class)) &        \
\  (\\<forall>Yr Xr. subclass(compos(Yr::'a,Xr),cross_product(universal_class::'a,universal_class))) & \
\  (\\<forall>Z Yr Xr Y. member(ordered_pair(Y::'a,Z),compos(Yr::'a,Xr)) --> member(Z::'a,image_(Yr::'a,image_(Xr::'a,singleton(Y))))) &     \
\  (\\<forall>Y Z Yr Xr. member(Z::'a,image_(Yr::'a,image_(Xr::'a,singleton(Y)))) & member(ordered_pair(Y::'a,Z),cross_product(universal_class::'a,universal_class)) --> member(ordered_pair(Y::'a,Z),compos(Yr::'a,Xr))) &  \
\  (\\<forall>X. single_valued_class(X) --> subclass(compos(X::'a,INVERSE(X)),identity_relation)) &        \
\  (\\<forall>X. subclass(compos(X::'a,INVERSE(X)),identity_relation) --> single_valued_class(X)) &        \
\  (\\<forall>Xf. function(Xf) --> subclass(Xf::'a,cross_product(universal_class::'a,universal_class))) &       \
\  (\\<forall>Xf. function(Xf) --> subclass(compos(Xf::'a,INVERSE(Xf)),identity_relation)) &       \
\  (\\<forall>Xf. subclass(Xf::'a,cross_product(universal_class::'a,universal_class)) & subclass(compos(Xf::'a,INVERSE(Xf)),identity_relation) --> function(Xf)) & \
\  (\\<forall>Xf X. function(Xf) & member(X::'a,universal_class) --> member(image_(Xf::'a,X),universal_class)) & \
\  (\\<forall>X. equal(X::'a,null_class) | member(regular(X),X)) & \
\  (\\<forall>X. equal(X::'a,null_class) | equal(intersection(X::'a,regular(X)),null_class)) & \
\  (\\<forall>Xf Y. equal(sum_class(image_(Xf::'a,singleton(Y))),apply(Xf::'a,Y))) &     \
\  (function(choice)) & \
\  (\\<forall>Y. member(Y::'a,universal_class) --> equal(Y::'a,null_class) | member(apply(choice::'a,Y),Y)) &      \
\  (\\<forall>Xf. one_to_one(Xf) --> function(Xf)) &    \
\  (\\<forall>Xf. one_to_one(Xf) --> function(INVERSE(Xf))) &   \
\  (\\<forall>Xf. function(INVERSE(Xf)) & function(Xf) --> one_to_one(Xf)) &    \
\  (equal(intersection(cross_product(universal_class::'a,universal_class),intersection(cross_product(universal_class::'a,universal_class),complement(compos(complement(element_relation),INVERSE(element_relation))))),subset_relation)) &     \
\  (equal(intersection(INVERSE(subset_relation),subset_relation),identity_relation)) &  \
\  (\\<forall>Xr. equal(complement(domain_of(intersection(Xr::'a,identity_relation))),diagonalise(Xr))) &   \
\  (\\<forall>X. equal(intersection(domain_of(X),diagonalise(compos(INVERSE(element_relation),X))),cantor(X))) &       \
\  (\\<forall>Xf. operation(Xf) --> function(Xf)) &     \
\  (\\<forall>Xf. operation(Xf) --> equal(cross_product(domain_of(domain_of(Xf)),domain_of(domain_of(Xf))),domain_of(Xf))) &    \
\  (\\<forall>Xf. operation(Xf) --> subclass(range_of(Xf),domain_of(domain_of(Xf)))) &  \
\  (\\<forall>Xf. function(Xf) & equal(cross_product(domain_of(domain_of(Xf)),domain_of(domain_of(Xf))),domain_of(Xf)) & subclass(range_of(Xf),domain_of(domain_of(Xf))) --> operation(Xf)) &   \
\  (\\<forall>Xf1 Xf2 Xh. compatible(Xh::'a,Xf1,Xf2) --> function(Xh)) &    \
\  (\\<forall>Xf2 Xf1 Xh. compatible(Xh::'a,Xf1,Xf2) --> equal(domain_of(domain_of(Xf1)),domain_of(Xh))) &  \
\  (\\<forall>Xf1 Xh Xf2. compatible(Xh::'a,Xf1,Xf2) --> subclass(range_of(Xh),domain_of(domain_of(Xf2)))) &        \
\  (\\<forall>Xh Xh1 Xf1 Xf2. function(Xh) & equal(domain_of(domain_of(Xf1)),domain_of(Xh)) & subclass(range_of(Xh),domain_of(domain_of(Xf2))) --> compatible(Xh1::'a,Xf1,Xf2)) &   \
\  (\\<forall>Xh Xf2 Xf1. homomorphism(Xh::'a,Xf1,Xf2) --> operation(Xf1)) &        \
\  (\\<forall>Xh Xf1 Xf2. homomorphism(Xh::'a,Xf1,Xf2) --> operation(Xf2)) &        \
\  (\\<forall>Xh Xf1 Xf2. homomorphism(Xh::'a,Xf1,Xf2) --> compatible(Xh::'a,Xf1,Xf2)) &        \
\  (\\<forall>Xf2 Xh Xf1 X Y. homomorphism(Xh::'a,Xf1,Xf2) & member(ordered_pair(X::'a,Y),domain_of(Xf1)) --> equal(apply(Xf2::'a,ordered_pair(apply(Xh::'a,X),apply(Xh::'a,Y))),apply(Xh::'a,apply(Xf1::'a,ordered_pair(X::'a,Y))))) & \
\  (\\<forall>Xh Xf1 Xf2. operation(Xf1) & operation(Xf2) & compatible(Xh::'a,Xf1,Xf2) --> member(ordered_pair(not_homomorphism1(Xh::'a,Xf1,Xf2),not_homomorphism2(Xh::'a,Xf1,Xf2)),domain_of(Xf1)) | homomorphism(Xh::'a,Xf1,Xf2)) &  \
\  (\\<forall>Xh Xf1 Xf2. operation(Xf1) & operation(Xf2) & compatible(Xh::'a,Xf1,Xf2) & equal(apply(Xf2::'a,ordered_pair(apply(Xh::'a,not_homomorphism1(Xh::'a,Xf1,Xf2)),apply(Xh::'a,not_homomorphism2(Xh::'a,Xf1,Xf2)))),apply(Xh::'a,apply(Xf1::'a,ordered_pair(not_homomorphism1(Xh::'a,Xf1,Xf2),not_homomorphism2(Xh::'a,Xf1,Xf2))))) --> homomorphism(Xh::'a,Xf1,Xf2)) &     \
\  (\\<forall>D E F'. equal(D::'a,E) --> equal(apply(D::'a,F'),apply(E::'a,F'))) &  \
\  (\\<forall>G I' H. equal(G::'a,H) --> equal(apply(I'::'a,G),apply(I'::'a,H))) &  \
\  (\\<forall>J K'. equal(J::'a,K') --> equal(cantor(J),cantor(K'))) &      \
\  (\\<forall>L M. equal(L::'a,M) --> equal(complement(L),complement(M))) & \
\  (\\<forall>N O_ P. equal(N::'a,O_) --> equal(compos(N::'a,P),compos(O_::'a,P))) & \
\  (\\<forall>Q S' R. equal(Q::'a,R) --> equal(compos(S'::'a,Q),compos(S'::'a,R))) &      \
\  (\\<forall>T' U V. equal(T'::'a,U) --> equal(cross_product(T'::'a,V),cross_product(U::'a,V))) &  \
\  (\\<forall>W Y X. equal(W::'a,X) --> equal(cross_product(Y::'a,W),cross_product(Y::'a,X))) &     \
\  (\\<forall>Z A1. equal(Z::'a,A1) --> equal(diagonalise(Z),diagonalise(A1))) &    \
\  (\\<forall>B1 C1 D1. equal(B1::'a,C1) --> equal(difference(B1::'a,D1),difference(C1::'a,D1))) &  \
\  (\\<forall>E1 G1 F1. equal(E1::'a,F1) --> equal(difference(G1::'a,E1),difference(G1::'a,F1))) &  \
\  (\\<forall>H1 I1 J1 K1. equal(H1::'a,I1) --> equal(domain(H1::'a,J1,K1),domain(I1::'a,J1,K1))) & \
\  (\\<forall>L1 N1 M1 O1. equal(L1::'a,M1) --> equal(domain(N1::'a,L1,O1),domain(N1::'a,M1,O1))) & \
\  (\\<forall>P1 R1 S1 Q1. equal(P1::'a,Q1) --> equal(domain(R1::'a,S1,P1),domain(R1::'a,S1,Q1))) & \
\  (\\<forall>T1 U1. equal(T1::'a,U1) --> equal(domain_of(T1),domain_of(U1))) &     \
\  (\\<forall>V1 W1. equal(V1::'a,W1) --> equal(first(V1),first(W1))) &     \
\  (\\<forall>X1 Y1. equal(X1::'a,Y1) --> equal(flip(X1),flip(Y1))) &       \
\  (\\<forall>Z1 A2 B2. equal(Z1::'a,A2) --> equal(image_(Z1::'a,B2),image_(A2::'a,B2))) &    \
\  (\\<forall>C2 E2 D2. equal(C2::'a,D2) --> equal(image_(E2::'a,C2),image_(E2::'a,D2))) &    \
\  (\\<forall>F2 G2 H2. equal(F2::'a,G2) --> equal(intersection(F2::'a,H2),intersection(G2::'a,H2))) &      \
\  (\\<forall>I2 K2 J2. equal(I2::'a,J2) --> equal(intersection(K2::'a,I2),intersection(K2::'a,J2))) &      \
\  (\\<forall>L2 M2. equal(L2::'a,M2) --> equal(INVERSE(L2),INVERSE(M2))) & \
\  (\\<forall>N2 O2 P2 Q2. equal(N2::'a,O2) --> equal(not_homomorphism1(N2::'a,P2,Q2),not_homomorphism1(O2::'a,P2,Q2))) &   \
\  (\\<forall>R2 T2 S2 U2. equal(R2::'a,S2) --> equal(not_homomorphism1(T2::'a,R2,U2),not_homomorphism1(T2::'a,S2,U2))) &   \
\  (\\<forall>V2 X2 Y2 W2. equal(V2::'a,W2) --> equal(not_homomorphism1(X2::'a,Y2,V2),not_homomorphism1(X2::'a,Y2,W2))) &   \
\  (\\<forall>Z2 A3 B3 C3. equal(Z2::'a,A3) --> equal(not_homomorphism2(Z2::'a,B3,C3),not_homomorphism2(A3::'a,B3,C3))) &   \
\  (\\<forall>D3 F3 E3 G3. equal(D3::'a,E3) --> equal(not_homomorphism2(F3::'a,D3,G3),not_homomorphism2(F3::'a,E3,G3))) &   \
\  (\\<forall>H3 J3 K3 I3. equal(H3::'a,I3) --> equal(not_homomorphism2(J3::'a,K3,H3),not_homomorphism2(J3::'a,K3,I3))) &   \
\  (\\<forall>L3 M3 N3. equal(L3::'a,M3) --> equal(not_subclass_element(L3::'a,N3),not_subclass_element(M3::'a,N3))) &      \
\  (\\<forall>O3 Q3 P3. equal(O3::'a,P3) --> equal(not_subclass_element(Q3::'a,O3),not_subclass_element(Q3::'a,P3))) &      \
\  (\\<forall>R3 S3 T3. equal(R3::'a,S3) --> equal(ordered_pair(R3::'a,T3),ordered_pair(S3::'a,T3))) &      \
\  (\\<forall>U3 W3 V3. equal(U3::'a,V3) --> equal(ordered_pair(W3::'a,U3),ordered_pair(W3::'a,V3))) &      \
\  (\\<forall>X3 Y3. equal(X3::'a,Y3) --> equal(powerClass(X3),powerClass(Y3))) & \
\  (\\<forall>Z3 A4 B4 C4. equal(Z3::'a,A4) --> equal(rng(Z3::'a,B4,C4),rng(A4::'a,B4,C4))) &   \
\  (\\<forall>D4 F4 E4 G4. equal(D4::'a,E4) --> equal(rng(F4::'a,D4,G4),rng(F4::'a,E4,G4))) &   \
\  (\\<forall>H4 J4 K4 I4. equal(H4::'a,I4) --> equal(rng(J4::'a,K4,H4),rng(J4::'a,K4,I4))) &   \
\  (\\<forall>L4 M4. equal(L4::'a,M4) --> equal(range_of(L4),range_of(M4))) &       \
\  (\\<forall>N4 O4. equal(N4::'a,O4) --> equal(regular(N4),regular(O4))) & \
\  (\\<forall>P4 Q4 R4 S4. equal(P4::'a,Q4) --> equal(restrct(P4::'a,R4,S4),restrct(Q4::'a,R4,S4))) &     \
\  (\\<forall>T4 V4 U4 W4. equal(T4::'a,U4) --> equal(restrct(V4::'a,T4,W4),restrct(V4::'a,U4,W4))) &     \
\  (\\<forall>X4 Z4 A5 Y4. equal(X4::'a,Y4) --> equal(restrct(Z4::'a,A5,X4),restrct(Z4::'a,A5,Y4))) &     \
\  (\\<forall>B5 C5. equal(B5::'a,C5) --> equal(rotate(B5),rotate(C5))) &   \
\  (\\<forall>D5 E5. equal(D5::'a,E5) --> equal(second(D5),second(E5))) &   \
\  (\\<forall>F5 G5. equal(F5::'a,G5) --> equal(singleton(F5),singleton(G5))) &     \
\  (\\<forall>H5 I5. equal(H5::'a,I5) --> equal(successor(H5),successor(I5))) &     \
\  (\\<forall>J5 K5. equal(J5::'a,K5) --> equal(sum_class(J5),sum_class(K5))) &     \
\  (\\<forall>L5 M5 N5. equal(L5::'a,M5) --> equal(union(L5::'a,N5),union(M5::'a,N5))) &    \
\  (\\<forall>O5 Q5 P5. equal(O5::'a,P5) --> equal(union(Q5::'a,O5),union(Q5::'a,P5))) &    \
\  (\\<forall>R5 S5 T5. equal(R5::'a,S5) --> equal(unordered_pair(R5::'a,T5),unordered_pair(S5::'a,T5))) &  \
\  (\\<forall>U5 W5 V5. equal(U5::'a,V5) --> equal(unordered_pair(W5::'a,U5),unordered_pair(W5::'a,V5))) &  \
\  (\\<forall>X5 Y5 Z5 A6. equal(X5::'a,Y5) & compatible(X5::'a,Z5,A6) --> compatible(Y5::'a,Z5,A6)) &      \
\  (\\<forall>B6 D6 C6 E6. equal(B6::'a,C6) & compatible(D6::'a,B6,E6) --> compatible(D6::'a,C6,E6)) &      \
\  (\\<forall>F6 H6 I6 G6. equal(F6::'a,G6) & compatible(H6::'a,I6,F6) --> compatible(H6::'a,I6,G6)) &      \
\  (\\<forall>J6 K6. equal(J6::'a,K6) & function(J6) --> function(K6)) &    \
\  (\\<forall>L6 M6 N6 O6. equal(L6::'a,M6) & homomorphism(L6::'a,N6,O6) --> homomorphism(M6::'a,N6,O6)) &  \
\  (\\<forall>P6 R6 Q6 S6. equal(P6::'a,Q6) & homomorphism(R6::'a,P6,S6) --> homomorphism(R6::'a,Q6,S6)) &  \
\  (\\<forall>T6 V6 W6 U6. equal(T6::'a,U6) & homomorphism(V6::'a,W6,T6) --> homomorphism(V6::'a,W6,U6)) &  \
\  (\\<forall>X6 Y6. equal(X6::'a,Y6) & inductive(X6) --> inductive(Y6)) &  \
\  (\\<forall>Z6 A7 B7. equal(Z6::'a,A7) & member(Z6::'a,B7) --> member(A7::'a,B7)) &       \
\  (\\<forall>C7 E7 D7. equal(C7::'a,D7) & member(E7::'a,C7) --> member(E7::'a,D7)) &       \
\  (\\<forall>F7 G7. equal(F7::'a,G7) & one_to_one(F7) --> one_to_one(G7)) &        \
\  (\\<forall>H7 I7. equal(H7::'a,I7) & operation(H7) --> operation(I7)) &  \
\  (\\<forall>J7 K7. equal(J7::'a,K7) & single_valued_class(J7) --> single_valued_class(K7)) &      \
\  (\\<forall>L7 M7 N7. equal(L7::'a,M7) & subclass(L7::'a,N7) --> subclass(M7::'a,N7)) &   \
\  (\\<forall>O7 Q7 P7. equal(O7::'a,P7) & subclass(Q7::'a,O7) --> subclass(Q7::'a,P7)) &   \
\  (\\<forall>X. subclass(compose_class(X),cross_product(universal_class::'a,universal_class))) &   \
\  (\\<forall>X Y Z. member(ordered_pair(Y::'a,Z),compose_class(X)) --> equal(compos(X::'a,Y),Z)) &    \
\  (\\<forall>Y Z X. member(ordered_pair(Y::'a,Z),cross_product(universal_class::'a,universal_class)) & equal(compos(X::'a,Y),Z) --> member(ordered_pair(Y::'a,Z),compose_class(X))) & \
\  (subclass(composition_function::'a,cross_product(universal_class::'a,cross_product(universal_class::'a,universal_class)))) &     \
\  (\\<forall>X Y Z. member(ordered_pair(X::'a,ordered_pair(Y::'a,Z)),composition_function) --> equal(compos(X::'a,Y),Z)) &        \
\  (\\<forall>X Y. member(ordered_pair(X::'a,Y),cross_product(universal_class::'a,universal_class)) --> member(ordered_pair(X::'a,ordered_pair(Y::'a,compos(X::'a,Y))),composition_function)) &    \
\  (subclass(domain_relation::'a,cross_product(universal_class::'a,universal_class))) & \
\  (\\<forall>X Y. member(ordered_pair(X::'a,Y),domain_relation) --> equal(domain_of(X),Y)) &       \
\  (\\<forall>X. member(X::'a,universal_class) --> member(ordered_pair(X::'a,domain_of(X)),domain_relation)) &  \
\  (\\<forall>X. equal(first(not_subclass_element(compos(X::'a,INVERSE(X)),identity_relation)),single_valued1(X))) &       \
\  (\\<forall>X. equal(second(not_subclass_element(compos(X::'a,INVERSE(X)),identity_relation)),single_valued2(X))) &      \
\  (\\<forall>X. equal(domain(X::'a,image_(INVERSE(X),singleton(single_valued1(X))),single_valued2(X)),single_valued3(X))) & \
\  (equal(intersection(complement(compos(element_relation::'a,complement(identity_relation))),element_relation),singleton_relation)) &     \
\  (subclass(application_function::'a,cross_product(universal_class::'a,cross_product(universal_class::'a,universal_class)))) &     \
\  (\\<forall>Z Y X. member(ordered_pair(X::'a,ordered_pair(Y::'a,Z)),application_function) --> member(Y::'a,domain_of(X))) &       \
\  (\\<forall>X Y Z. member(ordered_pair(X::'a,ordered_pair(Y::'a,Z)),application_function) --> equal(apply(X::'a,Y),Z)) &  \
\  (\\<forall>Z X Y. member(ordered_pair(X::'a,ordered_pair(Y::'a,Z)),cross_product(universal_class::'a,cross_product(universal_class::'a,universal_class))) & member(Y::'a,domain_of(X)) --> member(ordered_pair(X::'a,ordered_pair(Y::'a,apply(X::'a,Y))),application_function)) &    \
\  (\\<forall>X Y Xf. maps(Xf::'a,X,Y) --> function(Xf)) &  \
\  (\\<forall>Y Xf X. maps(Xf::'a,X,Y) --> equal(domain_of(Xf),X)) &        \
\  (\\<forall>X Xf Y. maps(Xf::'a,X,Y) --> subclass(range_of(Xf),Y)) &      \
\  (\\<forall>Xf Y. function(Xf) & subclass(range_of(Xf),Y) --> maps(Xf::'a,domain_of(Xf),Y)) &     \
\  (\\<forall>L M. equal(L::'a,M) --> equal(compose_class(L),compose_class(M))) &   \
\  (\\<forall>N2 O2. equal(N2::'a,O2) --> equal(single_valued1(N2),single_valued1(O2))) &   \
\  (\\<forall>P2 Q2. equal(P2::'a,Q2) --> equal(single_valued2(P2),single_valued2(Q2))) &   \
\  (\\<forall>R2 S2. equal(R2::'a,S2) --> equal(single_valued3(R2),single_valued3(S2))) &   \
\  (\\<forall>X2 Y2 Z2 A3. equal(X2::'a,Y2) & maps(X2::'a,Z2,A3) --> maps(Y2::'a,Z2,A3)) &  \
\  (\\<forall>B3 D3 C3 E3. equal(B3::'a,C3) & maps(D3::'a,B3,E3) --> maps(D3::'a,C3,E3)) &  \
\  (\\<forall>F3 H3 I3 G3. equal(F3::'a,G3) & maps(H3::'a,I3,F3) --> maps(H3::'a,I3,G3)) &  \
\  (\\<forall>X. equal(union(X::'a,INVERSE(X)),symmetrization_of(X))) &     \
\  (\\<forall>X Y. irreflexive(X::'a,Y) --> subclass(restrct(X::'a,Y,Y),complement(identity_relation))) &      \
\  (\\<forall>X Y. subclass(restrct(X::'a,Y,Y),complement(identity_relation)) --> irreflexive(X::'a,Y)) &      \
\  (\\<forall>Y X. connected(X::'a,Y) --> subclass(cross_product(Y::'a,Y),union(identity_relation::'a,symmetrization_of(X)))) &     \
\  (\\<forall>X Y. subclass(cross_product(Y::'a,Y),union(identity_relation::'a,symmetrization_of(X))) --> connected(X::'a,Y)) &     \
\  (\\<forall>Xr Y. transitive(Xr::'a,Y) --> subclass(compos(restrct(Xr::'a,Y,Y),restrct(Xr::'a,Y,Y)),restrct(Xr::'a,Y,Y))) &       \
\  (\\<forall>Xr Y. subclass(compos(restrct(Xr::'a,Y,Y),restrct(Xr::'a,Y,Y)),restrct(Xr::'a,Y,Y)) --> transitive(Xr::'a,Y)) &       \
\  (\\<forall>Xr Y. asymmetric(Xr::'a,Y) --> equal(restrct(intersection(Xr::'a,INVERSE(Xr)),Y,Y),null_class)) &        \
\  (\\<forall>Xr Y. equal(restrct(intersection(Xr::'a,INVERSE(Xr)),Y,Y),null_class) --> asymmetric(Xr::'a,Y)) &        \
\  (\\<forall>Xr Y Z. equal(segment(Xr::'a,Y,Z),domain_of(restrct(Xr::'a,Y,singleton(Z))))) &  \
\  (\\<forall>X Y. well_ordering(X::'a,Y) --> connected(X::'a,Y)) &     \
\  (\\<forall>Y Xr U. well_ordering(Xr::'a,Y) & subclass(U::'a,Y) --> equal(U::'a,null_class) | member(least(Xr::'a,U),U)) &   \
\  (\\<forall>Y V Xr U. well_ordering(Xr::'a,Y) & subclass(U::'a,Y) & member(V::'a,U) --> member(least(Xr::'a,U),U)) &  \
\  (\\<forall>Y Xr U. well_ordering(Xr::'a,Y) & subclass(U::'a,Y) --> equal(segment(Xr::'a,U,least(Xr::'a,U)),null_class)) &    \
\  (\\<forall>Y V U Xr. ~(well_ordering(Xr::'a,Y) & subclass(U::'a,Y) & member(V::'a,U) & member(ordered_pair(V::'a,least(Xr::'a,U)),Xr))) &        \
\  (\\<forall>Xr Y. connected(Xr::'a,Y) & equal(not_well_ordering(Xr::'a,Y),null_class) --> well_ordering(Xr::'a,Y)) &      \
\  (\\<forall>Xr Y. connected(Xr::'a,Y) --> subclass(not_well_ordering(Xr::'a,Y),Y) | well_ordering(Xr::'a,Y)) &   \
\  (\\<forall>V Xr Y. member(V::'a,not_well_ordering(Xr::'a,Y)) & equal(segment(Xr::'a,not_well_ordering(Xr::'a,Y),V),null_class) & connected(Xr::'a,Y) --> well_ordering(Xr::'a,Y)) &  \
\  (\\<forall>Xr Y Z. section(Xr::'a,Y,Z) --> subclass(Y::'a,Z)) &      \
\  (\\<forall>Xr Z Y. section(Xr::'a,Y,Z) --> subclass(domain_of(restrct(Xr::'a,Z,Y)),Y)) &    \
\  (\\<forall>Xr Y Z. subclass(Y::'a,Z) & subclass(domain_of(restrct(Xr::'a,Z,Y)),Y) --> section(Xr::'a,Y,Z)) &    \
\  (\\<forall>X. member(X::'a,ordinal_numbers) --> well_ordering(element_relation::'a,X)) &     \
\  (\\<forall>X. member(X::'a,ordinal_numbers) --> subclass(sum_class(X),X)) &      \
\  (\\<forall>X. well_ordering(element_relation::'a,X) & subclass(sum_class(X),X) & member(X::'a,universal_class) --> member(X::'a,ordinal_numbers)) &      \
\  (\\<forall>X. well_ordering(element_relation::'a,X) & subclass(sum_class(X),X) --> member(X::'a,ordinal_numbers) | equal(X::'a,ordinal_numbers)) &      \
\  (equal(union(singleton(null_class),image_(successor_relation::'a,ordinal_numbers)),kind_1_ordinals)) &    \
\  (equal(intersection(complement(kind_1_ordinals),ordinal_numbers),limit_ordinals)) &  \
\  (\\<forall>X. subclass(rest_of(X),cross_product(universal_class::'a,universal_class))) & \
\  (\\<forall>V U X. member(ordered_pair(U::'a,V),rest_of(X)) --> member(U::'a,domain_of(X))) & \
\  (\\<forall>X U V. member(ordered_pair(U::'a,V),rest_of(X)) --> equal(restrct(X::'a,U,universal_class),V)) & \
\  (\\<forall>U V X. member(U::'a,domain_of(X)) & equal(restrct(X::'a,U,universal_class),V) --> member(ordered_pair(U::'a,V),rest_of(X))) &        \
\  (subclass(rest_relation::'a,cross_product(universal_class::'a,universal_class))) &   \
\  (\\<forall>X Y. member(ordered_pair(X::'a,Y),rest_relation) --> equal(rest_of(X),Y)) &   \
\  (\\<forall>X. member(X::'a,universal_class) --> member(ordered_pair(X::'a,rest_of(X)),rest_relation)) &      \
\  (\\<forall>X Z. member(X::'a,recursion_equation_functions(Z)) --> function(Z)) & \
\  (\\<forall>Z X. member(X::'a,recursion_equation_functions(Z)) --> function(X)) & \
\  (\\<forall>Z X. member(X::'a,recursion_equation_functions(Z)) --> member(domain_of(X),ordinal_numbers)) &        \
\  (\\<forall>Z X. member(X::'a,recursion_equation_functions(Z)) --> equal(compos(Z::'a,rest_of(X)),X)) &      \
\  (\\<forall>X Z. function(Z) & function(X) & member(domain_of(X),ordinal_numbers) & equal(compos(Z::'a,rest_of(X)),X) --> member(X::'a,recursion_equation_functions(Z))) &   \
\  (subclass(union_of_range_map::'a,cross_product(universal_class::'a,universal_class))) &      \
\  (\\<forall>X Y. member(ordered_pair(X::'a,Y),union_of_range_map) --> equal(sum_class(range_of(X)),Y)) &  \
\  (\\<forall>X Y. member(ordered_pair(X::'a,Y),cross_product(universal_class::'a,universal_class)) & equal(sum_class(range_of(X)),Y) --> member(ordered_pair(X::'a,Y),union_of_range_map)) &       \
\  (\\<forall>X Y. equal(apply(recursion(X::'a,successor_relation,union_of_range_map),Y),ordinal_add(X::'a,Y))) &       \
\  (\\<forall>X Y. equal(recursion(null_class::'a,apply(add_relation::'a,X),union_of_range_map),ordinal_multiply(X::'a,Y))) &       \
\  (\\<forall>X. member(X::'a,omega) --> equal(integer_of(X),X)) &  \
\  (\\<forall>X. member(X::'a,omega) | equal(integer_of(X),null_class)) &  \
\  (\\<forall>D E. equal(D::'a,E) --> equal(integer_of(D),integer_of(E))) & \
\  (\\<forall>F' G H. equal(F'::'a,G) --> equal(least(F'::'a,H),least(G::'a,H))) &  \
\  (\\<forall>I' K' J. equal(I'::'a,J) --> equal(least(K'::'a,I'),least(K'::'a,J))) &       \
\  (\\<forall>L M N. equal(L::'a,M) --> equal(not_well_ordering(L::'a,N),not_well_ordering(M::'a,N))) &     \
\  (\\<forall>O_ Q P. equal(O_::'a,P) --> equal(not_well_ordering(Q::'a,O_),not_well_ordering(Q::'a,P))) &     \
\  (\\<forall>R S' T'. equal(R::'a,S') --> equal(ordinal_add(R::'a,T'),ordinal_add(S'::'a,T'))) &   \
\  (\\<forall>U W V. equal(U::'a,V) --> equal(ordinal_add(W::'a,U),ordinal_add(W::'a,V))) & \
\  (\\<forall>X Y Z. equal(X::'a,Y) --> equal(ordinal_multiply(X::'a,Z),ordinal_multiply(Y::'a,Z))) &       \
\  (\\<forall>A1 C1 B1. equal(A1::'a,B1) --> equal(ordinal_multiply(C1::'a,A1),ordinal_multiply(C1::'a,B1))) &      \
\  (\\<forall>F1 G1 H1 I1. equal(F1::'a,G1) --> equal(recursion(F1::'a,H1,I1),recursion(G1::'a,H1,I1))) &   \
\  (\\<forall>J1 L1 K1 M1. equal(J1::'a,K1) --> equal(recursion(L1::'a,J1,M1),recursion(L1::'a,K1,M1))) &   \
\  (\\<forall>N1 P1 Q1 O1. equal(N1::'a,O1) --> equal(recursion(P1::'a,Q1,N1),recursion(P1::'a,Q1,O1))) &   \
\  (\\<forall>R1 S1. equal(R1::'a,S1) --> equal(recursion_equation_functions(R1),recursion_equation_functions(S1))) &       \
\  (\\<forall>T1 U1. equal(T1::'a,U1) --> equal(rest_of(T1),rest_of(U1))) & \
\  (\\<forall>V1 W1 X1 Y1. equal(V1::'a,W1) --> equal(segment(V1::'a,X1,Y1),segment(W1::'a,X1,Y1))) &       \
\  (\\<forall>Z1 B2 A2 C2. equal(Z1::'a,A2) --> equal(segment(B2::'a,Z1,C2),segment(B2::'a,A2,C2))) &       \
\  (\\<forall>D2 F2 G2 E2. equal(D2::'a,E2) --> equal(segment(F2::'a,G2,D2),segment(F2::'a,G2,E2))) &       \
\  (\\<forall>H2 I2. equal(H2::'a,I2) --> equal(symmetrization_of(H2),symmetrization_of(I2))) &     \
\  (\\<forall>J2 K2 L2. equal(J2::'a,K2) & asymmetric(J2::'a,L2) --> asymmetric(K2::'a,L2)) &       \
\  (\\<forall>M2 O2 N2. equal(M2::'a,N2) & asymmetric(O2::'a,M2) --> asymmetric(O2::'a,N2)) &       \
\  (\\<forall>P2 Q2 R2. equal(P2::'a,Q2) & connected(P2::'a,R2) --> connected(Q2::'a,R2)) & \
\  (\\<forall>S2 U2 T2. equal(S2::'a,T2) & connected(U2::'a,S2) --> connected(U2::'a,T2)) & \
\  (\\<forall>V2 W2 X2. equal(V2::'a,W2) & irreflexive(V2::'a,X2) --> irreflexive(W2::'a,X2)) &     \
\  (\\<forall>Y2 A3 Z2. equal(Y2::'a,Z2) & irreflexive(A3::'a,Y2) --> irreflexive(A3::'a,Z2)) &     \
\  (\\<forall>B3 C3 D3 E3. equal(B3::'a,C3) & section(B3::'a,D3,E3) --> section(C3::'a,D3,E3)) &    \
\  (\\<forall>F3 H3 G3 I3. equal(F3::'a,G3) & section(H3::'a,F3,I3) --> section(H3::'a,G3,I3)) &    \
\  (\\<forall>J3 L3 M3 K3. equal(J3::'a,K3) & section(L3::'a,M3,J3) --> section(L3::'a,M3,K3)) &    \
\  (\\<forall>N3 O3 P3. equal(N3::'a,O3) & transitive(N3::'a,P3) --> transitive(O3::'a,P3)) &       \
\  (\\<forall>Q3 S3 R3. equal(Q3::'a,R3) & transitive(S3::'a,Q3) --> transitive(S3::'a,R3)) &       \
\  (\\<forall>T3 U3 V3. equal(T3::'a,U3) & well_ordering(T3::'a,V3) --> well_ordering(U3::'a,V3)) & \
\  (\\<forall>W3 Y3 X3. equal(W3::'a,X3) & well_ordering(Y3::'a,W3) --> well_ordering(Y3::'a,X3)) & \
\  (~function(z)) &     \
\  (~equal(recursion_equation_functions(z),null_class)) --> False",
  meson_tac 1);


(*4868 inferences so far.  Searching to depth 12.  4.3 secs*)
val PLA002_1 = prove_hard
 ("(\\<forall>Situation1 Situation2. warm(Situation1) | cold(Situation2)) &    \
\  (\\<forall>Situation. at(a::'a,Situation) --> at(b::'a,walk(b::'a,Situation))) & \
\  (\\<forall>Situation. at(a::'a,Situation) --> at(b::'a,drive(b::'a,Situation))) &        \
\  (\\<forall>Situation. at(b::'a,Situation) --> at(a::'a,walk(a::'a,Situation))) & \
\  (\\<forall>Situation. at(b::'a,Situation) --> at(a::'a,drive(a::'a,Situation))) &        \
\  (\\<forall>Situation. cold(Situation) & at(b::'a,Situation) --> at(c::'a,skate(c::'a,Situation))) &      \
\  (\\<forall>Situation. cold(Situation) & at(c::'a,Situation) --> at(b::'a,skate(b::'a,Situation))) &      \
\  (\\<forall>Situation. warm(Situation) & at(b::'a,Situation) --> at(d::'a,climb(d::'a,Situation))) &      \
\  (\\<forall>Situation. warm(Situation) & at(d::'a,Situation) --> at(b::'a,climb(b::'a,Situation))) &      \
\  (\\<forall>Situation. at(c::'a,Situation) --> at(d::'a,go(d::'a,Situation))) &   \
\  (\\<forall>Situation. at(d::'a,Situation) --> at(c::'a,go(c::'a,Situation))) &   \
\  (\\<forall>Situation. at(c::'a,Situation) --> at(e::'a,go(e::'a,Situation))) &   \
\  (\\<forall>Situation. at(e::'a,Situation) --> at(c::'a,go(c::'a,Situation))) &   \
\  (\\<forall>Situation. at(d::'a,Situation) --> at(f::'a,go(f::'a,Situation))) &   \
\  (\\<forall>Situation. at(f::'a,Situation) --> at(d::'a,go(d::'a,Situation))) &   \
\  (at(f::'a,s0)) & \
\  (\\<forall>S'. ~at(a::'a,S')) --> False",
  meson_tac 1);

(*190 inferences so far.  Searching to depth 10.  0.6 secs*)
val PLA006_1 = prove
 ("(\\<forall>X Y State. holds(X::'a,State) & holds(Y::'a,State) --> holds(and'(X::'a,Y),State)) &  \
\  (\\<forall>State X. holds(EMPTY::'a,State) & holds(clear(X),State) & differ(X::'a,table) --> holds(holding(X),do(pickup(X),State))) &        \
\  (\\<forall>Y X State. holds(on(X::'a,Y),State) & holds(clear(X),State) & holds(EMPTY::'a,State) --> holds(clear(Y),do(pickup(X),State))) &   \
\  (\\<forall>Y State X Z. holds(on(X::'a,Y),State) & differ(X::'a,Z) --> holds(on(X::'a,Y),do(pickup(Z),State))) & \
\  (\\<forall>State X Z. holds(clear(X),State) & differ(X::'a,Z) --> holds(clear(X),do(pickup(Z),State))) & \
\  (\\<forall>X Y State. holds(holding(X),State) & holds(clear(Y),State) --> holds(EMPTY::'a,do(putdown(X::'a,Y),State))) &     \
\  (\\<forall>X Y State. holds(holding(X),State) & holds(clear(Y),State) --> holds(on(X::'a,Y),do(putdown(X::'a,Y),State))) &   \
\  (\\<forall>X Y State. holds(holding(X),State) & holds(clear(Y),State) --> holds(clear(X),do(putdown(X::'a,Y),State))) &  \
\  (\\<forall>Z W X Y State. holds(on(X::'a,Y),State) --> holds(on(X::'a,Y),do(putdown(Z::'a,W),State))) &  \
\  (\\<forall>X State Z Y. holds(clear(Z),State) & differ(Z::'a,Y) --> holds(clear(Z),do(putdown(X::'a,Y),State))) &    \
\  (\\<forall>Y X. differ(Y::'a,X) --> differ(X::'a,Y)) &       \
\  (differ(a::'a,b)) &      \
\  (differ(a::'a,c)) &      \
\  (differ(a::'a,d)) &      \
\  (differ(a::'a,table)) &  \
\  (differ(b::'a,c)) &      \
\  (differ(b::'a,d)) &      \
\  (differ(b::'a,table)) &  \
\  (differ(c::'a,d)) &      \
\  (differ(c::'a,table)) &  \
\  (differ(d::'a,table)) &  \
\  (holds(on(a::'a,table),s0)) &    \
\  (holds(on(b::'a,table),s0)) &    \
\  (holds(on(c::'a,d),s0)) &        \
\  (holds(on(d::'a,table),s0)) &    \
\  (holds(clear(a),s0)) &       \
\  (holds(clear(b),s0)) &       \
\  (holds(clear(c),s0)) &       \
\  (holds(EMPTY::'a,s0)) &  \
\  (\\<forall>State. holds(clear(table),State)) &       \
\  (\\<forall>State. ~holds(on(c::'a,table),State)) --> False",
  meson_tac 1);

(*190 inferences so far.  Searching to depth 10.  0.5 secs*)
val PLA017_1 = prove
 ("(\\<forall>X Y State. holds(X::'a,State) & holds(Y::'a,State) --> holds(and'(X::'a,Y),State)) &  \
\  (\\<forall>State X. holds(EMPTY::'a,State) & holds(clear(X),State) & differ(X::'a,table) --> holds(holding(X),do(pickup(X),State))) &        \
\  (\\<forall>Y X State. holds(on(X::'a,Y),State) & holds(clear(X),State) & holds(EMPTY::'a,State) --> holds(clear(Y),do(pickup(X),State))) &   \
\  (\\<forall>Y State X Z. holds(on(X::'a,Y),State) & differ(X::'a,Z) --> holds(on(X::'a,Y),do(pickup(Z),State))) & \
\  (\\<forall>State X Z. holds(clear(X),State) & differ(X::'a,Z) --> holds(clear(X),do(pickup(Z),State))) & \
\  (\\<forall>X Y State. holds(holding(X),State) & holds(clear(Y),State) --> holds(EMPTY::'a,do(putdown(X::'a,Y),State))) &     \
\  (\\<forall>X Y State. holds(holding(X),State) & holds(clear(Y),State) --> holds(on(X::'a,Y),do(putdown(X::'a,Y),State))) &   \
\  (\\<forall>X Y State. holds(holding(X),State) & holds(clear(Y),State) --> holds(clear(X),do(putdown(X::'a,Y),State))) &  \
\  (\\<forall>Z W X Y State. holds(on(X::'a,Y),State) --> holds(on(X::'a,Y),do(putdown(Z::'a,W),State))) &  \
\  (\\<forall>X State Z Y. holds(clear(Z),State) & differ(Z::'a,Y) --> holds(clear(Z),do(putdown(X::'a,Y),State))) &    \
\  (\\<forall>Y X. differ(Y::'a,X) --> differ(X::'a,Y)) &       \
\  (differ(a::'a,b)) &      \
\  (differ(a::'a,c)) &      \
\  (differ(a::'a,d)) &      \
\  (differ(a::'a,table)) &  \
\  (differ(b::'a,c)) &      \
\  (differ(b::'a,d)) &      \
\  (differ(b::'a,table)) &  \
\  (differ(c::'a,d)) &      \
\  (differ(c::'a,table)) &  \
\  (differ(d::'a,table)) &  \
\  (holds(on(a::'a,table),s0)) &    \
\  (holds(on(b::'a,table),s0)) &    \
\  (holds(on(c::'a,d),s0)) &        \
\  (holds(on(d::'a,table),s0)) &    \
\  (holds(clear(a),s0)) &       \
\  (holds(clear(b),s0)) &       \
\  (holds(clear(c),s0)) &       \
\  (holds(EMPTY::'a,s0)) &  \
\  (\\<forall>State. holds(clear(table),State)) &       \
\  (\\<forall>State. ~holds(on(a::'a,c),State)) --> False",
  meson_tac 1);

(*13732 inferences so far.  Searching to depth 16.  9.8 secs*)
val PLA022_1 = prove_hard
 ("(\\<forall>X Y State. holds(X::'a,State) & holds(Y::'a,State) --> holds(and'(X::'a,Y),State)) &  \
\  (\\<forall>State X. holds(EMPTY::'a,State) & holds(clear(X),State) & differ(X::'a,table) --> holds(holding(X),do(pickup(X),State))) &        \
\  (\\<forall>Y X State. holds(on(X::'a,Y),State) & holds(clear(X),State) & holds(EMPTY::'a,State) --> holds(clear(Y),do(pickup(X),State))) &   \
\  (\\<forall>Y State X Z. holds(on(X::'a,Y),State) & differ(X::'a,Z) --> holds(on(X::'a,Y),do(pickup(Z),State))) & \
\  (\\<forall>State X Z. holds(clear(X),State) & differ(X::'a,Z) --> holds(clear(X),do(pickup(Z),State))) & \
\  (\\<forall>X Y State. holds(holding(X),State) & holds(clear(Y),State) --> holds(EMPTY::'a,do(putdown(X::'a,Y),State))) &     \
\  (\\<forall>X Y State. holds(holding(X),State) & holds(clear(Y),State) --> holds(on(X::'a,Y),do(putdown(X::'a,Y),State))) &   \
\  (\\<forall>X Y State. holds(holding(X),State) & holds(clear(Y),State) --> holds(clear(X),do(putdown(X::'a,Y),State))) &  \
\  (\\<forall>Z W X Y State. holds(on(X::'a,Y),State) --> holds(on(X::'a,Y),do(putdown(Z::'a,W),State))) &  \
\  (\\<forall>X State Z Y. holds(clear(Z),State) & differ(Z::'a,Y) --> holds(clear(Z),do(putdown(X::'a,Y),State))) &    \
\  (\\<forall>Y X. differ(Y::'a,X) --> differ(X::'a,Y)) &       \
\  (differ(a::'a,b)) &      \
\  (differ(a::'a,c)) &      \
\  (differ(a::'a,d)) &      \
\  (differ(a::'a,table)) &  \
\  (differ(b::'a,c)) &      \
\  (differ(b::'a,d)) &      \
\  (differ(b::'a,table)) &  \
\  (differ(c::'a,d)) &      \
\  (differ(c::'a,table)) &  \
\  (differ(d::'a,table)) &  \
\  (holds(on(a::'a,table),s0)) &    \
\  (holds(on(b::'a,table),s0)) &    \
\  (holds(on(c::'a,d),s0)) &        \
\  (holds(on(d::'a,table),s0)) &    \
\  (holds(clear(a),s0)) &       \
\  (holds(clear(b),s0)) &       \
\  (holds(clear(c),s0)) &       \
\  (holds(EMPTY::'a,s0)) &  \
\  (\\<forall>State. holds(clear(table),State)) &       \
\  (\\<forall>State. ~holds(and'(on(c::'a,d),on(a::'a,c)),State)) --> False",
  meson_tac 1);

(*217 inferences so far.  Searching to depth 13.  0.7 secs*)
val PLA022_2 = prove
 ("(\\<forall>X Y State. holds(X::'a,State) & holds(Y::'a,State) --> holds(and'(X::'a,Y),State)) &  \
\  (\\<forall>State X. holds(EMPTY::'a,State) & holds(clear(X),State) & differ(X::'a,table) --> holds(holding(X),do(pickup(X),State))) &        \
\  (\\<forall>Y X State. holds(on(X::'a,Y),State) & holds(clear(X),State) & holds(EMPTY::'a,State) --> holds(clear(Y),do(pickup(X),State))) &   \
\  (\\<forall>Y State X Z. holds(on(X::'a,Y),State) & differ(X::'a,Z) --> holds(on(X::'a,Y),do(pickup(Z),State))) & \
\  (\\<forall>State X Z. holds(clear(X),State) & differ(X::'a,Z) --> holds(clear(X),do(pickup(Z),State))) & \
\  (\\<forall>X Y State. holds(holding(X),State) & holds(clear(Y),State) --> holds(EMPTY::'a,do(putdown(X::'a,Y),State))) &     \
\  (\\<forall>X Y State. holds(holding(X),State) & holds(clear(Y),State) --> holds(on(X::'a,Y),do(putdown(X::'a,Y),State))) &   \
\  (\\<forall>X Y State. holds(holding(X),State) & holds(clear(Y),State) --> holds(clear(X),do(putdown(X::'a,Y),State))) &  \
\  (\\<forall>Z W X Y State. holds(on(X::'a,Y),State) --> holds(on(X::'a,Y),do(putdown(Z::'a,W),State))) &  \
\  (\\<forall>X State Z Y. holds(clear(Z),State) & differ(Z::'a,Y) --> holds(clear(Z),do(putdown(X::'a,Y),State))) &    \
\  (\\<forall>Y X. differ(Y::'a,X) --> differ(X::'a,Y)) &       \
\  (differ(a::'a,b)) &      \
\  (differ(a::'a,c)) &      \
\  (differ(a::'a,d)) &      \
\  (differ(a::'a,table)) &  \
\  (differ(b::'a,c)) &      \
\  (differ(b::'a,d)) &      \
\  (differ(b::'a,table)) &  \
\  (differ(c::'a,d)) &      \
\  (differ(c::'a,table)) &  \
\  (differ(d::'a,table)) &  \
\  (holds(on(a::'a,table),s0)) &    \
\  (holds(on(b::'a,table),s0)) &    \
\  (holds(on(c::'a,d),s0)) &        \
\  (holds(on(d::'a,table),s0)) &    \
\  (holds(clear(a),s0)) &       \
\  (holds(clear(b),s0)) &       \
\  (holds(clear(c),s0)) &       \
\  (holds(EMPTY::'a,s0)) &  \
\  (\\<forall>State. holds(clear(table),State)) &       \
\  (\\<forall>State. ~holds(and'(on(a::'a,c),on(c::'a,d)),State)) --> False",
  meson_tac 1);

(*948 inferences so far.  Searching to depth 18.  1.1 secs*)
val PRV001_1 = prove
 ("(\\<forall>X Y Z. q1(X::'a,Y,Z) & less_or_equal(X::'a,Y) --> q2(X::'a,Y,Z)) &    \
\  (\\<forall>X Y Z. q1(X::'a,Y,Z) --> less_or_equal(X::'a,Y) | q3(X::'a,Y,Z)) &   \
\  (\\<forall>Z X Y. q2(X::'a,Y,Z) --> q4(X::'a,Y,Y)) & \
\  (\\<forall>Z Y X. q3(X::'a,Y,Z) --> q4(X::'a,Y,X)) & \
\  (\\<forall>X. less_or_equal(X::'a,X)) &  \
\  (\\<forall>X Y. less_or_equal(X::'a,Y) & less_or_equal(Y::'a,X) --> equal(X::'a,Y)) &    \
\  (\\<forall>Y X Z. less_or_equal(X::'a,Y) & less_or_equal(Y::'a,Z) --> less_or_equal(X::'a,Z)) &  \
\  (\\<forall>Y X. less_or_equal(X::'a,Y) | less_or_equal(Y::'a,X)) &  \
\  (\\<forall>X Y. equal(X::'a,Y) --> less_or_equal(X::'a,Y)) & \
\  (\\<forall>X Y Z. equal(X::'a,Y) & less_or_equal(X::'a,Z) --> less_or_equal(Y::'a,Z)) &  \
\  (\\<forall>X Z Y. equal(X::'a,Y) & less_or_equal(Z::'a,X) --> less_or_equal(Z::'a,Y)) &  \
\  (q1(a::'a,b,c)) &        \
\  (\\<forall>W. ~(q4(a::'a,b,W) & less_or_equal(a::'a,W) & less_or_equal(b::'a,W) & less_or_equal(W::'a,a))) & \
\  (\\<forall>W. ~(q4(a::'a,b,W) & less_or_equal(a::'a,W) & less_or_equal(b::'a,W) & less_or_equal(W::'a,b))) --> False",
  meson_tac 1);

(*21 inferences so far.  Searching to depth 5.  0.4 secs*)
val PRV003_1 = prove
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X. equal(predecessor(successor(X)),X)) &  \
\  (\\<forall>X. equal(successor(predecessor(X)),X)) &  \
\  (\\<forall>X Y. equal(predecessor(X),predecessor(Y)) --> equal(X::'a,Y)) &       \
\  (\\<forall>X Y. equal(successor(X),successor(Y)) --> equal(X::'a,Y)) &   \
\  (\\<forall>X. LESS_THAN(predecessor(X),X)) & \
\  (\\<forall>X. LESS_THAN(X::'a,successor(X))) &   \
\  (\\<forall>X Y Z. LESS_THAN(X::'a,Y) & LESS_THAN(Y::'a,Z) --> LESS_THAN(X::'a,Z)) &      \
\  (\\<forall>X Y. LESS_THAN(X::'a,Y) | LESS_THAN(Y::'a,X) | equal(X::'a,Y)) &    \
\  (\\<forall>X. ~LESS_THAN(X::'a,X)) &     \
\  (\\<forall>Y X. ~(LESS_THAN(X::'a,Y) & LESS_THAN(Y::'a,X))) &        \
\  (\\<forall>Y X Z. equal(X::'a,Y) & LESS_THAN(X::'a,Z) --> LESS_THAN(Y::'a,Z)) &  \
\  (\\<forall>Y Z X. equal(X::'a,Y) & LESS_THAN(Z::'a,X) --> LESS_THAN(Z::'a,Y)) &  \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(predecessor(X),predecessor(Y))) &       \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(successor(X),successor(Y))) &   \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(a(X),a(Y))) &   \
\  (~LESS_THAN(n::'a,j)) &  \
\  (LESS_THAN(k::'a,j)) &   \
\  (~LESS_THAN(k::'a,i)) &  \
\  (LESS_THAN(i::'a,n)) &   \
\  (LESS_THAN(a(j),a(k))) &     \
\  (\\<forall>X. LESS_THAN(X::'a,j) & LESS_THAN(a(X),a(k)) --> LESS_THAN(X::'a,i)) &    \
\  (\\<forall>X. LESS_THAN(one::'a,i) & LESS_THAN(a(X),a(predecessor(i))) --> LESS_THAN(X::'a,i) | LESS_THAN(n::'a,X)) &   \
\  (\\<forall>X. ~(LESS_THAN(one::'a,X) & LESS_THAN(X::'a,i) & LESS_THAN(a(X),a(predecessor(X))))) &    \
\  (LESS_THAN(j::'a,i)) --> False",
  meson_tac 1);

(*584 inferences so far.  Searching to depth 7.  1.1 secs*)
val PRV005_1 = prove
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X. equal(predecessor(successor(X)),X)) &  \
\  (\\<forall>X. equal(successor(predecessor(X)),X)) &  \
\  (\\<forall>X Y. equal(predecessor(X),predecessor(Y)) --> equal(X::'a,Y)) &       \
\  (\\<forall>X Y. equal(successor(X),successor(Y)) --> equal(X::'a,Y)) &   \
\  (\\<forall>X. LESS_THAN(predecessor(X),X)) & \
\  (\\<forall>X. LESS_THAN(X::'a,successor(X))) &   \
\  (\\<forall>X Y Z. LESS_THAN(X::'a,Y) & LESS_THAN(Y::'a,Z) --> LESS_THAN(X::'a,Z)) &      \
\  (\\<forall>X Y. LESS_THAN(X::'a,Y) | LESS_THAN(Y::'a,X) | equal(X::'a,Y)) &    \
\  (\\<forall>X. ~LESS_THAN(X::'a,X)) &     \
\  (\\<forall>Y X. ~(LESS_THAN(X::'a,Y) & LESS_THAN(Y::'a,X))) &        \
\  (\\<forall>Y X Z. equal(X::'a,Y) & LESS_THAN(X::'a,Z) --> LESS_THAN(Y::'a,Z)) &  \
\  (\\<forall>Y Z X. equal(X::'a,Y) & LESS_THAN(Z::'a,X) --> LESS_THAN(Z::'a,Y)) &  \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(predecessor(X),predecessor(Y))) &       \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(successor(X),successor(Y))) &   \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(a(X),a(Y))) &   \
\  (~LESS_THAN(n::'a,k)) &  \
\  (~LESS_THAN(k::'a,l)) &  \
\  (~LESS_THAN(k::'a,i)) &  \
\  (LESS_THAN(l::'a,n)) &   \
\  (LESS_THAN(one::'a,l)) & \
\  (LESS_THAN(a(k),a(predecessor(l)))) &        \
\  (\\<forall>X. LESS_THAN(X::'a,successor(n)) & LESS_THAN(a(X),a(k)) --> LESS_THAN(X::'a,l)) & \
\  (\\<forall>X. LESS_THAN(one::'a,l) & LESS_THAN(a(X),a(predecessor(l))) --> LESS_THAN(X::'a,l) | LESS_THAN(n::'a,X)) &   \
\  (\\<forall>X. ~(LESS_THAN(one::'a,X) & LESS_THAN(X::'a,l) & LESS_THAN(a(X),a(predecessor(X))))) --> False",
  meson_tac 1);

(*2343 inferences so far.  Searching to depth 8.  3.5 secs*)
val PRV006_1 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X. equal(predecessor(successor(X)),X)) &  \
\  (\\<forall>X. equal(successor(predecessor(X)),X)) &  \
\  (\\<forall>X Y. equal(predecessor(X),predecessor(Y)) --> equal(X::'a,Y)) &       \
\  (\\<forall>X Y. equal(successor(X),successor(Y)) --> equal(X::'a,Y)) &   \
\  (\\<forall>X. LESS_THAN(predecessor(X),X)) & \
\  (\\<forall>X. LESS_THAN(X::'a,successor(X))) &   \
\  (\\<forall>X Y Z. LESS_THAN(X::'a,Y) & LESS_THAN(Y::'a,Z) --> LESS_THAN(X::'a,Z)) &      \
\  (\\<forall>X Y. LESS_THAN(X::'a,Y) | LESS_THAN(Y::'a,X) | equal(X::'a,Y)) &    \
\  (\\<forall>X. ~LESS_THAN(X::'a,X)) &     \
\  (\\<forall>Y X. ~(LESS_THAN(X::'a,Y) & LESS_THAN(Y::'a,X))) &        \
\  (\\<forall>Y X Z. equal(X::'a,Y) & LESS_THAN(X::'a,Z) --> LESS_THAN(Y::'a,Z)) &  \
\  (\\<forall>Y Z X. equal(X::'a,Y) & LESS_THAN(Z::'a,X) --> LESS_THAN(Z::'a,Y)) &  \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(predecessor(X),predecessor(Y))) &       \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(successor(X),successor(Y))) &   \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(a(X),a(Y))) &   \
\  (~LESS_THAN(n::'a,m)) &  \
\  (LESS_THAN(i::'a,m)) &   \
\  (LESS_THAN(i::'a,n)) &   \
\  (~LESS_THAN(i::'a,one)) &        \
\  (LESS_THAN(a(i),a(m))) &     \
\  (\\<forall>X. LESS_THAN(X::'a,successor(n)) & LESS_THAN(a(X),a(m)) --> LESS_THAN(X::'a,i)) & \
\  (\\<forall>X. LESS_THAN(one::'a,i) & LESS_THAN(a(X),a(predecessor(i))) --> LESS_THAN(X::'a,i) | LESS_THAN(n::'a,X)) &   \
\  (\\<forall>X. ~(LESS_THAN(one::'a,X) & LESS_THAN(X::'a,i) & LESS_THAN(a(X),a(predecessor(X))))) --> False",
  meson_tac 1);

(*86 inferences so far.  Searching to depth 14.  0.1 secs*)
val PRV009_1 = prove
 ("(\\<forall>Y X. less_or_equal(X::'a,Y) | less(Y::'a,X)) &   \
\  (less(j::'a,i)) &        \
\  (less_or_equal(m::'a,p)) &       \
\  (less_or_equal(p::'a,q)) &       \
\  (less_or_equal(q::'a,n)) &       \
\  (\\<forall>X Y. less_or_equal(m::'a,X) & less(X::'a,i) & less(j::'a,Y) & less_or_equal(Y::'a,n) --> less_or_equal(a(X),a(Y))) &      \
\  (\\<forall>X Y. less_or_equal(m::'a,X) & less_or_equal(X::'a,Y) & less_or_equal(Y::'a,j) --> less_or_equal(a(X),a(Y))) & \
\  (\\<forall>X Y. less_or_equal(i::'a,X) & less_or_equal(X::'a,Y) & less_or_equal(Y::'a,n) --> less_or_equal(a(X),a(Y))) & \
\  (~less_or_equal(a(p),a(q))) --> False",
  meson_tac 1);

(*222 inferences so far.  Searching to depth 8.  0.4 secs*)
val PUZ012_1 = prove
 ("(\\<forall>X. equal_fruits(X::'a,X)) &   \
\  (\\<forall>X. equal_boxes(X::'a,X)) &    \
\  (\\<forall>X Y. ~(label(X::'a,Y) & contains(X::'a,Y))) &     \
\  (\\<forall>X. contains(boxa::'a,X) | contains(boxb::'a,X) | contains(boxc::'a,X)) &    \
\  (\\<forall>X. contains(X::'a,apples) | contains(X::'a,bananas) | contains(X::'a,oranges)) &    \
\  (\\<forall>X Y Z. contains(X::'a,Y) & contains(X::'a,Z) --> equal_fruits(Y::'a,Z)) &     \
\  (\\<forall>Y X Z. contains(X::'a,Y) & contains(Z::'a,Y) --> equal_boxes(X::'a,Z)) &      \
\  (~equal_boxes(boxa::'a,boxb)) &  \
\  (~equal_boxes(boxb::'a,boxc)) &  \
\  (~equal_boxes(boxa::'a,boxc)) &  \
\  (~equal_fruits(apples::'a,bananas)) &    \
\  (~equal_fruits(bananas::'a,oranges)) &   \
\  (~equal_fruits(apples::'a,oranges)) &    \
\  (label(boxa::'a,apples)) &       \
\  (label(boxb::'a,oranges)) &      \
\  (label(boxc::'a,bananas)) &      \
\  (contains(boxb::'a,apples)) &    \
\  (~(contains(boxa::'a,bananas) & contains(boxc::'a,oranges))) --> False",
  meson_tac 1);

(*35 inferences so far.  Searching to depth 5.  3.2 secs*)
val PUZ020_1 = prove
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>A B. equal(A::'a,B) --> equal(statement_by(A),statement_by(B))) &     \
\  (\\<forall>X. person(X) --> knight(X) | knave(X)) & \
\  (\\<forall>X. ~(person(X) & knight(X) & knave(X))) & \
\  (\\<forall>X Y. says(X::'a,Y) & a_truth(Y) --> a_truth(Y)) &     \
\  (\\<forall>X Y. ~(says(X::'a,Y) & equal(X::'a,Y))) & \
\  (\\<forall>Y X. says(X::'a,Y) --> equal(Y::'a,statement_by(X))) &    \
\  (\\<forall>X Y. ~(person(X) & equal(X::'a,statement_by(Y)))) &   \
\  (\\<forall>X. person(X) & a_truth(statement_by(X)) --> knight(X)) &  \
\  (\\<forall>X. person(X) --> a_truth(statement_by(X)) | knave(X)) &  \
\  (\\<forall>X Y. equal(X::'a,Y) & knight(X) --> knight(Y)) &      \
\  (\\<forall>X Y. equal(X::'a,Y) & knave(X) --> knave(Y)) &        \
\  (\\<forall>X Y. equal(X::'a,Y) & person(X) --> person(Y)) &      \
\  (\\<forall>X Y Z. equal(X::'a,Y) & says(X::'a,Z) --> says(Y::'a,Z)) &    \
\  (\\<forall>X Z Y. equal(X::'a,Y) & says(Z::'a,X) --> says(Z::'a,Y)) &    \
\  (\\<forall>X Y. equal(X::'a,Y) & a_truth(X) --> a_truth(Y)) &    \
\  (\\<forall>X Y. knight(X) & says(X::'a,Y) --> a_truth(Y)) &      \
\  (\\<forall>X Y. ~(knave(X) & says(X::'a,Y) & a_truth(Y))) &      \
\  (person(husband)) &  \
\  (person(wife)) &     \
\  (~equal(husband::'a,wife)) &     \
\  (says(husband::'a,statement_by(husband))) &      \
\  (a_truth(statement_by(husband)) & knight(husband) --> knight(wife)) &        \
\  (knight(husband) --> a_truth(statement_by(husband))) &       \
\  (a_truth(statement_by(husband)) | knight(wife)) &   \
\  (knight(wife) --> a_truth(statement_by(husband))) &  \
\  (~knight(husband)) --> False",
  meson_tac 1);

(*121806 inferences so far.  Searching to depth 17.  63.0 secs*)
val PUZ025_1 = prove_hard
 ("(\\<forall>X. a_truth(truthteller(X)) | a_truth(liar(X))) & \
\  (\\<forall>X. ~(a_truth(truthteller(X)) & a_truth(liar(X)))) &       \
\  (\\<forall>Truthteller Statement. a_truth(truthteller(Truthteller)) & a_truth(says(Truthteller::'a,Statement)) --> a_truth(Statement)) & \
\  (\\<forall>Liar Statement. ~(a_truth(liar(Liar)) & a_truth(says(Liar::'a,Statement)) & a_truth(Statement))) &    \
\  (\\<forall>Statement Truthteller. a_truth(Statement) & a_truth(says(Truthteller::'a,Statement)) --> a_truth(truthteller(Truthteller))) & \
\  (\\<forall>Statement Liar. a_truth(says(Liar::'a,Statement)) --> a_truth(Statement) | a_truth(liar(Liar))) &    \
\  (\\<forall>Z X Y. people(X::'a,Y,Z) & a_truth(liar(X)) & a_truth(liar(Y)) --> a_truth(equal_type(X::'a,Y))) &        \
\  (\\<forall>Z X Y. people(X::'a,Y,Z) & a_truth(truthteller(X)) & a_truth(truthteller(Y)) --> a_truth(equal_type(X::'a,Y))) &  \
\  (\\<forall>X Y. a_truth(equal_type(X::'a,Y)) & a_truth(truthteller(X)) --> a_truth(truthteller(Y))) &    \
\  (\\<forall>X Y. a_truth(equal_type(X::'a,Y)) & a_truth(liar(X)) --> a_truth(liar(Y))) &  \
\  (\\<forall>X Y. a_truth(truthteller(X)) --> a_truth(equal_type(X::'a,Y)) | a_truth(liar(Y))) &  \
\  (\\<forall>X Y. a_truth(liar(X)) --> a_truth(equal_type(X::'a,Y)) | a_truth(truthteller(Y))) &  \
\  (\\<forall>Y X. a_truth(equal_type(X::'a,Y)) --> a_truth(equal_type(Y::'a,X))) &     \
\  (\\<forall>X Y. ask_1_if_2(X::'a,Y) & a_truth(truthteller(X)) & a_truth(Y) --> answer(yes)) &    \
\  (\\<forall>X Y. ask_1_if_2(X::'a,Y) & a_truth(truthteller(X)) --> a_truth(Y) | answer(no)) &    \
\  (\\<forall>X Y. ask_1_if_2(X::'a,Y) & a_truth(liar(X)) & a_truth(Y) --> answer(no)) &    \
\  (\\<forall>X Y. ask_1_if_2(X::'a,Y) & a_truth(liar(X)) --> a_truth(Y) | answer(yes)) &  \
\  (people(b::'a,c,a)) &    \
\  (people(a::'a,b,a)) &    \
\  (people(a::'a,c,b)) &    \
\  (people(c::'a,b,a)) &    \
\  (a_truth(says(a::'a,equal_type(b::'a,c)))) & \
\  (ask_1_if_2(c::'a,equal_type(a::'a,b))) &    \
\  (\\<forall>Answer. ~answer(Answer)) --> False",
  meson_tac 1);


(*621 inferences so far.  Searching to depth 18.  0.2 secs*)
val PUZ029_1 = prove
 ("(\\<forall>X. dances_on_tightropes(X) | eats_pennybuns(X) | old(X)) &      \
\  (\\<forall>X. pig(X) & liable_to_giddiness(X) --> treated_with_respect(X)) & \
\  (\\<forall>X. wise(X) & balloonist(X) --> has_umbrella(X)) & \
\  (\\<forall>X. ~(looks_ridiculous(X) & eats_pennybuns(X) & eats_lunch_in_public(X))) &        \
\  (\\<forall>X. balloonist(X) & young(X) --> liable_to_giddiness(X)) & \
\  (\\<forall>X. fat(X) & looks_ridiculous(X) --> dances_on_tightropes(X) | eats_lunch_in_public(X)) & \
\  (\\<forall>X. ~(liable_to_giddiness(X) & wise(X) & dances_on_tightropes(X))) &       \
\  (\\<forall>X. pig(X) & has_umbrella(X) --> looks_ridiculous(X)) &    \
\  (\\<forall>X. treated_with_respect(X) --> dances_on_tightropes(X) | fat(X)) &       \
\  (\\<forall>X. young(X) | old(X)) &  \
\  (\\<forall>X. ~(young(X) & old(X))) &        \
\  (wise(piggy)) &      \
\  (young(piggy)) &     \
\  (pig(piggy)) &       \
\  (balloonist(piggy)) --> False",
  meson_tac 1);

(*93620 inferences so far.  Searching to depth 24.  65.9 secs*)
val RNG001_3 = prove_hard
 ("(\\<forall>X. sum(additive_identity::'a,X,X)) &  \
\  (\\<forall>X. sum(additive_inverse(X),X,additive_identity)) &        \
\  (\\<forall>Y U Z X V W. sum(X::'a,Y,U) & sum(Y::'a,Z,V) & sum(U::'a,Z,W) --> sum(X::'a,V,W)) &       \
\  (\\<forall>Y X V U Z W. sum(X::'a,Y,U) & sum(Y::'a,Z,V) & sum(X::'a,V,W) --> sum(U::'a,Z,W)) &       \
\  (\\<forall>X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (\\<forall>Y Z X V3 V1 V2 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & product(X::'a,V3,V4) --> sum(V1::'a,V2,V4)) &        \
\  (\\<forall>Y Z V1 V2 X V3 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(X::'a,V3,V4)) &        \
\  (~product(a::'a,additive_identity,additive_identity)) --> False",
  meson_tac 1);


(****************SLOW
3057170 inferences so far.  Searching to depth 16.  No proof after 45 minutes.
val RNG001_5 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X. sum(additive_identity::'a,X,X)) &  \
\  (\\<forall>X. sum(X::'a,additive_identity,X)) &  \
\  (\\<forall>X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (\\<forall>X Y. sum(X::'a,Y,add(X::'a,Y))) & \
\  (\\<forall>X. sum(additive_inverse(X),X,additive_identity)) &        \
\  (\\<forall>X. sum(X::'a,additive_inverse(X),additive_identity)) &        \
\  (\\<forall>Y U Z X V W. sum(X::'a,Y,U) & sum(Y::'a,Z,V) & sum(U::'a,Z,W) --> sum(X::'a,V,W)) &       \
\  (\\<forall>Y X V U Z W. sum(X::'a,Y,U) & sum(Y::'a,Z,V) & sum(X::'a,V,W) --> sum(U::'a,Z,W)) &       \
\  (\\<forall>Y X Z. sum(X::'a,Y,Z) --> sum(Y::'a,X,Z)) &       \
\  (\\<forall>Y U Z X V W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(U::'a,Z,W) --> product(X::'a,V,W)) &       \
\  (\\<forall>Y X V U Z W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(X::'a,V,W) --> product(U::'a,Z,W)) &       \
\  (\\<forall>Y Z X V3 V1 V2 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & product(X::'a,V3,V4) --> sum(V1::'a,V2,V4)) &        \
\  (\\<forall>Y Z V1 V2 X V3 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(X::'a,V3,V4)) &        \
\  (\\<forall>Y Z V3 X V1 V2 V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & product(V3::'a,X,V4) --> sum(V1::'a,V2,V4)) &        \
\  (\\<forall>Y Z V1 V2 V3 X V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(V3::'a,X,V4)) &        \
\  (\\<forall>X Y U V. sum(X::'a,Y,U) & sum(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (\\<forall>X Y U V. product(X::'a,Y,U) & product(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(additive_inverse(X),additive_inverse(Y))) &     \
\  (\\<forall>X Y W. equal(X::'a,Y) --> equal(add(X::'a,W),add(Y::'a,W))) & \
\  (\\<forall>X Y W Z. equal(X::'a,Y) & sum(X::'a,W,Z) --> sum(Y::'a,W,Z)) &        \
\  (\\<forall>X W Y Z. equal(X::'a,Y) & sum(W::'a,X,Z) --> sum(W::'a,Y,Z)) &        \
\  (\\<forall>X W Z Y. equal(X::'a,Y) & sum(W::'a,Z,X) --> sum(W::'a,Z,Y)) &        \
\  (\\<forall>X Y W. equal(X::'a,Y) --> equal(multiply(X::'a,W),multiply(Y::'a,W))) &       \
\  (\\<forall>X Y W Z. equal(X::'a,Y) & product(X::'a,W,Z) --> product(Y::'a,W,Z)) &        \
\  (\\<forall>X W Y Z. equal(X::'a,Y) & product(W::'a,X,Z) --> product(W::'a,Y,Z)) &        \
\  (\\<forall>X W Z Y. equal(X::'a,Y) & product(W::'a,Z,X) --> product(W::'a,Z,Y)) &        \
\  (~product(a::'a,additive_identity,additive_identity)) --> False",
  meson_tac 1);
****************)

(*0 inferences so far.  Searching to depth 0.  0.5 secs*)
val RNG011_5 = prove
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>A B C. equal(A::'a,B) --> equal(add(A::'a,C),add(B::'a,C))) & \
\  (\\<forall>D F' E. equal(D::'a,E) --> equal(add(F'::'a,D),add(F'::'a,E))) &      \
\  (\\<forall>G H. equal(G::'a,H) --> equal(additive_inverse(G),additive_inverse(H))) &     \
\  (\\<forall>I' J K'. equal(I'::'a,J) --> equal(multiply(I'::'a,K'),multiply(J::'a,K'))) & \
\  (\\<forall>L N M. equal(L::'a,M) --> equal(multiply(N::'a,L),multiply(N::'a,M))) &       \
\  (\\<forall>A B C D. equal(A::'a,B) --> equal(associator(A::'a,C,D),associator(B::'a,C,D))) &     \
\  (\\<forall>E G F' H. equal(E::'a,F') --> equal(associator(G::'a,E,H),associator(G::'a,F',H))) &  \
\  (\\<forall>I' K' L J. equal(I'::'a,J) --> equal(associator(K'::'a,L,I'),associator(K'::'a,L,J))) &       \
\  (\\<forall>M N O_. equal(M::'a,N) --> equal(commutator(M::'a,O_),commutator(N::'a,O_))) &   \
\  (\\<forall>P R Q. equal(P::'a,Q) --> equal(commutator(R::'a,P),commutator(R::'a,Q))) &   \
\  (\\<forall>Y X. equal(add(X::'a,Y),add(Y::'a,X))) &  \
\  (\\<forall>X Y Z. equal(add(add(X::'a,Y),Z),add(X::'a,add(Y::'a,Z)))) &  \
\  (\\<forall>X. equal(add(X::'a,additive_identity),X)) &   \
\  (\\<forall>X. equal(add(additive_identity::'a,X),X)) &   \
\  (\\<forall>X. equal(add(X::'a,additive_inverse(X)),additive_identity)) & \
\  (\\<forall>X. equal(add(additive_inverse(X),X),additive_identity)) & \
\  (equal(additive_inverse(additive_identity),additive_identity)) &     \
\  (\\<forall>X Y. equal(add(X::'a,add(additive_inverse(X),Y)),Y)) &        \
\  (\\<forall>X Y. equal(additive_inverse(add(X::'a,Y)),add(additive_inverse(X),additive_inverse(Y)))) &    \
\  (\\<forall>X. equal(additive_inverse(additive_inverse(X)),X)) &      \
\  (\\<forall>X. equal(multiply(X::'a,additive_identity),additive_identity)) &      \
\  (\\<forall>X. equal(multiply(additive_identity::'a,X),additive_identity)) &      \
\  (\\<forall>X Y. equal(multiply(additive_inverse(X),additive_inverse(Y)),multiply(X::'a,Y))) &    \
\  (\\<forall>X Y. equal(multiply(X::'a,additive_inverse(Y)),additive_inverse(multiply(X::'a,Y)))) &    \
\  (\\<forall>X Y. equal(multiply(additive_inverse(X),Y),additive_inverse(multiply(X::'a,Y)))) &    \
\  (\\<forall>Y X Z. equal(multiply(X::'a,add(Y::'a,Z)),add(multiply(X::'a,Y),multiply(X::'a,Z)))) &    \
\  (\\<forall>X Y Z. equal(multiply(add(X::'a,Y),Z),add(multiply(X::'a,Z),multiply(Y::'a,Z)))) &    \
\  (\\<forall>X Y. equal(multiply(multiply(X::'a,Y),Y),multiply(X::'a,multiply(Y::'a,Y)))) &        \
\  (\\<forall>X Y Z. equal(associator(X::'a,Y,Z),add(multiply(multiply(X::'a,Y),Z),additive_inverse(multiply(X::'a,multiply(Y::'a,Z)))))) &     \
\  (\\<forall>X Y. equal(commutator(X::'a,Y),add(multiply(Y::'a,X),additive_inverse(multiply(X::'a,Y))))) & \
\  (\\<forall>X Y. equal(multiply(multiply(associator(X::'a,X,Y),X),associator(X::'a,X,Y)),additive_identity)) &        \
\  (~equal(multiply(multiply(associator(a::'a,a,b),a),associator(a::'a,a,b)),additive_identity)) --> False",
  meson_tac 1);

(*202 inferences so far.  Searching to depth 8.  0.6 secs*)
val RNG023_6 = prove
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>Y X. equal(add(X::'a,Y),add(Y::'a,X))) &  \
\  (\\<forall>X Y Z. equal(add(X::'a,add(Y::'a,Z)),add(add(X::'a,Y),Z))) &  \
\  (\\<forall>X. equal(add(additive_identity::'a,X),X)) &   \
\  (\\<forall>X. equal(add(X::'a,additive_identity),X)) &   \
\  (\\<forall>X. equal(multiply(additive_identity::'a,X),additive_identity)) &      \
\  (\\<forall>X. equal(multiply(X::'a,additive_identity),additive_identity)) &      \
\  (\\<forall>X. equal(add(additive_inverse(X),X),additive_identity)) & \
\  (\\<forall>X. equal(add(X::'a,additive_inverse(X)),additive_identity)) & \
\  (\\<forall>Y X Z. equal(multiply(X::'a,add(Y::'a,Z)),add(multiply(X::'a,Y),multiply(X::'a,Z)))) &    \
\  (\\<forall>X Y Z. equal(multiply(add(X::'a,Y),Z),add(multiply(X::'a,Z),multiply(Y::'a,Z)))) &    \
\  (\\<forall>X. equal(additive_inverse(additive_inverse(X)),X)) &      \
\  (\\<forall>X Y. equal(multiply(multiply(X::'a,Y),Y),multiply(X::'a,multiply(Y::'a,Y)))) &        \
\  (\\<forall>X Y. equal(multiply(multiply(X::'a,X),Y),multiply(X::'a,multiply(X::'a,Y)))) &        \
\  (\\<forall>X Y Z. equal(associator(X::'a,Y,Z),add(multiply(multiply(X::'a,Y),Z),additive_inverse(multiply(X::'a,multiply(Y::'a,Z)))))) &     \
\  (\\<forall>X Y. equal(commutator(X::'a,Y),add(multiply(Y::'a,X),additive_inverse(multiply(X::'a,Y))))) & \
\  (\\<forall>D E F'. equal(D::'a,E) --> equal(add(D::'a,F'),add(E::'a,F'))) &      \
\  (\\<forall>G I' H. equal(G::'a,H) --> equal(add(I'::'a,G),add(I'::'a,H))) &      \
\  (\\<forall>J K'. equal(J::'a,K') --> equal(additive_inverse(J),additive_inverse(K'))) &  \
\  (\\<forall>L M N O_. equal(L::'a,M) --> equal(associator(L::'a,N,O_),associator(M::'a,N,O_))) &     \
\  (\\<forall>P R Q S'. equal(P::'a,Q) --> equal(associator(R::'a,P,S'),associator(R::'a,Q,S'))) &  \
\  (\\<forall>T' V W U. equal(T'::'a,U) --> equal(associator(V::'a,W,T'),associator(V::'a,W,U))) &  \
\  (\\<forall>X Y Z. equal(X::'a,Y) --> equal(commutator(X::'a,Z),commutator(Y::'a,Z))) &   \
\  (\\<forall>A1 C1 B1. equal(A1::'a,B1) --> equal(commutator(C1::'a,A1),commutator(C1::'a,B1))) &  \
\  (\\<forall>D1 E1 F1. equal(D1::'a,E1) --> equal(multiply(D1::'a,F1),multiply(E1::'a,F1))) &      \
\  (\\<forall>G1 I1 H1. equal(G1::'a,H1) --> equal(multiply(I1::'a,G1),multiply(I1::'a,H1))) &      \
\  (~equal(associator(x::'a,x,y),additive_identity)) --> False",
  meson_tac 1);

(*0 inferences so far.  Searching to depth 0.  0.6 secs*)
val RNG028_2 = prove
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X. equal(add(additive_identity::'a,X),X)) &   \
\  (\\<forall>X. equal(multiply(additive_identity::'a,X),additive_identity)) &      \
\  (\\<forall>X. equal(multiply(X::'a,additive_identity),additive_identity)) &      \
\  (\\<forall>X. equal(add(additive_inverse(X),X),additive_identity)) & \
\  (\\<forall>X Y. equal(additive_inverse(add(X::'a,Y)),add(additive_inverse(X),additive_inverse(Y)))) &    \
\  (\\<forall>X. equal(additive_inverse(additive_inverse(X)),X)) &      \
\  (\\<forall>Y X Z. equal(multiply(X::'a,add(Y::'a,Z)),add(multiply(X::'a,Y),multiply(X::'a,Z)))) &    \
\  (\\<forall>X Y Z. equal(multiply(add(X::'a,Y),Z),add(multiply(X::'a,Z),multiply(Y::'a,Z)))) &    \
\  (\\<forall>X Y. equal(multiply(multiply(X::'a,Y),Y),multiply(X::'a,multiply(Y::'a,Y)))) &        \
\  (\\<forall>X Y. equal(multiply(multiply(X::'a,X),Y),multiply(X::'a,multiply(X::'a,Y)))) &        \
\  (\\<forall>X Y. equal(multiply(additive_inverse(X),Y),additive_inverse(multiply(X::'a,Y)))) &    \
\  (\\<forall>X Y. equal(multiply(X::'a,additive_inverse(Y)),additive_inverse(multiply(X::'a,Y)))) &    \
\  (equal(additive_inverse(additive_identity),additive_identity)) &     \
\  (\\<forall>Y X. equal(add(X::'a,Y),add(Y::'a,X))) &  \
\  (\\<forall>X Y Z. equal(add(X::'a,add(Y::'a,Z)),add(add(X::'a,Y),Z))) &  \
\  (\\<forall>Z X Y. equal(add(X::'a,Z),add(Y::'a,Z)) --> equal(X::'a,Y)) & \
\  (\\<forall>Z X Y. equal(add(Z::'a,X),add(Z::'a,Y)) --> equal(X::'a,Y)) & \
\  (\\<forall>D E F'. equal(D::'a,E) --> equal(add(D::'a,F'),add(E::'a,F'))) &      \
\  (\\<forall>G I' H. equal(G::'a,H) --> equal(add(I'::'a,G),add(I'::'a,H))) &      \
\  (\\<forall>J K'. equal(J::'a,K') --> equal(additive_inverse(J),additive_inverse(K'))) &  \
\  (\\<forall>D1 E1 F1. equal(D1::'a,E1) --> equal(multiply(D1::'a,F1),multiply(E1::'a,F1))) &      \
\  (\\<forall>G1 I1 H1. equal(G1::'a,H1) --> equal(multiply(I1::'a,G1),multiply(I1::'a,H1))) &      \
\  (\\<forall>X Y Z. equal(associator(X::'a,Y,Z),add(multiply(multiply(X::'a,Y),Z),additive_inverse(multiply(X::'a,multiply(Y::'a,Z)))))) &     \
\  (\\<forall>L M N O_. equal(L::'a,M) --> equal(associator(L::'a,N,O_),associator(M::'a,N,O_))) &     \
\  (\\<forall>P R Q S'. equal(P::'a,Q) --> equal(associator(R::'a,P,S'),associator(R::'a,Q,S'))) &  \
\  (\\<forall>T' V W U. equal(T'::'a,U) --> equal(associator(V::'a,W,T'),associator(V::'a,W,U))) &  \
\  (\\<forall>X Y. ~equal(multiply(multiply(Y::'a,X),Y),multiply(Y::'a,multiply(X::'a,Y)))) &       \
\  (\\<forall>X Y Z. ~equal(associator(Y::'a,X,Z),additive_inverse(associator(X::'a,Y,Z)))) &   \
\  (\\<forall>X Y Z. ~equal(associator(Z::'a,Y,X),additive_inverse(associator(X::'a,Y,Z)))) &   \
\  (~equal(multiply(multiply(cx::'a,multiply(cy::'a,cx)),cz),multiply(cx::'a,multiply(cy::'a,multiply(cx::'a,cz))))) --> False",
  meson_tac 1);

(*209 inferences so far.  Searching to depth 9.  1.2 secs*)
val RNG038_2 = prove
 ("(\\<forall>X. sum(X::'a,additive_identity,X)) &  \
\  (\\<forall>X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (\\<forall>X Y. sum(X::'a,Y,add(X::'a,Y))) & \
\  (\\<forall>X. sum(X::'a,additive_inverse(X),additive_identity)) &        \
\  (\\<forall>Y U Z X V W. sum(X::'a,Y,U) & sum(Y::'a,Z,V) & sum(U::'a,Z,W) --> sum(X::'a,V,W)) &       \
\  (\\<forall>Y X V U Z W. sum(X::'a,Y,U) & sum(Y::'a,Z,V) & sum(X::'a,V,W) --> sum(U::'a,Z,W)) &       \
\  (\\<forall>Y X Z. sum(X::'a,Y,Z) --> sum(Y::'a,X,Z)) &       \
\  (\\<forall>Y U Z X V W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(U::'a,Z,W) --> product(X::'a,V,W)) &       \
\  (\\<forall>Y X V U Z W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(X::'a,V,W) --> product(U::'a,Z,W)) &       \
\  (\\<forall>Y Z X V3 V1 V2 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & product(X::'a,V3,V4) --> sum(V1::'a,V2,V4)) &        \
\  (\\<forall>Y Z V1 V2 X V3 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(X::'a,V3,V4)) &        \
\  (\\<forall>Y Z V3 X V1 V2 V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & product(V3::'a,X,V4) --> sum(V1::'a,V2,V4)) &        \
\  (\\<forall>Y Z V1 V2 V3 X V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(V3::'a,X,V4)) &        \
\  (\\<forall>X Y U V. sum(X::'a,Y,U) & sum(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (\\<forall>X Y U V. product(X::'a,Y,U) & product(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(additive_inverse(X),additive_inverse(Y))) &     \
\  (\\<forall>X Y W. equal(X::'a,Y) --> equal(add(X::'a,W),add(Y::'a,W))) & \
\  (\\<forall>X Y W Z. equal(X::'a,Y) & sum(X::'a,W,Z) --> sum(Y::'a,W,Z)) &        \
\  (\\<forall>X W Y Z. equal(X::'a,Y) & sum(W::'a,X,Z) --> sum(W::'a,Y,Z)) &        \
\  (\\<forall>X W Z Y. equal(X::'a,Y) & sum(W::'a,Z,X) --> sum(W::'a,Z,Y)) &        \
\  (\\<forall>X Y W. equal(X::'a,Y) --> equal(multiply(X::'a,W),multiply(Y::'a,W))) &       \
\  (\\<forall>X Y W Z. equal(X::'a,Y) & product(X::'a,W,Z) --> product(Y::'a,W,Z)) &        \
\  (\\<forall>X W Y Z. equal(X::'a,Y) & product(W::'a,X,Z) --> product(W::'a,Y,Z)) &        \
\  (\\<forall>X W Z Y. equal(X::'a,Y) & product(W::'a,Z,X) --> product(W::'a,Z,Y)) &        \
\  (\\<forall>X. product(additive_identity::'a,X,additive_identity)) &      \
\  (\\<forall>X. product(X::'a,additive_identity,additive_identity)) &      \
\  (\\<forall>X Y. equal(X::'a,additive_identity) --> product(X::'a,h(X::'a,Y),Y)) &        \
\  (product(a::'a,b,additive_identity)) &   \
\  (~equal(a::'a,additive_identity)) &      \
\  (~equal(b::'a,additive_identity)) --> False",
  meson_tac 1);

(*2660 inferences so far.  Searching to depth 10.  7.0 secs*)
val RNG040_2 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(additive_inverse(X),additive_inverse(Y))) &     \
\  (\\<forall>X Y W. equal(X::'a,Y) --> equal(add(X::'a,W),add(Y::'a,W))) & \
\  (\\<forall>X W Y. equal(X::'a,Y) --> equal(add(W::'a,X),add(W::'a,Y))) & \
\  (\\<forall>X Y W Z. equal(X::'a,Y) & sum(X::'a,W,Z) --> sum(Y::'a,W,Z)) &        \
\  (\\<forall>X W Y Z. equal(X::'a,Y) & sum(W::'a,X,Z) --> sum(W::'a,Y,Z)) &        \
\  (\\<forall>X W Z Y. equal(X::'a,Y) & sum(W::'a,Z,X) --> sum(W::'a,Z,Y)) &        \
\  (\\<forall>X Y W. equal(X::'a,Y) --> equal(multiply(X::'a,W),multiply(Y::'a,W))) &       \
\  (\\<forall>X W Y. equal(X::'a,Y) --> equal(multiply(W::'a,X),multiply(W::'a,Y))) &       \
\  (\\<forall>X Y W Z. equal(X::'a,Y) & product(X::'a,W,Z) --> product(Y::'a,W,Z)) &        \
\  (\\<forall>X W Y Z. equal(X::'a,Y) & product(W::'a,X,Z) --> product(W::'a,Y,Z)) &        \
\  (\\<forall>X W Z Y. equal(X::'a,Y) & product(W::'a,Z,X) --> product(W::'a,Z,Y)) &        \
\  (\\<forall>X. sum(additive_identity::'a,X,X)) &  \
\  (\\<forall>X. sum(X::'a,additive_identity,X)) &  \
\  (\\<forall>X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (\\<forall>X Y. sum(X::'a,Y,add(X::'a,Y))) & \
\  (\\<forall>X. sum(additive_inverse(X),X,additive_identity)) &        \
\  (\\<forall>X. sum(X::'a,additive_inverse(X),additive_identity)) &        \
\  (\\<forall>Y U Z X V W. sum(X::'a,Y,U) & sum(Y::'a,Z,V) & sum(U::'a,Z,W) --> sum(X::'a,V,W)) &       \
\  (\\<forall>Y X V U Z W. sum(X::'a,Y,U) & sum(Y::'a,Z,V) & sum(X::'a,V,W) --> sum(U::'a,Z,W)) &       \
\  (\\<forall>Y X Z. sum(X::'a,Y,Z) --> sum(Y::'a,X,Z)) &       \
\  (\\<forall>Y U Z X V W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(U::'a,Z,W) --> product(X::'a,V,W)) &       \
\  (\\<forall>Y X V U Z W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(X::'a,V,W) --> product(U::'a,Z,W)) &       \
\  (\\<forall>Y Z X V3 V1 V2 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & product(X::'a,V3,V4) --> sum(V1::'a,V2,V4)) &        \
\  (\\<forall>Y Z V1 V2 X V3 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(X::'a,V3,V4)) &        \
\  (\\<forall>X Y U V. sum(X::'a,Y,U) & sum(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (\\<forall>X Y U V. product(X::'a,Y,U) & product(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (\\<forall>A. product(A::'a,multiplicative_identity,A)) &        \
\  (\\<forall>A. product(multiplicative_identity::'a,A,A)) &        \
\  (\\<forall>A. product(A::'a,h(A),multiplicative_identity) | equal(A::'a,additive_identity)) &       \
\  (\\<forall>A. product(h(A),A,multiplicative_identity) | equal(A::'a,additive_identity)) &       \
\  (\\<forall>B A C. product(A::'a,B,C) --> product(B::'a,A,C)) &       \
\  (\\<forall>A B. equal(A::'a,B) --> equal(h(A),h(B))) &   \
\  (sum(b::'a,c,d)) &       \
\  (product(d::'a,a,additive_identity)) &   \
\  (product(b::'a,a,l)) &   \
\  (product(c::'a,a,n)) &   \
\  (~sum(l::'a,n,additive_identity)) --> False",
  meson_tac 1);

(*8991 inferences so far.  Searching to depth 9.  22.2 secs*)
val RNG041_1 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>X. sum(additive_identity::'a,X,X)) &  \
\  (\\<forall>X. sum(X::'a,additive_identity,X)) &  \
\  (\\<forall>X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (\\<forall>X Y. sum(X::'a,Y,add(X::'a,Y))) & \
\  (\\<forall>X. sum(additive_inverse(X),X,additive_identity)) &        \
\  (\\<forall>X. sum(X::'a,additive_inverse(X),additive_identity)) &        \
\  (\\<forall>Y U Z X V W. sum(X::'a,Y,U) & sum(Y::'a,Z,V) & sum(U::'a,Z,W) --> sum(X::'a,V,W)) &       \
\  (\\<forall>Y X V U Z W. sum(X::'a,Y,U) & sum(Y::'a,Z,V) & sum(X::'a,V,W) --> sum(U::'a,Z,W)) &       \
\  (\\<forall>Y X Z. sum(X::'a,Y,Z) --> sum(Y::'a,X,Z)) &       \
\  (\\<forall>Y U Z X V W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(U::'a,Z,W) --> product(X::'a,V,W)) &       \
\  (\\<forall>Y X V U Z W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(X::'a,V,W) --> product(U::'a,Z,W)) &       \
\  (\\<forall>Y Z X V3 V1 V2 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & product(X::'a,V3,V4) --> sum(V1::'a,V2,V4)) &        \
\  (\\<forall>Y Z V1 V2 X V3 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(X::'a,V3,V4)) &        \
\  (\\<forall>Y Z V3 X V1 V2 V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & product(V3::'a,X,V4) --> sum(V1::'a,V2,V4)) &        \
\  (\\<forall>Y Z V1 V2 V3 X V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(V3::'a,X,V4)) &        \
\  (\\<forall>X Y U V. sum(X::'a,Y,U) & sum(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (\\<forall>X Y U V. product(X::'a,Y,U) & product(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (\\<forall>X Y. equal(X::'a,Y) --> equal(additive_inverse(X),additive_inverse(Y))) &     \
\  (\\<forall>X Y W. equal(X::'a,Y) --> equal(add(X::'a,W),add(Y::'a,W))) & \
\  (\\<forall>X W Y. equal(X::'a,Y) --> equal(add(W::'a,X),add(W::'a,Y))) & \
\  (\\<forall>X Y W Z. equal(X::'a,Y) & sum(X::'a,W,Z) --> sum(Y::'a,W,Z)) &        \
\  (\\<forall>X W Y Z. equal(X::'a,Y) & sum(W::'a,X,Z) --> sum(W::'a,Y,Z)) &        \
\  (\\<forall>X W Z Y. equal(X::'a,Y) & sum(W::'a,Z,X) --> sum(W::'a,Z,Y)) &        \
\  (\\<forall>X Y W. equal(X::'a,Y) --> equal(multiply(X::'a,W),multiply(Y::'a,W))) &       \
\  (\\<forall>X W Y. equal(X::'a,Y) --> equal(multiply(W::'a,X),multiply(W::'a,Y))) &       \
\  (\\<forall>X Y W Z. equal(X::'a,Y) & product(X::'a,W,Z) --> product(Y::'a,W,Z)) &        \
\  (\\<forall>X W Y Z. equal(X::'a,Y) & product(W::'a,X,Z) --> product(W::'a,Y,Z)) &        \
\  (\\<forall>X W Z Y. equal(X::'a,Y) & product(W::'a,Z,X) --> product(W::'a,Z,Y)) &        \
\  (\\<forall>A B. equal(A::'a,B) --> equal(h(A),h(B))) &   \
\  (\\<forall>A. product(additive_identity::'a,A,additive_identity)) &      \
\  (\\<forall>A. product(A::'a,additive_identity,additive_identity)) &      \
\  (\\<forall>A. product(A::'a,multiplicative_identity,A)) &        \
\  (\\<forall>A. product(multiplicative_identity::'a,A,A)) &        \
\  (\\<forall>A. product(A::'a,h(A),multiplicative_identity) | equal(A::'a,additive_identity)) &       \
\  (\\<forall>A. product(h(A),A,multiplicative_identity) | equal(A::'a,additive_identity)) &       \
\  (product(a::'a,b,additive_identity)) &   \
\  (~equal(a::'a,additive_identity)) &      \
\  (~equal(b::'a,additive_identity)) --> False",
  meson_tac 1);

(*101319 inferences so far.  Searching to depth 14.  76.0 secs*)
val ROB010_1 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>Y X. equal(add(X::'a,Y),add(Y::'a,X))) &  \
\  (\\<forall>X Y Z. equal(add(add(X::'a,Y),Z),add(X::'a,add(Y::'a,Z)))) &  \
\  (\\<forall>Y X. equal(negate(add(negate(add(X::'a,Y)),negate(add(X::'a,negate(Y))))),X)) &   \
\  (\\<forall>A B C. equal(A::'a,B) --> equal(add(A::'a,C),add(B::'a,C))) & \
\  (\\<forall>D F' E. equal(D::'a,E) --> equal(add(F'::'a,D),add(F'::'a,E))) &      \
\  (\\<forall>G H. equal(G::'a,H) --> equal(negate(G),negate(H))) & \
\  (equal(negate(add(a::'a,negate(b))),c)) &        \
\  (~equal(negate(add(c::'a,negate(add(b::'a,a)))),a)) --> False",
  meson_tac 1);


(*6933 inferences so far.  Searching to depth 12.  5.1 secs*)
val ROB013_1 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>Y X. equal(add(X::'a,Y),add(Y::'a,X))) &  \
\  (\\<forall>X Y Z. equal(add(add(X::'a,Y),Z),add(X::'a,add(Y::'a,Z)))) &  \
\  (\\<forall>Y X. equal(negate(add(negate(add(X::'a,Y)),negate(add(X::'a,negate(Y))))),X)) &   \
\  (\\<forall>A B C. equal(A::'a,B) --> equal(add(A::'a,C),add(B::'a,C))) & \
\  (\\<forall>D F' E. equal(D::'a,E) --> equal(add(F'::'a,D),add(F'::'a,E))) &      \
\  (\\<forall>G H. equal(G::'a,H) --> equal(negate(G),negate(H))) & \
\  (equal(negate(add(a::'a,b)),c)) &        \
\  (~equal(negate(add(c::'a,negate(add(negate(b),a)))),a)) --> False",
  meson_tac 1);

(*6614 inferences so far.  Searching to depth 11.  20.4 secs*)
val ROB016_1 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>Y X. equal(add(X::'a,Y),add(Y::'a,X))) &  \
\  (\\<forall>X Y Z. equal(add(add(X::'a,Y),Z),add(X::'a,add(Y::'a,Z)))) &  \
\  (\\<forall>Y X. equal(negate(add(negate(add(X::'a,Y)),negate(add(X::'a,negate(Y))))),X)) &   \
\  (\\<forall>A B C. equal(A::'a,B) --> equal(add(A::'a,C),add(B::'a,C))) & \
\  (\\<forall>D F' E. equal(D::'a,E) --> equal(add(F'::'a,D),add(F'::'a,E))) &      \
\  (\\<forall>G H. equal(G::'a,H) --> equal(negate(G),negate(H))) & \
\  (\\<forall>J K' L. equal(J::'a,K') --> equal(multiply(J::'a,L),multiply(K'::'a,L))) &    \
\  (\\<forall>M O_ N. equal(M::'a,N) --> equal(multiply(O_::'a,M),multiply(O_::'a,N))) &       \
\  (\\<forall>P Q. equal(P::'a,Q) --> equal(successor(P),successor(Q))) &   \
\  (\\<forall>R S'. equal(R::'a,S') & positive_integer(R) --> positive_integer(S')) &       \
\  (\\<forall>X. equal(multiply(one::'a,X),X)) &    \
\  (\\<forall>V X. positive_integer(X) --> equal(multiply(successor(V),X),add(X::'a,multiply(V::'a,X)))) &      \
\  (positive_integer(one)) &    \
\  (\\<forall>X. positive_integer(X) --> positive_integer(successor(X))) &      \
\  (equal(negate(add(d::'a,e)),negate(e))) &        \
\  (positive_integer(k)) &      \
\  (\\<forall>Vk X Y. equal(negate(add(negate(Y),negate(add(X::'a,negate(Y))))),X) & positive_integer(Vk) --> equal(negate(add(Y::'a,multiply(Vk::'a,add(X::'a,negate(add(X::'a,negate(Y))))))),negate(Y))) &       \
\  (~equal(negate(add(e::'a,multiply(k::'a,add(d::'a,negate(add(d::'a,negate(e))))))),negate(e))) --> False",
  meson_tac 1);

(*14077 inferences so far.  Searching to depth 11.  32.8 secs*)
val ROB021_1 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>Y X. equal(add(X::'a,Y),add(Y::'a,X))) &  \
\  (\\<forall>X Y Z. equal(add(add(X::'a,Y),Z),add(X::'a,add(Y::'a,Z)))) &  \
\  (\\<forall>Y X. equal(negate(add(negate(add(X::'a,Y)),negate(add(X::'a,negate(Y))))),X)) &   \
\  (\\<forall>A B C. equal(A::'a,B) --> equal(add(A::'a,C),add(B::'a,C))) & \
\  (\\<forall>D F' E. equal(D::'a,E) --> equal(add(F'::'a,D),add(F'::'a,E))) &      \
\  (\\<forall>G H. equal(G::'a,H) --> equal(negate(G),negate(H))) & \
\  (\\<forall>X Y. equal(negate(X),negate(Y)) --> equal(X::'a,Y)) & \
\  (~equal(add(negate(add(a::'a,negate(b))),negate(add(negate(a),negate(b)))),b)) --> False",
  meson_tac 1);

(*35532 inferences so far.  Searching to depth 19.  54.3 secs*)
val SET005_1 = prove_hard
 ("(\\<forall>Subset Element Superset. member(Element::'a,Subset) & subset(Subset::'a,Superset) --> member(Element::'a,Superset)) & \
\  (\\<forall>Superset Subset. subset(Subset::'a,Superset) | member(member_of_1_not_of_2(Subset::'a,Superset),Subset)) &       \
\  (\\<forall>Subset Superset. member(member_of_1_not_of_2(Subset::'a,Superset),Superset) --> subset(Subset::'a,Superset)) &    \
\  (\\<forall>Subset Superset. equal_sets(Subset::'a,Superset) --> subset(Subset::'a,Superset)) &       \
\  (\\<forall>Subset Superset. equal_sets(Superset::'a,Subset) --> subset(Subset::'a,Superset)) &       \
\  (\\<forall>Set2 Set1. subset(Set1::'a,Set2) & subset(Set2::'a,Set1) --> equal_sets(Set2::'a,Set1)) &     \
\  (\\<forall>Set2 Intersection Element Set1. intersection(Set1::'a,Set2,Intersection) & member(Element::'a,Intersection) --> member(Element::'a,Set1)) &   \
\  (\\<forall>Set1 Intersection Element Set2. intersection(Set1::'a,Set2,Intersection) & member(Element::'a,Intersection) --> member(Element::'a,Set2)) &   \
\  (\\<forall>Set2 Set1 Element Intersection. intersection(Set1::'a,Set2,Intersection) & member(Element::'a,Set2) & member(Element::'a,Set1) --> member(Element::'a,Intersection)) &    \
\  (\\<forall>Set2 Intersection Set1. member(h(Set1::'a,Set2,Intersection),Intersection) | intersection(Set1::'a,Set2,Intersection) | member(h(Set1::'a,Set2,Intersection),Set1)) &       \
\  (\\<forall>Set1 Intersection Set2. member(h(Set1::'a,Set2,Intersection),Intersection) | intersection(Set1::'a,Set2,Intersection) | member(h(Set1::'a,Set2,Intersection),Set2)) &       \
\  (\\<forall>Set1 Set2 Intersection. member(h(Set1::'a,Set2,Intersection),Intersection) & member(h(Set1::'a,Set2,Intersection),Set2) & member(h(Set1::'a,Set2,Intersection),Set1) --> intersection(Set1::'a,Set2,Intersection)) &      \
\  (intersection(a::'a,b,aIb)) &    \
\  (intersection(b::'a,c,bIc)) &    \
\  (intersection(a::'a,bIc,aIbIc)) &        \
\  (~intersection(aIb::'a,c,aIbIc)) --> False",
  meson_tac 1);


(*6450 inferences so far.  Searching to depth 14.  4.2 secs*)
val SET009_1 = prove_hard
 ("(\\<forall>Subset Element Superset. member(Element::'a,Subset) & subset(Subset::'a,Superset) --> member(Element::'a,Superset)) & \
\  (\\<forall>Superset Subset. subset(Subset::'a,Superset) | member(member_of_1_not_of_2(Subset::'a,Superset),Subset)) &       \
\  (\\<forall>Subset Superset. member(member_of_1_not_of_2(Subset::'a,Superset),Superset) --> subset(Subset::'a,Superset)) &    \
\  (\\<forall>Subset Superset. equal_sets(Subset::'a,Superset) --> subset(Subset::'a,Superset)) &       \
\  (\\<forall>Subset Superset. equal_sets(Superset::'a,Subset) --> subset(Subset::'a,Superset)) &       \
\  (\\<forall>Set2 Set1. subset(Set1::'a,Set2) & subset(Set2::'a,Set1) --> equal_sets(Set2::'a,Set1)) &     \
\  (\\<forall>Set2 Difference Element Set1. difference(Set1::'a,Set2,Difference) & member(Element::'a,Difference) --> member(Element::'a,Set1)) &   \
\  (\\<forall>Element A_set Set1 Set2. ~(member(Element::'a,Set1) & member(Element::'a,Set2) & difference(A_set::'a,Set1,Set2))) &  \
\  (\\<forall>Set1 Difference Element Set2. member(Element::'a,Set1) & difference(Set1::'a,Set2,Difference) --> member(Element::'a,Difference) | member(Element::'a,Set2)) &   \
\  (\\<forall>Set1 Set2 Difference. difference(Set1::'a,Set2,Difference) | member(k(Set1::'a,Set2,Difference),Set1) | member(k(Set1::'a,Set2,Difference),Difference)) &   \
\  (\\<forall>Set1 Set2 Difference. member(k(Set1::'a,Set2,Difference),Set2) --> member(k(Set1::'a,Set2,Difference),Difference) | difference(Set1::'a,Set2,Difference)) &  \
\  (\\<forall>Set1 Set2 Difference. member(k(Set1::'a,Set2,Difference),Difference) & member(k(Set1::'a,Set2,Difference),Set1) --> member(k(Set1::'a,Set2,Difference),Set2) | difference(Set1::'a,Set2,Difference)) &   \
\  (subset(d::'a,a)) &      \
\  (difference(b::'a,a,bDa)) &      \
\  (difference(b::'a,d,bDd)) &      \
\  (~subset(bDa::'a,bDd)) --> False",
  meson_tac 1);

(*34726 inferences so far.  Searching to depth 6.  2420 secs: 40 mins\\<forall> BIG*)
val SET025_4 = prove_hard
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (\\<forall>Y X. member(X::'a,Y) --> little_set(X)) &     \
\  (\\<forall>X Y. little_set(f1(X::'a,Y)) | equal(X::'a,Y)) & \
\  (\\<forall>X Y. member(f1(X::'a,Y),X) | member(f1(X::'a,Y),Y) | equal(X::'a,Y)) &      \
\  (\\<forall>X Y. member(f1(X::'a,Y),X) & member(f1(X::'a,Y),Y) --> equal(X::'a,Y)) &      \
\  (\\<forall>X U Y. member(U::'a,non_ordered_pair(X::'a,Y)) --> equal(U::'a,X) | equal(U::'a,Y)) &    \
\  (\\<forall>Y U X. little_set(U) & equal(U::'a,X) --> member(U::'a,non_ordered_pair(X::'a,Y))) &  \
\  (\\<forall>X U Y. little_set(U) & equal(U::'a,Y) --> member(U::'a,non_ordered_pair(X::'a,Y))) &  \
\  (\\<forall>X Y. little_set(non_ordered_pair(X::'a,Y))) & \
\  (\\<forall>X. equal(singleton_set(X),non_ordered_pair(X::'a,X))) &       \
\  (\\<forall>X Y. equal(ordered_pair(X::'a,Y),non_ordered_pair(singleton_set(X),non_ordered_pair(X::'a,Y)))) & \
\  (\\<forall>X. ordered_pair_predicate(X) --> little_set(f2(X))) &     \
\  (\\<forall>X. ordered_pair_predicate(X) --> little_set(f3(X))) &     \
\  (\\<forall>X. ordered_pair_predicate(X) --> equal(X::'a,ordered_pair(f2(X),f3(X)))) &    \
\  (\\<forall>X Y Z. little_set(Y) & little_set(Z) & equal(X::'a,ordered_pair(Y::'a,Z)) --> ordered_pair_predicate(X)) &        \
\  (\\<forall>Z X. member(Z::'a,first(X)) --> little_set(f4(Z::'a,X))) &        \
\  (\\<forall>Z X. member(Z::'a,first(X)) --> little_set(f5(Z::'a,X))) &        \
\  (\\<forall>Z X. member(Z::'a,first(X)) --> equal(X::'a,ordered_pair(f4(Z::'a,X),f5(Z::'a,X)))) &     \
\  (\\<forall>Z X. member(Z::'a,first(X)) --> member(Z::'a,f4(Z::'a,X))) &  \
\  (\\<forall>X V Z U. little_set(U) & little_set(V) & equal(X::'a,ordered_pair(U::'a,V)) & member(Z::'a,U) --> member(Z::'a,first(X))) &       \
\  (\\<forall>Z X. member(Z::'a,second(X)) --> little_set(f6(Z::'a,X))) &       \
\  (\\<forall>Z X. member(Z::'a,second(X)) --> little_set(f7(Z::'a,X))) &       \
\  (\\<forall>Z X. member(Z::'a,second(X)) --> equal(X::'a,ordered_pair(f6(Z::'a,X),f7(Z::'a,X)))) &    \
\  (\\<forall>Z X. member(Z::'a,second(X)) --> member(Z::'a,f7(Z::'a,X))) & \
\  (\\<forall>X U Z V. little_set(U) & little_set(V) & equal(X::'a,ordered_pair(U::'a,V)) & member(Z::'a,V) --> member(Z::'a,second(X))) &      \
\  (\\<forall>Z. member(Z::'a,estin) --> ordered_pair_predicate(Z)) &       \
\  (\\<forall>Z. member(Z::'a,estin) --> member(first(Z),second(Z))) &      \
\  (\\<forall>Z. little_set(Z) & ordered_pair_predicate(Z) & member(first(Z),second(Z)) --> member(Z::'a,estin)) &  \
\  (\\<forall>Y Z X. member(Z::'a,intersection(X::'a,Y)) --> member(Z::'a,X)) &     \
\  (\\<forall>X Z Y. member(Z::'a,intersection(X::'a,Y)) --> member(Z::'a,Y)) &     \
\  (\\<forall>X Z Y. member(Z::'a,X) & member(Z::'a,Y) --> member(Z::'a,intersection(X::'a,Y))) &       \
\  (\\<forall>Z X. ~(member(Z::'a,complement(X)) & member(Z::'a,X))) &  \
\  (\\<forall>Z X. little_set(Z) --> member(Z::'a,complement(X)) | member(Z::'a,X)) &  \
\  (\\<forall>X Y. equal(union(X::'a,Y),complement(intersection(complement(X),complement(Y))))) &   \
\  (\\<forall>Z X. member(Z::'a,domain_of(X)) --> ordered_pair_predicate(f8(Z::'a,X))) &        \
\  (\\<forall>Z X. member(Z::'a,domain_of(X)) --> member(f8(Z::'a,X),X)) &      \
\  (\\<forall>Z X. member(Z::'a,domain_of(X)) --> equal(Z::'a,first(f8(Z::'a,X)))) &        \
\  (\\<forall>X Z Xp. little_set(Z) & ordered_pair_predicate(Xp) & member(Xp::'a,X) & equal(Z::'a,first(Xp)) --> member(Z::'a,domain_of(X))) &      \
\  (\\<forall>X Y Z. member(Z::'a,cross_product(X::'a,Y)) --> ordered_pair_predicate(Z)) &      \
\  (\\<forall>Y Z X. member(Z::'a,cross_product(X::'a,Y)) --> member(first(Z),X)) &     \
\  (\\<forall>X Z Y. member(Z::'a,cross_product(X::'a,Y)) --> member(second(Z),Y)) &    \
\  (\\<forall>X Z Y. little_set(Z) & ordered_pair_predicate(Z) & member(first(Z),X) & member(second(Z),Y) --> member(Z::'a,cross_product(X::'a,Y))) &   \
\  (\\<forall>X Z. member(Z::'a,inv1 X) --> ordered_pair_predicate(Z)) &       \
\  (\\<forall>Z X. member(Z::'a,inv1 X) --> member(ordered_pair(second(Z),first(Z)),X)) &      \
\  (\\<forall>Z X. little_set(Z) & ordered_pair_predicate(Z) & member(ordered_pair(second(Z),first(Z)),X) --> member(Z::'a,inv1 X)) &  \
\  (\\<forall>Z X. member(Z::'a,rotate_right(X)) --> little_set(f9(Z::'a,X))) & \
\  (\\<forall>Z X. member(Z::'a,rotate_right(X)) --> little_set(f10(Z::'a,X))) &        \
\  (\\<forall>Z X. member(Z::'a,rotate_right(X)) --> little_set(f11(Z::'a,X))) &        \
\  (\\<forall>Z X. member(Z::'a,rotate_right(X)) --> equal(Z::'a,ordered_pair(f9(Z::'a,X),ordered_pair(f10(Z::'a,X),f11(Z::'a,X))))) &      \
\  (\\<forall>Z X. member(Z::'a,rotate_right(X)) --> member(ordered_pair(f10(Z::'a,X),ordered_pair(f11(Z::'a,X),f9(Z::'a,X))),X)) &     \
\  (\\<forall>Z V W U X. little_set(Z) & little_set(U) & little_set(V) & little_set(W) & equal(Z::'a,ordered_pair(U::'a,ordered_pair(V::'a,W))) & member(ordered_pair(V::'a,ordered_pair(W::'a,U)),X) --> member(Z::'a,rotate_right(X))) &      \
\  (\\<forall>Z X. member(Z::'a,flip_range_of(X)) --> little_set(f12(Z::'a,X))) &       \
\  (\\<forall>Z X. member(Z::'a,flip_range_of(X)) --> little_set(f13(Z::'a,X))) &       \
\  (\\<forall>Z X. member(Z::'a,flip_range_of(X)) --> little_set(f14(Z::'a,X))) &       \
\  (\\<forall>Z X. member(Z::'a,flip_range_of(X)) --> equal(Z::'a,ordered_pair(f12(Z::'a,X),ordered_pair(f13(Z::'a,X),f14(Z::'a,X))))) &    \
\  (\\<forall>Z X. member(Z::'a,flip_range_of(X)) --> member(ordered_pair(f12(Z::'a,X),ordered_pair(f14(Z::'a,X),f13(Z::'a,X))),X)) &   \
\  (\\<forall>Z U W V X. little_set(Z) & little_set(U) & little_set(V) & little_set(W) & equal(Z::'a,ordered_pair(U::'a,ordered_pair(V::'a,W))) & member(ordered_pair(U::'a,ordered_pair(W::'a,V)),X) --> member(Z::'a,flip_range_of(X))) &     \
\  (\\<forall>X. equal(successor(X),union(X::'a,singleton_set(X)))) &       \
\  (\\<forall>Z. ~member(Z::'a,empty_set)) &        \
\  (\\<forall>Z. little_set(Z) --> member(Z::'a,universal_set)) &   \
\  (little_set(infinity)) &     \
\  (member(empty_set::'a,infinity)) &       \
\  (\\<forall>X. member(X::'a,infinity) --> member(successor(X),infinity)) &        \
\  (\\<forall>Z X. member(Z::'a,sigma(X)) --> member(f16(Z::'a,X),X)) & \
\  (\\<forall>Z X. member(Z::'a,sigma(X)) --> member(Z::'a,f16(Z::'a,X))) & \
\  (\\<forall>X Z Y. member(Y::'a,X) & member(Z::'a,Y) --> member(Z::'a,sigma(X))) &        \
\  (\\<forall>U. little_set(U) --> little_set(sigma(U))) &      \
\  (\\<forall>X U Y. subset(X::'a,Y) & member(U::'a,X) --> member(U::'a,Y)) &       \
\  (\\<forall>Y X. subset(X::'a,Y) | member(f17(X::'a,Y),X)) & \
\  (\\<forall>X Y. member(f17(X::'a,Y),Y) --> subset(X::'a,Y)) &        \
\  (\\<forall>X Y. proper_subset(X::'a,Y) --> subset(X::'a,Y)) &        \
\  (\\<forall>X Y. ~(proper_subset(X::'a,Y) & equal(X::'a,Y))) &        \
\  (\\<forall>X Y. subset(X::'a,Y) --> proper_subset(X::'a,Y) | equal(X::'a,Y)) &  \
\  (\\<forall>Z X. member(Z::'a,powerset(X)) --> subset(Z::'a,X)) &     \
\  (\\<forall>Z X. little_set(Z) & subset(Z::'a,X) --> member(Z::'a,powerset(X))) &     \
\  (\\<forall>U. little_set(U) --> little_set(powerset(U))) &   \
\  (\\<forall>Z X. relation(Z) & member(X::'a,Z) --> ordered_pair_predicate(X)) &   \
\  (\\<forall>Z. relation(Z) | member(f18(Z),Z)) &     \
\  (\\<forall>Z. ordered_pair_predicate(f18(Z)) --> relation(Z)) &      \
\  (\\<forall>U X V W. single_valued_set(X) & little_set(U) & little_set(V) & little_set(W) & member(ordered_pair(U::'a,V),X) & member(ordered_pair(U::'a,W),X) --> equal(V::'a,W)) &       \
\  (\\<forall>X. single_valued_set(X) | little_set(f19(X))) &  \
\  (\\<forall>X. single_valued_set(X) | little_set(f20(X))) &  \
\  (\\<forall>X. single_valued_set(X) | little_set(f21(X))) &  \
\  (\\<forall>X. single_valued_set(X) | member(ordered_pair(f19(X),f20(X)),X)) &       \
\  (\\<forall>X. single_valued_set(X) | member(ordered_pair(f19(X),f21(X)),X)) &       \
\  (\\<forall>X. equal(f20(X),f21(X)) --> single_valued_set(X)) &       \
\  (\\<forall>Xf. function(Xf) --> relation(Xf)) &      \
\  (\\<forall>Xf. function(Xf) --> single_valued_set(Xf)) &     \
\  (\\<forall>Xf. relation(Xf) & single_valued_set(Xf) --> function(Xf)) &      \
\  (\\<forall>Z X Xf. member(Z::'a,image_(X::'a,Xf)) --> ordered_pair_predicate(f22(Z::'a,X,Xf))) &  \
\  (\\<forall>Z X Xf. member(Z::'a,image_(X::'a,Xf)) --> member(f22(Z::'a,X,Xf),Xf)) &       \
\  (\\<forall>Z Xf X. member(Z::'a,image_(X::'a,Xf)) --> member(first(f22(Z::'a,X,Xf)),X)) & \
\  (\\<forall>X Xf Z. member(Z::'a,image_(X::'a,Xf)) --> equal(second(f22(Z::'a,X,Xf)),Z)) & \
\  (\\<forall>Xf X Y Z. little_set(Z) & ordered_pair_predicate(Y) & member(Y::'a,Xf) & member(first(Y),X) & equal(second(Y),Z) --> member(Z::'a,image_(X::'a,Xf))) & \
\  (\\<forall>X Xf. little_set(X) & function(Xf) --> little_set(image_(X::'a,Xf))) & \
\  (\\<forall>X U Y. ~(disjoint(X::'a,Y) & member(U::'a,X) & member(U::'a,Y))) &    \
\  (\\<forall>Y X. disjoint(X::'a,Y) | member(f23(X::'a,Y),X)) &       \
\  (\\<forall>X Y. disjoint(X::'a,Y) | member(f23(X::'a,Y),Y)) &       \
\  (\\<forall>X. equal(X::'a,empty_set) | member(f24(X),X)) &      \
\  (\\<forall>X. equal(X::'a,empty_set) | disjoint(f24(X),X)) &    \
\  (function(f25)) &    \
\  (\\<forall>X. little_set(X) --> equal(X::'a,empty_set) | member(f26(X),X)) &    \
\  (\\<forall>X. little_set(X) --> equal(X::'a,empty_set) | member(ordered_pair(X::'a,f26(X)),f25)) &  \
\  (\\<forall>Z X. member(Z::'a,range_of(X)) --> ordered_pair_predicate(f27(Z::'a,X))) &        \
\  (\\<forall>Z X. member(Z::'a,range_of(X)) --> member(f27(Z::'a,X),X)) &      \
\  (\\<forall>Z X. member(Z::'a,range_of(X)) --> equal(Z::'a,second(f27(Z::'a,X)))) &       \
\  (\\<forall>X Z Xp. little_set(Z) & ordered_pair_predicate(Xp) & member(Xp::'a,X) & equal(Z::'a,second(Xp)) --> member(Z::'a,range_of(X))) &      \
\  (\\<forall>Z. member(Z::'a,identity_relation) --> ordered_pair_predicate(Z)) &   \
\  (\\<forall>Z. member(Z::'a,identity_relation) --> equal(first(Z),second(Z))) &   \
\  (\\<forall>Z. little_set(Z) & ordered_pair_predicate(Z) & equal(first(Z),second(Z)) --> member(Z::'a,identity_relation)) &       \
\  (\\<forall>X Y. equal(restrct(X::'a,Y),intersection(X::'a,cross_product(Y::'a,universal_set)))) &       \
\  (\\<forall>Xf. one_to_one_function(Xf) --> function(Xf)) &   \
\  (\\<forall>Xf. one_to_one_function(Xf) --> function(inv1 Xf)) & \
\  (\\<forall>Xf. function(Xf) & function(inv1 Xf) --> one_to_one_function(Xf)) &  \
\  (\\<forall>Z Xf Y. member(Z::'a,apply(Xf::'a,Y)) --> ordered_pair_predicate(f28(Z::'a,Xf,Y))) &  \
\  (\\<forall>Z Y Xf. member(Z::'a,apply(Xf::'a,Y)) --> member(f28(Z::'a,Xf,Y),Xf)) &       \
\  (\\<forall>Z Xf Y. member(Z::'a,apply(Xf::'a,Y)) --> equal(first(f28(Z::'a,Xf,Y)),Y)) &  \
\  (\\<forall>Z Xf Y. member(Z::'a,apply(Xf::'a,Y)) --> member(Z::'a,second(f28(Z::'a,Xf,Y)))) &        \
\  (\\<forall>Xf Y Z W. ordered_pair_predicate(W) & member(W::'a,Xf) & equal(first(W),Y) & member(Z::'a,second(W)) --> member(Z::'a,apply(Xf::'a,Y))) & \
\  (\\<forall>Xf X Y. equal(apply_to_two_arguments(Xf::'a,X,Y),apply(Xf::'a,ordered_pair(X::'a,Y)))) &      \
\  (\\<forall>X Y Xf. maps(Xf::'a,X,Y) --> function(Xf)) &  \
\  (\\<forall>Y Xf X. maps(Xf::'a,X,Y) --> equal(domain_of(Xf),X)) &        \
\  (\\<forall>X Xf Y. maps(Xf::'a,X,Y) --> subset(range_of(Xf),Y)) &        \
\  (\\<forall>X Xf Y. function(Xf) & equal(domain_of(Xf),X) & subset(range_of(Xf),Y) --> maps(Xf::'a,X,Y)) &        \
\  (\\<forall>Xf Xs. closed(Xs::'a,Xf) --> little_set(Xs)) &        \
\  (\\<forall>Xs Xf. closed(Xs::'a,Xf) --> little_set(Xf)) &        \
\  (\\<forall>Xf Xs. closed(Xs::'a,Xf) --> maps(Xf::'a,cross_product(Xs::'a,Xs),Xs)) &      \
\  (\\<forall>Xf Xs. little_set(Xs) & little_set(Xf) & maps(Xf::'a,cross_product(Xs::'a,Xs),Xs) --> closed(Xs::'a,Xf)) &    \
\  (\\<forall>Z Xf Xg. member(Z::'a,composition(Xf::'a,Xg)) --> little_set(f29(Z::'a,Xf,Xg))) &     \
\  (\\<forall>Z Xf Xg. member(Z::'a,composition(Xf::'a,Xg)) --> little_set(f30(Z::'a,Xf,Xg))) &     \
\  (\\<forall>Z Xf Xg. member(Z::'a,composition(Xf::'a,Xg)) --> little_set(f31(Z::'a,Xf,Xg))) &     \
\  (\\<forall>Z Xf Xg. member(Z::'a,composition(Xf::'a,Xg)) --> equal(Z::'a,ordered_pair(f29(Z::'a,Xf,Xg),f30(Z::'a,Xf,Xg)))) &     \
\  (\\<forall>Z Xg Xf. member(Z::'a,composition(Xf::'a,Xg)) --> member(ordered_pair(f29(Z::'a,Xf,Xg),f31(Z::'a,Xf,Xg)),Xf)) &   \
\  (\\<forall>Z Xf Xg. member(Z::'a,composition(Xf::'a,Xg)) --> member(ordered_pair(f31(Z::'a,Xf,Xg),f30(Z::'a,Xf,Xg)),Xg)) &   \
\  (\\<forall>Z X Xf W Y Xg. little_set(Z) & little_set(X) & little_set(Y) & little_set(W) & equal(Z::'a,ordered_pair(X::'a,Y)) & member(ordered_pair(X::'a,W),Xf) & member(ordered_pair(W::'a,Y),Xg) --> member(Z::'a,composition(Xf::'a,Xg))) &       \
\  (\\<forall>Xh Xs2 Xf2 Xs1 Xf1. homomorphism(Xh::'a,Xs1,Xf1,Xs2,Xf2) --> closed(Xs1::'a,Xf1)) &       \
\  (\\<forall>Xh Xs1 Xf1 Xs2 Xf2. homomorphism(Xh::'a,Xs1,Xf1,Xs2,Xf2) --> closed(Xs2::'a,Xf2)) &       \
\  (\\<forall>Xf1 Xf2 Xh Xs1 Xs2. homomorphism(Xh::'a,Xs1,Xf1,Xs2,Xf2) --> maps(Xh::'a,Xs1,Xs2)) &      \
\  (\\<forall>Xs2 Xs1 Xf1 Xf2 X Xh Y. homomorphism(Xh::'a,Xs1,Xf1,Xs2,Xf2) & member(X::'a,Xs1) & member(Y::'a,Xs1) --> equal(apply(Xh::'a,apply_to_two_arguments(Xf1::'a,X,Y)),apply_to_two_arguments(Xf2::'a,apply(Xh::'a,X),apply(Xh::'a,Y)))) &      \
\  (\\<forall>Xh Xf1 Xs2 Xf2 Xs1. closed(Xs1::'a,Xf1) & closed(Xs2::'a,Xf2) & maps(Xh::'a,Xs1,Xs2) --> homomorphism(Xh::'a,Xs1,Xf1,Xs2,Xf2) | member(f32(Xh::'a,Xs1,Xf1,Xs2,Xf2),Xs1)) &   \
\  (\\<forall>Xh Xf1 Xs2 Xf2 Xs1. closed(Xs1::'a,Xf1) & closed(Xs2::'a,Xf2) & maps(Xh::'a,Xs1,Xs2) --> homomorphism(Xh::'a,Xs1,Xf1,Xs2,Xf2) | member(f33(Xh::'a,Xs1,Xf1,Xs2,Xf2),Xs1)) &   \
\  (\\<forall>Xh Xs1 Xf1 Xs2 Xf2. closed(Xs1::'a,Xf1) & closed(Xs2::'a,Xf2) & maps(Xh::'a,Xs1,Xs2) & equal(apply(Xh::'a,apply_to_two_arguments(Xf1::'a,f32(Xh::'a,Xs1,Xf1,Xs2,Xf2),f33(Xh::'a,Xs1,Xf1,Xs2,Xf2))),apply_to_two_arguments(Xf2::'a,apply(Xh::'a,f32(Xh::'a,Xs1,Xf1,Xs2,Xf2)),apply(Xh::'a,f33(Xh::'a,Xs1,Xf1,Xs2,Xf2)))) --> homomorphism(Xh::'a,Xs1,Xf1,Xs2,Xf2)) &   \
\  (\\<forall>A B C. equal(A::'a,B) --> equal(f1(A::'a,C),f1(B::'a,C))) &   \
\  (\\<forall>D F' E. equal(D::'a,E) --> equal(f1(F'::'a,D),f1(F'::'a,E))) &        \
\  (\\<forall>A2 B2. equal(A2::'a,B2) --> equal(f2(A2),f2(B2))) &   \
\  (\\<forall>G4 H4. equal(G4::'a,H4) --> equal(f3(G4),f3(H4))) &   \
\  (\\<forall>O7 P7 Q7. equal(O7::'a,P7) --> equal(f4(O7::'a,Q7),f4(P7::'a,Q7))) &  \
\  (\\<forall>R7 T7 S7. equal(R7::'a,S7) --> equal(f4(T7::'a,R7),f4(T7::'a,S7))) &  \
\  (\\<forall>U7 V7 W7. equal(U7::'a,V7) --> equal(f5(U7::'a,W7),f5(V7::'a,W7))) &  \
\  (\\<forall>X7 Z7 Y7. equal(X7::'a,Y7) --> equal(f5(Z7::'a,X7),f5(Z7::'a,Y7))) &  \
\  (\\<forall>A8 B8 C8. equal(A8::'a,B8) --> equal(f6(A8::'a,C8),f6(B8::'a,C8))) &  \
\  (\\<forall>D8 F8 E8. equal(D8::'a,E8) --> equal(f6(F8::'a,D8),f6(F8::'a,E8))) &  \
\  (\\<forall>G8 H8 I8. equal(G8::'a,H8) --> equal(f7(G8::'a,I8),f7(H8::'a,I8))) &  \
\  (\\<forall>J8 L8 K8. equal(J8::'a,K8) --> equal(f7(L8::'a,J8),f7(L8::'a,K8))) &  \
\  (\\<forall>M8 N8 O8. equal(M8::'a,N8) --> equal(f8(M8::'a,O8),f8(N8::'a,O8))) &  \
\  (\\<forall>P8 R8 Q8. equal(P8::'a,Q8) --> equal(f8(R8::'a,P8),f8(R8::'a,Q8))) &  \
\  (\\<forall>S8 T8 U8. equal(S8::'a,T8) --> equal(f9(S8::'a,U8),f9(T8::'a,U8))) &  \
\  (\\<forall>V8 X8 W8. equal(V8::'a,W8) --> equal(f9(X8::'a,V8),f9(X8::'a,W8))) &  \
\  (\\<forall>G H I'. equal(G::'a,H) --> equal(f10(G::'a,I'),f10(H::'a,I'))) &      \
\  (\\<forall>J L K'. equal(J::'a,K') --> equal(f10(L::'a,J),f10(L::'a,K'))) &      \
\  (\\<forall>M N O_. equal(M::'a,N) --> equal(f11(M::'a,O_),f11(N::'a,O_))) & \
\  (\\<forall>P R Q. equal(P::'a,Q) --> equal(f11(R::'a,P),f11(R::'a,Q))) & \
\  (\\<forall>S' T' U. equal(S'::'a,T') --> equal(f12(S'::'a,U),f12(T'::'a,U))) &   \
\  (\\<forall>V X W. equal(V::'a,W) --> equal(f12(X::'a,V),f12(X::'a,W))) & \
\  (\\<forall>Y Z A1. equal(Y::'a,Z) --> equal(f13(Y::'a,A1),f13(Z::'a,A1))) &      \
\  (\\<forall>B1 D1 C1. equal(B1::'a,C1) --> equal(f13(D1::'a,B1),f13(D1::'a,C1))) &        \
\  (\\<forall>E1 F1 G1. equal(E1::'a,F1) --> equal(f14(E1::'a,G1),f14(F1::'a,G1))) &        \
\  (\\<forall>H1 J1 I1. equal(H1::'a,I1) --> equal(f14(J1::'a,H1),f14(J1::'a,I1))) &        \
\  (\\<forall>K1 L1 M1. equal(K1::'a,L1) --> equal(f16(K1::'a,M1),f16(L1::'a,M1))) &        \
\  (\\<forall>N1 P1 O1. equal(N1::'a,O1) --> equal(f16(P1::'a,N1),f16(P1::'a,O1))) &        \
\  (\\<forall>Q1 R1 S1. equal(Q1::'a,R1) --> equal(f17(Q1::'a,S1),f17(R1::'a,S1))) &        \
\  (\\<forall>T1 V1 U1. equal(T1::'a,U1) --> equal(f17(V1::'a,T1),f17(V1::'a,U1))) &        \
\  (\\<forall>W1 X1. equal(W1::'a,X1) --> equal(f18(W1),f18(X1))) & \
\  (\\<forall>Y1 Z1. equal(Y1::'a,Z1) --> equal(f19(Y1),f19(Z1))) & \
\  (\\<forall>C2 D2. equal(C2::'a,D2) --> equal(f20(C2),f20(D2))) & \
\  (\\<forall>E2 F2. equal(E2::'a,F2) --> equal(f21(E2),f21(F2))) & \
\  (\\<forall>G2 H2 I2 J2. equal(G2::'a,H2) --> equal(f22(G2::'a,I2,J2),f22(H2::'a,I2,J2))) &       \
\  (\\<forall>K2 M2 L2 N2. equal(K2::'a,L2) --> equal(f22(M2::'a,K2,N2),f22(M2::'a,L2,N2))) &       \
\  (\\<forall>O2 Q2 R2 P2. equal(O2::'a,P2) --> equal(f22(Q2::'a,R2,O2),f22(Q2::'a,R2,P2))) &       \
\  (\\<forall>S2 T2 U2. equal(S2::'a,T2) --> equal(f23(S2::'a,U2),f23(T2::'a,U2))) &        \
\  (\\<forall>V2 X2 W2. equal(V2::'a,W2) --> equal(f23(X2::'a,V2),f23(X2::'a,W2))) &        \
\  (\\<forall>Y2 Z2. equal(Y2::'a,Z2) --> equal(f24(Y2),f24(Z2))) & \
\  (\\<forall>A3 B3. equal(A3::'a,B3) --> equal(f26(A3),f26(B3))) & \
\  (\\<forall>C3 D3 E3. equal(C3::'a,D3) --> equal(f27(C3::'a,E3),f27(D3::'a,E3))) &        \
\  (\\<forall>F3 H3 G3. equal(F3::'a,G3) --> equal(f27(H3::'a,F3),f27(H3::'a,G3))) &        \
\  (\\<forall>I3 J3 K3 L3. equal(I3::'a,J3) --> equal(f28(I3::'a,K3,L3),f28(J3::'a,K3,L3))) &       \
\  (\\<forall>M3 O3 N3 P3. equal(M3::'a,N3) --> equal(f28(O3::'a,M3,P3),f28(O3::'a,N3,P3))) &       \
\  (\\<forall>Q3 S3 T3 R3. equal(Q3::'a,R3) --> equal(f28(S3::'a,T3,Q3),f28(S3::'a,T3,R3))) &       \
\  (\\<forall>U3 V3 W3 X3. equal(U3::'a,V3) --> equal(f29(U3::'a,W3,X3),f29(V3::'a,W3,X3))) &       \
\  (\\<forall>Y3 A4 Z3 B4. equal(Y3::'a,Z3) --> equal(f29(A4::'a,Y3,B4),f29(A4::'a,Z3,B4))) &       \
\  (\\<forall>C4 E4 F4 D4. equal(C4::'a,D4) --> equal(f29(E4::'a,F4,C4),f29(E4::'a,F4,D4))) &       \
\  (\\<forall>I4 J4 K4 L4. equal(I4::'a,J4) --> equal(f30(I4::'a,K4,L4),f30(J4::'a,K4,L4))) &       \
\  (\\<forall>M4 O4 N4 P4. equal(M4::'a,N4) --> equal(f30(O4::'a,M4,P4),f30(O4::'a,N4,P4))) &       \
\  (\\<forall>Q4 S4 T4 R4. equal(Q4::'a,R4) --> equal(f30(S4::'a,T4,Q4),f30(S4::'a,T4,R4))) &       \
\  (\\<forall>U4 V4 W4 X4. equal(U4::'a,V4) --> equal(f31(U4::'a,W4,X4),f31(V4::'a,W4,X4))) &       \
\  (\\<forall>Y4 A5 Z4 B5. equal(Y4::'a,Z4) --> equal(f31(A5::'a,Y4,B5),f31(A5::'a,Z4,B5))) &       \
\  (\\<forall>C5 E5 F5 D5. equal(C5::'a,D5) --> equal(f31(E5::'a,F5,C5),f31(E5::'a,F5,D5))) &       \
\  (\\<forall>G5 H5 I5 J5 K5 L5. equal(G5::'a,H5) --> equal(f32(G5::'a,I5,J5,K5,L5),f32(H5::'a,I5,J5,K5,L5))) &     \
\  (\\<forall>M5 O5 N5 P5 Q5 R5. equal(M5::'a,N5) --> equal(f32(O5::'a,M5,P5,Q5,R5),f32(O5::'a,N5,P5,Q5,R5))) &     \
\  (\\<forall>S5 U5 V5 T5 W5 X5. equal(S5::'a,T5) --> equal(f32(U5::'a,V5,S5,W5,X5),f32(U5::'a,V5,T5,W5,X5))) &     \
\  (\\<forall>Y5 A6 B6 C6 Z5 D6. equal(Y5::'a,Z5) --> equal(f32(A6::'a,B6,C6,Y5,D6),f32(A6::'a,B6,C6,Z5,D6))) &     \
\  (\\<forall>E6 G6 H6 I6 J6 F6. equal(E6::'a,F6) --> equal(f32(G6::'a,H6,I6,J6,E6),f32(G6::'a,H6,I6,J6,F6))) &     \
\  (\\<forall>K6 L6 M6 N6 O6 P6. equal(K6::'a,L6) --> equal(f33(K6::'a,M6,N6,O6,P6),f33(L6::'a,M6,N6,O6,P6))) &     \
\  (\\<forall>Q6 S6 R6 T6 U6 V6. equal(Q6::'a,R6) --> equal(f33(S6::'a,Q6,T6,U6,V6),f33(S6::'a,R6,T6,U6,V6))) &     \
\  (\\<forall>W6 Y6 Z6 X6 A7 B7. equal(W6::'a,X6) --> equal(f33(Y6::'a,Z6,W6,A7,B7),f33(Y6::'a,Z6,X6,A7,B7))) &     \
\  (\\<forall>C7 E7 F7 G7 D7 H7. equal(C7::'a,D7) --> equal(f33(E7::'a,F7,G7,C7,H7),f33(E7::'a,F7,G7,D7,H7))) &     \
\  (\\<forall>I7 K7 L7 M7 N7 J7. equal(I7::'a,J7) --> equal(f33(K7::'a,L7,M7,N7,I7),f33(K7::'a,L7,M7,N7,J7))) &     \
\  (\\<forall>A B C. equal(A::'a,B) --> equal(apply(A::'a,C),apply(B::'a,C))) &     \
\  (\\<forall>D F' E. equal(D::'a,E) --> equal(apply(F'::'a,D),apply(F'::'a,E))) &  \
\  (\\<forall>G H I' J. equal(G::'a,H) --> equal(apply_to_two_arguments(G::'a,I',J),apply_to_two_arguments(H::'a,I',J))) &  \
\  (\\<forall>K' M L N. equal(K'::'a,L) --> equal(apply_to_two_arguments(M::'a,K',N),apply_to_two_arguments(M::'a,L,N))) &  \
\  (\\<forall>O_ Q R P. equal(O_::'a,P) --> equal(apply_to_two_arguments(Q::'a,R,O_),apply_to_two_arguments(Q::'a,R,P))) &     \
\  (\\<forall>S' T'. equal(S'::'a,T') --> equal(complement(S'),complement(T'))) &   \
\  (\\<forall>U V W. equal(U::'a,V) --> equal(composition(U::'a,W),composition(V::'a,W))) & \
\  (\\<forall>X Z Y. equal(X::'a,Y) --> equal(composition(Z::'a,X),composition(Z::'a,Y))) & \
\  (\\<forall>A1 B1. equal(A1::'a,B1) --> equal(inv1 A1,inv1 B1)) &       \
\  (\\<forall>C1 D1 E1. equal(C1::'a,D1) --> equal(cross_product(C1::'a,E1),cross_product(D1::'a,E1))) &    \
\  (\\<forall>F1 H1 G1. equal(F1::'a,G1) --> equal(cross_product(H1::'a,F1),cross_product(H1::'a,G1))) &    \
\  (\\<forall>I1 J1. equal(I1::'a,J1) --> equal(domain_of(I1),domain_of(J1))) &     \
\  (\\<forall>I10 J10. equal(I10::'a,J10) --> equal(first(I10),first(J10))) &       \
\  (\\<forall>Q10 R10. equal(Q10::'a,R10) --> equal(flip_range_of(Q10),flip_range_of(R10))) &       \
\  (\\<forall>S10 T10 U10. equal(S10::'a,T10) --> equal(image_(S10::'a,U10),image_(T10::'a,U10))) &   \
\  (\\<forall>V10 X10 W10. equal(V10::'a,W10) --> equal(image_(X10::'a,V10),image_(X10::'a,W10))) &   \
\  (\\<forall>Y10 Z10 A11. equal(Y10::'a,Z10) --> equal(intersection(Y10::'a,A11),intersection(Z10::'a,A11))) &     \
\  (\\<forall>B11 D11 C11. equal(B11::'a,C11) --> equal(intersection(D11::'a,B11),intersection(D11::'a,C11))) &     \
\  (\\<forall>E11 F11 G11. equal(E11::'a,F11) --> equal(non_ordered_pair(E11::'a,G11),non_ordered_pair(F11::'a,G11))) &     \
\  (\\<forall>H11 J11 I11. equal(H11::'a,I11) --> equal(non_ordered_pair(J11::'a,H11),non_ordered_pair(J11::'a,I11))) &     \
\  (\\<forall>K11 L11 M11. equal(K11::'a,L11) --> equal(ordered_pair(K11::'a,M11),ordered_pair(L11::'a,M11))) &     \
\  (\\<forall>N11 P11 O11. equal(N11::'a,O11) --> equal(ordered_pair(P11::'a,N11),ordered_pair(P11::'a,O11))) &     \
\  (\\<forall>Q11 R11. equal(Q11::'a,R11) --> equal(powerset(Q11),powerset(R11))) & \
\  (\\<forall>S11 T11. equal(S11::'a,T11) --> equal(range_of(S11),range_of(T11))) & \
\  (\\<forall>U11 V11 W11. equal(U11::'a,V11) --> equal(restrct(U11::'a,W11),restrct(V11::'a,W11))) &     \
\  (\\<forall>X11 Z11 Y11. equal(X11::'a,Y11) --> equal(restrct(Z11::'a,X11),restrct(Z11::'a,Y11))) &     \
\  (\\<forall>A12 B12. equal(A12::'a,B12) --> equal(rotate_right(A12),rotate_right(B12))) & \
\  (\\<forall>C12 D12. equal(C12::'a,D12) --> equal(second(C12),second(D12))) &     \
\  (\\<forall>K12 L12. equal(K12::'a,L12) --> equal(sigma(K12),sigma(L12))) &       \
\  (\\<forall>M12 N12. equal(M12::'a,N12) --> equal(singleton_set(M12),singleton_set(N12))) &       \
\  (\\<forall>O12 P12. equal(O12::'a,P12) --> equal(successor(O12),successor(P12))) &       \
\  (\\<forall>Q12 R12 S12. equal(Q12::'a,R12) --> equal(union(Q12::'a,S12),union(R12::'a,S12))) &   \
\  (\\<forall>T12 V12 U12. equal(T12::'a,U12) --> equal(union(V12::'a,T12),union(V12::'a,U12))) &   \
\  (\\<forall>W12 X12 Y12. equal(W12::'a,X12) & closed(W12::'a,Y12) --> closed(X12::'a,Y12)) &      \
\  (\\<forall>Z12 B13 A13. equal(Z12::'a,A13) & closed(B13::'a,Z12) --> closed(B13::'a,A13)) &      \
\  (\\<forall>C13 D13 E13. equal(C13::'a,D13) & disjoint(C13::'a,E13) --> disjoint(D13::'a,E13)) &  \
\  (\\<forall>F13 H13 G13. equal(F13::'a,G13) & disjoint(H13::'a,F13) --> disjoint(H13::'a,G13)) &  \
\  (\\<forall>I13 J13. equal(I13::'a,J13) & function(I13) --> function(J13)) &      \
\  (\\<forall>K13 L13 M13 N13 O13 P13. equal(K13::'a,L13) & homomorphism(K13::'a,M13,N13,O13,P13) --> homomorphism(L13::'a,M13,N13,O13,P13)) &      \
\  (\\<forall>Q13 S13 R13 T13 U13 V13. equal(Q13::'a,R13) & homomorphism(S13::'a,Q13,T13,U13,V13) --> homomorphism(S13::'a,R13,T13,U13,V13)) &      \
\  (\\<forall>W13 Y13 Z13 X13 A14 B14. equal(W13::'a,X13) & homomorphism(Y13::'a,Z13,W13,A14,B14) --> homomorphism(Y13::'a,Z13,X13,A14,B14)) &      \
\  (\\<forall>C14 E14 F14 G14 D14 H14. equal(C14::'a,D14) & homomorphism(E14::'a,F14,G14,C14,H14) --> homomorphism(E14::'a,F14,G14,D14,H14)) &      \
\  (\\<forall>I14 K14 L14 M14 N14 J14. equal(I14::'a,J14) & homomorphism(K14::'a,L14,M14,N14,I14) --> homomorphism(K14::'a,L14,M14,N14,J14)) &      \
\  (\\<forall>O14 P14. equal(O14::'a,P14) & little_set(O14) --> little_set(P14)) &  \
\  (\\<forall>Q14 R14 S14 T14. equal(Q14::'a,R14) & maps(Q14::'a,S14,T14) --> maps(R14::'a,S14,T14)) &      \
\  (\\<forall>U14 W14 V14 X14. equal(U14::'a,V14) & maps(W14::'a,U14,X14) --> maps(W14::'a,V14,X14)) &      \
\  (\\<forall>Y14 A15 B15 Z14. equal(Y14::'a,Z14) & maps(A15::'a,B15,Y14) --> maps(A15::'a,B15,Z14)) &      \
\  (\\<forall>C15 D15 E15. equal(C15::'a,D15) & member(C15::'a,E15) --> member(D15::'a,E15)) &      \
\  (\\<forall>F15 H15 G15. equal(F15::'a,G15) & member(H15::'a,F15) --> member(H15::'a,G15)) &      \
\  (\\<forall>I15 J15. equal(I15::'a,J15) & one_to_one_function(I15) --> one_to_one_function(J15)) &        \
\  (\\<forall>K15 L15. equal(K15::'a,L15) & ordered_pair_predicate(K15) --> ordered_pair_predicate(L15)) &  \
\  (\\<forall>M15 N15 O15. equal(M15::'a,N15) & proper_subset(M15::'a,O15) --> proper_subset(N15::'a,O15)) &        \
\  (\\<forall>P15 R15 Q15. equal(P15::'a,Q15) & proper_subset(R15::'a,P15) --> proper_subset(R15::'a,Q15)) &        \
\  (\\<forall>S15 T15. equal(S15::'a,T15) & relation(S15) --> relation(T15)) &      \
\  (\\<forall>U15 V15. equal(U15::'a,V15) & single_valued_set(U15) --> single_valued_set(V15)) &    \
\  (\\<forall>W15 X15 Y15. equal(W15::'a,X15) & subset(W15::'a,Y15) --> subset(X15::'a,Y15)) &      \
\  (\\<forall>Z15 B16 A16. equal(Z15::'a,A16) & subset(B16::'a,Z15) --> subset(B16::'a,A16)) &      \
\  (~little_set(ordered_pair(a::'a,b))) --> False",
  meson_tac 1);


(*13 inferences so far.  Searching to depth 8.  0 secs*)
val SET046_5 = prove
 ("(\\<forall>Y X. ~(element(X::'a,a) & element(X::'a,Y) & element(Y::'a,X))) &     \
\  (\\<forall>X. element(X::'a,f(X)) | element(X::'a,a)) &     \
\  (\\<forall>X. element(f(X),X) | element(X::'a,a)) --> False",
  meson_tac 1);

(*33 inferences so far.  Searching to depth 9.  0.2 secs*)
val SET047_5 = prove
 ("(\\<forall>X Z Y. set_equal(X::'a,Y) & element(Z::'a,X) --> element(Z::'a,Y)) &  \
\  (\\<forall>Y Z X. set_equal(X::'a,Y) & element(Z::'a,Y) --> element(Z::'a,X)) &  \
\  (\\<forall>X Y. element(f(X::'a,Y),X) | element(f(X::'a,Y),Y) | set_equal(X::'a,Y)) &  \
\  (\\<forall>X Y. element(f(X::'a,Y),Y) & element(f(X::'a,Y),X) --> set_equal(X::'a,Y)) &  \
\  (set_equal(a::'a,b) | set_equal(b::'a,a)) & \
\  (~(set_equal(b::'a,a) & set_equal(a::'a,b))) --> False",
  meson_tac 1);

(*311 inferences so far.  Searching to depth 12.  0.1 secs*)
val SYN034_1 = prove
 ("(\\<forall>A. p(A::'a,a) | p(A::'a,f(A))) & \
\  (\\<forall>A. p(A::'a,a) | p(f(A),A)) & \
\  (\\<forall>A B. ~(p(A::'a,B) & p(B::'a,A) & p(B::'a,a))) --> False",
  meson_tac 1);

(*30 inferences so far.  Searching to depth 6.  0.2 secs*)
val SYN071_1 = prove
 ("(\\<forall>X. equal(X::'a,X)) &  \
\  (\\<forall>Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (\\<forall>Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (equal(a::'a,b) | equal(c::'a,d)) & \
\  (equal(a::'a,c) | equal(b::'a,d)) & \
\  (~equal(a::'a,d)) &      \
\  (~equal(b::'a,c)) --> False",
  meson_tac 1);

(****************SLOW
655670 inferences so far.  Searching to depth 44.  No proof after 10 minutes.
val SYN349_1 = prove_hard
 ("(\\<forall>X Y. f(w(X),g(X::'a,Y)) --> f(X::'a,g(X::'a,Y))) &    \
\  (\\<forall>X Y. f(X::'a,g(X::'a,Y)) --> f(w(X),g(X::'a,Y))) &    \
\  (\\<forall>Y X. f(X::'a,g(X::'a,Y)) & f(Y::'a,g(X::'a,Y)) --> f(g(X::'a,Y),Y) | f(g(X::'a,Y),w(X))) &       \
\  (\\<forall>Y X. f(g(X::'a,Y),Y) & f(Y::'a,g(X::'a,Y)) --> f(X::'a,g(X::'a,Y)) | f(g(X::'a,Y),w(X))) &       \
\  (\\<forall>Y X. f(X::'a,g(X::'a,Y)) | f(g(X::'a,Y),Y) | f(Y::'a,g(X::'a,Y)) | f(g(X::'a,Y),w(X))) &       \
\  (\\<forall>Y X. f(X::'a,g(X::'a,Y)) & f(g(X::'a,Y),Y) --> f(Y::'a,g(X::'a,Y)) | f(g(X::'a,Y),w(X))) &       \
\  (\\<forall>Y X. f(X::'a,g(X::'a,Y)) & f(g(X::'a,Y),w(X)) --> f(g(X::'a,Y),Y) | f(Y::'a,g(X::'a,Y))) &       \
\  (\\<forall>Y X. f(g(X::'a,Y),Y) & f(g(X::'a,Y),w(X)) --> f(X::'a,g(X::'a,Y)) | f(Y::'a,g(X::'a,Y))) &       \
\  (\\<forall>Y X. f(Y::'a,g(X::'a,Y)) & f(g(X::'a,Y),w(X)) --> f(X::'a,g(X::'a,Y)) | f(g(X::'a,Y),Y)) &       \
\  (\\<forall>Y X. ~(f(X::'a,g(X::'a,Y)) & f(g(X::'a,Y),Y) & f(Y::'a,g(X::'a,Y)) & f(g(X::'a,Y),w(X)))) --> False",
  meson_tac 1);
****************)

(*398 inferences so far.  Searching to depth 12.  0.4 secs*)
val SYN352_1 = prove
 ("(f(a::'a,b)) &   \
\  (\\<forall>X Y. f(X::'a,Y) --> f(b::'a,z(X::'a,Y)) | f(Y::'a,z(X::'a,Y))) &     \
\  (\\<forall>X Y. f(X::'a,Y) | f(z(X::'a,Y),z(X::'a,Y))) &        \
\  (\\<forall>X Y. f(b::'a,z(X::'a,Y)) | f(X::'a,z(X::'a,Y)) | f(z(X::'a,Y),z(X::'a,Y))) &    \
\  (\\<forall>X Y. f(b::'a,z(X::'a,Y)) & f(X::'a,z(X::'a,Y)) --> f(z(X::'a,Y),z(X::'a,Y))) &    \
\  (\\<forall>X Y. ~(f(X::'a,Y) & f(X::'a,z(X::'a,Y)) & f(Y::'a,z(X::'a,Y)))) &     \
\  (\\<forall>X Y. f(X::'a,Y) --> f(X::'a,z(X::'a,Y)) | f(Y::'a,z(X::'a,Y))) --> False",
  meson_tac 1);

(*5336 inferences so far.  Searching to depth 15.  5.3 secs*)
val TOP001_2 = prove_hard
 ("(\\<forall>Vf U. element_of_set(U::'a,union_of_members(Vf)) --> element_of_set(U::'a,f1(Vf::'a,U))) &    \
\  (\\<forall>U Vf. element_of_set(U::'a,union_of_members(Vf)) --> element_of_collection(f1(Vf::'a,U),Vf)) &    \
\  (\\<forall>U Uu1 Vf. element_of_set(U::'a,Uu1) & element_of_collection(Uu1::'a,Vf) --> element_of_set(U::'a,union_of_members(Vf))) &     \
\  (\\<forall>Vf X. basis(X::'a,Vf) --> equal_sets(union_of_members(Vf),X)) &       \
\  (\\<forall>Vf U X. element_of_collection(U::'a,top_of_basis(Vf)) & element_of_set(X::'a,U) --> element_of_set(X::'a,f10(Vf::'a,U,X))) &      \
\  (\\<forall>U X Vf. element_of_collection(U::'a,top_of_basis(Vf)) & element_of_set(X::'a,U) --> element_of_collection(f10(Vf::'a,U,X),Vf)) &      \
\  (\\<forall>X. subset_sets(X::'a,X)) &    \
\  (\\<forall>X U Y. subset_sets(X::'a,Y) & element_of_set(U::'a,X) --> element_of_set(U::'a,Y)) &  \
\  (\\<forall>X Y. equal_sets(X::'a,Y) --> subset_sets(X::'a,Y)) &      \
\  (\\<forall>Y X. subset_sets(X::'a,Y) | element_of_set(in_1st_set(X::'a,Y),X)) &     \
\  (\\<forall>X Y. element_of_set(in_1st_set(X::'a,Y),Y) --> subset_sets(X::'a,Y)) &    \
\  (basis(cx::'a,f)) &      \
\  (~subset_sets(union_of_members(top_of_basis(f)),cx)) --> False",
  meson_tac 1);

(*0 inferences so far.  Searching to depth 0.  0 secs*)
val TOP002_2 = prove
 ("(\\<forall>Vf U. element_of_collection(U::'a,top_of_basis(Vf)) | element_of_set(f11(Vf::'a,U),U)) & \
\  (\\<forall>X. ~element_of_set(X::'a,empty_set)) &        \
\  (~element_of_collection(empty_set::'a,top_of_basis(f))) --> False",
  meson_tac 1);

(*0 inferences so far.  Searching to depth 0.  6.5 secs.  BIG*)
val TOP004_1 = prove_hard
 ("(\\<forall>Vf U. element_of_set(U::'a,union_of_members(Vf)) --> element_of_set(U::'a,f1(Vf::'a,U))) &    \
\  (\\<forall>U Vf. element_of_set(U::'a,union_of_members(Vf)) --> element_of_collection(f1(Vf::'a,U),Vf)) &    \
\  (\\<forall>U Uu1 Vf. element_of_set(U::'a,Uu1) & element_of_collection(Uu1::'a,Vf) --> element_of_set(U::'a,union_of_members(Vf))) &     \
\  (\\<forall>Vf U Va. element_of_set(U::'a,intersection_of_members(Vf)) & element_of_collection(Va::'a,Vf) --> element_of_set(U::'a,Va)) & \
\  (\\<forall>U Vf. element_of_set(U::'a,intersection_of_members(Vf)) | element_of_collection(f2(Vf::'a,U),Vf)) &      \
\  (\\<forall>Vf U. element_of_set(U::'a,f2(Vf::'a,U)) --> element_of_set(U::'a,intersection_of_members(Vf))) &     \
\  (\\<forall>Vt X. topological_space(X::'a,Vt) --> equal_sets(union_of_members(Vt),X)) &   \
\  (\\<forall>X Vt. topological_space(X::'a,Vt) --> element_of_collection(empty_set::'a,Vt)) &  \
\  (\\<forall>X Vt. topological_space(X::'a,Vt) --> element_of_collection(X::'a,Vt)) &  \
\  (\\<forall>X Y Z Vt. topological_space(X::'a,Vt) & element_of_collection(Y::'a,Vt) & element_of_collection(Z::'a,Vt) --> element_of_collection(intersection_of_sets(Y::'a,Z),Vt)) &  \
\  (\\<forall>X Vf Vt. topological_space(X::'a,Vt) & subset_collections(Vf::'a,Vt) --> element_of_collection(union_of_members(Vf),Vt)) &        \
\  (\\<forall>X Vt. equal_sets(union_of_members(Vt),X) & element_of_collection(empty_set::'a,Vt) & element_of_collection(X::'a,Vt) --> topological_space(X::'a,Vt) | element_of_collection(f3(X::'a,Vt),Vt) | subset_collections(f5(X::'a,Vt),Vt)) &      \
\  (\\<forall>X Vt. equal_sets(union_of_members(Vt),X) & element_of_collection(empty_set::'a,Vt) & element_of_collection(X::'a,Vt) & element_of_collection(union_of_members(f5(X::'a,Vt)),Vt) --> topological_space(X::'a,Vt) | element_of_collection(f3(X::'a,Vt),Vt)) &  \
\  (\\<forall>X Vt. equal_sets(union_of_members(Vt),X) & element_of_collection(empty_set::'a,Vt) & element_of_collection(X::'a,Vt) --> topological_space(X::'a,Vt) | element_of_collection(f4(X::'a,Vt),Vt) | subset_collections(f5(X::'a,Vt),Vt)) &      \
\  (\\<forall>X Vt. equal_sets(union_of_members(Vt),X) & element_of_collection(empty_set::'a,Vt) & element_of_collection(X::'a,Vt) & element_of_collection(union_of_members(f5(X::'a,Vt)),Vt) --> topological_space(X::'a,Vt) | element_of_collection(f4(X::'a,Vt),Vt)) &  \
\  (\\<forall>X Vt. equal_sets(union_of_members(Vt),X) & element_of_collection(empty_set::'a,Vt) & element_of_collection(X::'a,Vt) & element_of_collection(intersection_of_sets(f3(X::'a,Vt),f4(X::'a,Vt)),Vt) --> topological_space(X::'a,Vt) | subset_collections(f5(X::'a,Vt),Vt)) &        \
\  (\\<forall>X Vt. equal_sets(union_of_members(Vt),X) & element_of_collection(empty_set::'a,Vt) & element_of_collection(X::'a,Vt) & element_of_collection(intersection_of_sets(f3(X::'a,Vt),f4(X::'a,Vt)),Vt) & element_of_collection(union_of_members(f5(X::'a,Vt)),Vt) --> topological_space(X::'a,Vt)) &    \
\  (\\<forall>U X Vt. open(U::'a,X,Vt) --> topological_space(X::'a,Vt)) &       \
\  (\\<forall>X U Vt. open(U::'a,X,Vt) --> element_of_collection(U::'a,Vt)) &   \
\  (\\<forall>X U Vt. topological_space(X::'a,Vt) & element_of_collection(U::'a,Vt) --> open(U::'a,X,Vt)) & \
\  (\\<forall>U X Vt. closed(U::'a,X,Vt) --> topological_space(X::'a,Vt)) &     \
\  (\\<forall>U X Vt. closed(U::'a,X,Vt) --> open(relative_complement_sets(U::'a,X),X,Vt)) &    \
\  (\\<forall>U X Vt. topological_space(X::'a,Vt) & open(relative_complement_sets(U::'a,X),X,Vt) --> closed(U::'a,X,Vt)) &  \
\  (\\<forall>Vs X Vt. finer(Vt::'a,Vs,X) --> topological_space(X::'a,Vt)) &    \
\  (\\<forall>Vt X Vs. finer(Vt::'a,Vs,X) --> topological_space(X::'a,Vs)) &    \
\  (\\<forall>X Vs Vt. finer(Vt::'a,Vs,X) --> subset_collections(Vs::'a,Vt)) &  \
\  (\\<forall>X Vs Vt. topological_space(X::'a,Vt) & topological_space(X::'a,Vs) & subset_collections(Vs::'a,Vt) --> finer(Vt::'a,Vs,X)) &      \
\  (\\<forall>Vf X. basis(X::'a,Vf) --> equal_sets(union_of_members(Vf),X)) &       \
\  (\\<forall>X Vf Y Vb1 Vb2. basis(X::'a,Vf) & element_of_set(Y::'a,X) & element_of_collection(Vb1::'a,Vf) & element_of_collection(Vb2::'a,Vf) & element_of_set(Y::'a,intersection_of_sets(Vb1::'a,Vb2)) --> element_of_set(Y::'a,f6(X::'a,Vf,Y,Vb1,Vb2))) &   \
\  (\\<forall>X Y Vb1 Vb2 Vf. basis(X::'a,Vf) & element_of_set(Y::'a,X) & element_of_collection(Vb1::'a,Vf) & element_of_collection(Vb2::'a,Vf) & element_of_set(Y::'a,intersection_of_sets(Vb1::'a,Vb2)) --> element_of_collection(f6(X::'a,Vf,Y,Vb1,Vb2),Vf)) &   \
\  (\\<forall>X Vf Y Vb1 Vb2. basis(X::'a,Vf) & element_of_set(Y::'a,X) & element_of_collection(Vb1::'a,Vf) & element_of_collection(Vb2::'a,Vf) & element_of_set(Y::'a,intersection_of_sets(Vb1::'a,Vb2)) --> subset_sets(f6(X::'a,Vf,Y,Vb1,Vb2),intersection_of_sets(Vb1::'a,Vb2))) &  \
\  (\\<forall>Vf X. equal_sets(union_of_members(Vf),X) --> basis(X::'a,Vf) | element_of_set(f7(X::'a,Vf),X)) & \
\  (\\<forall>X Vf. equal_sets(union_of_members(Vf),X) --> basis(X::'a,Vf) | element_of_collection(f8(X::'a,Vf),Vf)) & \
\  (\\<forall>X Vf. equal_sets(union_of_members(Vf),X) --> basis(X::'a,Vf) | element_of_collection(f9(X::'a,Vf),Vf)) & \
\  (\\<forall>X Vf. equal_sets(union_of_members(Vf),X) --> basis(X::'a,Vf) | element_of_set(f7(X::'a,Vf),intersection_of_sets(f8(X::'a,Vf),f9(X::'a,Vf)))) &   \
\  (\\<forall>Uu9 X Vf. equal_sets(union_of_members(Vf),X) & element_of_set(f7(X::'a,Vf),Uu9) & element_of_collection(Uu9::'a,Vf) & subset_sets(Uu9::'a,intersection_of_sets(f8(X::'a,Vf),f9(X::'a,Vf))) --> basis(X::'a,Vf)) & \
\  (\\<forall>Vf U X. element_of_collection(U::'a,top_of_basis(Vf)) & element_of_set(X::'a,U) --> element_of_set(X::'a,f10(Vf::'a,U,X))) &      \
\  (\\<forall>U X Vf. element_of_collection(U::'a,top_of_basis(Vf)) & element_of_set(X::'a,U) --> element_of_collection(f10(Vf::'a,U,X),Vf)) &      \
\  (\\<forall>Vf X U. element_of_collection(U::'a,top_of_basis(Vf)) & element_of_set(X::'a,U) --> subset_sets(f10(Vf::'a,U,X),U)) & \
\  (\\<forall>Vf U. element_of_collection(U::'a,top_of_basis(Vf)) | element_of_set(f11(Vf::'a,U),U)) & \
\  (\\<forall>Vf Uu11 U. element_of_set(f11(Vf::'a,U),Uu11) & element_of_collection(Uu11::'a,Vf) & subset_sets(Uu11::'a,U) --> element_of_collection(U::'a,top_of_basis(Vf))) & \
\  (\\<forall>U Y X Vt. element_of_collection(U::'a,subspace_topology(X::'a,Vt,Y)) --> topological_space(X::'a,Vt)) &       \
\  (\\<forall>U Vt Y X. element_of_collection(U::'a,subspace_topology(X::'a,Vt,Y)) --> subset_sets(Y::'a,X)) &      \
\  (\\<forall>X Y U Vt. element_of_collection(U::'a,subspace_topology(X::'a,Vt,Y)) --> element_of_collection(f12(X::'a,Vt,Y,U),Vt)) &       \
\  (\\<forall>X Vt Y U. element_of_collection(U::'a,subspace_topology(X::'a,Vt,Y)) --> equal_sets(U::'a,intersection_of_sets(Y::'a,f12(X::'a,Vt,Y,U)))) &   \
\  (\\<forall>X Vt U Y Uu12. topological_space(X::'a,Vt) & subset_sets(Y::'a,X) & element_of_collection(Uu12::'a,Vt) & equal_sets(U::'a,intersection_of_sets(Y::'a,Uu12)) --> element_of_collection(U::'a,subspace_topology(X::'a,Vt,Y))) & \
\  (\\<forall>U Y X Vt. element_of_set(U::'a,interior(Y::'a,X,Vt)) --> topological_space(X::'a,Vt)) &       \
\  (\\<forall>U Vt Y X. element_of_set(U::'a,interior(Y::'a,X,Vt)) --> subset_sets(Y::'a,X)) &      \
\  (\\<forall>Y X Vt U. element_of_set(U::'a,interior(Y::'a,X,Vt)) --> element_of_set(U::'a,f13(Y::'a,X,Vt,U))) &       \
\  (\\<forall>X Vt U Y. element_of_set(U::'a,interior(Y::'a,X,Vt)) --> subset_sets(f13(Y::'a,X,Vt,U),Y)) &  \
\  (\\<forall>Y U X Vt. element_of_set(U::'a,interior(Y::'a,X,Vt)) --> open(f13(Y::'a,X,Vt,U),X,Vt)) &      \
\  (\\<forall>U Y Uu13 X Vt. topological_space(X::'a,Vt) & subset_sets(Y::'a,X) & element_of_set(U::'a,Uu13) & subset_sets(Uu13::'a,Y) & open(Uu13::'a,X,Vt) --> element_of_set(U::'a,interior(Y::'a,X,Vt))) &      \
\  (\\<forall>U Y X Vt. element_of_set(U::'a,closure(Y::'a,X,Vt)) --> topological_space(X::'a,Vt)) &        \
\  (\\<forall>U Vt Y X. element_of_set(U::'a,closure(Y::'a,X,Vt)) --> subset_sets(Y::'a,X)) &       \
\  (\\<forall>Y X Vt U V. element_of_set(U::'a,closure(Y::'a,X,Vt)) & subset_sets(Y::'a,V) & closed(V::'a,X,Vt) --> element_of_set(U::'a,V)) &      \
\  (\\<forall>Y X Vt U. topological_space(X::'a,Vt) & subset_sets(Y::'a,X) --> element_of_set(U::'a,closure(Y::'a,X,Vt)) | subset_sets(Y::'a,f14(Y::'a,X,Vt,U))) &     \
\  (\\<forall>Y U X Vt. topological_space(X::'a,Vt) & subset_sets(Y::'a,X) --> element_of_set(U::'a,closure(Y::'a,X,Vt)) | closed(f14(Y::'a,X,Vt,U),X,Vt)) &       \
\  (\\<forall>Y X Vt U. topological_space(X::'a,Vt) & subset_sets(Y::'a,X) & element_of_set(U::'a,f14(Y::'a,X,Vt,U)) --> element_of_set(U::'a,closure(Y::'a,X,Vt))) &   \
\  (\\<forall>U Y X Vt. neighborhood(U::'a,Y,X,Vt) --> topological_space(X::'a,Vt)) &   \
\  (\\<forall>Y U X Vt. neighborhood(U::'a,Y,X,Vt) --> open(U::'a,X,Vt)) &      \
\  (\\<forall>X Vt Y U. neighborhood(U::'a,Y,X,Vt) --> element_of_set(Y::'a,U)) &       \
\  (\\<forall>X Vt Y U. topological_space(X::'a,Vt) & open(U::'a,X,Vt) & element_of_set(Y::'a,U) --> neighborhood(U::'a,Y,X,Vt)) &      \
\  (\\<forall>Z Y X Vt. limit_point(Z::'a,Y,X,Vt) --> topological_space(X::'a,Vt)) &    \
\  (\\<forall>Z Vt Y X. limit_point(Z::'a,Y,X,Vt) --> subset_sets(Y::'a,X)) &   \
\  (\\<forall>Z X Vt U Y. limit_point(Z::'a,Y,X,Vt) & neighborhood(U::'a,Z,X,Vt) --> element_of_set(f15(Z::'a,Y,X,Vt,U),intersection_of_sets(U::'a,Y))) &       \
\  (\\<forall>Y X Vt U Z. ~(limit_point(Z::'a,Y,X,Vt) & neighborhood(U::'a,Z,X,Vt) & eq_p(f15(Z::'a,Y,X,Vt,U),Z))) &        \
\  (\\<forall>Y Z X Vt. topological_space(X::'a,Vt) & subset_sets(Y::'a,X) --> limit_point(Z::'a,Y,X,Vt) | neighborhood(f16(Z::'a,Y,X,Vt),Z,X,Vt)) &   \
\  (\\<forall>X Vt Y Uu16 Z. topological_space(X::'a,Vt) & subset_sets(Y::'a,X) & element_of_set(Uu16::'a,intersection_of_sets(f16(Z::'a,Y,X,Vt),Y)) --> limit_point(Z::'a,Y,X,Vt) | eq_p(Uu16::'a,Z)) &       \
\  (\\<forall>U Y X Vt. element_of_set(U::'a,boundary(Y::'a,X,Vt)) --> topological_space(X::'a,Vt)) &       \
\  (\\<forall>U Y X Vt. element_of_set(U::'a,boundary(Y::'a,X,Vt)) --> element_of_set(U::'a,closure(Y::'a,X,Vt))) &     \
\  (\\<forall>U Y X Vt. element_of_set(U::'a,boundary(Y::'a,X,Vt)) --> element_of_set(U::'a,closure(relative_complement_sets(Y::'a,X),X,Vt))) & \
\  (\\<forall>U Y X Vt. topological_space(X::'a,Vt) & element_of_set(U::'a,closure(Y::'a,X,Vt)) & element_of_set(U::'a,closure(relative_complement_sets(Y::'a,X),X,Vt)) --> element_of_set(U::'a,boundary(Y::'a,X,Vt))) &   \
\  (\\<forall>X Vt. hausdorff(X::'a,Vt) --> topological_space(X::'a,Vt)) &      \
\  (\\<forall>X_2 X_1 X Vt. hausdorff(X::'a,Vt) & element_of_set(X_1::'a,X) & element_of_set(X_2::'a,X) --> eq_p(X_1::'a,X_2) | neighborhood(f17(X::'a,Vt,X_1,X_2),X_1,X,Vt)) &    \
\  (\\<forall>X_1 X_2 X Vt. hausdorff(X::'a,Vt) & element_of_set(X_1::'a,X) & element_of_set(X_2::'a,X) --> eq_p(X_1::'a,X_2) | neighborhood(f18(X::'a,Vt,X_1,X_2),X_2,X,Vt)) &    \
\  (\\<forall>X Vt X_1 X_2. hausdorff(X::'a,Vt) & element_of_set(X_1::'a,X) & element_of_set(X_2::'a,X) --> eq_p(X_1::'a,X_2) | disjoint_s(f17(X::'a,Vt,X_1,X_2),f18(X::'a,Vt,X_1,X_2))) &     \
\  (\\<forall>Vt X. topological_space(X::'a,Vt) --> hausdorff(X::'a,Vt) | element_of_set(f19(X::'a,Vt),X)) &       \
\  (\\<forall>Vt X. topological_space(X::'a,Vt) --> hausdorff(X::'a,Vt) | element_of_set(f20(X::'a,Vt),X)) &       \
\  (\\<forall>X Vt. topological_space(X::'a,Vt) & eq_p(f19(X::'a,Vt),f20(X::'a,Vt)) --> hausdorff(X::'a,Vt)) &  \
\  (\\<forall>X Vt Uu19 Uu20. topological_space(X::'a,Vt) & neighborhood(Uu19::'a,f19(X::'a,Vt),X,Vt) & neighborhood(Uu20::'a,f20(X::'a,Vt),X,Vt) & disjoint_s(Uu19::'a,Uu20) --> hausdorff(X::'a,Vt)) &    \
\  (\\<forall>Va1 Va2 X Vt. separation(Va1::'a,Va2,X,Vt) --> topological_space(X::'a,Vt)) &     \
\  (\\<forall>Va2 X Vt Va1. ~(separation(Va1::'a,Va2,X,Vt) & equal_sets(Va1::'a,empty_set))) &  \
\  (\\<forall>Va1 X Vt Va2. ~(separation(Va1::'a,Va2,X,Vt) & equal_sets(Va2::'a,empty_set))) &  \
\  (\\<forall>Va2 X Va1 Vt. separation(Va1::'a,Va2,X,Vt) --> element_of_collection(Va1::'a,Vt)) &       \
\  (\\<forall>Va1 X Va2 Vt. separation(Va1::'a,Va2,X,Vt) --> element_of_collection(Va2::'a,Vt)) &       \
\  (\\<forall>Vt Va1 Va2 X. separation(Va1::'a,Va2,X,Vt) --> equal_sets(union_of_sets(Va1::'a,Va2),X)) &        \
\  (\\<forall>X Vt Va1 Va2. separation(Va1::'a,Va2,X,Vt) --> disjoint_s(Va1::'a,Va2)) & \
\  (\\<forall>Vt X Va1 Va2. topological_space(X::'a,Vt) & element_of_collection(Va1::'a,Vt) & element_of_collection(Va2::'a,Vt) & equal_sets(union_of_sets(Va1::'a,Va2),X) & disjoint_s(Va1::'a,Va2) --> separation(Va1::'a,Va2,X,Vt) | equal_sets(Va1::'a,empty_set) | equal_sets(Va2::'a,empty_set)) &      \
\  (\\<forall>X Vt. connected_space(X::'a,Vt) --> topological_space(X::'a,Vt)) &        \
\  (\\<forall>Va1 Va2 X Vt. ~(connected_space(X::'a,Vt) & separation(Va1::'a,Va2,X,Vt))) &      \
\  (\\<forall>X Vt. topological_space(X::'a,Vt) --> connected_space(X::'a,Vt) | separation(f21(X::'a,Vt),f22(X::'a,Vt),X,Vt)) &        \
\  (\\<forall>Va X Vt. connected_set(Va::'a,X,Vt) --> topological_space(X::'a,Vt)) &    \
\  (\\<forall>Vt Va X. connected_set(Va::'a,X,Vt) --> subset_sets(Va::'a,X)) &  \
\  (\\<forall>X Vt Va. connected_set(Va::'a,X,Vt) --> connected_space(Va::'a,subspace_topology(X::'a,Vt,Va))) &     \
\  (\\<forall>X Vt Va. topological_space(X::'a,Vt) & subset_sets(Va::'a,X) & connected_space(Va::'a,subspace_topology(X::'a,Vt,Va)) --> connected_set(Va::'a,X,Vt)) &       \
\  (\\<forall>Vf X Vt. open_covering(Vf::'a,X,Vt) --> topological_space(X::'a,Vt)) &    \
\  (\\<forall>X Vf Vt. open_covering(Vf::'a,X,Vt) --> subset_collections(Vf::'a,Vt)) &  \
\  (\\<forall>Vt Vf X. open_covering(Vf::'a,X,Vt) --> equal_sets(union_of_members(Vf),X)) & \
\  (\\<forall>Vt Vf X. topological_space(X::'a,Vt) & subset_collections(Vf::'a,Vt) & equal_sets(union_of_members(Vf),X) --> open_covering(Vf::'a,X,Vt)) &   \
\  (\\<forall>X Vt. compact_space(X::'a,Vt) --> topological_space(X::'a,Vt)) &  \
\  (\\<forall>X Vt Vf1. compact_space(X::'a,Vt) & open_covering(Vf1::'a,X,Vt) --> finite(f23(X::'a,Vt,Vf1))) &      \
\  (\\<forall>X Vt Vf1. compact_space(X::'a,Vt) & open_covering(Vf1::'a,X,Vt) --> subset_collections(f23(X::'a,Vt,Vf1),Vf1)) &      \
\  (\\<forall>Vf1 X Vt. compact_space(X::'a,Vt) & open_covering(Vf1::'a,X,Vt) --> open_covering(f23(X::'a,Vt,Vf1),X,Vt)) &  \
\  (\\<forall>X Vt. topological_space(X::'a,Vt) --> compact_space(X::'a,Vt) | open_covering(f24(X::'a,Vt),X,Vt)) & \
\  (\\<forall>Uu24 X Vt. topological_space(X::'a,Vt) & finite(Uu24) & subset_collections(Uu24::'a,f24(X::'a,Vt)) & open_covering(Uu24::'a,X,Vt) --> compact_space(X::'a,Vt)) &      \
\  (\\<forall>Va X Vt. compact_set(Va::'a,X,Vt) --> topological_space(X::'a,Vt)) &      \
\  (\\<forall>Vt Va X. compact_set(Va::'a,X,Vt) --> subset_sets(Va::'a,X)) &    \
\  (\\<forall>X Vt Va. compact_set(Va::'a,X,Vt) --> compact_space(Va::'a,subspace_topology(X::'a,Vt,Va))) & \
\  (\\<forall>X Vt Va. topological_space(X::'a,Vt) & subset_sets(Va::'a,X) & compact_space(Va::'a,subspace_topology(X::'a,Vt,Va)) --> compact_set(Va::'a,X,Vt)) &   \
\  (basis(cx::'a,f)) &      \
\  (\\<forall>U. element_of_collection(U::'a,top_of_basis(f))) &    \
\  (\\<forall>V. element_of_collection(V::'a,top_of_basis(f))) &    \
\  (\\<forall>U V. ~element_of_collection(intersection_of_sets(U::'a,V),top_of_basis(f))) --> False",
  meson_tac 1);


(*0 inferences so far.  Searching to depth 0.  0.8 secs*)
val TOP004_2 = prove
 ("(\\<forall>U Uu1 Vf. element_of_set(U::'a,Uu1) & element_of_collection(Uu1::'a,Vf) --> element_of_set(U::'a,union_of_members(Vf))) &     \
\  (\\<forall>Vf X. basis(X::'a,Vf) --> equal_sets(union_of_members(Vf),X)) &       \
\  (\\<forall>X Vf Y Vb1 Vb2. basis(X::'a,Vf) & element_of_set(Y::'a,X) & element_of_collection(Vb1::'a,Vf) & element_of_collection(Vb2::'a,Vf) & element_of_set(Y::'a,intersection_of_sets(Vb1::'a,Vb2)) --> element_of_set(Y::'a,f6(X::'a,Vf,Y,Vb1,Vb2))) &   \
\  (\\<forall>X Y Vb1 Vb2 Vf. basis(X::'a,Vf) & element_of_set(Y::'a,X) & element_of_collection(Vb1::'a,Vf) & element_of_collection(Vb2::'a,Vf) & element_of_set(Y::'a,intersection_of_sets(Vb1::'a,Vb2)) --> element_of_collection(f6(X::'a,Vf,Y,Vb1,Vb2),Vf)) &   \
\  (\\<forall>X Vf Y Vb1 Vb2. basis(X::'a,Vf) & element_of_set(Y::'a,X) & element_of_collection(Vb1::'a,Vf) & element_of_collection(Vb2::'a,Vf) & element_of_set(Y::'a,intersection_of_sets(Vb1::'a,Vb2)) --> subset_sets(f6(X::'a,Vf,Y,Vb1,Vb2),intersection_of_sets(Vb1::'a,Vb2))) &  \
\  (\\<forall>Vf U X. element_of_collection(U::'a,top_of_basis(Vf)) & element_of_set(X::'a,U) --> element_of_set(X::'a,f10(Vf::'a,U,X))) &      \
\  (\\<forall>U X Vf. element_of_collection(U::'a,top_of_basis(Vf)) & element_of_set(X::'a,U) --> element_of_collection(f10(Vf::'a,U,X),Vf)) &      \
\  (\\<forall>Vf X U. element_of_collection(U::'a,top_of_basis(Vf)) & element_of_set(X::'a,U) --> subset_sets(f10(Vf::'a,U,X),U)) & \
\  (\\<forall>Vf U. element_of_collection(U::'a,top_of_basis(Vf)) | element_of_set(f11(Vf::'a,U),U)) & \
\  (\\<forall>Vf Uu11 U. element_of_set(f11(Vf::'a,U),Uu11) & element_of_collection(Uu11::'a,Vf) & subset_sets(Uu11::'a,U) --> element_of_collection(U::'a,top_of_basis(Vf))) & \
\  (\\<forall>Y X Z. subset_sets(X::'a,Y) & subset_sets(Y::'a,Z) --> subset_sets(X::'a,Z)) &        \
\  (\\<forall>Y Z X. element_of_set(Z::'a,intersection_of_sets(X::'a,Y)) --> element_of_set(Z::'a,X)) &     \
\  (\\<forall>X Z Y. element_of_set(Z::'a,intersection_of_sets(X::'a,Y)) --> element_of_set(Z::'a,Y)) &     \
\  (\\<forall>X Z Y. element_of_set(Z::'a,X) & element_of_set(Z::'a,Y) --> element_of_set(Z::'a,intersection_of_sets(X::'a,Y))) &       \
\  (\\<forall>X U Y V. subset_sets(X::'a,Y) & subset_sets(U::'a,V) --> subset_sets(intersection_of_sets(X::'a,U),intersection_of_sets(Y::'a,V))) &      \
\  (\\<forall>X Z Y. equal_sets(X::'a,Y) & element_of_set(Z::'a,X) --> element_of_set(Z::'a,Y)) &   \
\  (\\<forall>Y X. equal_sets(intersection_of_sets(X::'a,Y),intersection_of_sets(Y::'a,X))) &   \
\  (basis(cx::'a,f)) &      \
\  (\\<forall>U. element_of_collection(U::'a,top_of_basis(f))) &    \
\  (\\<forall>V. element_of_collection(V::'a,top_of_basis(f))) &    \
\  (\\<forall>U V. ~element_of_collection(intersection_of_sets(U::'a,V),top_of_basis(f))) --> False",
  meson_tac 1);

(*53777 inferences so far.  Searching to depth 20.  68.7 secs*)
val TOP005_2 = prove_hard
 ("(\\<forall>Vf U. element_of_set(U::'a,union_of_members(Vf)) --> element_of_set(U::'a,f1(Vf::'a,U))) &    \
\  (\\<forall>U Vf. element_of_set(U::'a,union_of_members(Vf)) --> element_of_collection(f1(Vf::'a,U),Vf)) &    \
\  (\\<forall>Vf U X. element_of_collection(U::'a,top_of_basis(Vf)) & element_of_set(X::'a,U) --> element_of_set(X::'a,f10(Vf::'a,U,X))) &      \
\  (\\<forall>U X Vf. element_of_collection(U::'a,top_of_basis(Vf)) & element_of_set(X::'a,U) --> element_of_collection(f10(Vf::'a,U,X),Vf)) &      \
\  (\\<forall>Vf X U. element_of_collection(U::'a,top_of_basis(Vf)) & element_of_set(X::'a,U) --> subset_sets(f10(Vf::'a,U,X),U)) & \
\  (\\<forall>Vf U. element_of_collection(U::'a,top_of_basis(Vf)) | element_of_set(f11(Vf::'a,U),U)) & \
\  (\\<forall>Vf Uu11 U. element_of_set(f11(Vf::'a,U),Uu11) & element_of_collection(Uu11::'a,Vf) & subset_sets(Uu11::'a,U) --> element_of_collection(U::'a,top_of_basis(Vf))) & \
\  (\\<forall>X U Y. element_of_set(U::'a,X) --> subset_sets(X::'a,Y) | element_of_set(U::'a,Y)) & \
\  (\\<forall>Y X Z. subset_sets(X::'a,Y) & element_of_collection(Y::'a,Z) --> subset_sets(X::'a,union_of_members(Z))) &    \
\  (\\<forall>X U Y. subset_collections(X::'a,Y) & element_of_collection(U::'a,X) --> element_of_collection(U::'a,Y)) &     \
\  (subset_collections(g::'a,top_of_basis(f))) &    \
\  (~element_of_collection(union_of_members(g),top_of_basis(f))) --> False",
  meson_tac 1);


