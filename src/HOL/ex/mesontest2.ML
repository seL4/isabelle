(*  Title:      HOL/ex/mesontest2
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

MORE and MUCH HARDER test data for the MESON proof procedure

Courtesy John Harrison 
*)

(*All but the fastest are ignored to reduce build time*)
val even_hard_ones = false;

(*Prod.thy instead of HOL.thy regards arguments as tuples.
  But Main.thy would allow clashes with many other constants*)
fun prove (s,tac) = prove_goal Prod.thy s (fn [] => [tac]);

fun prove_hard arg = if even_hard_ones then prove arg else TrueI;

val meson_tac = safe_meson_tac 1;

set proof_timing;

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
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X Y. sum(X::'a,Y,add(X::'a,Y))) & \
\  (! X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (! Y X Z. sum(X::'a,Y,Z) --> sum(Y::'a,X,Z)) &       \
\  (! Y X Z. product(X::'a,Y,Z) --> product(Y::'a,X,Z)) &       \
\  (! X. sum(additive_identity::'a,X,X)) &  \
\  (! X. sum(X::'a,additive_identity,X)) &  \
\  (! X. product(multiplicative_identity::'a,X,X)) &        \
\  (! X. product(X::'a,multiplicative_identity,X)) &        \
\  (! Y Z X V3 V1 V2 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & product(X::'a,V3,V4) --> sum(V1::'a,V2,V4)) &        \
\  (! Y Z V1 V2 X V3 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(X::'a,V3,V4)) &        \
\  (! Y Z V3 X V1 V2 V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & product(V3::'a,X,V4) --> sum(V1::'a,V2,V4)) &        \
\  (! Y Z V1 V2 V3 X V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(V3::'a,X,V4)) &        \
\  (! Y Z X V3 V1 V2 V4. sum(X::'a,Y,V1) & sum(X::'a,Z,V2) & product(Y::'a,Z,V3) & sum(X::'a,V3,V4) --> product(V1::'a,V2,V4)) &    \
\  (! Y Z V1 V2 X V3 V4. sum(X::'a,Y,V1) & sum(X::'a,Z,V2) & product(Y::'a,Z,V3) & product(V1::'a,V2,V4) --> sum(X::'a,V3,V4)) &    \
\  (! Y Z V3 X V1 V2 V4. sum(Y::'a,X,V1) & sum(Z::'a,X,V2) & product(Y::'a,Z,V3) & sum(V3::'a,X,V4) --> product(V1::'a,V2,V4)) &    \
\  (! Y Z V1 V2 V3 X V4. sum(Y::'a,X,V1) & sum(Z::'a,X,V2) & product(Y::'a,Z,V3) & product(V1::'a,V2,V4) --> sum(V3::'a,X,V4)) &    \
\  (! X. sum(inverse(X),X,multiplicative_identity)) &   \
\  (! X. sum(X::'a,inverse(X),multiplicative_identity)) &   \
\  (! X. product(inverse(X),X,additive_identity)) &     \
\  (! X. product(X::'a,inverse(X),additive_identity)) &     \
\  (! X Y U V. sum(X::'a,Y,U) & sum(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (! X Y U V. product(X::'a,Y,U) & product(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (! X Y W Z. equal(X::'a,Y) & sum(X::'a,W,Z) --> sum(Y::'a,W,Z)) &        \
\  (! X W Y Z. equal(X::'a,Y) & sum(W::'a,X,Z) --> sum(W::'a,Y,Z)) &        \
\  (! X W Z Y. equal(X::'a,Y) & sum(W::'a,Z,X) --> sum(W::'a,Z,Y)) &        \
\  (! X Y W Z. equal(X::'a,Y) & product(X::'a,W,Z) --> product(Y::'a,W,Z)) &        \
\  (! X W Y Z. equal(X::'a,Y) & product(W::'a,X,Z) --> product(W::'a,Y,Z)) &        \
\  (! X W Z Y. equal(X::'a,Y) & product(W::'a,Z,X) --> product(W::'a,Z,Y)) &        \
\  (! X Y W. equal(X::'a,Y) --> equal(add(X::'a,W),add(Y::'a,W))) & \
\  (! X W Y. equal(X::'a,Y) --> equal(add(W::'a,X),add(W::'a,Y))) & \
\  (! X Y W. equal(X::'a,Y) --> equal(multiply(X::'a,W),multiply(Y::'a,W))) &       \
\  (! X W Y. equal(X::'a,Y) --> equal(multiply(W::'a,X),multiply(W::'a,Y))) &       \
\  (! X Y. equal(X::'a,Y) --> equal(inverse(X),inverse(Y))) &       \
\  (~product(x::'a,x,x)) --> False",
  meson_tac);

(*51194 inferences so far.  Searching to depth 13. 204.6 secs
  Strange!  The previous problem also has 51194 inferences at depth 13.  They
   must be very similar!*)
val BOO004_1 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X Y. sum(X::'a,Y,add(X::'a,Y))) & \
\  (! X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (! Y X Z. sum(X::'a,Y,Z) --> sum(Y::'a,X,Z)) &       \
\  (! Y X Z. product(X::'a,Y,Z) --> product(Y::'a,X,Z)) &       \
\  (! X. sum(additive_identity::'a,X,X)) &  \
\  (! X. sum(X::'a,additive_identity,X)) &  \
\  (! X. product(multiplicative_identity::'a,X,X)) &        \
\  (! X. product(X::'a,multiplicative_identity,X)) &        \
\  (! Y Z X V3 V1 V2 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & product(X::'a,V3,V4) --> sum(V1::'a,V2,V4)) &        \
\  (! Y Z V1 V2 X V3 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(X::'a,V3,V4)) &        \
\  (! Y Z V3 X V1 V2 V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & product(V3::'a,X,V4) --> sum(V1::'a,V2,V4)) &        \
\  (! Y Z V1 V2 V3 X V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(V3::'a,X,V4)) &        \
\  (! Y Z X V3 V1 V2 V4. sum(X::'a,Y,V1) & sum(X::'a,Z,V2) & product(Y::'a,Z,V3) & sum(X::'a,V3,V4) --> product(V1::'a,V2,V4)) &    \
\  (! Y Z V1 V2 X V3 V4. sum(X::'a,Y,V1) & sum(X::'a,Z,V2) & product(Y::'a,Z,V3) & product(V1::'a,V2,V4) --> sum(X::'a,V3,V4)) &    \
\  (! Y Z V3 X V1 V2 V4. sum(Y::'a,X,V1) & sum(Z::'a,X,V2) & product(Y::'a,Z,V3) & sum(V3::'a,X,V4) --> product(V1::'a,V2,V4)) &    \
\  (! Y Z V1 V2 V3 X V4. sum(Y::'a,X,V1) & sum(Z::'a,X,V2) & product(Y::'a,Z,V3) & product(V1::'a,V2,V4) --> sum(V3::'a,X,V4)) &    \
\  (! X. sum(inverse(X),X,multiplicative_identity)) &   \
\  (! X. sum(X::'a,inverse(X),multiplicative_identity)) &   \
\  (! X. product(inverse(X),X,additive_identity)) &     \
\  (! X. product(X::'a,inverse(X),additive_identity)) &     \
\  (! X Y U V. sum(X::'a,Y,U) & sum(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (! X Y U V. product(X::'a,Y,U) & product(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (! X Y W Z. equal(X::'a,Y) & sum(X::'a,W,Z) --> sum(Y::'a,W,Z)) &        \
\  (! X W Y Z. equal(X::'a,Y) & sum(W::'a,X,Z) --> sum(W::'a,Y,Z)) &        \
\  (! X W Z Y. equal(X::'a,Y) & sum(W::'a,Z,X) --> sum(W::'a,Z,Y)) &        \
\  (! X Y W Z. equal(X::'a,Y) & product(X::'a,W,Z) --> product(Y::'a,W,Z)) &        \
\  (! X W Y Z. equal(X::'a,Y) & product(W::'a,X,Z) --> product(W::'a,Y,Z)) &        \
\  (! X W Z Y. equal(X::'a,Y) & product(W::'a,Z,X) --> product(W::'a,Z,Y)) &        \
\  (! X Y W. equal(X::'a,Y) --> equal(add(X::'a,W),add(Y::'a,W))) & \
\  (! X W Y. equal(X::'a,Y) --> equal(add(W::'a,X),add(W::'a,Y))) & \
\  (! X Y W. equal(X::'a,Y) --> equal(multiply(X::'a,W),multiply(Y::'a,W))) &       \
\  (! X W Y. equal(X::'a,Y) --> equal(multiply(W::'a,X),multiply(W::'a,Y))) &       \
\  (! X Y. equal(X::'a,Y) --> equal(inverse(X),inverse(Y))) &       \
\  (~sum(x::'a,x,x)) --> False",
  meson_tac);

(*74799 inferences so far.  Searching to depth 13.  290.0 secs*)
val BOO005_1 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X Y. sum(X::'a,Y,add(X::'a,Y))) & \
\  (! X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (! Y X Z. sum(X::'a,Y,Z) --> sum(Y::'a,X,Z)) &       \
\  (! Y X Z. product(X::'a,Y,Z) --> product(Y::'a,X,Z)) &       \
\  (! X. sum(additive_identity::'a,X,X)) &  \
\  (! X. sum(X::'a,additive_identity,X)) &  \
\  (! X. product(multiplicative_identity::'a,X,X)) &        \
\  (! X. product(X::'a,multiplicative_identity,X)) &        \
\  (! Y Z X V3 V1 V2 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & product(X::'a,V3,V4) --> sum(V1::'a,V2,V4)) &        \
\  (! Y Z V1 V2 X V3 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(X::'a,V3,V4)) &        \
\  (! Y Z V3 X V1 V2 V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & product(V3::'a,X,V4) --> sum(V1::'a,V2,V4)) &        \
\  (! Y Z V1 V2 V3 X V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(V3::'a,X,V4)) &        \
\  (! Y Z X V3 V1 V2 V4. sum(X::'a,Y,V1) & sum(X::'a,Z,V2) & product(Y::'a,Z,V3) & sum(X::'a,V3,V4) --> product(V1::'a,V2,V4)) &    \
\  (! Y Z V1 V2 X V3 V4. sum(X::'a,Y,V1) & sum(X::'a,Z,V2) & product(Y::'a,Z,V3) & product(V1::'a,V2,V4) --> sum(X::'a,V3,V4)) &    \
\  (! Y Z V3 X V1 V2 V4. sum(Y::'a,X,V1) & sum(Z::'a,X,V2) & product(Y::'a,Z,V3) & sum(V3::'a,X,V4) --> product(V1::'a,V2,V4)) &    \
\  (! Y Z V1 V2 V3 X V4. sum(Y::'a,X,V1) & sum(Z::'a,X,V2) & product(Y::'a,Z,V3) & product(V1::'a,V2,V4) --> sum(V3::'a,X,V4)) &    \
\  (! X. sum(inverse(X),X,multiplicative_identity)) &   \
\  (! X. sum(X::'a,inverse(X),multiplicative_identity)) &   \
\  (! X. product(inverse(X),X,additive_identity)) &     \
\  (! X. product(X::'a,inverse(X),additive_identity)) &     \
\  (! X Y U V. sum(X::'a,Y,U) & sum(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (! X Y U V. product(X::'a,Y,U) & product(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (! X Y W Z. equal(X::'a,Y) & sum(X::'a,W,Z) --> sum(Y::'a,W,Z)) &        \
\  (! X W Y Z. equal(X::'a,Y) & sum(W::'a,X,Z) --> sum(W::'a,Y,Z)) &        \
\  (! X W Z Y. equal(X::'a,Y) & sum(W::'a,Z,X) --> sum(W::'a,Z,Y)) &        \
\  (! X Y W Z. equal(X::'a,Y) & product(X::'a,W,Z) --> product(Y::'a,W,Z)) &        \
\  (! X W Y Z. equal(X::'a,Y) & product(W::'a,X,Z) --> product(W::'a,Y,Z)) &        \
\  (! X W Z Y. equal(X::'a,Y) & product(W::'a,Z,X) --> product(W::'a,Z,Y)) &        \
\  (! X Y W. equal(X::'a,Y) --> equal(add(X::'a,W),add(Y::'a,W))) & \
\  (! X W Y. equal(X::'a,Y) --> equal(add(W::'a,X),add(W::'a,Y))) & \
\  (! X Y W. equal(X::'a,Y) --> equal(multiply(X::'a,W),multiply(Y::'a,W))) &       \
\  (! X W Y. equal(X::'a,Y) --> equal(multiply(W::'a,X),multiply(W::'a,Y))) &       \
\  (! X Y. equal(X::'a,Y) --> equal(inverse(X),inverse(Y))) &       \
\  (~sum(x::'a,multiplicative_identity,multiplicative_identity)) --> False",
  meson_tac);

(*74799 inferences so far.  Searching to depth 13.  314.6 secs*)
val BOO006_1 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X Y. sum(X::'a,Y,add(X::'a,Y))) & \
\  (! X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (! Y X Z. sum(X::'a,Y,Z) --> sum(Y::'a,X,Z)) &       \
\  (! Y X Z. product(X::'a,Y,Z) --> product(Y::'a,X,Z)) &       \
\  (! X. sum(additive_identity::'a,X,X)) &  \
\  (! X. sum(X::'a,additive_identity,X)) &  \
\  (! X. product(multiplicative_identity::'a,X,X)) &        \
\  (! X. product(X::'a,multiplicative_identity,X)) &        \
\  (! Y Z X V3 V1 V2 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & product(X::'a,V3,V4) --> sum(V1::'a,V2,V4)) &        \
\  (! Y Z V1 V2 X V3 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(X::'a,V3,V4)) &        \
\  (! Y Z V3 X V1 V2 V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & product(V3::'a,X,V4) --> sum(V1::'a,V2,V4)) &        \
\  (! Y Z V1 V2 V3 X V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(V3::'a,X,V4)) &        \
\  (! Y Z X V3 V1 V2 V4. sum(X::'a,Y,V1) & sum(X::'a,Z,V2) & product(Y::'a,Z,V3) & sum(X::'a,V3,V4) --> product(V1::'a,V2,V4)) &    \
\  (! Y Z V1 V2 X V3 V4. sum(X::'a,Y,V1) & sum(X::'a,Z,V2) & product(Y::'a,Z,V3) & product(V1::'a,V2,V4) --> sum(X::'a,V3,V4)) &    \
\  (! Y Z V3 X V1 V2 V4. sum(Y::'a,X,V1) & sum(Z::'a,X,V2) & product(Y::'a,Z,V3) & sum(V3::'a,X,V4) --> product(V1::'a,V2,V4)) &    \
\  (! Y Z V1 V2 V3 X V4. sum(Y::'a,X,V1) & sum(Z::'a,X,V2) & product(Y::'a,Z,V3) & product(V1::'a,V2,V4) --> sum(V3::'a,X,V4)) &    \
\  (! X. sum(inverse(X),X,multiplicative_identity)) &   \
\  (! X. sum(X::'a,inverse(X),multiplicative_identity)) &   \
\  (! X. product(inverse(X),X,additive_identity)) &     \
\  (! X. product(X::'a,inverse(X),additive_identity)) &     \
\  (! X Y U V. sum(X::'a,Y,U) & sum(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (! X Y U V. product(X::'a,Y,U) & product(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (! X Y W Z. equal(X::'a,Y) & sum(X::'a,W,Z) --> sum(Y::'a,W,Z)) &        \
\  (! X W Y Z. equal(X::'a,Y) & sum(W::'a,X,Z) --> sum(W::'a,Y,Z)) &        \
\  (! X W Z Y. equal(X::'a,Y) & sum(W::'a,Z,X) --> sum(W::'a,Z,Y)) &        \
\  (! X Y W Z. equal(X::'a,Y) & product(X::'a,W,Z) --> product(Y::'a,W,Z)) &        \
\  (! X W Y Z. equal(X::'a,Y) & product(W::'a,X,Z) --> product(W::'a,Y,Z)) &        \
\  (! X W Z Y. equal(X::'a,Y) & product(W::'a,Z,X) --> product(W::'a,Z,Y)) &        \
\  (! X Y W. equal(X::'a,Y) --> equal(add(X::'a,W),add(Y::'a,W))) & \
\  (! X W Y. equal(X::'a,Y) --> equal(add(W::'a,X),add(W::'a,Y))) & \
\  (! X Y W. equal(X::'a,Y) --> equal(multiply(X::'a,W),multiply(Y::'a,W))) &       \
\  (! X W Y. equal(X::'a,Y) --> equal(multiply(W::'a,X),multiply(W::'a,Y))) &       \
\  (! X Y. equal(X::'a,Y) --> equal(inverse(X),inverse(Y))) &       \
\  (~product(x::'a,additive_identity,additive_identity)) --> False",
  meson_tac);

(*5 inferences so far.  Searching to depth 5.  1.3 secs*)
val BOO011_1 = prove
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X Y. sum(X::'a,Y,add(X::'a,Y))) & \
\  (! X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (! Y X Z. sum(X::'a,Y,Z) --> sum(Y::'a,X,Z)) &       \
\  (! Y X Z. product(X::'a,Y,Z) --> product(Y::'a,X,Z)) &       \
\  (! X. sum(additive_identity::'a,X,X)) &  \
\  (! X. sum(X::'a,additive_identity,X)) &  \
\  (! X. product(multiplicative_identity::'a,X,X)) &        \
\  (! X. product(X::'a,multiplicative_identity,X)) &        \
\  (! Y Z X V3 V1 V2 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & product(X::'a,V3,V4) --> sum(V1::'a,V2,V4)) &        \
\  (! Y Z V1 V2 X V3 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(X::'a,V3,V4)) &        \
\  (! Y Z V3 X V1 V2 V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & product(V3::'a,X,V4) --> sum(V1::'a,V2,V4)) &        \
\  (! Y Z V1 V2 V3 X V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(V3::'a,X,V4)) &        \
\  (! Y Z X V3 V1 V2 V4. sum(X::'a,Y,V1) & sum(X::'a,Z,V2) & product(Y::'a,Z,V3) & sum(X::'a,V3,V4) --> product(V1::'a,V2,V4)) &    \
\  (! Y Z V1 V2 X V3 V4. sum(X::'a,Y,V1) & sum(X::'a,Z,V2) & product(Y::'a,Z,V3) & product(V1::'a,V2,V4) --> sum(X::'a,V3,V4)) &    \
\  (! Y Z V3 X V1 V2 V4. sum(Y::'a,X,V1) & sum(Z::'a,X,V2) & product(Y::'a,Z,V3) & sum(V3::'a,X,V4) --> product(V1::'a,V2,V4)) &    \
\  (! Y Z V1 V2 V3 X V4. sum(Y::'a,X,V1) & sum(Z::'a,X,V2) & product(Y::'a,Z,V3) & product(V1::'a,V2,V4) --> sum(V3::'a,X,V4)) &    \
\  (! X. sum(inverse(X),X,multiplicative_identity)) &   \
\  (! X. sum(X::'a,inverse(X),multiplicative_identity)) &   \
\  (! X. product(inverse(X),X,additive_identity)) &     \
\  (! X. product(X::'a,inverse(X),additive_identity)) &     \
\  (! X Y U V. sum(X::'a,Y,U) & sum(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (! X Y U V. product(X::'a,Y,U) & product(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (! X Y W Z. equal(X::'a,Y) & sum(X::'a,W,Z) --> sum(Y::'a,W,Z)) &        \
\  (! X W Y Z. equal(X::'a,Y) & sum(W::'a,X,Z) --> sum(W::'a,Y,Z)) &        \
\  (! X W Z Y. equal(X::'a,Y) & sum(W::'a,Z,X) --> sum(W::'a,Z,Y)) &        \
\  (! X Y W Z. equal(X::'a,Y) & product(X::'a,W,Z) --> product(Y::'a,W,Z)) &        \
\  (! X W Y Z. equal(X::'a,Y) & product(W::'a,X,Z) --> product(W::'a,Y,Z)) &        \
\  (! X W Z Y. equal(X::'a,Y) & product(W::'a,Z,X) --> product(W::'a,Z,Y)) &        \
\  (! X Y W. equal(X::'a,Y) --> equal(add(X::'a,W),add(Y::'a,W))) & \
\  (! X W Y. equal(X::'a,Y) --> equal(add(W::'a,X),add(W::'a,Y))) & \
\  (! X Y W. equal(X::'a,Y) --> equal(multiply(X::'a,W),multiply(Y::'a,W))) &       \
\  (! X W Y. equal(X::'a,Y) --> equal(multiply(W::'a,X),multiply(W::'a,Y))) &       \
\  (! X Y. equal(X::'a,Y) --> equal(inverse(X),inverse(Y))) &       \
\  (~equal(inverse(additive_identity),multiplicative_identity)) --> False",
  meson_tac);

(*4007 inferences so far.  Searching to depth 9.  13 secs*)
val CAT001_3 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! Y X. equivalent(X::'a,Y) --> there_exists(X)) &       \
\  (! X Y. equivalent(X::'a,Y) --> equal(X::'a,Y)) &    \
\  (! X Y. there_exists(X) & equal(X::'a,Y) --> equivalent(X::'a,Y)) &  \
\  (! X. there_exists(domain(X)) --> there_exists(X)) & \
\  (! X. there_exists(codomain(X)) --> there_exists(X)) &       \
\  (! Y X. there_exists(compos(X::'a,Y)) --> there_exists(domain(X))) &    \
\  (! X Y. there_exists(compos(X::'a,Y)) --> equal(domain(X),codomain(Y))) &       \
\  (! X Y. there_exists(domain(X)) & equal(domain(X),codomain(Y)) --> there_exists(compos(X::'a,Y))) &     \
\  (! X Y Z. equal(compos(X::'a,compos(Y::'a,Z)),compos(compos(X::'a,Y),Z))) &  \
\  (! X. equal(compos(X::'a,domain(X)),X)) &       \
\  (! X. equal(compos(codomain(X),X),X)) &     \
\  (! X Y. equivalent(X::'a,Y) --> there_exists(Y)) &       \
\  (! X Y. there_exists(X) & there_exists(Y) & equal(X::'a,Y) --> equivalent(X::'a,Y)) &        \
\  (! Y X. there_exists(compos(X::'a,Y)) --> there_exists(codomain(X))) &  \
\  (! X Y. there_exists(f1(X::'a,Y)) | equal(X::'a,Y)) &       \
\  (! X Y. equal(X::'a,f1(X::'a,Y)) | equal(Y::'a,f1(X::'a,Y)) | equal(X::'a,Y)) &        \
\  (! X Y. equal(X::'a,f1(X::'a,Y)) & equal(Y::'a,f1(X::'a,Y)) --> equal(X::'a,Y)) &        \
\  (! X Y. equal(X::'a,Y) & there_exists(X) --> there_exists(Y)) &  \
\  (! X Y Z. equal(X::'a,Y) & equivalent(X::'a,Z) --> equivalent(Y::'a,Z)) &        \
\  (! X Z Y. equal(X::'a,Y) & equivalent(Z::'a,X) --> equivalent(Z::'a,Y)) &        \
\  (! X Y. equal(X::'a,Y) --> equal(domain(X),domain(Y))) & \
\  (! X Y. equal(X::'a,Y) --> equal(codomain(X),codomain(Y))) &     \
\  (! X Y Z. equal(X::'a,Y) --> equal(compos(X::'a,Z),compos(Y::'a,Z))) & \
\  (! X Z Y. equal(X::'a,Y) --> equal(compos(Z::'a,X),compos(Z::'a,Y))) & \
\  (! A B C. equal(A::'a,B) --> equal(f1(A::'a,C),f1(B::'a,C))) &   \
\  (! D F' E. equal(D::'a,E) --> equal(f1(F'::'a,D),f1(F'::'a,E))) &        \
\  (there_exists(compos(a::'a,b))) &       \
\  (! Y X Z. equal(compos(compos(a::'a,b),X),Y) & equal(compos(compos(a::'a,b),Z),Y) --> equal(X::'a,Z)) &      \
\  (there_exists(compos(b::'a,h))) &       \
\  (equal(compos(b::'a,h),compos(b::'a,g))) & \
\  (~equal(h::'a,g)) --> False",
  meson_tac);

(*245 inferences so far.  Searching to depth 7.  1.0 secs*)
val CAT003_3 = prove
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! Y X. equivalent(X::'a,Y) --> there_exists(X)) &       \
\  (! X Y. equivalent(X::'a,Y) --> equal(X::'a,Y)) &    \
\  (! X Y. there_exists(X) & equal(X::'a,Y) --> equivalent(X::'a,Y)) &  \
\  (! X. there_exists(domain(X)) --> there_exists(X)) & \
\  (! X. there_exists(codomain(X)) --> there_exists(X)) &       \
\  (! Y X. there_exists(compos(X::'a,Y)) --> there_exists(domain(X))) &    \
\  (! X Y. there_exists(compos(X::'a,Y)) --> equal(domain(X),codomain(Y))) &       \
\  (! X Y. there_exists(domain(X)) & equal(domain(X),codomain(Y)) --> there_exists(compos(X::'a,Y))) &     \
\  (! X Y Z. equal(compos(X::'a,compos(Y::'a,Z)),compos(compos(X::'a,Y),Z))) &  \
\  (! X. equal(compos(X::'a,domain(X)),X)) &       \
\  (! X. equal(compos(codomain(X),X),X)) &     \
\  (! X Y. equivalent(X::'a,Y) --> there_exists(Y)) &       \
\  (! X Y. there_exists(X) & there_exists(Y) & equal(X::'a,Y) --> equivalent(X::'a,Y)) &        \
\  (! Y X. there_exists(compos(X::'a,Y)) --> there_exists(codomain(X))) &  \
\  (! X Y. there_exists(f1(X::'a,Y)) | equal(X::'a,Y)) &       \
\  (! X Y. equal(X::'a,f1(X::'a,Y)) | equal(Y::'a,f1(X::'a,Y)) | equal(X::'a,Y)) &        \
\  (! X Y. equal(X::'a,f1(X::'a,Y)) & equal(Y::'a,f1(X::'a,Y)) --> equal(X::'a,Y)) &        \
\  (! X Y. equal(X::'a,Y) & there_exists(X) --> there_exists(Y)) &  \
\  (! X Y Z. equal(X::'a,Y) & equivalent(X::'a,Z) --> equivalent(Y::'a,Z)) &        \
\  (! X Z Y. equal(X::'a,Y) & equivalent(Z::'a,X) --> equivalent(Z::'a,Y)) &        \
\  (! X Y. equal(X::'a,Y) --> equal(domain(X),domain(Y))) & \
\  (! X Y. equal(X::'a,Y) --> equal(codomain(X),codomain(Y))) &     \
\  (! X Y Z. equal(X::'a,Y) --> equal(compos(X::'a,Z),compos(Y::'a,Z))) & \
\  (! X Z Y. equal(X::'a,Y) --> equal(compos(Z::'a,X),compos(Z::'a,Y))) & \
\  (! A B C. equal(A::'a,B) --> equal(f1(A::'a,C),f1(B::'a,C))) &   \
\  (! D F' E. equal(D::'a,E) --> equal(f1(F'::'a,D),f1(F'::'a,E))) &        \
\  (there_exists(compos(a::'a,b))) &       \
\  (! Y X Z. equal(compos(X::'a,compos(a::'a,b)),Y) & equal(compos(Z::'a,compos(a::'a,b)),Y) --> equal(X::'a,Z)) &      \
\  (there_exists(h)) &  \
\  (equal(compos(h::'a,a),compos(g::'a,a))) & \
\  (~equal(g::'a,h)) --> False",
  meson_tac);

(*54288 inferences so far.  Searching to depth 14.  118.0 secs*)
val CAT005_1 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X Y. defined(X::'a,Y) --> product(X::'a,Y,compos(X::'a,Y))) &        \
\  (! Z X Y. product(X::'a,Y,Z) --> defined(X::'a,Y)) & \
\  (! X Xy Y Z. product(X::'a,Y,Xy) & defined(Xy::'a,Z) --> defined(Y::'a,Z)) &     \
\  (! Y Xy Z X Yz. product(X::'a,Y,Xy) & product(Y::'a,Z,Yz) & defined(Xy::'a,Z) --> defined(X::'a,Yz)) &       \
\  (! Xy Y Z X Yz Xyz. product(X::'a,Y,Xy) & product(Xy::'a,Z,Xyz) & product(Y::'a,Z,Yz) --> product(X::'a,Yz,Xyz)) &   \
\  (! Z Yz X Y. product(Y::'a,Z,Yz) & defined(X::'a,Yz) --> defined(X::'a,Y)) &     \
\  (! Y X Yz Xy Z. product(Y::'a,Z,Yz) & product(X::'a,Y,Xy) & defined(X::'a,Yz) --> defined(Xy::'a,Z)) &       \
\  (! Yz X Y Xy Z Xyz. product(Y::'a,Z,Yz) & product(X::'a,Yz,Xyz) & product(X::'a,Y,Xy) --> product(Xy::'a,Z,Xyz)) &   \
\  (! Y X Z. defined(X::'a,Y) & defined(Y::'a,Z) & identity_map(Y) --> defined(X::'a,Z)) &  \
\  (! X. identity_map(domain(X))) &     \
\  (! X. identity_map(codomain(X))) &   \
\  (! X. defined(X::'a,domain(X))) &        \
\  (! X. defined(codomain(X),X)) &      \
\  (! X. product(X::'a,domain(X),X)) &      \
\  (! X. product(codomain(X),X,X)) &    \
\  (! X Y. defined(X::'a,Y) & identity_map(X) --> product(X::'a,Y,Y)) & \
\  (! Y X. defined(X::'a,Y) & identity_map(Y) --> product(X::'a,Y,X)) & \
\  (! X Y Z W. product(X::'a,Y,Z) & product(X::'a,Y,W) --> equal(Z::'a,W)) &        \
\  (! X Y Z W. equal(X::'a,Y) & product(X::'a,Z,W) --> product(Y::'a,Z,W)) &        \
\  (! X Z Y W. equal(X::'a,Y) & product(Z::'a,X,W) --> product(Z::'a,Y,W)) &        \
\  (! X Z W Y. equal(X::'a,Y) & product(Z::'a,W,X) --> product(Z::'a,W,Y)) &        \
\  (! X Y. equal(X::'a,Y) --> equal(domain(X),domain(Y))) & \
\  (! X Y. equal(X::'a,Y) --> equal(codomain(X),codomain(Y))) &     \
\  (! X Y. equal(X::'a,Y) & identity_map(X) --> identity_map(Y)) &  \
\  (! X Y Z. equal(X::'a,Y) & defined(X::'a,Z) --> defined(Y::'a,Z)) &      \
\  (! X Z Y. equal(X::'a,Y) & defined(Z::'a,X) --> defined(Z::'a,Y)) &      \
\  (! X Z Y. equal(X::'a,Y) --> equal(compos(Z::'a,X),compos(Z::'a,Y))) & \
\  (! X Y Z. equal(X::'a,Y) --> equal(compos(X::'a,Z),compos(Y::'a,Z))) & \
\  (defined(a::'a,d)) &     \
\  (identity_map(d)) &  \
\  (~equal(domain(a),d)) --> False",
  meson_tac);


(*1728 inferences so far.  Searching to depth 10.  5.8 secs*)
val CAT007_1 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X Y. defined(X::'a,Y) --> product(X::'a,Y,compos(X::'a,Y))) &        \
\  (! Z X Y. product(X::'a,Y,Z) --> defined(X::'a,Y)) & \
\  (! X Xy Y Z. product(X::'a,Y,Xy) & defined(Xy::'a,Z) --> defined(Y::'a,Z)) &     \
\  (! Y Xy Z X Yz. product(X::'a,Y,Xy) & product(Y::'a,Z,Yz) & defined(Xy::'a,Z) --> defined(X::'a,Yz)) &       \
\  (! Xy Y Z X Yz Xyz. product(X::'a,Y,Xy) & product(Xy::'a,Z,Xyz) & product(Y::'a,Z,Yz) --> product(X::'a,Yz,Xyz)) &   \
\  (! Z Yz X Y. product(Y::'a,Z,Yz) & defined(X::'a,Yz) --> defined(X::'a,Y)) &     \
\  (! Y X Yz Xy Z. product(Y::'a,Z,Yz) & product(X::'a,Y,Xy) & defined(X::'a,Yz) --> defined(Xy::'a,Z)) &       \
\  (! Yz X Y Xy Z Xyz. product(Y::'a,Z,Yz) & product(X::'a,Yz,Xyz) & product(X::'a,Y,Xy) --> product(Xy::'a,Z,Xyz)) &   \
\  (! Y X Z. defined(X::'a,Y) & defined(Y::'a,Z) & identity_map(Y) --> defined(X::'a,Z)) &  \
\  (! X. identity_map(domain(X))) &     \
\  (! X. identity_map(codomain(X))) &   \
\  (! X. defined(X::'a,domain(X))) &        \
\  (! X. defined(codomain(X),X)) &      \
\  (! X. product(X::'a,domain(X),X)) &      \
\  (! X. product(codomain(X),X,X)) &    \
\  (! X Y. defined(X::'a,Y) & identity_map(X) --> product(X::'a,Y,Y)) & \
\  (! Y X. defined(X::'a,Y) & identity_map(Y) --> product(X::'a,Y,X)) & \
\  (! X Y Z W. product(X::'a,Y,Z) & product(X::'a,Y,W) --> equal(Z::'a,W)) &        \
\  (! X Y Z W. equal(X::'a,Y) & product(X::'a,Z,W) --> product(Y::'a,Z,W)) &        \
\  (! X Z Y W. equal(X::'a,Y) & product(Z::'a,X,W) --> product(Z::'a,Y,W)) &        \
\  (! X Z W Y. equal(X::'a,Y) & product(Z::'a,W,X) --> product(Z::'a,W,Y)) &        \
\  (! X Y. equal(X::'a,Y) --> equal(domain(X),domain(Y))) & \
\  (! X Y. equal(X::'a,Y) --> equal(codomain(X),codomain(Y))) &     \
\  (! X Y. equal(X::'a,Y) & identity_map(X) --> identity_map(Y)) &  \
\  (! X Y Z. equal(X::'a,Y) & defined(X::'a,Z) --> defined(Y::'a,Z)) &      \
\  (! X Z Y. equal(X::'a,Y) & defined(Z::'a,X) --> defined(Z::'a,Y)) &      \
\  (! X Z Y. equal(X::'a,Y) --> equal(compos(Z::'a,X),compos(Z::'a,Y))) & \
\  (! X Y Z. equal(X::'a,Y) --> equal(compos(X::'a,Z),compos(Y::'a,Z))) & \
\  (equal(domain(a),codomain(b))) &     \
\  (~defined(a::'a,b)) --> False",
  meson_tac);

(*82895 inferences so far.  Searching to depth 13.  355 secs*)
val CAT018_1 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X Y. defined(X::'a,Y) --> product(X::'a,Y,compos(X::'a,Y))) &        \
\  (! Z X Y. product(X::'a,Y,Z) --> defined(X::'a,Y)) & \
\  (! X Xy Y Z. product(X::'a,Y,Xy) & defined(Xy::'a,Z) --> defined(Y::'a,Z)) &     \
\  (! Y Xy Z X Yz. product(X::'a,Y,Xy) & product(Y::'a,Z,Yz) & defined(Xy::'a,Z) --> defined(X::'a,Yz)) &       \
\  (! Xy Y Z X Yz Xyz. product(X::'a,Y,Xy) & product(Xy::'a,Z,Xyz) & product(Y::'a,Z,Yz) --> product(X::'a,Yz,Xyz)) &   \
\  (! Z Yz X Y. product(Y::'a,Z,Yz) & defined(X::'a,Yz) --> defined(X::'a,Y)) &     \
\  (! Y X Yz Xy Z. product(Y::'a,Z,Yz) & product(X::'a,Y,Xy) & defined(X::'a,Yz) --> defined(Xy::'a,Z)) &       \
\  (! Yz X Y Xy Z Xyz. product(Y::'a,Z,Yz) & product(X::'a,Yz,Xyz) & product(X::'a,Y,Xy) --> product(Xy::'a,Z,Xyz)) &   \
\  (! Y X Z. defined(X::'a,Y) & defined(Y::'a,Z) & identity_map(Y) --> defined(X::'a,Z)) &  \
\  (! X. identity_map(domain(X))) &     \
\  (! X. identity_map(codomain(X))) &   \
\  (! X. defined(X::'a,domain(X))) &        \
\  (! X. defined(codomain(X),X)) &      \
\  (! X. product(X::'a,domain(X),X)) &      \
\  (! X. product(codomain(X),X,X)) &    \
\  (! X Y. defined(X::'a,Y) & identity_map(X) --> product(X::'a,Y,Y)) & \
\  (! Y X. defined(X::'a,Y) & identity_map(Y) --> product(X::'a,Y,X)) & \
\  (! X Y Z W. product(X::'a,Y,Z) & product(X::'a,Y,W) --> equal(Z::'a,W)) &        \
\  (! X Y Z W. equal(X::'a,Y) & product(X::'a,Z,W) --> product(Y::'a,Z,W)) &        \
\  (! X Z Y W. equal(X::'a,Y) & product(Z::'a,X,W) --> product(Z::'a,Y,W)) &        \
\  (! X Z W Y. equal(X::'a,Y) & product(Z::'a,W,X) --> product(Z::'a,W,Y)) &        \
\  (! X Y. equal(X::'a,Y) --> equal(domain(X),domain(Y))) & \
\  (! X Y. equal(X::'a,Y) --> equal(codomain(X),codomain(Y))) &     \
\  (! X Y. equal(X::'a,Y) & identity_map(X) --> identity_map(Y)) &  \
\  (! X Y Z. equal(X::'a,Y) & defined(X::'a,Z) --> defined(Y::'a,Z)) &      \
\  (! X Z Y. equal(X::'a,Y) & defined(Z::'a,X) --> defined(Z::'a,Y)) &      \
\  (! X Z Y. equal(X::'a,Y) --> equal(compos(Z::'a,X),compos(Z::'a,Y))) & \
\  (! X Y Z. equal(X::'a,Y) --> equal(compos(X::'a,Z),compos(Y::'a,Z))) & \
\  (defined(a::'a,b)) &     \
\  (defined(b::'a,c)) &     \
\  (~defined(a::'a,compos(b::'a,c))) --> False",
  meson_tac);

(*1118 inferences so far.  Searching to depth 8.  2.3 secs*)
val COL001_2 = prove
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X Y Z. equal(apply(apply(apply(s::'a,X),Y),Z),apply(apply(X::'a,Z),apply(Y::'a,Z)))) &        \
\  (! Y X. equal(apply(apply(k::'a,X),Y),X)) &      \
\  (! X Y Z. equal(apply(apply(apply(b::'a,X),Y),Z),apply(X::'a,apply(Y::'a,Z)))) & \
\  (! X. equal(apply(i::'a,X),X)) & \
\  (! A B C. equal(A::'a,B) --> equal(apply(A::'a,C),apply(B::'a,C))) &     \
\  (! D F' E. equal(D::'a,E) --> equal(apply(F'::'a,D),apply(F'::'a,E))) &  \
\  (! X. equal(apply(apply(apply(s::'a,apply(b::'a,X)),i),apply(apply(s::'a,apply(b::'a,X)),i)),apply(x::'a,apply(apply(apply(s::'a,apply(b::'a,X)),i),apply(apply(s::'a,apply(b::'a,X)),i))))) &   \
\  (! Y. ~equal(Y::'a,apply(combinator::'a,Y))) --> False",
  meson_tac);

(*500 inferences so far.  Searching to depth 8.  0.9 secs*)
val COL023_1 = prove
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X Y Z. equal(apply(apply(apply(b::'a,X),Y),Z),apply(X::'a,apply(Y::'a,Z)))) & \
\  (! X Y Z. equal(apply(apply(apply(n::'a,X),Y),Z),apply(apply(apply(X::'a,Z),Y),Z))) &        \
\  (! A B C. equal(A::'a,B) --> equal(apply(A::'a,C),apply(B::'a,C))) &     \
\  (! D F' E. equal(D::'a,E) --> equal(apply(F'::'a,D),apply(F'::'a,E))) &  \
\  (! Y. ~equal(Y::'a,apply(combinator::'a,Y))) --> False",
  meson_tac);

(*3018 inferences so far.  Searching to depth 10.  4.3 secs*)
val COL032_1 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X. equal(apply(m::'a,X),apply(X::'a,X))) &        \
\  (! Y X Z. equal(apply(apply(apply(q::'a,X),Y),Z),apply(Y::'a,apply(X::'a,Z)))) & \
\  (! A B C. equal(A::'a,B) --> equal(apply(A::'a,C),apply(B::'a,C))) &     \
\  (! D F' E. equal(D::'a,E) --> equal(apply(F'::'a,D),apply(F'::'a,E))) &  \
\  (! G H. equal(G::'a,H) --> equal(f(G),f(H))) &   \
\  (! Y. ~equal(apply(Y::'a,f(Y)),apply(f(Y),apply(Y::'a,f(Y))))) --> False",
  meson_tac);

(*381878 inferences so far.  Searching to depth 13.  670.4 secs*)
val COL052_2 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X Y W. equal(response(compos(X::'a,Y),W),response(X::'a,response(Y::'a,W)))) &       \
\  (! X Y. agreeable(X) --> equal(response(X::'a,common_bird(Y)),response(Y::'a,common_bird(Y)))) &     \
\  (! Z X. equal(response(X::'a,Z),response(compatible(X),Z)) --> agreeable(X)) &   \
\  (! A B. equal(A::'a,B) --> equal(common_bird(A),common_bird(B))) &       \
\  (! C D. equal(C::'a,D) --> equal(compatible(C),compatible(D))) & \
\  (! Q R. equal(Q::'a,R) & agreeable(Q) --> agreeable(R)) &        \
\  (! A B C. equal(A::'a,B) --> equal(compos(A::'a,C),compos(B::'a,C))) & \
\  (! D F' E. equal(D::'a,E) --> equal(compos(F'::'a,D),compos(F'::'a,E))) &      \
\  (! G H I'. equal(G::'a,H) --> equal(response(G::'a,I'),response(H::'a,I'))) &    \
\  (! J L K'. equal(J::'a,K') --> equal(response(L::'a,J),response(L::'a,K'))) &    \
\  (agreeable(c)) &     \
\  (~agreeable(a)) &    \
\  (equal(c::'a,compos(a::'a,b))) --> False",
  meson_tac);

(*13201 inferences so far.  Searching to depth 11.  31.9 secs*)
val COL075_2 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! Y X. equal(apply(apply(k::'a,X),Y),X)) &      \
\  (! X Y Z. equal(apply(apply(apply(abstraction::'a,X),Y),Z),apply(apply(X::'a,apply(k::'a,Z)),apply(Y::'a,Z)))) &     \
\  (! D E F'. equal(D::'a,E) --> equal(apply(D::'a,F'),apply(E::'a,F'))) &  \
\  (! G I' H. equal(G::'a,H) --> equal(apply(I'::'a,G),apply(I'::'a,H))) &  \
\  (! A B. equal(A::'a,B) --> equal(b(A),b(B))) &   \
\  (! C D. equal(C::'a,D) --> equal(c(C),c(D))) &   \
\  (! Y. ~equal(apply(apply(Y::'a,b(Y)),c(Y)),apply(b(Y),b(Y)))) --> False",
  meson_tac);

(*33 inferences so far.  Searching to depth 7.  0.1 secs*)
val COM001_1 = prove
 ("(! Goal_state Start_state. follows(Goal_state::'a,Start_state) --> succeeds(Goal_state::'a,Start_state)) &   \
\  (! Goal_state Intermediate_state Start_state. succeeds(Goal_state::'a,Intermediate_state) & succeeds(Intermediate_state::'a,Start_state) --> succeeds(Goal_state::'a,Start_state)) &     \
\  (! Start_state Label Goal_state. has(Start_state::'a,goto(Label)) & labels(Label::'a,Goal_state) --> succeeds(Goal_state::'a,Start_state)) &     \
\  (! Start_state Condition Goal_state. has(Start_state::'a,ifthen(Condition::'a,Goal_state)) --> succeeds(Goal_state::'a,Start_state)) &   \
\  (labels(loop::'a,p3)) &  \
\  (has(p3::'a,ifthen(equal(register_j::'a,n),p4))) &   \
\  (has(p4::'a,goto(out))) &        \
\  (follows(p5::'a,p4)) &   \
\  (follows(p8::'a,p3)) &   \
\  (has(p8::'a,goto(loop))) &       \
\  (~succeeds(p3::'a,p3)) --> False",
  meson_tac);

(*533 inferences so far.  Searching to depth 13.  0.3 secs*)
val COM002_1 = prove
 ("(! Goal_state Start_state. follows(Goal_state::'a,Start_state) --> succeeds(Goal_state::'a,Start_state)) &   \
\  (! Goal_state Intermediate_state Start_state. succeeds(Goal_state::'a,Intermediate_state) & succeeds(Intermediate_state::'a,Start_state) --> succeeds(Goal_state::'a,Start_state)) &     \
\  (! Start_state Label Goal_state. has(Start_state::'a,goto(Label)) & labels(Label::'a,Goal_state) --> succeeds(Goal_state::'a,Start_state)) &     \
\  (! Start_state Condition Goal_state. has(Start_state::'a,ifthen(Condition::'a,Goal_state)) --> succeeds(Goal_state::'a,Start_state)) &   \
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
  meson_tac);

(*4821 inferences so far.  Searching to depth 14.  1.3 secs*)
val COM002_2 = prove
 ("(! Goal_state Start_state. ~(fails(Goal_state::'a,Start_state) & follows(Goal_state::'a,Start_state))) &     \
\  (! Goal_state Intermediate_state Start_state. fails(Goal_state::'a,Start_state) --> fails(Goal_state::'a,Intermediate_state) | fails(Intermediate_state::'a,Start_state)) &     \
\  (! Start_state Label Goal_state. ~(fails(Goal_state::'a,Start_state) & has(Start_state::'a,goto(Label)) & labels(Label::'a,Goal_state))) &       \
\  (! Start_state Condition Goal_state. ~(fails(Goal_state::'a,Start_state) & has(Start_state::'a,ifthen(Condition::'a,Goal_state)))) &     \
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
  meson_tac);

(*98 inferences so far.  Searching to depth 10.  1.1 secs*)
val COM003_2 = prove
 ("(! X Y Z. program_decides(X) & program(Y) --> decides(X::'a,Y,Z)) &      \
\  (! X. program_decides(X) | program(f2(X))) &        \
\  (! X. decides(X::'a,f2(X),f1(X)) --> program_decides(X)) &       \
\  (! X. program_program_decides(X) --> program(X)) &   \
\  (! X. program_program_decides(X) --> program_decides(X)) &   \
\  (! X. program(X) & program_decides(X) --> program_program_decides(X)) &      \
\  (! X. algorithm_program_decides(X) --> algorithm(X)) &       \
\  (! X. algorithm_program_decides(X) --> program_decides(X)) & \
\  (! X. algorithm(X) & program_decides(X) --> algorithm_program_decides(X)) &  \
\  (! Y X. program_halts2(X::'a,Y) --> program(X)) &        \
\  (! X Y. program_halts2(X::'a,Y) --> halts2(X::'a,Y)) &       \
\  (! X Y. program(X) & halts2(X::'a,Y) --> program_halts2(X::'a,Y)) &  \
\  (! W X Y Z. halts3_outputs(X::'a,Y,Z,W) --> halts3(X::'a,Y,Z)) &     \
\  (! Y Z X W. halts3_outputs(X::'a,Y,Z,W) --> outputs(X::'a,W)) &      \
\  (! Y Z X W. halts3(X::'a,Y,Z) & outputs(X::'a,W) --> halts3_outputs(X::'a,Y,Z,W)) &      \
\  (! Y X. program_not_halts2(X::'a,Y) --> program(X)) &    \
\  (! X Y. ~(program_not_halts2(X::'a,Y) & halts2(X::'a,Y))) &  \
\  (! X Y. program(X) --> program_not_halts2(X::'a,Y) | halts2(X::'a,Y)) &     \
\  (! W X Y. halts2_outputs(X::'a,Y,W) --> halts2(X::'a,Y)) &   \
\  (! Y X W. halts2_outputs(X::'a,Y,W) --> outputs(X::'a,W)) &  \
\  (! Y X W. halts2(X::'a,Y) & outputs(X::'a,W) --> halts2_outputs(X::'a,Y,W)) &    \
\  (! X W Y Z. program_halts2_halts3_outputs(X::'a,Y,Z,W) --> program_halts2(Y::'a,Z)) &        \
\  (! X Y Z W. program_halts2_halts3_outputs(X::'a,Y,Z,W) --> halts3_outputs(X::'a,Y,Z,W)) &    \
\  (! X Y Z W. program_halts2(Y::'a,Z) & halts3_outputs(X::'a,Y,Z,W) --> program_halts2_halts3_outputs(X::'a,Y,Z,W)) &      \
\  (! X W Y Z. program_not_halts2_halts3_outputs(X::'a,Y,Z,W) --> program_not_halts2(Y::'a,Z)) &        \
\  (! X Y Z W. program_not_halts2_halts3_outputs(X::'a,Y,Z,W) --> halts3_outputs(X::'a,Y,Z,W)) &        \
\  (! X Y Z W. program_not_halts2(Y::'a,Z) & halts3_outputs(X::'a,Y,Z,W) --> program_not_halts2_halts3_outputs(X::'a,Y,Z,W)) &      \
\  (! X W Y. program_halts2_halts2_outputs(X::'a,Y,W) --> program_halts2(Y::'a,Y)) &    \
\  (! X Y W. program_halts2_halts2_outputs(X::'a,Y,W) --> halts2_outputs(X::'a,Y,W)) &  \
\  (! X Y W. program_halts2(Y::'a,Y) & halts2_outputs(X::'a,Y,W) --> program_halts2_halts2_outputs(X::'a,Y,W)) &    \
\  (! X W Y. program_not_halts2_halts2_outputs(X::'a,Y,W) --> program_not_halts2(Y::'a,Y)) &    \
\  (! X Y W. program_not_halts2_halts2_outputs(X::'a,Y,W) --> halts2_outputs(X::'a,Y,W)) &      \
\  (! X Y W. program_not_halts2(Y::'a,Y) & halts2_outputs(X::'a,Y,W) --> program_not_halts2_halts2_outputs(X::'a,Y,W)) &    \
\  (! X. algorithm_program_decides(X) --> program_program_decides(c1)) &        \
\  (! W Y Z. program_program_decides(W) --> program_halts2_halts3_outputs(W::'a,Y,Z,good)) &        \
\  (! W Y Z. program_program_decides(W) --> program_not_halts2_halts3_outputs(W::'a,Y,Z,bad)) &     \
\  (! W. program(W) & program_halts2_halts3_outputs(W::'a,f3(W),f3(W),good) & program_not_halts2_halts3_outputs(W::'a,f3(W),f3(W),bad) --> program(c2)) &       \
\  (! W Y. program(W) & program_halts2_halts3_outputs(W::'a,f3(W),f3(W),good) & program_not_halts2_halts3_outputs(W::'a,f3(W),f3(W),bad) --> program_halts2_halts2_outputs(c2::'a,Y,good)) &        \
\  (! W Y. program(W) & program_halts2_halts3_outputs(W::'a,f3(W),f3(W),good) & program_not_halts2_halts3_outputs(W::'a,f3(W),f3(W),bad) --> program_not_halts2_halts2_outputs(c2::'a,Y,bad)) &     \
\  (! V. program(V) & program_halts2_halts2_outputs(V::'a,f4(V),good) & program_not_halts2_halts2_outputs(V::'a,f4(V),bad) --> program(c3)) &   \
\  (! V Y. program(V) & program_halts2_halts2_outputs(V::'a,f4(V),good) & program_not_halts2_halts2_outputs(V::'a,f4(V),bad) & program_halts2(Y::'a,Y) --> halts2(c3::'a,Y)) &  \
\  (! V Y. program(V) & program_halts2_halts2_outputs(V::'a,f4(V),good) & program_not_halts2_halts2_outputs(V::'a,f4(V),bad) --> program_not_halts2_halts2_outputs(c3::'a,Y,bad)) & \
\  (algorithm_program_decides(c4)) --> False",
  meson_tac);

(****************SLOW
2100398 inferences so far.  Searching to depth 12.  No proof after 30 mins.
val COM004_1 = prove
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! C D P Q X Y. failure_node(X::'a,or(C::'a,P)) & failure_node(Y::'a,or(D::'a,Q)) & contradictory(P::'a,Q) & siblings(X::'a,Y) --> failure_node(parent_of(X::'a,Y),or(C::'a,D))) &   \
\  (! X. contradictory(negate(X),X)) &  \
\  (! X. contradictory(X::'a,negate(X))) &  \
\  (! X. siblings(left_child_of(X),right_child_of(X))) &        \
\  (! D E. equal(D::'a,E) --> equal(left_child_of(D),left_child_of(E))) &   \
\  (! F' G. equal(F'::'a,G) --> equal(negate(F'),negate(G))) &      \
\  (! H I' J. equal(H::'a,I') --> equal(or(H::'a,J),or(I'::'a,J))) &        \
\  (! K' M L. equal(K'::'a,L) --> equal(or(M::'a,K'),or(M::'a,L))) &        \
\  (! N O_ P. equal(N::'a,O_) --> equal(parent_of(N::'a,P),parent_of(O_::'a,P))) &     \
\  (! Q S' R. equal(Q::'a,R) --> equal(parent_of(S'::'a,Q),parent_of(S'::'a,R))) &  \
\  (! T' U. equal(T'::'a,U) --> equal(right_child_of(T'),right_child_of(U))) &      \
\  (! V W X. equal(V::'a,W) & contradictory(V::'a,X) --> contradictory(W::'a,X)) &  \
\  (! Y A1 Z. equal(Y::'a,Z) & contradictory(A1::'a,Y) --> contradictory(A1::'a,Z)) &       \
\  (! B1 C1 D1. equal(B1::'a,C1) & failure_node(B1::'a,D1) --> failure_node(C1::'a,D1)) &   \
\  (! E1 G1 F1. equal(E1::'a,F1) & failure_node(G1::'a,E1) --> failure_node(G1::'a,F1)) &   \
\  (! H1 I1 J1. equal(H1::'a,I1) & siblings(H1::'a,J1) --> siblings(I1::'a,J1)) &   \
\  (! K1 M1 L1. equal(K1::'a,L1) & siblings(M1::'a,K1) --> siblings(M1::'a,L1)) &   \
\  (failure_node(n_left::'a,or(empty::'a,atom))) &      \
\  (failure_node(n_right::'a,or(empty::'a,negate(atom)))) &     \
\  (equal(n_left::'a,left_child_of(n))) &   \
\  (equal(n_right::'a,right_child_of(n))) & \
\  (! Z. ~failure_node(Z::'a,or(empty::'a,empty))) --> False",
  meson_tac);
****************)

(*179 inferences so far.  Searching to depth 7.  3.9 secs*)
val GEO003_1 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X Y. between(X::'a,Y,X) --> equal(X::'a,Y)) &     \
\  (! V X Y Z. between(X::'a,Y,V) & between(Y::'a,Z,V) --> between(X::'a,Y,Z)) &    \
\  (! Y X V Z. between(X::'a,Y,Z) & between(X::'a,Y,V) --> equal(X::'a,Y) | between(X::'a,Z,V) | between(X::'a,V,Z)) &    \
\  (! Y X. equidistant(X::'a,Y,Y,X)) &      \
\  (! Z X Y. equidistant(X::'a,Y,Z,Z) --> equal(X::'a,Y)) &     \
\  (! X Y Z V V2 W. equidistant(X::'a,Y,Z,V) & equidistant(X::'a,Y,V2,W) --> equidistant(Z::'a,V,V2,W)) &   \
\  (! W X Z V Y. between(X::'a,W,V) & between(Y::'a,V,Z) --> between(X::'a,outer_pasch(W::'a,X,Y,Z,V),Y)) &     \
\  (! W X Y Z V. between(X::'a,W,V) & between(Y::'a,V,Z) --> between(Z::'a,W,outer_pasch(W::'a,X,Y,Z,V))) &     \
\  (! W X Y Z V. between(X::'a,V,W) & between(Y::'a,V,Z) --> equal(X::'a,V) | between(X::'a,Z,euclid1(W::'a,X,Y,Z,V))) &   \
\  (! W X Y Z V. between(X::'a,V,W) & between(Y::'a,V,Z) --> equal(X::'a,V) | between(X::'a,Y,euclid2(W::'a,X,Y,Z,V))) &   \
\  (! W X Y Z V. between(X::'a,V,W) & between(Y::'a,V,Z) --> equal(X::'a,V) | between(euclid1(W::'a,X,Y,Z,V),W,euclid2(W::'a,X,Y,Z,V))) &  \
\  (! X1 Y1 X Y Z V Z1 V1. equidistant(X::'a,Y,X1,Y1) & equidistant(Y::'a,Z,Y1,Z1) & equidistant(X::'a,V,X1,V1) & equidistant(Y::'a,V,Y1,V1) & between(X::'a,Y,Z) & between(X1::'a,Y1,Z1) --> equal(X::'a,Y) | equidistant(Z::'a,V,Z1,V1)) &   \
\  (! X Y W V. between(X::'a,Y,extension(X::'a,Y,W,V))) &       \
\  (! X Y W V. equidistant(Y::'a,extension(X::'a,Y,W,V),W,V)) & \
\  (~between(lower_dimension_point_1::'a,lower_dimension_point_2,lower_dimension_point_3)) &        \
\  (~between(lower_dimension_point_2::'a,lower_dimension_point_3,lower_dimension_point_1)) &        \
\  (~between(lower_dimension_point_3::'a,lower_dimension_point_1,lower_dimension_point_2)) &        \
\  (! Z X Y W V. equidistant(X::'a,W,X,V) & equidistant(Y::'a,W,Y,V) & equidistant(Z::'a,W,Z,V) --> between(X::'a,Y,Z) | between(Y::'a,Z,X) | between(Z::'a,X,Y) | equal(W::'a,V)) &     \
\  (! X Y Z X1 Z1 V. equidistant(V::'a,X,V,X1) & equidistant(V::'a,Z,V,Z1) & between(V::'a,X,Z) & between(X::'a,Y,Z) --> equidistant(V::'a,Y,Z,continuous(X::'a,Y,Z,X1,Z1,V))) &        \
\  (! X Y Z X1 V Z1. equidistant(V::'a,X,V,X1) & equidistant(V::'a,Z,V,Z1) & between(V::'a,X,Z) & between(X::'a,Y,Z) --> between(X1::'a,continuous(X::'a,Y,Z,X1,Z1,V),Z1)) &    \
\  (! X Y W Z. equal(X::'a,Y) & between(X::'a,W,Z) --> between(Y::'a,W,Z)) &        \
\  (! X W Y Z. equal(X::'a,Y) & between(W::'a,X,Z) --> between(W::'a,Y,Z)) &        \
\  (! X W Z Y. equal(X::'a,Y) & between(W::'a,Z,X) --> between(W::'a,Z,Y)) &        \
\  (! X Y V W Z. equal(X::'a,Y) & equidistant(X::'a,V,W,Z) --> equidistant(Y::'a,V,W,Z)) &  \
\  (! X V Y W Z. equal(X::'a,Y) & equidistant(V::'a,X,W,Z) --> equidistant(V::'a,Y,W,Z)) &  \
\  (! X V W Y Z. equal(X::'a,Y) & equidistant(V::'a,W,X,Z) --> equidistant(V::'a,W,Y,Z)) &  \
\  (! X V W Z Y. equal(X::'a,Y) & equidistant(V::'a,W,Z,X) --> equidistant(V::'a,W,Z,Y)) &  \
\  (! X Y V1 V2 V3 V4. equal(X::'a,Y) --> equal(outer_pasch(X::'a,V1,V2,V3,V4),outer_pasch(Y::'a,V1,V2,V3,V4))) &   \
\  (! X V1 Y V2 V3 V4. equal(X::'a,Y) --> equal(outer_pasch(V1::'a,X,V2,V3,V4),outer_pasch(V1::'a,Y,V2,V3,V4))) &   \
\  (! X V1 V2 Y V3 V4. equal(X::'a,Y) --> equal(outer_pasch(V1::'a,V2,X,V3,V4),outer_pasch(V1::'a,V2,Y,V3,V4))) &   \
\  (! X V1 V2 V3 Y V4. equal(X::'a,Y) --> equal(outer_pasch(V1::'a,V2,V3,X,V4),outer_pasch(V1::'a,V2,V3,Y,V4))) &   \
\  (! X V1 V2 V3 V4 Y. equal(X::'a,Y) --> equal(outer_pasch(V1::'a,V2,V3,V4,X),outer_pasch(V1::'a,V2,V3,V4,Y))) &   \
\  (! A B C D E F'. equal(A::'a,B) --> equal(euclid1(A::'a,C,D,E,F'),euclid1(B::'a,C,D,E,F'))) &    \
\  (! G I' H J K' L. equal(G::'a,H) --> equal(euclid1(I'::'a,G,J,K',L),euclid1(I'::'a,H,J,K',L))) & \
\  (! M O_ P N Q R. equal(M::'a,N) --> equal(euclid1(O_::'a,P,M,Q,R),euclid1(O_::'a,P,N,Q,R))) &       \
\  (! S' U V W T' X. equal(S'::'a,T') --> equal(euclid1(U::'a,V,W,S',X),euclid1(U::'a,V,W,T',X))) & \
\  (! Y A1 B1 C1 D1 Z. equal(Y::'a,Z) --> equal(euclid1(A1::'a,B1,C1,D1,Y),euclid1(A1::'a,B1,C1,D1,Z))) &   \
\  (! E1 F1 G1 H1 I1 J1. equal(E1::'a,F1) --> equal(euclid2(E1::'a,G1,H1,I1,J1),euclid2(F1::'a,G1,H1,I1,J1))) &     \
\  (! K1 M1 L1 N1 O1 P1. equal(K1::'a,L1) --> equal(euclid2(M1::'a,K1,N1,O1,P1),euclid2(M1::'a,L1,N1,O1,P1))) &     \
\  (! Q1 S1 T1 R1 U1 V1. equal(Q1::'a,R1) --> equal(euclid2(S1::'a,T1,Q1,U1,V1),euclid2(S1::'a,T1,R1,U1,V1))) &     \
\  (! W1 Y1 Z1 A2 X1 B2. equal(W1::'a,X1) --> equal(euclid2(Y1::'a,Z1,A2,W1,B2),euclid2(Y1::'a,Z1,A2,X1,B2))) &     \
\  (! C2 E2 F2 G2 H2 D2. equal(C2::'a,D2) --> equal(euclid2(E2::'a,F2,G2,H2,C2),euclid2(E2::'a,F2,G2,H2,D2))) &     \
\  (! X Y V1 V2 V3. equal(X::'a,Y) --> equal(extension(X::'a,V1,V2,V3),extension(Y::'a,V1,V2,V3))) &        \
\  (! X V1 Y V2 V3. equal(X::'a,Y) --> equal(extension(V1::'a,X,V2,V3),extension(V1::'a,Y,V2,V3))) &        \
\  (! X V1 V2 Y V3. equal(X::'a,Y) --> equal(extension(V1::'a,V2,X,V3),extension(V1::'a,V2,Y,V3))) &        \
\  (! X V1 V2 V3 Y. equal(X::'a,Y) --> equal(extension(V1::'a,V2,V3,X),extension(V1::'a,V2,V3,Y))) &        \
\  (! X Y V1 V2 V3 V4 V5. equal(X::'a,Y) --> equal(continuous(X::'a,V1,V2,V3,V4,V5),continuous(Y::'a,V1,V2,V3,V4,V5))) &    \
\  (! X V1 Y V2 V3 V4 V5. equal(X::'a,Y) --> equal(continuous(V1::'a,X,V2,V3,V4,V5),continuous(V1::'a,Y,V2,V3,V4,V5))) &    \
\  (! X V1 V2 Y V3 V4 V5. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,X,V3,V4,V5),continuous(V1::'a,V2,Y,V3,V4,V5))) &    \
\  (! X V1 V2 V3 Y V4 V5. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,V3,X,V4,V5),continuous(V1::'a,V2,V3,Y,V4,V5))) &    \
\  (! X V1 V2 V3 V4 Y V5. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,V3,V4,X,V5),continuous(V1::'a,V2,V3,V4,Y,V5))) &    \
\  (! X V1 V2 V3 V4 V5 Y. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,V3,V4,V5,X),continuous(V1::'a,V2,V3,V4,V5,Y))) &    \
\  (~between(a::'a,b,b)) --> False",
  meson_tac);

(*4272 inferences so far.  Searching to depth 10.  29.4 secs*)
val GEO017_2 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! Y X. equidistant(X::'a,Y,Y,X)) &      \
\  (! X Y Z V V2 W. equidistant(X::'a,Y,Z,V) & equidistant(X::'a,Y,V2,W) --> equidistant(Z::'a,V,V2,W)) &   \
\  (! Z X Y. equidistant(X::'a,Y,Z,Z) --> equal(X::'a,Y)) &     \
\  (! X Y W V. between(X::'a,Y,extension(X::'a,Y,W,V))) &       \
\  (! X Y W V. equidistant(Y::'a,extension(X::'a,Y,W,V),W,V)) & \
\  (! X1 Y1 X Y Z V Z1 V1. equidistant(X::'a,Y,X1,Y1) & equidistant(Y::'a,Z,Y1,Z1) & equidistant(X::'a,V,X1,V1) & equidistant(Y::'a,V,Y1,V1) & between(X::'a,Y,Z) & between(X1::'a,Y1,Z1) --> equal(X::'a,Y) | equidistant(Z::'a,V,Z1,V1)) &   \
\  (! X Y. between(X::'a,Y,X) --> equal(X::'a,Y)) &     \
\  (! U V W X Y. between(U::'a,V,W) & between(Y::'a,X,W) --> between(V::'a,inner_pasch(U::'a,V,W,X,Y),Y)) &     \
\  (! V W X Y U. between(U::'a,V,W) & between(Y::'a,X,W) --> between(X::'a,inner_pasch(U::'a,V,W,X,Y),U)) &     \
\  (~between(lower_dimension_point_1::'a,lower_dimension_point_2,lower_dimension_point_3)) &        \
\  (~between(lower_dimension_point_2::'a,lower_dimension_point_3,lower_dimension_point_1)) &        \
\  (~between(lower_dimension_point_3::'a,lower_dimension_point_1,lower_dimension_point_2)) &        \
\  (! Z X Y W V. equidistant(X::'a,W,X,V) & equidistant(Y::'a,W,Y,V) & equidistant(Z::'a,W,Z,V) --> between(X::'a,Y,Z) | between(Y::'a,Z,X) | between(Z::'a,X,Y) | equal(W::'a,V)) &     \
\  (! U V W X Y. between(U::'a,W,Y) & between(V::'a,W,X) --> equal(U::'a,W) | between(U::'a,V,euclid1(U::'a,V,W,X,Y))) &   \
\  (! U V W X Y. between(U::'a,W,Y) & between(V::'a,W,X) --> equal(U::'a,W) | between(U::'a,X,euclid2(U::'a,V,W,X,Y))) &   \
\  (! U V W X Y. between(U::'a,W,Y) & between(V::'a,W,X) --> equal(U::'a,W) | between(euclid1(U::'a,V,W,X,Y),Y,euclid2(U::'a,V,W,X,Y))) &  \
\  (! U V V1 W X X1. equidistant(U::'a,V,U,V1) & equidistant(U::'a,X,U,X1) & between(U::'a,V,X) & between(V::'a,W,X) --> between(V1::'a,continuous(U::'a,V,V1,W,X,X1),X1)) &    \
\  (! U V V1 W X X1. equidistant(U::'a,V,U,V1) & equidistant(U::'a,X,U,X1) & between(U::'a,V,X) & between(V::'a,W,X) --> equidistant(U::'a,W,U,continuous(U::'a,V,V1,W,X,X1))) &        \
\  (! X Y W Z. equal(X::'a,Y) & between(X::'a,W,Z) --> between(Y::'a,W,Z)) &        \
\  (! X W Y Z. equal(X::'a,Y) & between(W::'a,X,Z) --> between(W::'a,Y,Z)) &        \
\  (! X W Z Y. equal(X::'a,Y) & between(W::'a,Z,X) --> between(W::'a,Z,Y)) &        \
\  (! X Y V W Z. equal(X::'a,Y) & equidistant(X::'a,V,W,Z) --> equidistant(Y::'a,V,W,Z)) &  \
\  (! X V Y W Z. equal(X::'a,Y) & equidistant(V::'a,X,W,Z) --> equidistant(V::'a,Y,W,Z)) &  \
\  (! X V W Y Z. equal(X::'a,Y) & equidistant(V::'a,W,X,Z) --> equidistant(V::'a,W,Y,Z)) &  \
\  (! X V W Z Y. equal(X::'a,Y) & equidistant(V::'a,W,Z,X) --> equidistant(V::'a,W,Z,Y)) &  \
\  (! X Y V1 V2 V3 V4. equal(X::'a,Y) --> equal(inner_pasch(X::'a,V1,V2,V3,V4),inner_pasch(Y::'a,V1,V2,V3,V4))) &   \
\  (! X V1 Y V2 V3 V4. equal(X::'a,Y) --> equal(inner_pasch(V1::'a,X,V2,V3,V4),inner_pasch(V1::'a,Y,V2,V3,V4))) &   \
\  (! X V1 V2 Y V3 V4. equal(X::'a,Y) --> equal(inner_pasch(V1::'a,V2,X,V3,V4),inner_pasch(V1::'a,V2,Y,V3,V4))) &   \
\  (! X V1 V2 V3 Y V4. equal(X::'a,Y) --> equal(inner_pasch(V1::'a,V2,V3,X,V4),inner_pasch(V1::'a,V2,V3,Y,V4))) &   \
\  (! X V1 V2 V3 V4 Y. equal(X::'a,Y) --> equal(inner_pasch(V1::'a,V2,V3,V4,X),inner_pasch(V1::'a,V2,V3,V4,Y))) &   \
\  (! A B C D E F'. equal(A::'a,B) --> equal(euclid1(A::'a,C,D,E,F'),euclid1(B::'a,C,D,E,F'))) &    \
\  (! G I' H J K' L. equal(G::'a,H) --> equal(euclid1(I'::'a,G,J,K',L),euclid1(I'::'a,H,J,K',L))) & \
\  (! M O_ P N Q R. equal(M::'a,N) --> equal(euclid1(O_::'a,P,M,Q,R),euclid1(O_::'a,P,N,Q,R))) &       \
\  (! S' U V W T' X. equal(S'::'a,T') --> equal(euclid1(U::'a,V,W,S',X),euclid1(U::'a,V,W,T',X))) & \
\  (! Y A1 B1 C1 D1 Z. equal(Y::'a,Z) --> equal(euclid1(A1::'a,B1,C1,D1,Y),euclid1(A1::'a,B1,C1,D1,Z))) &   \
\  (! E1 F1 G1 H1 I1 J1. equal(E1::'a,F1) --> equal(euclid2(E1::'a,G1,H1,I1,J1),euclid2(F1::'a,G1,H1,I1,J1))) &     \
\  (! K1 M1 L1 N1 O1 P1. equal(K1::'a,L1) --> equal(euclid2(M1::'a,K1,N1,O1,P1),euclid2(M1::'a,L1,N1,O1,P1))) &     \
\  (! Q1 S1 T1 R1 U1 V1. equal(Q1::'a,R1) --> equal(euclid2(S1::'a,T1,Q1,U1,V1),euclid2(S1::'a,T1,R1,U1,V1))) &     \
\  (! W1 Y1 Z1 A2 X1 B2. equal(W1::'a,X1) --> equal(euclid2(Y1::'a,Z1,A2,W1,B2),euclid2(Y1::'a,Z1,A2,X1,B2))) &     \
\  (! C2 E2 F2 G2 H2 D2. equal(C2::'a,D2) --> equal(euclid2(E2::'a,F2,G2,H2,C2),euclid2(E2::'a,F2,G2,H2,D2))) &     \
\  (! X Y V1 V2 V3. equal(X::'a,Y) --> equal(extension(X::'a,V1,V2,V3),extension(Y::'a,V1,V2,V3))) &        \
\  (! X V1 Y V2 V3. equal(X::'a,Y) --> equal(extension(V1::'a,X,V2,V3),extension(V1::'a,Y,V2,V3))) &        \
\  (! X V1 V2 Y V3. equal(X::'a,Y) --> equal(extension(V1::'a,V2,X,V3),extension(V1::'a,V2,Y,V3))) &        \
\  (! X V1 V2 V3 Y. equal(X::'a,Y) --> equal(extension(V1::'a,V2,V3,X),extension(V1::'a,V2,V3,Y))) &        \
\  (! X Y V1 V2 V3 V4 V5. equal(X::'a,Y) --> equal(continuous(X::'a,V1,V2,V3,V4,V5),continuous(Y::'a,V1,V2,V3,V4,V5))) &    \
\  (! X V1 Y V2 V3 V4 V5. equal(X::'a,Y) --> equal(continuous(V1::'a,X,V2,V3,V4,V5),continuous(V1::'a,Y,V2,V3,V4,V5))) &    \
\  (! X V1 V2 Y V3 V4 V5. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,X,V3,V4,V5),continuous(V1::'a,V2,Y,V3,V4,V5))) &    \
\  (! X V1 V2 V3 Y V4 V5. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,V3,X,V4,V5),continuous(V1::'a,V2,V3,Y,V4,V5))) &    \
\  (! X V1 V2 V3 V4 Y V5. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,V3,V4,X,V5),continuous(V1::'a,V2,V3,V4,Y,V5))) &    \
\  (! X V1 V2 V3 V4 V5 Y. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,V3,V4,V5,X),continuous(V1::'a,V2,V3,V4,V5,Y))) &    \
\  (equidistant(u::'a,v,w,x)) &     \
\  (~equidistant(u::'a,v,x,w)) --> False",
  meson_tac);

(****************SLOW
382903 inferences so far.  Searching to depth 9.  No proof after 35 minutes.
val GEO027_3 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! Y X. equidistant(X::'a,Y,Y,X)) &      \
\  (! X Y Z V V2 W. equidistant(X::'a,Y,Z,V) & equidistant(X::'a,Y,V2,W) --> equidistant(Z::'a,V,V2,W)) &   \
\  (! Z X Y. equidistant(X::'a,Y,Z,Z) --> equal(X::'a,Y)) &     \
\  (! X Y W V. between(X::'a,Y,extension(X::'a,Y,W,V))) &       \
\  (! X Y W V. equidistant(Y::'a,extension(X::'a,Y,W,V),W,V)) & \
\  (! X1 Y1 X Y Z V Z1 V1. equidistant(X::'a,Y,X1,Y1) & equidistant(Y::'a,Z,Y1,Z1) & equidistant(X::'a,V,X1,V1) & equidistant(Y::'a,V,Y1,V1) & between(X::'a,Y,Z) & between(X1::'a,Y1,Z1) --> equal(X::'a,Y) | equidistant(Z::'a,V,Z1,V1)) &   \
\  (! X Y. between(X::'a,Y,X) --> equal(X::'a,Y)) &     \
\  (! U V W X Y. between(U::'a,V,W) & between(Y::'a,X,W) --> between(V::'a,inner_pasch(U::'a,V,W,X,Y),Y)) &     \
\  (! V W X Y U. between(U::'a,V,W) & between(Y::'a,X,W) --> between(X::'a,inner_pasch(U::'a,V,W,X,Y),U)) &     \
\  (~between(lower_dimension_point_1::'a,lower_dimension_point_2,lower_dimension_point_3)) &        \
\  (~between(lower_dimension_point_2::'a,lower_dimension_point_3,lower_dimension_point_1)) &        \
\  (~between(lower_dimension_point_3::'a,lower_dimension_point_1,lower_dimension_point_2)) &        \
\  (! Z X Y W V. equidistant(X::'a,W,X,V) & equidistant(Y::'a,W,Y,V) & equidistant(Z::'a,W,Z,V) --> between(X::'a,Y,Z) | between(Y::'a,Z,X) | between(Z::'a,X,Y) | equal(W::'a,V)) &     \
\  (! U V W X Y. between(U::'a,W,Y) & between(V::'a,W,X) --> equal(U::'a,W) | between(U::'a,V,euclid1(U::'a,V,W,X,Y))) &   \
\  (! U V W X Y. between(U::'a,W,Y) & between(V::'a,W,X) --> equal(U::'a,W) | between(U::'a,X,euclid2(U::'a,V,W,X,Y))) &   \
\  (! U V W X Y. between(U::'a,W,Y) & between(V::'a,W,X) --> equal(U::'a,W) | between(euclid1(U::'a,V,W,X,Y),Y,euclid2(U::'a,V,W,X,Y))) &  \
\  (! U V V1 W X X1. equidistant(U::'a,V,U,V1) & equidistant(U::'a,X,U,X1) & between(U::'a,V,X) & between(V::'a,W,X) --> between(V1::'a,continuous(U::'a,V,V1,W,X,X1),X1)) &    \
\  (! U V V1 W X X1. equidistant(U::'a,V,U,V1) & equidistant(U::'a,X,U,X1) & between(U::'a,V,X) & between(V::'a,W,X) --> equidistant(U::'a,W,U,continuous(U::'a,V,V1,W,X,X1))) &        \
\  (! X Y W Z. equal(X::'a,Y) & between(X::'a,W,Z) --> between(Y::'a,W,Z)) &        \
\  (! X W Y Z. equal(X::'a,Y) & between(W::'a,X,Z) --> between(W::'a,Y,Z)) &        \
\  (! X W Z Y. equal(X::'a,Y) & between(W::'a,Z,X) --> between(W::'a,Z,Y)) &        \
\  (! X Y V W Z. equal(X::'a,Y) & equidistant(X::'a,V,W,Z) --> equidistant(Y::'a,V,W,Z)) &  \
\  (! X V Y W Z. equal(X::'a,Y) & equidistant(V::'a,X,W,Z) --> equidistant(V::'a,Y,W,Z)) &  \
\  (! X V W Y Z. equal(X::'a,Y) & equidistant(V::'a,W,X,Z) --> equidistant(V::'a,W,Y,Z)) &  \
\  (! X V W Z Y. equal(X::'a,Y) & equidistant(V::'a,W,Z,X) --> equidistant(V::'a,W,Z,Y)) &  \
\  (! X Y V1 V2 V3 V4. equal(X::'a,Y) --> equal(inner_pasch(X::'a,V1,V2,V3,V4),inner_pasch(Y::'a,V1,V2,V3,V4))) &   \
\  (! X V1 Y V2 V3 V4. equal(X::'a,Y) --> equal(inner_pasch(V1::'a,X,V2,V3,V4),inner_pasch(V1::'a,Y,V2,V3,V4))) &   \
\  (! X V1 V2 Y V3 V4. equal(X::'a,Y) --> equal(inner_pasch(V1::'a,V2,X,V3,V4),inner_pasch(V1::'a,V2,Y,V3,V4))) &   \
\  (! X V1 V2 V3 Y V4. equal(X::'a,Y) --> equal(inner_pasch(V1::'a,V2,V3,X,V4),inner_pasch(V1::'a,V2,V3,Y,V4))) &   \
\  (! X V1 V2 V3 V4 Y. equal(X::'a,Y) --> equal(inner_pasch(V1::'a,V2,V3,V4,X),inner_pasch(V1::'a,V2,V3,V4,Y))) &   \
\  (! A B C D E F'. equal(A::'a,B) --> equal(euclid1(A::'a,C,D,E,F'),euclid1(B::'a,C,D,E,F'))) &    \
\  (! G I' H J K' L. equal(G::'a,H) --> equal(euclid1(I'::'a,G,J,K',L),euclid1(I'::'a,H,J,K',L))) & \
\  (! M O_ P N Q R. equal(M::'a,N) --> equal(euclid1(O_::'a,P,M,Q,R),euclid1(O_::'a,P,N,Q,R))) &       \
\  (! S' U V W T' X. equal(S'::'a,T') --> equal(euclid1(U::'a,V,W,S',X),euclid1(U::'a,V,W,T',X))) & \
\  (! Y A1 B1 C1 D1 Z. equal(Y::'a,Z) --> equal(euclid1(A1::'a,B1,C1,D1,Y),euclid1(A1::'a,B1,C1,D1,Z))) &   \
\  (! E1 F1 G1 H1 I1 J1. equal(E1::'a,F1) --> equal(euclid2(E1::'a,G1,H1,I1,J1),euclid2(F1::'a,G1,H1,I1,J1))) &     \
\  (! K1 M1 L1 N1 O1 P1. equal(K1::'a,L1) --> equal(euclid2(M1::'a,K1,N1,O1,P1),euclid2(M1::'a,L1,N1,O1,P1))) &     \
\  (! Q1 S1 T1 R1 U1 V1. equal(Q1::'a,R1) --> equal(euclid2(S1::'a,T1,Q1,U1,V1),euclid2(S1::'a,T1,R1,U1,V1))) &     \
\  (! W1 Y1 Z1 A2 X1 B2. equal(W1::'a,X1) --> equal(euclid2(Y1::'a,Z1,A2,W1,B2),euclid2(Y1::'a,Z1,A2,X1,B2))) &     \
\  (! C2 E2 F2 G2 H2 D2. equal(C2::'a,D2) --> equal(euclid2(E2::'a,F2,G2,H2,C2),euclid2(E2::'a,F2,G2,H2,D2))) &     \
\  (! X Y V1 V2 V3. equal(X::'a,Y) --> equal(extension(X::'a,V1,V2,V3),extension(Y::'a,V1,V2,V3))) &        \
\  (! X V1 Y V2 V3. equal(X::'a,Y) --> equal(extension(V1::'a,X,V2,V3),extension(V1::'a,Y,V2,V3))) &        \
\  (! X V1 V2 Y V3. equal(X::'a,Y) --> equal(extension(V1::'a,V2,X,V3),extension(V1::'a,V2,Y,V3))) &        \
\  (! X V1 V2 V3 Y. equal(X::'a,Y) --> equal(extension(V1::'a,V2,V3,X),extension(V1::'a,V2,V3,Y))) &        \
\  (! X Y V1 V2 V3 V4 V5. equal(X::'a,Y) --> equal(continuous(X::'a,V1,V2,V3,V4,V5),continuous(Y::'a,V1,V2,V3,V4,V5))) &    \
\  (! X V1 Y V2 V3 V4 V5. equal(X::'a,Y) --> equal(continuous(V1::'a,X,V2,V3,V4,V5),continuous(V1::'a,Y,V2,V3,V4,V5))) &    \
\  (! X V1 V2 Y V3 V4 V5. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,X,V3,V4,V5),continuous(V1::'a,V2,Y,V3,V4,V5))) &    \
\  (! X V1 V2 V3 Y V4 V5. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,V3,X,V4,V5),continuous(V1::'a,V2,V3,Y,V4,V5))) &    \
\  (! X V1 V2 V3 V4 Y V5. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,V3,V4,X,V5),continuous(V1::'a,V2,V3,V4,Y,V5))) &    \
\  (! X V1 V2 V3 V4 V5 Y. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,V3,V4,V5,X),continuous(V1::'a,V2,V3,V4,V5,Y))) &    \
\  (! U V. equal(reflection(U::'a,V),extension(U::'a,V,U,V))) & \
\  (! X Y Z. equal(X::'a,Y) --> equal(reflection(X::'a,Z),reflection(Y::'a,Z))) &   \
\  (! A1 C1 B1. equal(A1::'a,B1) --> equal(reflection(C1::'a,A1),reflection(C1::'a,B1))) &  \
\  (! U V. equidistant(U::'a,V,U,V)) &      \
\  (! W X U V. equidistant(U::'a,V,W,X) --> equidistant(W::'a,X,U,V)) & \
\  (! V U W X. equidistant(U::'a,V,W,X) --> equidistant(V::'a,U,W,X)) & \
\  (! U V X W. equidistant(U::'a,V,W,X) --> equidistant(U::'a,V,X,W)) & \
\  (! V U X W. equidistant(U::'a,V,W,X) --> equidistant(V::'a,U,X,W)) & \
\  (! W X V U. equidistant(U::'a,V,W,X) --> equidistant(W::'a,X,V,U)) & \
\  (! X W U V. equidistant(U::'a,V,W,X) --> equidistant(X::'a,W,U,V)) & \
\  (! X W V U. equidistant(U::'a,V,W,X) --> equidistant(X::'a,W,V,U)) & \
\  (! W X U V Y Z. equidistant(U::'a,V,W,X) & equidistant(W::'a,X,Y,Z) --> equidistant(U::'a,V,Y,Z)) &      \
\  (! U V W. equal(V::'a,extension(U::'a,V,W,W))) &     \
\  (! W X U V Y. equal(Y::'a,extension(U::'a,V,W,X)) --> between(U::'a,V,Y)) &      \
\  (! U V. between(U::'a,V,reflection(U::'a,V))) &      \
\  (! U V. equidistant(V::'a,reflection(U::'a,V),U,V)) &        \
\  (! U V. equal(U::'a,V) --> equal(V::'a,reflection(U::'a,V))) &   \
\  (! U. equal(U::'a,reflection(U::'a,U))) &    \
\  (! U V. equal(V::'a,reflection(U::'a,V)) --> equal(U::'a,V)) &   \
\  (! U V. equidistant(U::'a,U,V,V)) &      \
\  (! V V1 U W U1 W1. equidistant(U::'a,V,U1,V1) & equidistant(V::'a,W,V1,W1) & between(U::'a,V,W) & between(U1::'a,V1,W1) --> equidistant(U::'a,W,U1,W1)) &        \
\  (! U V W X. between(U::'a,V,W) & between(U::'a,V,X) & equidistant(V::'a,W,V,X) --> equal(U::'a,V) | equal(W::'a,X)) &   \
\  (between(u::'a,v,w)) &   \
\  (~equal(u::'a,v)) &      \
\  (~equal(w::'a,extension(u::'a,v,v,w))) --> False",
  meson_tac);
****************)

(*313884 inferences so far.  Searching to depth 10.  887 secs: 15 mins.*)
val GEO058_2 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! Y X. equidistant(X::'a,Y,Y,X)) &      \
\  (! X Y Z V V2 W. equidistant(X::'a,Y,Z,V) & equidistant(X::'a,Y,V2,W) --> equidistant(Z::'a,V,V2,W)) &   \
\  (! Z X Y. equidistant(X::'a,Y,Z,Z) --> equal(X::'a,Y)) &     \
\  (! X Y W V. between(X::'a,Y,extension(X::'a,Y,W,V))) &       \
\  (! X Y W V. equidistant(Y::'a,extension(X::'a,Y,W,V),W,V)) & \
\  (! X1 Y1 X Y Z V Z1 V1. equidistant(X::'a,Y,X1,Y1) & equidistant(Y::'a,Z,Y1,Z1) & equidistant(X::'a,V,X1,V1) & equidistant(Y::'a,V,Y1,V1) & between(X::'a,Y,Z) & between(X1::'a,Y1,Z1) --> equal(X::'a,Y) | equidistant(Z::'a,V,Z1,V1)) &   \
\  (! X Y. between(X::'a,Y,X) --> equal(X::'a,Y)) &     \
\  (! U V W X Y. between(U::'a,V,W) & between(Y::'a,X,W) --> between(V::'a,inner_pasch(U::'a,V,W,X,Y),Y)) &     \
\  (! V W X Y U. between(U::'a,V,W) & between(Y::'a,X,W) --> between(X::'a,inner_pasch(U::'a,V,W,X,Y),U)) &     \
\  (~between(lower_dimension_point_1::'a,lower_dimension_point_2,lower_dimension_point_3)) &        \
\  (~between(lower_dimension_point_2::'a,lower_dimension_point_3,lower_dimension_point_1)) &        \
\  (~between(lower_dimension_point_3::'a,lower_dimension_point_1,lower_dimension_point_2)) &        \
\  (! Z X Y W V. equidistant(X::'a,W,X,V) & equidistant(Y::'a,W,Y,V) & equidistant(Z::'a,W,Z,V) --> between(X::'a,Y,Z) | between(Y::'a,Z,X) | between(Z::'a,X,Y) | equal(W::'a,V)) &     \
\  (! U V W X Y. between(U::'a,W,Y) & between(V::'a,W,X) --> equal(U::'a,W) | between(U::'a,V,euclid1(U::'a,V,W,X,Y))) &   \
\  (! U V W X Y. between(U::'a,W,Y) & between(V::'a,W,X) --> equal(U::'a,W) | between(U::'a,X,euclid2(U::'a,V,W,X,Y))) &   \
\  (! U V W X Y. between(U::'a,W,Y) & between(V::'a,W,X) --> equal(U::'a,W) | between(euclid1(U::'a,V,W,X,Y),Y,euclid2(U::'a,V,W,X,Y))) &  \
\  (! U V V1 W X X1. equidistant(U::'a,V,U,V1) & equidistant(U::'a,X,U,X1) & between(U::'a,V,X) & between(V::'a,W,X) --> between(V1::'a,continuous(U::'a,V,V1,W,X,X1),X1)) &    \
\  (! U V V1 W X X1. equidistant(U::'a,V,U,V1) & equidistant(U::'a,X,U,X1) & between(U::'a,V,X) & between(V::'a,W,X) --> equidistant(U::'a,W,U,continuous(U::'a,V,V1,W,X,X1))) &        \
\  (! X Y W Z. equal(X::'a,Y) & between(X::'a,W,Z) --> between(Y::'a,W,Z)) &        \
\  (! X W Y Z. equal(X::'a,Y) & between(W::'a,X,Z) --> between(W::'a,Y,Z)) &        \
\  (! X W Z Y. equal(X::'a,Y) & between(W::'a,Z,X) --> between(W::'a,Z,Y)) &        \
\  (! X Y V W Z. equal(X::'a,Y) & equidistant(X::'a,V,W,Z) --> equidistant(Y::'a,V,W,Z)) &  \
\  (! X V Y W Z. equal(X::'a,Y) & equidistant(V::'a,X,W,Z) --> equidistant(V::'a,Y,W,Z)) &  \
\  (! X V W Y Z. equal(X::'a,Y) & equidistant(V::'a,W,X,Z) --> equidistant(V::'a,W,Y,Z)) &  \
\  (! X V W Z Y. equal(X::'a,Y) & equidistant(V::'a,W,Z,X) --> equidistant(V::'a,W,Z,Y)) &  \
\  (! X Y V1 V2 V3 V4. equal(X::'a,Y) --> equal(inner_pasch(X::'a,V1,V2,V3,V4),inner_pasch(Y::'a,V1,V2,V3,V4))) &   \
\  (! X V1 Y V2 V3 V4. equal(X::'a,Y) --> equal(inner_pasch(V1::'a,X,V2,V3,V4),inner_pasch(V1::'a,Y,V2,V3,V4))) &   \
\  (! X V1 V2 Y V3 V4. equal(X::'a,Y) --> equal(inner_pasch(V1::'a,V2,X,V3,V4),inner_pasch(V1::'a,V2,Y,V3,V4))) &   \
\  (! X V1 V2 V3 Y V4. equal(X::'a,Y) --> equal(inner_pasch(V1::'a,V2,V3,X,V4),inner_pasch(V1::'a,V2,V3,Y,V4))) &   \
\  (! X V1 V2 V3 V4 Y. equal(X::'a,Y) --> equal(inner_pasch(V1::'a,V2,V3,V4,X),inner_pasch(V1::'a,V2,V3,V4,Y))) &   \
\  (! A B C D E F'. equal(A::'a,B) --> equal(euclid1(A::'a,C,D,E,F'),euclid1(B::'a,C,D,E,F'))) &    \
\  (! G I' H J K' L. equal(G::'a,H) --> equal(euclid1(I'::'a,G,J,K',L),euclid1(I'::'a,H,J,K',L))) & \
\  (! M O_ P N Q R. equal(M::'a,N) --> equal(euclid1(O_::'a,P,M,Q,R),euclid1(O_::'a,P,N,Q,R))) &       \
\  (! S' U V W T' X. equal(S'::'a,T') --> equal(euclid1(U::'a,V,W,S',X),euclid1(U::'a,V,W,T',X))) & \
\  (! Y A1 B1 C1 D1 Z. equal(Y::'a,Z) --> equal(euclid1(A1::'a,B1,C1,D1,Y),euclid1(A1::'a,B1,C1,D1,Z))) &   \
\  (! E1 F1 G1 H1 I1 J1. equal(E1::'a,F1) --> equal(euclid2(E1::'a,G1,H1,I1,J1),euclid2(F1::'a,G1,H1,I1,J1))) &     \
\  (! K1 M1 L1 N1 O1 P1. equal(K1::'a,L1) --> equal(euclid2(M1::'a,K1,N1,O1,P1),euclid2(M1::'a,L1,N1,O1,P1))) &     \
\  (! Q1 S1 T1 R1 U1 V1. equal(Q1::'a,R1) --> equal(euclid2(S1::'a,T1,Q1,U1,V1),euclid2(S1::'a,T1,R1,U1,V1))) &     \
\  (! W1 Y1 Z1 A2 X1 B2. equal(W1::'a,X1) --> equal(euclid2(Y1::'a,Z1,A2,W1,B2),euclid2(Y1::'a,Z1,A2,X1,B2))) &     \
\  (! C2 E2 F2 G2 H2 D2. equal(C2::'a,D2) --> equal(euclid2(E2::'a,F2,G2,H2,C2),euclid2(E2::'a,F2,G2,H2,D2))) &     \
\  (! X Y V1 V2 V3. equal(X::'a,Y) --> equal(extension(X::'a,V1,V2,V3),extension(Y::'a,V1,V2,V3))) &        \
\  (! X V1 Y V2 V3. equal(X::'a,Y) --> equal(extension(V1::'a,X,V2,V3),extension(V1::'a,Y,V2,V3))) &        \
\  (! X V1 V2 Y V3. equal(X::'a,Y) --> equal(extension(V1::'a,V2,X,V3),extension(V1::'a,V2,Y,V3))) &        \
\  (! X V1 V2 V3 Y. equal(X::'a,Y) --> equal(extension(V1::'a,V2,V3,X),extension(V1::'a,V2,V3,Y))) &        \
\  (! X Y V1 V2 V3 V4 V5. equal(X::'a,Y) --> equal(continuous(X::'a,V1,V2,V3,V4,V5),continuous(Y::'a,V1,V2,V3,V4,V5))) &    \
\  (! X V1 Y V2 V3 V4 V5. equal(X::'a,Y) --> equal(continuous(V1::'a,X,V2,V3,V4,V5),continuous(V1::'a,Y,V2,V3,V4,V5))) &    \
\  (! X V1 V2 Y V3 V4 V5. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,X,V3,V4,V5),continuous(V1::'a,V2,Y,V3,V4,V5))) &    \
\  (! X V1 V2 V3 Y V4 V5. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,V3,X,V4,V5),continuous(V1::'a,V2,V3,Y,V4,V5))) &    \
\  (! X V1 V2 V3 V4 Y V5. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,V3,V4,X,V5),continuous(V1::'a,V2,V3,V4,Y,V5))) &    \
\  (! X V1 V2 V3 V4 V5 Y. equal(X::'a,Y) --> equal(continuous(V1::'a,V2,V3,V4,V5,X),continuous(V1::'a,V2,V3,V4,V5,Y))) &    \
\  (! U V. equal(reflection(U::'a,V),extension(U::'a,V,U,V))) & \
\  (! X Y Z. equal(X::'a,Y) --> equal(reflection(X::'a,Z),reflection(Y::'a,Z))) &   \
\  (! A1 C1 B1. equal(A1::'a,B1) --> equal(reflection(C1::'a,A1),reflection(C1::'a,B1))) &  \
\  (equal(v::'a,reflection(u::'a,v))) & \
\  (~equal(u::'a,v)) --> False",
  meson_tac);

(*0 inferences so far.  Searching to depth 0.  0.2 secs*)
val GEO079_1 = prove
 ("(! U V W X Y Z. right_angle(U::'a,V,W) & right_angle(X::'a,Y,Z) --> eq(U::'a,V,W,X,Y,Z)) &       \
\  (! U V W X Y Z. congruent(U::'a,V,W,X,Y,Z) --> eq(U::'a,V,W,X,Y,Z)) &        \
\  (! V W U X. trapezoid(U::'a,V,W,X) --> parallel(V::'a,W,U,X)) &      \
\  (! U V X Y. parallel(U::'a,V,X,Y) --> eq(X::'a,V,U,V,X,Y)) & \
\  (trapezoid(a::'a,b,c,d)) &       \
\  (~eq(a::'a,c,b,c,a,d)) --> False",
  meson_tac);

(****************SLOW
2032008 inferences so far.  Searching to depth 16.  No proof after 30 minutes.
val GRP001_1 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X. product(identity::'a,X,X)) &       \
\  (! X. product(X::'a,identity,X)) &       \
\  (! X. product(inverse(X),X,identity)) &      \
\  (! X. product(X::'a,inverse(X),identity)) &      \
\  (! X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (! X Y Z W. product(X::'a,Y,Z) & product(X::'a,Y,W) --> equal(Z::'a,W)) &        \
\  (! Y U Z X V W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(U::'a,Z,W) --> product(X::'a,V,W)) &       \
\  (! Y X V U Z W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(X::'a,V,W) --> product(U::'a,Z,W)) &       \
\  (! X Y. equal(X::'a,Y) --> equal(inverse(X),inverse(Y))) &       \
\  (! X Y W. equal(X::'a,Y) --> equal(multiply(X::'a,W),multiply(Y::'a,W))) &       \
\  (! X W Y. equal(X::'a,Y) --> equal(multiply(W::'a,X),multiply(W::'a,Y))) &       \
\  (! X Y W Z. equal(X::'a,Y) & product(X::'a,W,Z) --> product(Y::'a,W,Z)) &        \
\  (! X W Y Z. equal(X::'a,Y) & product(W::'a,X,Z) --> product(W::'a,Y,Z)) &        \
\  (! X W Z Y. equal(X::'a,Y) & product(W::'a,Z,X) --> product(W::'a,Z,Y)) &        \
\  (! X. product(X::'a,X,identity)) &       \
\  (product(a::'a,b,c)) &   \
\  (~product(b::'a,a,c)) --> False",
  meson_tac);
****************)

(*2386 inferences so far.  Searching to depth 11.  8.7 secs*)
val GRP008_1 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X. product(identity::'a,X,X)) &       \
\  (! X. product(X::'a,identity,X)) &       \
\  (! X. product(inverse(X),X,identity)) &      \
\  (! X. product(X::'a,inverse(X),identity)) &      \
\  (! X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (! X Y Z W. product(X::'a,Y,Z) & product(X::'a,Y,W) --> equal(Z::'a,W)) &        \
\  (! Y U Z X V W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(U::'a,Z,W) --> product(X::'a,V,W)) &       \
\  (! Y X V U Z W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(X::'a,V,W) --> product(U::'a,Z,W)) &       \
\  (! X Y. equal(X::'a,Y) --> equal(inverse(X),inverse(Y))) &       \
\  (! X Y W. equal(X::'a,Y) --> equal(multiply(X::'a,W),multiply(Y::'a,W))) &       \
\  (! X W Y. equal(X::'a,Y) --> equal(multiply(W::'a,X),multiply(W::'a,Y))) &       \
\  (! X Y W Z. equal(X::'a,Y) & product(X::'a,W,Z) --> product(Y::'a,W,Z)) &        \
\  (! X W Y Z. equal(X::'a,Y) & product(W::'a,X,Z) --> product(W::'a,Y,Z)) &        \
\  (! X W Z Y. equal(X::'a,Y) & product(W::'a,Z,X) --> product(W::'a,Z,Y)) &        \
\  (! A B. equal(A::'a,B) --> equal(h(A),h(B))) &   \
\  (! C D. equal(C::'a,D) --> equal(j(C),j(D))) &   \
\  (! A B. equal(A::'a,B) & q(A) --> q(B)) &        \
\  (! B A C. q(A) & product(A::'a,B,C) --> product(B::'a,A,C)) &        \
\  (! A. product(j(A),A,h(A)) | product(A::'a,j(A),h(A)) | q(A)) &        \
\  (! A. product(j(A),A,h(A)) & product(A::'a,j(A),h(A)) --> q(A)) &        \
\  (~q(identity)) --> False",
  meson_tac);

(*8625 inferences so far.  Searching to depth 11.  20 secs*)
val GRP013_1 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X. product(identity::'a,X,X)) &       \
\  (! X. product(X::'a,identity,X)) &       \
\  (! X. product(inverse(X),X,identity)) &      \
\  (! X. product(X::'a,inverse(X),identity)) &      \
\  (! X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (! X Y Z W. product(X::'a,Y,Z) & product(X::'a,Y,W) --> equal(Z::'a,W)) &        \
\  (! Y U Z X V W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(U::'a,Z,W) --> product(X::'a,V,W)) &       \
\  (! Y X V U Z W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(X::'a,V,W) --> product(U::'a,Z,W)) &       \
\  (! X Y. equal(X::'a,Y) --> equal(inverse(X),inverse(Y))) &       \
\  (! X Y W. equal(X::'a,Y) --> equal(multiply(X::'a,W),multiply(Y::'a,W))) &       \
\  (! X W Y. equal(X::'a,Y) --> equal(multiply(W::'a,X),multiply(W::'a,Y))) &       \
\  (! X Y W Z. equal(X::'a,Y) & product(X::'a,W,Z) --> product(Y::'a,W,Z)) &        \
\  (! X W Y Z. equal(X::'a,Y) & product(W::'a,X,Z) --> product(W::'a,Y,Z)) &        \
\  (! X W Z Y. equal(X::'a,Y) & product(W::'a,Z,X) --> product(W::'a,Z,Y)) &        \
\  (! A. product(A::'a,A,identity)) &       \
\  (product(a::'a,b,c)) &   \
\  (product(inverse(a),inverse(b),d)) & \
\  (! A C B. product(inverse(A),inverse(B),C) --> product(A::'a,C,B)) &     \
\  (~product(c::'a,d,identity)) --> False",
  meson_tac);

(*2448 inferences so far.  Searching to depth 10.  7.2 secs*)
val GRP037_3 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X. product(identity::'a,X,X)) &       \
\  (! X. product(X::'a,identity,X)) &       \
\  (! X. product(inverse(X),X,identity)) &      \
\  (! X. product(X::'a,inverse(X),identity)) &      \
\  (! X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (! X Y Z W. product(X::'a,Y,Z) & product(X::'a,Y,W) --> equal(Z::'a,W)) &        \
\  (! Y U Z X V W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(U::'a,Z,W) --> product(X::'a,V,W)) &       \
\  (! Y X V U Z W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(X::'a,V,W) --> product(U::'a,Z,W)) &       \
\  (! X Y. equal(X::'a,Y) --> equal(inverse(X),inverse(Y))) &       \
\  (! X Y W. equal(X::'a,Y) --> equal(multiply(X::'a,W),multiply(Y::'a,W))) &       \
\  (! X W Y. equal(X::'a,Y) --> equal(multiply(W::'a,X),multiply(W::'a,Y))) &       \
\  (! X Y W Z. equal(X::'a,Y) & product(X::'a,W,Z) --> product(Y::'a,W,Z)) &        \
\  (! X W Y Z. equal(X::'a,Y) & product(W::'a,X,Z) --> product(W::'a,Y,Z)) &        \
\  (! X W Z Y. equal(X::'a,Y) & product(W::'a,Z,X) --> product(W::'a,Z,Y)) &        \
\  (! A B C. subgroup_member(A) & subgroup_member(B) & product(A::'a,inverse(B),C) --> subgroup_member(C)) &        \
\  (! A B. equal(A::'a,B) & subgroup_member(A) --> subgroup_member(B)) &    \
\  (! A. subgroup_member(A) --> product(another_identity::'a,A,A)) &        \
\  (! A. subgroup_member(A) --> product(A::'a,another_identity,A)) &        \
\  (! A. subgroup_member(A) --> product(A::'a,another_inverse(A),another_identity)) &       \
\  (! A. subgroup_member(A) --> product(another_inverse(A),A,another_identity)) &       \
\  (! A. subgroup_member(A) --> subgroup_member(another_inverse(A))) &  \
\  (! A B. equal(A::'a,B) --> equal(another_inverse(A),another_inverse(B))) &       \
\  (! A C D B. product(A::'a,B,C) & product(A::'a,D,C) --> equal(D::'a,B)) &        \
\  (! B C D A. product(A::'a,B,C) & product(D::'a,B,C) --> equal(D::'a,A)) &        \
\  (subgroup_member(a)) &       \
\  (subgroup_member(another_identity)) &        \
\  (~equal(inverse(a),another_inverse(a))) --> False",
  meson_tac);

(*163 inferences so far.  Searching to depth 11.  0.3 secs*)
val GRP031_2 = prove
 ("(! X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (! X Y Z W. product(X::'a,Y,Z) & product(X::'a,Y,W) --> equal(Z::'a,W)) &        \
\  (! Y U Z X V W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(U::'a,Z,W) --> product(X::'a,V,W)) &       \
\  (! Y X V U Z W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(X::'a,V,W) --> product(U::'a,Z,W)) &       \
\  (! A. product(A::'a,inverse(A),identity)) &      \
\  (! A. product(A::'a,identity,A)) &       \
\  (! A. ~product(A::'a,a,identity)) --> False",
  meson_tac);

(*47 inferences so far.  Searching to depth 11.   0.2 secs*)
val GRP034_4 = prove
 ("(! X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (! X. product(identity::'a,X,X)) &       \
\  (! X. product(X::'a,identity,X)) &       \
\  (! X. product(X::'a,inverse(X),identity)) &      \
\  (! Y U Z X V W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(U::'a,Z,W) --> product(X::'a,V,W)) &       \
\  (! Y X V U Z W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(X::'a,V,W) --> product(U::'a,Z,W)) &       \
\  (! B A C. subgroup_member(A) & subgroup_member(B) & product(B::'a,inverse(A),C) --> subgroup_member(C)) &        \
\  (subgroup_member(a)) &       \
\  (~subgroup_member(inverse(a))) --> False",
  meson_tac);

(*3287 inferences so far.  Searching to depth 14.  3.5 secs*)
val GRP047_2 = prove_hard
 ("(! X. product(identity::'a,X,X)) &       \
\  (! X. product(inverse(X),X,identity)) &      \
\  (! X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (! X Y Z W. product(X::'a,Y,Z) & product(X::'a,Y,W) --> equal(Z::'a,W)) &        \
\  (! Y U Z X V W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(U::'a,Z,W) --> product(X::'a,V,W)) &       \
\  (! Y X V U Z W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(X::'a,V,W) --> product(U::'a,Z,W)) &       \
\  (! X W Z Y. equal(X::'a,Y) & product(W::'a,Z,X) --> product(W::'a,Z,Y)) &        \
\  (equal(a::'a,b)) &       \
\  (~equal(multiply(c::'a,a),multiply(c::'a,b))) --> False",
  meson_tac);

(*25559 inferences so far.  Searching to depth 19.  16.9 secs*)
val GRP130_1_002 = prove_hard
 ("(group_element(e_1)) &       \
\  (group_element(e_2)) &       \
\  (~equal(e_1::'a,e_2)) &  \
\  (~equal(e_2::'a,e_1)) &  \
\  (! X Y. group_element(X) & group_element(Y) --> product(X::'a,Y,e_1) | product(X::'a,Y,e_2)) &      \
\  (! X Y W Z. product(X::'a,Y,W) & product(X::'a,Y,Z) --> equal(W::'a,Z)) &        \
\  (! X Y W Z. product(X::'a,W,Y) & product(X::'a,Z,Y) --> equal(W::'a,Z)) &        \
\  (! Y X W Z. product(W::'a,Y,X) & product(Z::'a,Y,X) --> equal(W::'a,Z)) &        \
\  (! Z1 Z2 Y X. product(X::'a,Y,Z1) & product(X::'a,Z1,Z2) --> product(Z2::'a,Y,X)) --> False",
  meson_tac);

(*3468 inferences so far.  Searching to depth 10.  9.1 secs*)
val GRP156_1 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X. equal(multiply(identity::'a,X),X)) &       \
\  (! X. equal(multiply(inverse(X),X),identity)) &      \
\  (! X Y Z. equal(multiply(multiply(X::'a,Y),Z),multiply(X::'a,multiply(Y::'a,Z)))) &      \
\  (! A B. equal(A::'a,B) --> equal(inverse(A),inverse(B))) &       \
\  (! C D E. equal(C::'a,D) --> equal(multiply(C::'a,E),multiply(D::'a,E))) &       \
\  (! F' H G. equal(F'::'a,G) --> equal(multiply(H::'a,F'),multiply(H::'a,G))) &    \
\  (! Y X. equal(greatest_lower_bound(X::'a,Y),greatest_lower_bound(Y::'a,X))) &        \
\  (! Y X. equal(least_upper_bound(X::'a,Y),least_upper_bound(Y::'a,X))) &      \
\  (! X Y Z. equal(greatest_lower_bound(X::'a,greatest_lower_bound(Y::'a,Z)),greatest_lower_bound(greatest_lower_bound(X::'a,Y),Z))) &      \
\  (! X Y Z. equal(least_upper_bound(X::'a,least_upper_bound(Y::'a,Z)),least_upper_bound(least_upper_bound(X::'a,Y),Z))) &  \
\  (! X. equal(least_upper_bound(X::'a,X),X)) &     \
\  (! X. equal(greatest_lower_bound(X::'a,X),X)) &  \
\  (! Y X. equal(least_upper_bound(X::'a,greatest_lower_bound(X::'a,Y)),X)) &   \
\  (! Y X. equal(greatest_lower_bound(X::'a,least_upper_bound(X::'a,Y)),X)) &   \
\  (! Y X Z. equal(multiply(X::'a,least_upper_bound(Y::'a,Z)),least_upper_bound(multiply(X::'a,Y),multiply(X::'a,Z)))) &        \
\  (! Y X Z. equal(multiply(X::'a,greatest_lower_bound(Y::'a,Z)),greatest_lower_bound(multiply(X::'a,Y),multiply(X::'a,Z)))) &  \
\  (! Y Z X. equal(multiply(least_upper_bound(Y::'a,Z),X),least_upper_bound(multiply(Y::'a,X),multiply(Z::'a,X)))) &        \
\  (! Y Z X. equal(multiply(greatest_lower_bound(Y::'a,Z),X),greatest_lower_bound(multiply(Y::'a,X),multiply(Z::'a,X)))) &  \
\  (! A B C. equal(A::'a,B) --> equal(greatest_lower_bound(A::'a,C),greatest_lower_bound(B::'a,C))) &       \
\  (! A C B. equal(A::'a,B) --> equal(greatest_lower_bound(C::'a,A),greatest_lower_bound(C::'a,B))) &       \
\  (! A B C. equal(A::'a,B) --> equal(least_upper_bound(A::'a,C),least_upper_bound(B::'a,C))) &     \
\  (! A C B. equal(A::'a,B) --> equal(least_upper_bound(C::'a,A),least_upper_bound(C::'a,B))) &     \
\  (! A B C. equal(A::'a,B) --> equal(multiply(A::'a,C),multiply(B::'a,C))) &       \
\  (! A C B. equal(A::'a,B) --> equal(multiply(C::'a,A),multiply(C::'a,B))) &       \
\  (equal(least_upper_bound(a::'a,b),b)) &  \
\  (~equal(greatest_lower_bound(multiply(a::'a,c),multiply(b::'a,c)),multiply(a::'a,c))) --> False",
  meson_tac);

(*4394 inferences so far.  Searching to depth 10.  8.2 secs*)
val GRP168_1 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X. equal(multiply(identity::'a,X),X)) &       \
\  (! X. equal(multiply(inverse(X),X),identity)) &      \
\  (! X Y Z. equal(multiply(multiply(X::'a,Y),Z),multiply(X::'a,multiply(Y::'a,Z)))) &      \
\  (! A B. equal(A::'a,B) --> equal(inverse(A),inverse(B))) &       \
\  (! C D E. equal(C::'a,D) --> equal(multiply(C::'a,E),multiply(D::'a,E))) &       \
\  (! F' H G. equal(F'::'a,G) --> equal(multiply(H::'a,F'),multiply(H::'a,G))) &    \
\  (! Y X. equal(greatest_lower_bound(X::'a,Y),greatest_lower_bound(Y::'a,X))) &        \
\  (! Y X. equal(least_upper_bound(X::'a,Y),least_upper_bound(Y::'a,X))) &      \
\  (! X Y Z. equal(greatest_lower_bound(X::'a,greatest_lower_bound(Y::'a,Z)),greatest_lower_bound(greatest_lower_bound(X::'a,Y),Z))) &      \
\  (! X Y Z. equal(least_upper_bound(X::'a,least_upper_bound(Y::'a,Z)),least_upper_bound(least_upper_bound(X::'a,Y),Z))) &  \
\  (! X. equal(least_upper_bound(X::'a,X),X)) &     \
\  (! X. equal(greatest_lower_bound(X::'a,X),X)) &  \
\  (! Y X. equal(least_upper_bound(X::'a,greatest_lower_bound(X::'a,Y)),X)) &   \
\  (! Y X. equal(greatest_lower_bound(X::'a,least_upper_bound(X::'a,Y)),X)) &   \
\  (! Y X Z. equal(multiply(X::'a,least_upper_bound(Y::'a,Z)),least_upper_bound(multiply(X::'a,Y),multiply(X::'a,Z)))) &        \
\  (! Y X Z. equal(multiply(X::'a,greatest_lower_bound(Y::'a,Z)),greatest_lower_bound(multiply(X::'a,Y),multiply(X::'a,Z)))) &  \
\  (! Y Z X. equal(multiply(least_upper_bound(Y::'a,Z),X),least_upper_bound(multiply(Y::'a,X),multiply(Z::'a,X)))) &        \
\  (! Y Z X. equal(multiply(greatest_lower_bound(Y::'a,Z),X),greatest_lower_bound(multiply(Y::'a,X),multiply(Z::'a,X)))) &  \
\  (! A B C. equal(A::'a,B) --> equal(greatest_lower_bound(A::'a,C),greatest_lower_bound(B::'a,C))) &       \
\  (! A C B. equal(A::'a,B) --> equal(greatest_lower_bound(C::'a,A),greatest_lower_bound(C::'a,B))) &       \
\  (! A B C. equal(A::'a,B) --> equal(least_upper_bound(A::'a,C),least_upper_bound(B::'a,C))) &     \
\  (! A C B. equal(A::'a,B) --> equal(least_upper_bound(C::'a,A),least_upper_bound(C::'a,B))) &     \
\  (! A B C. equal(A::'a,B) --> equal(multiply(A::'a,C),multiply(B::'a,C))) &       \
\  (! A C B. equal(A::'a,B) --> equal(multiply(C::'a,A),multiply(C::'a,B))) &       \
\  (equal(least_upper_bound(a::'a,b),b)) &  \
\  (~equal(least_upper_bound(multiply(inverse(c),multiply(a::'a,c)),multiply(inverse(c),multiply(b::'a,c))),multiply(inverse(c),multiply(b::'a,c)))) --> False",
  meson_tac);

(*250258 inferences so far.  Searching to depth 16.  406.2 secs*)
val HEN003_3 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X Y. less_equal(X::'a,Y) --> equal(divide(X::'a,Y),zero)) &       \
\  (! X Y. equal(divide(X::'a,Y),zero) --> less_equal(X::'a,Y)) &       \
\  (! Y X. less_equal(divide(X::'a,Y),X)) & \
\  (! X Y Z. less_equal(divide(divide(X::'a,Z),divide(Y::'a,Z)),divide(divide(X::'a,Y),Z))) &       \
\  (! X. less_equal(zero::'a,X)) &  \
\  (! X Y. less_equal(X::'a,Y) & less_equal(Y::'a,X) --> equal(X::'a,Y)) &  \
\  (! X. less_equal(X::'a,identity)) &      \
\  (! A B C. equal(A::'a,B) --> equal(divide(A::'a,C),divide(B::'a,C))) &   \
\  (! D F' E. equal(D::'a,E) --> equal(divide(F'::'a,D),divide(F'::'a,E))) &        \
\  (! G H I'. equal(G::'a,H) & less_equal(G::'a,I') --> less_equal(H::'a,I')) &     \
\  (! J L K'. equal(J::'a,K') & less_equal(L::'a,J) --> less_equal(L::'a,K')) &     \
\  (~equal(divide(a::'a,a),zero)) --> False",
  meson_tac);


(*202177 inferences so far.  Searching to depth 14.  451 secs*)
val HEN007_2 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X Y. less_equal(X::'a,Y) --> quotient(X::'a,Y,zero)) &    \
\  (! X Y. quotient(X::'a,Y,zero) --> less_equal(X::'a,Y)) &    \
\  (! Y Z X. quotient(X::'a,Y,Z) --> less_equal(Z::'a,X)) &     \
\  (! Y X V3 V2 V1 Z V4 V5. quotient(X::'a,Y,V1) & quotient(Y::'a,Z,V2) & quotient(X::'a,Z,V3) & quotient(V3::'a,V2,V4) & quotient(V1::'a,Z,V5) --> less_equal(V4::'a,V5)) &    \
\  (! X. less_equal(zero::'a,X)) &  \
\  (! X Y. less_equal(X::'a,Y) & less_equal(Y::'a,X) --> equal(X::'a,Y)) &  \
\  (! X. less_equal(X::'a,identity)) &      \
\  (! X Y. quotient(X::'a,Y,divide(X::'a,Y))) & \
\  (! X Y Z W. quotient(X::'a,Y,Z) & quotient(X::'a,Y,W) --> equal(Z::'a,W)) &      \
\  (! X Y W Z. equal(X::'a,Y) & quotient(X::'a,W,Z) --> quotient(Y::'a,W,Z)) &      \
\  (! X W Y Z. equal(X::'a,Y) & quotient(W::'a,X,Z) --> quotient(W::'a,Y,Z)) &      \
\  (! X W Z Y. equal(X::'a,Y) & quotient(W::'a,Z,X) --> quotient(W::'a,Z,Y)) &      \
\  (! X Z Y. equal(X::'a,Y) & less_equal(Z::'a,X) --> less_equal(Z::'a,Y)) &        \
\  (! X Y Z. equal(X::'a,Y) & less_equal(X::'a,Z) --> less_equal(Y::'a,Z)) &        \
\  (! X Y W. equal(X::'a,Y) --> equal(divide(X::'a,W),divide(Y::'a,W))) &   \
\  (! X W Y. equal(X::'a,Y) --> equal(divide(W::'a,X),divide(W::'a,Y))) &   \
\  (! X. quotient(X::'a,identity,zero)) &   \
\  (! X. quotient(zero::'a,X,zero)) &       \
\  (! X. quotient(X::'a,X,zero)) &  \
\  (! X. quotient(X::'a,zero,X)) &  \
\  (! Y X Z. less_equal(X::'a,Y) & less_equal(Y::'a,Z) --> less_equal(X::'a,Z)) &   \
\  (! W1 X Z W2 Y. quotient(X::'a,Y,W1) & less_equal(W1::'a,Z) & quotient(X::'a,Z,W2) --> less_equal(W2::'a,Y)) &       \
\  (less_equal(x::'a,y)) &  \
\  (quotient(z::'a,y,zQy)) &        \
\  (quotient(z::'a,x,zQx)) &        \
\  (~less_equal(zQy::'a,zQx)) --> False",
  meson_tac);

(*60026 inferences so far.  Searching to depth 12.  42.2 secs*)
val HEN008_4 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X Y. less_equal(X::'a,Y) --> equal(divide(X::'a,Y),zero)) &       \
\  (! X Y. equal(divide(X::'a,Y),zero) --> less_equal(X::'a,Y)) &       \
\  (! Y X. less_equal(divide(X::'a,Y),X)) & \
\  (! X Y Z. less_equal(divide(divide(X::'a,Z),divide(Y::'a,Z)),divide(divide(X::'a,Y),Z))) &       \
\  (! X. less_equal(zero::'a,X)) &  \
\  (! X Y. less_equal(X::'a,Y) & less_equal(Y::'a,X) --> equal(X::'a,Y)) &  \
\  (! X. less_equal(X::'a,identity)) &      \
\  (! A B C. equal(A::'a,B) --> equal(divide(A::'a,C),divide(B::'a,C))) &   \
\  (! D F' E. equal(D::'a,E) --> equal(divide(F'::'a,D),divide(F'::'a,E))) &        \
\  (! G H I'. equal(G::'a,H) & less_equal(G::'a,I') --> less_equal(H::'a,I')) &     \
\  (! J L K'. equal(J::'a,K') & less_equal(L::'a,J) --> less_equal(L::'a,K')) &     \
\  (! X. equal(divide(X::'a,identity),zero)) &      \
\  (! X. equal(divide(zero::'a,X),zero)) &  \
\  (! X. equal(divide(X::'a,X),zero)) &     \
\  (equal(divide(a::'a,zero),a)) &  \
\  (! Y X Z. less_equal(X::'a,Y) & less_equal(Y::'a,Z) --> less_equal(X::'a,Z)) &   \
\  (! X Z Y. less_equal(divide(X::'a,Y),Z) --> less_equal(divide(X::'a,Z),Y)) & \
\  (! Y Z X. less_equal(X::'a,Y) --> less_equal(divide(Z::'a,Y),divide(Z::'a,X))) & \
\  (less_equal(a::'a,b)) &  \
\  (~less_equal(divide(a::'a,c),divide(b::'a,c))) --> False",
  meson_tac);


(*3160 inferences so far.  Searching to depth 11.  3.5 secs*)
val HEN009_5 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! Y X. equal(divide(divide(X::'a,Y),X),zero)) & \
\  (! X Y Z. equal(divide(divide(divide(X::'a,Z),divide(Y::'a,Z)),divide(divide(X::'a,Y),Z)),zero)) &       \
\  (! X. equal(divide(zero::'a,X),zero)) &  \
\  (! X Y. equal(divide(X::'a,Y),zero) & equal(divide(Y::'a,X),zero) --> equal(X::'a,Y)) &  \
\  (! X. equal(divide(X::'a,identity),zero)) &      \
\  (! A B C. equal(A::'a,B) --> equal(divide(A::'a,C),divide(B::'a,C))) &   \
\  (! D F' E. equal(D::'a,E) --> equal(divide(F'::'a,D),divide(F'::'a,E))) &        \
\  (! Y X Z. equal(divide(X::'a,Y),zero) & equal(divide(Y::'a,Z),zero) --> equal(divide(X::'a,Z),zero)) &   \
\  (! X Z Y. equal(divide(divide(X::'a,Y),Z),zero) --> equal(divide(divide(X::'a,Z),Y),zero)) & \
\  (! Y Z X. equal(divide(X::'a,Y),zero) --> equal(divide(divide(Z::'a,Y),divide(Z::'a,X)),zero)) & \
\  (~equal(divide(identity::'a,a),divide(identity::'a,divide(identity::'a,divide(identity::'a,a))))) &  \
\  (equal(divide(identity::'a,a),b)) &      \
\  (equal(divide(identity::'a,b),c)) &      \
\  (equal(divide(identity::'a,c),d)) &      \
\  (~equal(b::'a,d)) --> False",
  meson_tac);

(*970373 inferences so far.  Searching to depth 17.  890.0 secs*)
val HEN012_3 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X Y. less_equal(X::'a,Y) --> equal(divide(X::'a,Y),zero)) &       \
\  (! X Y. equal(divide(X::'a,Y),zero) --> less_equal(X::'a,Y)) &       \
\  (! Y X. less_equal(divide(X::'a,Y),X)) & \
\  (! X Y Z. less_equal(divide(divide(X::'a,Z),divide(Y::'a,Z)),divide(divide(X::'a,Y),Z))) &       \
\  (! X. less_equal(zero::'a,X)) &  \
\  (! X Y. less_equal(X::'a,Y) & less_equal(Y::'a,X) --> equal(X::'a,Y)) &  \
\  (! X. less_equal(X::'a,identity)) &      \
\  (! A B C. equal(A::'a,B) --> equal(divide(A::'a,C),divide(B::'a,C))) &   \
\  (! D F' E. equal(D::'a,E) --> equal(divide(F'::'a,D),divide(F'::'a,E))) &        \
\  (! G H I'. equal(G::'a,H) & less_equal(G::'a,I') --> less_equal(H::'a,I')) &     \
\  (! J L K'. equal(J::'a,K') & less_equal(L::'a,J) --> less_equal(L::'a,K')) &     \
\  (~less_equal(a::'a,a)) --> False",
  meson_tac);


(*1063 inferences so far.  Searching to depth 20.  1.0 secs*)
val LCL010_1 = prove
 ("(! X Y. is_a_theorem(equivalent(X::'a,Y)) & is_a_theorem(X) --> is_a_theorem(Y)) &       \
\  (! X Z Y. is_a_theorem(equivalent(equivalent(X::'a,Y),equivalent(equivalent(X::'a,Z),equivalent(Z::'a,Y))))) &   \
\  (~is_a_theorem(equivalent(equivalent(a::'a,b),equivalent(equivalent(c::'a,b),equivalent(a::'a,c))))) --> False",
  meson_tac);

(*2549 inferences so far.  Searching to depth 12.  1.4 secs*)
val LCL077_2 = prove
 ("(! X Y. is_a_theorem(implies(X,Y)) & is_a_theorem(X) --> is_a_theorem(Y)) &  \
\  (! Y X. is_a_theorem(implies(X,implies(Y,X)))) &     \
\  (! Y X Z. is_a_theorem(implies(implies(X,implies(Y,Z)),implies(implies(X,Y),implies(X,Z))))) &       \
\  (! Y X. is_a_theorem(implies(implies(not(X),not(Y)),implies(Y,X)))) &        \
\  (! X2 X1 X3. is_a_theorem(implies(X1,X2)) & is_a_theorem(implies(X2,X3)) --> is_a_theorem(implies(X1,X3))) & \
\  (~is_a_theorem(implies(not(not(a)),a))) --> False",
  meson_tac);

(*2036 inferences so far.  Searching to depth 20.  1.5 secs*)
val LCL082_1 = prove
 ("(! X Y. is_a_theorem(implies(X::'a,Y)) & is_a_theorem(X) --> is_a_theorem(Y)) &  \
\  (! Y Z U X. is_a_theorem(implies(implies(implies(X::'a,Y),Z),implies(implies(Z::'a,X),implies(U::'a,X))))) &     \
\  (~is_a_theorem(implies(a::'a,implies(b::'a,a)))) --> False",
  meson_tac);

(*1100 inferences so far.  Searching to depth 13.  1.0 secs*)
val LCL111_1 = prove
 ("(! X Y. is_a_theorem(implies(X,Y)) & is_a_theorem(X) --> is_a_theorem(Y)) &  \
\  (! Y X. is_a_theorem(implies(X,implies(Y,X)))) &     \
\  (! Y X Z. is_a_theorem(implies(implies(X,Y),implies(implies(Y,Z),implies(X,Z))))) &  \
\  (! Y X. is_a_theorem(implies(implies(implies(X,Y),Y),implies(implies(Y,X),X)))) &    \
\  (! Y X. is_a_theorem(implies(implies(not(X),not(Y)),implies(Y,X)))) &        \
\  (~is_a_theorem(implies(implies(a,b),implies(implies(c,a),implies(c,b))))) --> False",
  meson_tac);

(*667 inferences so far.  Searching to depth 9.  1.4 secs*)
val LCL143_1 = prove
 ("(! X. equal(X,X)) &  \
\  (! Y X. equal(X,Y) --> equal(Y,X)) & \
\  (! Y X Z. equal(X,Y) & equal(Y,Z) --> equal(X,Z)) &  \
\  (! X. equal(implies(true,X),X)) &    \
\  (! Y X Z. equal(implies(implies(X,Y),implies(implies(Y,Z),implies(X,Z))),true)) &    \
\  (! Y X. equal(implies(implies(X,Y),Y),implies(implies(Y,X),X))) &    \
\  (! Y X. equal(implies(implies(not(X),not(Y)),implies(Y,X)),true)) &  \
\  (! A B C. equal(A,B) --> equal(implies(A,C),implies(B,C))) & \
\  (! D F' E. equal(D,E) --> equal(implies(F',D),implies(F',E))) &      \
\  (! G H. equal(G,H) --> equal(not(G),not(H))) &       \
\  (! X Y. equal(big_V(X,Y),implies(implies(X,Y),Y))) & \
\  (! X Y. equal(big_hat(X,Y),not(big_V(not(X),not(Y))))) &     \
\  (! X Y. ordered(X,Y) --> equal(implies(X,Y),true)) & \
\  (! X Y. equal(implies(X,Y),true) --> ordered(X,Y)) & \
\  (! A B C. equal(A,B) --> equal(big_V(A,C),big_V(B,C))) &     \
\  (! D F' E. equal(D,E) --> equal(big_V(F',D),big_V(F',E))) &  \
\  (! G H I'. equal(G,H) --> equal(big_hat(G,I'),big_hat(H,I'))) &      \
\  (! J L K'. equal(J,K') --> equal(big_hat(L,J),big_hat(L,K'))) &      \
\  (! M N O_. equal(M,N) & ordered(M,O_) --> ordered(N,O_)) &      \
\  (! P R Q. equal(P,Q) & ordered(R,P) --> ordered(R,Q)) &      \
\  (ordered(x,y)) &     \
\  (~ordered(implies(z,x),implies(z,y))) --> False",
  meson_tac);

(*5245 inferences so far.  Searching to depth 12.  4.6 secs*)
val LCL182_1 = prove_hard
 ("(! A. axiom(or(not(or(A,A)),A))) &   \
\  (! B A. axiom(or(not(A),or(B,A)))) & \
\  (! B A. axiom(or(not(or(A,B)),or(B,A)))) &   \
\  (! B A C. axiom(or(not(or(A,or(B,C))),or(B,or(A,C))))) &     \
\  (! A C B. axiom(or(not(or(not(A),B)),or(not(or(C,A)),or(C,B))))) &   \
\  (! X. axiom(X) --> theorem(X)) &     \
\  (! X Y. axiom(or(not(Y),X)) & theorem(Y) --> theorem(X)) &   \
\  (! X Y Z. axiom(or(not(X),Y)) & theorem(or(not(Y),Z)) --> theorem(or(not(X),Z))) &   \
\  (~theorem(or(not(or(not(p),q)),or(not(not(q)),not(p))))) --> False",
  meson_tac);

(*410 inferences so far.  Searching to depth 10.  0.3 secs*)
val LCL200_1 = prove
 ("(! A. axiom(or(not(or(A,A)),A))) &   \
\  (! B A. axiom(or(not(A),or(B,A)))) & \
\  (! B A. axiom(or(not(or(A,B)),or(B,A)))) &   \
\  (! B A C. axiom(or(not(or(A,or(B,C))),or(B,or(A,C))))) &     \
\  (! A C B. axiom(or(not(or(not(A),B)),or(not(or(C,A)),or(C,B))))) &   \
\  (! X. axiom(X) --> theorem(X)) &     \
\  (! X Y. axiom(or(not(Y),X)) & theorem(Y) --> theorem(X)) &   \
\  (! X Y Z. axiom(or(not(X),Y)) & theorem(or(not(Y),Z)) --> theorem(or(not(X),Z))) &   \
\  (~theorem(or(not(not(or(p,q))),not(q)))) --> False",
  meson_tac);

(*5849 inferences so far.  Searching to depth 12.  5.6 secs*)
val LCL215_1 = prove_hard
 ("(! A. axiom(or(not(or(A,A)),A))) &   \
\  (! B A. axiom(or(not(A),or(B,A)))) & \
\  (! B A. axiom(or(not(or(A,B)),or(B,A)))) &   \
\  (! B A C. axiom(or(not(or(A,or(B,C))),or(B,or(A,C))))) &     \
\  (! A C B. axiom(or(not(or(not(A),B)),or(not(or(C,A)),or(C,B))))) &   \
\  (! X. axiom(X) --> theorem(X)) &     \
\  (! X Y. axiom(or(not(Y),X)) & theorem(Y) --> theorem(X)) &   \
\  (! X Y Z. axiom(or(not(X),Y)) & theorem(or(not(Y),Z)) --> theorem(or(not(X),Z))) &   \
\  (~theorem(or(not(or(not(p),q)),or(not(or(p,q)),q)))) --> False",
  meson_tac);

(*0 secs.  Not sure that a search even starts!*)
val LCL230_2 = prove
 ("(q --> p | r) &     \
\  (~p) &       \
\  (q) &        \
\  (~r) --> False",
  meson_tac);

(*119585 inferences so far.  Searching to depth 14.  262.4 secs*)
val LDA003_1 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! Y X Z. equal(f(X::'a,f(Y::'a,Z)),f(f(X::'a,Y),f(X::'a,Z)))) &     \
\  (! X Y. left(X::'a,f(X::'a,Y))) &    \
\  (! Y X Z. left(X::'a,Y) & left(Y::'a,Z) --> left(X::'a,Z)) &     \
\  (equal(num2::'a,f(num1::'a,num1))) &  \
\  (equal(num3::'a,f(num2::'a,num1))) &  \
\  (equal(u::'a,f(num2::'a,num2))) &  \
\  (! A B C. equal(A::'a,B) --> equal(f(A::'a,C),f(B::'a,C))) &     \
\  (! D F' E. equal(D::'a,E) --> equal(f(F'::'a,D),f(F'::'a,E))) &  \
\  (! G H I'. equal(G::'a,H) & left(G::'a,I') --> left(H::'a,I')) & \
\  (! J L K'. equal(J::'a,K') & left(L::'a,J) --> left(L::'a,K')) & \
\  (~left(num3::'a,u)) --> False",
  meson_tac);


(*2392 inferences so far.  Searching to depth 12.  2.2 secs*)
val MSC002_1 = prove
 ("(at(something::'a,here,now)) &   \
\  (! Place Situation. hand_at(Place::'a,Situation) --> hand_at(Place::'a,let_go(Situation))) & \
\  (! Place Another_place Situation. hand_at(Place::'a,Situation) --> hand_at(Another_place::'a,go(Another_place::'a,Situation))) & \
\  (! Thing Situation. ~held(Thing::'a,let_go(Situation))) &        \
\  (! Situation Thing. at(Thing::'a,here,Situation) --> red(Thing)) &       \
\  (! Thing Place Situation. at(Thing::'a,Place,Situation) --> at(Thing::'a,Place,let_go(Situation))) & \
\  (! Thing Place Situation. at(Thing::'a,Place,Situation) --> at(Thing::'a,Place,pick_up(Situation))) &        \
\  (! Thing Place Situation. at(Thing::'a,Place,Situation) --> grabbed(Thing::'a,pick_up(go(Place::'a,let_go(Situation))))) &       \
\  (! Thing Situation. red(Thing) & put(Thing::'a,there,Situation) --> answer(Situation)) & \
\  (! Place Thing Another_place Situation. at(Thing::'a,Place,Situation) & grabbed(Thing::'a,Situation) --> put(Thing::'a,Another_place,go(Another_place::'a,Situation))) &     \
\  (! Thing Place Another_place Situation. at(Thing::'a,Place,Situation) --> held(Thing::'a,Situation) | at(Thing::'a,Place,go(Another_place::'a,Situation))) &        \
\  (! One_place Thing Place Situation. hand_at(One_place::'a,Situation) & held(Thing::'a,Situation) --> at(Thing::'a,Place,go(Place::'a,Situation))) &  \
\  (! Place Thing Situation. hand_at(Place::'a,Situation) & at(Thing::'a,Place,Situation) --> held(Thing::'a,pick_up(Situation))) & \
\  (! Situation. ~answer(Situation)) --> False",
  meson_tac);

(*73 inferences so far.  Searching to depth 10.  0.2 secs*)
val MSC003_1 = prove
 ("(! Number_of_small_parts Small_part Big_part Number_of_mid_parts Mid_part. has_parts(Big_part::'a,Number_of_mid_parts,Mid_part) --> in'(object_in(Big_part::'a,Mid_part,Small_part,Number_of_mid_parts,Number_of_small_parts),Mid_part) | has_parts(Big_part::'a,times(Number_of_mid_parts::'a,Number_of_small_parts),Small_part)) &        \
\  (! Big_part Mid_part Number_of_mid_parts Number_of_small_parts Small_part. has_parts(Big_part::'a,Number_of_mid_parts,Mid_part) & has_parts(object_in(Big_part::'a,Mid_part,Small_part,Number_of_mid_parts,Number_of_small_parts),Number_of_small_parts,Small_part) --> has_parts(Big_part::'a,times(Number_of_mid_parts::'a,Number_of_small_parts),Small_part)) &   \
\  (in'(john::'a,boy)) &    \
\  (! X. in'(X::'a,boy) --> in'(X::'a,human)) & \
\  (! X. in'(X::'a,hand) --> has_parts(X::'a,num5,fingers)) &      \
\  (! X. in'(X::'a,human) --> has_parts(X::'a,num2,arm)) & \
\  (! X. in'(X::'a,arm) --> has_parts(X::'a,num1,hand)) &  \
\  (~has_parts(john::'a,times(num2::'a,num1),hand)) --> False",
  meson_tac);

(*1486 inferences so far.  Searching to depth 20.  1.2 secs*)
val MSC004_1 = prove
 ("(! Number_of_small_parts Small_part Big_part Number_of_mid_parts Mid_part. has_parts(Big_part::'a,Number_of_mid_parts,Mid_part) --> in'(object_in(Big_part::'a,Mid_part,Small_part,Number_of_mid_parts,Number_of_small_parts),Mid_part) | has_parts(Big_part::'a,times(Number_of_mid_parts::'a,Number_of_small_parts),Small_part)) &        \
\  (! Big_part Mid_part Number_of_mid_parts Number_of_small_parts Small_part. has_parts(Big_part::'a,Number_of_mid_parts,Mid_part) & has_parts(object_in(Big_part::'a,Mid_part,Small_part,Number_of_mid_parts,Number_of_small_parts),Number_of_small_parts,Small_part) --> has_parts(Big_part::'a,times(Number_of_mid_parts::'a,Number_of_small_parts),Small_part)) &   \
\  (in'(john::'a,boy)) &    \
\  (! X. in'(X::'a,boy) --> in'(X::'a,human)) & \
\  (! X. in'(X::'a,hand) --> has_parts(X::'a,num5,fingers)) &      \
\  (! X. in'(X::'a,human) --> has_parts(X::'a,num2,arm)) & \
\  (! X. in'(X::'a,arm) --> has_parts(X::'a,num1,hand)) &  \
\  (~has_parts(john::'a,times(times(num2::'a,num1),num5),fingers)) --> False",
  meson_tac);

(*100 inferences so far.  Searching to depth 12.  0.1 secs*)
val MSC005_1 = prove
 ("(value(truth::'a,truth)) &       \
\  (value(falsity::'a,falsity)) &   \
\  (! X Y. value(X::'a,truth) & value(Y::'a,truth) --> value(xor(X::'a,Y),falsity)) &       \
\  (! X Y. value(X::'a,truth) & value(Y::'a,falsity) --> value(xor(X::'a,Y),truth)) &       \
\  (! X Y. value(X::'a,falsity) & value(Y::'a,truth) --> value(xor(X::'a,Y),truth)) &       \
\  (! X Y. value(X::'a,falsity) & value(Y::'a,falsity) --> value(xor(X::'a,Y),falsity)) &   \
\  (! Value. ~value(xor(xor(xor(xor(truth::'a,falsity),falsity),truth),falsity),Value)) --> False",
  meson_tac);

(*19116 inferences so far.  Searching to depth 16.  15.9 secs*)
val MSC006_1 = prove_hard
 ("(! Y X Z. p(X::'a,Y) & p(Y::'a,Z) --> p(X::'a,Z)) &      \
\  (! Y X Z. q(X::'a,Y) & q(Y::'a,Z) --> q(X::'a,Z)) &      \
\  (! Y X. q(X::'a,Y) --> q(Y::'a,X)) & \
\  (! X Y. p(X::'a,Y) | q(X::'a,Y)) &  \
\  (~p(a::'a,b)) &  \
\  (~q(c::'a,d)) --> False",
  meson_tac);

(*1713 inferences so far.  Searching to depth 10.  2.8 secs*)
val NUM001_1 = prove
 ("(! A. equal(A::'a,A)) &                                                \
\  (! B A C. equal(A::'a,B) & equal(B::'a,C) --> equal(A::'a,C)) &        \
\  (! B A. equal(add(A::'a,B),add(B::'a,A))) &                            \
\  (! A B C. equal(add(A::'a,add(B::'a,C)),add(add(A::'a,B),C))) &        \
\  (! B A. equal(subtract(add(A::'a,B),B),A)) &                           \
\  (! A B. equal(A::'a,subtract(add(A::'a,B),B))) &                       \
\  (! A C B. equal(add(subtract(A::'a,B),C),subtract(add(A::'a,C),B))) &  \
\  (! A C B. equal(subtract(add(A::'a,B),C),add(subtract(A::'a,C),B))) &  \
\  (! A C B D. equal(A::'a,B) & equal(C::'a,add(A::'a,D)) --> equal(C::'a,add(B::'a,D))) &  \
\  (! A C D B. equal(A::'a,B) & equal(C::'a,add(D::'a,A)) --> equal(C::'a,add(D::'a,B))) &  \
\  (! A C B D. equal(A::'a,B) & equal(C::'a,subtract(A::'a,D)) --> equal(C::'a,subtract(B::'a,D))) &        \
\  (! A C D B. equal(A::'a,B) & equal(C::'a,subtract(D::'a,A)) --> equal(C::'a,subtract(D::'a,B))) &        \
\  (~equal(add(add(a::'a,b),c),add(a::'a,add(b::'a,c)))) --> False",
  meson_tac);

(*20717 inferences so far.  Searching to depth 11.  13.7 secs*)
val NUM021_1 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! A. equal(add(A::'a,num0),A)) &   \
\  (! A B. equal(add(A::'a,successor(B)),successor(add(A::'a,B)))) &    \
\  (! A. equal(multiply(A::'a,num0),num0)) &      \
\  (! B A. equal(multiply(A::'a,successor(B)),add(multiply(A::'a,B),A))) &      \
\  (! A B. equal(successor(A),successor(B)) --> equal(A::'a,B)) &   \
\  (! A B. equal(A::'a,B) --> equal(successor(A),successor(B))) &   \
\  (! A C B. less(A::'a,B) & less(C::'a,A) --> less(C::'a,B)) &     \
\  (! A B C. equal(add(successor(A),B),C) --> less(B::'a,C)) &      \
\  (! A B. less(A::'a,B) --> equal(add(successor(predecessor_of_1st_minus_2nd(B::'a,A)),A),B)) &        \
\  (! A B. divides(A::'a,B) --> less(A::'a,B) | equal(A::'a,B)) &  \
\  (! A B. less(A::'a,B) --> divides(A::'a,B)) &        \
\  (! A B. equal(A::'a,B) --> divides(A::'a,B)) &       \
\  (less(b::'a,c)) &        \
\  (~less(b::'a,a)) &       \
\  (divides(c::'a,a)) &     \
\  (! A. ~equal(successor(A),num0)) --> False",
  meson_tac);

(*26320 inferences so far.  Searching to depth 10.  26.4 secs*)
val NUM024_1 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! A. equal(add(A::'a,num0),A)) &   \
\  (! A B. equal(add(A::'a,successor(B)),successor(add(A::'a,B)))) &    \
\  (! A. equal(multiply(A::'a,num0),num0)) &      \
\  (! B A. equal(multiply(A::'a,successor(B)),add(multiply(A::'a,B),A))) &      \
\  (! A B. equal(successor(A),successor(B)) --> equal(A::'a,B)) &   \
\  (! A B. equal(A::'a,B) --> equal(successor(A),successor(B))) &   \
\  (! A C B. less(A::'a,B) & less(C::'a,A) --> less(C::'a,B)) &     \
\  (! A B C. equal(add(successor(A),B),C) --> less(B::'a,C)) &      \
\  (! A B. less(A::'a,B) --> equal(add(successor(predecessor_of_1st_minus_2nd(B::'a,A)),A),B)) &        \
\  (! B A. equal(add(A::'a,B),add(B::'a,A))) &  \
\  (! B A C. equal(add(A::'a,B),add(C::'a,B)) --> equal(A::'a,C)) & \
\  (less(a::'a,a)) &        \
\  (! A. ~equal(successor(A),num0)) --> False",
  meson_tac);


(*1345 inferences so far.  Searching to depth 7.  23.3 secs.  BIG*)
val NUM180_1 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X U Y. subclass(X::'a,Y) & member(U::'a,X) --> member(U::'a,Y)) &     \
\  (! X Y. member(not_subclass_element(X::'a,Y),X) | subclass(X::'a,Y)) &      \
\  (! X Y. member(not_subclass_element(X::'a,Y),Y) --> subclass(X::'a,Y)) &     \
\  (! X. subclass(X::'a,universal_class)) & \
\  (! X Y. equal(X::'a,Y) --> subclass(X::'a,Y)) &      \
\  (! Y X. equal(X::'a,Y) --> subclass(Y::'a,X)) &      \
\  (! X Y. subclass(X::'a,Y) & subclass(Y::'a,X) --> equal(X::'a,Y)) &      \
\  (! X U Y. member(U::'a,unordered_pair(X::'a,Y)) --> equal(U::'a,X) | equal(U::'a,Y)) &      \
\  (! X Y. member(X::'a,universal_class) --> member(X::'a,unordered_pair(X::'a,Y))) &       \
\  (! X Y. member(Y::'a,universal_class) --> member(Y::'a,unordered_pair(X::'a,Y))) &       \
\  (! X Y. member(unordered_pair(X::'a,Y),universal_class)) &       \
\  (! X. equal(unordered_pair(X::'a,X),singleton(X))) &     \
\  (! X Y. equal(unordered_pair(singleton(X),unordered_pair(X::'a,singleton(Y))),ordered_pair(X::'a,Y))) &      \
\  (! V Y U X. member(ordered_pair(U::'a,V),cross_product(X::'a,Y)) --> member(U::'a,X)) &  \
\  (! U X V Y. member(ordered_pair(U::'a,V),cross_product(X::'a,Y)) --> member(V::'a,Y)) &  \
\  (! U V X Y. member(U::'a,X) & member(V::'a,Y) --> member(ordered_pair(U::'a,V),cross_product(X::'a,Y))) &    \
\  (! X Y Z. member(Z::'a,cross_product(X::'a,Y)) --> equal(ordered_pair(first(Z),second(Z)),Z)) &      \
\  (subclass(element_relation::'a,cross_product(universal_class::'a,universal_class))) &        \
\  (! X Y. member(ordered_pair(X::'a,Y),element_relation) --> member(X::'a,Y)) &        \
\  (! X Y. member(ordered_pair(X::'a,Y),cross_product(universal_class::'a,universal_class)) & member(X::'a,Y) --> member(ordered_pair(X::'a,Y),element_relation)) &     \
\  (! Y Z X. member(Z::'a,intersection(X::'a,Y)) --> member(Z::'a,X)) &     \
\  (! X Z Y. member(Z::'a,intersection(X::'a,Y)) --> member(Z::'a,Y)) &     \
\  (! Z X Y. member(Z::'a,X) & member(Z::'a,Y) --> member(Z::'a,intersection(X::'a,Y))) &       \
\  (! Z X. ~(member(Z::'a,complement(X)) & member(Z::'a,X))) &  \
\  (! Z X. member(Z::'a,universal_class) --> member(Z::'a,complement(X)) | member(Z::'a,X)) &      \
\  (! X Y. equal(complement(intersection(complement(X),complement(Y))),union(X::'a,Y))) &   \
\  (! X Y. equal(intersection(complement(intersection(X::'a,Y)),complement(intersection(complement(X),complement(Y)))),difference(X::'a,Y))) &  \
\  (! Xr X Y. equal(intersection(Xr::'a,cross_product(X::'a,Y)),restrct(Xr::'a,X,Y))) &    \
\  (! Xr X Y. equal(intersection(cross_product(X::'a,Y),Xr),restrct(Xr::'a,X,Y))) &    \
\  (! Z X. ~(equal(restrct(X::'a,singleton(Z),universal_class),null_class) & member(Z::'a,domain_of(X)))) &    \
\  (! Z X. member(Z::'a,universal_class) --> equal(restrct(X::'a,singleton(Z),universal_class),null_class) | member(Z::'a,domain_of(X))) &        \
\  (! X. subclass(rotate(X),cross_product(cross_product(universal_class::'a,universal_class),universal_class))) &   \
\  (! V W U X. member(ordered_pair(ordered_pair(U::'a,V),W),rotate(X)) --> member(ordered_pair(ordered_pair(V::'a,W),U),X)) &   \
\  (! U V W X. member(ordered_pair(ordered_pair(V::'a,W),U),X) & member(ordered_pair(ordered_pair(U::'a,V),W),cross_product(cross_product(universal_class::'a,universal_class),universal_class)) --> member(ordered_pair(ordered_pair(U::'a,V),W),rotate(X))) & \
\  (! X. subclass(flip(X),cross_product(cross_product(universal_class::'a,universal_class),universal_class))) &     \
\  (! V U W X. member(ordered_pair(ordered_pair(U::'a,V),W),flip(X)) --> member(ordered_pair(ordered_pair(V::'a,U),W),X)) &     \
\  (! U V W X. member(ordered_pair(ordered_pair(V::'a,U),W),X) & member(ordered_pair(ordered_pair(U::'a,V),W),cross_product(cross_product(universal_class::'a,universal_class),universal_class)) --> member(ordered_pair(ordered_pair(U::'a,V),W),flip(X))) &   \
\  (! Y. equal(domain_of(flip(cross_product(Y::'a,universal_class))),inverse(Y))) & \
\  (! Z. equal(domain_of(inverse(Z)),range_of(Z))) &    \
\  (! Z X Y. equal(first(not_subclass_element(restrct(Z::'a,X,singleton(Y)),null_class)),domain(Z::'a,X,Y))) & \
\  (! Z X Y. equal(second(not_subclass_element(restrct(Z::'a,singleton(X),Y),null_class)),rng(Z::'a,X,Y))) & \
\  (! Xr X. equal(range_of(restrct(Xr::'a,X,universal_class)),image_(Xr::'a,X))) &      \
\  (! X. equal(union(X::'a,singleton(X)),successor(X))) &   \
\  (subclass(successor_relation::'a,cross_product(universal_class::'a,universal_class))) &      \
\  (! X Y. member(ordered_pair(X::'a,Y),successor_relation) --> equal(successor(X),Y)) &    \
\  (! X Y. equal(successor(X),Y) & member(ordered_pair(X::'a,Y),cross_product(universal_class::'a,universal_class)) --> member(ordered_pair(X::'a,Y),successor_relation)) & \
\  (! X. inductive(X) --> member(null_class::'a,X)) &       \
\  (! X. inductive(X) --> subclass(image_(successor_relation::'a,X),X)) &    \
\  (! X. member(null_class::'a,X) & subclass(image_(successor_relation::'a,X),X) --> inductive(X)) &     \
\  (inductive(omega)) & \
\  (! Y. inductive(Y) --> subclass(omega::'a,Y)) &  \
\  (member(omega::'a,universal_class)) &    \
\  (! X. equal(domain_of(restrct(element_relation::'a,universal_class,X)),sum_class(X))) & \
\  (! X. member(X::'a,universal_class) --> member(sum_class(X),universal_class)) &  \
\  (! X. equal(complement(image_(element_relation::'a,complement(X))),powerClass(X))) &     \
\  (! U. member(U::'a,universal_class) --> member(powerClass(U),universal_class)) &        \
\  (! Yr Xr. subclass(compos(Yr::'a,Xr),cross_product(universal_class::'a,universal_class))) & \
\  (! Z Yr Xr Y. member(ordered_pair(Y::'a,Z),compos(Yr::'a,Xr)) --> member(Z::'a,image_(Yr::'a,image_(Xr::'a,singleton(Y))))) &     \
\  (! Y Z Yr Xr. member(Z::'a,image_(Yr::'a,image_(Xr::'a,singleton(Y)))) & member(ordered_pair(Y::'a,Z),cross_product(universal_class::'a,universal_class)) --> member(ordered_pair(Y::'a,Z),compos(Yr::'a,Xr))) &  \
\  (! X. single_valued_class(X) --> subclass(compos(X::'a,inverse(X)),identity_relation)) &        \
\  (! X. subclass(compos(X::'a,inverse(X)),identity_relation) --> single_valued_class(X)) &        \
\  (! Xf. function(Xf) --> subclass(Xf::'a,cross_product(universal_class::'a,universal_class))) &       \
\  (! Xf. function(Xf) --> subclass(compos(Xf::'a,inverse(Xf)),identity_relation)) &       \
\  (! Xf. subclass(Xf::'a,cross_product(universal_class::'a,universal_class)) & subclass(compos(Xf::'a,inverse(Xf)),identity_relation) --> function(Xf)) & \
\  (! Xf X. function(Xf) & member(X::'a,universal_class) --> member(image_(Xf::'a,X),universal_class)) & \
\  (! X. equal(X::'a,null_class) | member(regular(X),X)) & \
\  (! X. equal(X::'a,null_class) | equal(intersection(X::'a,regular(X)),null_class)) & \
\  (! Xf Y. equal(sum_class(image_(Xf::'a,singleton(Y))),apply(Xf::'a,Y))) &     \
\  (function(choice)) & \
\  (! Y. member(Y::'a,universal_class) --> equal(Y::'a,null_class) | member(apply(choice::'a,Y),Y)) &      \
\  (! Xf. one_to_one(Xf) --> function(Xf)) &    \
\  (! Xf. one_to_one(Xf) --> function(inverse(Xf))) &   \
\  (! Xf. function(inverse(Xf)) & function(Xf) --> one_to_one(Xf)) &    \
\  (equal(intersection(cross_product(universal_class::'a,universal_class),intersection(cross_product(universal_class::'a,universal_class),complement(compos(complement(element_relation),inverse(element_relation))))),subset_relation)) &     \
\  (equal(intersection(inverse(subset_relation),subset_relation),identity_relation)) &  \
\  (! Xr. equal(complement(domain_of(intersection(Xr::'a,identity_relation))),diagonalise(Xr))) &   \
\  (! X. equal(intersection(domain_of(X),diagonalise(compos(inverse(element_relation),X))),cantor(X))) &       \
\  (! Xf. operation(Xf) --> function(Xf)) &     \
\  (! Xf. operation(Xf) --> equal(cross_product(domain_of(domain_of(Xf)),domain_of(domain_of(Xf))),domain_of(Xf))) &    \
\  (! Xf. operation(Xf) --> subclass(range_of(Xf),domain_of(domain_of(Xf)))) &  \
\  (! Xf. function(Xf) & equal(cross_product(domain_of(domain_of(Xf)),domain_of(domain_of(Xf))),domain_of(Xf)) & subclass(range_of(Xf),domain_of(domain_of(Xf))) --> operation(Xf)) &   \
\  (! Xf1 Xf2 Xh. compatible(Xh::'a,Xf1,Xf2) --> function(Xh)) &    \
\  (! Xf2 Xf1 Xh. compatible(Xh::'a,Xf1,Xf2) --> equal(domain_of(domain_of(Xf1)),domain_of(Xh))) &  \
\  (! Xf1 Xh Xf2. compatible(Xh::'a,Xf1,Xf2) --> subclass(range_of(Xh),domain_of(domain_of(Xf2)))) &        \
\  (! Xh Xh1 Xf1 Xf2. function(Xh) & equal(domain_of(domain_of(Xf1)),domain_of(Xh)) & subclass(range_of(Xh),domain_of(domain_of(Xf2))) --> compatible(Xh1::'a,Xf1,Xf2)) &   \
\  (! Xh Xf2 Xf1. homomorphism(Xh::'a,Xf1,Xf2) --> operation(Xf1)) &        \
\  (! Xh Xf1 Xf2. homomorphism(Xh::'a,Xf1,Xf2) --> operation(Xf2)) &        \
\  (! Xh Xf1 Xf2. homomorphism(Xh::'a,Xf1,Xf2) --> compatible(Xh::'a,Xf1,Xf2)) &        \
\  (! Xf2 Xh Xf1 X Y. homomorphism(Xh::'a,Xf1,Xf2) & member(ordered_pair(X::'a,Y),domain_of(Xf1)) --> equal(apply(Xf2::'a,ordered_pair(apply(Xh::'a,X),apply(Xh::'a,Y))),apply(Xh::'a,apply(Xf1::'a,ordered_pair(X::'a,Y))))) & \
\  (! Xh Xf1 Xf2. operation(Xf1) & operation(Xf2) & compatible(Xh::'a,Xf1,Xf2) --> member(ordered_pair(not_homomorphism1(Xh::'a,Xf1,Xf2),not_homomorphism2(Xh::'a,Xf1,Xf2)),domain_of(Xf1)) | homomorphism(Xh::'a,Xf1,Xf2)) &  \
\  (! Xh Xf1 Xf2. operation(Xf1) & operation(Xf2) & compatible(Xh::'a,Xf1,Xf2) & equal(apply(Xf2::'a,ordered_pair(apply(Xh::'a,not_homomorphism1(Xh::'a,Xf1,Xf2)),apply(Xh::'a,not_homomorphism2(Xh::'a,Xf1,Xf2)))),apply(Xh::'a,apply(Xf1::'a,ordered_pair(not_homomorphism1(Xh::'a,Xf1,Xf2),not_homomorphism2(Xh::'a,Xf1,Xf2))))) --> homomorphism(Xh::'a,Xf1,Xf2)) &     \
\  (! D E F'. equal(D::'a,E) --> equal(apply(D::'a,F'),apply(E::'a,F'))) &  \
\  (! G I' H. equal(G::'a,H) --> equal(apply(I'::'a,G),apply(I'::'a,H))) &  \
\  (! J K'. equal(J::'a,K') --> equal(cantor(J),cantor(K'))) &      \
\  (! L M. equal(L::'a,M) --> equal(complement(L),complement(M))) & \
\  (! N O_ P. equal(N::'a,O_) --> equal(compos(N::'a,P),compos(O_::'a,P))) & \
\  (! Q S' R. equal(Q::'a,R) --> equal(compos(S'::'a,Q),compos(S'::'a,R))) &      \
\  (! T' U V. equal(T'::'a,U) --> equal(cross_product(T'::'a,V),cross_product(U::'a,V))) &  \
\  (! W Y X. equal(W::'a,X) --> equal(cross_product(Y::'a,W),cross_product(Y::'a,X))) &     \
\  (! Z A1. equal(Z::'a,A1) --> equal(diagonalise(Z),diagonalise(A1))) &    \
\  (! B1 C1 D1. equal(B1::'a,C1) --> equal(difference(B1::'a,D1),difference(C1::'a,D1))) &  \
\  (! E1 G1 F1. equal(E1::'a,F1) --> equal(difference(G1::'a,E1),difference(G1::'a,F1))) &  \
\  (! H1 I1 J1 K1. equal(H1::'a,I1) --> equal(domain(H1::'a,J1,K1),domain(I1::'a,J1,K1))) & \
\  (! L1 N1 M1 O1. equal(L1::'a,M1) --> equal(domain(N1::'a,L1,O1),domain(N1::'a,M1,O1))) & \
\  (! P1 R1 S1 Q1. equal(P1::'a,Q1) --> equal(domain(R1::'a,S1,P1),domain(R1::'a,S1,Q1))) & \
\  (! T1 U1. equal(T1::'a,U1) --> equal(domain_of(T1),domain_of(U1))) &     \
\  (! V1 W1. equal(V1::'a,W1) --> equal(first(V1),first(W1))) &     \
\  (! X1 Y1. equal(X1::'a,Y1) --> equal(flip(X1),flip(Y1))) &       \
\  (! Z1 A2 B2. equal(Z1::'a,A2) --> equal(image_(Z1::'a,B2),image_(A2::'a,B2))) &    \
\  (! C2 E2 D2. equal(C2::'a,D2) --> equal(image_(E2::'a,C2),image_(E2::'a,D2))) &    \
\  (! F2 G2 H2. equal(F2::'a,G2) --> equal(intersection(F2::'a,H2),intersection(G2::'a,H2))) &      \
\  (! I2 K2 J2. equal(I2::'a,J2) --> equal(intersection(K2::'a,I2),intersection(K2::'a,J2))) &      \
\  (! L2 M2. equal(L2::'a,M2) --> equal(inverse(L2),inverse(M2))) & \
\  (! N2 O2 P2 Q2. equal(N2::'a,O2) --> equal(not_homomorphism1(N2::'a,P2,Q2),not_homomorphism1(O2::'a,P2,Q2))) &   \
\  (! R2 T2 S2 U2. equal(R2::'a,S2) --> equal(not_homomorphism1(T2::'a,R2,U2),not_homomorphism1(T2::'a,S2,U2))) &   \
\  (! V2 X2 Y2 W2. equal(V2::'a,W2) --> equal(not_homomorphism1(X2::'a,Y2,V2),not_homomorphism1(X2::'a,Y2,W2))) &   \
\  (! Z2 A3 B3 C3. equal(Z2::'a,A3) --> equal(not_homomorphism2(Z2::'a,B3,C3),not_homomorphism2(A3::'a,B3,C3))) &   \
\  (! D3 F3 E3 G3. equal(D3::'a,E3) --> equal(not_homomorphism2(F3::'a,D3,G3),not_homomorphism2(F3::'a,E3,G3))) &   \
\  (! H3 J3 K3 I3. equal(H3::'a,I3) --> equal(not_homomorphism2(J3::'a,K3,H3),not_homomorphism2(J3::'a,K3,I3))) &   \
\  (! L3 M3 N3. equal(L3::'a,M3) --> equal(not_subclass_element(L3::'a,N3),not_subclass_element(M3::'a,N3))) &      \
\  (! O3 Q3 P3. equal(O3::'a,P3) --> equal(not_subclass_element(Q3::'a,O3),not_subclass_element(Q3::'a,P3))) &      \
\  (! R3 S3 T3. equal(R3::'a,S3) --> equal(ordered_pair(R3::'a,T3),ordered_pair(S3::'a,T3))) &      \
\  (! U3 W3 V3. equal(U3::'a,V3) --> equal(ordered_pair(W3::'a,U3),ordered_pair(W3::'a,V3))) &      \
\  (! X3 Y3. equal(X3::'a,Y3) --> equal(powerClass(X3),powerClass(Y3))) & \
\  (! Z3 A4 B4 C4. equal(Z3::'a,A4) --> equal(rng(Z3::'a,B4,C4),rng(A4::'a,B4,C4))) &   \
\  (! D4 F4 E4 G4. equal(D4::'a,E4) --> equal(rng(F4::'a,D4,G4),rng(F4::'a,E4,G4))) &   \
\  (! H4 J4 K4 I4. equal(H4::'a,I4) --> equal(rng(J4::'a,K4,H4),rng(J4::'a,K4,I4))) &   \
\  (! L4 M4. equal(L4::'a,M4) --> equal(range_of(L4),range_of(M4))) &       \
\  (! N4 O4. equal(N4::'a,O4) --> equal(regular(N4),regular(O4))) & \
\  (! P4 Q4 R4 S4. equal(P4::'a,Q4) --> equal(restrct(P4::'a,R4,S4),restrct(Q4::'a,R4,S4))) &     \
\  (! T4 V4 U4 W4. equal(T4::'a,U4) --> equal(restrct(V4::'a,T4,W4),restrct(V4::'a,U4,W4))) &     \
\  (! X4 Z4 A5 Y4. equal(X4::'a,Y4) --> equal(restrct(Z4::'a,A5,X4),restrct(Z4::'a,A5,Y4))) &     \
\  (! B5 C5. equal(B5::'a,C5) --> equal(rotate(B5),rotate(C5))) &   \
\  (! D5 E5. equal(D5::'a,E5) --> equal(second(D5),second(E5))) &   \
\  (! F5 G5. equal(F5::'a,G5) --> equal(singleton(F5),singleton(G5))) &     \
\  (! H5 I5. equal(H5::'a,I5) --> equal(successor(H5),successor(I5))) &     \
\  (! J5 K5. equal(J5::'a,K5) --> equal(sum_class(J5),sum_class(K5))) &     \
\  (! L5 M5 N5. equal(L5::'a,M5) --> equal(union(L5::'a,N5),union(M5::'a,N5))) &    \
\  (! O5 Q5 P5. equal(O5::'a,P5) --> equal(union(Q5::'a,O5),union(Q5::'a,P5))) &    \
\  (! R5 S5 T5. equal(R5::'a,S5) --> equal(unordered_pair(R5::'a,T5),unordered_pair(S5::'a,T5))) &  \
\  (! U5 W5 V5. equal(U5::'a,V5) --> equal(unordered_pair(W5::'a,U5),unordered_pair(W5::'a,V5))) &  \
\  (! X5 Y5 Z5 A6. equal(X5::'a,Y5) & compatible(X5::'a,Z5,A6) --> compatible(Y5::'a,Z5,A6)) &      \
\  (! B6 D6 C6 E6. equal(B6::'a,C6) & compatible(D6::'a,B6,E6) --> compatible(D6::'a,C6,E6)) &      \
\  (! F6 H6 I6 G6. equal(F6::'a,G6) & compatible(H6::'a,I6,F6) --> compatible(H6::'a,I6,G6)) &      \
\  (! J6 K6. equal(J6::'a,K6) & function(J6) --> function(K6)) &    \
\  (! L6 M6 N6 O6. equal(L6::'a,M6) & homomorphism(L6::'a,N6,O6) --> homomorphism(M6::'a,N6,O6)) &  \
\  (! P6 R6 Q6 S6. equal(P6::'a,Q6) & homomorphism(R6::'a,P6,S6) --> homomorphism(R6::'a,Q6,S6)) &  \
\  (! T6 V6 W6 U6. equal(T6::'a,U6) & homomorphism(V6::'a,W6,T6) --> homomorphism(V6::'a,W6,U6)) &  \
\  (! X6 Y6. equal(X6::'a,Y6) & inductive(X6) --> inductive(Y6)) &  \
\  (! Z6 A7 B7. equal(Z6::'a,A7) & member(Z6::'a,B7) --> member(A7::'a,B7)) &       \
\  (! C7 E7 D7. equal(C7::'a,D7) & member(E7::'a,C7) --> member(E7::'a,D7)) &       \
\  (! F7 G7. equal(F7::'a,G7) & one_to_one(F7) --> one_to_one(G7)) &        \
\  (! H7 I7. equal(H7::'a,I7) & operation(H7) --> operation(I7)) &  \
\  (! J7 K7. equal(J7::'a,K7) & single_valued_class(J7) --> single_valued_class(K7)) &      \
\  (! L7 M7 N7. equal(L7::'a,M7) & subclass(L7::'a,N7) --> subclass(M7::'a,N7)) &   \
\  (! O7 Q7 P7. equal(O7::'a,P7) & subclass(Q7::'a,O7) --> subclass(Q7::'a,P7)) &   \
\  (! X. subclass(compose_class(X),cross_product(universal_class::'a,universal_class))) &   \
\  (! X Y Z. member(ordered_pair(Y::'a,Z),compose_class(X)) --> equal(compos(X::'a,Y),Z)) &    \
\  (! Y Z X. member(ordered_pair(Y::'a,Z),cross_product(universal_class::'a,universal_class)) & equal(compos(X::'a,Y),Z) --> member(ordered_pair(Y::'a,Z),compose_class(X))) & \
\  (subclass(composition_function::'a,cross_product(universal_class::'a,cross_product(universal_class::'a,universal_class)))) &     \
\  (! X Y Z. member(ordered_pair(X::'a,ordered_pair(Y::'a,Z)),composition_function) --> equal(compos(X::'a,Y),Z)) &        \
\  (! X Y. member(ordered_pair(X::'a,Y),cross_product(universal_class::'a,universal_class)) --> member(ordered_pair(X::'a,ordered_pair(Y::'a,compos(X::'a,Y))),composition_function)) &    \
\  (subclass(domain_relation::'a,cross_product(universal_class::'a,universal_class))) & \
\  (! X Y. member(ordered_pair(X::'a,Y),domain_relation) --> equal(domain_of(X),Y)) &       \
\  (! X. member(X::'a,universal_class) --> member(ordered_pair(X::'a,domain_of(X)),domain_relation)) &  \
\  (! X. equal(first(not_subclass_element(compos(X::'a,inverse(X)),identity_relation)),single_valued1(X))) &       \
\  (! X. equal(second(not_subclass_element(compos(X::'a,inverse(X)),identity_relation)),single_valued2(X))) &      \
\  (! X. equal(domain(X::'a,image_(inverse(X),singleton(single_valued1(X))),single_valued2(X)),single_valued3(X))) & \
\  (equal(intersection(complement(compos(element_relation::'a,complement(identity_relation))),element_relation),singleton_relation)) &     \
\  (subclass(application_function::'a,cross_product(universal_class::'a,cross_product(universal_class::'a,universal_class)))) &     \
\  (! Z Y X. member(ordered_pair(X::'a,ordered_pair(Y::'a,Z)),application_function) --> member(Y::'a,domain_of(X))) &       \
\  (! X Y Z. member(ordered_pair(X::'a,ordered_pair(Y::'a,Z)),application_function) --> equal(apply(X::'a,Y),Z)) &  \
\  (! Z X Y. member(ordered_pair(X::'a,ordered_pair(Y::'a,Z)),cross_product(universal_class::'a,cross_product(universal_class::'a,universal_class))) & member(Y::'a,domain_of(X)) --> member(ordered_pair(X::'a,ordered_pair(Y::'a,apply(X::'a,Y))),application_function)) &    \
\  (! X Y Xf. maps(Xf::'a,X,Y) --> function(Xf)) &  \
\  (! Y Xf X. maps(Xf::'a,X,Y) --> equal(domain_of(Xf),X)) &        \
\  (! X Xf Y. maps(Xf::'a,X,Y) --> subclass(range_of(Xf),Y)) &      \
\  (! Xf Y. function(Xf) & subclass(range_of(Xf),Y) --> maps(Xf::'a,domain_of(Xf),Y)) &     \
\  (! L M. equal(L::'a,M) --> equal(compose_class(L),compose_class(M))) &   \
\  (! N2 O2. equal(N2::'a,O2) --> equal(single_valued1(N2),single_valued1(O2))) &   \
\  (! P2 Q2. equal(P2::'a,Q2) --> equal(single_valued2(P2),single_valued2(Q2))) &   \
\  (! R2 S2. equal(R2::'a,S2) --> equal(single_valued3(R2),single_valued3(S2))) &   \
\  (! X2 Y2 Z2 A3. equal(X2::'a,Y2) & maps(X2::'a,Z2,A3) --> maps(Y2::'a,Z2,A3)) &  \
\  (! B3 D3 C3 E3. equal(B3::'a,C3) & maps(D3::'a,B3,E3) --> maps(D3::'a,C3,E3)) &  \
\  (! F3 H3 I3 G3. equal(F3::'a,G3) & maps(H3::'a,I3,F3) --> maps(H3::'a,I3,G3)) &  \
\  (! X. equal(union(X::'a,inverse(X)),symmetrization_of(X))) &     \
\  (! X Y. irreflexive(X::'a,Y) --> subclass(restrct(X::'a,Y,Y),complement(identity_relation))) &      \
\  (! X Y. subclass(restrct(X::'a,Y,Y),complement(identity_relation)) --> irreflexive(X::'a,Y)) &      \
\  (! Y X. connected(X::'a,Y) --> subclass(cross_product(Y::'a,Y),union(identity_relation::'a,symmetrization_of(X)))) &     \
\  (! X Y. subclass(cross_product(Y::'a,Y),union(identity_relation::'a,symmetrization_of(X))) --> connected(X::'a,Y)) &     \
\  (! Xr Y. transitive(Xr::'a,Y) --> subclass(compos(restrct(Xr::'a,Y,Y),restrct(Xr::'a,Y,Y)),restrct(Xr::'a,Y,Y))) &       \
\  (! Xr Y. subclass(compos(restrct(Xr::'a,Y,Y),restrct(Xr::'a,Y,Y)),restrct(Xr::'a,Y,Y)) --> transitive(Xr::'a,Y)) &       \
\  (! Xr Y. asymmetric(Xr::'a,Y) --> equal(restrct(intersection(Xr::'a,inverse(Xr)),Y,Y),null_class)) &        \
\  (! Xr Y. equal(restrct(intersection(Xr::'a,inverse(Xr)),Y,Y),null_class) --> asymmetric(Xr::'a,Y)) &        \
\  (! Xr Y Z. equal(segment(Xr::'a,Y,Z),domain_of(restrct(Xr::'a,Y,singleton(Z))))) &  \
\  (! X Y. well_ordering(X::'a,Y) --> connected(X::'a,Y)) &     \
\  (! Y Xr U. well_ordering(Xr::'a,Y) & subclass(U::'a,Y) --> equal(U::'a,null_class) | member(least(Xr::'a,U),U)) &   \
\  (! Y V Xr U. well_ordering(Xr::'a,Y) & subclass(U::'a,Y) & member(V::'a,U) --> member(least(Xr::'a,U),U)) &  \
\  (! Y Xr U. well_ordering(Xr::'a,Y) & subclass(U::'a,Y) --> equal(segment(Xr::'a,U,least(Xr::'a,U)),null_class)) &    \
\  (! Y V U Xr. ~(well_ordering(Xr::'a,Y) & subclass(U::'a,Y) & member(V::'a,U) & member(ordered_pair(V::'a,least(Xr::'a,U)),Xr))) &        \
\  (! Xr Y. connected(Xr::'a,Y) & equal(not_well_ordering(Xr::'a,Y),null_class) --> well_ordering(Xr::'a,Y)) &      \
\  (! Xr Y. connected(Xr::'a,Y) --> subclass(not_well_ordering(Xr::'a,Y),Y) | well_ordering(Xr::'a,Y)) &   \
\  (! V Xr Y. member(V::'a,not_well_ordering(Xr::'a,Y)) & equal(segment(Xr::'a,not_well_ordering(Xr::'a,Y),V),null_class) & connected(Xr::'a,Y) --> well_ordering(Xr::'a,Y)) &  \
\  (! Xr Y Z. section(Xr::'a,Y,Z) --> subclass(Y::'a,Z)) &      \
\  (! Xr Z Y. section(Xr::'a,Y,Z) --> subclass(domain_of(restrct(Xr::'a,Z,Y)),Y)) &    \
\  (! Xr Y Z. subclass(Y::'a,Z) & subclass(domain_of(restrct(Xr::'a,Z,Y)),Y) --> section(Xr::'a,Y,Z)) &    \
\  (! X. member(X::'a,ordinal_numbers) --> well_ordering(element_relation::'a,X)) &     \
\  (! X. member(X::'a,ordinal_numbers) --> subclass(sum_class(X),X)) &      \
\  (! X. well_ordering(element_relation::'a,X) & subclass(sum_class(X),X) & member(X::'a,universal_class) --> member(X::'a,ordinal_numbers)) &      \
\  (! X. well_ordering(element_relation::'a,X) & subclass(sum_class(X),X) --> member(X::'a,ordinal_numbers) | equal(X::'a,ordinal_numbers)) &      \
\  (equal(union(singleton(null_class),image_(successor_relation::'a,ordinal_numbers)),kind_1_ordinals)) &    \
\  (equal(intersection(complement(kind_1_ordinals),ordinal_numbers),limit_ordinals)) &  \
\  (! X. subclass(rest_of(X),cross_product(universal_class::'a,universal_class))) & \
\  (! V U X. member(ordered_pair(U::'a,V),rest_of(X)) --> member(U::'a,domain_of(X))) & \
\  (! X U V. member(ordered_pair(U::'a,V),rest_of(X)) --> equal(restrct(X::'a,U,universal_class),V)) & \
\  (! U V X. member(U::'a,domain_of(X)) & equal(restrct(X::'a,U,universal_class),V) --> member(ordered_pair(U::'a,V),rest_of(X))) &        \
\  (subclass(rest_relation::'a,cross_product(universal_class::'a,universal_class))) &   \
\  (! X Y. member(ordered_pair(X::'a,Y),rest_relation) --> equal(rest_of(X),Y)) &   \
\  (! X. member(X::'a,universal_class) --> member(ordered_pair(X::'a,rest_of(X)),rest_relation)) &      \
\  (! X Z. member(X::'a,recursion_equation_functions(Z)) --> function(Z)) & \
\  (! Z X. member(X::'a,recursion_equation_functions(Z)) --> function(X)) & \
\  (! Z X. member(X::'a,recursion_equation_functions(Z)) --> member(domain_of(X),ordinal_numbers)) &        \
\  (! Z X. member(X::'a,recursion_equation_functions(Z)) --> equal(compos(Z::'a,rest_of(X)),X)) &      \
\  (! X Z. function(Z) & function(X) & member(domain_of(X),ordinal_numbers) & equal(compos(Z::'a,rest_of(X)),X) --> member(X::'a,recursion_equation_functions(Z))) &   \
\  (subclass(union_of_range_map::'a,cross_product(universal_class::'a,universal_class))) &      \
\  (! X Y. member(ordered_pair(X::'a,Y),union_of_range_map) --> equal(sum_class(range_of(X)),Y)) &  \
\  (! X Y. member(ordered_pair(X::'a,Y),cross_product(universal_class::'a,universal_class)) & equal(sum_class(range_of(X)),Y) --> member(ordered_pair(X::'a,Y),union_of_range_map)) &       \
\  (! X Y. equal(apply(recursion(X::'a,successor_relation,union_of_range_map),Y),ordinal_add(X::'a,Y))) &       \
\  (! X Y. equal(recursion(null_class::'a,apply(add_relation::'a,X),union_of_range_map),ordinal_multiply(X::'a,Y))) &       \
\  (! X. member(X::'a,omega) --> equal(integer_of(X),X)) &  \
\  (! X. member(X::'a,omega) | equal(integer_of(X),null_class)) &  \
\  (! D E. equal(D::'a,E) --> equal(integer_of(D),integer_of(E))) & \
\  (! F' G H. equal(F'::'a,G) --> equal(least(F'::'a,H),least(G::'a,H))) &  \
\  (! I' K' J. equal(I'::'a,J) --> equal(least(K'::'a,I'),least(K'::'a,J))) &       \
\  (! L M N. equal(L::'a,M) --> equal(not_well_ordering(L::'a,N),not_well_ordering(M::'a,N))) &     \
\  (! O_ Q P. equal(O_::'a,P) --> equal(not_well_ordering(Q::'a,O_),not_well_ordering(Q::'a,P))) &     \
\  (! R S' T'. equal(R::'a,S') --> equal(ordinal_add(R::'a,T'),ordinal_add(S'::'a,T'))) &   \
\  (! U W V. equal(U::'a,V) --> equal(ordinal_add(W::'a,U),ordinal_add(W::'a,V))) & \
\  (! X Y Z. equal(X::'a,Y) --> equal(ordinal_multiply(X::'a,Z),ordinal_multiply(Y::'a,Z))) &       \
\  (! A1 C1 B1. equal(A1::'a,B1) --> equal(ordinal_multiply(C1::'a,A1),ordinal_multiply(C1::'a,B1))) &      \
\  (! F1 G1 H1 I1. equal(F1::'a,G1) --> equal(recursion(F1::'a,H1,I1),recursion(G1::'a,H1,I1))) &   \
\  (! J1 L1 K1 M1. equal(J1::'a,K1) --> equal(recursion(L1::'a,J1,M1),recursion(L1::'a,K1,M1))) &   \
\  (! N1 P1 Q1 O1. equal(N1::'a,O1) --> equal(recursion(P1::'a,Q1,N1),recursion(P1::'a,Q1,O1))) &   \
\  (! R1 S1. equal(R1::'a,S1) --> equal(recursion_equation_functions(R1),recursion_equation_functions(S1))) &       \
\  (! T1 U1. equal(T1::'a,U1) --> equal(rest_of(T1),rest_of(U1))) & \
\  (! V1 W1 X1 Y1. equal(V1::'a,W1) --> equal(segment(V1::'a,X1,Y1),segment(W1::'a,X1,Y1))) &       \
\  (! Z1 B2 A2 C2. equal(Z1::'a,A2) --> equal(segment(B2::'a,Z1,C2),segment(B2::'a,A2,C2))) &       \
\  (! D2 F2 G2 E2. equal(D2::'a,E2) --> equal(segment(F2::'a,G2,D2),segment(F2::'a,G2,E2))) &       \
\  (! H2 I2. equal(H2::'a,I2) --> equal(symmetrization_of(H2),symmetrization_of(I2))) &     \
\  (! J2 K2 L2. equal(J2::'a,K2) & asymmetric(J2::'a,L2) --> asymmetric(K2::'a,L2)) &       \
\  (! M2 O2 N2. equal(M2::'a,N2) & asymmetric(O2::'a,M2) --> asymmetric(O2::'a,N2)) &       \
\  (! P2 Q2 R2. equal(P2::'a,Q2) & connected(P2::'a,R2) --> connected(Q2::'a,R2)) & \
\  (! S2 U2 T2. equal(S2::'a,T2) & connected(U2::'a,S2) --> connected(U2::'a,T2)) & \
\  (! V2 W2 X2. equal(V2::'a,W2) & irreflexive(V2::'a,X2) --> irreflexive(W2::'a,X2)) &     \
\  (! Y2 A3 Z2. equal(Y2::'a,Z2) & irreflexive(A3::'a,Y2) --> irreflexive(A3::'a,Z2)) &     \
\  (! B3 C3 D3 E3. equal(B3::'a,C3) & section(B3::'a,D3,E3) --> section(C3::'a,D3,E3)) &    \
\  (! F3 H3 G3 I3. equal(F3::'a,G3) & section(H3::'a,F3,I3) --> section(H3::'a,G3,I3)) &    \
\  (! J3 L3 M3 K3. equal(J3::'a,K3) & section(L3::'a,M3,J3) --> section(L3::'a,M3,K3)) &    \
\  (! N3 O3 P3. equal(N3::'a,O3) & transitive(N3::'a,P3) --> transitive(O3::'a,P3)) &       \
\  (! Q3 S3 R3. equal(Q3::'a,R3) & transitive(S3::'a,Q3) --> transitive(S3::'a,R3)) &       \
\  (! T3 U3 V3. equal(T3::'a,U3) & well_ordering(T3::'a,V3) --> well_ordering(U3::'a,V3)) & \
\  (! W3 Y3 X3. equal(W3::'a,X3) & well_ordering(Y3::'a,W3) --> well_ordering(Y3::'a,X3)) & \
\  (~subclass(limit_ordinals::'a,ordinal_numbers)) --> False",
  meson_tac);


(*0 inferences so far.  Searching to depth 0.  16.8 secs.  BIG*)
val NUM228_1 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X U Y. subclass(X::'a,Y) & member(U::'a,X) --> member(U::'a,Y)) &     \
\  (! X Y. member(not_subclass_element(X::'a,Y),X) | subclass(X::'a,Y)) &      \
\  (! X Y. member(not_subclass_element(X::'a,Y),Y) --> subclass(X::'a,Y)) &     \
\  (! X. subclass(X::'a,universal_class)) & \
\  (! X Y. equal(X::'a,Y) --> subclass(X::'a,Y)) &      \
\  (! Y X. equal(X::'a,Y) --> subclass(Y::'a,X)) &      \
\  (! X Y. subclass(X::'a,Y) & subclass(Y::'a,X) --> equal(X::'a,Y)) &      \
\  (! X U Y. member(U::'a,unordered_pair(X::'a,Y)) --> equal(U::'a,X) | equal(U::'a,Y)) &      \
\  (! X Y. member(X::'a,universal_class) --> member(X::'a,unordered_pair(X::'a,Y))) &       \
\  (! X Y. member(Y::'a,universal_class) --> member(Y::'a,unordered_pair(X::'a,Y))) &       \
\  (! X Y. member(unordered_pair(X::'a,Y),universal_class)) &       \
\  (! X. equal(unordered_pair(X::'a,X),singleton(X))) &     \
\  (! X Y. equal(unordered_pair(singleton(X),unordered_pair(X::'a,singleton(Y))),ordered_pair(X::'a,Y))) &      \
\  (! V Y U X. member(ordered_pair(U::'a,V),cross_product(X::'a,Y)) --> member(U::'a,X)) &  \
\  (! U X V Y. member(ordered_pair(U::'a,V),cross_product(X::'a,Y)) --> member(V::'a,Y)) &  \
\  (! U V X Y. member(U::'a,X) & member(V::'a,Y) --> member(ordered_pair(U::'a,V),cross_product(X::'a,Y))) &    \
\  (! X Y Z. member(Z::'a,cross_product(X::'a,Y)) --> equal(ordered_pair(first(Z),second(Z)),Z)) &      \
\  (subclass(element_relation::'a,cross_product(universal_class::'a,universal_class))) &        \
\  (! X Y. member(ordered_pair(X::'a,Y),element_relation) --> member(X::'a,Y)) &        \
\  (! X Y. member(ordered_pair(X::'a,Y),cross_product(universal_class::'a,universal_class)) & member(X::'a,Y) --> member(ordered_pair(X::'a,Y),element_relation)) &     \
\  (! Y Z X. member(Z::'a,intersection(X::'a,Y)) --> member(Z::'a,X)) &     \
\  (! X Z Y. member(Z::'a,intersection(X::'a,Y)) --> member(Z::'a,Y)) &     \
\  (! Z X Y. member(Z::'a,X) & member(Z::'a,Y) --> member(Z::'a,intersection(X::'a,Y))) &       \
\  (! Z X. ~(member(Z::'a,complement(X)) & member(Z::'a,X))) &  \
\  (! Z X. member(Z::'a,universal_class) --> member(Z::'a,complement(X)) | member(Z::'a,X)) &      \
\  (! X Y. equal(complement(intersection(complement(X),complement(Y))),union(X::'a,Y))) &   \
\  (! X Y. equal(intersection(complement(intersection(X::'a,Y)),complement(intersection(complement(X),complement(Y)))),difference(X::'a,Y))) &  \
\  (! Xr X Y. equal(intersection(Xr::'a,cross_product(X::'a,Y)),restrct(Xr::'a,X,Y))) &    \
\  (! Xr X Y. equal(intersection(cross_product(X::'a,Y),Xr),restrct(Xr::'a,X,Y))) &    \
\  (! Z X. ~(equal(restrct(X::'a,singleton(Z),universal_class),null_class) & member(Z::'a,domain_of(X)))) &    \
\  (! Z X. member(Z::'a,universal_class) --> equal(restrct(X::'a,singleton(Z),universal_class),null_class) | member(Z::'a,domain_of(X))) &        \
\  (! X. subclass(rotate(X),cross_product(cross_product(universal_class::'a,universal_class),universal_class))) &   \
\  (! V W U X. member(ordered_pair(ordered_pair(U::'a,V),W),rotate(X)) --> member(ordered_pair(ordered_pair(V::'a,W),U),X)) &   \
\  (! U V W X. member(ordered_pair(ordered_pair(V::'a,W),U),X) & member(ordered_pair(ordered_pair(U::'a,V),W),cross_product(cross_product(universal_class::'a,universal_class),universal_class)) --> member(ordered_pair(ordered_pair(U::'a,V),W),rotate(X))) & \
\  (! X. subclass(flip(X),cross_product(cross_product(universal_class::'a,universal_class),universal_class))) &     \
\  (! V U W X. member(ordered_pair(ordered_pair(U::'a,V),W),flip(X)) --> member(ordered_pair(ordered_pair(V::'a,U),W),X)) &     \
\  (! U V W X. member(ordered_pair(ordered_pair(V::'a,U),W),X) & member(ordered_pair(ordered_pair(U::'a,V),W),cross_product(cross_product(universal_class::'a,universal_class),universal_class)) --> member(ordered_pair(ordered_pair(U::'a,V),W),flip(X))) &   \
\  (! Y. equal(domain_of(flip(cross_product(Y::'a,universal_class))),inverse(Y))) & \
\  (! Z. equal(domain_of(inverse(Z)),range_of(Z))) &    \
\  (! Z X Y. equal(first(not_subclass_element(restrct(Z::'a,X,singleton(Y)),null_class)),domain(Z::'a,X,Y))) & \
\  (! Z X Y. equal(second(not_subclass_element(restrct(Z::'a,singleton(X),Y),null_class)),rng(Z::'a,X,Y))) & \
\  (! Xr X. equal(range_of(restrct(Xr::'a,X,universal_class)),image_(Xr::'a,X))) &      \
\  (! X. equal(union(X::'a,singleton(X)),successor(X))) &   \
\  (subclass(successor_relation::'a,cross_product(universal_class::'a,universal_class))) &      \
\  (! X Y. member(ordered_pair(X::'a,Y),successor_relation) --> equal(successor(X),Y)) &    \
\  (! X Y. equal(successor(X),Y) & member(ordered_pair(X::'a,Y),cross_product(universal_class::'a,universal_class)) --> member(ordered_pair(X::'a,Y),successor_relation)) & \
\  (! X. inductive(X) --> member(null_class::'a,X)) &       \
\  (! X. inductive(X) --> subclass(image_(successor_relation::'a,X),X)) &    \
\  (! X. member(null_class::'a,X) & subclass(image_(successor_relation::'a,X),X) --> inductive(X)) &     \
\  (inductive(omega)) & \
\  (! Y. inductive(Y) --> subclass(omega::'a,Y)) &  \
\  (member(omega::'a,universal_class)) &    \
\  (! X. equal(domain_of(restrct(element_relation::'a,universal_class,X)),sum_class(X))) & \
\  (! X. member(X::'a,universal_class) --> member(sum_class(X),universal_class)) &  \
\  (! X. equal(complement(image_(element_relation::'a,complement(X))),powerClass(X))) &     \
\  (! U. member(U::'a,universal_class) --> member(powerClass(U),universal_class)) &        \
\  (! Yr Xr. subclass(compos(Yr::'a,Xr),cross_product(universal_class::'a,universal_class))) & \
\  (! Z Yr Xr Y. member(ordered_pair(Y::'a,Z),compos(Yr::'a,Xr)) --> member(Z::'a,image_(Yr::'a,image_(Xr::'a,singleton(Y))))) &     \
\  (! Y Z Yr Xr. member(Z::'a,image_(Yr::'a,image_(Xr::'a,singleton(Y)))) & member(ordered_pair(Y::'a,Z),cross_product(universal_class::'a,universal_class)) --> member(ordered_pair(Y::'a,Z),compos(Yr::'a,Xr))) &  \
\  (! X. single_valued_class(X) --> subclass(compos(X::'a,inverse(X)),identity_relation)) &        \
\  (! X. subclass(compos(X::'a,inverse(X)),identity_relation) --> single_valued_class(X)) &        \
\  (! Xf. function(Xf) --> subclass(Xf::'a,cross_product(universal_class::'a,universal_class))) &       \
\  (! Xf. function(Xf) --> subclass(compos(Xf::'a,inverse(Xf)),identity_relation)) &       \
\  (! Xf. subclass(Xf::'a,cross_product(universal_class::'a,universal_class)) & subclass(compos(Xf::'a,inverse(Xf)),identity_relation) --> function(Xf)) & \
\  (! Xf X. function(Xf) & member(X::'a,universal_class) --> member(image_(Xf::'a,X),universal_class)) & \
\  (! X. equal(X::'a,null_class) | member(regular(X),X)) & \
\  (! X. equal(X::'a,null_class) | equal(intersection(X::'a,regular(X)),null_class)) & \
\  (! Xf Y. equal(sum_class(image_(Xf::'a,singleton(Y))),apply(Xf::'a,Y))) &     \
\  (function(choice)) & \
\  (! Y. member(Y::'a,universal_class) --> equal(Y::'a,null_class) | member(apply(choice::'a,Y),Y)) &      \
\  (! Xf. one_to_one(Xf) --> function(Xf)) &    \
\  (! Xf. one_to_one(Xf) --> function(inverse(Xf))) &   \
\  (! Xf. function(inverse(Xf)) & function(Xf) --> one_to_one(Xf)) &    \
\  (equal(intersection(cross_product(universal_class::'a,universal_class),intersection(cross_product(universal_class::'a,universal_class),complement(compos(complement(element_relation),inverse(element_relation))))),subset_relation)) &     \
\  (equal(intersection(inverse(subset_relation),subset_relation),identity_relation)) &  \
\  (! Xr. equal(complement(domain_of(intersection(Xr::'a,identity_relation))),diagonalise(Xr))) &   \
\  (! X. equal(intersection(domain_of(X),diagonalise(compos(inverse(element_relation),X))),cantor(X))) &       \
\  (! Xf. operation(Xf) --> function(Xf)) &     \
\  (! Xf. operation(Xf) --> equal(cross_product(domain_of(domain_of(Xf)),domain_of(domain_of(Xf))),domain_of(Xf))) &    \
\  (! Xf. operation(Xf) --> subclass(range_of(Xf),domain_of(domain_of(Xf)))) &  \
\  (! Xf. function(Xf) & equal(cross_product(domain_of(domain_of(Xf)),domain_of(domain_of(Xf))),domain_of(Xf)) & subclass(range_of(Xf),domain_of(domain_of(Xf))) --> operation(Xf)) &   \
\  (! Xf1 Xf2 Xh. compatible(Xh::'a,Xf1,Xf2) --> function(Xh)) &    \
\  (! Xf2 Xf1 Xh. compatible(Xh::'a,Xf1,Xf2) --> equal(domain_of(domain_of(Xf1)),domain_of(Xh))) &  \
\  (! Xf1 Xh Xf2. compatible(Xh::'a,Xf1,Xf2) --> subclass(range_of(Xh),domain_of(domain_of(Xf2)))) &        \
\  (! Xh Xh1 Xf1 Xf2. function(Xh) & equal(domain_of(domain_of(Xf1)),domain_of(Xh)) & subclass(range_of(Xh),domain_of(domain_of(Xf2))) --> compatible(Xh1::'a,Xf1,Xf2)) &   \
\  (! Xh Xf2 Xf1. homomorphism(Xh::'a,Xf1,Xf2) --> operation(Xf1)) &        \
\  (! Xh Xf1 Xf2. homomorphism(Xh::'a,Xf1,Xf2) --> operation(Xf2)) &        \
\  (! Xh Xf1 Xf2. homomorphism(Xh::'a,Xf1,Xf2) --> compatible(Xh::'a,Xf1,Xf2)) &        \
\  (! Xf2 Xh Xf1 X Y. homomorphism(Xh::'a,Xf1,Xf2) & member(ordered_pair(X::'a,Y),domain_of(Xf1)) --> equal(apply(Xf2::'a,ordered_pair(apply(Xh::'a,X),apply(Xh::'a,Y))),apply(Xh::'a,apply(Xf1::'a,ordered_pair(X::'a,Y))))) & \
\  (! Xh Xf1 Xf2. operation(Xf1) & operation(Xf2) & compatible(Xh::'a,Xf1,Xf2) --> member(ordered_pair(not_homomorphism1(Xh::'a,Xf1,Xf2),not_homomorphism2(Xh::'a,Xf1,Xf2)),domain_of(Xf1)) | homomorphism(Xh::'a,Xf1,Xf2)) &  \
\  (! Xh Xf1 Xf2. operation(Xf1) & operation(Xf2) & compatible(Xh::'a,Xf1,Xf2) & equal(apply(Xf2::'a,ordered_pair(apply(Xh::'a,not_homomorphism1(Xh::'a,Xf1,Xf2)),apply(Xh::'a,not_homomorphism2(Xh::'a,Xf1,Xf2)))),apply(Xh::'a,apply(Xf1::'a,ordered_pair(not_homomorphism1(Xh::'a,Xf1,Xf2),not_homomorphism2(Xh::'a,Xf1,Xf2))))) --> homomorphism(Xh::'a,Xf1,Xf2)) &     \
\  (! D E F'. equal(D::'a,E) --> equal(apply(D::'a,F'),apply(E::'a,F'))) &  \
\  (! G I' H. equal(G::'a,H) --> equal(apply(I'::'a,G),apply(I'::'a,H))) &  \
\  (! J K'. equal(J::'a,K') --> equal(cantor(J),cantor(K'))) &      \
\  (! L M. equal(L::'a,M) --> equal(complement(L),complement(M))) & \
\  (! N O_ P. equal(N::'a,O_) --> equal(compos(N::'a,P),compos(O_::'a,P))) & \
\  (! Q S' R. equal(Q::'a,R) --> equal(compos(S'::'a,Q),compos(S'::'a,R))) &      \
\  (! T' U V. equal(T'::'a,U) --> equal(cross_product(T'::'a,V),cross_product(U::'a,V))) &  \
\  (! W Y X. equal(W::'a,X) --> equal(cross_product(Y::'a,W),cross_product(Y::'a,X))) &     \
\  (! Z A1. equal(Z::'a,A1) --> equal(diagonalise(Z),diagonalise(A1))) &    \
\  (! B1 C1 D1. equal(B1::'a,C1) --> equal(difference(B1::'a,D1),difference(C1::'a,D1))) &  \
\  (! E1 G1 F1. equal(E1::'a,F1) --> equal(difference(G1::'a,E1),difference(G1::'a,F1))) &  \
\  (! H1 I1 J1 K1. equal(H1::'a,I1) --> equal(domain(H1::'a,J1,K1),domain(I1::'a,J1,K1))) & \
\  (! L1 N1 M1 O1. equal(L1::'a,M1) --> equal(domain(N1::'a,L1,O1),domain(N1::'a,M1,O1))) & \
\  (! P1 R1 S1 Q1. equal(P1::'a,Q1) --> equal(domain(R1::'a,S1,P1),domain(R1::'a,S1,Q1))) & \
\  (! T1 U1. equal(T1::'a,U1) --> equal(domain_of(T1),domain_of(U1))) &     \
\  (! V1 W1. equal(V1::'a,W1) --> equal(first(V1),first(W1))) &     \
\  (! X1 Y1. equal(X1::'a,Y1) --> equal(flip(X1),flip(Y1))) &       \
\  (! Z1 A2 B2. equal(Z1::'a,A2) --> equal(image_(Z1::'a,B2),image_(A2::'a,B2))) &    \
\  (! C2 E2 D2. equal(C2::'a,D2) --> equal(image_(E2::'a,C2),image_(E2::'a,D2))) &    \
\  (! F2 G2 H2. equal(F2::'a,G2) --> equal(intersection(F2::'a,H2),intersection(G2::'a,H2))) &      \
\  (! I2 K2 J2. equal(I2::'a,J2) --> equal(intersection(K2::'a,I2),intersection(K2::'a,J2))) &      \
\  (! L2 M2. equal(L2::'a,M2) --> equal(inverse(L2),inverse(M2))) & \
\  (! N2 O2 P2 Q2. equal(N2::'a,O2) --> equal(not_homomorphism1(N2::'a,P2,Q2),not_homomorphism1(O2::'a,P2,Q2))) &   \
\  (! R2 T2 S2 U2. equal(R2::'a,S2) --> equal(not_homomorphism1(T2::'a,R2,U2),not_homomorphism1(T2::'a,S2,U2))) &   \
\  (! V2 X2 Y2 W2. equal(V2::'a,W2) --> equal(not_homomorphism1(X2::'a,Y2,V2),not_homomorphism1(X2::'a,Y2,W2))) &   \
\  (! Z2 A3 B3 C3. equal(Z2::'a,A3) --> equal(not_homomorphism2(Z2::'a,B3,C3),not_homomorphism2(A3::'a,B3,C3))) &   \
\  (! D3 F3 E3 G3. equal(D3::'a,E3) --> equal(not_homomorphism2(F3::'a,D3,G3),not_homomorphism2(F3::'a,E3,G3))) &   \
\  (! H3 J3 K3 I3. equal(H3::'a,I3) --> equal(not_homomorphism2(J3::'a,K3,H3),not_homomorphism2(J3::'a,K3,I3))) &   \
\  (! L3 M3 N3. equal(L3::'a,M3) --> equal(not_subclass_element(L3::'a,N3),not_subclass_element(M3::'a,N3))) &      \
\  (! O3 Q3 P3. equal(O3::'a,P3) --> equal(not_subclass_element(Q3::'a,O3),not_subclass_element(Q3::'a,P3))) &      \
\  (! R3 S3 T3. equal(R3::'a,S3) --> equal(ordered_pair(R3::'a,T3),ordered_pair(S3::'a,T3))) &      \
\  (! U3 W3 V3. equal(U3::'a,V3) --> equal(ordered_pair(W3::'a,U3),ordered_pair(W3::'a,V3))) &      \
\  (! X3 Y3. equal(X3::'a,Y3) --> equal(powerClass(X3),powerClass(Y3))) & \
\  (! Z3 A4 B4 C4. equal(Z3::'a,A4) --> equal(rng(Z3::'a,B4,C4),rng(A4::'a,B4,C4))) &   \
\  (! D4 F4 E4 G4. equal(D4::'a,E4) --> equal(rng(F4::'a,D4,G4),rng(F4::'a,E4,G4))) &   \
\  (! H4 J4 K4 I4. equal(H4::'a,I4) --> equal(rng(J4::'a,K4,H4),rng(J4::'a,K4,I4))) &   \
\  (! L4 M4. equal(L4::'a,M4) --> equal(range_of(L4),range_of(M4))) &       \
\  (! N4 O4. equal(N4::'a,O4) --> equal(regular(N4),regular(O4))) & \
\  (! P4 Q4 R4 S4. equal(P4::'a,Q4) --> equal(restrct(P4::'a,R4,S4),restrct(Q4::'a,R4,S4))) &     \
\  (! T4 V4 U4 W4. equal(T4::'a,U4) --> equal(restrct(V4::'a,T4,W4),restrct(V4::'a,U4,W4))) &     \
\  (! X4 Z4 A5 Y4. equal(X4::'a,Y4) --> equal(restrct(Z4::'a,A5,X4),restrct(Z4::'a,A5,Y4))) &     \
\  (! B5 C5. equal(B5::'a,C5) --> equal(rotate(B5),rotate(C5))) &   \
\  (! D5 E5. equal(D5::'a,E5) --> equal(second(D5),second(E5))) &   \
\  (! F5 G5. equal(F5::'a,G5) --> equal(singleton(F5),singleton(G5))) &     \
\  (! H5 I5. equal(H5::'a,I5) --> equal(successor(H5),successor(I5))) &     \
\  (! J5 K5. equal(J5::'a,K5) --> equal(sum_class(J5),sum_class(K5))) &     \
\  (! L5 M5 N5. equal(L5::'a,M5) --> equal(union(L5::'a,N5),union(M5::'a,N5))) &    \
\  (! O5 Q5 P5. equal(O5::'a,P5) --> equal(union(Q5::'a,O5),union(Q5::'a,P5))) &    \
\  (! R5 S5 T5. equal(R5::'a,S5) --> equal(unordered_pair(R5::'a,T5),unordered_pair(S5::'a,T5))) &  \
\  (! U5 W5 V5. equal(U5::'a,V5) --> equal(unordered_pair(W5::'a,U5),unordered_pair(W5::'a,V5))) &  \
\  (! X5 Y5 Z5 A6. equal(X5::'a,Y5) & compatible(X5::'a,Z5,A6) --> compatible(Y5::'a,Z5,A6)) &      \
\  (! B6 D6 C6 E6. equal(B6::'a,C6) & compatible(D6::'a,B6,E6) --> compatible(D6::'a,C6,E6)) &      \
\  (! F6 H6 I6 G6. equal(F6::'a,G6) & compatible(H6::'a,I6,F6) --> compatible(H6::'a,I6,G6)) &      \
\  (! J6 K6. equal(J6::'a,K6) & function(J6) --> function(K6)) &    \
\  (! L6 M6 N6 O6. equal(L6::'a,M6) & homomorphism(L6::'a,N6,O6) --> homomorphism(M6::'a,N6,O6)) &  \
\  (! P6 R6 Q6 S6. equal(P6::'a,Q6) & homomorphism(R6::'a,P6,S6) --> homomorphism(R6::'a,Q6,S6)) &  \
\  (! T6 V6 W6 U6. equal(T6::'a,U6) & homomorphism(V6::'a,W6,T6) --> homomorphism(V6::'a,W6,U6)) &  \
\  (! X6 Y6. equal(X6::'a,Y6) & inductive(X6) --> inductive(Y6)) &  \
\  (! Z6 A7 B7. equal(Z6::'a,A7) & member(Z6::'a,B7) --> member(A7::'a,B7)) &       \
\  (! C7 E7 D7. equal(C7::'a,D7) & member(E7::'a,C7) --> member(E7::'a,D7)) &       \
\  (! F7 G7. equal(F7::'a,G7) & one_to_one(F7) --> one_to_one(G7)) &        \
\  (! H7 I7. equal(H7::'a,I7) & operation(H7) --> operation(I7)) &  \
\  (! J7 K7. equal(J7::'a,K7) & single_valued_class(J7) --> single_valued_class(K7)) &      \
\  (! L7 M7 N7. equal(L7::'a,M7) & subclass(L7::'a,N7) --> subclass(M7::'a,N7)) &   \
\  (! O7 Q7 P7. equal(O7::'a,P7) & subclass(Q7::'a,O7) --> subclass(Q7::'a,P7)) &   \
\  (! X. subclass(compose_class(X),cross_product(universal_class::'a,universal_class))) &   \
\  (! X Y Z. member(ordered_pair(Y::'a,Z),compose_class(X)) --> equal(compos(X::'a,Y),Z)) &    \
\  (! Y Z X. member(ordered_pair(Y::'a,Z),cross_product(universal_class::'a,universal_class)) & equal(compos(X::'a,Y),Z) --> member(ordered_pair(Y::'a,Z),compose_class(X))) & \
\  (subclass(composition_function::'a,cross_product(universal_class::'a,cross_product(universal_class::'a,universal_class)))) &     \
\  (! X Y Z. member(ordered_pair(X::'a,ordered_pair(Y::'a,Z)),composition_function) --> equal(compos(X::'a,Y),Z)) &        \
\  (! X Y. member(ordered_pair(X::'a,Y),cross_product(universal_class::'a,universal_class)) --> member(ordered_pair(X::'a,ordered_pair(Y::'a,compos(X::'a,Y))),composition_function)) &    \
\  (subclass(domain_relation::'a,cross_product(universal_class::'a,universal_class))) & \
\  (! X Y. member(ordered_pair(X::'a,Y),domain_relation) --> equal(domain_of(X),Y)) &       \
\  (! X. member(X::'a,universal_class) --> member(ordered_pair(X::'a,domain_of(X)),domain_relation)) &  \
\  (! X. equal(first(not_subclass_element(compos(X::'a,inverse(X)),identity_relation)),single_valued1(X))) &       \
\  (! X. equal(second(not_subclass_element(compos(X::'a,inverse(X)),identity_relation)),single_valued2(X))) &      \
\  (! X. equal(domain(X::'a,image_(inverse(X),singleton(single_valued1(X))),single_valued2(X)),single_valued3(X))) & \
\  (equal(intersection(complement(compos(element_relation::'a,complement(identity_relation))),element_relation),singleton_relation)) &     \
\  (subclass(application_function::'a,cross_product(universal_class::'a,cross_product(universal_class::'a,universal_class)))) &     \
\  (! Z Y X. member(ordered_pair(X::'a,ordered_pair(Y::'a,Z)),application_function) --> member(Y::'a,domain_of(X))) &       \
\  (! X Y Z. member(ordered_pair(X::'a,ordered_pair(Y::'a,Z)),application_function) --> equal(apply(X::'a,Y),Z)) &  \
\  (! Z X Y. member(ordered_pair(X::'a,ordered_pair(Y::'a,Z)),cross_product(universal_class::'a,cross_product(universal_class::'a,universal_class))) & member(Y::'a,domain_of(X)) --> member(ordered_pair(X::'a,ordered_pair(Y::'a,apply(X::'a,Y))),application_function)) &    \
\  (! X Y Xf. maps(Xf::'a,X,Y) --> function(Xf)) &  \
\  (! Y Xf X. maps(Xf::'a,X,Y) --> equal(domain_of(Xf),X)) &        \
\  (! X Xf Y. maps(Xf::'a,X,Y) --> subclass(range_of(Xf),Y)) &      \
\  (! Xf Y. function(Xf) & subclass(range_of(Xf),Y) --> maps(Xf::'a,domain_of(Xf),Y)) &     \
\  (! L M. equal(L::'a,M) --> equal(compose_class(L),compose_class(M))) &   \
\  (! N2 O2. equal(N2::'a,O2) --> equal(single_valued1(N2),single_valued1(O2))) &   \
\  (! P2 Q2. equal(P2::'a,Q2) --> equal(single_valued2(P2),single_valued2(Q2))) &   \
\  (! R2 S2. equal(R2::'a,S2) --> equal(single_valued3(R2),single_valued3(S2))) &   \
\  (! X2 Y2 Z2 A3. equal(X2::'a,Y2) & maps(X2::'a,Z2,A3) --> maps(Y2::'a,Z2,A3)) &  \
\  (! B3 D3 C3 E3. equal(B3::'a,C3) & maps(D3::'a,B3,E3) --> maps(D3::'a,C3,E3)) &  \
\  (! F3 H3 I3 G3. equal(F3::'a,G3) & maps(H3::'a,I3,F3) --> maps(H3::'a,I3,G3)) &  \
\  (! X. equal(union(X::'a,inverse(X)),symmetrization_of(X))) &     \
\  (! X Y. irreflexive(X::'a,Y) --> subclass(restrct(X::'a,Y,Y),complement(identity_relation))) &      \
\  (! X Y. subclass(restrct(X::'a,Y,Y),complement(identity_relation)) --> irreflexive(X::'a,Y)) &      \
\  (! Y X. connected(X::'a,Y) --> subclass(cross_product(Y::'a,Y),union(identity_relation::'a,symmetrization_of(X)))) &     \
\  (! X Y. subclass(cross_product(Y::'a,Y),union(identity_relation::'a,symmetrization_of(X))) --> connected(X::'a,Y)) &     \
\  (! Xr Y. transitive(Xr::'a,Y) --> subclass(compos(restrct(Xr::'a,Y,Y),restrct(Xr::'a,Y,Y)),restrct(Xr::'a,Y,Y))) &       \
\  (! Xr Y. subclass(compos(restrct(Xr::'a,Y,Y),restrct(Xr::'a,Y,Y)),restrct(Xr::'a,Y,Y)) --> transitive(Xr::'a,Y)) &       \
\  (! Xr Y. asymmetric(Xr::'a,Y) --> equal(restrct(intersection(Xr::'a,inverse(Xr)),Y,Y),null_class)) &        \
\  (! Xr Y. equal(restrct(intersection(Xr::'a,inverse(Xr)),Y,Y),null_class) --> asymmetric(Xr::'a,Y)) &        \
\  (! Xr Y Z. equal(segment(Xr::'a,Y,Z),domain_of(restrct(Xr::'a,Y,singleton(Z))))) &  \
\  (! X Y. well_ordering(X::'a,Y) --> connected(X::'a,Y)) &     \
\  (! Y Xr U. well_ordering(Xr::'a,Y) & subclass(U::'a,Y) --> equal(U::'a,null_class) | member(least(Xr::'a,U),U)) &   \
\  (! Y V Xr U. well_ordering(Xr::'a,Y) & subclass(U::'a,Y) & member(V::'a,U) --> member(least(Xr::'a,U),U)) &  \
\  (! Y Xr U. well_ordering(Xr::'a,Y) & subclass(U::'a,Y) --> equal(segment(Xr::'a,U,least(Xr::'a,U)),null_class)) &    \
\  (! Y V U Xr. ~(well_ordering(Xr::'a,Y) & subclass(U::'a,Y) & member(V::'a,U) & member(ordered_pair(V::'a,least(Xr::'a,U)),Xr))) &        \
\  (! Xr Y. connected(Xr::'a,Y) & equal(not_well_ordering(Xr::'a,Y),null_class) --> well_ordering(Xr::'a,Y)) &      \
\  (! Xr Y. connected(Xr::'a,Y) --> subclass(not_well_ordering(Xr::'a,Y),Y) | well_ordering(Xr::'a,Y)) &   \
\  (! V Xr Y. member(V::'a,not_well_ordering(Xr::'a,Y)) & equal(segment(Xr::'a,not_well_ordering(Xr::'a,Y),V),null_class) & connected(Xr::'a,Y) --> well_ordering(Xr::'a,Y)) &  \
\  (! Xr Y Z. section(Xr::'a,Y,Z) --> subclass(Y::'a,Z)) &      \
\  (! Xr Z Y. section(Xr::'a,Y,Z) --> subclass(domain_of(restrct(Xr::'a,Z,Y)),Y)) &    \
\  (! Xr Y Z. subclass(Y::'a,Z) & subclass(domain_of(restrct(Xr::'a,Z,Y)),Y) --> section(Xr::'a,Y,Z)) &    \
\  (! X. member(X::'a,ordinal_numbers) --> well_ordering(element_relation::'a,X)) &     \
\  (! X. member(X::'a,ordinal_numbers) --> subclass(sum_class(X),X)) &      \
\  (! X. well_ordering(element_relation::'a,X) & subclass(sum_class(X),X) & member(X::'a,universal_class) --> member(X::'a,ordinal_numbers)) &      \
\  (! X. well_ordering(element_relation::'a,X) & subclass(sum_class(X),X) --> member(X::'a,ordinal_numbers) | equal(X::'a,ordinal_numbers)) &      \
\  (equal(union(singleton(null_class),image_(successor_relation::'a,ordinal_numbers)),kind_1_ordinals)) &    \
\  (equal(intersection(complement(kind_1_ordinals),ordinal_numbers),limit_ordinals)) &  \
\  (! X. subclass(rest_of(X),cross_product(universal_class::'a,universal_class))) & \
\  (! V U X. member(ordered_pair(U::'a,V),rest_of(X)) --> member(U::'a,domain_of(X))) & \
\  (! X U V. member(ordered_pair(U::'a,V),rest_of(X)) --> equal(restrct(X::'a,U,universal_class),V)) & \
\  (! U V X. member(U::'a,domain_of(X)) & equal(restrct(X::'a,U,universal_class),V) --> member(ordered_pair(U::'a,V),rest_of(X))) &        \
\  (subclass(rest_relation::'a,cross_product(universal_class::'a,universal_class))) &   \
\  (! X Y. member(ordered_pair(X::'a,Y),rest_relation) --> equal(rest_of(X),Y)) &   \
\  (! X. member(X::'a,universal_class) --> member(ordered_pair(X::'a,rest_of(X)),rest_relation)) &      \
\  (! X Z. member(X::'a,recursion_equation_functions(Z)) --> function(Z)) & \
\  (! Z X. member(X::'a,recursion_equation_functions(Z)) --> function(X)) & \
\  (! Z X. member(X::'a,recursion_equation_functions(Z)) --> member(domain_of(X),ordinal_numbers)) &        \
\  (! Z X. member(X::'a,recursion_equation_functions(Z)) --> equal(compos(Z::'a,rest_of(X)),X)) &      \
\  (! X Z. function(Z) & function(X) & member(domain_of(X),ordinal_numbers) & equal(compos(Z::'a,rest_of(X)),X) --> member(X::'a,recursion_equation_functions(Z))) &   \
\  (subclass(union_of_range_map::'a,cross_product(universal_class::'a,universal_class))) &      \
\  (! X Y. member(ordered_pair(X::'a,Y),union_of_range_map) --> equal(sum_class(range_of(X)),Y)) &  \
\  (! X Y. member(ordered_pair(X::'a,Y),cross_product(universal_class::'a,universal_class)) & equal(sum_class(range_of(X)),Y) --> member(ordered_pair(X::'a,Y),union_of_range_map)) &       \
\  (! X Y. equal(apply(recursion(X::'a,successor_relation,union_of_range_map),Y),ordinal_add(X::'a,Y))) &       \
\  (! X Y. equal(recursion(null_class::'a,apply(add_relation::'a,X),union_of_range_map),ordinal_multiply(X::'a,Y))) &       \
\  (! X. member(X::'a,omega) --> equal(integer_of(X),X)) &  \
\  (! X. member(X::'a,omega) | equal(integer_of(X),null_class)) &  \
\  (! D E. equal(D::'a,E) --> equal(integer_of(D),integer_of(E))) & \
\  (! F' G H. equal(F'::'a,G) --> equal(least(F'::'a,H),least(G::'a,H))) &  \
\  (! I' K' J. equal(I'::'a,J) --> equal(least(K'::'a,I'),least(K'::'a,J))) &       \
\  (! L M N. equal(L::'a,M) --> equal(not_well_ordering(L::'a,N),not_well_ordering(M::'a,N))) &     \
\  (! O_ Q P. equal(O_::'a,P) --> equal(not_well_ordering(Q::'a,O_),not_well_ordering(Q::'a,P))) &     \
\  (! R S' T'. equal(R::'a,S') --> equal(ordinal_add(R::'a,T'),ordinal_add(S'::'a,T'))) &   \
\  (! U W V. equal(U::'a,V) --> equal(ordinal_add(W::'a,U),ordinal_add(W::'a,V))) & \
\  (! X Y Z. equal(X::'a,Y) --> equal(ordinal_multiply(X::'a,Z),ordinal_multiply(Y::'a,Z))) &       \
\  (! A1 C1 B1. equal(A1::'a,B1) --> equal(ordinal_multiply(C1::'a,A1),ordinal_multiply(C1::'a,B1))) &      \
\  (! F1 G1 H1 I1. equal(F1::'a,G1) --> equal(recursion(F1::'a,H1,I1),recursion(G1::'a,H1,I1))) &   \
\  (! J1 L1 K1 M1. equal(J1::'a,K1) --> equal(recursion(L1::'a,J1,M1),recursion(L1::'a,K1,M1))) &   \
\  (! N1 P1 Q1 O1. equal(N1::'a,O1) --> equal(recursion(P1::'a,Q1,N1),recursion(P1::'a,Q1,O1))) &   \
\  (! R1 S1. equal(R1::'a,S1) --> equal(recursion_equation_functions(R1),recursion_equation_functions(S1))) &       \
\  (! T1 U1. equal(T1::'a,U1) --> equal(rest_of(T1),rest_of(U1))) & \
\  (! V1 W1 X1 Y1. equal(V1::'a,W1) --> equal(segment(V1::'a,X1,Y1),segment(W1::'a,X1,Y1))) &       \
\  (! Z1 B2 A2 C2. equal(Z1::'a,A2) --> equal(segment(B2::'a,Z1,C2),segment(B2::'a,A2,C2))) &       \
\  (! D2 F2 G2 E2. equal(D2::'a,E2) --> equal(segment(F2::'a,G2,D2),segment(F2::'a,G2,E2))) &       \
\  (! H2 I2. equal(H2::'a,I2) --> equal(symmetrization_of(H2),symmetrization_of(I2))) &     \
\  (! J2 K2 L2. equal(J2::'a,K2) & asymmetric(J2::'a,L2) --> asymmetric(K2::'a,L2)) &       \
\  (! M2 O2 N2. equal(M2::'a,N2) & asymmetric(O2::'a,M2) --> asymmetric(O2::'a,N2)) &       \
\  (! P2 Q2 R2. equal(P2::'a,Q2) & connected(P2::'a,R2) --> connected(Q2::'a,R2)) & \
\  (! S2 U2 T2. equal(S2::'a,T2) & connected(U2::'a,S2) --> connected(U2::'a,T2)) & \
\  (! V2 W2 X2. equal(V2::'a,W2) & irreflexive(V2::'a,X2) --> irreflexive(W2::'a,X2)) &     \
\  (! Y2 A3 Z2. equal(Y2::'a,Z2) & irreflexive(A3::'a,Y2) --> irreflexive(A3::'a,Z2)) &     \
\  (! B3 C3 D3 E3. equal(B3::'a,C3) & section(B3::'a,D3,E3) --> section(C3::'a,D3,E3)) &    \
\  (! F3 H3 G3 I3. equal(F3::'a,G3) & section(H3::'a,F3,I3) --> section(H3::'a,G3,I3)) &    \
\  (! J3 L3 M3 K3. equal(J3::'a,K3) & section(L3::'a,M3,J3) --> section(L3::'a,M3,K3)) &    \
\  (! N3 O3 P3. equal(N3::'a,O3) & transitive(N3::'a,P3) --> transitive(O3::'a,P3)) &       \
\  (! Q3 S3 R3. equal(Q3::'a,R3) & transitive(S3::'a,Q3) --> transitive(S3::'a,R3)) &       \
\  (! T3 U3 V3. equal(T3::'a,U3) & well_ordering(T3::'a,V3) --> well_ordering(U3::'a,V3)) & \
\  (! W3 Y3 X3. equal(W3::'a,X3) & well_ordering(Y3::'a,W3) --> well_ordering(Y3::'a,X3)) & \
\  (~function(z)) &     \
\  (~equal(recursion_equation_functions(z),null_class)) --> False",
  meson_tac);


(*4868 inferences so far.  Searching to depth 12.  4.3 secs*)
val PLA002_1 = prove_hard
 ("(! Situation1 Situation2. warm(Situation1) | cold(Situation2)) &    \
\  (! Situation. at(a::'a,Situation) --> at(b::'a,walk(b::'a,Situation))) & \
\  (! Situation. at(a::'a,Situation) --> at(b::'a,drive(b::'a,Situation))) &        \
\  (! Situation. at(b::'a,Situation) --> at(a::'a,walk(a::'a,Situation))) & \
\  (! Situation. at(b::'a,Situation) --> at(a::'a,drive(a::'a,Situation))) &        \
\  (! Situation. cold(Situation) & at(b::'a,Situation) --> at(c::'a,skate(c::'a,Situation))) &      \
\  (! Situation. cold(Situation) & at(c::'a,Situation) --> at(b::'a,skate(b::'a,Situation))) &      \
\  (! Situation. warm(Situation) & at(b::'a,Situation) --> at(d::'a,climb(d::'a,Situation))) &      \
\  (! Situation. warm(Situation) & at(d::'a,Situation) --> at(b::'a,climb(b::'a,Situation))) &      \
\  (! Situation. at(c::'a,Situation) --> at(d::'a,go(d::'a,Situation))) &   \
\  (! Situation. at(d::'a,Situation) --> at(c::'a,go(c::'a,Situation))) &   \
\  (! Situation. at(c::'a,Situation) --> at(e::'a,go(e::'a,Situation))) &   \
\  (! Situation. at(e::'a,Situation) --> at(c::'a,go(c::'a,Situation))) &   \
\  (! Situation. at(d::'a,Situation) --> at(f::'a,go(f::'a,Situation))) &   \
\  (! Situation. at(f::'a,Situation) --> at(d::'a,go(d::'a,Situation))) &   \
\  (at(f::'a,s0)) & \
\  (! S'. ~at(a::'a,S')) --> False",
  meson_tac);

(*190 inferences so far.  Searching to depth 10.  0.6 secs*)
val PLA006_1 = prove
 ("(! X Y State. holds(X::'a,State) & holds(Y::'a,State) --> holds(and'(X::'a,Y),State)) &  \
\  (! State X. holds(empty::'a,State) & holds(clear(X),State) & differ(X::'a,table) --> holds(holding(X),do(pickup(X),State))) &        \
\  (! Y X State. holds(on(X::'a,Y),State) & holds(clear(X),State) & holds(empty::'a,State) --> holds(clear(Y),do(pickup(X),State))) &   \
\  (! Y State X Z. holds(on(X::'a,Y),State) & differ(X::'a,Z) --> holds(on(X::'a,Y),do(pickup(Z),State))) & \
\  (! State X Z. holds(clear(X),State) & differ(X::'a,Z) --> holds(clear(X),do(pickup(Z),State))) & \
\  (! X Y State. holds(holding(X),State) & holds(clear(Y),State) --> holds(empty::'a,do(putdown(X::'a,Y),State))) &     \
\  (! X Y State. holds(holding(X),State) & holds(clear(Y),State) --> holds(on(X::'a,Y),do(putdown(X::'a,Y),State))) &   \
\  (! X Y State. holds(holding(X),State) & holds(clear(Y),State) --> holds(clear(X),do(putdown(X::'a,Y),State))) &  \
\  (! Z W X Y State. holds(on(X::'a,Y),State) --> holds(on(X::'a,Y),do(putdown(Z::'a,W),State))) &  \
\  (! X State Z Y. holds(clear(Z),State) & differ(Z::'a,Y) --> holds(clear(Z),do(putdown(X::'a,Y),State))) &    \
\  (! Y X. differ(Y::'a,X) --> differ(X::'a,Y)) &       \
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
\  (holds(empty::'a,s0)) &  \
\  (! State. holds(clear(table),State)) &       \
\  (! State. ~holds(on(c::'a,table),State)) --> False",
  meson_tac);

(*190 inferences so far.  Searching to depth 10.  0.5 secs*)
val PLA017_1 = prove
 ("(! X Y State. holds(X::'a,State) & holds(Y::'a,State) --> holds(and'(X::'a,Y),State)) &  \
\  (! State X. holds(empty::'a,State) & holds(clear(X),State) & differ(X::'a,table) --> holds(holding(X),do(pickup(X),State))) &        \
\  (! Y X State. holds(on(X::'a,Y),State) & holds(clear(X),State) & holds(empty::'a,State) --> holds(clear(Y),do(pickup(X),State))) &   \
\  (! Y State X Z. holds(on(X::'a,Y),State) & differ(X::'a,Z) --> holds(on(X::'a,Y),do(pickup(Z),State))) & \
\  (! State X Z. holds(clear(X),State) & differ(X::'a,Z) --> holds(clear(X),do(pickup(Z),State))) & \
\  (! X Y State. holds(holding(X),State) & holds(clear(Y),State) --> holds(empty::'a,do(putdown(X::'a,Y),State))) &     \
\  (! X Y State. holds(holding(X),State) & holds(clear(Y),State) --> holds(on(X::'a,Y),do(putdown(X::'a,Y),State))) &   \
\  (! X Y State. holds(holding(X),State) & holds(clear(Y),State) --> holds(clear(X),do(putdown(X::'a,Y),State))) &  \
\  (! Z W X Y State. holds(on(X::'a,Y),State) --> holds(on(X::'a,Y),do(putdown(Z::'a,W),State))) &  \
\  (! X State Z Y. holds(clear(Z),State) & differ(Z::'a,Y) --> holds(clear(Z),do(putdown(X::'a,Y),State))) &    \
\  (! Y X. differ(Y::'a,X) --> differ(X::'a,Y)) &       \
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
\  (holds(empty::'a,s0)) &  \
\  (! State. holds(clear(table),State)) &       \
\  (! State. ~holds(on(a::'a,c),State)) --> False",
  meson_tac);

(*13732 inferences so far.  Searching to depth 16.  9.8 secs*)
val PLA022_1 = prove_hard
 ("(! X Y State. holds(X::'a,State) & holds(Y::'a,State) --> holds(and'(X::'a,Y),State)) &  \
\  (! State X. holds(empty::'a,State) & holds(clear(X),State) & differ(X::'a,table) --> holds(holding(X),do(pickup(X),State))) &        \
\  (! Y X State. holds(on(X::'a,Y),State) & holds(clear(X),State) & holds(empty::'a,State) --> holds(clear(Y),do(pickup(X),State))) &   \
\  (! Y State X Z. holds(on(X::'a,Y),State) & differ(X::'a,Z) --> holds(on(X::'a,Y),do(pickup(Z),State))) & \
\  (! State X Z. holds(clear(X),State) & differ(X::'a,Z) --> holds(clear(X),do(pickup(Z),State))) & \
\  (! X Y State. holds(holding(X),State) & holds(clear(Y),State) --> holds(empty::'a,do(putdown(X::'a,Y),State))) &     \
\  (! X Y State. holds(holding(X),State) & holds(clear(Y),State) --> holds(on(X::'a,Y),do(putdown(X::'a,Y),State))) &   \
\  (! X Y State. holds(holding(X),State) & holds(clear(Y),State) --> holds(clear(X),do(putdown(X::'a,Y),State))) &  \
\  (! Z W X Y State. holds(on(X::'a,Y),State) --> holds(on(X::'a,Y),do(putdown(Z::'a,W),State))) &  \
\  (! X State Z Y. holds(clear(Z),State) & differ(Z::'a,Y) --> holds(clear(Z),do(putdown(X::'a,Y),State))) &    \
\  (! Y X. differ(Y::'a,X) --> differ(X::'a,Y)) &       \
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
\  (holds(empty::'a,s0)) &  \
\  (! State. holds(clear(table),State)) &       \
\  (! State. ~holds(and'(on(c::'a,d),on(a::'a,c)),State)) --> False",
  meson_tac);

(*217 inferences so far.  Searching to depth 13.  0.7 secs*)
val PLA022_2 = prove
 ("(! X Y State. holds(X::'a,State) & holds(Y::'a,State) --> holds(and'(X::'a,Y),State)) &  \
\  (! State X. holds(empty::'a,State) & holds(clear(X),State) & differ(X::'a,table) --> holds(holding(X),do(pickup(X),State))) &        \
\  (! Y X State. holds(on(X::'a,Y),State) & holds(clear(X),State) & holds(empty::'a,State) --> holds(clear(Y),do(pickup(X),State))) &   \
\  (! Y State X Z. holds(on(X::'a,Y),State) & differ(X::'a,Z) --> holds(on(X::'a,Y),do(pickup(Z),State))) & \
\  (! State X Z. holds(clear(X),State) & differ(X::'a,Z) --> holds(clear(X),do(pickup(Z),State))) & \
\  (! X Y State. holds(holding(X),State) & holds(clear(Y),State) --> holds(empty::'a,do(putdown(X::'a,Y),State))) &     \
\  (! X Y State. holds(holding(X),State) & holds(clear(Y),State) --> holds(on(X::'a,Y),do(putdown(X::'a,Y),State))) &   \
\  (! X Y State. holds(holding(X),State) & holds(clear(Y),State) --> holds(clear(X),do(putdown(X::'a,Y),State))) &  \
\  (! Z W X Y State. holds(on(X::'a,Y),State) --> holds(on(X::'a,Y),do(putdown(Z::'a,W),State))) &  \
\  (! X State Z Y. holds(clear(Z),State) & differ(Z::'a,Y) --> holds(clear(Z),do(putdown(X::'a,Y),State))) &    \
\  (! Y X. differ(Y::'a,X) --> differ(X::'a,Y)) &       \
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
\  (holds(empty::'a,s0)) &  \
\  (! State. holds(clear(table),State)) &       \
\  (! State. ~holds(and'(on(a::'a,c),on(c::'a,d)),State)) --> False",
  meson_tac);

(*948 inferences so far.  Searching to depth 18.  1.1 secs*)
val PRV001_1 = prove
 ("(! X Y Z. q1(X::'a,Y,Z) & less_or_equal(X::'a,Y) --> q2(X::'a,Y,Z)) &    \
\  (! X Y Z. q1(X::'a,Y,Z) --> less_or_equal(X::'a,Y) | q3(X::'a,Y,Z)) &   \
\  (! Z X Y. q2(X::'a,Y,Z) --> q4(X::'a,Y,Y)) & \
\  (! Z Y X. q3(X::'a,Y,Z) --> q4(X::'a,Y,X)) & \
\  (! X. less_or_equal(X::'a,X)) &  \
\  (! X Y. less_or_equal(X::'a,Y) & less_or_equal(Y::'a,X) --> equal(X::'a,Y)) &    \
\  (! Y X Z. less_or_equal(X::'a,Y) & less_or_equal(Y::'a,Z) --> less_or_equal(X::'a,Z)) &  \
\  (! Y X. less_or_equal(X::'a,Y) | less_or_equal(Y::'a,X)) &  \
\  (! X Y. equal(X::'a,Y) --> less_or_equal(X::'a,Y)) & \
\  (! X Y Z. equal(X::'a,Y) & less_or_equal(X::'a,Z) --> less_or_equal(Y::'a,Z)) &  \
\  (! X Z Y. equal(X::'a,Y) & less_or_equal(Z::'a,X) --> less_or_equal(Z::'a,Y)) &  \
\  (q1(a::'a,b,c)) &        \
\  (! W. ~(q4(a::'a,b,W) & less_or_equal(a::'a,W) & less_or_equal(b::'a,W) & less_or_equal(W::'a,a))) & \
\  (! W. ~(q4(a::'a,b,W) & less_or_equal(a::'a,W) & less_or_equal(b::'a,W) & less_or_equal(W::'a,b))) --> False",
  meson_tac);

(*21 inferences so far.  Searching to depth 5.  0.4 secs*)
val PRV003_1 = prove
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X. equal(predecessor(successor(X)),X)) &  \
\  (! X. equal(successor(predecessor(X)),X)) &  \
\  (! X Y. equal(predecessor(X),predecessor(Y)) --> equal(X::'a,Y)) &       \
\  (! X Y. equal(successor(X),successor(Y)) --> equal(X::'a,Y)) &   \
\  (! X. less_than(predecessor(X),X)) & \
\  (! X. less_than(X::'a,successor(X))) &   \
\  (! X Y Z. less_than(X::'a,Y) & less_than(Y::'a,Z) --> less_than(X::'a,Z)) &      \
\  (! X Y. less_than(X::'a,Y) | less_than(Y::'a,X) | equal(X::'a,Y)) &    \
\  (! X. ~less_than(X::'a,X)) &     \
\  (! Y X. ~(less_than(X::'a,Y) & less_than(Y::'a,X))) &        \
\  (! Y X Z. equal(X::'a,Y) & less_than(X::'a,Z) --> less_than(Y::'a,Z)) &  \
\  (! Y Z X. equal(X::'a,Y) & less_than(Z::'a,X) --> less_than(Z::'a,Y)) &  \
\  (! X Y. equal(X::'a,Y) --> equal(predecessor(X),predecessor(Y))) &       \
\  (! X Y. equal(X::'a,Y) --> equal(successor(X),successor(Y))) &   \
\  (! X Y. equal(X::'a,Y) --> equal(a(X),a(Y))) &   \
\  (~less_than(n::'a,j)) &  \
\  (less_than(k::'a,j)) &   \
\  (~less_than(k::'a,i)) &  \
\  (less_than(i::'a,n)) &   \
\  (less_than(a(j),a(k))) &     \
\  (! X. less_than(X::'a,j) & less_than(a(X),a(k)) --> less_than(X::'a,i)) &    \
\  (! X. less_than(one::'a,i) & less_than(a(X),a(predecessor(i))) --> less_than(X::'a,i) | less_than(n::'a,X)) &   \
\  (! X. ~(less_than(one::'a,X) & less_than(X::'a,i) & less_than(a(X),a(predecessor(X))))) &    \
\  (less_than(j::'a,i)) --> False",
  meson_tac);

(*584 inferences so far.  Searching to depth 7.  1.1 secs*)
val PRV005_1 = prove
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X. equal(predecessor(successor(X)),X)) &  \
\  (! X. equal(successor(predecessor(X)),X)) &  \
\  (! X Y. equal(predecessor(X),predecessor(Y)) --> equal(X::'a,Y)) &       \
\  (! X Y. equal(successor(X),successor(Y)) --> equal(X::'a,Y)) &   \
\  (! X. less_than(predecessor(X),X)) & \
\  (! X. less_than(X::'a,successor(X))) &   \
\  (! X Y Z. less_than(X::'a,Y) & less_than(Y::'a,Z) --> less_than(X::'a,Z)) &      \
\  (! X Y. less_than(X::'a,Y) | less_than(Y::'a,X) | equal(X::'a,Y)) &    \
\  (! X. ~less_than(X::'a,X)) &     \
\  (! Y X. ~(less_than(X::'a,Y) & less_than(Y::'a,X))) &        \
\  (! Y X Z. equal(X::'a,Y) & less_than(X::'a,Z) --> less_than(Y::'a,Z)) &  \
\  (! Y Z X. equal(X::'a,Y) & less_than(Z::'a,X) --> less_than(Z::'a,Y)) &  \
\  (! X Y. equal(X::'a,Y) --> equal(predecessor(X),predecessor(Y))) &       \
\  (! X Y. equal(X::'a,Y) --> equal(successor(X),successor(Y))) &   \
\  (! X Y. equal(X::'a,Y) --> equal(a(X),a(Y))) &   \
\  (~less_than(n::'a,k)) &  \
\  (~less_than(k::'a,l)) &  \
\  (~less_than(k::'a,i)) &  \
\  (less_than(l::'a,n)) &   \
\  (less_than(one::'a,l)) & \
\  (less_than(a(k),a(predecessor(l)))) &        \
\  (! X. less_than(X::'a,successor(n)) & less_than(a(X),a(k)) --> less_than(X::'a,l)) & \
\  (! X. less_than(one::'a,l) & less_than(a(X),a(predecessor(l))) --> less_than(X::'a,l) | less_than(n::'a,X)) &   \
\  (! X. ~(less_than(one::'a,X) & less_than(X::'a,l) & less_than(a(X),a(predecessor(X))))) --> False",
  meson_tac);

(*2343 inferences so far.  Searching to depth 8.  3.5 secs*)
val PRV006_1 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X. equal(predecessor(successor(X)),X)) &  \
\  (! X. equal(successor(predecessor(X)),X)) &  \
\  (! X Y. equal(predecessor(X),predecessor(Y)) --> equal(X::'a,Y)) &       \
\  (! X Y. equal(successor(X),successor(Y)) --> equal(X::'a,Y)) &   \
\  (! X. less_than(predecessor(X),X)) & \
\  (! X. less_than(X::'a,successor(X))) &   \
\  (! X Y Z. less_than(X::'a,Y) & less_than(Y::'a,Z) --> less_than(X::'a,Z)) &      \
\  (! X Y. less_than(X::'a,Y) | less_than(Y::'a,X) | equal(X::'a,Y)) &    \
\  (! X. ~less_than(X::'a,X)) &     \
\  (! Y X. ~(less_than(X::'a,Y) & less_than(Y::'a,X))) &        \
\  (! Y X Z. equal(X::'a,Y) & less_than(X::'a,Z) --> less_than(Y::'a,Z)) &  \
\  (! Y Z X. equal(X::'a,Y) & less_than(Z::'a,X) --> less_than(Z::'a,Y)) &  \
\  (! X Y. equal(X::'a,Y) --> equal(predecessor(X),predecessor(Y))) &       \
\  (! X Y. equal(X::'a,Y) --> equal(successor(X),successor(Y))) &   \
\  (! X Y. equal(X::'a,Y) --> equal(a(X),a(Y))) &   \
\  (~less_than(n::'a,m)) &  \
\  (less_than(i::'a,m)) &   \
\  (less_than(i::'a,n)) &   \
\  (~less_than(i::'a,one)) &        \
\  (less_than(a(i),a(m))) &     \
\  (! X. less_than(X::'a,successor(n)) & less_than(a(X),a(m)) --> less_than(X::'a,i)) & \
\  (! X. less_than(one::'a,i) & less_than(a(X),a(predecessor(i))) --> less_than(X::'a,i) | less_than(n::'a,X)) &   \
\  (! X. ~(less_than(one::'a,X) & less_than(X::'a,i) & less_than(a(X),a(predecessor(X))))) --> False",
  meson_tac);

(*86 inferences so far.  Searching to depth 14.  0.1 secs*)
val PRV009_1 = prove
 ("(! Y X. less_or_equal(X::'a,Y) | less(Y::'a,X)) &   \
\  (less(j::'a,i)) &        \
\  (less_or_equal(m::'a,p)) &       \
\  (less_or_equal(p::'a,q)) &       \
\  (less_or_equal(q::'a,n)) &       \
\  (! X Y. less_or_equal(m::'a,X) & less(X::'a,i) & less(j::'a,Y) & less_or_equal(Y::'a,n) --> less_or_equal(a(X),a(Y))) &      \
\  (! X Y. less_or_equal(m::'a,X) & less_or_equal(X::'a,Y) & less_or_equal(Y::'a,j) --> less_or_equal(a(X),a(Y))) & \
\  (! X Y. less_or_equal(i::'a,X) & less_or_equal(X::'a,Y) & less_or_equal(Y::'a,n) --> less_or_equal(a(X),a(Y))) & \
\  (~less_or_equal(a(p),a(q))) --> False",
  meson_tac);

(*222 inferences so far.  Searching to depth 8.  0.4 secs*)
val PUZ012_1 = prove
 ("(! X. equal_fruits(X::'a,X)) &   \
\  (! X. equal_boxes(X::'a,X)) &    \
\  (! X Y. ~(label(X::'a,Y) & contains(X::'a,Y))) &     \
\  (! X. contains(boxa::'a,X) | contains(boxb::'a,X) | contains(boxc::'a,X)) &    \
\  (! X. contains(X::'a,apples) | contains(X::'a,bananas) | contains(X::'a,oranges)) &    \
\  (! X Y Z. contains(X::'a,Y) & contains(X::'a,Z) --> equal_fruits(Y::'a,Z)) &     \
\  (! Y X Z. contains(X::'a,Y) & contains(Z::'a,Y) --> equal_boxes(X::'a,Z)) &      \
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
  meson_tac);

(*35 inferences so far.  Searching to depth 5.  3.2 secs*)
val PUZ020_1 = prove
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! A B. equal(A::'a,B) --> equal(statement_by(A),statement_by(B))) &     \
\  (! X. person(X) --> knight(X) | knave(X)) & \
\  (! X. ~(person(X) & knight(X) & knave(X))) & \
\  (! X Y. says(X::'a,Y) & a_truth(Y) --> a_truth(Y)) &     \
\  (! X Y. ~(says(X::'a,Y) & equal(X::'a,Y))) & \
\  (! Y X. says(X::'a,Y) --> equal(Y::'a,statement_by(X))) &    \
\  (! X Y. ~(person(X) & equal(X::'a,statement_by(Y)))) &   \
\  (! X. person(X) & a_truth(statement_by(X)) --> knight(X)) &  \
\  (! X. person(X) --> a_truth(statement_by(X)) | knave(X)) &  \
\  (! X Y. equal(X::'a,Y) & knight(X) --> knight(Y)) &      \
\  (! X Y. equal(X::'a,Y) & knave(X) --> knave(Y)) &        \
\  (! X Y. equal(X::'a,Y) & person(X) --> person(Y)) &      \
\  (! X Y Z. equal(X::'a,Y) & says(X::'a,Z) --> says(Y::'a,Z)) &    \
\  (! X Z Y. equal(X::'a,Y) & says(Z::'a,X) --> says(Z::'a,Y)) &    \
\  (! X Y. equal(X::'a,Y) & a_truth(X) --> a_truth(Y)) &    \
\  (! X Y. knight(X) & says(X::'a,Y) --> a_truth(Y)) &      \
\  (! X Y. ~(knave(X) & says(X::'a,Y) & a_truth(Y))) &      \
\  (person(husband)) &  \
\  (person(wife)) &     \
\  (~equal(husband::'a,wife)) &     \
\  (says(husband::'a,statement_by(husband))) &      \
\  (a_truth(statement_by(husband)) & knight(husband) --> knight(wife)) &        \
\  (knight(husband) --> a_truth(statement_by(husband))) &       \
\  (a_truth(statement_by(husband)) | knight(wife)) &   \
\  (knight(wife) --> a_truth(statement_by(husband))) &  \
\  (~knight(husband)) --> False",
  meson_tac);

(*121806 inferences so far.  Searching to depth 17.  63.0 secs*)
val PUZ025_1 = prove_hard
 ("(! X. a_truth(truthteller(X)) | a_truth(liar(X))) & \
\  (! X. ~(a_truth(truthteller(X)) & a_truth(liar(X)))) &       \
\  (! Truthteller Statement. a_truth(truthteller(Truthteller)) & a_truth(says(Truthteller::'a,Statement)) --> a_truth(Statement)) & \
\  (! Liar Statement. ~(a_truth(liar(Liar)) & a_truth(says(Liar::'a,Statement)) & a_truth(Statement))) &    \
\  (! Statement Truthteller. a_truth(Statement) & a_truth(says(Truthteller::'a,Statement)) --> a_truth(truthteller(Truthteller))) & \
\  (! Statement Liar. a_truth(says(Liar::'a,Statement)) --> a_truth(Statement) | a_truth(liar(Liar))) &    \
\  (! Z X Y. people(X::'a,Y,Z) & a_truth(liar(X)) & a_truth(liar(Y)) --> a_truth(equal_type(X::'a,Y))) &        \
\  (! Z X Y. people(X::'a,Y,Z) & a_truth(truthteller(X)) & a_truth(truthteller(Y)) --> a_truth(equal_type(X::'a,Y))) &  \
\  (! X Y. a_truth(equal_type(X::'a,Y)) & a_truth(truthteller(X)) --> a_truth(truthteller(Y))) &    \
\  (! X Y. a_truth(equal_type(X::'a,Y)) & a_truth(liar(X)) --> a_truth(liar(Y))) &  \
\  (! X Y. a_truth(truthteller(X)) --> a_truth(equal_type(X::'a,Y)) | a_truth(liar(Y))) &  \
\  (! X Y. a_truth(liar(X)) --> a_truth(equal_type(X::'a,Y)) | a_truth(truthteller(Y))) &  \
\  (! Y X. a_truth(equal_type(X::'a,Y)) --> a_truth(equal_type(Y::'a,X))) &     \
\  (! X Y. ask_1_if_2(X::'a,Y) & a_truth(truthteller(X)) & a_truth(Y) --> answer(yes)) &    \
\  (! X Y. ask_1_if_2(X::'a,Y) & a_truth(truthteller(X)) --> a_truth(Y) | answer(no)) &    \
\  (! X Y. ask_1_if_2(X::'a,Y) & a_truth(liar(X)) & a_truth(Y) --> answer(no)) &    \
\  (! X Y. ask_1_if_2(X::'a,Y) & a_truth(liar(X)) --> a_truth(Y) | answer(yes)) &  \
\  (people(b::'a,c,a)) &    \
\  (people(a::'a,b,a)) &    \
\  (people(a::'a,c,b)) &    \
\  (people(c::'a,b,a)) &    \
\  (a_truth(says(a::'a,equal_type(b::'a,c)))) & \
\  (ask_1_if_2(c::'a,equal_type(a::'a,b))) &    \
\  (! Answer. ~answer(Answer)) --> False",
  meson_tac);


(*621 inferences so far.  Searching to depth 18.  0.2 secs*)
val PUZ029_1 = prove
 ("(! X. dances_on_tightropes(X) | eats_pennybuns(X) | old(X)) &      \
\  (! X. pig(X) & liable_to_giddiness(X) --> treated_with_respect(X)) & \
\  (! X. wise(X) & balloonist(X) --> has_umbrella(X)) & \
\  (! X. ~(looks_ridiculous(X) & eats_pennybuns(X) & eats_lunch_in_public(X))) &        \
\  (! X. balloonist(X) & young(X) --> liable_to_giddiness(X)) & \
\  (! X. fat(X) & looks_ridiculous(X) --> dances_on_tightropes(X) | eats_lunch_in_public(X)) & \
\  (! X. ~(liable_to_giddiness(X) & wise(X) & dances_on_tightropes(X))) &       \
\  (! X. pig(X) & has_umbrella(X) --> looks_ridiculous(X)) &    \
\  (! X. treated_with_respect(X) --> dances_on_tightropes(X) | fat(X)) &       \
\  (! X. young(X) | old(X)) &  \
\  (! X. ~(young(X) & old(X))) &        \
\  (wise(piggy)) &      \
\  (young(piggy)) &     \
\  (pig(piggy)) &       \
\  (balloonist(piggy)) --> False",
  meson_tac);

(*93620 inferences so far.  Searching to depth 24.  65.9 secs*)
val RNG001_3 = prove_hard
 ("(! X. sum(additive_identity::'a,X,X)) &  \
\  (! X. sum(additive_inverse(X),X,additive_identity)) &        \
\  (! Y U Z X V W. sum(X::'a,Y,U) & sum(Y::'a,Z,V) & sum(U::'a,Z,W) --> sum(X::'a,V,W)) &       \
\  (! Y X V U Z W. sum(X::'a,Y,U) & sum(Y::'a,Z,V) & sum(X::'a,V,W) --> sum(U::'a,Z,W)) &       \
\  (! X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (! Y Z X V3 V1 V2 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & product(X::'a,V3,V4) --> sum(V1::'a,V2,V4)) &        \
\  (! Y Z V1 V2 X V3 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(X::'a,V3,V4)) &        \
\  (~product(a::'a,additive_identity,additive_identity)) --> False",
  meson_tac);


(****************SLOW
3057170 inferences so far.  Searching to depth 16.  No proof after 45 minutes.
val RNG001_5 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X. sum(additive_identity::'a,X,X)) &  \
\  (! X. sum(X::'a,additive_identity,X)) &  \
\  (! X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (! X Y. sum(X::'a,Y,add(X::'a,Y))) & \
\  (! X. sum(additive_inverse(X),X,additive_identity)) &        \
\  (! X. sum(X::'a,additive_inverse(X),additive_identity)) &        \
\  (! Y U Z X V W. sum(X::'a,Y,U) & sum(Y::'a,Z,V) & sum(U::'a,Z,W) --> sum(X::'a,V,W)) &       \
\  (! Y X V U Z W. sum(X::'a,Y,U) & sum(Y::'a,Z,V) & sum(X::'a,V,W) --> sum(U::'a,Z,W)) &       \
\  (! Y X Z. sum(X::'a,Y,Z) --> sum(Y::'a,X,Z)) &       \
\  (! Y U Z X V W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(U::'a,Z,W) --> product(X::'a,V,W)) &       \
\  (! Y X V U Z W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(X::'a,V,W) --> product(U::'a,Z,W)) &       \
\  (! Y Z X V3 V1 V2 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & product(X::'a,V3,V4) --> sum(V1::'a,V2,V4)) &        \
\  (! Y Z V1 V2 X V3 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(X::'a,V3,V4)) &        \
\  (! Y Z V3 X V1 V2 V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & product(V3::'a,X,V4) --> sum(V1::'a,V2,V4)) &        \
\  (! Y Z V1 V2 V3 X V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(V3::'a,X,V4)) &        \
\  (! X Y U V. sum(X::'a,Y,U) & sum(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (! X Y U V. product(X::'a,Y,U) & product(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (! X Y. equal(X::'a,Y) --> equal(additive_inverse(X),additive_inverse(Y))) &     \
\  (! X Y W. equal(X::'a,Y) --> equal(add(X::'a,W),add(Y::'a,W))) & \
\  (! X Y W Z. equal(X::'a,Y) & sum(X::'a,W,Z) --> sum(Y::'a,W,Z)) &        \
\  (! X W Y Z. equal(X::'a,Y) & sum(W::'a,X,Z) --> sum(W::'a,Y,Z)) &        \
\  (! X W Z Y. equal(X::'a,Y) & sum(W::'a,Z,X) --> sum(W::'a,Z,Y)) &        \
\  (! X Y W. equal(X::'a,Y) --> equal(multiply(X::'a,W),multiply(Y::'a,W))) &       \
\  (! X Y W Z. equal(X::'a,Y) & product(X::'a,W,Z) --> product(Y::'a,W,Z)) &        \
\  (! X W Y Z. equal(X::'a,Y) & product(W::'a,X,Z) --> product(W::'a,Y,Z)) &        \
\  (! X W Z Y. equal(X::'a,Y) & product(W::'a,Z,X) --> product(W::'a,Z,Y)) &        \
\  (~product(a::'a,additive_identity,additive_identity)) --> False",
  meson_tac);
****************)

(*0 inferences so far.  Searching to depth 0.  0.5 secs*)
val RNG011_5 = prove
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! A B C. equal(A::'a,B) --> equal(add(A::'a,C),add(B::'a,C))) & \
\  (! D F' E. equal(D::'a,E) --> equal(add(F'::'a,D),add(F'::'a,E))) &      \
\  (! G H. equal(G::'a,H) --> equal(additive_inverse(G),additive_inverse(H))) &     \
\  (! I' J K'. equal(I'::'a,J) --> equal(multiply(I'::'a,K'),multiply(J::'a,K'))) & \
\  (! L N M. equal(L::'a,M) --> equal(multiply(N::'a,L),multiply(N::'a,M))) &       \
\  (! A B C D. equal(A::'a,B) --> equal(associator(A::'a,C,D),associator(B::'a,C,D))) &     \
\  (! E G F' H. equal(E::'a,F') --> equal(associator(G::'a,E,H),associator(G::'a,F',H))) &  \
\  (! I' K' L J. equal(I'::'a,J) --> equal(associator(K'::'a,L,I'),associator(K'::'a,L,J))) &       \
\  (! M N O_. equal(M::'a,N) --> equal(commutator(M::'a,O_),commutator(N::'a,O_))) &   \
\  (! P R Q. equal(P::'a,Q) --> equal(commutator(R::'a,P),commutator(R::'a,Q))) &   \
\  (! Y X. equal(add(X::'a,Y),add(Y::'a,X))) &  \
\  (! X Y Z. equal(add(add(X::'a,Y),Z),add(X::'a,add(Y::'a,Z)))) &  \
\  (! X. equal(add(X::'a,additive_identity),X)) &   \
\  (! X. equal(add(additive_identity::'a,X),X)) &   \
\  (! X. equal(add(X::'a,additive_inverse(X)),additive_identity)) & \
\  (! X. equal(add(additive_inverse(X),X),additive_identity)) & \
\  (equal(additive_inverse(additive_identity),additive_identity)) &     \
\  (! X Y. equal(add(X::'a,add(additive_inverse(X),Y)),Y)) &        \
\  (! X Y. equal(additive_inverse(add(X::'a,Y)),add(additive_inverse(X),additive_inverse(Y)))) &    \
\  (! X. equal(additive_inverse(additive_inverse(X)),X)) &      \
\  (! X. equal(multiply(X::'a,additive_identity),additive_identity)) &      \
\  (! X. equal(multiply(additive_identity::'a,X),additive_identity)) &      \
\  (! X Y. equal(multiply(additive_inverse(X),additive_inverse(Y)),multiply(X::'a,Y))) &    \
\  (! X Y. equal(multiply(X::'a,additive_inverse(Y)),additive_inverse(multiply(X::'a,Y)))) &    \
\  (! X Y. equal(multiply(additive_inverse(X),Y),additive_inverse(multiply(X::'a,Y)))) &    \
\  (! Y X Z. equal(multiply(X::'a,add(Y::'a,Z)),add(multiply(X::'a,Y),multiply(X::'a,Z)))) &    \
\  (! X Y Z. equal(multiply(add(X::'a,Y),Z),add(multiply(X::'a,Z),multiply(Y::'a,Z)))) &    \
\  (! X Y. equal(multiply(multiply(X::'a,Y),Y),multiply(X::'a,multiply(Y::'a,Y)))) &        \
\  (! X Y Z. equal(associator(X::'a,Y,Z),add(multiply(multiply(X::'a,Y),Z),additive_inverse(multiply(X::'a,multiply(Y::'a,Z)))))) &     \
\  (! X Y. equal(commutator(X::'a,Y),add(multiply(Y::'a,X),additive_inverse(multiply(X::'a,Y))))) & \
\  (! X Y. equal(multiply(multiply(associator(X::'a,X,Y),X),associator(X::'a,X,Y)),additive_identity)) &        \
\  (~equal(multiply(multiply(associator(a::'a,a,b),a),associator(a::'a,a,b)),additive_identity)) --> False",
  meson_tac);

(*202 inferences so far.  Searching to depth 8.  0.6 secs*)
val RNG023_6 = prove
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! Y X. equal(add(X::'a,Y),add(Y::'a,X))) &  \
\  (! X Y Z. equal(add(X::'a,add(Y::'a,Z)),add(add(X::'a,Y),Z))) &  \
\  (! X. equal(add(additive_identity::'a,X),X)) &   \
\  (! X. equal(add(X::'a,additive_identity),X)) &   \
\  (! X. equal(multiply(additive_identity::'a,X),additive_identity)) &      \
\  (! X. equal(multiply(X::'a,additive_identity),additive_identity)) &      \
\  (! X. equal(add(additive_inverse(X),X),additive_identity)) & \
\  (! X. equal(add(X::'a,additive_inverse(X)),additive_identity)) & \
\  (! Y X Z. equal(multiply(X::'a,add(Y::'a,Z)),add(multiply(X::'a,Y),multiply(X::'a,Z)))) &    \
\  (! X Y Z. equal(multiply(add(X::'a,Y),Z),add(multiply(X::'a,Z),multiply(Y::'a,Z)))) &    \
\  (! X. equal(additive_inverse(additive_inverse(X)),X)) &      \
\  (! X Y. equal(multiply(multiply(X::'a,Y),Y),multiply(X::'a,multiply(Y::'a,Y)))) &        \
\  (! X Y. equal(multiply(multiply(X::'a,X),Y),multiply(X::'a,multiply(X::'a,Y)))) &        \
\  (! X Y Z. equal(associator(X::'a,Y,Z),add(multiply(multiply(X::'a,Y),Z),additive_inverse(multiply(X::'a,multiply(Y::'a,Z)))))) &     \
\  (! X Y. equal(commutator(X::'a,Y),add(multiply(Y::'a,X),additive_inverse(multiply(X::'a,Y))))) & \
\  (! D E F'. equal(D::'a,E) --> equal(add(D::'a,F'),add(E::'a,F'))) &      \
\  (! G I' H. equal(G::'a,H) --> equal(add(I'::'a,G),add(I'::'a,H))) &      \
\  (! J K'. equal(J::'a,K') --> equal(additive_inverse(J),additive_inverse(K'))) &  \
\  (! L M N O_. equal(L::'a,M) --> equal(associator(L::'a,N,O_),associator(M::'a,N,O_))) &     \
\  (! P R Q S'. equal(P::'a,Q) --> equal(associator(R::'a,P,S'),associator(R::'a,Q,S'))) &  \
\  (! T' V W U. equal(T'::'a,U) --> equal(associator(V::'a,W,T'),associator(V::'a,W,U))) &  \
\  (! X Y Z. equal(X::'a,Y) --> equal(commutator(X::'a,Z),commutator(Y::'a,Z))) &   \
\  (! A1 C1 B1. equal(A1::'a,B1) --> equal(commutator(C1::'a,A1),commutator(C1::'a,B1))) &  \
\  (! D1 E1 F1. equal(D1::'a,E1) --> equal(multiply(D1::'a,F1),multiply(E1::'a,F1))) &      \
\  (! G1 I1 H1. equal(G1::'a,H1) --> equal(multiply(I1::'a,G1),multiply(I1::'a,H1))) &      \
\  (~equal(associator(x::'a,x,y),additive_identity)) --> False",
  meson_tac);

(*0 inferences so far.  Searching to depth 0.  0.6 secs*)
val RNG028_2 = prove
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X. equal(add(additive_identity::'a,X),X)) &   \
\  (! X. equal(multiply(additive_identity::'a,X),additive_identity)) &      \
\  (! X. equal(multiply(X::'a,additive_identity),additive_identity)) &      \
\  (! X. equal(add(additive_inverse(X),X),additive_identity)) & \
\  (! X Y. equal(additive_inverse(add(X::'a,Y)),add(additive_inverse(X),additive_inverse(Y)))) &    \
\  (! X. equal(additive_inverse(additive_inverse(X)),X)) &      \
\  (! Y X Z. equal(multiply(X::'a,add(Y::'a,Z)),add(multiply(X::'a,Y),multiply(X::'a,Z)))) &    \
\  (! X Y Z. equal(multiply(add(X::'a,Y),Z),add(multiply(X::'a,Z),multiply(Y::'a,Z)))) &    \
\  (! X Y. equal(multiply(multiply(X::'a,Y),Y),multiply(X::'a,multiply(Y::'a,Y)))) &        \
\  (! X Y. equal(multiply(multiply(X::'a,X),Y),multiply(X::'a,multiply(X::'a,Y)))) &        \
\  (! X Y. equal(multiply(additive_inverse(X),Y),additive_inverse(multiply(X::'a,Y)))) &    \
\  (! X Y. equal(multiply(X::'a,additive_inverse(Y)),additive_inverse(multiply(X::'a,Y)))) &    \
\  (equal(additive_inverse(additive_identity),additive_identity)) &     \
\  (! Y X. equal(add(X::'a,Y),add(Y::'a,X))) &  \
\  (! X Y Z. equal(add(X::'a,add(Y::'a,Z)),add(add(X::'a,Y),Z))) &  \
\  (! Z X Y. equal(add(X::'a,Z),add(Y::'a,Z)) --> equal(X::'a,Y)) & \
\  (! Z X Y. equal(add(Z::'a,X),add(Z::'a,Y)) --> equal(X::'a,Y)) & \
\  (! D E F'. equal(D::'a,E) --> equal(add(D::'a,F'),add(E::'a,F'))) &      \
\  (! G I' H. equal(G::'a,H) --> equal(add(I'::'a,G),add(I'::'a,H))) &      \
\  (! J K'. equal(J::'a,K') --> equal(additive_inverse(J),additive_inverse(K'))) &  \
\  (! D1 E1 F1. equal(D1::'a,E1) --> equal(multiply(D1::'a,F1),multiply(E1::'a,F1))) &      \
\  (! G1 I1 H1. equal(G1::'a,H1) --> equal(multiply(I1::'a,G1),multiply(I1::'a,H1))) &      \
\  (! X Y Z. equal(associator(X::'a,Y,Z),add(multiply(multiply(X::'a,Y),Z),additive_inverse(multiply(X::'a,multiply(Y::'a,Z)))))) &     \
\  (! L M N O_. equal(L::'a,M) --> equal(associator(L::'a,N,O_),associator(M::'a,N,O_))) &     \
\  (! P R Q S'. equal(P::'a,Q) --> equal(associator(R::'a,P,S'),associator(R::'a,Q,S'))) &  \
\  (! T' V W U. equal(T'::'a,U) --> equal(associator(V::'a,W,T'),associator(V::'a,W,U))) &  \
\  (! X Y. ~equal(multiply(multiply(Y::'a,X),Y),multiply(Y::'a,multiply(X::'a,Y)))) &       \
\  (! X Y Z. ~equal(associator(Y::'a,X,Z),additive_inverse(associator(X::'a,Y,Z)))) &   \
\  (! X Y Z. ~equal(associator(Z::'a,Y,X),additive_inverse(associator(X::'a,Y,Z)))) &   \
\  (~equal(multiply(multiply(cx::'a,multiply(cy::'a,cx)),cz),multiply(cx::'a,multiply(cy::'a,multiply(cx::'a,cz))))) --> False",
  meson_tac);

(*209 inferences so far.  Searching to depth 9.  1.2 secs*)
val RNG038_2 = prove
 ("(! X. sum(X::'a,additive_identity,X)) &  \
\  (! X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (! X Y. sum(X::'a,Y,add(X::'a,Y))) & \
\  (! X. sum(X::'a,additive_inverse(X),additive_identity)) &        \
\  (! Y U Z X V W. sum(X::'a,Y,U) & sum(Y::'a,Z,V) & sum(U::'a,Z,W) --> sum(X::'a,V,W)) &       \
\  (! Y X V U Z W. sum(X::'a,Y,U) & sum(Y::'a,Z,V) & sum(X::'a,V,W) --> sum(U::'a,Z,W)) &       \
\  (! Y X Z. sum(X::'a,Y,Z) --> sum(Y::'a,X,Z)) &       \
\  (! Y U Z X V W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(U::'a,Z,W) --> product(X::'a,V,W)) &       \
\  (! Y X V U Z W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(X::'a,V,W) --> product(U::'a,Z,W)) &       \
\  (! Y Z X V3 V1 V2 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & product(X::'a,V3,V4) --> sum(V1::'a,V2,V4)) &        \
\  (! Y Z V1 V2 X V3 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(X::'a,V3,V4)) &        \
\  (! Y Z V3 X V1 V2 V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & product(V3::'a,X,V4) --> sum(V1::'a,V2,V4)) &        \
\  (! Y Z V1 V2 V3 X V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(V3::'a,X,V4)) &        \
\  (! X Y U V. sum(X::'a,Y,U) & sum(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (! X Y U V. product(X::'a,Y,U) & product(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (! X Y. equal(X::'a,Y) --> equal(additive_inverse(X),additive_inverse(Y))) &     \
\  (! X Y W. equal(X::'a,Y) --> equal(add(X::'a,W),add(Y::'a,W))) & \
\  (! X Y W Z. equal(X::'a,Y) & sum(X::'a,W,Z) --> sum(Y::'a,W,Z)) &        \
\  (! X W Y Z. equal(X::'a,Y) & sum(W::'a,X,Z) --> sum(W::'a,Y,Z)) &        \
\  (! X W Z Y. equal(X::'a,Y) & sum(W::'a,Z,X) --> sum(W::'a,Z,Y)) &        \
\  (! X Y W. equal(X::'a,Y) --> equal(multiply(X::'a,W),multiply(Y::'a,W))) &       \
\  (! X Y W Z. equal(X::'a,Y) & product(X::'a,W,Z) --> product(Y::'a,W,Z)) &        \
\  (! X W Y Z. equal(X::'a,Y) & product(W::'a,X,Z) --> product(W::'a,Y,Z)) &        \
\  (! X W Z Y. equal(X::'a,Y) & product(W::'a,Z,X) --> product(W::'a,Z,Y)) &        \
\  (! X. product(additive_identity::'a,X,additive_identity)) &      \
\  (! X. product(X::'a,additive_identity,additive_identity)) &      \
\  (! X Y. equal(X::'a,additive_identity) --> product(X::'a,h(X::'a,Y),Y)) &        \
\  (product(a::'a,b,additive_identity)) &   \
\  (~equal(a::'a,additive_identity)) &      \
\  (~equal(b::'a,additive_identity)) --> False",
  meson_tac);

(*2660 inferences so far.  Searching to depth 10.  7.0 secs*)
val RNG040_2 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X Y. equal(X::'a,Y) --> equal(additive_inverse(X),additive_inverse(Y))) &     \
\  (! X Y W. equal(X::'a,Y) --> equal(add(X::'a,W),add(Y::'a,W))) & \
\  (! X W Y. equal(X::'a,Y) --> equal(add(W::'a,X),add(W::'a,Y))) & \
\  (! X Y W Z. equal(X::'a,Y) & sum(X::'a,W,Z) --> sum(Y::'a,W,Z)) &        \
\  (! X W Y Z. equal(X::'a,Y) & sum(W::'a,X,Z) --> sum(W::'a,Y,Z)) &        \
\  (! X W Z Y. equal(X::'a,Y) & sum(W::'a,Z,X) --> sum(W::'a,Z,Y)) &        \
\  (! X Y W. equal(X::'a,Y) --> equal(multiply(X::'a,W),multiply(Y::'a,W))) &       \
\  (! X W Y. equal(X::'a,Y) --> equal(multiply(W::'a,X),multiply(W::'a,Y))) &       \
\  (! X Y W Z. equal(X::'a,Y) & product(X::'a,W,Z) --> product(Y::'a,W,Z)) &        \
\  (! X W Y Z. equal(X::'a,Y) & product(W::'a,X,Z) --> product(W::'a,Y,Z)) &        \
\  (! X W Z Y. equal(X::'a,Y) & product(W::'a,Z,X) --> product(W::'a,Z,Y)) &        \
\  (! X. sum(additive_identity::'a,X,X)) &  \
\  (! X. sum(X::'a,additive_identity,X)) &  \
\  (! X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (! X Y. sum(X::'a,Y,add(X::'a,Y))) & \
\  (! X. sum(additive_inverse(X),X,additive_identity)) &        \
\  (! X. sum(X::'a,additive_inverse(X),additive_identity)) &        \
\  (! Y U Z X V W. sum(X::'a,Y,U) & sum(Y::'a,Z,V) & sum(U::'a,Z,W) --> sum(X::'a,V,W)) &       \
\  (! Y X V U Z W. sum(X::'a,Y,U) & sum(Y::'a,Z,V) & sum(X::'a,V,W) --> sum(U::'a,Z,W)) &       \
\  (! Y X Z. sum(X::'a,Y,Z) --> sum(Y::'a,X,Z)) &       \
\  (! Y U Z X V W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(U::'a,Z,W) --> product(X::'a,V,W)) &       \
\  (! Y X V U Z W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(X::'a,V,W) --> product(U::'a,Z,W)) &       \
\  (! Y Z X V3 V1 V2 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & product(X::'a,V3,V4) --> sum(V1::'a,V2,V4)) &        \
\  (! Y Z V1 V2 X V3 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(X::'a,V3,V4)) &        \
\  (! X Y U V. sum(X::'a,Y,U) & sum(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (! X Y U V. product(X::'a,Y,U) & product(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (! A. product(A::'a,multiplicative_identity,A)) &        \
\  (! A. product(multiplicative_identity::'a,A,A)) &        \
\  (! A. product(A::'a,h(A),multiplicative_identity) | equal(A::'a,additive_identity)) &       \
\  (! A. product(h(A),A,multiplicative_identity) | equal(A::'a,additive_identity)) &       \
\  (! B A C. product(A::'a,B,C) --> product(B::'a,A,C)) &       \
\  (! A B. equal(A::'a,B) --> equal(h(A),h(B))) &   \
\  (sum(b::'a,c,d)) &       \
\  (product(d::'a,a,additive_identity)) &   \
\  (product(b::'a,a,l)) &   \
\  (product(c::'a,a,n)) &   \
\  (~sum(l::'a,n,additive_identity)) --> False",
  meson_tac);

(*8991 inferences so far.  Searching to depth 9.  22.2 secs*)
val RNG041_1 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! X. sum(additive_identity::'a,X,X)) &  \
\  (! X. sum(X::'a,additive_identity,X)) &  \
\  (! X Y. product(X::'a,Y,multiply(X::'a,Y))) &        \
\  (! X Y. sum(X::'a,Y,add(X::'a,Y))) & \
\  (! X. sum(additive_inverse(X),X,additive_identity)) &        \
\  (! X. sum(X::'a,additive_inverse(X),additive_identity)) &        \
\  (! Y U Z X V W. sum(X::'a,Y,U) & sum(Y::'a,Z,V) & sum(U::'a,Z,W) --> sum(X::'a,V,W)) &       \
\  (! Y X V U Z W. sum(X::'a,Y,U) & sum(Y::'a,Z,V) & sum(X::'a,V,W) --> sum(U::'a,Z,W)) &       \
\  (! Y X Z. sum(X::'a,Y,Z) --> sum(Y::'a,X,Z)) &       \
\  (! Y U Z X V W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(U::'a,Z,W) --> product(X::'a,V,W)) &       \
\  (! Y X V U Z W. product(X::'a,Y,U) & product(Y::'a,Z,V) & product(X::'a,V,W) --> product(U::'a,Z,W)) &       \
\  (! Y Z X V3 V1 V2 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & product(X::'a,V3,V4) --> sum(V1::'a,V2,V4)) &        \
\  (! Y Z V1 V2 X V3 V4. product(X::'a,Y,V1) & product(X::'a,Z,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(X::'a,V3,V4)) &        \
\  (! Y Z V3 X V1 V2 V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & product(V3::'a,X,V4) --> sum(V1::'a,V2,V4)) &        \
\  (! Y Z V1 V2 V3 X V4. product(Y::'a,X,V1) & product(Z::'a,X,V2) & sum(Y::'a,Z,V3) & sum(V1::'a,V2,V4) --> product(V3::'a,X,V4)) &        \
\  (! X Y U V. sum(X::'a,Y,U) & sum(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (! X Y U V. product(X::'a,Y,U) & product(X::'a,Y,V) --> equal(U::'a,V)) &        \
\  (! X Y. equal(X::'a,Y) --> equal(additive_inverse(X),additive_inverse(Y))) &     \
\  (! X Y W. equal(X::'a,Y) --> equal(add(X::'a,W),add(Y::'a,W))) & \
\  (! X W Y. equal(X::'a,Y) --> equal(add(W::'a,X),add(W::'a,Y))) & \
\  (! X Y W Z. equal(X::'a,Y) & sum(X::'a,W,Z) --> sum(Y::'a,W,Z)) &        \
\  (! X W Y Z. equal(X::'a,Y) & sum(W::'a,X,Z) --> sum(W::'a,Y,Z)) &        \
\  (! X W Z Y. equal(X::'a,Y) & sum(W::'a,Z,X) --> sum(W::'a,Z,Y)) &        \
\  (! X Y W. equal(X::'a,Y) --> equal(multiply(X::'a,W),multiply(Y::'a,W))) &       \
\  (! X W Y. equal(X::'a,Y) --> equal(multiply(W::'a,X),multiply(W::'a,Y))) &       \
\  (! X Y W Z. equal(X::'a,Y) & product(X::'a,W,Z) --> product(Y::'a,W,Z)) &        \
\  (! X W Y Z. equal(X::'a,Y) & product(W::'a,X,Z) --> product(W::'a,Y,Z)) &        \
\  (! X W Z Y. equal(X::'a,Y) & product(W::'a,Z,X) --> product(W::'a,Z,Y)) &        \
\  (! A B. equal(A::'a,B) --> equal(h(A),h(B))) &   \
\  (! A. product(additive_identity::'a,A,additive_identity)) &      \
\  (! A. product(A::'a,additive_identity,additive_identity)) &      \
\  (! A. product(A::'a,multiplicative_identity,A)) &        \
\  (! A. product(multiplicative_identity::'a,A,A)) &        \
\  (! A. product(A::'a,h(A),multiplicative_identity) | equal(A::'a,additive_identity)) &       \
\  (! A. product(h(A),A,multiplicative_identity) | equal(A::'a,additive_identity)) &       \
\  (product(a::'a,b,additive_identity)) &   \
\  (~equal(a::'a,additive_identity)) &      \
\  (~equal(b::'a,additive_identity)) --> False",
  meson_tac);

(*101319 inferences so far.  Searching to depth 14.  76.0 secs*)
val ROB010_1 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! Y X. equal(add(X::'a,Y),add(Y::'a,X))) &  \
\  (! X Y Z. equal(add(add(X::'a,Y),Z),add(X::'a,add(Y::'a,Z)))) &  \
\  (! Y X. equal(negate(add(negate(add(X::'a,Y)),negate(add(X::'a,negate(Y))))),X)) &   \
\  (! A B C. equal(A::'a,B) --> equal(add(A::'a,C),add(B::'a,C))) & \
\  (! D F' E. equal(D::'a,E) --> equal(add(F'::'a,D),add(F'::'a,E))) &      \
\  (! G H. equal(G::'a,H) --> equal(negate(G),negate(H))) & \
\  (equal(negate(add(a::'a,negate(b))),c)) &        \
\  (~equal(negate(add(c::'a,negate(add(b::'a,a)))),a)) --> False",
  meson_tac);


(*6933 inferences so far.  Searching to depth 12.  5.1 secs*)
val ROB013_1 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! Y X. equal(add(X::'a,Y),add(Y::'a,X))) &  \
\  (! X Y Z. equal(add(add(X::'a,Y),Z),add(X::'a,add(Y::'a,Z)))) &  \
\  (! Y X. equal(negate(add(negate(add(X::'a,Y)),negate(add(X::'a,negate(Y))))),X)) &   \
\  (! A B C. equal(A::'a,B) --> equal(add(A::'a,C),add(B::'a,C))) & \
\  (! D F' E. equal(D::'a,E) --> equal(add(F'::'a,D),add(F'::'a,E))) &      \
\  (! G H. equal(G::'a,H) --> equal(negate(G),negate(H))) & \
\  (equal(negate(add(a::'a,b)),c)) &        \
\  (~equal(negate(add(c::'a,negate(add(negate(b),a)))),a)) --> False",
  meson_tac);

(*6614 inferences so far.  Searching to depth 11.  20.4 secs*)
val ROB016_1 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! Y X. equal(add(X::'a,Y),add(Y::'a,X))) &  \
\  (! X Y Z. equal(add(add(X::'a,Y),Z),add(X::'a,add(Y::'a,Z)))) &  \
\  (! Y X. equal(negate(add(negate(add(X::'a,Y)),negate(add(X::'a,negate(Y))))),X)) &   \
\  (! A B C. equal(A::'a,B) --> equal(add(A::'a,C),add(B::'a,C))) & \
\  (! D F' E. equal(D::'a,E) --> equal(add(F'::'a,D),add(F'::'a,E))) &      \
\  (! G H. equal(G::'a,H) --> equal(negate(G),negate(H))) & \
\  (! J K' L. equal(J::'a,K') --> equal(multiply(J::'a,L),multiply(K'::'a,L))) &    \
\  (! M O_ N. equal(M::'a,N) --> equal(multiply(O_::'a,M),multiply(O_::'a,N))) &       \
\  (! P Q. equal(P::'a,Q) --> equal(successor(P),successor(Q))) &   \
\  (! R S'. equal(R::'a,S') & positive_integer(R) --> positive_integer(S')) &       \
\  (! X. equal(multiply(one::'a,X),X)) &    \
\  (! V X. positive_integer(X) --> equal(multiply(successor(V),X),add(X::'a,multiply(V::'a,X)))) &      \
\  (positive_integer(one)) &    \
\  (! X. positive_integer(X) --> positive_integer(successor(X))) &      \
\  (equal(negate(add(d::'a,e)),negate(e))) &        \
\  (positive_integer(k)) &      \
\  (! Vk X Y. equal(negate(add(negate(Y),negate(add(X::'a,negate(Y))))),X) & positive_integer(Vk) --> equal(negate(add(Y::'a,multiply(Vk::'a,add(X::'a,negate(add(X::'a,negate(Y))))))),negate(Y))) &       \
\  (~equal(negate(add(e::'a,multiply(k::'a,add(d::'a,negate(add(d::'a,negate(e))))))),negate(e))) --> False",
  meson_tac);

(*14077 inferences so far.  Searching to depth 11.  32.8 secs*)
val ROB021_1 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! Y X. equal(add(X::'a,Y),add(Y::'a,X))) &  \
\  (! X Y Z. equal(add(add(X::'a,Y),Z),add(X::'a,add(Y::'a,Z)))) &  \
\  (! Y X. equal(negate(add(negate(add(X::'a,Y)),negate(add(X::'a,negate(Y))))),X)) &   \
\  (! A B C. equal(A::'a,B) --> equal(add(A::'a,C),add(B::'a,C))) & \
\  (! D F' E. equal(D::'a,E) --> equal(add(F'::'a,D),add(F'::'a,E))) &      \
\  (! G H. equal(G::'a,H) --> equal(negate(G),negate(H))) & \
\  (! X Y. equal(negate(X),negate(Y)) --> equal(X::'a,Y)) & \
\  (~equal(add(negate(add(a::'a,negate(b))),negate(add(negate(a),negate(b)))),b)) --> False",
  meson_tac);

(*35532 inferences so far.  Searching to depth 19.  54.3 secs*)
val SET005_1 = prove_hard
 ("(! Subset Element Superset. member(Element::'a,Subset) & subset(Subset::'a,Superset) --> member(Element::'a,Superset)) & \
\  (! Superset Subset. subset(Subset::'a,Superset) | member(member_of_1_not_of_2(Subset::'a,Superset),Subset)) &       \
\  (! Subset Superset. member(member_of_1_not_of_2(Subset::'a,Superset),Superset) --> subset(Subset::'a,Superset)) &    \
\  (! Subset Superset. equal_sets(Subset::'a,Superset) --> subset(Subset::'a,Superset)) &       \
\  (! Subset Superset. equal_sets(Superset::'a,Subset) --> subset(Subset::'a,Superset)) &       \
\  (! Set2 Set1. subset(Set1::'a,Set2) & subset(Set2::'a,Set1) --> equal_sets(Set2::'a,Set1)) &     \
\  (! Set2 Intersection Element Set1. intersection(Set1::'a,Set2,Intersection) & member(Element::'a,Intersection) --> member(Element::'a,Set1)) &   \
\  (! Set1 Intersection Element Set2. intersection(Set1::'a,Set2,Intersection) & member(Element::'a,Intersection) --> member(Element::'a,Set2)) &   \
\  (! Set2 Set1 Element Intersection. intersection(Set1::'a,Set2,Intersection) & member(Element::'a,Set2) & member(Element::'a,Set1) --> member(Element::'a,Intersection)) &    \
\  (! Set2 Intersection Set1. member(h(Set1::'a,Set2,Intersection),Intersection) | intersection(Set1::'a,Set2,Intersection) | member(h(Set1::'a,Set2,Intersection),Set1)) &       \
\  (! Set1 Intersection Set2. member(h(Set1::'a,Set2,Intersection),Intersection) | intersection(Set1::'a,Set2,Intersection) | member(h(Set1::'a,Set2,Intersection),Set2)) &       \
\  (! Set1 Set2 Intersection. member(h(Set1::'a,Set2,Intersection),Intersection) & member(h(Set1::'a,Set2,Intersection),Set2) & member(h(Set1::'a,Set2,Intersection),Set1) --> intersection(Set1::'a,Set2,Intersection)) &      \
\  (intersection(a::'a,b,aIb)) &    \
\  (intersection(b::'a,c,bIc)) &    \
\  (intersection(a::'a,bIc,aIbIc)) &        \
\  (~intersection(aIb::'a,c,aIbIc)) --> False",
  meson_tac);


(*6450 inferences so far.  Searching to depth 14.  4.2 secs*)
val SET009_1 = prove_hard
 ("(! Subset Element Superset. member(Element::'a,Subset) & subset(Subset::'a,Superset) --> member(Element::'a,Superset)) & \
\  (! Superset Subset. subset(Subset::'a,Superset) | member(member_of_1_not_of_2(Subset::'a,Superset),Subset)) &       \
\  (! Subset Superset. member(member_of_1_not_of_2(Subset::'a,Superset),Superset) --> subset(Subset::'a,Superset)) &    \
\  (! Subset Superset. equal_sets(Subset::'a,Superset) --> subset(Subset::'a,Superset)) &       \
\  (! Subset Superset. equal_sets(Superset::'a,Subset) --> subset(Subset::'a,Superset)) &       \
\  (! Set2 Set1. subset(Set1::'a,Set2) & subset(Set2::'a,Set1) --> equal_sets(Set2::'a,Set1)) &     \
\  (! Set2 Difference Element Set1. difference(Set1::'a,Set2,Difference) & member(Element::'a,Difference) --> member(Element::'a,Set1)) &   \
\  (! Element A_set Set1 Set2. ~(member(Element::'a,Set1) & member(Element::'a,Set2) & difference(A_set::'a,Set1,Set2))) &  \
\  (! Set1 Difference Element Set2. member(Element::'a,Set1) & difference(Set1::'a,Set2,Difference) --> member(Element::'a,Difference) | member(Element::'a,Set2)) &   \
\  (! Set1 Set2 Difference. difference(Set1::'a,Set2,Difference) | member(k(Set1::'a,Set2,Difference),Set1) | member(k(Set1::'a,Set2,Difference),Difference)) &   \
\  (! Set1 Set2 Difference. member(k(Set1::'a,Set2,Difference),Set2) --> member(k(Set1::'a,Set2,Difference),Difference) | difference(Set1::'a,Set2,Difference)) &  \
\  (! Set1 Set2 Difference. member(k(Set1::'a,Set2,Difference),Difference) & member(k(Set1::'a,Set2,Difference),Set1) --> member(k(Set1::'a,Set2,Difference),Set2) | difference(Set1::'a,Set2,Difference)) &   \
\  (subset(d::'a,a)) &      \
\  (difference(b::'a,a,bDa)) &      \
\  (difference(b::'a,d,bDd)) &      \
\  (~subset(bDa::'a,bDd)) --> False",
  meson_tac);

(*34726 inferences so far.  Searching to depth 6.  2420 secs: 40 mins!  BIG*)
val SET025_4 = prove_hard
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (! Y X. member(X::'a,Y) --> little_set(X)) &     \
\  (! X Y. little_set(f1(X::'a,Y)) | equal(X::'a,Y)) & \
\  (! X Y. member(f1(X::'a,Y),X) | member(f1(X::'a,Y),Y) | equal(X::'a,Y)) &      \
\  (! X Y. member(f1(X::'a,Y),X) & member(f1(X::'a,Y),Y) --> equal(X::'a,Y)) &      \
\  (! X U Y. member(U::'a,non_ordered_pair(X::'a,Y)) --> equal(U::'a,X) | equal(U::'a,Y)) &    \
\  (! Y U X. little_set(U) & equal(U::'a,X) --> member(U::'a,non_ordered_pair(X::'a,Y))) &  \
\  (! X U Y. little_set(U) & equal(U::'a,Y) --> member(U::'a,non_ordered_pair(X::'a,Y))) &  \
\  (! X Y. little_set(non_ordered_pair(X::'a,Y))) & \
\  (! X. equal(singleton_set(X),non_ordered_pair(X::'a,X))) &       \
\  (! X Y. equal(ordered_pair(X::'a,Y),non_ordered_pair(singleton_set(X),non_ordered_pair(X::'a,Y)))) & \
\  (! X. ordered_pair_predicate(X) --> little_set(f2(X))) &     \
\  (! X. ordered_pair_predicate(X) --> little_set(f3(X))) &     \
\  (! X. ordered_pair_predicate(X) --> equal(X::'a,ordered_pair(f2(X),f3(X)))) &    \
\  (! X Y Z. little_set(Y) & little_set(Z) & equal(X::'a,ordered_pair(Y::'a,Z)) --> ordered_pair_predicate(X)) &        \
\  (! Z X. member(Z::'a,first(X)) --> little_set(f4(Z::'a,X))) &        \
\  (! Z X. member(Z::'a,first(X)) --> little_set(f5(Z::'a,X))) &        \
\  (! Z X. member(Z::'a,first(X)) --> equal(X::'a,ordered_pair(f4(Z::'a,X),f5(Z::'a,X)))) &     \
\  (! Z X. member(Z::'a,first(X)) --> member(Z::'a,f4(Z::'a,X))) &  \
\  (! X V Z U. little_set(U) & little_set(V) & equal(X::'a,ordered_pair(U::'a,V)) & member(Z::'a,U) --> member(Z::'a,first(X))) &       \
\  (! Z X. member(Z::'a,second(X)) --> little_set(f6(Z::'a,X))) &       \
\  (! Z X. member(Z::'a,second(X)) --> little_set(f7(Z::'a,X))) &       \
\  (! Z X. member(Z::'a,second(X)) --> equal(X::'a,ordered_pair(f6(Z::'a,X),f7(Z::'a,X)))) &    \
\  (! Z X. member(Z::'a,second(X)) --> member(Z::'a,f7(Z::'a,X))) & \
\  (! X U Z V. little_set(U) & little_set(V) & equal(X::'a,ordered_pair(U::'a,V)) & member(Z::'a,V) --> member(Z::'a,second(X))) &      \
\  (! Z. member(Z::'a,estin) --> ordered_pair_predicate(Z)) &       \
\  (! Z. member(Z::'a,estin) --> member(first(Z),second(Z))) &      \
\  (! Z. little_set(Z) & ordered_pair_predicate(Z) & member(first(Z),second(Z)) --> member(Z::'a,estin)) &  \
\  (! Y Z X. member(Z::'a,intersection(X::'a,Y)) --> member(Z::'a,X)) &     \
\  (! X Z Y. member(Z::'a,intersection(X::'a,Y)) --> member(Z::'a,Y)) &     \
\  (! X Z Y. member(Z::'a,X) & member(Z::'a,Y) --> member(Z::'a,intersection(X::'a,Y))) &       \
\  (! Z X. ~(member(Z::'a,complement(X)) & member(Z::'a,X))) &  \
\  (! Z X. little_set(Z) --> member(Z::'a,complement(X)) | member(Z::'a,X)) &  \
\  (! X Y. equal(union(X::'a,Y),complement(intersection(complement(X),complement(Y))))) &   \
\  (! Z X. member(Z::'a,domain_of(X)) --> ordered_pair_predicate(f8(Z::'a,X))) &        \
\  (! Z X. member(Z::'a,domain_of(X)) --> member(f8(Z::'a,X),X)) &      \
\  (! Z X. member(Z::'a,domain_of(X)) --> equal(Z::'a,first(f8(Z::'a,X)))) &        \
\  (! X Z Xp. little_set(Z) & ordered_pair_predicate(Xp) & member(Xp::'a,X) & equal(Z::'a,first(Xp)) --> member(Z::'a,domain_of(X))) &      \
\  (! X Y Z. member(Z::'a,cross_product(X::'a,Y)) --> ordered_pair_predicate(Z)) &      \
\  (! Y Z X. member(Z::'a,cross_product(X::'a,Y)) --> member(first(Z),X)) &     \
\  (! X Z Y. member(Z::'a,cross_product(X::'a,Y)) --> member(second(Z),Y)) &    \
\  (! X Z Y. little_set(Z) & ordered_pair_predicate(Z) & member(first(Z),X) & member(second(Z),Y) --> member(Z::'a,cross_product(X::'a,Y))) &   \
\  (! X Z. member(Z::'a,inv1 X) --> ordered_pair_predicate(Z)) &       \
\  (! Z X. member(Z::'a,inv1 X) --> member(ordered_pair(second(Z),first(Z)),X)) &      \
\  (! Z X. little_set(Z) & ordered_pair_predicate(Z) & member(ordered_pair(second(Z),first(Z)),X) --> member(Z::'a,inv1 X)) &  \
\  (! Z X. member(Z::'a,rotate_right(X)) --> little_set(f9(Z::'a,X))) & \
\  (! Z X. member(Z::'a,rotate_right(X)) --> little_set(f10(Z::'a,X))) &        \
\  (! Z X. member(Z::'a,rotate_right(X)) --> little_set(f11(Z::'a,X))) &        \
\  (! Z X. member(Z::'a,rotate_right(X)) --> equal(Z::'a,ordered_pair(f9(Z::'a,X),ordered_pair(f10(Z::'a,X),f11(Z::'a,X))))) &      \
\  (! Z X. member(Z::'a,rotate_right(X)) --> member(ordered_pair(f10(Z::'a,X),ordered_pair(f11(Z::'a,X),f9(Z::'a,X))),X)) &     \
\  (! Z V W U X. little_set(Z) & little_set(U) & little_set(V) & little_set(W) & equal(Z::'a,ordered_pair(U::'a,ordered_pair(V::'a,W))) & member(ordered_pair(V::'a,ordered_pair(W::'a,U)),X) --> member(Z::'a,rotate_right(X))) &      \
\  (! Z X. member(Z::'a,flip_range_of(X)) --> little_set(f12(Z::'a,X))) &       \
\  (! Z X. member(Z::'a,flip_range_of(X)) --> little_set(f13(Z::'a,X))) &       \
\  (! Z X. member(Z::'a,flip_range_of(X)) --> little_set(f14(Z::'a,X))) &       \
\  (! Z X. member(Z::'a,flip_range_of(X)) --> equal(Z::'a,ordered_pair(f12(Z::'a,X),ordered_pair(f13(Z::'a,X),f14(Z::'a,X))))) &    \
\  (! Z X. member(Z::'a,flip_range_of(X)) --> member(ordered_pair(f12(Z::'a,X),ordered_pair(f14(Z::'a,X),f13(Z::'a,X))),X)) &   \
\  (! Z U W V X. little_set(Z) & little_set(U) & little_set(V) & little_set(W) & equal(Z::'a,ordered_pair(U::'a,ordered_pair(V::'a,W))) & member(ordered_pair(U::'a,ordered_pair(W::'a,V)),X) --> member(Z::'a,flip_range_of(X))) &     \
\  (! X. equal(successor(X),union(X::'a,singleton_set(X)))) &       \
\  (! Z. ~member(Z::'a,empty_set)) &        \
\  (! Z. little_set(Z) --> member(Z::'a,universal_set)) &   \
\  (little_set(infinity)) &     \
\  (member(empty_set::'a,infinity)) &       \
\  (! X. member(X::'a,infinity) --> member(successor(X),infinity)) &        \
\  (! Z X. member(Z::'a,sigma(X)) --> member(f16(Z::'a,X),X)) & \
\  (! Z X. member(Z::'a,sigma(X)) --> member(Z::'a,f16(Z::'a,X))) & \
\  (! X Z Y. member(Y::'a,X) & member(Z::'a,Y) --> member(Z::'a,sigma(X))) &        \
\  (! U. little_set(U) --> little_set(sigma(U))) &      \
\  (! X U Y. subset(X::'a,Y) & member(U::'a,X) --> member(U::'a,Y)) &       \
\  (! Y X. subset(X::'a,Y) | member(f17(X::'a,Y),X)) & \
\  (! X Y. member(f17(X::'a,Y),Y) --> subset(X::'a,Y)) &        \
\  (! X Y. proper_subset(X::'a,Y) --> subset(X::'a,Y)) &        \
\  (! X Y. ~(proper_subset(X::'a,Y) & equal(X::'a,Y))) &        \
\  (! X Y. subset(X::'a,Y) --> proper_subset(X::'a,Y) | equal(X::'a,Y)) &  \
\  (! Z X. member(Z::'a,powerset(X)) --> subset(Z::'a,X)) &     \
\  (! Z X. little_set(Z) & subset(Z::'a,X) --> member(Z::'a,powerset(X))) &     \
\  (! U. little_set(U) --> little_set(powerset(U))) &   \
\  (! Z X. relation(Z) & member(X::'a,Z) --> ordered_pair_predicate(X)) &   \
\  (! Z. relation(Z) | member(f18(Z),Z)) &     \
\  (! Z. ordered_pair_predicate(f18(Z)) --> relation(Z)) &      \
\  (! U X V W. single_valued_set(X) & little_set(U) & little_set(V) & little_set(W) & member(ordered_pair(U::'a,V),X) & member(ordered_pair(U::'a,W),X) --> equal(V::'a,W)) &       \
\  (! X. single_valued_set(X) | little_set(f19(X))) &  \
\  (! X. single_valued_set(X) | little_set(f20(X))) &  \
\  (! X. single_valued_set(X) | little_set(f21(X))) &  \
\  (! X. single_valued_set(X) | member(ordered_pair(f19(X),f20(X)),X)) &       \
\  (! X. single_valued_set(X) | member(ordered_pair(f19(X),f21(X)),X)) &       \
\  (! X. equal(f20(X),f21(X)) --> single_valued_set(X)) &       \
\  (! Xf. function(Xf) --> relation(Xf)) &      \
\  (! Xf. function(Xf) --> single_valued_set(Xf)) &     \
\  (! Xf. relation(Xf) & single_valued_set(Xf) --> function(Xf)) &      \
\  (! Z X Xf. member(Z::'a,image_(X::'a,Xf)) --> ordered_pair_predicate(f22(Z::'a,X,Xf))) &  \
\  (! Z X Xf. member(Z::'a,image_(X::'a,Xf)) --> member(f22(Z::'a,X,Xf),Xf)) &       \
\  (! Z Xf X. member(Z::'a,image_(X::'a,Xf)) --> member(first(f22(Z::'a,X,Xf)),X)) & \
\  (! X Xf Z. member(Z::'a,image_(X::'a,Xf)) --> equal(second(f22(Z::'a,X,Xf)),Z)) & \
\  (! Xf X Y Z. little_set(Z) & ordered_pair_predicate(Y) & member(Y::'a,Xf) & member(first(Y),X) & equal(second(Y),Z) --> member(Z::'a,image_(X::'a,Xf))) & \
\  (! X Xf. little_set(X) & function(Xf) --> little_set(image_(X::'a,Xf))) & \
\  (! X U Y. ~(disjoint(X::'a,Y) & member(U::'a,X) & member(U::'a,Y))) &    \
\  (! Y X. disjoint(X::'a,Y) | member(f23(X::'a,Y),X)) &       \
\  (! X Y. disjoint(X::'a,Y) | member(f23(X::'a,Y),Y)) &       \
\  (! X. equal(X::'a,empty_set) | member(f24(X),X)) &      \
\  (! X. equal(X::'a,empty_set) | disjoint(f24(X),X)) &    \
\  (function(f25)) &    \
\  (! X. little_set(X) --> equal(X::'a,empty_set) | member(f26(X),X)) &    \
\  (! X. little_set(X) --> equal(X::'a,empty_set) | member(ordered_pair(X::'a,f26(X)),f25)) &  \
\  (! Z X. member(Z::'a,range_of(X)) --> ordered_pair_predicate(f27(Z::'a,X))) &        \
\  (! Z X. member(Z::'a,range_of(X)) --> member(f27(Z::'a,X),X)) &      \
\  (! Z X. member(Z::'a,range_of(X)) --> equal(Z::'a,second(f27(Z::'a,X)))) &       \
\  (! X Z Xp. little_set(Z) & ordered_pair_predicate(Xp) & member(Xp::'a,X) & equal(Z::'a,second(Xp)) --> member(Z::'a,range_of(X))) &      \
\  (! Z. member(Z::'a,identity_relation) --> ordered_pair_predicate(Z)) &   \
\  (! Z. member(Z::'a,identity_relation) --> equal(first(Z),second(Z))) &   \
\  (! Z. little_set(Z) & ordered_pair_predicate(Z) & equal(first(Z),second(Z)) --> member(Z::'a,identity_relation)) &       \
\  (! X Y. equal(restrct(X::'a,Y),intersection(X::'a,cross_product(Y::'a,universal_set)))) &       \
\  (! Xf. one_to_one_function(Xf) --> function(Xf)) &   \
\  (! Xf. one_to_one_function(Xf) --> function(inv1 Xf)) & \
\  (! Xf. function(Xf) & function(inv1 Xf) --> one_to_one_function(Xf)) &  \
\  (! Z Xf Y. member(Z::'a,apply(Xf::'a,Y)) --> ordered_pair_predicate(f28(Z::'a,Xf,Y))) &  \
\  (! Z Y Xf. member(Z::'a,apply(Xf::'a,Y)) --> member(f28(Z::'a,Xf,Y),Xf)) &       \
\  (! Z Xf Y. member(Z::'a,apply(Xf::'a,Y)) --> equal(first(f28(Z::'a,Xf,Y)),Y)) &  \
\  (! Z Xf Y. member(Z::'a,apply(Xf::'a,Y)) --> member(Z::'a,second(f28(Z::'a,Xf,Y)))) &        \
\  (! Xf Y Z W. ordered_pair_predicate(W) & member(W::'a,Xf) & equal(first(W),Y) & member(Z::'a,second(W)) --> member(Z::'a,apply(Xf::'a,Y))) & \
\  (! Xf X Y. equal(apply_to_two_arguments(Xf::'a,X,Y),apply(Xf::'a,ordered_pair(X::'a,Y)))) &      \
\  (! X Y Xf. maps(Xf::'a,X,Y) --> function(Xf)) &  \
\  (! Y Xf X. maps(Xf::'a,X,Y) --> equal(domain_of(Xf),X)) &        \
\  (! X Xf Y. maps(Xf::'a,X,Y) --> subset(range_of(Xf),Y)) &        \
\  (! X Xf Y. function(Xf) & equal(domain_of(Xf),X) & subset(range_of(Xf),Y) --> maps(Xf::'a,X,Y)) &        \
\  (! Xf Xs. closed(Xs::'a,Xf) --> little_set(Xs)) &        \
\  (! Xs Xf. closed(Xs::'a,Xf) --> little_set(Xf)) &        \
\  (! Xf Xs. closed(Xs::'a,Xf) --> maps(Xf::'a,cross_product(Xs::'a,Xs),Xs)) &      \
\  (! Xf Xs. little_set(Xs) & little_set(Xf) & maps(Xf::'a,cross_product(Xs::'a,Xs),Xs) --> closed(Xs::'a,Xf)) &    \
\  (! Z Xf Xg. member(Z::'a,composition(Xf::'a,Xg)) --> little_set(f29(Z::'a,Xf,Xg))) &     \
\  (! Z Xf Xg. member(Z::'a,composition(Xf::'a,Xg)) --> little_set(f30(Z::'a,Xf,Xg))) &     \
\  (! Z Xf Xg. member(Z::'a,composition(Xf::'a,Xg)) --> little_set(f31(Z::'a,Xf,Xg))) &     \
\  (! Z Xf Xg. member(Z::'a,composition(Xf::'a,Xg)) --> equal(Z::'a,ordered_pair(f29(Z::'a,Xf,Xg),f30(Z::'a,Xf,Xg)))) &     \
\  (! Z Xg Xf. member(Z::'a,composition(Xf::'a,Xg)) --> member(ordered_pair(f29(Z::'a,Xf,Xg),f31(Z::'a,Xf,Xg)),Xf)) &   \
\  (! Z Xf Xg. member(Z::'a,composition(Xf::'a,Xg)) --> member(ordered_pair(f31(Z::'a,Xf,Xg),f30(Z::'a,Xf,Xg)),Xg)) &   \
\  (! Z X Xf W Y Xg. little_set(Z) & little_set(X) & little_set(Y) & little_set(W) & equal(Z::'a,ordered_pair(X::'a,Y)) & member(ordered_pair(X::'a,W),Xf) & member(ordered_pair(W::'a,Y),Xg) --> member(Z::'a,composition(Xf::'a,Xg))) &       \
\  (! Xh Xs2 Xf2 Xs1 Xf1. homomorphism(Xh::'a,Xs1,Xf1,Xs2,Xf2) --> closed(Xs1::'a,Xf1)) &       \
\  (! Xh Xs1 Xf1 Xs2 Xf2. homomorphism(Xh::'a,Xs1,Xf1,Xs2,Xf2) --> closed(Xs2::'a,Xf2)) &       \
\  (! Xf1 Xf2 Xh Xs1 Xs2. homomorphism(Xh::'a,Xs1,Xf1,Xs2,Xf2) --> maps(Xh::'a,Xs1,Xs2)) &      \
\  (! Xs2 Xs1 Xf1 Xf2 X Xh Y. homomorphism(Xh::'a,Xs1,Xf1,Xs2,Xf2) & member(X::'a,Xs1) & member(Y::'a,Xs1) --> equal(apply(Xh::'a,apply_to_two_arguments(Xf1::'a,X,Y)),apply_to_two_arguments(Xf2::'a,apply(Xh::'a,X),apply(Xh::'a,Y)))) &      \
\  (! Xh Xf1 Xs2 Xf2 Xs1. closed(Xs1::'a,Xf1) & closed(Xs2::'a,Xf2) & maps(Xh::'a,Xs1,Xs2) --> homomorphism(Xh::'a,Xs1,Xf1,Xs2,Xf2) | member(f32(Xh::'a,Xs1,Xf1,Xs2,Xf2),Xs1)) &   \
\  (! Xh Xf1 Xs2 Xf2 Xs1. closed(Xs1::'a,Xf1) & closed(Xs2::'a,Xf2) & maps(Xh::'a,Xs1,Xs2) --> homomorphism(Xh::'a,Xs1,Xf1,Xs2,Xf2) | member(f33(Xh::'a,Xs1,Xf1,Xs2,Xf2),Xs1)) &   \
\  (! Xh Xs1 Xf1 Xs2 Xf2. closed(Xs1::'a,Xf1) & closed(Xs2::'a,Xf2) & maps(Xh::'a,Xs1,Xs2) & equal(apply(Xh::'a,apply_to_two_arguments(Xf1::'a,f32(Xh::'a,Xs1,Xf1,Xs2,Xf2),f33(Xh::'a,Xs1,Xf1,Xs2,Xf2))),apply_to_two_arguments(Xf2::'a,apply(Xh::'a,f32(Xh::'a,Xs1,Xf1,Xs2,Xf2)),apply(Xh::'a,f33(Xh::'a,Xs1,Xf1,Xs2,Xf2)))) --> homomorphism(Xh::'a,Xs1,Xf1,Xs2,Xf2)) &   \
\  (! A B C. equal(A::'a,B) --> equal(f1(A::'a,C),f1(B::'a,C))) &   \
\  (! D F' E. equal(D::'a,E) --> equal(f1(F'::'a,D),f1(F'::'a,E))) &        \
\  (! A2 B2. equal(A2::'a,B2) --> equal(f2(A2),f2(B2))) &   \
\  (! G4 H4. equal(G4::'a,H4) --> equal(f3(G4),f3(H4))) &   \
\  (! O7 P7 Q7. equal(O7::'a,P7) --> equal(f4(O7::'a,Q7),f4(P7::'a,Q7))) &  \
\  (! R7 T7 S7. equal(R7::'a,S7) --> equal(f4(T7::'a,R7),f4(T7::'a,S7))) &  \
\  (! U7 V7 W7. equal(U7::'a,V7) --> equal(f5(U7::'a,W7),f5(V7::'a,W7))) &  \
\  (! X7 Z7 Y7. equal(X7::'a,Y7) --> equal(f5(Z7::'a,X7),f5(Z7::'a,Y7))) &  \
\  (! A8 B8 C8. equal(A8::'a,B8) --> equal(f6(A8::'a,C8),f6(B8::'a,C8))) &  \
\  (! D8 F8 E8. equal(D8::'a,E8) --> equal(f6(F8::'a,D8),f6(F8::'a,E8))) &  \
\  (! G8 H8 I8. equal(G8::'a,H8) --> equal(f7(G8::'a,I8),f7(H8::'a,I8))) &  \
\  (! J8 L8 K8. equal(J8::'a,K8) --> equal(f7(L8::'a,J8),f7(L8::'a,K8))) &  \
\  (! M8 N8 O8. equal(M8::'a,N8) --> equal(f8(M8::'a,O8),f8(N8::'a,O8))) &  \
\  (! P8 R8 Q8. equal(P8::'a,Q8) --> equal(f8(R8::'a,P8),f8(R8::'a,Q8))) &  \
\  (! S8 T8 U8. equal(S8::'a,T8) --> equal(f9(S8::'a,U8),f9(T8::'a,U8))) &  \
\  (! V8 X8 W8. equal(V8::'a,W8) --> equal(f9(X8::'a,V8),f9(X8::'a,W8))) &  \
\  (! G H I'. equal(G::'a,H) --> equal(f10(G::'a,I'),f10(H::'a,I'))) &      \
\  (! J L K'. equal(J::'a,K') --> equal(f10(L::'a,J),f10(L::'a,K'))) &      \
\  (! M N O_. equal(M::'a,N) --> equal(f11(M::'a,O_),f11(N::'a,O_))) & \
\  (! P R Q. equal(P::'a,Q) --> equal(f11(R::'a,P),f11(R::'a,Q))) & \
\  (! S' T' U. equal(S'::'a,T') --> equal(f12(S'::'a,U),f12(T'::'a,U))) &   \
\  (! V X W. equal(V::'a,W) --> equal(f12(X::'a,V),f12(X::'a,W))) & \
\  (! Y Z A1. equal(Y::'a,Z) --> equal(f13(Y::'a,A1),f13(Z::'a,A1))) &      \
\  (! B1 D1 C1. equal(B1::'a,C1) --> equal(f13(D1::'a,B1),f13(D1::'a,C1))) &        \
\  (! E1 F1 G1. equal(E1::'a,F1) --> equal(f14(E1::'a,G1),f14(F1::'a,G1))) &        \
\  (! H1 J1 I1. equal(H1::'a,I1) --> equal(f14(J1::'a,H1),f14(J1::'a,I1))) &        \
\  (! K1 L1 M1. equal(K1::'a,L1) --> equal(f16(K1::'a,M1),f16(L1::'a,M1))) &        \
\  (! N1 P1 O1. equal(N1::'a,O1) --> equal(f16(P1::'a,N1),f16(P1::'a,O1))) &        \
\  (! Q1 R1 S1. equal(Q1::'a,R1) --> equal(f17(Q1::'a,S1),f17(R1::'a,S1))) &        \
\  (! T1 V1 U1. equal(T1::'a,U1) --> equal(f17(V1::'a,T1),f17(V1::'a,U1))) &        \
\  (! W1 X1. equal(W1::'a,X1) --> equal(f18(W1),f18(X1))) & \
\  (! Y1 Z1. equal(Y1::'a,Z1) --> equal(f19(Y1),f19(Z1))) & \
\  (! C2 D2. equal(C2::'a,D2) --> equal(f20(C2),f20(D2))) & \
\  (! E2 F2. equal(E2::'a,F2) --> equal(f21(E2),f21(F2))) & \
\  (! G2 H2 I2 J2. equal(G2::'a,H2) --> equal(f22(G2::'a,I2,J2),f22(H2::'a,I2,J2))) &       \
\  (! K2 M2 L2 N2. equal(K2::'a,L2) --> equal(f22(M2::'a,K2,N2),f22(M2::'a,L2,N2))) &       \
\  (! O2 Q2 R2 P2. equal(O2::'a,P2) --> equal(f22(Q2::'a,R2,O2),f22(Q2::'a,R2,P2))) &       \
\  (! S2 T2 U2. equal(S2::'a,T2) --> equal(f23(S2::'a,U2),f23(T2::'a,U2))) &        \
\  (! V2 X2 W2. equal(V2::'a,W2) --> equal(f23(X2::'a,V2),f23(X2::'a,W2))) &        \
\  (! Y2 Z2. equal(Y2::'a,Z2) --> equal(f24(Y2),f24(Z2))) & \
\  (! A3 B3. equal(A3::'a,B3) --> equal(f26(A3),f26(B3))) & \
\  (! C3 D3 E3. equal(C3::'a,D3) --> equal(f27(C3::'a,E3),f27(D3::'a,E3))) &        \
\  (! F3 H3 G3. equal(F3::'a,G3) --> equal(f27(H3::'a,F3),f27(H3::'a,G3))) &        \
\  (! I3 J3 K3 L3. equal(I3::'a,J3) --> equal(f28(I3::'a,K3,L3),f28(J3::'a,K3,L3))) &       \
\  (! M3 O3 N3 P3. equal(M3::'a,N3) --> equal(f28(O3::'a,M3,P3),f28(O3::'a,N3,P3))) &       \
\  (! Q3 S3 T3 R3. equal(Q3::'a,R3) --> equal(f28(S3::'a,T3,Q3),f28(S3::'a,T3,R3))) &       \
\  (! U3 V3 W3 X3. equal(U3::'a,V3) --> equal(f29(U3::'a,W3,X3),f29(V3::'a,W3,X3))) &       \
\  (! Y3 A4 Z3 B4. equal(Y3::'a,Z3) --> equal(f29(A4::'a,Y3,B4),f29(A4::'a,Z3,B4))) &       \
\  (! C4 E4 F4 D4. equal(C4::'a,D4) --> equal(f29(E4::'a,F4,C4),f29(E4::'a,F4,D4))) &       \
\  (! I4 J4 K4 L4. equal(I4::'a,J4) --> equal(f30(I4::'a,K4,L4),f30(J4::'a,K4,L4))) &       \
\  (! M4 O4 N4 P4. equal(M4::'a,N4) --> equal(f30(O4::'a,M4,P4),f30(O4::'a,N4,P4))) &       \
\  (! Q4 S4 T4 R4. equal(Q4::'a,R4) --> equal(f30(S4::'a,T4,Q4),f30(S4::'a,T4,R4))) &       \
\  (! U4 V4 W4 X4. equal(U4::'a,V4) --> equal(f31(U4::'a,W4,X4),f31(V4::'a,W4,X4))) &       \
\  (! Y4 A5 Z4 B5. equal(Y4::'a,Z4) --> equal(f31(A5::'a,Y4,B5),f31(A5::'a,Z4,B5))) &       \
\  (! C5 E5 F5 D5. equal(C5::'a,D5) --> equal(f31(E5::'a,F5,C5),f31(E5::'a,F5,D5))) &       \
\  (! G5 H5 I5 J5 K5 L5. equal(G5::'a,H5) --> equal(f32(G5::'a,I5,J5,K5,L5),f32(H5::'a,I5,J5,K5,L5))) &     \
\  (! M5 O5 N5 P5 Q5 R5. equal(M5::'a,N5) --> equal(f32(O5::'a,M5,P5,Q5,R5),f32(O5::'a,N5,P5,Q5,R5))) &     \
\  (! S5 U5 V5 T5 W5 X5. equal(S5::'a,T5) --> equal(f32(U5::'a,V5,S5,W5,X5),f32(U5::'a,V5,T5,W5,X5))) &     \
\  (! Y5 A6 B6 C6 Z5 D6. equal(Y5::'a,Z5) --> equal(f32(A6::'a,B6,C6,Y5,D6),f32(A6::'a,B6,C6,Z5,D6))) &     \
\  (! E6 G6 H6 I6 J6 F6. equal(E6::'a,F6) --> equal(f32(G6::'a,H6,I6,J6,E6),f32(G6::'a,H6,I6,J6,F6))) &     \
\  (! K6 L6 M6 N6 O6 P6. equal(K6::'a,L6) --> equal(f33(K6::'a,M6,N6,O6,P6),f33(L6::'a,M6,N6,O6,P6))) &     \
\  (! Q6 S6 R6 T6 U6 V6. equal(Q6::'a,R6) --> equal(f33(S6::'a,Q6,T6,U6,V6),f33(S6::'a,R6,T6,U6,V6))) &     \
\  (! W6 Y6 Z6 X6 A7 B7. equal(W6::'a,X6) --> equal(f33(Y6::'a,Z6,W6,A7,B7),f33(Y6::'a,Z6,X6,A7,B7))) &     \
\  (! C7 E7 F7 G7 D7 H7. equal(C7::'a,D7) --> equal(f33(E7::'a,F7,G7,C7,H7),f33(E7::'a,F7,G7,D7,H7))) &     \
\  (! I7 K7 L7 M7 N7 J7. equal(I7::'a,J7) --> equal(f33(K7::'a,L7,M7,N7,I7),f33(K7::'a,L7,M7,N7,J7))) &     \
\  (! A B C. equal(A::'a,B) --> equal(apply(A::'a,C),apply(B::'a,C))) &     \
\  (! D F' E. equal(D::'a,E) --> equal(apply(F'::'a,D),apply(F'::'a,E))) &  \
\  (! G H I' J. equal(G::'a,H) --> equal(apply_to_two_arguments(G::'a,I',J),apply_to_two_arguments(H::'a,I',J))) &  \
\  (! K' M L N. equal(K'::'a,L) --> equal(apply_to_two_arguments(M::'a,K',N),apply_to_two_arguments(M::'a,L,N))) &  \
\  (! O_ Q R P. equal(O_::'a,P) --> equal(apply_to_two_arguments(Q::'a,R,O_),apply_to_two_arguments(Q::'a,R,P))) &     \
\  (! S' T'. equal(S'::'a,T') --> equal(complement(S'),complement(T'))) &   \
\  (! U V W. equal(U::'a,V) --> equal(composition(U::'a,W),composition(V::'a,W))) & \
\  (! X Z Y. equal(X::'a,Y) --> equal(composition(Z::'a,X),composition(Z::'a,Y))) & \
\  (! A1 B1. equal(A1::'a,B1) --> equal(inv1 A1,inv1 B1)) &       \
\  (! C1 D1 E1. equal(C1::'a,D1) --> equal(cross_product(C1::'a,E1),cross_product(D1::'a,E1))) &    \
\  (! F1 H1 G1. equal(F1::'a,G1) --> equal(cross_product(H1::'a,F1),cross_product(H1::'a,G1))) &    \
\  (! I1 J1. equal(I1::'a,J1) --> equal(domain_of(I1),domain_of(J1))) &     \
\  (! I10 J10. equal(I10::'a,J10) --> equal(first(I10),first(J10))) &       \
\  (! Q10 R10. equal(Q10::'a,R10) --> equal(flip_range_of(Q10),flip_range_of(R10))) &       \
\  (! S10 T10 U10. equal(S10::'a,T10) --> equal(image_(S10::'a,U10),image_(T10::'a,U10))) &   \
\  (! V10 X10 W10. equal(V10::'a,W10) --> equal(image_(X10::'a,V10),image_(X10::'a,W10))) &   \
\  (! Y10 Z10 A11. equal(Y10::'a,Z10) --> equal(intersection(Y10::'a,A11),intersection(Z10::'a,A11))) &     \
\  (! B11 D11 C11. equal(B11::'a,C11) --> equal(intersection(D11::'a,B11),intersection(D11::'a,C11))) &     \
\  (! E11 F11 G11. equal(E11::'a,F11) --> equal(non_ordered_pair(E11::'a,G11),non_ordered_pair(F11::'a,G11))) &     \
\  (! H11 J11 I11. equal(H11::'a,I11) --> equal(non_ordered_pair(J11::'a,H11),non_ordered_pair(J11::'a,I11))) &     \
\  (! K11 L11 M11. equal(K11::'a,L11) --> equal(ordered_pair(K11::'a,M11),ordered_pair(L11::'a,M11))) &     \
\  (! N11 P11 O11. equal(N11::'a,O11) --> equal(ordered_pair(P11::'a,N11),ordered_pair(P11::'a,O11))) &     \
\  (! Q11 R11. equal(Q11::'a,R11) --> equal(powerset(Q11),powerset(R11))) & \
\  (! S11 T11. equal(S11::'a,T11) --> equal(range_of(S11),range_of(T11))) & \
\  (! U11 V11 W11. equal(U11::'a,V11) --> equal(restrct(U11::'a,W11),restrct(V11::'a,W11))) &     \
\  (! X11 Z11 Y11. equal(X11::'a,Y11) --> equal(restrct(Z11::'a,X11),restrct(Z11::'a,Y11))) &     \
\  (! A12 B12. equal(A12::'a,B12) --> equal(rotate_right(A12),rotate_right(B12))) & \
\  (! C12 D12. equal(C12::'a,D12) --> equal(second(C12),second(D12))) &     \
\  (! K12 L12. equal(K12::'a,L12) --> equal(sigma(K12),sigma(L12))) &       \
\  (! M12 N12. equal(M12::'a,N12) --> equal(singleton_set(M12),singleton_set(N12))) &       \
\  (! O12 P12. equal(O12::'a,P12) --> equal(successor(O12),successor(P12))) &       \
\  (! Q12 R12 S12. equal(Q12::'a,R12) --> equal(union(Q12::'a,S12),union(R12::'a,S12))) &   \
\  (! T12 V12 U12. equal(T12::'a,U12) --> equal(union(V12::'a,T12),union(V12::'a,U12))) &   \
\  (! W12 X12 Y12. equal(W12::'a,X12) & closed(W12::'a,Y12) --> closed(X12::'a,Y12)) &      \
\  (! Z12 B13 A13. equal(Z12::'a,A13) & closed(B13::'a,Z12) --> closed(B13::'a,A13)) &      \
\  (! C13 D13 E13. equal(C13::'a,D13) & disjoint(C13::'a,E13) --> disjoint(D13::'a,E13)) &  \
\  (! F13 H13 G13. equal(F13::'a,G13) & disjoint(H13::'a,F13) --> disjoint(H13::'a,G13)) &  \
\  (! I13 J13. equal(I13::'a,J13) & function(I13) --> function(J13)) &      \
\  (! K13 L13 M13 N13 O13 P13. equal(K13::'a,L13) & homomorphism(K13::'a,M13,N13,O13,P13) --> homomorphism(L13::'a,M13,N13,O13,P13)) &      \
\  (! Q13 S13 R13 T13 U13 V13. equal(Q13::'a,R13) & homomorphism(S13::'a,Q13,T13,U13,V13) --> homomorphism(S13::'a,R13,T13,U13,V13)) &      \
\  (! W13 Y13 Z13 X13 A14 B14. equal(W13::'a,X13) & homomorphism(Y13::'a,Z13,W13,A14,B14) --> homomorphism(Y13::'a,Z13,X13,A14,B14)) &      \
\  (! C14 E14 F14 G14 D14 H14. equal(C14::'a,D14) & homomorphism(E14::'a,F14,G14,C14,H14) --> homomorphism(E14::'a,F14,G14,D14,H14)) &      \
\  (! I14 K14 L14 M14 N14 J14. equal(I14::'a,J14) & homomorphism(K14::'a,L14,M14,N14,I14) --> homomorphism(K14::'a,L14,M14,N14,J14)) &      \
\  (! O14 P14. equal(O14::'a,P14) & little_set(O14) --> little_set(P14)) &  \
\  (! Q14 R14 S14 T14. equal(Q14::'a,R14) & maps(Q14::'a,S14,T14) --> maps(R14::'a,S14,T14)) &      \
\  (! U14 W14 V14 X14. equal(U14::'a,V14) & maps(W14::'a,U14,X14) --> maps(W14::'a,V14,X14)) &      \
\  (! Y14 A15 B15 Z14. equal(Y14::'a,Z14) & maps(A15::'a,B15,Y14) --> maps(A15::'a,B15,Z14)) &      \
\  (! C15 D15 E15. equal(C15::'a,D15) & member(C15::'a,E15) --> member(D15::'a,E15)) &      \
\  (! F15 H15 G15. equal(F15::'a,G15) & member(H15::'a,F15) --> member(H15::'a,G15)) &      \
\  (! I15 J15. equal(I15::'a,J15) & one_to_one_function(I15) --> one_to_one_function(J15)) &        \
\  (! K15 L15. equal(K15::'a,L15) & ordered_pair_predicate(K15) --> ordered_pair_predicate(L15)) &  \
\  (! M15 N15 O15. equal(M15::'a,N15) & proper_subset(M15::'a,O15) --> proper_subset(N15::'a,O15)) &        \
\  (! P15 R15 Q15. equal(P15::'a,Q15) & proper_subset(R15::'a,P15) --> proper_subset(R15::'a,Q15)) &        \
\  (! S15 T15. equal(S15::'a,T15) & relation(S15) --> relation(T15)) &      \
\  (! U15 V15. equal(U15::'a,V15) & single_valued_set(U15) --> single_valued_set(V15)) &    \
\  (! W15 X15 Y15. equal(W15::'a,X15) & subset(W15::'a,Y15) --> subset(X15::'a,Y15)) &      \
\  (! Z15 B16 A16. equal(Z15::'a,A16) & subset(B16::'a,Z15) --> subset(B16::'a,A16)) &      \
\  (~little_set(ordered_pair(a::'a,b))) --> False",
  meson_tac);


(*13 inferences so far.  Searching to depth 8.  0 secs*)
val SET046_5 = prove
 ("(! Y X. ~(element(X::'a,a) & element(X::'a,Y) & element(Y::'a,X))) &     \
\  (! X. element(X::'a,f(X)) | element(X::'a,a)) &     \
\  (! X. element(f(X),X) | element(X::'a,a)) --> False",
  meson_tac);

(*33 inferences so far.  Searching to depth 9.  0.2 secs*)
val SET047_5 = prove
 ("(! X Z Y. set_equal(X::'a,Y) & element(Z::'a,X) --> element(Z::'a,Y)) &  \
\  (! Y Z X. set_equal(X::'a,Y) & element(Z::'a,Y) --> element(Z::'a,X)) &  \
\  (! X Y. element(f(X::'a,Y),X) | element(f(X::'a,Y),Y) | set_equal(X::'a,Y)) &  \
\  (! X Y. element(f(X::'a,Y),Y) & element(f(X::'a,Y),X) --> set_equal(X::'a,Y)) &  \
\  (set_equal(a::'a,b) | set_equal(b::'a,a)) & \
\  (~(set_equal(b::'a,a) & set_equal(a::'a,b))) --> False",
  meson_tac);

(*311 inferences so far.  Searching to depth 12.  0.1 secs*)
val SYN034_1 = prove
 ("(! A. p(A::'a,a) | p(A::'a,f(A))) & \
\  (! A. p(A::'a,a) | p(f(A),A)) & \
\  (! A B. ~(p(A::'a,B) & p(B::'a,A) & p(B::'a,a))) --> False",
  meson_tac);

(*30 inferences so far.  Searching to depth 6.  0.2 secs*)
val SYN071_1 = prove
 ("(! X. equal(X::'a,X)) &  \
\  (! Y X. equal(X::'a,Y) --> equal(Y::'a,X)) & \
\  (! Y X Z. equal(X::'a,Y) & equal(Y::'a,Z) --> equal(X::'a,Z)) &  \
\  (equal(a::'a,b) | equal(c::'a,d)) & \
\  (equal(a::'a,c) | equal(b::'a,d)) & \
\  (~equal(a::'a,d)) &      \
\  (~equal(b::'a,c)) --> False",
  meson_tac);

(****************SLOW
655670 inferences so far.  Searching to depth 44.  No proof after 10 minutes.
val SYN349_1 = prove_hard
 ("(! X Y. f(w(X),g(X::'a,Y)) --> f(X::'a,g(X::'a,Y))) &    \
\  (! X Y. f(X::'a,g(X::'a,Y)) --> f(w(X),g(X::'a,Y))) &    \
\  (! Y X. f(X::'a,g(X::'a,Y)) & f(Y::'a,g(X::'a,Y)) --> f(g(X::'a,Y),Y) | f(g(X::'a,Y),w(X))) &       \
\  (! Y X. f(g(X::'a,Y),Y) & f(Y::'a,g(X::'a,Y)) --> f(X::'a,g(X::'a,Y)) | f(g(X::'a,Y),w(X))) &       \
\  (! Y X. f(X::'a,g(X::'a,Y)) | f(g(X::'a,Y),Y) | f(Y::'a,g(X::'a,Y)) | f(g(X::'a,Y),w(X))) &       \
\  (! Y X. f(X::'a,g(X::'a,Y)) & f(g(X::'a,Y),Y) --> f(Y::'a,g(X::'a,Y)) | f(g(X::'a,Y),w(X))) &       \
\  (! Y X. f(X::'a,g(X::'a,Y)) & f(g(X::'a,Y),w(X)) --> f(g(X::'a,Y),Y) | f(Y::'a,g(X::'a,Y))) &       \
\  (! Y X. f(g(X::'a,Y),Y) & f(g(X::'a,Y),w(X)) --> f(X::'a,g(X::'a,Y)) | f(Y::'a,g(X::'a,Y))) &       \
\  (! Y X. f(Y::'a,g(X::'a,Y)) & f(g(X::'a,Y),w(X)) --> f(X::'a,g(X::'a,Y)) | f(g(X::'a,Y),Y)) &       \
\  (! Y X. ~(f(X::'a,g(X::'a,Y)) & f(g(X::'a,Y),Y) & f(Y::'a,g(X::'a,Y)) & f(g(X::'a,Y),w(X)))) --> False",
  meson_tac);
****************)

(*398 inferences so far.  Searching to depth 12.  0.4 secs*)
val SYN352_1 = prove
 ("(f(a::'a,b)) &   \
\  (! X Y. f(X::'a,Y) --> f(b::'a,z(X::'a,Y)) | f(Y::'a,z(X::'a,Y))) &     \
\  (! X Y. f(X::'a,Y) | f(z(X::'a,Y),z(X::'a,Y))) &        \
\  (! X Y. f(b::'a,z(X::'a,Y)) | f(X::'a,z(X::'a,Y)) | f(z(X::'a,Y),z(X::'a,Y))) &    \
\  (! X Y. f(b::'a,z(X::'a,Y)) & f(X::'a,z(X::'a,Y)) --> f(z(X::'a,Y),z(X::'a,Y))) &    \
\  (! X Y. ~(f(X::'a,Y) & f(X::'a,z(X::'a,Y)) & f(Y::'a,z(X::'a,Y)))) &     \
\  (! X Y. f(X::'a,Y) --> f(X::'a,z(X::'a,Y)) | f(Y::'a,z(X::'a,Y))) --> False",
  meson_tac);

(*5336 inferences so far.  Searching to depth 15.  5.3 secs*)
val TOP001_2 = prove_hard
 ("(! Vf U. element_of_set(U::'a,union_of_members(Vf)) --> element_of_set(U::'a,f1(Vf::'a,U))) &    \
\  (! U Vf. element_of_set(U::'a,union_of_members(Vf)) --> element_of_collection(f1(Vf::'a,U),Vf)) &    \
\  (! U Uu1 Vf. element_of_set(U::'a,Uu1) & element_of_collection(Uu1::'a,Vf) --> element_of_set(U::'a,union_of_members(Vf))) &     \
\  (! Vf X. basis(X::'a,Vf) --> equal_sets(union_of_members(Vf),X)) &       \
\  (! Vf U X. element_of_collection(U::'a,top_of_basis(Vf)) & element_of_set(X::'a,U) --> element_of_set(X::'a,f10(Vf::'a,U,X))) &      \
\  (! U X Vf. element_of_collection(U::'a,top_of_basis(Vf)) & element_of_set(X::'a,U) --> element_of_collection(f10(Vf::'a,U,X),Vf)) &      \
\  (! X. subset_sets(X::'a,X)) &    \
\  (! X U Y. subset_sets(X::'a,Y) & element_of_set(U::'a,X) --> element_of_set(U::'a,Y)) &  \
\  (! X Y. equal_sets(X::'a,Y) --> subset_sets(X::'a,Y)) &      \
\  (! Y X. subset_sets(X::'a,Y) | element_of_set(in_1st_set(X::'a,Y),X)) &     \
\  (! X Y. element_of_set(in_1st_set(X::'a,Y),Y) --> subset_sets(X::'a,Y)) &    \
\  (basis(cx::'a,f)) &      \
\  (~subset_sets(union_of_members(top_of_basis(f)),cx)) --> False",
  meson_tac);

(*0 inferences so far.  Searching to depth 0.  0 secs*)
val TOP002_2 = prove
 ("(! Vf U. element_of_collection(U::'a,top_of_basis(Vf)) | element_of_set(f11(Vf::'a,U),U)) & \
\  (! X. ~element_of_set(X::'a,empty_set)) &        \
\  (~element_of_collection(empty_set::'a,top_of_basis(f))) --> False",
  meson_tac);

(*0 inferences so far.  Searching to depth 0.  6.5 secs.  BIG*)
val TOP004_1 = prove_hard
 ("(! Vf U. element_of_set(U::'a,union_of_members(Vf)) --> element_of_set(U::'a,f1(Vf::'a,U))) &    \
\  (! U Vf. element_of_set(U::'a,union_of_members(Vf)) --> element_of_collection(f1(Vf::'a,U),Vf)) &    \
\  (! U Uu1 Vf. element_of_set(U::'a,Uu1) & element_of_collection(Uu1::'a,Vf) --> element_of_set(U::'a,union_of_members(Vf))) &     \
\  (! Vf U Va. element_of_set(U::'a,intersection_of_members(Vf)) & element_of_collection(Va::'a,Vf) --> element_of_set(U::'a,Va)) & \
\  (! U Vf. element_of_set(U::'a,intersection_of_members(Vf)) | element_of_collection(f2(Vf::'a,U),Vf)) &      \
\  (! Vf U. element_of_set(U::'a,f2(Vf::'a,U)) --> element_of_set(U::'a,intersection_of_members(Vf))) &     \
\  (! Vt X. topological_space(X::'a,Vt) --> equal_sets(union_of_members(Vt),X)) &   \
\  (! X Vt. topological_space(X::'a,Vt) --> element_of_collection(empty_set::'a,Vt)) &  \
\  (! X Vt. topological_space(X::'a,Vt) --> element_of_collection(X::'a,Vt)) &  \
\  (! X Y Z Vt. topological_space(X::'a,Vt) & element_of_collection(Y::'a,Vt) & element_of_collection(Z::'a,Vt) --> element_of_collection(intersection_of_sets(Y::'a,Z),Vt)) &  \
\  (! X Vf Vt. topological_space(X::'a,Vt) & subset_collections(Vf::'a,Vt) --> element_of_collection(union_of_members(Vf),Vt)) &        \
\  (! X Vt. equal_sets(union_of_members(Vt),X) & element_of_collection(empty_set::'a,Vt) & element_of_collection(X::'a,Vt) --> topological_space(X::'a,Vt) | element_of_collection(f3(X::'a,Vt),Vt) | subset_collections(f5(X::'a,Vt),Vt)) &      \
\  (! X Vt. equal_sets(union_of_members(Vt),X) & element_of_collection(empty_set::'a,Vt) & element_of_collection(X::'a,Vt) & element_of_collection(union_of_members(f5(X::'a,Vt)),Vt) --> topological_space(X::'a,Vt) | element_of_collection(f3(X::'a,Vt),Vt)) &  \
\  (! X Vt. equal_sets(union_of_members(Vt),X) & element_of_collection(empty_set::'a,Vt) & element_of_collection(X::'a,Vt) --> topological_space(X::'a,Vt) | element_of_collection(f4(X::'a,Vt),Vt) | subset_collections(f5(X::'a,Vt),Vt)) &      \
\  (! X Vt. equal_sets(union_of_members(Vt),X) & element_of_collection(empty_set::'a,Vt) & element_of_collection(X::'a,Vt) & element_of_collection(union_of_members(f5(X::'a,Vt)),Vt) --> topological_space(X::'a,Vt) | element_of_collection(f4(X::'a,Vt),Vt)) &  \
\  (! X Vt. equal_sets(union_of_members(Vt),X) & element_of_collection(empty_set::'a,Vt) & element_of_collection(X::'a,Vt) & element_of_collection(intersection_of_sets(f3(X::'a,Vt),f4(X::'a,Vt)),Vt) --> topological_space(X::'a,Vt) | subset_collections(f5(X::'a,Vt),Vt)) &        \
\  (! X Vt. equal_sets(union_of_members(Vt),X) & element_of_collection(empty_set::'a,Vt) & element_of_collection(X::'a,Vt) & element_of_collection(intersection_of_sets(f3(X::'a,Vt),f4(X::'a,Vt)),Vt) & element_of_collection(union_of_members(f5(X::'a,Vt)),Vt) --> topological_space(X::'a,Vt)) &    \
\  (! U X Vt. open(U::'a,X,Vt) --> topological_space(X::'a,Vt)) &       \
\  (! X U Vt. open(U::'a,X,Vt) --> element_of_collection(U::'a,Vt)) &   \
\  (! X U Vt. topological_space(X::'a,Vt) & element_of_collection(U::'a,Vt) --> open(U::'a,X,Vt)) & \
\  (! U X Vt. closed(U::'a,X,Vt) --> topological_space(X::'a,Vt)) &     \
\  (! U X Vt. closed(U::'a,X,Vt) --> open(relative_complement_sets(U::'a,X),X,Vt)) &    \
\  (! U X Vt. topological_space(X::'a,Vt) & open(relative_complement_sets(U::'a,X),X,Vt) --> closed(U::'a,X,Vt)) &  \
\  (! Vs X Vt. finer(Vt::'a,Vs,X) --> topological_space(X::'a,Vt)) &    \
\  (! Vt X Vs. finer(Vt::'a,Vs,X) --> topological_space(X::'a,Vs)) &    \
\  (! X Vs Vt. finer(Vt::'a,Vs,X) --> subset_collections(Vs::'a,Vt)) &  \
\  (! X Vs Vt. topological_space(X::'a,Vt) & topological_space(X::'a,Vs) & subset_collections(Vs::'a,Vt) --> finer(Vt::'a,Vs,X)) &      \
\  (! Vf X. basis(X::'a,Vf) --> equal_sets(union_of_members(Vf),X)) &       \
\  (! X Vf Y Vb1 Vb2. basis(X::'a,Vf) & element_of_set(Y::'a,X) & element_of_collection(Vb1::'a,Vf) & element_of_collection(Vb2::'a,Vf) & element_of_set(Y::'a,intersection_of_sets(Vb1::'a,Vb2)) --> element_of_set(Y::'a,f6(X::'a,Vf,Y,Vb1,Vb2))) &   \
\  (! X Y Vb1 Vb2 Vf. basis(X::'a,Vf) & element_of_set(Y::'a,X) & element_of_collection(Vb1::'a,Vf) & element_of_collection(Vb2::'a,Vf) & element_of_set(Y::'a,intersection_of_sets(Vb1::'a,Vb2)) --> element_of_collection(f6(X::'a,Vf,Y,Vb1,Vb2),Vf)) &   \
\  (! X Vf Y Vb1 Vb2. basis(X::'a,Vf) & element_of_set(Y::'a,X) & element_of_collection(Vb1::'a,Vf) & element_of_collection(Vb2::'a,Vf) & element_of_set(Y::'a,intersection_of_sets(Vb1::'a,Vb2)) --> subset_sets(f6(X::'a,Vf,Y,Vb1,Vb2),intersection_of_sets(Vb1::'a,Vb2))) &  \
\  (! Vf X. equal_sets(union_of_members(Vf),X) --> basis(X::'a,Vf) | element_of_set(f7(X::'a,Vf),X)) & \
\  (! X Vf. equal_sets(union_of_members(Vf),X) --> basis(X::'a,Vf) | element_of_collection(f8(X::'a,Vf),Vf)) & \
\  (! X Vf. equal_sets(union_of_members(Vf),X) --> basis(X::'a,Vf) | element_of_collection(f9(X::'a,Vf),Vf)) & \
\  (! X Vf. equal_sets(union_of_members(Vf),X) --> basis(X::'a,Vf) | element_of_set(f7(X::'a,Vf),intersection_of_sets(f8(X::'a,Vf),f9(X::'a,Vf)))) &   \
\  (! Uu9 X Vf. equal_sets(union_of_members(Vf),X) & element_of_set(f7(X::'a,Vf),Uu9) & element_of_collection(Uu9::'a,Vf) & subset_sets(Uu9::'a,intersection_of_sets(f8(X::'a,Vf),f9(X::'a,Vf))) --> basis(X::'a,Vf)) & \
\  (! Vf U X. element_of_collection(U::'a,top_of_basis(Vf)) & element_of_set(X::'a,U) --> element_of_set(X::'a,f10(Vf::'a,U,X))) &      \
\  (! U X Vf. element_of_collection(U::'a,top_of_basis(Vf)) & element_of_set(X::'a,U) --> element_of_collection(f10(Vf::'a,U,X),Vf)) &      \
\  (! Vf X U. element_of_collection(U::'a,top_of_basis(Vf)) & element_of_set(X::'a,U) --> subset_sets(f10(Vf::'a,U,X),U)) & \
\  (! Vf U. element_of_collection(U::'a,top_of_basis(Vf)) | element_of_set(f11(Vf::'a,U),U)) & \
\  (! Vf Uu11 U. element_of_set(f11(Vf::'a,U),Uu11) & element_of_collection(Uu11::'a,Vf) & subset_sets(Uu11::'a,U) --> element_of_collection(U::'a,top_of_basis(Vf))) & \
\  (! U Y X Vt. element_of_collection(U::'a,subspace_topology(X::'a,Vt,Y)) --> topological_space(X::'a,Vt)) &       \
\  (! U Vt Y X. element_of_collection(U::'a,subspace_topology(X::'a,Vt,Y)) --> subset_sets(Y::'a,X)) &      \
\  (! X Y U Vt. element_of_collection(U::'a,subspace_topology(X::'a,Vt,Y)) --> element_of_collection(f12(X::'a,Vt,Y,U),Vt)) &       \
\  (! X Vt Y U. element_of_collection(U::'a,subspace_topology(X::'a,Vt,Y)) --> equal_sets(U::'a,intersection_of_sets(Y::'a,f12(X::'a,Vt,Y,U)))) &   \
\  (! X Vt U Y Uu12. topological_space(X::'a,Vt) & subset_sets(Y::'a,X) & element_of_collection(Uu12::'a,Vt) & equal_sets(U::'a,intersection_of_sets(Y::'a,Uu12)) --> element_of_collection(U::'a,subspace_topology(X::'a,Vt,Y))) & \
\  (! U Y X Vt. element_of_set(U::'a,interior(Y::'a,X,Vt)) --> topological_space(X::'a,Vt)) &       \
\  (! U Vt Y X. element_of_set(U::'a,interior(Y::'a,X,Vt)) --> subset_sets(Y::'a,X)) &      \
\  (! Y X Vt U. element_of_set(U::'a,interior(Y::'a,X,Vt)) --> element_of_set(U::'a,f13(Y::'a,X,Vt,U))) &       \
\  (! X Vt U Y. element_of_set(U::'a,interior(Y::'a,X,Vt)) --> subset_sets(f13(Y::'a,X,Vt,U),Y)) &  \
\  (! Y U X Vt. element_of_set(U::'a,interior(Y::'a,X,Vt)) --> open(f13(Y::'a,X,Vt,U),X,Vt)) &      \
\  (! U Y Uu13 X Vt. topological_space(X::'a,Vt) & subset_sets(Y::'a,X) & element_of_set(U::'a,Uu13) & subset_sets(Uu13::'a,Y) & open(Uu13::'a,X,Vt) --> element_of_set(U::'a,interior(Y::'a,X,Vt))) &      \
\  (! U Y X Vt. element_of_set(U::'a,closure(Y::'a,X,Vt)) --> topological_space(X::'a,Vt)) &        \
\  (! U Vt Y X. element_of_set(U::'a,closure(Y::'a,X,Vt)) --> subset_sets(Y::'a,X)) &       \
\  (! Y X Vt U V. element_of_set(U::'a,closure(Y::'a,X,Vt)) & subset_sets(Y::'a,V) & closed(V::'a,X,Vt) --> element_of_set(U::'a,V)) &      \
\  (! Y X Vt U. topological_space(X::'a,Vt) & subset_sets(Y::'a,X) --> element_of_set(U::'a,closure(Y::'a,X,Vt)) | subset_sets(Y::'a,f14(Y::'a,X,Vt,U))) &     \
\  (! Y U X Vt. topological_space(X::'a,Vt) & subset_sets(Y::'a,X) --> element_of_set(U::'a,closure(Y::'a,X,Vt)) | closed(f14(Y::'a,X,Vt,U),X,Vt)) &       \
\  (! Y X Vt U. topological_space(X::'a,Vt) & subset_sets(Y::'a,X) & element_of_set(U::'a,f14(Y::'a,X,Vt,U)) --> element_of_set(U::'a,closure(Y::'a,X,Vt))) &   \
\  (! U Y X Vt. neighborhood(U::'a,Y,X,Vt) --> topological_space(X::'a,Vt)) &   \
\  (! Y U X Vt. neighborhood(U::'a,Y,X,Vt) --> open(U::'a,X,Vt)) &      \
\  (! X Vt Y U. neighborhood(U::'a,Y,X,Vt) --> element_of_set(Y::'a,U)) &       \
\  (! X Vt Y U. topological_space(X::'a,Vt) & open(U::'a,X,Vt) & element_of_set(Y::'a,U) --> neighborhood(U::'a,Y,X,Vt)) &      \
\  (! Z Y X Vt. limit_point(Z::'a,Y,X,Vt) --> topological_space(X::'a,Vt)) &    \
\  (! Z Vt Y X. limit_point(Z::'a,Y,X,Vt) --> subset_sets(Y::'a,X)) &   \
\  (! Z X Vt U Y. limit_point(Z::'a,Y,X,Vt) & neighborhood(U::'a,Z,X,Vt) --> element_of_set(f15(Z::'a,Y,X,Vt,U),intersection_of_sets(U::'a,Y))) &       \
\  (! Y X Vt U Z. ~(limit_point(Z::'a,Y,X,Vt) & neighborhood(U::'a,Z,X,Vt) & eq_p(f15(Z::'a,Y,X,Vt,U),Z))) &        \
\  (! Y Z X Vt. topological_space(X::'a,Vt) & subset_sets(Y::'a,X) --> limit_point(Z::'a,Y,X,Vt) | neighborhood(f16(Z::'a,Y,X,Vt),Z,X,Vt)) &   \
\  (! X Vt Y Uu16 Z. topological_space(X::'a,Vt) & subset_sets(Y::'a,X) & element_of_set(Uu16::'a,intersection_of_sets(f16(Z::'a,Y,X,Vt),Y)) --> limit_point(Z::'a,Y,X,Vt) | eq_p(Uu16::'a,Z)) &       \
\  (! U Y X Vt. element_of_set(U::'a,boundary(Y::'a,X,Vt)) --> topological_space(X::'a,Vt)) &       \
\  (! U Y X Vt. element_of_set(U::'a,boundary(Y::'a,X,Vt)) --> element_of_set(U::'a,closure(Y::'a,X,Vt))) &     \
\  (! U Y X Vt. element_of_set(U::'a,boundary(Y::'a,X,Vt)) --> element_of_set(U::'a,closure(relative_complement_sets(Y::'a,X),X,Vt))) & \
\  (! U Y X Vt. topological_space(X::'a,Vt) & element_of_set(U::'a,closure(Y::'a,X,Vt)) & element_of_set(U::'a,closure(relative_complement_sets(Y::'a,X),X,Vt)) --> element_of_set(U::'a,boundary(Y::'a,X,Vt))) &   \
\  (! X Vt. hausdorff(X::'a,Vt) --> topological_space(X::'a,Vt)) &      \
\  (! X_2 X_1 X Vt. hausdorff(X::'a,Vt) & element_of_set(X_1::'a,X) & element_of_set(X_2::'a,X) --> eq_p(X_1::'a,X_2) | neighborhood(f17(X::'a,Vt,X_1,X_2),X_1,X,Vt)) &    \
\  (! X_1 X_2 X Vt. hausdorff(X::'a,Vt) & element_of_set(X_1::'a,X) & element_of_set(X_2::'a,X) --> eq_p(X_1::'a,X_2) | neighborhood(f18(X::'a,Vt,X_1,X_2),X_2,X,Vt)) &    \
\  (! X Vt X_1 X_2. hausdorff(X::'a,Vt) & element_of_set(X_1::'a,X) & element_of_set(X_2::'a,X) --> eq_p(X_1::'a,X_2) | disjoint_s(f17(X::'a,Vt,X_1,X_2),f18(X::'a,Vt,X_1,X_2))) &     \
\  (! Vt X. topological_space(X::'a,Vt) --> hausdorff(X::'a,Vt) | element_of_set(f19(X::'a,Vt),X)) &       \
\  (! Vt X. topological_space(X::'a,Vt) --> hausdorff(X::'a,Vt) | element_of_set(f20(X::'a,Vt),X)) &       \
\  (! X Vt. topological_space(X::'a,Vt) & eq_p(f19(X::'a,Vt),f20(X::'a,Vt)) --> hausdorff(X::'a,Vt)) &  \
\  (! X Vt Uu19 Uu20. topological_space(X::'a,Vt) & neighborhood(Uu19::'a,f19(X::'a,Vt),X,Vt) & neighborhood(Uu20::'a,f20(X::'a,Vt),X,Vt) & disjoint_s(Uu19::'a,Uu20) --> hausdorff(X::'a,Vt)) &    \
\  (! Va1 Va2 X Vt. separation(Va1::'a,Va2,X,Vt) --> topological_space(X::'a,Vt)) &     \
\  (! Va2 X Vt Va1. ~(separation(Va1::'a,Va2,X,Vt) & equal_sets(Va1::'a,empty_set))) &  \
\  (! Va1 X Vt Va2. ~(separation(Va1::'a,Va2,X,Vt) & equal_sets(Va2::'a,empty_set))) &  \
\  (! Va2 X Va1 Vt. separation(Va1::'a,Va2,X,Vt) --> element_of_collection(Va1::'a,Vt)) &       \
\  (! Va1 X Va2 Vt. separation(Va1::'a,Va2,X,Vt) --> element_of_collection(Va2::'a,Vt)) &       \
\  (! Vt Va1 Va2 X. separation(Va1::'a,Va2,X,Vt) --> equal_sets(union_of_sets(Va1::'a,Va2),X)) &        \
\  (! X Vt Va1 Va2. separation(Va1::'a,Va2,X,Vt) --> disjoint_s(Va1::'a,Va2)) & \
\  (! Vt X Va1 Va2. topological_space(X::'a,Vt) & element_of_collection(Va1::'a,Vt) & element_of_collection(Va2::'a,Vt) & equal_sets(union_of_sets(Va1::'a,Va2),X) & disjoint_s(Va1::'a,Va2) --> separation(Va1::'a,Va2,X,Vt) | equal_sets(Va1::'a,empty_set) | equal_sets(Va2::'a,empty_set)) &      \
\  (! X Vt. connected_space(X::'a,Vt) --> topological_space(X::'a,Vt)) &        \
\  (! Va1 Va2 X Vt. ~(connected_space(X::'a,Vt) & separation(Va1::'a,Va2,X,Vt))) &      \
\  (! X Vt. topological_space(X::'a,Vt) --> connected_space(X::'a,Vt) | separation(f21(X::'a,Vt),f22(X::'a,Vt),X,Vt)) &        \
\  (! Va X Vt. connected_set(Va::'a,X,Vt) --> topological_space(X::'a,Vt)) &    \
\  (! Vt Va X. connected_set(Va::'a,X,Vt) --> subset_sets(Va::'a,X)) &  \
\  (! X Vt Va. connected_set(Va::'a,X,Vt) --> connected_space(Va::'a,subspace_topology(X::'a,Vt,Va))) &     \
\  (! X Vt Va. topological_space(X::'a,Vt) & subset_sets(Va::'a,X) & connected_space(Va::'a,subspace_topology(X::'a,Vt,Va)) --> connected_set(Va::'a,X,Vt)) &       \
\  (! Vf X Vt. open_covering(Vf::'a,X,Vt) --> topological_space(X::'a,Vt)) &    \
\  (! X Vf Vt. open_covering(Vf::'a,X,Vt) --> subset_collections(Vf::'a,Vt)) &  \
\  (! Vt Vf X. open_covering(Vf::'a,X,Vt) --> equal_sets(union_of_members(Vf),X)) & \
\  (! Vt Vf X. topological_space(X::'a,Vt) & subset_collections(Vf::'a,Vt) & equal_sets(union_of_members(Vf),X) --> open_covering(Vf::'a,X,Vt)) &   \
\  (! X Vt. compact_space(X::'a,Vt) --> topological_space(X::'a,Vt)) &  \
\  (! X Vt Vf1. compact_space(X::'a,Vt) & open_covering(Vf1::'a,X,Vt) --> finite(f23(X::'a,Vt,Vf1))) &      \
\  (! X Vt Vf1. compact_space(X::'a,Vt) & open_covering(Vf1::'a,X,Vt) --> subset_collections(f23(X::'a,Vt,Vf1),Vf1)) &      \
\  (! Vf1 X Vt. compact_space(X::'a,Vt) & open_covering(Vf1::'a,X,Vt) --> open_covering(f23(X::'a,Vt,Vf1),X,Vt)) &  \
\  (! X Vt. topological_space(X::'a,Vt) --> compact_space(X::'a,Vt) | open_covering(f24(X::'a,Vt),X,Vt)) & \
\  (! Uu24 X Vt. topological_space(X::'a,Vt) & finite(Uu24) & subset_collections(Uu24::'a,f24(X::'a,Vt)) & open_covering(Uu24::'a,X,Vt) --> compact_space(X::'a,Vt)) &      \
\  (! Va X Vt. compact_set(Va::'a,X,Vt) --> topological_space(X::'a,Vt)) &      \
\  (! Vt Va X. compact_set(Va::'a,X,Vt) --> subset_sets(Va::'a,X)) &    \
\  (! X Vt Va. compact_set(Va::'a,X,Vt) --> compact_space(Va::'a,subspace_topology(X::'a,Vt,Va))) & \
\  (! X Vt Va. topological_space(X::'a,Vt) & subset_sets(Va::'a,X) & compact_space(Va::'a,subspace_topology(X::'a,Vt,Va)) --> compact_set(Va::'a,X,Vt)) &   \
\  (basis(cx::'a,f)) &      \
\  (! U. element_of_collection(U::'a,top_of_basis(f))) &    \
\  (! V. element_of_collection(V::'a,top_of_basis(f))) &    \
\  (! U V. ~element_of_collection(intersection_of_sets(U::'a,V),top_of_basis(f))) --> False",
  meson_tac);


(*0 inferences so far.  Searching to depth 0.  0.8 secs*)
val TOP004_2 = prove
 ("(! U Uu1 Vf. element_of_set(U::'a,Uu1) & element_of_collection(Uu1::'a,Vf) --> element_of_set(U::'a,union_of_members(Vf))) &     \
\  (! Vf X. basis(X::'a,Vf) --> equal_sets(union_of_members(Vf),X)) &       \
\  (! X Vf Y Vb1 Vb2. basis(X::'a,Vf) & element_of_set(Y::'a,X) & element_of_collection(Vb1::'a,Vf) & element_of_collection(Vb2::'a,Vf) & element_of_set(Y::'a,intersection_of_sets(Vb1::'a,Vb2)) --> element_of_set(Y::'a,f6(X::'a,Vf,Y,Vb1,Vb2))) &   \
\  (! X Y Vb1 Vb2 Vf. basis(X::'a,Vf) & element_of_set(Y::'a,X) & element_of_collection(Vb1::'a,Vf) & element_of_collection(Vb2::'a,Vf) & element_of_set(Y::'a,intersection_of_sets(Vb1::'a,Vb2)) --> element_of_collection(f6(X::'a,Vf,Y,Vb1,Vb2),Vf)) &   \
\  (! X Vf Y Vb1 Vb2. basis(X::'a,Vf) & element_of_set(Y::'a,X) & element_of_collection(Vb1::'a,Vf) & element_of_collection(Vb2::'a,Vf) & element_of_set(Y::'a,intersection_of_sets(Vb1::'a,Vb2)) --> subset_sets(f6(X::'a,Vf,Y,Vb1,Vb2),intersection_of_sets(Vb1::'a,Vb2))) &  \
\  (! Vf U X. element_of_collection(U::'a,top_of_basis(Vf)) & element_of_set(X::'a,U) --> element_of_set(X::'a,f10(Vf::'a,U,X))) &      \
\  (! U X Vf. element_of_collection(U::'a,top_of_basis(Vf)) & element_of_set(X::'a,U) --> element_of_collection(f10(Vf::'a,U,X),Vf)) &      \
\  (! Vf X U. element_of_collection(U::'a,top_of_basis(Vf)) & element_of_set(X::'a,U) --> subset_sets(f10(Vf::'a,U,X),U)) & \
\  (! Vf U. element_of_collection(U::'a,top_of_basis(Vf)) | element_of_set(f11(Vf::'a,U),U)) & \
\  (! Vf Uu11 U. element_of_set(f11(Vf::'a,U),Uu11) & element_of_collection(Uu11::'a,Vf) & subset_sets(Uu11::'a,U) --> element_of_collection(U::'a,top_of_basis(Vf))) & \
\  (! Y X Z. subset_sets(X::'a,Y) & subset_sets(Y::'a,Z) --> subset_sets(X::'a,Z)) &        \
\  (! Y Z X. element_of_set(Z::'a,intersection_of_sets(X::'a,Y)) --> element_of_set(Z::'a,X)) &     \
\  (! X Z Y. element_of_set(Z::'a,intersection_of_sets(X::'a,Y)) --> element_of_set(Z::'a,Y)) &     \
\  (! X Z Y. element_of_set(Z::'a,X) & element_of_set(Z::'a,Y) --> element_of_set(Z::'a,intersection_of_sets(X::'a,Y))) &       \
\  (! X U Y V. subset_sets(X::'a,Y) & subset_sets(U::'a,V) --> subset_sets(intersection_of_sets(X::'a,U),intersection_of_sets(Y::'a,V))) &      \
\  (! X Z Y. equal_sets(X::'a,Y) & element_of_set(Z::'a,X) --> element_of_set(Z::'a,Y)) &   \
\  (! Y X. equal_sets(intersection_of_sets(X::'a,Y),intersection_of_sets(Y::'a,X))) &   \
\  (basis(cx::'a,f)) &      \
\  (! U. element_of_collection(U::'a,top_of_basis(f))) &    \
\  (! V. element_of_collection(V::'a,top_of_basis(f))) &    \
\  (! U V. ~element_of_collection(intersection_of_sets(U::'a,V),top_of_basis(f))) --> False",
  meson_tac);

(*53777 inferences so far.  Searching to depth 20.  68.7 secs*)
val TOP005_2 = prove_hard
 ("(! Vf U. element_of_set(U::'a,union_of_members(Vf)) --> element_of_set(U::'a,f1(Vf::'a,U))) &    \
\  (! U Vf. element_of_set(U::'a,union_of_members(Vf)) --> element_of_collection(f1(Vf::'a,U),Vf)) &    \
\  (! Vf U X. element_of_collection(U::'a,top_of_basis(Vf)) & element_of_set(X::'a,U) --> element_of_set(X::'a,f10(Vf::'a,U,X))) &      \
\  (! U X Vf. element_of_collection(U::'a,top_of_basis(Vf)) & element_of_set(X::'a,U) --> element_of_collection(f10(Vf::'a,U,X),Vf)) &      \
\  (! Vf X U. element_of_collection(U::'a,top_of_basis(Vf)) & element_of_set(X::'a,U) --> subset_sets(f10(Vf::'a,U,X),U)) & \
\  (! Vf U. element_of_collection(U::'a,top_of_basis(Vf)) | element_of_set(f11(Vf::'a,U),U)) & \
\  (! Vf Uu11 U. element_of_set(f11(Vf::'a,U),Uu11) & element_of_collection(Uu11::'a,Vf) & subset_sets(Uu11::'a,U) --> element_of_collection(U::'a,top_of_basis(Vf))) & \
\  (! X U Y. element_of_set(U::'a,X) --> subset_sets(X::'a,Y) | element_of_set(U::'a,Y)) & \
\  (! Y X Z. subset_sets(X::'a,Y) & element_of_collection(Y::'a,Z) --> subset_sets(X::'a,union_of_members(Z))) &    \
\  (! X U Y. subset_collections(X::'a,Y) & element_of_collection(U::'a,X) --> element_of_collection(U::'a,Y)) &     \
\  (subset_collections(g::'a,top_of_basis(f))) &    \
\  (~element_of_collection(union_of_members(g),top_of_basis(f))) --> False",
  meson_tac);


