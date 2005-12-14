(*  Title:      Sudoku.thy
    ID:         $Id$
    Author:     Tjark Weber
    Copyright   2005
*)

header {* A SAT-based Sudoku Solver *}

theory Sudoku

imports Main

begin

text {*
  Please make sure you are using an efficient SAT solver (e.g. zChaff)
  when loading this theory.  See Isabelle's settings file for details.

  See the paper "A SAT-based Sudoku Solver" (Tjark Weber, published at
  LPAR'05) for further explanations.
*}

datatype digit = A ("1") | B ("2") | C ("3") | D ("4") | E ("5") | F ("6") | G ("7") | H ("8") | I ("9")

constdefs
  valid :: "digit => digit => digit => digit => digit => digit => digit => digit => digit => bool"

  "valid x1 x2 x3 x4 x5 x6 x7 x8 x9 ==
    (x1 \<noteq> x2) \<and> (x1 \<noteq> x3) \<and> (x1 \<noteq> x4) \<and> (x1 \<noteq> x5) \<and> (x1 \<noteq> x6) \<and> (x1 \<noteq> x7) \<and> (x1 \<noteq> x8) \<and> (x1 \<noteq> x9)
    \<and> (x2 \<noteq> x3) \<and> (x2 \<noteq> x4) \<and> (x2 \<noteq> x5) \<and> (x2 \<noteq> x6) \<and> (x2 \<noteq> x7) \<and> (x2 \<noteq> x8) \<and> (x2 \<noteq> x9)
    \<and> (x3 \<noteq> x4) \<and> (x3 \<noteq> x5) \<and> (x3 \<noteq> x6) \<and> (x3 \<noteq> x7) \<and> (x3 \<noteq> x8) \<and> (x3 \<noteq> x9)
    \<and> (x4 \<noteq> x5) \<and> (x4 \<noteq> x6) \<and> (x4 \<noteq> x7) \<and> (x4 \<noteq> x8) \<and> (x4 \<noteq> x9)
    \<and> (x5 \<noteq> x6) \<and> (x5 \<noteq> x7) \<and> (x5 \<noteq> x8) \<and> (x5 \<noteq> x9)
    \<and> (x6 \<noteq> x7) \<and> (x6 \<noteq> x8) \<and> (x6 \<noteq> x9)
    \<and> (x7 \<noteq> x8) \<and> (x7 \<noteq> x9)
    \<and> (x8 \<noteq> x9)"

constdefs
  sudoku :: "digit => digit => digit => digit => digit => digit => digit => digit => digit =>
    digit => digit => digit => digit => digit => digit => digit => digit => digit =>
    digit => digit => digit => digit => digit => digit => digit => digit => digit =>
    digit => digit => digit => digit => digit => digit => digit => digit => digit =>
    digit => digit => digit => digit => digit => digit => digit => digit => digit =>
    digit => digit => digit => digit => digit => digit => digit => digit => digit =>
    digit => digit => digit => digit => digit => digit => digit => digit => digit =>
    digit => digit => digit => digit => digit => digit => digit => digit => digit =>
    digit => digit => digit => digit => digit => digit => digit => digit => digit => bool"

  "sudoku x11 x12 x13 x14 x15 x16 x17 x18 x19
          x21 x22 x23 x24 x25 x26 x27 x28 x29
          x31 x32 x33 x34 x35 x36 x37 x38 x39
          x41 x42 x43 x44 x45 x46 x47 x48 x49
          x51 x52 x53 x54 x55 x56 x57 x58 x59
          x61 x62 x63 x64 x65 x66 x67 x68 x69
          x71 x72 x73 x74 x75 x76 x77 x78 x79
          x81 x82 x83 x84 x85 x86 x87 x88 x89
          x91 x92 x93 x94 x95 x96 x97 x98 x99 ==

       valid x11 x12 x13 x14 x15 x16 x17 x18 x19
     \<and> valid x21 x22 x23 x24 x25 x26 x27 x28 x29
     \<and> valid x31 x32 x33 x34 x35 x36 x37 x38 x39
     \<and> valid x41 x42 x43 x44 x45 x46 x47 x48 x49
     \<and> valid x51 x52 x53 x54 x55 x56 x57 x58 x59
     \<and> valid x61 x62 x63 x64 x65 x66 x67 x68 x69
     \<and> valid x71 x72 x73 x74 x75 x76 x77 x78 x79
     \<and> valid x81 x82 x83 x84 x85 x86 x87 x88 x89
     \<and> valid x91 x92 x93 x94 x95 x96 x97 x98 x99

     \<and> valid x11 x21 x31 x41 x51 x61 x71 x81 x91
     \<and> valid x12 x22 x32 x42 x52 x62 x72 x82 x92
     \<and> valid x13 x23 x33 x43 x53 x63 x73 x83 x93
     \<and> valid x14 x24 x34 x44 x54 x64 x74 x84 x94
     \<and> valid x15 x25 x35 x45 x55 x65 x75 x85 x95
     \<and> valid x16 x26 x36 x46 x56 x66 x76 x86 x96
     \<and> valid x17 x27 x37 x47 x57 x67 x77 x87 x97
     \<and> valid x18 x28 x38 x48 x58 x68 x78 x88 x98
     \<and> valid x19 x29 x39 x49 x59 x69 x79 x89 x99

     \<and> valid x11 x12 x13 x21 x22 x23 x31 x32 x33
     \<and> valid x14 x15 x16 x24 x25 x26 x34 x35 x36
     \<and> valid x17 x18 x19 x27 x28 x29 x37 x38 x39
     \<and> valid x41 x42 x43 x51 x52 x53 x61 x62 x63
     \<and> valid x44 x45 x46 x54 x55 x56 x64 x65 x66
     \<and> valid x47 x48 x49 x57 x58 x59 x67 x68 x69
     \<and> valid x71 x72 x73 x81 x82 x83 x91 x92 x93
     \<and> valid x74 x75 x76 x84 x85 x86 x94 x95 x96
     \<and> valid x77 x78 x79 x87 x88 x89 x97 x98 x99"

text {*
  Just an arbitrary Sudoku grid:
*}

theorem "\<not> sudoku
    x11 x12 x13 x14 x15 x16 x17 x18 x19
    x21 x22 x23 x24 x25 x26 x27 x28 x29
    x31 x32 x33 x34 x35 x36 x37 x38 x39
    x41 x42 x43 x44 x45 x46 x47 x48 x49
    x51 x52 x53 x54 x55 x56 x57 x58 x59
    x61 x62 x63 x64 x65 x66 x67 x68 x69
    x71 x72 x73 x74 x75 x76 x77 x78 x79
    x81 x82 x83 x84 x85 x86 x87 x88 x89
    x91 x92 x93 x94 x95 x96 x97 x98 x99"
  apply (unfold sudoku_def valid_def)
  refute
oops

text {*
  An "easy" Sudoku:
*}

theorem "\<not> sudoku
     5   3  x13 x14  7  x16 x17 x18 x19
     6  x22 x23  1   9   5  x27 x28 x29
    x31  9   8  x34 x35 x36 x37  6  x39
     8  x42 x43 x44  6  x46 x47 x48  3 
     4  x52 x53  8  x55  3  x57 x58  1 
     7  x62 x63 x64  2  x66 x67 x68  6 
    x71  6  x73 x74 x75 x76  2   8  x79
    x81 x82 x83  4   1   9  x87 x88  5 
    x91 x92 x93 x94  8  x96 x97  7   9 "
  apply (unfold sudoku_def valid_def)
  refute
oops

text {*
  A "hard" Sudoku:
*}

theorem "\<not> sudoku
    x11  2  x13 x14 x15 x16 x17 x18 x19
    x21 x22 x23  6  x25 x26 x27 x28  3 
    x31  7   4  x34  8  x36 x37 x38 x39
    x41 x42 x43 x44 x45  3  x47 x48  2 
    x51  8  x53 x54  4  x56 x57  1  x59
     6  x62 x63  5  x65 x66 x67 x68 x69
    x71 x72 x73 x74  1  x76  7   8  x79
     5  x82 x83 x84 x85  9  x87 x88 x89
    x91 x92 x93 x94 x95 x96 x97  4  x99"
  apply (unfold sudoku_def valid_def)
  refute
oops

end
