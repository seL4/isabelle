(*  Title:      HOL/ex/Sudoku.thy
    Author:     Tjark Weber
    Copyright   2005-2014
*)

section \<open>A SAT-based Sudoku Solver\<close>

theory Sudoku
imports Main
begin

text \<open>
  See the paper ``A SAT-based Sudoku Solver'' (Tjark Weber, published at
  LPAR'05) for further explanations.  (The paper describes an older version of
  this theory that used the model finder \<open>refute\<close> to find Sudoku
  solutions.  The \<open>refute\<close> tool has since been superseded by
  \<open>nitpick\<close>, which is used below.)
\<close>

no_notation Groups.one_class.one (\<open>1\<close>)

datatype digit = A (\<open>1\<close>) | B (\<open>2\<close>) | C (\<open>3\<close>) | D (\<open>4\<close>) | E (\<open>5\<close>) | F (\<open>6\<close>) | G (\<open>7\<close>) | H (\<open>8\<close>) | I (\<open>9\<close>)

definition valid :: "digit => digit => digit => digit => digit => digit => digit => digit => digit => bool" where

  "valid x1 x2 x3 x4 x5 x6 x7 x8 x9 ==
    (x1 \<noteq> x2) \<and> (x1 \<noteq> x3) \<and> (x1 \<noteq> x4) \<and> (x1 \<noteq> x5) \<and> (x1 \<noteq> x6) \<and> (x1 \<noteq> x7) \<and> (x1 \<noteq> x8) \<and> (x1 \<noteq> x9)
    \<and> (x2 \<noteq> x3) \<and> (x2 \<noteq> x4) \<and> (x2 \<noteq> x5) \<and> (x2 \<noteq> x6) \<and> (x2 \<noteq> x7) \<and> (x2 \<noteq> x8) \<and> (x2 \<noteq> x9)
    \<and> (x3 \<noteq> x4) \<and> (x3 \<noteq> x5) \<and> (x3 \<noteq> x6) \<and> (x3 \<noteq> x7) \<and> (x3 \<noteq> x8) \<and> (x3 \<noteq> x9)
    \<and> (x4 \<noteq> x5) \<and> (x4 \<noteq> x6) \<and> (x4 \<noteq> x7) \<and> (x4 \<noteq> x8) \<and> (x4 \<noteq> x9)
    \<and> (x5 \<noteq> x6) \<and> (x5 \<noteq> x7) \<and> (x5 \<noteq> x8) \<and> (x5 \<noteq> x9)
    \<and> (x6 \<noteq> x7) \<and> (x6 \<noteq> x8) \<and> (x6 \<noteq> x9)
    \<and> (x7 \<noteq> x8) \<and> (x7 \<noteq> x9)
    \<and> (x8 \<noteq> x9)"

definition sudoku :: "digit => digit => digit => digit => digit => digit => digit => digit => digit =>
    digit => digit => digit => digit => digit => digit => digit => digit => digit =>
    digit => digit => digit => digit => digit => digit => digit => digit => digit =>
    digit => digit => digit => digit => digit => digit => digit => digit => digit =>
    digit => digit => digit => digit => digit => digit => digit => digit => digit =>
    digit => digit => digit => digit => digit => digit => digit => digit => digit =>
    digit => digit => digit => digit => digit => digit => digit => digit => digit =>
    digit => digit => digit => digit => digit => digit => digit => digit => digit =>
    digit => digit => digit => digit => digit => digit => digit => digit => digit => bool" where

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

text \<open>
  Just an arbitrary Sudoku grid:
\<close>

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
  nitpick [expect=genuine]
oops

text \<open>
  An ``easy'' Sudoku:
\<close>

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
  nitpick [expect=genuine]
oops

text \<open>
  A ``hard'' Sudoku:
\<close>

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
  nitpick [expect=genuine]
oops

text \<open>
  Some ``exceptionally difficult'' Sudokus, taken from
  \<^url>\<open>https://en.wikipedia.org/w/index.php?title=Algorithmics_of_sudoku&oldid=254685903\<close>
  (accessed December~2, 2008).
\<close>

text \<open>
\begin{verbatim}
Rating Program: gsf's sudoku q1 (rating) 
Rating: 99408 
Poster: JPF 
Label: Easter Monster 
1.......2.9.4...5...6...7...5.9.3.......7.......85..4.7.....6...3...9.8...2.....1 
1 . . | . . . | . . 2  
. 9 . | 4 . . | . 5 .  
. . 6 | . . . | 7 . .  
------+-------+------ 
. 5 . | 9 . 3 | . . .  
. . . | . 7 . | . . .  
. . . | 8 5 . | . 4 .  
------+-------+------ 
7 . . | . . . | 6 . .  
. 3 . | . . 9 | . 8 .  
. . 2 | . . . | . . 1  
\end{verbatim}
\<close>

theorem "\<not> sudoku
     1  x12 x13 x14 x15 x16 x17 x18  2 
    x21  9  x23  4  x25 x26 x27  5  x29
    x31 x32  6  x34 x35 x36  7  x38 x39
    x41  5  x43  9  x45  3  x47 x48 x49
    x51 x52 x53 x54  7  x56 x57 x58 x59
    x61 x62 x63  8   5  x66 x67  4  x69
     7  x72 x73 x74 x75 x76  6  x78 x79
    x81  3  x83 x84 x85  9  x87  8  x89
    x91 x92  2  x94 x95 x96 x97 x98  1 "
  nitpick [expect=genuine]
oops

text \<open>
\begin{verbatim}
Rating Program: gsf's sudoku q1 (Processing time) 
Rating: 4m19s@2 GHz 
Poster: tarek 
Label: tarek071223170000-052 
..1..4.......6.3.5...9.....8.....7.3.......285...7.6..3...8...6..92......4...1... 
. . 1 | . . 4 | . . .  
. . . | . 6 . | 3 . 5  
. . . | 9 . . | . . .  
------+-------+------ 
8 . . | . . . | 7 . 3  
. . . | . . . | . 2 8  
5 . . | . 7 . | 6 . .  
------+-------+------ 
3 . . | . 8 . | . . 6  
. . 9 | 2 . . | . . .  
. 4 . | . . 1 | . . .  
\end{verbatim}
\<close>

theorem "\<not> sudoku
    x11 x12  1  x14 x15  4  x17 x18 x19
    x21 x22 x23 x24  6  x26  3  x28  5 
    x31 x32 x33  9  x35 x36 x37 x38 x39
     8  x42 x43 x44 x45 x46  7  x48  3 
    x51 x52 x53 x54 x55 x56 x57  2   8 
     5  x62 x63 x64  7  x66  6  x68 x69
     3  x72 x73 x74  8  x76 x77 x78  6 
    x81 x82  9   2  x85 x86 x87 x88 x89
    x91  4  x93 x94 x95  1  x97 x98 x99"
  nitpick [expect=genuine]
oops

text \<open>
\begin{verbatim}
Rating Program: Nicolas Juillerat's Sudoku explainer 1.2.1 
Rating: 11.9 
Poster: tarek 
Label: golden nugget 
.......39.....1..5..3.5.8....8.9...6.7...2...1..4.......9.8..5..2....6..4..7..... 
. . . | . . . | . 3 9  
. . . | . . 1 | . . 5  
. . 3 | . 5 . | 8 . .  
------+-------+------ 
. . 8 | . 9 . | . . 6  
. 7 . | . . 2 | . . .  
1 . . | 4 . . | . . .  
------+-------+------ 
. . 9 | . 8 . | . 5 .  
. 2 . | . . . | 6 . .  
4 . . | 7 . . | . . .  
\end{verbatim}
\<close>

theorem "\<not> sudoku
    x11 x12 x13 x14 x15 x16 x17  3   9 
    x21 x22 x23 x24 x25  1  x27 x28  5 
    x31 x32  3  x34  5  x36  8  x38 x39
    x41 x42  8  x44  9  x46 x47 x48  6 
    x51  7  x53 x54 x55  2  x57 x58 x59
     1  x62 x63  4  x65 x66 x67 x68 x69
    x71 x72  9  x74  8  x76 x77  5  x79
    x81  2  x83 x84 x85 x86  6  x88 x89
     4  x92 x93  7  x95 x96 x97 x98 x99"
  nitpick [expect=genuine]
oops

text \<open>
\begin{verbatim}
Rating Program: dukuso's suexrat9 
Rating: 4483 
Poster: coloin 
Label: col-02-08-071 
.2.4.37.........32........4.4.2...7.8...5.........1...5.....9...3.9....7..1..86.. 
. 2 . | 4 . 3 | 7 . .  
. . . | . . . | . 3 2  
. . . | . . . | . . 4  
------+-------+------ 
. 4 . | 2 . . | . 7 .  
8 . . | . 5 . | . . .  
. . . | . . 1 | . . .  
------+-------+------ 
5 . . | . . . | 9 . .  
. 3 . | 9 . . | . . 7  
. . 1 | . . 8 | 6 . .  
\end{verbatim}
\<close>

theorem "\<not> sudoku
    x11  2  x13  4  x15  3   7  x18 x19
    x21 x22 x23 x24 x25 x26 x27  3   2 
    x31 x32 x33 x34 x35 x36 x37 x38  4 
    x41  4  x43  2  x45 x46 x47  7  x49
     8  x52 x53 x54  5  x56 x57 x58 x59
    x61 x62 x63 x64 x65  1  x67 x68 x69
     5  x72 x73 x74 x75 x76  9  x78 x79
    x81  3  x83  9  x85 x86 x87 x88  7 
    x91 x92  1  x94 x95  8   6  x98 x99"
  nitpick [expect=genuine]
oops

text \<open>
\begin{verbatim}
Rating Program: dukuso's suexratt (10000 2 option) 
Rating: 2141 
Poster: tarek 
Label: golden nugget 
.......39.....1..5..3.5.8....8.9...6.7...2...1..4.......9.8..5..2....6..4..7..... 
. . . | . . . | . 3 9  
. . . | . . 1 | . . 5  
. . 3 | . 5 . | 8 . .  
------+-------+------ 
. . 8 | . 9 . | . . 6  
. 7 . | . . 2 | . . .  
1 . . | 4 . . | . . .  
------+-------+------ 
. . 9 | . 8 . | . 5 .  
. 2 . | . . . | 6 . .  
4 . . | 7 . . | . . .
\end{verbatim}
\<close>

theorem "\<not> sudoku
    x11 x12 x13 x14 x15 x16 x17  3   9 
    x21 x22 x23 x24 x25  1  x27 x28  5 
    x31 x32  3  x34  5  x36  8  x38 x39
    x41 x42  8  x44  9  x46 x47 x48  6 
    x51  7  x53 x54 x55  2  x57 x58 x59
     1  x62 x63  4  x65 x66 x67 x68 x69
    x71 x72  9  x74  8  x76 x77  5  x79
    x81  2  x83 x84 x85 x86  6  x88 x89
     4  x92 x93  7  x95 x96 x97 x98 x99"
  nitpick [expect=genuine]
oops

end
