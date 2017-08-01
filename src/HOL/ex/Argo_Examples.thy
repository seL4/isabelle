(*  Title:      HOL/ex/Argo_Examples.thy
    Author:     Sascha Boehme
*)

section \<open>Argo\<close>

theory Argo_Examples
imports Complex_Main
begin

text \<open>
  This theory is intended to showcase and test different features of the \<open>argo\<close> proof method.

  The \<open>argo\<close> proof method can be applied to propositional problems, problems involving equality
  reasoning and problems of linear real arithmetic.

  The \<open>argo\<close> proof method provides two options. To specify an upper limit of the proof methods
  run time in seconds, use the option \<open>argo_timeout\<close>. To specify the amount of output, use the
  option \<open>argo_trace\<close> with value \<open>none\<close> for no tracing output, value \<open>basic\<close> for viewing the
  underlying propositions and some timings, and value \<open>full\<close> for additionally inspecting the
  proof replay steps.
\<close>

declare[[argo_trace = full]]

subsection \<open>Propositional logic\<close>

notepad
begin
  have "True" by argo
next
  have "~False" by argo
next
  fix P :: bool
  assume "False"
  then have "P" by argo
next
  fix P :: bool
  assume "~True"
  then have "P" by argo
next
  fix P :: bool
  assume "P"
  then have "P" by argo
next
  fix P :: bool
  assume "~~P"
  then have "P" by argo
next
  fix P Q R :: bool
  assume "P & Q & R"
  then have "R & P & Q" by argo
next
  fix P Q R :: bool
  assume "P & (Q & True & R) & (Q & P) & True"
  then have "R & P & Q" by argo
next
  fix P Q1 Q2 Q3 Q4 Q5 :: bool
  assume "Q1 & (Q2 & P & Q3) & (Q4 & ~P & Q5)"
  then have "~True" by argo
next
  fix P Q1 Q2 Q3  :: bool
  assume "(Q1 & False) & Q2 & Q3"
  then have "P::bool" by argo
next
  fix P Q R :: bool
  assume "P | Q | R"
  then have "R | P | Q" by argo
next
  fix P Q R :: bool
  assume "P | (Q | False | R) | (Q | P) | False"
  then have "R | P | Q" by argo
next
  fix P Q1 Q2 Q3 Q4 :: bool
  have "(Q1 & P & Q2) --> False | (Q3 | (Q4 | P) | False)" by argo
next
  fix Q1 Q2 Q3 Q4 :: bool
  have "Q1 | (Q2 | True | Q3) | Q4" by argo
next
  fix P Q R :: bool
  assume "(P & Q) | (P & ~Q) | (P & R) | (P & ~R)"
  then have "P" by argo
next
  fix P :: bool
  assume "P = True"
  then have "P" by argo
next
  fix P :: bool
  assume "False = P"
  then have "~P" by argo
next
  fix P Q :: bool
  assume "P = (~P)"
  then have "Q" by argo
next
  fix P :: bool
  have "(~P) = (~P)" by argo
next
  fix P Q :: bool
  assume "P" and "~Q"
  then have "P = (~Q)" by argo
next
  fix P Q :: bool
  assume "((P::bool) = Q) | (Q = P)"
  then have "(P --> Q) & (Q --> P)" by argo
next
  fix P Q :: bool
  assume "(P::bool) = Q"
  then have "Q = P" by argo
next
  fix P Q R :: bool
  assume "if P then Q else R"
  then have "Q | R" by argo
next
  fix P Q :: bool
  assume "P | Q"
     and "P | ~Q"
     and "~P | Q"
     and "~P | ~Q"
  then have "False" by argo
next
  fix P Q R :: bool
  assume "P | Q | R"
     and "P | Q | ~R"
     and "P | ~Q | R"
     and "P | ~Q | ~R"
     and "~P | Q | R"
     and "~P | Q | ~R"
     and "~P | ~Q | R"
     and "~P | ~Q | ~R"
  then have "False" by argo
next
  fix a b c d e f g h i j k l m n p q :: bool
  assume "(a & b | c & d) & (e & f | g & h) | (i & j | k & l) & (m & n | p & q)"
  then have "(a & b | c & d) & (e & f | g & h) | (i & j | k & l) & (m & n | p & q)" by argo
next
  fix P :: bool
  have "P=P=P=P=P=P=P=P=P=P" by argo
next
  fix a b c d e f p q x :: bool
  assume "a | b | c | d"
     and "e | f | (a & d)"
     and "~(a | (c & ~c)) | b"
     and "~(b & (x | ~x)) | c"
     and "~(d | False) | c"
     and "~(c | (~p & (p | (q & ~q))))"
  then have "False" by argo
next
  have "(True & True & True) = True" by argo
next
  have "(False | False | False) = False" by argo
end


subsection \<open>Equality, congruence and predicates\<close>

notepad
begin
  fix t :: "'a"
  have "t = t" by argo
next
  fix t u :: "'a"
  assume "t = u"
  then have "u = t" by argo
next
  fix s t u :: "'a"
  assume "s = t" and "t = u"
  then have "s = u" by argo
next
  fix s t u v :: "'a"
  assume "s = t" and "t = u" and "u = v" and "u = s"
  then have "s = v" by argo
next
  fix s t u v w :: "'a"
  assume "s = t" and "t = u" and "s = v" and "v = w"
  then have "w = u" by argo
next
  fix s t u a b c :: "'a"
  assume "s = t" and "t = u" and "a = b" and "b = c"
  then have "s = a --> c = u" by argo
next
  fix a b c d :: "'a"
  assume "(a = b & b = c) | (a = d & d = c)"
  then have "a = c" by argo
next
  fix a b1 b2 b3 b4 c d :: "'a"
  assume "(a = b1 & ((b1 = b2 & b2 = b3) | (b1 = b4 & b4 = b3)) & b3 = c) | (a = d & d = c)"
  then have "a = c" by argo
next
  fix a b :: "'a"
  have "(if True then a else b) = a" by argo
next
  fix a b :: "'a"
  have "(if False then a else b) = b" by argo
next
  fix a b :: "'a"
  have "(if \<not>True then a else b) = b" by argo
next
  fix a b :: "'a"
  have "(if \<not>False then a else b) = a" by argo
next
  fix P :: "bool"
  fix a :: "'a"
  have "(if P then a else a) = a" by argo
next
  fix P :: "bool"
  fix a b c :: "'a"
  assume "P" and "a = c"
  then have "(if P then a else b) = c" by argo
next
  fix P :: "bool"
  fix a b c :: "'a"
  assume "~P" and "b = c"
  then have "(if P then a else b) = c" by argo
next
  fix P Q :: "bool"
  fix a b c d :: "'a"
  assume "P" and "Q" and "a = d"
  then have "(if P then (if Q then a else b) else c) = d" by argo
next
  fix a b c :: "'a"
  assume "a \<noteq> b" and "b = c"
  then have "a \<noteq> c" by argo
next
  fix a b c :: "'a"
  assume "a \<noteq> b" and "a = c"
  then have "c \<noteq> b" by argo
next
  fix a b c d :: "'a"
  assume "a = b" and "c = d" and "b \<noteq> d"
  then have "a \<noteq> c" by argo
next
  fix a b c d :: "'a"
  assume "a = b" and "c = d" and "d \<noteq> b"
  then have "a \<noteq> c" by argo
next
  fix a b c d :: "'a"
  assume "a = b" and "c = d" and "b \<noteq> d"
  then have "c \<noteq> a" by argo
next
  fix a b c d :: "'a"
  assume "a = b" and "c = d" and "d \<noteq> b"
  then have "c \<noteq> a" by argo
next
  fix a b c d e f :: "'a"
  assume "a \<noteq> b" and "b = c" and "b = d" and "d = e" and "a = f"
  then have "f \<noteq> e" by argo
next
  fix a b :: "'a" and f :: "'a \<Rightarrow> 'a"
  assume "a = b"
  then have "f a = f b" by argo
next
  fix a b c :: "'a" and f :: "'a \<Rightarrow> 'a"
  assume "f a = f b" and "b = c"
  then have "f a = f c" by argo
next
  fix a :: "'a" and f :: "'a \<Rightarrow> 'a"
  assume "f a = a"
  then have "f (f a) = a" by argo
next
  fix a b :: "'a" and f g :: "'a \<Rightarrow> 'a"
  assume "a = b"
  then have "g (f a) = g (f b)" by argo
next
  fix a b :: "'a" and f g :: "'a \<Rightarrow> 'a"
  assume "f a = b" and "g b = a"
  then have "f (g (f a)) = b" by argo
next
  fix a b :: "'a" and g :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assume "a = b"
  then have "g a b = g b a" by argo
next
  fix a b :: "'a" and f :: "'a \<Rightarrow> 'a" and g :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assume "f a = b"
  then have "g (f a) b = g b (f a)" by argo
next
  fix a b c d e g h :: "'a" and f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assume "c = d" and "e = c" and "e = b" and "b = h" and "f g h = d" and "f g d = a"
  then have "a = b" by argo
next
  fix a b :: "'a" and P :: "'a \<Rightarrow> bool"
  assume "P a" and "a = b"
  then have "P b" by argo
next
  fix a b :: "'a" and P :: "'a \<Rightarrow> bool"
  assume "~ P a" and "a = b"
  then have "~ P b" by argo
next
  fix a b c d :: "'a" and P :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assume "P a b" and "a = c" and "b = d"
  then have "P c d" by argo
next
  fix a b c d :: "'a" and P :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assume "~ P a b" and "a = c" and "b = d"
  then have "~ P c d" by argo
end


subsection \<open>Linear real arithmetic\<close>

subsubsection \<open>Negation and subtraction\<close>

notepad
begin
  fix a b :: real
  have
    "-a = -1 * a"
    "-(-a) = a"
    "a - b = a + -1 * b"
    "a - (-b) = a + b"
    by argo+
end


subsubsection \<open>Multiplication\<close>

notepad
begin
  fix a b c d :: real
  have
    "(2::real) * 3 = 6"
    "0 * a = 0"
    "a * 0 = 0"
    "1 * a = a"
    "a * 1 = a"
    "2 * a = a * 2"
    "2 * a * 3 = 6 * a"
    "2 * a * 3 * 5 = 30 * a"
    "2 * (a * (3 * 5)) = 30 * a"
    "a * 0 * b = 0"
    "a * (0 * b) = 0"
    "a * b = b * a"
    "a * b * a = b * a * a"
    "a * (b * c) = (a * b) * c"
    "a * (b * (c * d)) = ((a * b) * c) * d"
    "a * (b * (c * d)) = ((d * c) * b) * a"
    "a * (b + c + d) = a * b + a * c + a * d"
    "(a + b + c) * d = a * d + b * d + c * d"
    by argo+
end


subsubsection \<open>Division\<close>

notepad
begin
  fix a b c d :: real
  have
    "(6::real) / 2 = 3"
    "a / 0 = a / 0"
    "a / 0 <= a / 0"
    "~(a / 0 < a / 0)"
    "0 / a = 0"
    "a / 1 = a"
    "a / 3 = 1/3 * a"
    "6 * a / 2 = 3 * a"
    "(6 * a) / 2 = 3 * a"
    "a / ((5 * b) / 2) = 2/5 * a / b"
    "a / (5 * (b / 2)) = 2/5 * a / b"
    "(a / 5) * (b / 2) = 1/10 * a * b"
    "a / (3 * b) = 1/3 * a / b"
    "(a + b) / 5 = 1/5 * a + 1/5 * b"
    "a / (5 * 1/5) = a"
    "a * (b / c) = (b * a) / c"
    "(a / b) * c = (c * a) / b"
    "(a / b) / (c / d) = (a * d) / (c * b)"
    "1 / (a * b) = 1 / (b * a)"
    "a / (3 * b) = 1 / 3 * a / b"
    "(a + b + c) / d = a / d + b / d + c / d"
    by argo+
end


subsubsection \<open>Addition\<close>

notepad
begin
  fix a b c d :: real
  have
    "a + b = b + a"
    "a + b + c = c + b + a"
    "a + b + c + d = d + c + b + a"
    "a + (b + (c + d)) = ((a + b) + c) + d"
    "(5::real) + -3 = 2"
    "(3::real) + 5 + -1 = 7"
    "2 + a = a + 2"
    "a + b + a = b + 2 * a"
    "-1 + a + -1 + 2 + b + 5/3 + b + 1/3 + 5 * b + 2/3 = 8/3 + a + 7 * b"
    "1 + b + b + 5 * b + 3 * a + 7 + a + 2 = 10 + 4 * a + 7 * b"
    by argo+
end


subsubsection \<open>Minimum and maximum\<close>

notepad
begin
  fix a b :: real
  have
    "min (3::real) 5 = 3"
    "min (5::real) 3 = 3"
    "min (3::real) (-5) = -5"
    "min (-5::real) 3 = -5"
    "min a a = a"
    "a \<le> b \<longrightarrow> min a b = a"
    "a > b \<longrightarrow> min a b = b"
    "min a b \<le> a"
    "min a b \<le> b"
    "min a b = min b a"
    by argo+
next
  fix a b :: real
  have
    "max (3::real) 5 = 5"
    "max (5::real) 3 = 5"
    "max (3::real) (-5) = 3"
    "max (-5::real) 3 = 3"
    "max a a = a"
    "a \<le> b \<longrightarrow> max a b = b"
    "a > b \<longrightarrow> max a b = a"
    "a \<le> max a b"
    "b \<le> max a b"
    "max a b = max b a"
    by argo+
next
  fix a b :: real
  have
    "min a b \<le> max a b"
    "min a b + max a b = a + b"
    "a < b \<longrightarrow> min a b < max a b"
    by argo+
end


subsubsection \<open>Absolute value\<close>

notepad
begin
  fix a :: real
  have
    "abs (3::real) = 3"
    "abs (-3::real) = 3"
    "0 \<le> abs a"
    "a \<le> abs a"
    "a \<ge> 0 \<longrightarrow> abs a = a"
    "a < 0 \<longrightarrow> abs a = -a"
    "abs (abs a) = abs a"
    by argo+
end


subsubsection \<open>Equality\<close>

notepad
begin
  fix a b c d :: real
  have
    "(3::real) = 3"
    "~((3::real) = 4)"
    "~((4::real) = 3)"
    "3 * a = 5 --> a = 5/3"
    "-3 * a = 5 --> -5/3 = a"
    "5 = 3 * a --> 5/3  = a "
    "5 = -3 * a --> a = -5/3"
    "2 + 3 * a = 4 --> a = 2/3"
    "4 = 2 + 3 * a --> 2/3 = a"
    "2 + 3 * a + 5 * b + c = 4 --> 3 * a + 5 * b + c = 2"
    "4 = 2 + 3 * a + 5 * b + c --> 2 = 3 * a + 5 * b + c"
    "-2 * a + b + -3 * c = 7 --> -7 = 2 * a + -1 * b + 3 * c"
    "7 = -2 * a + b + -3 * c --> 2 * a + -1 * b + 3 * c = -7"
    "-2 * a + b + -3 * c + 4 * d = 7 --> -7 = 2 * a + -1 * b + 3 * c + -4 * d"
    "7 = -2 * a + b + -3 * c + 4 * d --> 2 * a + -1 * b + 3 * c + -4 * d = -7"
    "a + 3 * b = 5 * c + b --> a + 2 * b + -5 * c = 0"
    by argo+
end


subsubsection \<open>Less-equal\<close>

notepad
begin
  fix a b c d :: real
  have
    "(3::real) <= 3"
    "(3::real) <= 4"
    "~((4::real) <= 3)"
    "3 * a <= 5 --> a <= 5/3"
    "-3 * a <= 5 --> -5/3 <= a"
    "5 <= 3 * a --> 5/3  <= a "
    "5 <= -3 * a --> a <= -5/3"
    "2 + 3 * a <= 4 --> a <= 2/3"
    "4 <= 2 + 3 * a --> 2/3 <= a"
    "2 + 3 * a + 5 * b + c <= 4 --> 3 * a + 5 * b + c <= 2"
    "4 <= 2 + 3 * a + 5 * b + c --> 2 <= 3 * a + 5 * b + c"
    "-2 * a + b + -3 * c <= 7 --> -7 <= 2 * a + -1 * b + 3 * c"
    "7 <= -2 * a + b + -3 * c --> 2 * a + -1 * b + 3 * c <= -7"
    "-2 * a + b + -3 * c + 4 * d <= 7 --> -7 <= 2 * a + -1 * b + 3 * c + -4 * d"
    "7 <= -2 * a + b + -3 * c + 4 * d --> 2 * a + -1 * b + 3 * c + -4 * d <= -7"
    "a + 3 * b <= 5 * c + b --> a + 2 * b + -5 * c <= 0"
    by argo+
end

subsubsection \<open>Less\<close>

notepad
begin
  fix a b c d :: real
  have
    "(3::real) < 4"
    "~((3::real) < 3)"
    "~((4::real) < 3)"
    "3 * a < 5 --> a < 5/3"
    "-3 * a < 5 --> -5/3 < a"
    "5 < 3 * a --> 5/3  < a "
    "5 < -3 * a --> a < -5/3"
    "2 + 3 * a < 4 --> a < 2/3"
    "4 < 2 + 3 * a --> 2/3 < a"
    "2 + 3 * a + 5 * b + c < 4 --> 3 * a + 5 * b + c < 2"
    "4 < 2 + 3 * a + 5 * b + c --> 2 < 3 * a + 5 * b + c"
    "-2 * a + b + -3 * c < 7 --> -7 < 2 * a + -1 * b + 3 * c"
    "7 < -2 * a + b + -3 * c --> 2 * a + -1 * b + 3 * c < -7"
    "-2 * a + b + -3 * c + 4 * d < 7 --> -7 < 2 * a + -1 * b + 3 * c + -4 * d"
    "7 < -2 * a + b + -3 * c + 4 * d --> 2 * a + -1 * b + 3 * c + -4 * d < -7"
    "a + 3 * b < 5 * c + b --> a + 2 * b + -5 * c < 0"
    by argo+
end


subsubsection \<open>Other examples\<close>

notepad
begin
  fix a b :: real
  have "f (a + b) = f (b + a)" by argo
next
  have
    "(0::real) < 1"
    "(47::real) + 11 < 8 * 15"
    by argo+
next
  fix a :: real
  assume "a < 3"
  then have "a < 5" "a <= 5" "~(5 < a)" "~(5 <= a)" by argo+
next
  fix a :: real
  assume "a <= 3"
  then have "a < 5" "a <= 5" "~(5 < a)" "~(5 <= a)" by argo+
next
  fix a :: real
  assume "~(3 < a)"
  then have "a < 5" "a <= 5" "~(5 < a)" "~(5 <= a)" by argo+
next
  fix a :: real
  assume "~(3 <= a)"
  then have "a < 5" "a <= 5" "~(5 < a)" "~(5 <= a)" by argo+
next
  fix a :: real
  have "a < 3 | a = 3 | a > 3" by argo
next
  fix a b :: real
  assume "0 < a" and "a < b"
  then have "0 < b" by argo
next
  fix a b :: real
  assume "0 < a" and "a \<le> b"
  then have "0 \<le> b" by argo
next
  fix a b :: real
  assume "0 \<le> a" and "a < b"
  then have "0 \<le> b" by argo
next
  fix a b :: real
  assume "0 \<le> a" and "a \<le> b"
  then have "0 \<le> b" by argo
next
  fix a b c :: real
  assume "2 \<le> a" and "3 \<le> b" and "c \<le> 5"
  then have "-2 * a + -3 * b + 5 * c < 13" by argo
next
  fix a b c :: real
  assume "2 \<le> a" and "3 \<le> b" and "c \<le> 5"
  then have "-2 * a + -3 * b + 5 * c \<le> 12" by argo
next
  fix a b :: real
  assume "a = 2" and "b = 3"
  then have "a + b > 5 \<or> a < b" by argo
next
  fix a b c :: real
  assume "5 < b + c" and "a + c < 0" and "a > 0"
  then have "b > 0" by argo
next
  fix a b c :: real
  assume "a + b < 7" and "5 < b + c" and "a + c < 0" and "a > 0"
  then have "0 < b \<and> b < 7" by argo
next
  fix a b c :: real
  assume "a < b" and "b < c" and "c < a"
  then have "False" by argo
next
  fix a b :: real
  assume "a - 5 > b"
  then have "b < a" by argo
next
  fix a b :: real
  have "(a - b) - a = (a - a) - b" by argo
next
  fix n m n' m' :: real
  have "
    (n < m & m < n') | (n < m & m = n') | (n < n' & n' < m) |
    (n = n' & n' < m) | (n = m & m < n') |
    (n' < m & m < n) | (n' < m & m = n) |
    (n' < n & n < m) | (n' = n & n < m) | (n' = m & m < n) |
    (m < n & n < n') | (m < n & n' = n) | (m < n' & n' < n) |
    (m = n & n < n') | (m = n' & n' < n) |
    (n' = m & m = n)"
    by argo
end


subsection \<open>Larger examples\<close>

declare[[argo_trace = basic, argo_timeout = 60]]


text \<open>Translated from TPTP problem library: PUZ015-2.006.dimacs\<close>

lemma assumes 1: "~x0"
  and 2: "~x30"
  and 3: "~x29"
  and 4: "~x59"
  and 5: "x1 | x31 | x0"
  and 6: "x2 | x32 | x1"
  and 7: "x3 | x33 | x2"
  and 8: "x4 | x34 | x3"
  and 9: "x35 | x4"
  and 10: "x5 | x36 | x30"
  and 11: "x6 | x37 | x5 | x31"
  and 12: "x7 | x38 | x6 | x32"
  and 13: "x8 | x39 | x7 | x33"
  and 14: "x9 | x40 | x8 | x34"
  and 15: "x41 | x9 | x35"
  and 16: "x10 | x42 | x36"
  and 17: "x11 | x43 | x10 | x37"
  and 18: "x12 | x44 | x11 | x38"
  and 19: "x13 | x45 | x12 | x39"
  and 20: "x14 | x46 | x13 | x40"
  and 21: "x47 | x14 | x41"
  and 22: "x15 | x48 | x42"
  and 23: "x16 | x49 | x15 | x43"
  and 24: "x17 | x50 | x16 | x44"
  and 25: "x18 | x51 | x17 | x45"
  and 26: "x19 | x52 | x18 | x46"
  and 27: "x53 | x19 | x47"
  and 28: "x20 | x54 | x48"
  and 29: "x21 | x55 | x20 | x49"
  and 30: "x22 | x56 | x21 | x50"
  and 31: "x23 | x57 | x22 | x51"
  and 32: "x24 | x58 | x23 | x52"
  and 33: "x59 | x24 | x53"
  and 34: "x25 | x54"
  and 35: "x26 | x25 | x55"
  and 36: "x27 | x26 | x56"
  and 37: "x28 | x27 | x57"
  and 38: "x29 | x28 | x58"
  and 39: "~x1 | ~x31"
  and 40: "~x1 | ~x0"
  and 41: "~x31 | ~x0"
  and 42: "~x2 | ~x32"
  and 43: "~x2 | ~x1"
  and 44: "~x32 | ~x1"
  and 45: "~x3 | ~x33"
  and 46: "~x3 | ~x2"
  and 47: "~x33 | ~x2"
  and 48: "~x4 | ~x34"
  and 49: "~x4 | ~x3"
  and 50: "~x34 | ~x3"
  and 51: "~x35 | ~x4"
  and 52: "~x5 | ~x36"
  and 53: "~x5 | ~x30"
  and 54: "~x36 | ~x30"
  and 55: "~x6 | ~x37"
  and 56: "~x6 | ~x5"
  and 57: "~x6 | ~x31"
  and 58: "~x37 | ~x5"
  and 59: "~x37 | ~x31"
  and 60: "~x5 | ~x31"
  and 61: "~x7 | ~x38"
  and 62: "~x7 | ~x6"
  and 63: "~x7 | ~x32"
  and 64: "~x38 | ~x6"
  and 65: "~x38 | ~x32"
  and 66: "~x6 | ~x32"
  and 67: "~x8 | ~x39"
  and 68: "~x8 | ~x7"
  and 69: "~x8 | ~x33"
  and 70: "~x39 | ~x7"
  and 71: "~x39 | ~x33"
  and 72: "~x7 | ~x33"
  and 73: "~x9 | ~x40"
  and 74: "~x9 | ~x8"
  and 75: "~x9 | ~x34"
  and 76: "~x40 | ~x8"
  and 77: "~x40 | ~x34"
  and 78: "~x8 | ~x34"
  and 79: "~x41 | ~x9"
  and 80: "~x41 | ~x35"
  and 81: "~x9 | ~x35"
  and 82: "~x10 | ~x42"
  and 83: "~x10 | ~x36"
  and 84: "~x42 | ~x36"
  and 85: "~x11 | ~x43"
  and 86: "~x11 | ~x10"
  and 87: "~x11 | ~x37"
  and 88: "~x43 | ~x10"
  and 89: "~x43 | ~x37"
  and 90: "~x10 | ~x37"
  and 91: "~x12 | ~x44"
  and 92: "~x12 | ~x11"
  and 93: "~x12 | ~x38"
  and 94: "~x44 | ~x11"
  and 95: "~x44 | ~x38"
  and 96: "~x11 | ~x38"
  and 97: "~x13 | ~x45"
  and 98: "~x13 | ~x12"
  and 99: "~x13 | ~x39"
  and 100: "~x45 | ~x12"
  and 101: "~x45 | ~x39"
  and 102: "~x12 | ~x39"
  and 103: "~x14 | ~x46"
  and 104: "~x14 | ~x13"
  and 105: "~x14 | ~x40"
  and 106: "~x46 | ~x13"
  and 107: "~x46 | ~x40"
  and 108: "~x13 | ~x40"
  and 109: "~x47 | ~x14"
  and 110: "~x47 | ~x41"
  and 111: "~x14 | ~x41"
  and 112: "~x15 | ~x48"
  and 113: "~x15 | ~x42"
  and 114: "~x48 | ~x42"
  and 115: "~x16 | ~x49"
  and 116: "~x16 | ~x15"
  and 117: "~x16 | ~x43"
  and 118: "~x49 | ~x15"
  and 119: "~x49 | ~x43"
  and 120: "~x15 | ~x43"
  and 121: "~x17 | ~x50"
  and 122: "~x17 | ~x16"
  and 123: "~x17 | ~x44"
  and 124: "~x50 | ~x16"
  and 125: "~x50 | ~x44"
  and 126: "~x16 | ~x44"
  and 127: "~x18 | ~x51"
  and 128: "~x18 | ~x17"
  and 129: "~x18 | ~x45"
  and 130: "~x51 | ~x17"
  and 131: "~x51 | ~x45"
  and 132: "~x17 | ~x45"
  and 133: "~x19 | ~x52"
  and 134: "~x19 | ~x18"
  and 135: "~x19 | ~x46"
  and 136: "~x52 | ~x18"
  and 137: "~x52 | ~x46"
  and 138: "~x18 | ~x46"
  and 139: "~x53 | ~x19"
  and 140: "~x53 | ~x47"
  and 141: "~x19 | ~x47"
  and 142: "~x20 | ~x54"
  and 143: "~x20 | ~x48"
  and 144: "~x54 | ~x48"
  and 145: "~x21 | ~x55"
  and 146: "~x21 | ~x20"
  and 147: "~x21 | ~x49"
  and 148: "~x55 | ~x20"
  and 149: "~x55 | ~x49"
  and 150: "~x20 | ~x49"
  and 151: "~x22 | ~x56"
  and 152: "~x22 | ~x21"
  and 153: "~x22 | ~x50"
  and 154: "~x56 | ~x21"
  and 155: "~x56 | ~x50"
  and 156: "~x21 | ~x50"
  and 157: "~x23 | ~x57"
  and 158: "~x23 | ~x22"
  and 159: "~x23 | ~x51"
  and 160: "~x57 | ~x22"
  and 161: "~x57 | ~x51"
  and 162: "~x22 | ~x51"
  and 163: "~x24 | ~x58"
  and 164: "~x24 | ~x23"
  and 165: "~x24 | ~x52"
  and 166: "~x58 | ~x23"
  and 167: "~x58 | ~x52"
  and 168: "~x23 | ~x52"
  and 169: "~x59 | ~x24"
  and 170: "~x59 | ~x53"
  and 171: "~x24 | ~x53"
  and 172: "~x25 | ~x54"
  and 173: "~x26 | ~x25"
  and 174: "~x26 | ~x55"
  and 175: "~x25 | ~x55"
  and 176: "~x27 | ~x26"
  and 177: "~x27 | ~x56"
  and 178: "~x26 | ~x56"
  and 179: "~x28 | ~x27"
  and 180: "~x28 | ~x57"
  and 181: "~x27 | ~x57"
  and 182: "~x29 | ~x28"
  and 183: "~x29 | ~x58"
  and 184: "~x28 | ~x58"
  shows "False"
    using assms
    by argo


text \<open>Translated from TPTP problem library: MSC007-1.008.dimacs\<close>

lemma assumes 1: "x0 | x1 | x2 | x3 | x4 | x5 | x6"
  and 2: "x7 | x8 | x9 | x10 | x11 | x12 | x13"
  and 3: "x14 | x15 | x16 | x17 | x18 | x19 | x20"
  and 4: "x21 | x22 | x23 | x24 | x25 | x26 | x27"
  and 5: "x28 | x29 | x30 | x31 | x32 | x33 | x34"
  and 6: "x35 | x36 | x37 | x38 | x39 | x40 | x41"
  and 7: "x42 | x43 | x44 | x45 | x46 | x47 | x48"
  and 8: "x49 | x50 | x51 | x52 | x53 | x54 | x55"
  and 9: "~x0 | ~x7"
  and 10: "~x0 | ~x14"
  and 11: "~x0 | ~x21"
  and 12: "~x0 | ~x28"
  and 13: "~x0 | ~x35"
  and 14: "~x0 | ~x42"
  and 15: "~x0 | ~x49"
  and 16: "~x7 | ~x14"
  and 17: "~x7 | ~x21"
  and 18: "~x7 | ~x28"
  and 19: "~x7 | ~x35"
  and 20: "~x7 | ~x42"
  and 21: "~x7 | ~x49"
  and 22: "~x14 | ~x21"
  and 23: "~x14 | ~x28"
  and 24: "~x14 | ~x35"
  and 25: "~x14 | ~x42"
  and 26: "~x14 | ~x49"
  and 27: "~x21 | ~x28"
  and 28: "~x21 | ~x35"
  and 29: "~x21 | ~x42"
  and 30: "~x21 | ~x49"
  and 31: "~x28 | ~x35"
  and 32: "~x28 | ~x42"
  and 33: "~x28 | ~x49"
  and 34: "~x35 | ~x42"
  and 35: "~x35 | ~x49"
  and 36: "~x42 | ~x49"
  and 37: "~x1 | ~x8"
  and 38: "~x1 | ~x15"
  and 39: "~x1 | ~x22"
  and 40: "~x1 | ~x29"
  and 41: "~x1 | ~x36"
  and 42: "~x1 | ~x43"
  and 43: "~x1 | ~x50"
  and 44: "~x8 | ~x15"
  and 45: "~x8 | ~x22"
  and 46: "~x8 | ~x29"
  and 47: "~x8 | ~x36"
  and 48: "~x8 | ~x43"
  and 49: "~x8 | ~x50"
  and 50: "~x15 | ~x22"
  and 51: "~x15 | ~x29"
  and 52: "~x15 | ~x36"
  and 53: "~x15 | ~x43"
  and 54: "~x15 | ~x50"
  and 55: "~x22 | ~x29"
  and 56: "~x22 | ~x36"
  and 57: "~x22 | ~x43"
  and 58: "~x22 | ~x50"
  and 59: "~x29 | ~x36"
  and 60: "~x29 | ~x43"
  and 61: "~x29 | ~x50"
  and 62: "~x36 | ~x43"
  and 63: "~x36 | ~x50"
  and 64: "~x43 | ~x50"
  and 65: "~x2 | ~x9"
  and 66: "~x2 | ~x16"
  and 67: "~x2 | ~x23"
  and 68: "~x2 | ~x30"
  and 69: "~x2 | ~x37"
  and 70: "~x2 | ~x44"
  and 71: "~x2 | ~x51"
  and 72: "~x9 | ~x16"
  and 73: "~x9 | ~x23"
  and 74: "~x9 | ~x30"
  and 75: "~x9 | ~x37"
  and 76: "~x9 | ~x44"
  and 77: "~x9 | ~x51"
  and 78: "~x16 | ~x23"
  and 79: "~x16 | ~x30"
  and 80: "~x16 | ~x37"
  and 81: "~x16 | ~x44"
  and 82: "~x16 | ~x51"
  and 83: "~x23 | ~x30"
  and 84: "~x23 | ~x37"
  and 85: "~x23 | ~x44"
  and 86: "~x23 | ~x51"
  and 87: "~x30 | ~x37"
  and 88: "~x30 | ~x44"
  and 89: "~x30 | ~x51"
  and 90: "~x37 | ~x44"
  and 91: "~x37 | ~x51"
  and 92: "~x44 | ~x51"
  and 93: "~x3 | ~x10"
  and 94: "~x3 | ~x17"
  and 95: "~x3 | ~x24"
  and 96: "~x3 | ~x31"
  and 97: "~x3 | ~x38"
  and 98: "~x3 | ~x45"
  and 99: "~x3 | ~x52"
  and 100: "~x10 | ~x17"
  and 101: "~x10 | ~x24"
  and 102: "~x10 | ~x31"
  and 103: "~x10 | ~x38"
  and 104: "~x10 | ~x45"
  and 105: "~x10 | ~x52"
  and 106: "~x17 | ~x24"
  and 107: "~x17 | ~x31"
  and 108: "~x17 | ~x38"
  and 109: "~x17 | ~x45"
  and 110: "~x17 | ~x52"
  and 111: "~x24 | ~x31"
  and 112: "~x24 | ~x38"
  and 113: "~x24 | ~x45"
  and 114: "~x24 | ~x52"
  and 115: "~x31 | ~x38"
  and 116: "~x31 | ~x45"
  and 117: "~x31 | ~x52"
  and 118: "~x38 | ~x45"
  and 119: "~x38 | ~x52"
  and 120: "~x45 | ~x52"
  and 121: "~x4 | ~x11"
  and 122: "~x4 | ~x18"
  and 123: "~x4 | ~x25"
  and 124: "~x4 | ~x32"
  and 125: "~x4 | ~x39"
  and 126: "~x4 | ~x46"
  and 127: "~x4 | ~x53"
  and 128: "~x11 | ~x18"
  and 129: "~x11 | ~x25"
  and 130: "~x11 | ~x32"
  and 131: "~x11 | ~x39"
  and 132: "~x11 | ~x46"
  and 133: "~x11 | ~x53"
  and 134: "~x18 | ~x25"
  and 135: "~x18 | ~x32"
  and 136: "~x18 | ~x39"
  and 137: "~x18 | ~x46"
  and 138: "~x18 | ~x53"
  and 139: "~x25 | ~x32"
  and 140: "~x25 | ~x39"
  and 141: "~x25 | ~x46"
  and 142: "~x25 | ~x53"
  and 143: "~x32 | ~x39"
  and 144: "~x32 | ~x46"
  and 145: "~x32 | ~x53"
  and 146: "~x39 | ~x46"
  and 147: "~x39 | ~x53"
  and 148: "~x46 | ~x53"
  and 149: "~x5 | ~x12"
  and 150: "~x5 | ~x19"
  and 151: "~x5 | ~x26"
  and 152: "~x5 | ~x33"
  and 153: "~x5 | ~x40"
  and 154: "~x5 | ~x47"
  and 155: "~x5 | ~x54"
  and 156: "~x12 | ~x19"
  and 157: "~x12 | ~x26"
  and 158: "~x12 | ~x33"
  and 159: "~x12 | ~x40"
  and 160: "~x12 | ~x47"
  and 161: "~x12 | ~x54"
  and 162: "~x19 | ~x26"
  and 163: "~x19 | ~x33"
  and 164: "~x19 | ~x40"
  and 165: "~x19 | ~x47"
  and 166: "~x19 | ~x54"
  and 167: "~x26 | ~x33"
  and 168: "~x26 | ~x40"
  and 169: "~x26 | ~x47"
  and 170: "~x26 | ~x54"
  and 171: "~x33 | ~x40"
  and 172: "~x33 | ~x47"
  and 173: "~x33 | ~x54"
  and 174: "~x40 | ~x47"
  and 175: "~x40 | ~x54"
  and 176: "~x47 | ~x54"
  and 177: "~x6 | ~x13"
  and 178: "~x6 | ~x20"
  and 179: "~x6 | ~x27"
  and 180: "~x6 | ~x34"
  and 181: "~x6 | ~x41"
  and 182: "~x6 | ~x48"
  and 183: "~x6 | ~x55"
  and 184: "~x13 | ~x20"
  and 185: "~x13 | ~x27"
  and 186: "~x13 | ~x34"
  and 187: "~x13 | ~x41"
  and 188: "~x13 | ~x48"
  and 189: "~x13 | ~x55"
  and 190: "~x20 | ~x27"
  and 191: "~x20 | ~x34"
  and 192: "~x20 | ~x41"
  and 193: "~x20 | ~x48"
  and 194: "~x20 | ~x55"
  and 195: "~x27 | ~x34"
  and 196: "~x27 | ~x41"
  and 197: "~x27 | ~x48"
  and 198: "~x27 | ~x55"
  and 199: "~x34 | ~x41"
  and 200: "~x34 | ~x48"
  and 201: "~x34 | ~x55"
  and 202: "~x41 | ~x48"
  and 203: "~x41 | ~x55"
  and 204: "~x48 | ~x55"
  shows "False"
    using assms
    by argo


lemma "0 \<le> (yc::real) \<and>
       0 \<le> yd \<and> 0 \<le> yb \<and> 0 \<le> ya \<Longrightarrow>
       0 \<le> yf \<and>
       0 \<le> xh \<and> 0 \<le> ye \<and> 0 \<le> yg \<Longrightarrow>
       0 \<le> yw \<and> 0 \<le> xs \<and> 0 \<le> yu \<Longrightarrow>
       0 \<le> aea \<and> 0 \<le> aee \<and> 0 \<le> aed \<Longrightarrow>
       0 \<le> zy \<and> 0 \<le> xz \<and> 0 \<le> zw \<Longrightarrow>
       0 \<le> zb \<and>
       0 \<le> za \<and> 0 \<le> yy \<and> 0 \<le> yz \<Longrightarrow>
       0 \<le> zp \<and> 0 \<le> zo \<and> 0 \<le> yq \<Longrightarrow>
       0 \<le> adp \<and> 0 \<le> aeb \<and> 0 \<le> aec \<Longrightarrow>
       0 \<le> acm \<and> 0 \<le> aco \<and> 0 \<le> acn \<Longrightarrow>
       0 \<le> abl \<Longrightarrow>
       0 \<le> zr \<and> 0 \<le> zq \<and> 0 \<le> abh \<Longrightarrow>
       0 \<le> abq \<and> 0 \<le> zd \<and> 0 \<le> abo \<Longrightarrow>
       0 \<le> acd \<and>
       0 \<le> acc \<and> 0 \<le> xi \<and> 0 \<le> acb \<Longrightarrow>
       0 \<le> acp \<and> 0 \<le> acr \<and> 0 \<le> acq \<Longrightarrow>
       0 \<le> xw \<and>
       0 \<le> xr \<and> 0 \<le> xv \<and> 0 \<le> xu \<Longrightarrow>
       0 \<le> zc \<and> 0 \<le> acg \<and> 0 \<le> ach \<Longrightarrow>
       0 \<le> zt \<and> 0 \<le> zs \<and> 0 \<le> xy \<Longrightarrow>
       0 \<le> ady \<and> 0 \<le> adw \<and> 0 \<le> zg \<Longrightarrow>
       0 \<le> abd \<and>
       0 \<le> abc \<and> 0 \<le> yr \<and> 0 \<le> abb \<Longrightarrow>
       0 \<le> adi \<and>
       0 \<le> x \<and> 0 \<le> adh \<and> 0 \<le> xa \<Longrightarrow>
       0 \<le> aak \<and> 0 \<le> aai \<and> 0 \<le> aad \<Longrightarrow>
       0 \<le> aba \<and> 0 \<le> zh \<and> 0 \<le> aay \<Longrightarrow>
       0 \<le> abg \<and> 0 \<le> ys \<and> 0 \<le> abe \<Longrightarrow>
       0 \<le> abs1 \<and>
       0 \<le> yt \<and> 0 \<le> abr \<and> 0 \<le> zu \<Longrightarrow>
       0 \<le> abv \<and>
       0 \<le> zn \<and> 0 \<le> abw \<and> 0 \<le> zm \<Longrightarrow>
       0 \<le> adl \<and> 0 \<le> adn \<Longrightarrow>
       0 \<le> acf \<and> 0 \<le> aca \<Longrightarrow>
       0 \<le> ads \<and> 0 \<le> aaq \<Longrightarrow>
       0 \<le> ada \<Longrightarrow>
       0 \<le> aaf \<and> 0 \<le> aac \<and> 0 \<le> aag \<Longrightarrow>
       0 \<le> aal \<and>
       0 \<le> acu \<and> 0 \<le> acs \<and> 0 \<le> act \<Longrightarrow>
       0 \<le> aas \<and> 0 \<le> xb \<and> 0 \<le> aat \<Longrightarrow>
       0 \<le> zk \<and> 0 \<le> zj \<and> 0 \<le> zi \<Longrightarrow>
       0 \<le> ack \<and>
       0 \<le> acj \<and> 0 \<le> xc \<and> 0 \<le> aci \<Longrightarrow>
       0 \<le> aav \<and> 0 \<le> aah \<and> 0 \<le> xd \<Longrightarrow>
       0 \<le> abt \<and>
       0 \<le> xo \<and> 0 \<le> abu \<and> 0 \<le> xn \<Longrightarrow>
       0 \<le> adc \<and>
       0 \<le> abz \<and> 0 \<le> adc \<and> 0 \<le> abz \<Longrightarrow>
       0 \<le> xt \<and>
       0 \<le> zz \<and> 0 \<le> aab \<and> 0 \<le> aaa \<Longrightarrow>
       0 \<le> adq \<and>
       0 \<le> xl \<and> 0 \<le> adr \<and> 0 \<le> adb \<Longrightarrow>
       0 \<le> zf \<and> 0 \<le> yh \<and> 0 \<le> yi \<Longrightarrow>
       0 \<le> aao \<and> 0 \<le> aam \<and> 0 \<le> xe \<Longrightarrow>
       0 \<le> abk \<and>
       0 \<le> aby \<and> 0 \<le> abj \<and> 0 \<le> abx \<Longrightarrow>
       0 \<le> yp \<Longrightarrow>
       0 \<le> yl \<and> 0 \<le> yj \<and> 0 \<le> ym \<Longrightarrow>
       0 \<le> acw \<Longrightarrow>
       0 \<le> adk \<and>
       0 \<le> adg \<and> 0 \<le> adj \<and> 0 \<le> adf \<Longrightarrow>
       0 \<le> adv \<and> 0 \<le> xf \<and> 0 \<le> adu \<Longrightarrow>
       yc + yd + yb + ya = 1 \<Longrightarrow>
       yf + xh + ye + yg = 1 \<Longrightarrow>
       yw + xs + yu = 1 \<Longrightarrow>
       aea + aee + aed = 1 \<Longrightarrow>
       zy + xz + zw = 1 \<Longrightarrow>
       zb + za + yy + yz = 1 \<Longrightarrow>
       zp + zo + yq = 1 \<Longrightarrow>
       adp + aeb + aec = 1 \<Longrightarrow>
       acm + aco + acn = 1 \<Longrightarrow>
       abl + abl = 1 \<Longrightarrow>
       zr + zq + abh = 1 \<Longrightarrow>
       abq + zd + abo = 1 \<Longrightarrow>
       acd + acc + xi + acb = 1 \<Longrightarrow>
       acp + acr + acq = 1 \<Longrightarrow>
       xw + xr + xv + xu = 1 \<Longrightarrow>
       zc + acg + ach = 1 \<Longrightarrow>
       zt + zs + xy = 1 \<Longrightarrow>
       ady + adw + zg = 1 \<Longrightarrow>
       abd + abc + yr + abb = 1 \<Longrightarrow>
       adi + x + adh + xa = 1 \<Longrightarrow>
       aak + aai + aad = 1 \<Longrightarrow>
       aba + zh + aay = 1 \<Longrightarrow>
       abg + ys + abe = 1 \<Longrightarrow>
       abs1 + yt + abr + zu = 1 \<Longrightarrow>
       abv + zn + abw + zm = 1 \<Longrightarrow>
       adl + adn = 1 \<Longrightarrow>
       acf + aca = 1 \<Longrightarrow>
       ads + aaq = 1 \<Longrightarrow>
       ada + ada = 1 \<Longrightarrow>
       aaf + aac + aag = 1 \<Longrightarrow>
       aal + acu + acs + act = 1 \<Longrightarrow>
       aas + xb + aat = 1 \<Longrightarrow>
       zk + zj + zi = 1 \<Longrightarrow>
       ack + acj + xc + aci = 1 \<Longrightarrow>
       aav + aah + xd = 1 \<Longrightarrow>
       abt + xo + abu + xn = 1 \<Longrightarrow>
       adc + abz + adc + abz = 1 \<Longrightarrow>
       xt + zz + aab + aaa = 1 \<Longrightarrow>
       adq + xl + adr + adb = 1 \<Longrightarrow>
       zf + yh + yi = 1 \<Longrightarrow>
       aao + aam + xe = 1 \<Longrightarrow>
       abk + aby + abj + abx = 1 \<Longrightarrow>
       yp + yp = 1 \<Longrightarrow>
       yl + yj + ym = 1 \<Longrightarrow>
       acw + acw + acw + acw = 1 \<Longrightarrow>
       adk + adg + adj + adf = 1 \<Longrightarrow>
       adv + xf + adu = 1 \<Longrightarrow>
       yd = 0 \<or> yb = 0 \<Longrightarrow>
       xh = 0 \<or> ye = 0 \<Longrightarrow>
       yy = 0 \<or> za = 0 \<Longrightarrow>
       acc = 0 \<or> xi = 0 \<Longrightarrow>
       xv = 0 \<or> xr = 0 \<Longrightarrow>
       yr = 0 \<or> abc = 0 \<Longrightarrow>
       zn = 0 \<or> abw = 0 \<Longrightarrow>
       xo = 0 \<or> abu = 0 \<Longrightarrow>
       xl = 0 \<or> adr = 0 \<Longrightarrow>
       (yr + abd < abl \<or>
        yr + (abd + abb) < 1) \<or>
       yr + abd = abl \<and>
       yr + (abd + abb) = 1 \<Longrightarrow>
       adb + adr < xn + abu \<or>
       adb + adr = xn + abu \<Longrightarrow>
       (abl < abt \<or> abl < abt + xo) \<or>
       abl = abt \<and> abl = abt + xo \<Longrightarrow>
       yd + yc < abc + abd \<or>
       yd + yc = abc + abd \<Longrightarrow>
       aca < abb + yr \<or> aca = abb + yr \<Longrightarrow>
       acb + acc < xu + xv \<or>
       acb + acc = xu + xv \<Longrightarrow>
       (yq < xu + xr \<or>
        yq + zp < xu + (xr + xw)) \<or>
       yq = xu + xr \<and>
       yq + zp = xu + (xr + xw) \<Longrightarrow>
       (zw < xw \<or>
        zw < xw + xv \<or>
        zw + zy < xw + (xv + xu)) \<or>
       zw = xw \<and>
       zw = xw + xv \<and>
       zw + zy = xw + (xv + xu) \<Longrightarrow>
       xs + yw < zs + zt \<or>
       xs + yw = zs + zt \<Longrightarrow>
       aab + xt < ye + yf \<or>
       aab + xt = ye + yf \<Longrightarrow>
       (ya + yb < yg + ye \<or>
        ya + (yb + yc) < yg + (ye + yf)) \<or>
       ya + yb = yg + ye \<and>
       ya + (yb + yc) = yg + (ye + yf) \<Longrightarrow>
       (xu + xv < acb + acc \<or>
        xu + (xv + xw) < acb + (acc + acd)) \<or>
       xu + xv = acb + acc \<and>
       xu + (xv + xw) = acb + (acc + acd) \<Longrightarrow>
       (zs < xz + zy \<or>
        zs + xy < xz + (zy + zw)) \<or>
       zs = xz + zy \<and>
       zs + xy = xz + (zy + zw) \<Longrightarrow>
       (zs + zt < xz + zy \<or>
        zs + (zt + xy) < xz + (zy + zw)) \<or>
       zs + zt = xz + zy \<and>
       zs + (zt + xy) = xz + (zy + zw) \<Longrightarrow>
       yg + ye < ya + yb \<or>
       yg + ye = ya + yb \<Longrightarrow>
       (abd < yc \<or> abd + abc < yc + yd) \<or>
       abd = yc \<and> abd + abc = yc + yd \<Longrightarrow>
       (ye + yf < adr + adq \<or>
        ye + (yf + yg) < adr + (adq + adb)) \<or>
       ye + yf = adr + adq \<and>
       ye + (yf + yg) = adr + (adq + adb) \<Longrightarrow>
       yh + yi < ym + yj \<or>
       yh + yi = ym + yj \<Longrightarrow>
       (abq < yl \<or> abq + abo < yl + ym) \<or>
       abq = yl \<and> abq + abo = yl + ym \<Longrightarrow>
       (yp < zp \<or>
        yp < zp + zo \<or> 1 < zp + (zo + yq)) \<or>
       yp = zp \<and>
       yp = zp + zo \<and> 1 = zp + (zo + yq) \<Longrightarrow>
       (abb + yr < aca \<or>
        abb + (yr + abd) < aca + acf) \<or>
       abb + yr = aca \<and>
       abb + (yr + abd) = aca + acf \<Longrightarrow>
       adw + zg < abe + ys \<or>
       adw + zg = abe + ys \<Longrightarrow>
       zd + abq < ys + abg \<or>
       zd + abq = ys + abg \<Longrightarrow>
       yt + abs1 < aby + abk \<or>
       yt + abs1 = aby + abk \<Longrightarrow>
       (yu < abx \<or>
        yu < abx + aby \<or>
        yu + yw < abx + (aby + abk)) \<or>
       yu = abx \<and>
       yu = abx + aby \<and>
       yu + yw = abx + (aby + abk) \<Longrightarrow>
       aaf < adv \<or> aaf = adv \<Longrightarrow>
       abj + abk < yy + zb \<or>
       abj + abk = yy + zb \<Longrightarrow>
       (abb < yz \<or>
        abb + abc < yz + za \<or>
        abb + (abc + abd) < yz + (za + zb)) \<or>
       abb = yz \<and>
       abb + abc = yz + za \<and>
       abb + (abc + abd) = yz + (za + zb) \<Longrightarrow>
       (acg + zc < zd + abq \<or>
        acg + (zc + ach)
        < zd + (abq + abo)) \<or>
       acg + zc = zd + abq \<and>
       acg + (zc + ach) =
       zd + (abq + abo) \<Longrightarrow>
       zf < acm \<or> zf = acm \<Longrightarrow>
       (zg + ady < acn + acm \<or>
        zg + (ady + adw)
        < acn + (acm + aco)) \<or>
       zg + ady = acn + acm \<and>
       zg + (ady + adw) =
       acn + (acm + aco) \<Longrightarrow>
       aay + zh < zi + zj \<or>
       aay + zh = zi + zj \<Longrightarrow>
       zy < zk \<or> zy = zk \<Longrightarrow>
       (adn < zm + zn \<or>
        adn + adl < zm + (zn + abv)) \<or>
       adn = zm + zn \<and>
       adn + adl = zm + (zn + abv) \<Longrightarrow>
       zo + zp < zs + zt \<or>
       zo + zp = zs + zt \<Longrightarrow>
       zq + zr < zs + zt \<or>
       zq + zr = zs + zt \<Longrightarrow>
       (aai < adi \<or> aai < adi + adh) \<or>
       aai = adi \<and> aai = adi + adh \<Longrightarrow>
       (abr < acj \<or>
        abr + (abs1 + zu)
        < acj + (aci + ack)) \<or>
       abr = acj \<and>
       abr + (abs1 + zu) =
       acj + (aci + ack) \<Longrightarrow>
       (abl < zw \<or> 1 < zw + zy) \<or>
       abl = zw \<and> 1 = zw + zy \<Longrightarrow>
       (zz + aaa < act + acu \<or>
        zz + (aaa + aab)
        < act + (acu + aal)) \<or>
       zz + aaa = act + acu \<and>
       zz + (aaa + aab) =
       act + (acu + aal) \<Longrightarrow>
       (aam < aac \<or> aam + aao < aac + aaf) \<or>
       aam = aac \<and> aam + aao = aac + aaf \<Longrightarrow>
       (aak < aaf \<or> aak + aad < aaf + aag) \<or>
       aak = aaf \<and> aak + aad = aaf + aag \<Longrightarrow>
       (aah < aai \<or> aah + aav < aai + aak) \<or>
       aah = aai \<and> aah + aav = aai + aak \<Longrightarrow>
       act + (acu + aal) < aam + aao \<or>
       act + (acu + aal) = aam + aao \<Longrightarrow>
       (ads < aat \<or> 1 < aat + aas) \<or>
       ads = aat \<and> 1 = aat + aas \<Longrightarrow>
       (aba < aas \<or> aba + aay < aas + aat) \<or>
       aba = aas \<and> aba + aay = aas + aat \<Longrightarrow>
       acm < aav \<or> acm = aav \<Longrightarrow>
       (ada < aay \<or> 1 < aay + aba) \<or>
       ada = aay \<and> 1 = aay + aba \<Longrightarrow>
       abb + (abc + abd) < abe + abg \<or>
       abb + (abc + abd) = abe + abg \<Longrightarrow>
       (abh < abj \<or> abh < abj + abk) \<or>
       abh = abj \<and> abh = abj + abk \<Longrightarrow>
       1 < abo + abq \<or> 1 = abo + abq \<Longrightarrow>
       (acj < abr \<or> acj + aci < abr + abs1) \<or>
       acj = abr \<and> acj + aci = abr + abs1 \<Longrightarrow>
       (abt < abv \<or> abt + abu < abv + abw) \<or>
       abt = abv \<and> abt + abu = abv + abw \<Longrightarrow>
       (abx < adc \<or> abx + aby < adc + abz) \<or>
       abx = adc \<and> abx + aby = adc + abz \<Longrightarrow>
       (acf < acd \<or>
        acf < acd + acc \<or>
        1 < acd + (acc + acb)) \<or>
       acf = acd \<and>
       acf = acd + acc \<and>
       1 = acd + (acc + acb) \<Longrightarrow>
       acc + acd < acf \<or> acc + acd = acf \<Longrightarrow>
       (acg < acq \<or> acg + ach < acq + acr) \<or>
       acg = acq \<and> acg + ach = acq + acr \<Longrightarrow>
       aci + (acj + ack) < acr + acp \<or>
       aci + (acj + ack) = acr + acp \<Longrightarrow>
       (acm < acp \<or>
        acm + acn < acp + acq \<or>
        acm + (acn + aco)
        < acp + (acq + acr)) \<or>
       acm = acp \<and>
       acm + acn = acp + acq \<and>
       acm + (acn + aco) =
       acp + (acq + acr) \<Longrightarrow>
       (acs + act < acw + acw \<or>
        acs + (act + acu)
        < acw + (acw + acw)) \<or>
       acs + act = acw + acw \<and>
       acs + (act + acu) =
       acw + (acw + acw) \<Longrightarrow>
       (ada < adb + adr \<or>
        1 < adb + (adr + adq)) \<or>
       ada = adb + adr \<and>
       1 = adb + (adr + adq) \<Longrightarrow>
       (adc + adc < adf + adg \<or>
        adc + (adc + abz)
        < adf + (adg + adk)) \<or>
       adc + adc = adf + adg \<and>
       adc + (adc + abz) =
       adf + (adg + adk) \<Longrightarrow>
       adh + adi < adj + adk \<or>
       adh + adi = adj + adk \<Longrightarrow>
       (adl < aec \<or> 1 < aec + adp) \<or>
       adl = aec \<and> 1 = aec + adp \<Longrightarrow>
       (adq < ads \<or> adq + adr < ads) \<or>
       adq = ads \<and> adq + adr = ads \<Longrightarrow>
       adu + adv < aed + aea \<or>
       adu + adv = aed + aea \<Longrightarrow>
       (adw < aee \<or> adw + ady < aee + aea) \<or>
       adw = aee \<and> adw + ady = aee + aea \<Longrightarrow>
       (aeb < aed \<or> aeb + aec < aed + aee) \<or>
       aeb = aed \<and> aeb + aec = aed + aee \<Longrightarrow>
       False"
       by argo

end
