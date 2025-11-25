(* Author: Tobias Nipkow *)

theory Time_Manual
imports "HOL-Library.Time_Commands"
begin

section \<open>Introduction\<close>

text \<open>This manual describes the framework for the automatic definition of step-counting
`running-time' functions from HOL functions. The principles of the translation are described
in Section 1.5, Running Time, of the book
  Functional Data Structures and Algorithms. A Proof Assistant Approach.
  \<^url>\<open>https://fdsa-book.net\<close>
To load the framework import \<^theory>\<open>HOL-Library.Time_Commands\<close>
The framework was implemented by Jonas Stahl.

As a first simple example consider \<open>len\<close>, which we define here returning an \<open>int\<close>
(to distinguish it from the time functions returning \<open>nat\<close>):\<close>

fun len :: "'a list \<Rightarrow> int" where
"len [] = 0" |
"len (x#xs) = 1 + len xs"

time_fun len

text\<open>
Command \<open>time_fun\<close> defines a new function \<open>T_len\<close> of type \<open>'a list \<Rightarrow> nat\<close>, the time function
for \<open>len\<close> that counts the number of computation steps. The definition is printed by \<open>time_fun\<close>:
\<open>fun T_len :: "'a list \<Rightarrow> nat" where
 T_len [] = 1 |
 T_len (x # xs) = T_len xs + 1\<close>
The details of this translation are described in the book referenced above.
This manual is about the use of the time framework.

Command \<open>time_fun f\<close> retrieves the definition of \<open>f\<close> and defines a corresponding step-counting
running-time function \<open>T_f\<close>. For all auxiliary functions used by \<open>f\<close>
(excluding constructors and predefined functions (see below)),
running time functions must already have been defined. Example:\<close>

fun aux :: "'a \<Rightarrow> 'a" where
"aux x = x"

time_fun aux

fun main :: "bool \<Rightarrow> bool" where
"main x = aux x"

time_fun main

text \<open>For functions defined by \<open>definition\<close>, there is a corresponding \<open>time_definition\<close> command.
Example:\<close>

definition gdef :: "'a \<Rightarrow> 'a" where "gdef x = x"

time_definition gdef

thm T_gdef.simps

text \<open>Note that \<open>T_gdef\<close> is defined via \<open>fun\<close>, which means that the defining equation is not named
\<open>T_gdef_def\<close> but \<open>T_gdef.simps\<close> and is a simp-rule.

The time functions for many standard functions (in particular on lists) are already
defined in theory \<open>HOL-Library.Time_Functions\<close> and basic upper bounds are proved.\<close>


section \<open>Termination\<close>

text \<open>If the definition of a recursive function requires a manual termination proof,
use \<open>time_function\<close> accompanied by a \<open>termination\<close> command.\<close>

function sum_to :: "int \<Rightarrow> int \<Rightarrow> int" where
  "sum_to i j = (if j \<le> i then 0 else i + sum_to (i+1) j)"
by pat_completeness auto
termination
  by (relation "measure (\<lambda>(i,j). nat(j - i))") auto

time_function sum_to
termination
  by (relation "measure (\<lambda>(i,j). nat(j - i))") auto


section \<open>Partial Functions\<close>

text \<open>Partial functions can also be `timed'.\<close>

(* Partial functions defined with \<open>function\<close> can currently not be timed:
function pos1 :: "int \<Rightarrow> bool" where
"pos1 i = (if i = 1 then True else pos1 (i-1))"
by auto

time_function pos1

function T_pos1 :: "int \<Rightarrow> nat" where
"T_pos1 i = (if i = 1 then 1 else T_pos1 (i-1) + 1)"
by auto
*)

partial_function (tailrec) positive :: "int \<Rightarrow> bool" where
"positive i = (if i = 1 then True else positive (i-1))"

time_partial_function positive

text \<open>The difference is that \<open>T_positive\<close> has return type \<open>nat option\<close> because \<open>positive\<close>
may not terminate.

Timing a function defined with \<open>partial_function (option)\<close> is trickier and we do not go into it here.\<close>


section \<open>Higher-Order Functions\<close>

text \<open>A large subclass of higher-order functions are supported, covering \<open>map\<close>, \<open>filter\<close> and other
standard functions. For example,\<close>

time_fun map

text \<open>defines a time function \<open>T_map :: ('a \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat\<close>.
The first argument (called \<open>T_f\<close> below) is the time function for the first argument \<open>f\<close> of \<open>map\<close>.
We ignore the definition of \<open>T_map\<close> because the output of \<open>time_fun map\<close>
suggests that you should add these lemmas\<close>

lemma T_map_simps [simp,code]:
  "T_map T_f [] = 1"
  "T_map T_f (x # xs) = T_f x + T_map T_f xs + 1"
by (simp_all add: T_map_def)

text\<open>which are what you would expect as defining equations.
You can click on the suggestion to have it copied into your theory.
Afterwards, you can work with \<open>T_map\<close> as if it were defined via those equations.

In general, things are a bit more complicated, which is why \<open>T_map\<close> is defined the way it is.
Consider\<close>

fun foldl :: "('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b" where
"foldl f a [] = a" |
"foldl f a (x # xs) = foldl f (f a x) xs"

time_fun foldl

text\<open>This definition is generated:

\<open>fun T_foldl :: ('b \<Rightarrow> 'a \<Rightarrow> 'b) \<times> ('b \<Rightarrow> 'a \<Rightarrow> nat) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> nat where
 T_foldl (f,T_f) a [] = 1 |
 T_foldl (f,T_f) a (x # xs) = T_f a x + T_foldl f (f a x) xs + 1\<close>

The meaning of the pair \<open>(f, T_f)\<close> is obvious. The difference to \<open>T_map\<close> is
that \<open>T_foldl\<close> needs not just \<open>T_f\<close> (like \<open>T_map\<close>) but also \<open>f\<close>. Function \<open>T_map\<close> does not need \<open>f\<close>:
in the recursion equation \<open>map f (x # xs) = f x # map f xs\<close> the result of subterm \<open>f x\<close>
is irrelevant for the computation of \<open>T_map\<close> because the running time of \<open>(#)\<close> is constant.
This is in contrast to \<open>foldl\<close>, whose running time may depend on its second argument.

All higher-order functions are translated like \<open>foldl\<close>, but if the first element in \<open>(f,T_f)\<close>
is unused, a simplified definition is derived. This is the case for \<open>T_map\<close>.

In case you wonder how it is ensured that \<open>T_foldl\<close> is always passed a corresponding pair
of a function and its timing function: this is the responsibility of the time framework
when translating functions that use \<open>foldl\<close>. Example:\<close>

definition inc :: "int \<Rightarrow> 'a \<Rightarrow> int" where "inc i x = i+1"
definition "len2 xs = foldl inc 0 xs"
time_definition inc
time_definition len2

text \<open>In the defining equation \<open>T_len2 xs = T_foldl (inc, T_inc) 0 xs\<close>
we find the correct pair \<open>(inc, T_inc)\<close>.\<close>


subsection \<open>Limitations\<close>

text\<open>Partial application and lambda-abstraction are currently not supported.
They need to be replaced by additional function definitions, if possible. For example,\<close>

definition fHO :: "bool list \<Rightarrow> bool list" where \<open>fHO = map (\<lambda>x. x \<and> x)\<close>

text \<open>is not acceptable (i.e. \<open>time_definition fHO\<close> fails), but can be replaced with\<close>

definition double :: "int \<Rightarrow> int" where \<open>double i = 2 * i\<close>
definition fHO' :: "int list \<Rightarrow> int list" where \<open>fHO' xs = map double xs\<close>

time_definition double
time_definition fHO'

text \<open>That is why in the definition of \<open>len2\<close> above we could not just write
\<open>foldl (\<lambda>i x. i+1) 0 xs\<close>.\<close>


section \<open>Predefined Functions\<close>

text\<open>The time framework requires executable functions. However,
many basic types and functions are not defined via \<open>datatype\<close> and \<open>fun\<close>
but in an abstract mathematical fashion and are not executable,
i.e. the time framework does not apply (or gives the `wrong' result).

In order to model actual hardware that executes these predefined functions in constant time,
there is a command for axiomatically declaring that some function takes 0 time.
(This is how we model constant time, to simplify the resulting time expressions.
This does not change the asymptotic running time of user-defined functions using the
predefined functions because 1 is added for every user-defined function call.)
Theory \<^theory>\<open>HOL-Library.Time_Commands\<close> declares a number of predefined functions
as 0-time functions. This includes
\<open>(+)\<close>, \<open>-\<close>, \<open>(*)\<close>, \<open>/\<close>, \<open>div\<close>, \<open>min\<close>, \<open>max\<close>, \<open><\<close>, \<open>\<le>\<close>, \<open>\<not>\<close>, \<open>\<and>\<close>, \<open>\<or>\<close> and \<open>=\<close>
and can be extended with the command \<open>time_fun_0\<close>.
This feature has to be used with care:

\<^item> Many of these functions are polymorphic and reside in type classes.
The constant-time assumption is justified only for those types where the hardware offers
suitable support, e.g. numeric types. The argument size is implicitly bounded, too.

\<^item> The constant-time assumption for \<open>(=)\<close> is justified for recursive data types such as lists and trees
as long as the comparison is of the form \<open>t = c\<close> where \<open>c\<close> is a constant term, for example \<open>xs = []\<close>.

Users of the time framework need to ensure that 0-time functions are used only within these bounds.\<close>


section \<open>Locales\<close>

text \<open>If we want to apply the time framework to a function \<open>g\<close> defined within a locale,
we need to add additional locale parameters \<open>T_f :: \<tau> \<Rightarrow> nat\<close> for every locale
parameter \<open>f :: \<tau> \<Rightarrow> \<tau>'\<close> used in the definition of \<open>g\<close>.

In the following example we do not only parameterize the locale with \<open>T_f\<close>
but also assume a property of \<open>T_f\<close>. As a result we can prove a property of \<open>T_g\<close>
inside the locale:\<close>

lemma T_map_sum: "T_map T_f xs = sum_list (map T_f xs) + length xs + 1"
by(induction xs) (auto)

locale LT =
fixes f :: "'a \<Rightarrow> 'a"
and T_f :: "'a \<Rightarrow> nat"
assumes T_f: "T_f x \<le> 1"
begin

definition g where "g xs = map f xs"

time_definition g

lemma sum_list_map_T_f_ub: "sum_list (map T_f xs) \<le> length xs"
proof(induction xs)
  case (Cons a xs) thus ?case using T_f[of a] by auto
qed simp

lemma T_g_ub: "T_g xs \<le> 2 * length xs + 1"
unfolding T_g.simps T_map_sum using sum_list_map_T_f_ub[of xs]
by linarith

end

text \<open>Of course now you need to prove \<open>T_f x \<le> 1\<close> for every interpretation of the locale.
A more flexible approach is not to constrain \<open>T_f\<close> inside the locale. It may then be difficult
to derive a generic time bound for \<open>T_g\<close> inside the locale (in the above example it would not be
difficult). If that is the case, one may also derive a bound for \<open>T_g\<close> conditional
on some specific bound for \<open>T_f\<close>. Or one can derive the bound for \<open>T_g\<close>
after a specific interpretation with a specific \<open>T_f\<close>.
For a larger realistic example of the latter approach see theory
\<open>HOL-Data_Structures.Time_Locale_Example\<close>.\<close>


section \<open>Fine Points\<close>

text \<open>Time functions for mutually recursive functions \<open>f, g, \<dots>\<close>: \<open>time_fun f g \<dots>\<close>.\<close>

text \<open>If you want to generate time functions not from the defining equations of a function
but from lemmas proved as equations, you can provide those lemmas explicitly. Example:\<close>

fun f0 :: "nat \<Rightarrow> nat" where
"f0 0 = 0" |
"f0 (Suc n) = f0 n"

lemma f0_eq: "f0 n = 0"
by (induction n) auto

time_fun f0 equations f0_eq

text \<open>The \<open>T_\<close> prefix can be changed by modifying the \<open>time_prefix\<close> attribute. Example:\<close>

declare [[time_prefix = "t_"]]

text \<open>The time framework is not verified
(which is why the framework always prints out what it defines).
There is no underlying formal model. This remains future work.\<close>

end