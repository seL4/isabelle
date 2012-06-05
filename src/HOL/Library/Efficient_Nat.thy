(*  Title:      HOL/Library/Efficient_Nat.thy
    Author:     Stefan Berghofer, Florian Haftmann, TU Muenchen
*)

header {* Implementation of natural numbers by target-language integers *}

theory Efficient_Nat
imports Code_Nat Code_Integer Main
begin

text {*
  The efficiency of the generated code for natural numbers can be improved
  drastically by implementing natural numbers by target-language
  integers.  To do this, just include this theory.
*}

subsection {* Target language fundamentals *}

text {*
  For ML, we map @{typ nat} to target language integers, where we
  ensure that values are always non-negative.
*}

code_type nat
  (SML "IntInf.int")
  (OCaml "Big'_int.big'_int")
  (Eval "int")

text {*
  For Haskell and Scala we define our own @{typ nat} type.  The reason
  is that we have to distinguish type class instances for @{typ nat}
  and @{typ int}.
*}

code_include Haskell "Nat"
{*newtype Nat = Nat Integer deriving (Eq, Show, Read);

instance Num Nat where {
  fromInteger k = Nat (if k >= 0 then k else 0);
  Nat n + Nat m = Nat (n + m);
  Nat n - Nat m = fromInteger (n - m);
  Nat n * Nat m = Nat (n * m);
  abs n = n;
  signum _ = 1;
  negate n = error "negate Nat";
};

instance Ord Nat where {
  Nat n <= Nat m = n <= m;
  Nat n < Nat m = n < m;
};

instance Real Nat where {
  toRational (Nat n) = toRational n;
};

instance Enum Nat where {
  toEnum k = fromInteger (toEnum k);
  fromEnum (Nat n) = fromEnum n;
};

instance Integral Nat where {
  toInteger (Nat n) = n;
  divMod n m = quotRem n m;
  quotRem (Nat n) (Nat m)
    | (m == 0) = (0, Nat n)
    | otherwise = (Nat k, Nat l) where (k, l) = quotRem n m;
};
*}

code_reserved Haskell Nat

code_include Scala "Nat"
{*object Nat {

  def apply(numeral: BigInt): Nat = new Nat(numeral max 0)
  def apply(numeral: Int): Nat = Nat(BigInt(numeral))
  def apply(numeral: String): Nat = Nat(BigInt(numeral))

}

class Nat private(private val value: BigInt) {

  override def hashCode(): Int = this.value.hashCode()

  override def equals(that: Any): Boolean = that match {
    case that: Nat => this equals that
    case _ => false
  }

  override def toString(): String = this.value.toString

  def equals(that: Nat): Boolean = this.value == that.value

  def as_BigInt: BigInt = this.value
  def as_Int: Int = if (this.value >= scala.Int.MinValue && this.value <= scala.Int.MaxValue)
      this.value.intValue
    else error("Int value out of range: " + this.value.toString)

  def +(that: Nat): Nat = new Nat(this.value + that.value)
  def -(that: Nat): Nat = Nat(this.value - that.value)
  def *(that: Nat): Nat = new Nat(this.value * that.value)

  def /%(that: Nat): (Nat, Nat) = if (that.value == 0) (new Nat(0), this)
    else {
      val (k, l) = this.value /% that.value
      (new Nat(k), new Nat(l))
    }

  def <=(that: Nat): Boolean = this.value <= that.value

  def <(that: Nat): Boolean = this.value < that.value

}
*}

code_reserved Scala Nat

code_type nat
  (Haskell "Nat.Nat")
  (Scala "Nat")

code_instance nat :: equal
  (Haskell -)

setup {*
  fold (Numeral.add_code @{const_name nat_of_num}
    false Code_Printer.literal_positive_numeral) ["SML", "OCaml", "Haskell", "Scala"]
*}

code_const "0::nat"
  (SML "0")
  (OCaml "Big'_int.zero'_big'_int")
  (Haskell "0")
  (Scala "Nat(0)")


subsection {* Conversions *}

text {*
  Since natural numbers are implemented
  using integers in ML, the coercion function @{term "int"} of type
  @{typ "nat \<Rightarrow> int"} is simply implemented by the identity function.
  For the @{const nat} function for converting an integer to a natural
  number, we give a specific implementation using an ML expression that
  returns its input value, provided that it is non-negative, and otherwise
  returns @{text "0"}.
*}

definition int :: "nat \<Rightarrow> int" where
  [code_abbrev]: "int = of_nat"

code_const int
  (SML "_")
  (OCaml "_")

code_const nat
  (SML "IntInf.max/ (0,/ _)")
  (OCaml "Big'_int.max'_big'_int/ Big'_int.zero'_big'_int")
  (Eval "Integer.max/ 0")

text {* For Haskell and Scala, things are slightly different again. *}

code_const int and nat
  (Haskell "toInteger" and "fromInteger")
  (Scala "!_.as'_BigInt" and "Nat")

text {* Alternativ implementation for @{const of_nat} *}

lemma [code]:
  "of_nat n = (if n = 0 then 0 else
     let
       (q, m) = divmod_nat n 2;
       q' = 2 * of_nat q
     in if m = 0 then q' else q' + 1)"
proof -
  from mod_div_equality have *: "of_nat n = of_nat (n div 2 * 2 + n mod 2)" by simp
  show ?thesis
    apply (simp add: Let_def divmod_nat_div_mod mod_2_not_eq_zero_eq_one_nat
      of_nat_mult
      of_nat_add [symmetric])
    apply (auto simp add: of_nat_mult)
    apply (simp add: * of_nat_mult add_commute mult_commute)
    done
qed

text {* Conversion from and to code numerals *}

code_const Code_Numeral.of_nat
  (SML "IntInf.toInt")
  (OCaml "_")
  (Haskell "!(fromInteger/ ./ toInteger)")
  (Scala "!Natural(_.as'_BigInt)")
  (Eval "_")

code_const Code_Numeral.nat_of
  (SML "IntInf.fromInt")
  (OCaml "_")
  (Haskell "!(fromInteger/ ./ toInteger)")
  (Scala "!Nat(_.as'_BigInt)")
  (Eval "_")


subsection {* Target language arithmetic *}

code_const "plus \<Colon> nat \<Rightarrow> nat \<Rightarrow> nat"
  (SML "IntInf.+/ ((_),/ (_))")
  (OCaml "Big'_int.add'_big'_int")
  (Haskell infixl 6 "+")
  (Scala infixl 7 "+")
  (Eval infixl 8 "+")

code_const "minus \<Colon> nat \<Rightarrow> nat \<Rightarrow> nat"
  (SML "IntInf.max/ (0, IntInf.-/ ((_),/ (_)))")
  (OCaml "Big'_int.max'_big'_int/ Big'_int.zero'_big'_int/ (Big'_int.sub'_big'_int/ _/ _)")
  (Haskell infixl 6 "-")
  (Scala infixl 7 "-")
  (Eval "Integer.max/ 0/ (_ -/ _)")

code_const Code_Nat.dup
  (SML "IntInf.*/ (2,/ (_))")
  (OCaml "Big'_int.mult'_big'_int/ 2")
  (Haskell "!(2 * _)")
  (Scala "!(2 * _)")
  (Eval "!(2 * _)")

code_const Code_Nat.sub
  (SML "!(raise/ Fail/ \"sub\")")
  (OCaml "failwith/ \"sub\"")
  (Haskell "error/ \"sub\"")
  (Scala "!sys.error(\"sub\")")

code_const "times \<Colon> nat \<Rightarrow> nat \<Rightarrow> nat"
  (SML "IntInf.*/ ((_),/ (_))")
  (OCaml "Big'_int.mult'_big'_int")
  (Haskell infixl 7 "*")
  (Scala infixl 8 "*")
  (Eval infixl 9 "*")

code_const divmod_nat
  (SML "IntInf.divMod/ ((_),/ (_))")
  (OCaml "Big'_int.quomod'_big'_int")
  (Haskell "divMod")
  (Scala infixl 8 "/%")
  (Eval "Integer.div'_mod")

code_const "HOL.equal \<Colon> nat \<Rightarrow> nat \<Rightarrow> bool"
  (SML "!((_ : IntInf.int) = _)")
  (OCaml "Big'_int.eq'_big'_int")
  (Haskell infix 4 "==")
  (Scala infixl 5 "==")
  (Eval infixl 6 "=")

code_const "less_eq \<Colon> nat \<Rightarrow> nat \<Rightarrow> bool"
  (SML "IntInf.<=/ ((_),/ (_))")
  (OCaml "Big'_int.le'_big'_int")
  (Haskell infix 4 "<=")
  (Scala infixl 4 "<=")
  (Eval infixl 6 "<=")

code_const "less \<Colon> nat \<Rightarrow> nat \<Rightarrow> bool"
  (SML "IntInf.</ ((_),/ (_))")
  (OCaml "Big'_int.lt'_big'_int")
  (Haskell infix 4 "<")
  (Scala infixl 4 "<")
  (Eval infixl 6 "<")

code_const Num.num_of_nat
  (SML "!(raise/ Fail/ \"num'_of'_nat\")")
  (OCaml "failwith/ \"num'_of'_nat\"")
  (Haskell "error/ \"num'_of'_nat\"")
  (Scala "!sys.error(\"num'_of'_nat\")")


subsection {* Evaluation *}

lemma [code, code del]:
  "(Code_Evaluation.term_of \<Colon> nat \<Rightarrow> term) = Code_Evaluation.term_of" ..

code_const "Code_Evaluation.term_of \<Colon> nat \<Rightarrow> term"
  (SML "HOLogic.mk'_number/ HOLogic.natT")

text {*
  FIXME -- Evaluation with @{text "Quickcheck_Narrowing"} does not work, as
  @{text "code_module"} is very aggressive leading to bad Haskell code.
  Therefore, we simply deactivate the narrowing-based quickcheck from here on.
*}

declare [[quickcheck_narrowing_active = false]] 


code_modulename SML
  Efficient_Nat Arith

code_modulename OCaml
  Efficient_Nat Arith

code_modulename Haskell
  Efficient_Nat Arith

hide_const (open) int

end
