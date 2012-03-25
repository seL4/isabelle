(*  Title:      HOL/Library/Code_Natural.thy
    Author:     Florian Haftmann, TU Muenchen
*)

theory Code_Natural
imports "../Main"
begin

section {* Alternative representation of @{typ code_numeral} for @{text Haskell} and @{text Scala} *}

code_include Haskell "Natural"
{*import Data.Array.ST;

newtype Natural = Natural Integer deriving (Eq, Show, Read);

instance Num Natural where {
  fromInteger k = Natural (if k >= 0 then k else 0);
  Natural n + Natural m = Natural (n + m);
  Natural n - Natural m = fromInteger (n - m);
  Natural n * Natural m = Natural (n * m);
  abs n = n;
  signum _ = 1;
  negate n = error "negate Natural";
};

instance Ord Natural where {
  Natural n <= Natural m = n <= m;
  Natural n < Natural m = n < m;
};

instance Ix Natural where {
  range (Natural n, Natural m) = map Natural (range (n, m));
  index (Natural n, Natural m) (Natural q) = index (n, m) q;
  inRange (Natural n, Natural m) (Natural q) = inRange (n, m) q;
  rangeSize (Natural n, Natural m) = rangeSize (n, m);
};

instance Real Natural where {
  toRational (Natural n) = toRational n;
};

instance Enum Natural where {
  toEnum k = fromInteger (toEnum k);
  fromEnum (Natural n) = fromEnum n;
};

instance Integral Natural where {
  toInteger (Natural n) = n;
  divMod n m = quotRem n m;
  quotRem (Natural n) (Natural m)
    | (m == 0) = (0, Natural n)
    | otherwise = (Natural k, Natural l) where (k, l) = quotRem n m;
};*}


code_reserved Haskell Natural

code_include Scala "Natural"
{*object Natural {

  def apply(numeral: BigInt): Natural = new Natural(numeral max 0)
  def apply(numeral: Int): Natural = Natural(BigInt(numeral))
  def apply(numeral: String): Natural = Natural(BigInt(numeral))

}

class Natural private(private val value: BigInt) {

  override def hashCode(): Int = this.value.hashCode()

  override def equals(that: Any): Boolean = that match {
    case that: Natural => this equals that
    case _ => false
  }

  override def toString(): String = this.value.toString

  def equals(that: Natural): Boolean = this.value == that.value

  def as_BigInt: BigInt = this.value
  def as_Int: Int = if (this.value >= scala.Int.MinValue && this.value <= scala.Int.MaxValue)
      this.value.intValue
    else error("Int value out of range: " + this.value.toString)

  def +(that: Natural): Natural = new Natural(this.value + that.value)
  def -(that: Natural): Natural = Natural(this.value - that.value)
  def *(that: Natural): Natural = new Natural(this.value * that.value)

  def /%(that: Natural): (Natural, Natural) = if (that.value == 0) (new Natural(0), this)
    else {
      val (k, l) = this.value /% that.value
      (new Natural(k), new Natural(l))
    }

  def <=(that: Natural): Boolean = this.value <= that.value

  def <(that: Natural): Boolean = this.value < that.value

}
*}

code_reserved Scala Natural

code_type code_numeral
  (Haskell "Natural.Natural")
  (Scala "Natural")

setup {*
  fold (Numeral.add_code @{const_name Code_Numeral.Num}
    false Code_Printer.literal_alternative_numeral) ["Haskell", "Scala"]
*}

code_instance code_numeral :: equal
  (Haskell -)

code_const "0::code_numeral"
  (Haskell "0")
  (Scala "Natural(0)")

code_const "plus \<Colon> code_numeral \<Rightarrow> code_numeral \<Rightarrow> code_numeral"
  (Haskell infixl 6 "+")
  (Scala infixl 7 "+")

code_const "minus \<Colon> code_numeral \<Rightarrow> code_numeral \<Rightarrow> code_numeral"
  (Haskell infixl 6 "-")
  (Scala infixl 7 "-")

code_const "times \<Colon> code_numeral \<Rightarrow> code_numeral \<Rightarrow> code_numeral"
  (Haskell infixl 7 "*")
  (Scala infixl 8 "*")

code_const Code_Numeral.div_mod
  (Haskell "divMod")
  (Scala infixl 8 "/%")

code_const "HOL.equal \<Colon> code_numeral \<Rightarrow> code_numeral \<Rightarrow> bool"
  (Haskell infix 4 "==")
  (Scala infixl 5 "==")

code_const "less_eq \<Colon> code_numeral \<Rightarrow> code_numeral \<Rightarrow> bool"
  (Haskell infix 4 "<=")
  (Scala infixl 4 "<=")

code_const "less \<Colon> code_numeral \<Rightarrow> code_numeral \<Rightarrow> bool"
  (Haskell infix 4 "<")
  (Scala infixl 4 "<")

end
