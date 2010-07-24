(*  Title:      HOL/Library/Code_Integer.thy
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Pretty integer literals for code generation *}

theory Code_Integer
imports Main
begin

text {*
  HOL numeral expressions are mapped to integer literals
  in target languages, using predefined target language
  operations for abstract integer operations.
*}

text {*
  Preliminary: alternative representation of @{typ code_numeral}
  for @{text Haskell} and @{text Scala}.
*}

code_include Haskell "Natural" {*
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
};
*}

code_reserved Haskell Natural

code_include Scala "Natural" {*
import scala.Math

object Natural {

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
  def as_Int: Int = if (this.value >= Int.MinValue && this.value <= Int.MaxValue)
      this.value.intValue
    else this.value.intValue

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
  fold (Numeral.add_code @{const_name number_code_numeral_inst.number_of_code_numeral}
    false Code_Printer.literal_alternative_numeral) ["Haskell", "Scala"]
*}

code_instance code_numeral :: eq
  (Haskell -)

code_const "op + \<Colon> code_numeral \<Rightarrow> code_numeral \<Rightarrow> code_numeral"
  (Haskell infixl 6 "+")
  (Scala infixl 7 "+")

code_const "op - \<Colon> code_numeral \<Rightarrow> code_numeral \<Rightarrow> code_numeral"
  (Haskell infixl 6 "-")
  (Scala infixl 7 "-")

code_const "op * \<Colon> code_numeral \<Rightarrow> code_numeral \<Rightarrow> code_numeral"
  (Haskell infixl 7 "*")
  (Scala infixl 8 "*")

code_const div_mod_code_numeral
  (Haskell "divMod")
  (Scala infixl 8 "/%")

code_const "eq_class.eq \<Colon> code_numeral \<Rightarrow> code_numeral \<Rightarrow> bool"
  (Haskell infixl 4 "==")
  (Scala infixl 5 "==")

code_const "op \<le> \<Colon> code_numeral \<Rightarrow> code_numeral \<Rightarrow> bool"
  (Haskell infix 4 "<=")
  (Scala infixl 4 "<=")

code_const "op < \<Colon> code_numeral \<Rightarrow> code_numeral \<Rightarrow> bool"
  (Haskell infix 4 "<")
  (Scala infixl 4 "<")

text {*
  Setup for @{typ int} proper.
*}


code_type int
  (SML "IntInf.int")
  (OCaml "Big'_int.big'_int")
  (Haskell "Integer")
  (Scala "BigInt")

code_instance int :: eq
  (Haskell -)

setup {*
  fold (Numeral.add_code @{const_name number_int_inst.number_of_int}
    true Code_Printer.literal_numeral) ["SML", "OCaml", "Haskell", "Scala"]
*}

code_const "Int.Pls" and "Int.Min" and "Int.Bit0" and "Int.Bit1"
  (SML "raise/ Fail/ \"Pls\""
     and "raise/ Fail/ \"Min\""
     and "!((_);/ raise/ Fail/ \"Bit0\")"
     and "!((_);/ raise/ Fail/ \"Bit1\")")
  (OCaml "failwith/ \"Pls\""
     and "failwith/ \"Min\""
     and "!((_);/ failwith/ \"Bit0\")"
     and "!((_);/ failwith/ \"Bit1\")")
  (Haskell "error/ \"Pls\""
     and "error/ \"Min\""
     and "error/ \"Bit0\""
     and "error/ \"Bit1\"")
  (Scala "!error(\"Pls\")"
     and "!error(\"Min\")"
     and "!error(\"Bit0\")"
     and "!error(\"Bit1\")")

code_const Int.pred
  (SML "IntInf.- ((_), 1)")
  (OCaml "Big'_int.pred'_big'_int")
  (Haskell "!(_/ -/ 1)")
  (Scala "!(_/ -/ 1)")
  (Eval "!(_/ -/ 1)")

code_const Int.succ
  (SML "IntInf.+ ((_), 1)")
  (OCaml "Big'_int.succ'_big'_int")
  (Haskell "!(_/ +/ 1)")
  (Scala "!(_/ +/ 1)")
  (Eval "!(_/ +/ 1)")

code_const "op + \<Colon> int \<Rightarrow> int \<Rightarrow> int"
  (SML "IntInf.+ ((_), (_))")
  (OCaml "Big'_int.add'_big'_int")
  (Haskell infixl 6 "+")
  (Scala infixl 7 "+")
  (Eval infixl 8 "+")

code_const "uminus \<Colon> int \<Rightarrow> int"
  (SML "IntInf.~")
  (OCaml "Big'_int.minus'_big'_int")
  (Haskell "negate")
  (Scala "!(- _)")
  (Eval "~/ _")

code_const "op - \<Colon> int \<Rightarrow> int \<Rightarrow> int"
  (SML "IntInf.- ((_), (_))")
  (OCaml "Big'_int.sub'_big'_int")
  (Haskell infixl 6 "-")
  (Scala infixl 7 "-")
  (Eval infixl 8 "-")

code_const "op * \<Colon> int \<Rightarrow> int \<Rightarrow> int"
  (SML "IntInf.* ((_), (_))")
  (OCaml "Big'_int.mult'_big'_int")
  (Haskell infixl 7 "*")
  (Scala infixl 8 "*")
  (Eval infixl 9 "*")

code_const pdivmod
  (SML "IntInf.divMod/ (IntInf.abs _,/ IntInf.abs _)")
  (OCaml "Big'_int.quomod'_big'_int/ (Big'_int.abs'_big'_int _)/ (Big'_int.abs'_big'_int _)")
  (Haskell "divMod/ (abs _)/ (abs _)")
  (Scala "!((k: BigInt) => (l: BigInt) =>/ if (l == 0)/ (BigInt(0), k) else/ (k.abs '/% l.abs))")
  (Eval "Integer.div'_mod/ (abs _)/ (abs _)")

code_const "eq_class.eq \<Colon> int \<Rightarrow> int \<Rightarrow> bool"
  (SML "!((_ : IntInf.int) = _)")
  (OCaml "Big'_int.eq'_big'_int")
  (Haskell infixl 4 "==")
  (Scala infixl 5 "==")
  (Eval infixl 6 "=")

code_const "op \<le> \<Colon> int \<Rightarrow> int \<Rightarrow> bool"
  (SML "IntInf.<= ((_), (_))")
  (OCaml "Big'_int.le'_big'_int")
  (Haskell infix 4 "<=")
  (Scala infixl 4 "<=")
  (Eval infixl 6 "<=")

code_const "op < \<Colon> int \<Rightarrow> int \<Rightarrow> bool"
  (SML "IntInf.< ((_), (_))")
  (OCaml "Big'_int.lt'_big'_int")
  (Haskell infix 4 "<")
  (Scala infixl 4 "<")
  (Eval infixl 6 "<")

code_const Code_Numeral.int_of
  (SML "IntInf.fromInt")
  (OCaml "_")
  (Haskell "toInteger")
  (Scala "!_.as'_BigInt")
  (Eval "_")

text {* Evaluation *}

code_const "Code_Evaluation.term_of \<Colon> int \<Rightarrow> term"
  (Eval "HOLogic.mk'_number/ HOLogic.intT")

end