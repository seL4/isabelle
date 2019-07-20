/*  Title:      Pure/pure_thy.scala
    Author:     Makarius

Pure theory content.
*/

package isabelle


object Pure_Thy
{
  /* Pure logic */

  val DUMMY: String = "dummy"
  val FUN: String = "fun"
  val PROP: String = "prop"
  val ITSELF: String = "itself"

  val ALL: String = "Pure.all"
  val IMP: String = "Pure.imp"
  val EQ: String = "Pure.eq"
  val TYPE: String = "Pure.type"


  /* proof terms (abstract syntax) */

  val PROOF: String = "proof"

  val APPT: String = "Appt"
  val APPP: String = "AppP"
  val ABST: String = "Abst"
  val ABSP: String = "AbsP"
  val HYP: String = "Hyp"
  val ORACLE: String = "Oracle"
  val OFCLASS: String = "OfClass"
  val MINPROOF: String = "MinProof"
}
