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


  /* abstract syntax for proof terms */

  val PROOF: String = "Pure.proof"

  val APPT: String = "Pure.Appt"
  val APPP: String = "Pure.AppP"
  val ABST: String = "Pure.Abst"
  val ABSP: String = "Pure.AbsP"
  val HYP: String = "Pure.Hyp"
  val ORACLE: String = "Pure.Oracle"
  val OFCLASS: String = "Pure.OfClass"
  val MINPROOF: String = "Pure.MinProof"
}
