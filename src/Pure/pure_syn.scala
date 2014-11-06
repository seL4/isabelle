/*  Title:      Pure/pure_syn.scala
    Author:     Makarius

Minimal outer syntax for bootstrapping Isabelle/Pure.
*/

package isabelle


object Pure_Syn
{
  private val keywords: Thy_Header.Keywords =
    List(
      ("theory", Some((("thy_begin", Nil), List("theory"))), None),
      ("ML_file", Some((("thy_load", Nil), List("ML"))), None))

  def init(): Outer_Syntax = Outer_Syntax.init().add_keywords(keywords)
}

