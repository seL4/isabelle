/*  Title:      Pure/ROOT.scala
    Module:     PIDE
    Author:     Makarius

Root of isabelle package.
*/

package object isabelle extends isabelle.Basic_Library
{
  object Distribution     /*filled-in by makedist*/
  {
    val version = "unidentified repository version"
    val is_identified = false
    val is_official = false
  }
}

