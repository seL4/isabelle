/*  Title:      Pure/Tools/isabelle_system.scala
    ID:         $Id$
    Author:     Makarius

Isabelle system support.
*/

package isabelle


object IsabelleSystem {

  /* Isabelle settings */

  class BadSetting(val name: String) extends Exception

  private def strict_getenv(name: String) = {
    val value = System.getenv(name)
    if (value == null || value == "") throw new BadSetting(name)
    else value
  }

  def ISABELLE_HOME() = strict_getenv("ISABELLE_HOME_JVM")
  def ISABELLE_HOME_USER() = strict_getenv("ISABELLE_HOME_USER_JVM")

}
