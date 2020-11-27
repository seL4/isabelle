/*  Title:      HOL/SPARK/Tools/spark.scala
    Author:     Makarius

Scala support for HOL-SPARK.
*/

package isabelle.spark

import isabelle._


object SPARK
{
  class Load_Command1 extends Command_Span.Load_Command("spark_vcg")
  {
    override val extensions: List[String] = List("vcg", "fdl", "rls")
  }

  class Load_Command2 extends Command_Span.Load_Command("spark_siv")
  {
    override val extensions: List[String] = List("siv", "fdl", "rls")
  }
}
