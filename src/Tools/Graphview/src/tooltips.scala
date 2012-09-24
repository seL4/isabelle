/*  Title:      Tools/Graphview/src/graph_components.scala
    Author:     Markus Kaiser, TU Muenchen

Tooltip generation for graph components.
*/

package isabelle.graphview


import isabelle._
import java.awt.FontMetrics


object Tooltips {
  // taken (and modified slightly) from html_panel.scala
  private def make_HTML(term: XML.Body, fm: FontMetrics): String = {
    XML.string_of_body ( term.flatMap(div =>
              Pretty.formatted(List(div), 76, Pretty.font_metric(fm))
                .map( t=>
                  HTML.spans(t, false))
      ).head
    )
  }  
  
  def locale(key: String, model: Model, fm: FontMetrics): String = {
    val locale = model.complete.get_node(key)
    val parsed_name = key.split('.')
    
    if (!locale.isDefined) {
      """|<html>
        |<body style="margin: 3px">
        |%s
        |</body>
        |""".stripMargin.format(parsed_name.reduceLeft("%s<br>%s".format(_,_)))      
    } else {
      val Some(Locale(axioms, parameters)) = locale

      val parms = {
        if (parameters.size > 0) {
          """|
            |<p>Parameters:</p>
            |<ul>
            |%s
            |</ul>
            |""".stripMargin.format(parameters.map(
                                        y => "<li>%s :: %s</li>".format(
                                                y._1,
                                                make_HTML(y._2, fm))
                                    ).reduceLeft(_+_))
        } else ""
      }
      val axms = {
        if (axioms.size > 0) {
          """|
            |<p>Axioms:</p>
            |<ul>
            |%s
            |</ul>
            |""".stripMargin.format(axioms.map(
                                      y => "<li>%s</li>".format(
                                                make_HTML(y, fm))
                                    ).reduceLeft(_+_))
        } else ""
      }

      """|<html>
        |<style type="text/css">
        |/* isabelle style */
        |%s
        |
        |/* tooltip specific style */
        |
        |body  { margin: 10px; font-size: 12px; }
        |hr    { margin: 12px 0 0 0; height: 2px; }
        |p     { margin: 6px 0 2px 0; }
        |ul    { margin: 0 0 0 4px; list-style-type: none; }
        |li    { margin: 0 0 4px; }
        |
        |</style>
        |<body>
        |<center>%s</center>
        |<hr>
        |%s
        |%s
        |</body>
        |</html>
        |""".stripMargin.format(Parameters.tooltip_css,
                                parsed_name.reduceLeft("%s<br>%s".format(_,_)),
                                axms,
                                parms).replace("&apos;", "'")
    }  
  }
}