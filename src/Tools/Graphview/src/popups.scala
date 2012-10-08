/*  Title:      Tools/Graphview/src/popups.scala
    Author:     Markus Kaiser, TU Muenchen

PopupMenu generation for graph components.
*/

package isabelle.graphview


import isabelle._
import isabelle.graphview.Mutators._
import javax.swing.JPopupMenu
import scala.swing.{Action, Menu, MenuItem, Separator}


object Popups {
  def apply(panel: Graph_Panel, under_mouse: Option[String],
            selected: List[String]): JPopupMenu =
  {
    val add_mutator = panel.visualizer.model.Mutators.add _
    val curr = panel.visualizer.model.current
    
    def filter_context(ls: List[String], reverse: Boolean,
                       caption: String, edges: Boolean) =
      new Menu(caption) {
        contents += new MenuItem(new Action("This") {
            def apply =
              add_mutator(
                Mutators.create(
                  Node_List(ls, reverse, false, false)
                )
              )
          })

        contents += new MenuItem(new Action("Family") {
            def apply =
              add_mutator(
                Mutators.create(
                  Node_List(ls, reverse, true, true)
                )
              )
          })

        contents += new MenuItem(new Action("Parents") {
            def apply =
              add_mutator(
                Mutators.create(
                  Node_List(ls, reverse, false, true)
                )
              )
          })

        contents += new MenuItem(new Action("Children") {
            def apply =
              add_mutator(
                Mutators.create(
                  Node_List(ls, reverse, true, false)
                )
              )
          })


        if (edges) {
          val outs = ls.map(l => (l, curr.imm_succs(l)))  // FIXME iterator
                      .filter(_._2.size > 0).sortBy(_._1)
          val ins = ls.map(l => (l, curr.imm_preds(l)))  // FIXME iterator
                      .filter(_._2.size > 0).sortBy(_._1)

          if (outs.nonEmpty || ins.nonEmpty) {
            contents += new Separator()

            contents += new Menu("Edge") {
              if (outs.nonEmpty) {
                contents += new MenuItem("From...") {
                  enabled = false
                }

                outs.map( e => {
                  val (from, tos) = e
                  contents += new Menu(from) {
                    contents += new MenuItem("To..."){
                      enabled = false
                    }

                    tos.toList.sorted.distinct.map( to => {
                      contents += new MenuItem(new Action(to) {
                        def apply =
                          add_mutator(
                            Mutators.create(Edge_Endpoints(from, to))
                          )
                      })
                    })
                  }
                })
              }
              if (outs.nonEmpty && ins.nonEmpty) {
                contents += new Separator()       
              }
              if (ins.nonEmpty) {
                contents += new MenuItem("To...") {
                  enabled = false
                }

                ins.map( e => {
                  val (to, froms) = e
                  contents += new Menu(to) {
                    contents += new MenuItem("From..."){
                      enabled = false
                    }

                    froms.toList.sorted.distinct.map( from => {
                      contents += new MenuItem(new Action(from) {
                        def apply =
                          add_mutator(
                            Mutators.create(Edge_Endpoints(from, to))
                          )
                      })
                    })
                  }
                })
              }              
            }
          }
        }
    }

    val popup = new JPopupMenu()

    popup.add(new MenuItem(new Action("Remove all filters") {
          def apply = panel.visualizer.model.Mutators(Nil)
        }).peer
    )
    popup.add(new MenuItem(new Action("Remove transitive edges") {
          def apply = add_mutator(Mutators.create(Edge_Transitive()))
        }).peer
    )
    popup.add(new JPopupMenu.Separator)

    if (under_mouse.isDefined) {
      val v = under_mouse.get
      popup.add(new MenuItem("Mouseover: %s".format(panel.visualizer.Caption(v))) {
        enabled = false
      }.peer)

      popup.add(filter_context(List(v), true, "Hide", true).peer)
      popup.add(filter_context(List(v), false, "Show only", false).peer)
      
      popup.add(new JPopupMenu.Separator)      
    }
    if (!selected.isEmpty) {
      val text = {
        if (selected.length > 1) {
          "Multiple"
        } else {
          panel.visualizer.Caption(selected.head)
        }
      }

      popup.add(new MenuItem("Selected: %s".format(text)) {
        enabled = false
      }.peer)

      popup.add(filter_context(selected, true, "Hide", true).peer)
      popup.add(filter_context(selected, false, "Show only", false).peer)
      popup.add(new JPopupMenu.Separator)
    }


    popup.add(new MenuItem(new Action("Fit to Window") {
        def apply = panel.fit_to_window()
      }).peer
    )
    
    popup
  }
}
