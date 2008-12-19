/*
 * Text as event source
 *
 * @author Johannes Hölzl, TU Munich
 */

package isabelle.proofdocument

import isabelle.utils.EventSource

object Text {
  class Changed(val start : Int, val added : Int, val removed : Int) { }
}

trait Text {
  def content(start : Int, stop : Int) : String
  def length : Int
  
  def changes : EventSource[Text.Changed]
}
