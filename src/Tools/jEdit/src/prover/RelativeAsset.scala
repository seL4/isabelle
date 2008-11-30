/*
 * RelativeAsset.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package isabelle.prover

import sidekick.enhanced.SourceAsset
import javax.swing._
import javax.swing.text.Position

class RelativeAsset(base : Command, var rel_start : Int, var rel_end : Int, cons_name : String, desc : String)
      extends SourceAsset {

class MyPos(val o : Int) extends Position {
  override def getOffset = o
}
  {
    setStart(new MyPos(base.start + rel_start))
    setEnd(new MyPos(base.start + rel_end))
    setName(cons_name)
    setShort(cons_name)
    setLong(desc)

  }
	/**
	 * Set the start position
	 */
	override def setStart(start : Position) { rel_start = start.getOffset - base.start }

	/**
	 * Returns the starting position.
	 */
	override def getStart : Position = new MyPos(base.start + rel_start)

	/**
	 * Set the end position
	 */
	override def setEnd(end : Position) { rel_end = end.getOffset - base.start }

	/**
	 * Returns the end position.
	 */
	override def getEnd : Position = new MyPos(base.start + rel_end)

}
