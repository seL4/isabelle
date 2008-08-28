/*  Title:      lib/jedit/plugin/isabelle_parser.scala
    ID:         $Id$
    Author:     Makarius

Isabelle parser setup for Sidekick plugin.
*/

package isabelle.jedit

import javax.swing.text.Position
import javax.swing.tree.DefaultMutableTreeNode
import javax.swing.tree.DefaultTreeModel

import org.gjt.sp.jedit.{Buffer, EditPane}
import org.gjt.sp.util.Log

import errorlist.DefaultErrorSource
import sidekick.{Asset, SideKickParser, SideKickParsedData, SideKickCompletion}


private class IsabelleAsset(name: String, content: String) extends Asset(name)
{
  override def getShortString() = { name }
  override def getLongString() = { content }
  override def getIcon() = { null }
}


class IsabelleParser extends SideKickParser("isabelle") {

  /* parsing */

  private var stopped = false

  override def stop () { stopped = true }

  def parse(buffer: Buffer, e: DefaultErrorSource): SideKickParsedData = {
    stopped = false

    var text: String = null
    var data: SideKickParsedData = null

    try {
      buffer.readLock()
      text = buffer.getText(0, buffer.getLength)
      data = new SideKickParsedData(buffer.getName)

      val asset = new IsabelleAsset("theory", null)
      asset.setStart(buffer.createPosition(0))
      asset.setEnd(buffer.createPosition(buffer.getLength))

      val node = new DefaultMutableTreeNode(asset)
      data.root.insert(node, node.getChildCount)

    }
    finally {
      buffer.readUnlock()
    }

    data
  }


  /* completion */

  override def supportsCompletion = true
  override def canCompleteAnywhere = true

  override def complete(pane: EditPane, caret: Int): SideKickCompletion = null

}

