/*  Title:      jedit/plugin/IsabelleParser.scala
    ID:         $Id$
    Author:     Makarius

Isabelle parser setup for Sidekick plugin.
*/

package isabelle

import org.gjt.sp.jedit.Buffer
import org.gjt.sp.util.Log

import sidekick.SideKickParsedData
import sidekick.SideKickParser
import errorlist.DefaultErrorSource


class IsabelleParser extends SideKickParser("isabelle") {
  private var text: String = null
  private var data: SideKickParsedData = null
  private var buffer: Buffer = null

  // FIXME dummy -- no functionality yet
  def parse(buf: Buffer, e: DefaultErrorSource): SideKickParsedData = {
    buffer = buf
    buffer.readLock()
    text = buffer.getText(0, buffer.getLength())
    data = new SideKickParsedData(buffer.getName())
    buffer.readUnlock()
    data
  }
}

