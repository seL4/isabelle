/*
 * IsabelleSKParser.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package isabelle.prover

import isabelle.jedit.Plugin
import sidekick.{SideKickParser, SideKickParsedData, IAsset}
import org.gjt.sp.jedit.Buffer
import javax.swing.tree.DefaultMutableTreeNode
import errorlist.DefaultErrorSource;

class IsabelleSKParser() extends SideKickParser("isabelle") {
  
  override def parse(b : Buffer,
                     errorSource : DefaultErrorSource)
    : SideKickParsedData = {
      if(Plugin.plugin == null || Plugin.plugin.theoryView == null
         || Plugin.plugin.theoryView.buffer == null
         || !Plugin.plugin.theoryView.buffer.equals(b))
      {
        val data = new SideKickParsedData("WARNING:")
        data.root.add(new DefaultMutableTreeNode("can only parse buffer which is activated via IsabellePlugin -> activate"))
        data
      } else{
        val plugin = Plugin.plugin
        val prover = plugin.prover
        val buffer = Plugin.plugin.theoryView.buffer.asInstanceOf[Buffer]
        val document = prover.document
        val data = new SideKickParsedData(buffer.getPath)
        //TODO: catch npe s
        for(command <- document.commands){
          data.root.add(command.root_node)
        }
        data
      }
    }

}
