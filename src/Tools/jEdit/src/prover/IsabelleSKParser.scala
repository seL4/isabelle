/*
 * Sidekick parser for proof document
 *
 * @author Fabian Immler, TU Munich
 */

package isabelle.prover

import isabelle.jedit.{Plugin}
import sidekick.{SideKickParser, SideKickParsedData, IAsset}
import org.gjt.sp.jedit.{Buffer, ServiceManager}
import javax.swing.tree.DefaultMutableTreeNode
import errorlist.DefaultErrorSource;

class IsabelleSKParser extends SideKickParser("isabelle") {
  
  override def parse(b : Buffer,
                     errorSource : DefaultErrorSource)
    : SideKickParsedData = {
      Plugin.plugin.prover_setup(b) match {
        case None =>
          val data = new SideKickParsedData("WARNING:")
          data.root.add(new DefaultMutableTreeNode("can only parse buffer which is activated via IsabellePlugin -> activate"))
          data
        case Some(prover_setup) =>
          val prover = prover_setup.prover
          val document = prover.document
          val data = new SideKickParsedData(b.getPath)

          for(command <- document.commands){
            data.root.add(command.root_node.swing_node)
          }
          data
      }
    }

}
