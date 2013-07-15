/*  Title:      Pure/System/cygwin_init.scala
    Author:     Makarius

Initialize Isabelle distribution after download.
*/

package isabelle


import java.lang.System
import java.io.{File => JFile, BufferedReader, InputStreamReader}
import java.nio.file.{Paths, Files}
import java.awt.{GraphicsEnvironment, Point, Font}
import javax.swing.ImageIcon

import scala.swing.{ScrollPane, Button, FlowPanel,
  BorderPanel, MainFrame, TextArea, SwingApplication}
import scala.swing.event.ButtonClicked


object Cygwin_Init
{
  /* symlinks */

  def write_symlink(file: JFile, content: String)
  {
    require(Platform.is_windows)

    val path = file.toPath

    val writer = Files.newBufferedWriter(path, UTF8.charset)
    try { writer.write("!<symlink>" + content + "\0") }
    finally { writer.close }

    Files.setAttribute(path, "dos:system", true)
  }


  /* command-line entry point */

  def main(args: Array[String]) =
  {
    GUI.init_laf()
    try {
      require(Platform.is_windows)

      val isabelle_home = System.getProperty("isabelle.home")
      if (isabelle_home == null || isabelle_home == "")
        error("Unknown Isabelle home directory")
      if (!(new JFile(isabelle_home)).isDirectory)
        error("Bad Isabelle home directory: " + quote(isabelle_home))

      Swing_Thread.later { main_frame(isabelle_home) }
    }
    catch {
      case exn: Throwable =>
        GUI.error_dialog(null, "Isabelle init failure", GUI.scrollable_text(Exn.message(exn)))
        sys.exit(2)
    }
  }


  /* main window */

  private def main_frame(isabelle_home: String) = new MainFrame
  {
    title = "Isabelle system initialization"
    iconImage = new ImageIcon(isabelle_home + "\\lib\\logo\\isabelle.gif").getImage

    val layout_panel = new BorderPanel
    contents = layout_panel


    /* text area */

    def echo(msg: String) { text_area.append(msg + "\n") }

    val text_area = new TextArea {
      font = new Font("SansSerif", Font.PLAIN, GUI.resolution_scale(10) max 14)
      editable = false
      columns = 80
      rows = 24
    }

    layout_panel.layout(new ScrollPane(text_area)) = BorderPanel.Position.Center


    /* exit button */

    var _return_code: Option[Int] = None
    def maybe_exit(): Unit = _return_code.foreach(sys.exit(_))

    def return_code(rc: Int): Unit =
      Swing_Thread.later {
        _return_code = Some(rc)
        button.peer.getRootPane.setDefaultButton(button.peer)
        layout_panel.repaint
      }

    override def closeOperation { maybe_exit() }

    val button = new Button {
      text = "Done"
      reactions += { case ButtonClicked(_) => maybe_exit() }
    }
    val button_panel = new FlowPanel(FlowPanel.Alignment.Center)(button)

    layout_panel.layout(button_panel) = BorderPanel.Position.South


    /* show window */

    pack()
    val point = GraphicsEnvironment.getLocalGraphicsEnvironment().getCenterPoint()
    location = new Point(point.x - size.width / 2, point.y - size.height / 2)
    visible = true

    default_thread_pool.submit(() =>
      try {
        init(isabelle_home, echo)
        return_code(0)
      }
      catch {
        case exn: Throwable =>
          text_area.append("Error:\n" + Exn.message(exn) + "\n")
          return_code(2)
      }
    )
  }


  /* init Cygwin file-system */

  private def init(isabelle_home: String, echo: String => Unit)
  {
    val cygwin_root = isabelle_home + "\\contrib\\cygwin"

    if (!(new JFile(cygwin_root)).isDirectory)
      error("Bad Isabelle Cygwin directory: " + quote(cygwin_root))


    val execute_cwd = new JFile(isabelle_home)
    val execute_env = Map("CYGWIN" -> "nodosfilewarning")

    def execute(args: String*): Int =
    {
      val proc = Isabelle_System.raw_execute(execute_cwd, execute_env, true, args: _*)
      proc.getOutputStream.close

      val stdout = new BufferedReader(new InputStreamReader(proc.getInputStream, UTF8.charset))
      try {
        var line = stdout.readLine
        while (line != null) {
          echo(line)
          line = stdout.readLine
        }
      }
      finally { stdout.close }

      proc.waitFor
    }

    echo("Initializing Cygwin ...")
    execute("contrib\\cygwin\\bin\\dash", "/isabelle/rebaseall")
    execute("contrib\\cygwin\\bin\\bash", "/isabelle/postinstall")
  }
}

