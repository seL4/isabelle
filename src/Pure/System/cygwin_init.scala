/*  Title:      Pure/System/cygwin_init.scala
    Author:     Makarius

Initialize Isabelle distribution after extracting via 7zip.
*/

package isabelle


import java.io.{File => JFile, BufferedReader, InputStreamReader}
import java.nio.file.{Paths, Files}
import java.awt.{GraphicsEnvironment, Point, Font}
import javax.swing.ImageIcon

import scala.annotation.tailrec
import scala.swing.{ScrollPane, Button, FlowPanel,
  BorderPanel, MainFrame, TextArea, SwingApplication}
import scala.swing.event.ButtonClicked


object Cygwin_Init
{
  /* main GUI entry point */

  def main_frame(isabelle_home: String, continue: Int => Unit) = new MainFrame
  {
    title = "Isabelle system initialization"
    iconImage = GUI.isabelle_image()

    val layout_panel = new BorderPanel
    contents = layout_panel


    /* text area */

    def echo(msg: String) { text_area.append(msg + "\n") }

    val text_area = new TextArea {
      font = new Font("SansSerif", Font.PLAIN, GUI.resolution_scale(10) max 14)
      editable = false
      columns = 50
      rows = 15
    }

    layout_panel.layout(new ScrollPane(text_area)) = BorderPanel.Position.Center


    /* exit button */

    var _return_code: Option[Int] = None
    def maybe_exit()
    {
      _return_code match {
        case None =>
        case Some(rc) =>
          visible = false
          continue(rc)
      }
    }

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
        init_filesystem(isabelle_home, echo)
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

  private def init_filesystem(isabelle_home: String, echo: String => Unit)
  {
    val cygwin_root = isabelle_home + "\\contrib\\cygwin"

    def execute(args: String*): Int =
    {
      val cwd = new JFile(isabelle_home)
      val env = Map("CYGWIN" -> "nodosfilewarning")
      val proc = Isabelle_System.raw_execute(cwd, env, true, args: _*)
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

    echo("Initializing Cygwin:")

    echo("symlinks ...")
    val symlinks =
    {
      val path = (new JFile(cygwin_root + "\\isabelle\\symlinks")).toPath
      Files.readAllLines(path, UTF8.charset).toArray.toList.asInstanceOf[List[String]]
    }
    @tailrec def recover_symlinks(list: List[String]): Unit =
    {
      list match {
        case Nil | List("") =>
        case link :: content :: rest =>
          val path = (new JFile(isabelle_home, link)).toPath

          val writer = Files.newBufferedWriter(path, UTF8.charset)
          try { writer.write("!<symlink>" + content + "\0") }
          finally { writer.close }

          Files.setAttribute(path, "dos:system", true)

          recover_symlinks(rest)
        case _ => error("Unbalanced symlinks list")
      }
    }
    recover_symlinks(symlinks)

    echo("rebaseall ...")
    execute(cygwin_root + "\\bin\\dash.exe", "/isabelle/rebaseall")

    echo("postinstall ...")
    execute(cygwin_root + "\\bin\\bash.exe", "/isabelle/postinstall")

    echo("init ...")
    Isabelle_System.init()
    echo("OK")
  }
}

