/*  Title:      Pure/Tools/java_monitor.scala
    Author:     Makarius

Wrapper for the OpenJDK "jconsole" tool, with various adjustments.
*/

package isabelle


import java.awt.Component
import javax.swing.UIManager
import sun.tools.jconsole.{JConsole, LocalVirtualMachine, VMPanel, ProxyClient,
  Messages, Resources => JConsoleResources}


object Java_Monitor
{
  /* default arguments */

  def default_pid: Long = ProcessHandle.current().pid
  val default_update_interval = Time.seconds(3)


  /* java monitor on this JVM: asynchronous GUI application with with system exit */

  def java_monitor_internal(
    pid: Long = default_pid,
    look_and_feel: String = "",
    update_interval: Time = default_update_interval)
  {
    val vm =
      if (pid.toInt.toLong == pid) LocalVirtualMachine.getLocalVirtualMachine(pid.toInt)
      else null
    if (vm == null) error("Bad JVM process " + pid)

    GUI_Thread.later {
      proper_string(look_and_feel) match {
        case None =>
        case Some(laf) =>
          UIManager.setLookAndFeel(laf)
          System.setProperty("swing.defaultlaf", laf)
      }

      Desktop_App.about_handler {
        GUI.dialog(null, "Java Monitor",
          JConsoleResources.format(
            Messages.JCONSOLE_VERSION, System.getProperty("java.runtime.version"))
        )
      }

      val jconsole = new JConsole(false)

      val screen = GUI.mouse_location()
      val width = (1200 max (screen.bounds.width / 2)) min screen.bounds.width
      val height = (900 max (screen.bounds.height / 2)) min screen.bounds.height
      jconsole.setBounds(
        screen.bounds.x + (screen.bounds.width - width) / 2,
        screen.bounds.y + (screen.bounds.height - height) / 2,
        width, height)

      jconsole.setVisible(true)

      Untyped.method(classOf[JConsole], "createMDI").invoke(jconsole)

      Isabelle_Thread.fork(name = "JConsole.addVmid") {
        try {
          val proxy_client = ProxyClient.getProxyClient(vm)

          GUI_Thread.later {
            try {
              val vm_panel =
                Untyped.constructor(classOf[VMPanel], classOf[ProxyClient], Integer.TYPE)
                  .newInstance(proxy_client, java.lang.Integer.valueOf(update_interval.ms.toInt))

              Untyped.field(vm_panel, "shouldUseSSL").setBoolean(vm_panel, false)

              Untyped.method(classOf[JConsole], "addFrame", classOf[VMPanel])
                .invoke(jconsole, vm_panel)

              GUI_Thread.later { jconsole.tileWindows() }

              vm_panel.connect()
            }
            catch {
              case exn: Throwable =>
                GUI.error_dialog(jconsole, "Error", GUI.scrollable_text(Exn.message(exn)))
            }
          }
        }
        catch {
          case exn: Throwable =>
            GUI.error_dialog(jconsole, "Error", GUI.scrollable_text(Exn.message(exn)))
        }
      }
    }
  }


  /* java monitor on new JVM: asynchronous process */

  def java_monitor_external(
    parent: Component,
    pid: Long = default_pid,
    look_and_feel: String = "",
    update_interval: Time = default_update_interval)
  {
    Future.thread(name = "java_monitor", daemon = true) {
      try {
        Isabelle_System.bash(
          "isabelle java_monitor " +
            " -P " + Bash.string(pid.toString) +
            " -L " + Bash.string(look_and_feel) +
            " -s " + Bash.string(update_interval.seconds.toString)).check
      }
      catch {
        case exn: Throwable =>
          GUI_Thread.later {
            GUI.error_dialog(parent, "System error", GUI.scrollable_text(Exn.message(exn)))
          }
      }
    }
  }


  /* command line entry point */

  def main(args: Array[String])
  {
    Command_Line.tool {
      var look_and_feel = ""
      var pid = 0L
      var update_interval = default_update_interval

      val getopts = Getopts("""
Usage: isabelle java_monitor [OPTIONS]

  Options are:
    -L CLASS     class name of GUI look-and-feel
    -P PID       Java process id (REQUIRED)
    -s SECONDS   update interval in seconds (default: """ + default_update_interval + """)

  Monitor another Java process.
""",
        "L:" -> (arg => look_and_feel = arg),
        "P:" -> (arg => pid = Value.Long.parse(arg)),
        "s:" -> (arg => update_interval = Time.seconds(Value.Double.parse(arg))))

      val more_args = getopts(args)
      if (more_args.nonEmpty || pid == 0L) getopts.usage()

      java_monitor_internal(pid = pid, look_and_feel = look_and_feel, update_interval = update_interval)

      Thread.sleep(Long.MaxValue)
    }
  }
}
