/*  Title:      Pure/Tools/java_monitor.scala
    Author:     Makarius

Wrapper for the OpenJDK "jconsole" tool, with various adjustments.
*/

package isabelle


import java.lang.Class
import java.awt.Component
import javax.swing.UIManager


object Java_Monitor {
  /* Java classes */

  object ClassOf {
    val Component: Class[_ <: AnyRef] = Class.forName("java.awt.Component")
    val JConsole: Class[_ <: AnyRef] = Class.forName("sun.tools.jconsole.JConsole")
    val LocalVirtualMachine: Class[_ <: AnyRef] = Class.forName("sun.tools.jconsole.LocalVirtualMachine")
    val Messages: Class[_ <: AnyRef] = Class.forName("sun.tools.jconsole.Messages")
    val ProxyClient: Class[_ <: AnyRef] = Class.forName("sun.tools.jconsole.ProxyClient")
    val Resources: Class[_ <: AnyRef] = Class.forName("sun.tools.jconsole.Resources")
    val VMPanel: Class[_ <: AnyRef] = Class.forName("sun.tools.jconsole.VMPanel")
  }


  /* default arguments */

  def default_pid: Long = ProcessHandle.current().pid
  val default_update_interval: Time = Time.seconds(3)


  /* java monitor on this JVM: asynchronous GUI application with with system exit */

  def java_monitor_internal(
    pid: Long = default_pid,
    look_and_feel: String = "",
    update_interval: Time = default_update_interval
  ): Unit = {
    val vm =
      if (pid.toInt.toLong == pid) {
        Untyped.the_method(ClassOf.LocalVirtualMachine, "getLocalVirtualMachine")
          .invoke(null, pid.toInt)
      }
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
          Untyped.the_method(ClassOf.Resources, "format").
            invoke(null,
              Untyped.get_static(ClassOf.Messages, "JCONSOLE_VERSION"),
                System.getProperty("java.runtime.version")))
      }

      val jconsole =
        Untyped.the_constructor(ClassOf.JConsole).newInstance(false).asInstanceOf[Component]

      val screen = GUI.mouse_location()
      val width = (1200 max (screen.bounds.width / 2)) min screen.bounds.width
      val height = (900 max (screen.bounds.height / 2)) min screen.bounds.height
      Untyped.method(ClassOf.Component, "setBounds", classOf[Int], classOf[Int], classOf[Int], classOf[Int])
        .invoke(jconsole,
          screen.bounds.x + (screen.bounds.width - width) / 2,
          screen.bounds.y + (screen.bounds.height - height) / 2,
          width, height)

      Untyped.the_method(ClassOf.Component, "setVisible").invoke(jconsole, true)

      Untyped.the_method(ClassOf.JConsole, "createMDI").invoke(jconsole)

      Isabelle_Thread.fork(name = "JConsole.addVmid") {
        try {
          val proxy_client =
            Untyped.method(ClassOf.ProxyClient, "getProxyClient", ClassOf.LocalVirtualMachine)
              .invoke(null, vm)

          GUI_Thread.later {
            try {
              val vm_panel =
                Untyped.constructor(ClassOf.VMPanel, ClassOf.ProxyClient, Integer.TYPE)
                  .newInstance(proxy_client, java.lang.Integer.valueOf(update_interval.ms.toInt))

              Untyped.field(vm_panel, "shouldUseSSL").setBoolean(vm_panel, false)

              Untyped.method(ClassOf.JConsole, "addFrame", ClassOf.VMPanel)
                .invoke(jconsole, vm_panel)

              GUI_Thread.later {
                Untyped.the_method(ClassOf.JConsole, "tileWindows").invoke(jconsole)
              }

              Untyped.the_method(ClassOf.VMPanel, "connect").invoke(vm_panel)
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
    update_interval: Time = default_update_interval
  ): Unit = {
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

  def main(args: Array[String]): Unit = {
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
