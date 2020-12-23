/*  Title:      Pure/GUI/desktop_app.scala
    Author:     Makarius

Support for desktop applications, notably on macOS.
*/

package isabelle

import java.awt.Desktop


object Desktop_App
{
  def desktop_action(action: Desktop.Action, f: Desktop => Unit): Unit =
    if (Desktop.isDesktopSupported) {
      val desktop = Desktop.getDesktop
      if (desktop.isSupported(action)) f(desktop)
    }

  def about_handler(handler: => Unit): Unit =
    desktop_action(Desktop.Action.APP_ABOUT, _.setAboutHandler(_ => handler))
}
