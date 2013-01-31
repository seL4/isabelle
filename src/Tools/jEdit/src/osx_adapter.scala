/*  Title:      Tools/jEdit/src/osx_adapter.scala
    Author:     Makarius

Some native OS X support.
*/

package isabelle.jedit


import isabelle._

import java.lang.{Class, ClassNotFoundException}
import java.lang.reflect.{InvocationHandler, Method, Proxy}


object OSX_Adapter
{
  def set_quit_handler(target: AnyRef, quit_handler: Method)
  {
    set_handler(new OSX_Adapter("handle_quit", target, quit_handler))
  }

  var application: Any = null

  def set_handler(adapter: OSX_Adapter)
  {
    try {
      val application_class: Class[_] = Class.forName("com.apple.eawt.Application")
      if (application == null)
        application = application_class.getConstructor().newInstance()

      val application_listener_class: Class[_] =
        Class.forName("com.apple.eawt.ApplicationListener")
      val add_listener_method =
        application_class.getDeclaredMethod("addApplicationListener", application_listener_class)

      val osx_adapter_proxy =
        Proxy.newProxyInstance(classOf[OSX_Adapter].getClassLoader,
          Array(application_listener_class), adapter)
      add_listener_method.invoke(application, osx_adapter_proxy)
    }
    catch {
      case exn: ClassNotFoundException =>
        java.lang.System.err.println(
          "com.apple.eawt.Application unavailable -- cannot install native OS X handler")
    }
  }
}

class OSX_Adapter(proxy_signature: String, target_object: AnyRef, target_method: Method)
  extends InvocationHandler
{
  override def invoke(proxy: Any, method: Method, args: Array[AnyRef]): AnyRef =
  {
    if (proxy_signature == method.getName && args.length == 1) {
      val result = target_method.invoke(target_object)
      val handled = result == null || result.toString == "true"

      val event = args(0)
      if (event != null) {
        val set_handled_method =
          event.getClass.getDeclaredMethod("setHandled", classOf[java.lang.Boolean])
        set_handled_method.invoke(event, java.lang.Boolean.valueOf(handled))
      }
    }
    null
  }
}

