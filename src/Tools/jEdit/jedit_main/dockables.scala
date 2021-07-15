/*  Title:      Tools/jEdit/jedit_main/dockables.scala
    Author:     Makarius

Isabelle/jEdit dockables.
*/

package isabelle.jedit_main


import org.gjt.sp.jedit.View


class Debugger_Dockable(view: View, position: String)
  extends isabelle.jedit.Debugger_Dockable(view, position)

class Documentation_Dockable(view: View, position: String)
  extends isabelle.jedit.Documentation_Dockable(view, position)

class Info_Dockable(view: View, position: String)
  extends isabelle.jedit.Info_Dockable(view, position)

class Graphview_Dockable(view: View, position: String)
  extends isabelle.jedit.Graphview_Dockable(view, position)

class Monitor_Dockable(view: View, position: String)
  extends isabelle.jedit.Monitor_Dockable(view, position)

class Output_Dockable(view: View, position: String)
  extends isabelle.jedit.Output_Dockable(view, position)

class Protocol_Dockable(view: View, position: String)
  extends isabelle.jedit.Protocol_Dockable(view, position)

class Query_Dockable(view: View, position: String)
  extends isabelle.jedit.Query_Dockable(view, position)

class Raw_Output_Dockable(view: View, position: String)
  extends isabelle.jedit.Raw_Output_Dockable(view, position)

class Simplifier_Trace_Dockable(view: View, position: String)
  extends isabelle.jedit.Simplifier_Trace_Dockable(view, position)

class Sledgehammer_Dockable(view: View, position: String)
  extends isabelle.jedit.Sledgehammer_Dockable(view, position)

class State_Dockable(view: View, position: String)
  extends isabelle.jedit.State_Dockable(view, position)

class Symbols_Dockable(view: View, position: String)
  extends isabelle.jedit.Symbols_Dockable(view, position)

class Syslog_Dockable(view: View, position: String)
  extends isabelle.jedit.Syslog_Dockable(view, position)

class Theories_Dockable(view: View, position: String)
  extends isabelle.jedit.Theories_Dockable(view, position)

class Timing_Dockable(view: View, position: String)
  extends isabelle.jedit.Timing_Dockable(view, position)
