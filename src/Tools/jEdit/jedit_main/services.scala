/*  Title:      Tools/jEdit/jedit_main/services.scala
    Author:     Makarius

Isabelle/jEdit services.
*/

package isabelle.jedit_main


class Fold_Handler extends isabelle.jedit.Fold_Handling.Fold_Handler

class Context_Menu extends isabelle.jedit.Context_Menu

class Isabelle_Export_VFS extends isabelle.jedit.Isabelle_Export.VFS

class Isabelle_Session_VFS extends isabelle.jedit.Isabelle_Session.VFS

class Active_Misc_Handler extends isabelle.jedit.Active.Misc_Handler

class Graphview_Dockable_Handler extends isabelle.jedit.Graphview_Dockable.Handler

class Status_Widget_Java_Factory extends isabelle.jedit.Status_Widget.Java_Factory

class Status_Widget_ML_Factory extends isabelle.jedit.Status_Widget.ML_Factory
