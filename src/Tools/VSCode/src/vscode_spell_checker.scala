/*  Title:      Tools/VSCode/src/vscode_spell_checker.scala
    Author:     Makarius

Specific spell-checker support for Isabelle/VSCode.
*/

package isabelle.vscode


import isabelle._


object VSCode_Spell_Checker
{
  def decoration(rendering: VSCode_Rendering): VSCode_Model.Decoration =
  {
    val model = rendering.model
    val ranges =
      (for {
        spell_checker <- rendering.resources.spell_checker.get.iterator
        spell <- rendering.spell_checker(model.content.text_range).iterator
        text <- model.get_text(spell.range).iterator
        info <- spell_checker.marked_words(spell.range.start, text).iterator
      } yield info.range).toList
    VSCode_Model.Decoration.ranges("spell_checker", ranges)
  }

  def completion(rendering: VSCode_Rendering, caret: Text.Offset): Option[Completion.Result] =
    rendering.resources.spell_checker.get.flatMap(_.completion(rendering, caret))

  def menu_items(rendering: VSCode_Rendering, caret: Text.Offset): List[LSP.CompletionItem] =
  {
    val result =
      for {
        spell_checker <- rendering.resources.spell_checker.get
        range = rendering.before_caret_range(caret)
        Text.Info(_, word) <- Spell_Checker.current_word(rendering, range)
      } yield (spell_checker, word)

    result match {
      case Some((spell_checker, word)) =>

        def item(command: LSP.Command): LSP.CompletionItem =
          LSP.CompletionItem(
            label = command.title,
            text = Some(""),
            range = Some(rendering.model.content.doc.range(Text.Range(caret))),
            command = Some(command))

        val update_items =
          if (spell_checker.check(word))
            List(
              item(LSP.Exclude_Word.command),
              item(LSP.Exclude_Word_Permanently.command))
          else
            List(
              item(LSP.Include_Word.command),
              item(LSP.Include_Word_Permanently.command))

        val reset_items =
          spell_checker.reset_enabled() match {
            case 0 => Nil
            case n =>
              val command = LSP.Reset_Words.command
              List(item(command).copy(label = command.title + " (" + n + ")"))
          }

        update_items ::: reset_items

      case None => Nil
    }
  }
}
