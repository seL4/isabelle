/*  Title:      Tools/VSCode/src/vscode_spell_checker.scala
    Author:     Makarius

Specific spell-checker support for Isabelle/VSCode.
*/

package isabelle.vscode


import isabelle._


object VSCode_Spell_Checker
{
  def decoration(rendering: VSCode_Rendering): Document_Model.Decoration =
  {
    val model = rendering.model
    val ranges =
      (for {
        spell_checker <- rendering.resources.spell_checker.get.iterator
        spell_range <- rendering.spell_checker_ranges(model.content.text_range).iterator
        text <- model.try_get_text(spell_range).iterator
        info <- spell_checker.marked_words(spell_range.start, text).iterator
      } yield info.range).toList
    Document_Model.Decoration.ranges("spell_checker", ranges)
  }

  def completion(rendering: VSCode_Rendering, caret: Text.Offset): Option[Completion.Result] =
    rendering.resources.spell_checker.get.flatMap(_.completion(rendering, caret))

  def menu_items(rendering: VSCode_Rendering, caret: Text.Offset): List[Protocol.CompletionItem] =
  {
    val result =
      for {
        spell_checker <- rendering.resources.spell_checker.get
        range = rendering.before_caret_range(caret)
        Text.Info(_, word) <- Spell_Checker.current_word(rendering, range)
      } yield (spell_checker, word)

    result match {
      case Some((spell_checker, word)) =>

        def item(command: Protocol.Command): Protocol.CompletionItem =
          Protocol.CompletionItem(
            label = command.title,
            text = Some(""),
            range = Some(rendering.model.content.doc.range(Text.Range(caret))),
            command = Some(command))

        val update_items =
          if (spell_checker.check(word))
            List(
              item(Protocol.Exclude_Word.command),
              item(Protocol.Exclude_Word_Permanently.command))
          else
            List(
              item(Protocol.Include_Word.command),
              item(Protocol.Include_Word_Permanently.command))

        val reset_items =
          spell_checker.reset_enabled() match {
            case 0 => Nil
            case n =>
              val command = Protocol.Reset_Words.command
              List(item(command).copy(label = command.title + " (" + n + ")"))
          }

        update_items ::: reset_items

      case None => Nil
    }
  }
}
