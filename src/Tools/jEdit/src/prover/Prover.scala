/*
 * Higher-level prover communication
 *
 * @author Johannes Hölzl, TU Munich
 * @author Fabian Immler, TU Munich
 * @author Makarius
 */

package isabelle.prover


import scala.collection.mutable.{HashMap, HashSet}
import scala.collection.immutable.{TreeSet}

import org.gjt.sp.util.Log

import isabelle.proofdocument.{ProofDocument, Text, Token}
import isabelle.IsarDocument


class Prover(isabelle_system: IsabelleSystem)
{
  private var _logic = isabelle_system.getenv_strict("ISABELLE_LOGIC")
  private var process: Isar = null

  private val commands = new HashMap[IsarDocument.Command_ID, Command]


  /* outer syntax keywords */

  val decl_info = new EventBus[(String, String)]

  private val keyword_decls = new HashSet[String] {
    override def +=(name: String) = {
      decl_info.event(name, OuterKeyword.MINOR)
      super.+=(name)
    }
  }
  private val command_decls = new HashMap[String, String] {
    override def +=(entry: (String, String)) = {
      decl_info.event(entry)
      super.+=(entry)
    }
  }
  def is_command_keyword(s: String): Boolean = command_decls.contains(s)


  /* completions */

  var _completions = new TreeSet[String]
  def completions = _completions
  /* // TODO: ask Makarius to make Interpretation.symbols public (here: read-only as 'symbol_map')
  val map = isabelle.jedit.Isabelle.symbols.symbol_map
  for(xsymb <- map.keys) {
    _completions += xsymb
    if(map(xsymb).get("abbrev").isDefined) _completions += map(xsymb)("abbrev")
  }
  */
  decl_info += (k_v => _completions += k_v._1)


  /* event handling */

  private var initialized = false

  val activated = new EventBus[Unit]
  val command_info = new EventBus[Command]
  val output_info = new EventBus[String]
  var document: ProofDocument = null


  def command_change(c: Command) = Swing.now { command_info.event(c) }

  private def handle_result(r: IsabelleProcess.Result)
  {
    val (id, st) = r.props.find(p => p._1 == Markup.ID) match
      { case None => (null, null)
        case Some((_, i)) => (i, commands.getOrElse(i, null)) }

    if (r.kind == IsabelleProcess.Kind.STDOUT || r.kind == IsabelleProcess.Kind.STDIN)
      Swing.now { output_info.event(r.result) }
    else if (r.kind == IsabelleProcess.Kind.WRITELN && !initialized) {
      initialized = true
      Swing.now {
        if (document != null) {
          document.activate()
          activated.event(())
        }
      }
    }
    else {
      if (st == null || (st.status != Command.Status.REMOVED && st.status != Command.Status.REMOVE)) {
        r.kind match {

          case IsabelleProcess.Kind.STATUS =>
            //{{{ handle all kinds of status messages here
            val tree = process.parse_message(r)
            tree match {
              case XML.Elem(Markup.MESSAGE, _, elems) =>
                for (elem <- elems) {
                  elem match {
                    //{{{
                    // command status
                    case XML.Elem(Markup.FINISHED, _, _) =>
                      st.status = Command.Status.FINISHED
                      command_change(st)
                    case XML.Elem(Markup.UNPROCESSED, _, _) =>
                      st.status = Command.Status.UNPROCESSED
                      command_change(st)
                    case XML.Elem(Markup.FAILED, _, _) =>
                      st.status = Command.Status.FAILED
                      command_change(st)
                    case XML.Elem(Markup.DISPOSED, _, _) =>
                      commands.removeKey(st.id)
                      st.status = Command.Status.REMOVED
                      command_change(st)

                    // command and keyword declarations
                    case XML.Elem(Markup.COMMAND_DECL,
                        (Markup.NAME, name) :: (Markup.KIND, kind) :: _, _) =>
                      command_decls += (name -> kind)
                    case XML.Elem(Markup.KEYWORD_DECL, (Markup.NAME, name) :: _, _) =>
                      keyword_decls += name

                    // other markup
                    case XML.Elem(kind,
                        (Markup.OFFSET, offset) :: (Markup.END_OFFSET, end_offset) ::
                             (Markup.ID, markup_id) :: _, _) =>
                      val begin = Int.unbox(java.lang.Integer.valueOf(offset)) - 1
                      val end = Int.unbox(java.lang.Integer.valueOf(end_offset)) - 1

                      val command =
                        // outer syntax: no id in props
                        if (st == null) commands.getOrElse(markup_id, null)
                        // inner syntax: id from props
                        else st
                      command.root_node.insert(command.node_from(kind, begin, end))

                    case _ =>
                    //}}}
                  }
                }
              case _ =>
            }
            //}}}

          case IsabelleProcess.Kind.ERROR if st != null =>
            val tree = process.parse_message(r)
            if (st.status != Command.Status.REMOVED && st.status != Command.Status.REMOVE)
              st.status = Command.Status.FAILED
            st.add_result(tree)
            command_change(st)

          case IsabelleProcess.Kind.WRITELN | IsabelleProcess.Kind.PRIORITY
            | IsabelleProcess.Kind.WARNING if st != null =>
            val tree = process.parse_message(r)
            st.add_result(tree)
            command_change(st)

          case _ =>
        }
      }
    }
  }


  def start(logic: String) {
    if (logic != null) _logic = logic

    val results = new EventBus[IsabelleProcess.Result]
    results += handle_result
    results.logger = Log.log(Log.ERROR, null, _)

    process = new Isar(isabelle_system, results, "-m", "xsymbols", _logic)
  }

  def stop() {
    process.kill
  }

  def set_document(text: Text, path: String) {
    this.document = new ProofDocument(text, this)
    process.ML("ThyLoad.add_path " + IsabelleSyntax.encode_string(path))

    document.structural_changes += (changes => {
      for (cmd <- changes.removedCommands) remove(cmd)
      for (cmd <- changes.addedCommands) send(cmd)
    })
    if (initialized) {
      document.activate()
      activated.event(())
    }
  }

  private def send(cmd: Command) {
    cmd.status = Command.Status.UNPROCESSED
    commands.put(cmd.id, cmd)

    val content = isabelle_system.symbols.encode(document.getContent(cmd))
    process.create_command(cmd.id, content)
    process.insert_command(if (cmd.prev == null) "" else cmd.prev.id, cmd.id)
  }

  def remove(cmd: Command) {
    cmd.status = Command.Status.REMOVE
    process.remove_command(cmd.id)
  }
}
