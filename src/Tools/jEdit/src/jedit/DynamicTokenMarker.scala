/*
 * include isabelle's command- and keyword-declarations
 * live in jEdits syntax-highlighting
 * 
 * one TokenMarker per prover
 *
 * @author Fabian Immler, TU Munich
 */

package isabelle.jedit

import org.gjt.sp.jedit.syntax.{ModeProvider, Token, TokenMarker, ParserRuleSet, KeywordMap}

class DynamicTokenMarker extends TokenMarker {

  val ruleset = new ParserRuleSet("isabelle", "MAIN")

  // copy rules and keywords from basic isabelle mode
  val original = ModeProvider.instance.getMode("isabelle").getTokenMarker.getMainRuleSet
  ruleset.addRuleSet(original)
  ruleset.setKeywords(new KeywordMap(false))
  ruleset.setDefault(0)
  ruleset.setDigitRegexp(null)
  ruleset.setEscapeRule(original.getEscapeRule)
  ruleset.setHighlightDigits(false)
  ruleset.setIgnoreCase(false)
  ruleset.setNoWordSep("_'.?")
  ruleset.setProperties(null)
  ruleset.setTerminateChar(-1)

  addRuleSet(ruleset)

  private val kinds = List(
    OuterKeyword.minor -> Token.KEYWORD4,
    OuterKeyword.control -> Token.INVALID,
    OuterKeyword.diag -> Token.LABEL,
    OuterKeyword.heading -> Token.KEYWORD1,
    OuterKeyword.theory1 -> Token.KEYWORD4,
    OuterKeyword.theory2 -> Token.KEYWORD1,
    OuterKeyword.proof1 -> Token.KEYWORD1,
    OuterKeyword.proof2 -> Token.KEYWORD2,
    OuterKeyword.improper -> Token.DIGIT
  )
  def += (name: String, kind: String) = {
    kinds.find(pair => pair._1.contains(kind)) match {
      case None =>
      case Some((_, kind_byte)) => getMainRuleSet.getKeywords.add(name, kind_byte)
    }
  }
}
