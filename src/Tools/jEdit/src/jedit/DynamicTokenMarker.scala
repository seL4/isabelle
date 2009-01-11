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
  ruleset.setNoWordSep("_")
  ruleset.setProperties(null)
  ruleset.setTerminateChar(-1)

  addRuleSet(ruleset)

  def += (token:String, kind:String) = {
    val kind_byte = kind match {
      case Markup.COMMAND => Token.KEYWORD4
      case Markup.KEYWORD => Token.KEYWORD3
    }
    getMainRuleSet.getKeywords.add(token, kind_byte)
  }
}
