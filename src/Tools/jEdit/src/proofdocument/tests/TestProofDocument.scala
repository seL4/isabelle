package isabelle.proofdocument.tests

import org.testng.annotations._
import org.testng.Assert._
  
import isabelle.proofdocument._
import isabelle.utils.EventSource

class TextMockup() extends Text {
  var content = ""
  val changes = new EventSource[Text.Changed]

  def content(start : Int, stop : Int) = content.substring(start, stop)
  def length = content.length
  
  def change(start : Int, added : String, removed : Int) {
    content = content.substring(0, start) + added + content.substring(start + removed)
    changes.fire(new Text.Changed(start, added.length, removed))
  }
} 

class ProofDocumentTest(text : Text) extends ProofDocument[String](text) {
  var start : Token[String] = null
  var stop : Token[String] = null
  var removed : Token[String] = null

  def isStartKeyword(s : String) : Boolean = false
  
  def tokenChanged(start_ : Token[String], stop_ : Token[String], 
                   removed_ : Token[String]) {
    start = start_
    stop = stop_
    removed = removed_
  }
  
  override def tokens = super.tokens
  override def tokens(s : Token[String]) = super.tokens(s)
  override def tokens(s : Token[String], e : Token[String]) = super.tokens(s, e)
  
  def first = firstToken
  def last = lastToken
  
  def checkLinks(first : Token[String], last : Token[String]) {
    var iter = first
    var prev : Token[String] = null
    
    while(iter != null) {
      assert(iter.previous == prev)
      prev = iter
      iter = iter.next
    }
    if (last != null)
      assert(prev == last)
  }
}

class TestProofDocument {
  private def ranges(ts : Iterator[Token[String]]) =
    (for (t <- ts) yield (t.start, t.stop)).toList
  
  @Test
  def testParsing() {
    def check(tokens : String*) = {
      var content = ""
      var structure = Nil : List[(Int, Int)]
    
      for(tok <- tokens) {
        if (tok != " ")
          structure = (content.length, content.length + tok.length) :: structure
        content = content + tok
      }
      
      val text = new TextMockup()
      val document = new ProofDocumentTest(text)
      text.change(0, content, 0)
      document.checkLinks(document.first, document.last)
      assertEquals(ranges(document.tokens), structure.reverse)
    }
  
    check("lemma", " " , "fixes", " ", "A", " ", ":", ":", " ", "'a", " ", 
          "shows", "\"True\"", " ", "using", "`A = A`", "by", "(", "auto", " ", 
          "simp", " ", "add", ":", "refl", ")")
  }
  
  @Test
  def testChanging() {
    val text = new TextMockup()
    val document = new ProofDocumentTest(text)

    def compare(start : Int, add : String, remove : Int) {
      val oldDocument = ranges(document.tokens)
      text.change(start, add, remove)
      document.checkLinks(document.first, document.last)
      document.checkLinks(document.removed, null)
      
      val offset = remove - add.length
      val before = if (document.start == null) Nil 
                   else ranges(document.tokens(document.first, document.start.next))
      val after = (for(t <- document.tokens(document.stop)) 
                     yield (t.start + offset, t.stop + offset)).toList
      val removed = ranges(document.tokens(document.removed))
      assertEquals((before ++ removed ++ after).length, oldDocument.length, 
                   "Mismatch on token count")
      assertEquals(before, oldDocument.take(before.length),
                   "Tokens before changed part")
      assertEquals(after, oldDocument.drop(before.length + removed.length),
                   "Tokens before changed part")
    
      val newText = new TextMockup()
      val newDocument = new ProofDocumentTest(newText)
      newText.change(0, text.content, 0)
      newDocument.checkLinks(newDocument.first, newDocument.last)

      assertEquals(ranges(document.tokens), ranges(newDocument.tokens),
                   "Mismatch on entirely reparsed document")
    }
  
    val s = """lemma fixes a :: nat assumes T: \"A\" shows \"B ==> A\" using `A` by auto"""
    compare(0, s, text.content.length)
    compare(0, "(*", 0)
    compare(text.content.length, "*)", 0)
    compare(0, "", 2)
    compare(1, "", 7)
    
    compare(0, "test :: 12 34", text.content.length)
    compare(6, "", 1)
    compare(6, ":", 0)
    compare(8, "56", 2)
    compare(2, "", 4)
    
    compare(0, "test  :: 12 34", text.content.length)
    compare(5, "test 1 2", 0)
    compare(4, " test 2 3", 0)

    compare(0, "theory Scratch\nimports Main\nbegin\n\nlemma test_x: fixes X :: nat shows \"∃ X. X > 0\" by auto\n\nend", text.content.length)
    compare(72, "", 11)
    compare(71, "", 1)
  }
}
