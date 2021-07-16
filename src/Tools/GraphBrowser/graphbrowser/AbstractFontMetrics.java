/***************************************************************************
  Title:      graphbrowser/AWTFontMetrics.java
  Author:     Gerwin Klein, TU Muenchen

  AbstractFontMetrics avoids dependency on java.awt.FontMetrics in 
  batch mode.
  
***************************************************************************/

package isabelle.graphbrowser;

public interface AbstractFontMetrics {
  public int stringWidth(String str);
  public int getAscent();
  public int getDescent();
}
