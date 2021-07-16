/***************************************************************************
  Title:      GraphBrowser/AWTFontMetrics.java
  Author:     Gerwin Klein, TU Muenchen

  AbstractFontMetrics avoids dependency on java.awt.FontMetrics in 
  batch mode.
  
***************************************************************************/

package GraphBrowser;

public interface AbstractFontMetrics {
  public int stringWidth(String str);
  public int getAscent();
  public int getDescent();
}
