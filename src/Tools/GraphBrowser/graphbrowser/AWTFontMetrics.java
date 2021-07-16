/***************************************************************************
  Title:      graphbrowser/AWTFontMetrics.java
  Author:     Gerwin Klein, TU Muenchen

  AbstractFontMetrics from the AWT for graphics mode.
  
***************************************************************************/

package isabelle.graphbrowser;

import java.awt.FontMetrics;

public class AWTFontMetrics implements AbstractFontMetrics {
  private FontMetrics fontMetrics;

  public AWTFontMetrics(FontMetrics m) {
    fontMetrics = m;
  }

  public int stringWidth(String str) {
    return fontMetrics.stringWidth(str);
  }

  public int getAscent() {
    return fontMetrics.getAscent();
  }

  public int getDescent() {
    return fontMetrics.getDescent();
  }
}
