/***************************************************************************
  Title:      GraphBrowser/AWTFontMetrics.java
  ID:         $Id$
  Author:     Gerwin Klein, TU Muenchen
  Copyright   2003  TU Muenchen
  License:    GPL (GNU GENERAL PUBLIC LICENSE)

  AbstractFontMetrics avoids dependency on java.awt.FontMetrics in 
  batch mode.
  
***************************************************************************/

package GraphBrowser;

public interface AbstractFontMetrics {
  public int stringWidth(String str);
  public int getAscent();
  public int getDescent();
}
