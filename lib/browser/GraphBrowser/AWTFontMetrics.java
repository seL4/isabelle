package GraphBrowser;

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
