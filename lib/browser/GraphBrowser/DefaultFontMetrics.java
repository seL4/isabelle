/***************************************************************************
  Title:      GraphBrowser/DefaultFontMetrics.java
  ID:         $Id$
  Author:     Stefan Berghofer, TU Muenchen
  License:    GPL (GNU GENERAL PUBLIC LICENSE)

  Default font metrics which is used when no graphics context
  is available.
***************************************************************************/

package GraphBrowser;

import java.awt.*;

public class DefaultFontMetrics extends FontMetrics
{
    protected static int[] chars =
	{13, 13, 17, 27, 27, 43, 32, 11, 16, 16, 19, 28, 13, 28, 13, 13, 27,
	 27, 27, 27, 27, 27, 27, 27, 27, 27, 13, 13, 28, 28, 28, 27, 49, 32,
	 32, 35, 35, 32, 29, 37, 35, 13, 24, 32, 27, 40, 35, 37, 32, 37, 35,
	 32, 29, 35, 32, 45, 32, 32, 29, 13, 13, 13, 22, 27, 11, 27, 27, 24,
	 27, 27, 13, 27, 27, 11, 11, 24, 11, 40, 27, 27, 27, 27, 16, 24, 13,
	 27, 24, 35, 24, 24, 24, 16, 12, 16, 28};

    public DefaultFontMetrics(Font f)
    { super(f); }

    public int getLeading()
    { return 1; }

    public int getAscent()
    { return (int)(Math.round(font.getSize() * 46.0 / 48.0)); }

    public int getDescent()
    { return (int)(Math.round(font.getSize() * 10.0 / 48.0)); }

    public int charWidth(char c) {
	if (c < 32 || c > 126) { return 0; }
	else {
	    return (int)(Math.round(chars[c - 32] * font.getSize() / 48.0));
	}
    }

    public int stringWidth(String s) {
	int l=0, i;
	for (i=0; i < s.length(); i++) { l += charWidth(s.charAt(i)); }
	return l;
    }
}
