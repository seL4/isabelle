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
	public DefaultFontMetrics(Font f)
	{ super(f); }

	// note : values are rather inaccurate !

	public int getLeading()
	{ return 1; }

	public int getAscent()
	{ return (int)(Math.round(font.getSize()*5.0/6.0)); }

	public int getDescent()
	{ return (int)(Math.round(font.getSize()/6.0)); }

	public int stringWidth(String s)
	{ return (int)(Math.round(s.length()*font.getSize()/2.0)); }
}
