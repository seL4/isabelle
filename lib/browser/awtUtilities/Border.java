/***************************************************************************
  Title:      awtUtilities/Border.java
  ID:         $Id$
  Author:     Stefan Berghofer, TU Muenchen
  Copyright   1997  TU Muenchen

  This class defines a nice 3D border.
***************************************************************************/

package awtUtilities;

import java.awt.*;

public class Border extends Panel {
	int bs;

	public Insets insets() {
		return new Insets(bs*3/2,bs*3/2,bs*3/2,bs*3/2);
	}

	public Border(Component comp,int s) {
		setLayout(new GridLayout(1,1));
		add(comp);
		bs=s;
	}

	public void paint(Graphics g) {
		int w=size().width;
		int h=size().height;
		int x1[]={0,bs,w-bs,w}, y1[]={0,bs,bs,0};
		int x2[]={w,w-bs,w-bs,w}, y2[]={0,bs,h-bs,h};
		int y3[]={h,h-bs,h-bs,h};

		g.setColor(new Color(224,224,224));
		g.fillPolygon(y1,y2,4);
		g.fillPolygon(x1,y1,4);
		g.setColor(Color.gray);
		g.fillPolygon(x2,y2,4);
		g.fillPolygon(x1,y3,4);
	}
}
