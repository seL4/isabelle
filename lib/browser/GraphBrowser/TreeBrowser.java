/***************************************************************************
  Title:      GraphBrowser/TreeBrowser.java
  ID:         $Id$
  Author:     Stefan Berghofer, TU Muenchen
  Copyright   1997  TU Muenchen

  This class defines the browser window which is used to display directory
  trees. It contains methods for handling events.
***************************************************************************/

package GraphBrowser;

import java.awt.*;
import awtUtilities.ScrollCanvas;
import java.util.*;


public class TreeBrowser extends ScrollCanvas
{
	TreeNode t;
	TreeNode selected;
	GraphView gv;
	long timestamp;

	public TreeBrowser(TreeNode tn,GraphView gr) {
		t=tn;gv=gr;
	}

	public boolean mouseDown(Event e,int x,int y)
	{
		TreeNode l=t.lookup(y);

		if (l!=null)
		{
			if (l.select()) {
				Vector v=new Vector(10,10);
				t.collapsedDirectories(v);
				gv.collapseDir(v);
				gv.relayout();
			} else {
				Vertex vx=gv.getGraph().getVertexByNum(l.getNumber());
				gv.focusToVertex(l.getNumber());
				vx=gv.getOriginalGraph().getVertexByNum(l.getNumber());
				if (e.when-timestamp < 400 && !(vx.getPath().equals("")))
					gv.getBrowser().viewFile(vx.getPath());
				timestamp=e.when;

			}
			selected=l;repaint();
			
		}
		return true;
	}

	public void selectNode(TreeNode nd) {
		Vector v=new Vector(10,10);
		nd.select();
		t.collapsedDirectories(v);
		gv.collapseDir(v);
		gv.relayout();
		selected=nd;repaint();
	}

	public void paintCanvas(Graphics g)
	{
		Dimension d=t.draw(g,5,5,selected);
		set_size(5+d.width,5+d.height);
	}
}

