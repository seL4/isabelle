/***************************************************************************
  Title:      GraphBrowser/TreeBrowser.java
  ID:         $Id$
  Author:     Stefan Berghofer, TU Muenchen
  License:    GPL (GNU GENERAL PUBLIC LICENSE)

  This class defines the browser window which is used to display directory
  trees. It contains methods for handling events.
***************************************************************************/

package GraphBrowser;

import java.awt.*;
import java.awt.event.*;
import java.util.*;


public class TreeBrowser extends Canvas implements MouseListener
{
	TreeNode t;
	TreeNode selected;
	GraphView gv;
	long timestamp;
	Dimension size;
	boolean parent_needs_layout;
	Font font;

	public TreeBrowser(TreeNode tn, GraphView gr, Font f) {
		t = tn; gv = gr; font = f;
		size = new Dimension(0, 0);
		parent_needs_layout = true;
		addMouseListener(this);
	}

	public Dimension getPreferredSize() {
		return size;
	}

	public void mouseEntered(MouseEvent evt) {}

	public void mouseExited(MouseEvent evt) {}

	public void mouseReleased(MouseEvent evt) {}

	public void mousePressed(MouseEvent evt) {}

	public void mouseClicked(MouseEvent e)
	{
		TreeNode l=t.lookup(e.getY());

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
				if (e.getWhen()-timestamp < 400 && !(vx.getPath().equals("")))
					gv.getBrowser().viewFile(vx.getPath());
				timestamp=e.getWhen();

			}
			selected=l;
			parent_needs_layout = true;
			repaint();
		}
	}

	public void selectNode(TreeNode nd) {
		Vector v=new Vector(10,10);
		nd.select();
		t.collapsedDirectories(v);
		gv.collapseDir(v);
		gv.relayout();
		selected=nd;
		parent_needs_layout = true;
		repaint();
	}

	public void paint(Graphics g)
	{
		g.setFont(font);
		Dimension d = t.draw(g,5,5,selected);
		if (parent_needs_layout) {
			size = new Dimension(5+d.width, 5+d.height);
			parent_needs_layout = false;
			getParent().doLayout();
		}
	}
}

