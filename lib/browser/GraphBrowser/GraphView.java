/***************************************************************************
  Title:      GraphBrowser/GraphView.java
  ID:         $Id$
  Author:     Stefan Berghofer, TU Muenchen
  License:    GPL (GNU GENERAL PUBLIC LICENSE)

  This class defines the window in which the graph is displayed. It
  contains methods for handling events such as collapsing / uncollapsing
  nodes of the graph.
***************************************************************************/

package GraphBrowser;

import java.awt.*;
import java.awt.event.*;
import java.io.*;
import java.util.*;
import awtUtilities.*;

public class GraphView extends Canvas implements MouseListener, MouseMotionListener {
	Graph gra, gra2;
	GraphBrowser browser;
	Vertex v = null;
	Vector collapsed = new Vector(10,10);
	Vector collapsedDirs = new Vector(10,10);
	TreeBrowser tb;
	long timestamp;
	Vertex highlighted = null;
	Dimension size;
	boolean parent_needs_layout;

	public void setTreeBrowser(TreeBrowser br) {
		tb=br;
	}

	public GraphBrowser getBrowser() { return browser; }

	public Graph getGraph() { return gra; }

	public Graph getOriginalGraph() { return gra2; }

	public GraphView(Graph gr,GraphBrowser br) {
		gra2=gr;
		browser=br;
		gra=(Graph)(gra2.clone());
		parent_needs_layout = true;
		size = new Dimension(0, 0);
		addMouseListener(this);
		addMouseMotionListener(this);
	}

	public void PS(String fname,boolean printable) throws IOException {
	    Graph gra3 = (Graph)gra.clone();
	    gra3.layout(null);
	    gra3.PS(fname,printable);
	}

	public void paint(Graphics g) {
		gra.draw(g);
		if (highlighted!=null) highlighted.drawBox(g,Color.white);
		size = new Dimension(gra.max_x-gra.min_x, gra.max_y-gra.min_y);
		if (parent_needs_layout) {
			parent_needs_layout = false;
			getParent().doLayout();
		}
	}

	public Dimension getPreferredSize() {
		return size;
	}

	public void mouseMoved(MouseEvent evt) {
		int x = evt.getX() + gra.min_x;
		int y = evt.getY() + gra.min_y;

		Vertex v2=gra.vertexAt(x,y);
		Graphics g=getGraphics();
		g.translate(-gra.min_x,-gra.min_y);
		if (highlighted!=null) {
			highlighted.drawBox(g,Color.lightGray);
			highlighted=null;
		}
		if (v2!=v) {
			if (v!=null) v.removeButtons(g);
			if (v2!=null) v2.drawButtons(g);
			v=v2;
		}
	}

	public void mouseDragged(MouseEvent evt) {}

	/*****************************************************************/
	/* This method is called if successor / predecessor nodes (whose */
	/* numbers are stored in Vector c) of a certain node should be   */
        /* displayed again                                               */
	/*****************************************************************/

	void uncollapse(Vector c) {
		collapsed.removeElement(c);
		collapseNodes();
	}

	/*****************************************************************/
	/* This method is called by class TreeBrowser when directories   */
	/* are collapsed / uncollapsed by the user                       */
	/*****************************************************************/

	public void collapseDir(Vector v) {
		collapsedDirs=v;

		collapseNodes();
	}

	/*****************************************************************/
	/*                      Inflate node again                       */
	/*****************************************************************/

	public void inflateNode(Vector c) {
		Enumeration e1;

		e1=collapsedDirs.elements();
		while (e1.hasMoreElements()) {
			Directory d=(Directory)(e1.nextElement());
			if (d.collapsed==c) {
				tb.selectNode(d.getNode());
				return;
			}
		}

		collapsed.removeElement(c);
		e1=gra2.getVertices();
		while (e1.hasMoreElements()) {
			Vertex vx=(Vertex)(e1.nextElement());
			if (vx.getUp()==c) vx.setUp(null);
			if (vx.getDown()==c) vx.setDown(null);
		}

		collapseNodes();
		relayout();
	}

	public void relayout() {
		browser.showWaitMessage();
		highlighted=null;
		gra.layout(getGraphics());
		v=null;
		parent_needs_layout = true;
		update(getGraphics());
		browser.showReadyMessage();
	}

	public void focusToVertex(int n) {
		Vertex vx=gra.getVertexByNum(n);
		if (vx!=null) {
			ScrollPane scrollp = (ScrollPane)(getParent());
			Dimension vpsize = scrollp.getViewportSize();

                        int x = vx.getX()-gra.min_x;
                        int y = vx.getY()-gra.min_y;
			int offset_x = Math.min(scrollp.getHAdjustable().getMaximum(),
				Math.max(0,x-vpsize.width/2));
			int offset_y = Math.min(scrollp.getVAdjustable().getMaximum(),
				Math.max(0,y-vpsize.height/2));

			Graphics g=getGraphics();
			g.translate(-gra.min_x,-gra.min_y);
			if (highlighted!=null) highlighted.drawBox(g,Color.lightGray);
			vx.drawBox(g,Color.white);
			highlighted=vx;
			scrollp.setScrollPosition(offset_x, offset_y);
		}
	}

	/*****************************************************************/
	/*             Create new graph with collapsed nodes             */
	/*****************************************************************/

	public void collapseNodes() {
		Enumeration e1=collapsed.elements();
		gra=(Graph)(gra2.clone());

		while (e1.hasMoreElements()) {
			Vector v1=(Vector)(e1.nextElement());
			Vector v2=gra.decode(v1);
			if (!v2.isEmpty()) gra.collapse(v2,"[. . . .]",v1);
		}

		e1=collapsedDirs.elements();

		while (e1.hasMoreElements()) {
			Directory d=(Directory)(e1.nextElement());
			Vector v=gra.decode(d.getCollapsed());
			if (!v.isEmpty())
				gra.collapse(v,"["+d.getName()+"]",d.getCollapsed());
		}
	}

	public void mouseClicked(MouseEvent evt) {
		Vector code = null;
		Vertex v2;
		int x = evt.getX() + gra.min_x;
		int y = evt.getY() + gra.min_y;

		if (v!=null) {
			int num=v.getNumber();
			v2=gra2.getVertexByNum(num);
			if (v.leftButton(x,y)) {
				if (v.getUp()!=null) {
					code=v.getUp();
					v2.setUp(null);
					v=null;
					uncollapse(code);
					relayout();
					focusToVertex(num);
				} else {
					Vector vs=v2.getPreds();
					code=gra2.encode(vs);
					v.setUp(code);v2.setUp(code);
					v=null;
					collapsed.insertElementAt(code,0);
					collapseNodes();
					relayout();
					focusToVertex(num);
				}
			} else if (v.rightButton(x,y)) {
				if (v.getDown()!=null) {
					code=v.getDown();
					v2.setDown(null);
					v=null;
					uncollapse(code);
					relayout();
					focusToVertex(num);
				} else {
					Vector vs=v2.getSuccs();
					code=gra2.encode(vs);
					v.setDown(code);v2.setDown(code);
					v=null;
					collapsed.insertElementAt(code,0);
					collapseNodes();
					relayout();
					focusToVertex(num);
				}
			} else if (v.getInflate()!=null) {
				inflateNode(v.getInflate());
				v=null;
			} else {
				if (evt.getWhen()-timestamp < 400 && !(v.getPath().equals("")))
					browser.viewFile(v.getPath());
				timestamp=evt.getWhen();
			}
		}
	}

	public void mouseExited(MouseEvent evt) {
		Graphics g=getGraphics();
		g.translate(-gra.min_x,-gra.min_y);
		if (highlighted!=null) {
			highlighted.drawBox(g,Color.lightGray);
			highlighted=null;
		}
		if (v!=null) v.removeButtons(g);
		v=null;
	}

	public void mouseEntered(MouseEvent evt) {}

	public void mousePressed(MouseEvent evt) {}

	public void mouseReleased(MouseEvent evt) {}
}
