/***************************************************************************
  Title:      GraphBrowser/GraphView.java
  ID:         $Id$
  Author:     Stefan Berghofer, TU Muenchen
  Copyright   1997  TU Muenchen

  This class defines the window in which the graph is displayed. It
  contains methods for handling events such as collapsing / uncollapsing
  nodes of the graph.
***************************************************************************/

package GraphBrowser;

import java.awt.*;
import java.io.*;
import java.util.*;
import awtUtilities.*;

public class GraphView extends ScrollCanvas {
	Graph gra,gra2;
	GraphBrowser parent;
	Vertex v=null;
	Vector collapsed=new Vector(10,10);
	Vector collapsedDirs=new Vector(10,10);
	TreeBrowser tb;
	long timestamp;
	Vertex highlighted=null;

	public void setTreeBrowser(TreeBrowser br) {
		tb=br;
	}

	public GraphBrowser getBrowser() { return parent; }

	public Graph getGraph() { return gra; }

	public Graph getOriginalGraph() { return gra2; }

	public GraphView(Graph gr,GraphBrowser br) {
		gra2=gr;
		parent=br;
		gra=(Graph)(gra2.clone());
	}

	public void PS(String fname,boolean printable) throws IOException {
		gra.PS(fname,printable);
	}

	public void paintCanvas(Graphics g)
	{
		set_size(gra.max_x-gra.min_x,gra.max_y-gra.min_y);
		gra.draw(g);
	}

	public boolean mouseMove(Event evt,int x,int y) {
		x+=gra.min_x;
		y+=gra.min_y;

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
		return true;
	}

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
		parent.showWaitMessage();
		highlighted=null;
		gra.layout(getGraphics());
		v=null;
		update(getGraphics());
		parent.showReadyMessage();
	}

	public void focusToVertex(int n) {
		Vertex vx=gra.getVertexByNum(n);
		if (vx!=null) {
			focus_to(vx.getX()-gra.min_x,vx.getY()-gra.min_y);
			highlighted=vx;
			Graphics g=getGraphics();
			g.translate(-gra.min_x,-gra.min_y);
			vx.drawBox(g,Color.white);
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

	public boolean mouseDown(Event evt,int x,int y) {
		Vector code=null;
		Vertex v2;
		x+=gra.min_x;
		y+=gra.min_y;

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
				if (evt.when-timestamp < 400 && !(v.getPath().equals("")))
					parent.viewFile(v.getPath());
				timestamp=evt.when;
			}
		}
		return true;
	}

	public boolean mouseExit(Event evt,int x,int y) {
		Graphics g=getGraphics();
		g.translate(-gra.min_x,-gra.min_y);
		if (highlighted!=null) {
			highlighted.drawBox(g,Color.lightGray);
			highlighted=null;
		}
		if (v!=null) v.removeButtons(g);
		v=null;
		return true;
	}
}
