/***************************************************************************
  Title:      GraphBrowser/Region.java
  ID:         $Id$
  Author:     Stefan Berghofer, TU Muenchen
  Copyright   1997  TU Muenchen

  This is an auxiliary class which is used by the layout algorithm when
  calculating coordinates with the "pendulum method". A "region" is a
  group of nodes which "stick together".
***************************************************************************/

package GraphBrowser;

import java.util.*;

class Region {
	Vector vertices=new Vector(10,10);
	Graph gra;

	public Region(Graph g) { gra=g; }

	public void addVertex(Vertex v) {
		vertices.addElement(v);
	}

	public Enumeration getVertices() {
		return vertices.elements();
	}

	public int pred_deflection() {
		float d1=0;
		int n=0;
		Enumeration e1=vertices.elements();
		while (e1.hasMoreElements()) {
			float d2=0;
			int p=0;
			n++;
			Vertex v=(Vertex)(e1.nextElement());
			Enumeration e2=v.getParents();
			while (e2.hasMoreElements()) {
				p++;
				d2+=((Vertex)(e2.nextElement())).getX()-v.getX();
			}
			if (p>0) d1+=d2/p;
		}
		return (int)(Math.round(d1/n));
	}

	public int succ_deflection() {
		float d1=0;
		int n=0;
		Enumeration e1=vertices.elements();
		while (e1.hasMoreElements()) {
			float d2=0;
			int p=0;
			n++;
			Vertex v=(Vertex)(e1.nextElement());
			Enumeration e2=v.getChildren();
			while (e2.hasMoreElements()) {
				p++;
				d2+=((Vertex)(e2.nextElement())).getX()-v.getX();
			}
			if (p>0) d1+=d2/p;
		}
		return (int)(Math.round(d1/n));
	}

	public void move(int x) {
		Enumeration e1=vertices.elements();
		while (e1.hasMoreElements()) {
			Vertex v=(Vertex)(e1.nextElement());
			v.setX(v.getX()+x);
		}
	}

	public void combine(Region r2) {
		Enumeration e1=r2.getVertices();
		while (e1.hasMoreElements()) addVertex((Vertex)(e1.nextElement()));
	}

	public int spaceBetween(Region r2) {
		return ((Vertex)(r2.getVertices().nextElement())).leftX()-
			((Vertex)(vertices.lastElement())).rightX()-
			gra.box_hspace+gra.box_width;
	}

	public boolean touching(Region r2) {
		return spaceBetween(r2)==0;
	}
}
