/***************************************************************************
  Title:      GraphBrowser/Graph.java
  ID:         $Id$
  Author:     Stefan Berghofer, TU Muenchen
  Copyright   1997  TU Muenchen

  This class contains the core of the layout algorithm and methods for
  drawing and PostScript output.
***************************************************************************/

package GraphBrowser;

import java.util.*;
import java.awt.*;
import java.io.*;

class ParseError extends Exception {
	public ParseError(String s) { super(s); }
}

public class Graph {
	/**** parameters for layout ****/

	public int box_height=0;
	public int box_height2;
	public int box_width;
	public int box_width2;
	public int box_hspace;

	Vector vertices=new Vector(10,10);
	Vector splines=new Vector(10,10);
	Vector numEdges=new Vector(10,10);
	Vertex []vertices2;

	public int min_x=0,min_y=0,max_x=10,max_y=10;

	/********************************************************************/
	/*                         clone graph object                       */
	/********************************************************************/

	public Object clone() {
		Graph gr=new Graph();
		Enumeration e1;
		int i;

		gr.splines=(Vector)(splines.clone());

		e1=vertices.elements();
		while (e1.hasMoreElements())
			gr.addVertex((Vertex)(((Vertex)(e1.nextElement())).clone()));

		for (i=0;i<vertices.size();i++) {
			Vertex vx1=(Vertex)(gr.vertices.elementAt(i));
			e1=((Vertex)(vertices.elementAt(i))).getChildren();
			while (e1.hasMoreElements()) {
				Vertex vx2=(Vertex)(gr.vertices.elementAt(vertices.indexOf(e1.nextElement())));
				vx1.addChild(vx2);
			}
		}

		gr.vertices2 = new Vertex[vertices.size()];
		gr.vertices.copyInto(gr.vertices2);

		gr.min_x=min_x;gr.max_x=max_x;
		gr.min_y=min_y;gr.max_y=max_y;

		return gr;
	}

	Graph() {}

	/********************************************************************/
	/*                      Read graph from stream                      */
	/********************************************************************/

	public Graph(InputStream s,TreeNode tn) throws IOException, ParseError {
		StreamTokenizer tok=new StreamTokenizer(s);
		String name,dir,vertexID;
		Vertex ve1,ve2;
		boolean children,unfoldDir;
		int index=0;

		tok.nextToken();
		while (tok.ttype!=StreamTokenizer.TT_EOF) {
			if (tok.ttype!=StreamTokenizer.TT_WORD && tok.ttype!='"')
				throw new ParseError("expected: vertex name\nfound   : "+tok.toString());
			name=tok.sval;
                        tok.nextToken();
			if (tok.ttype!=StreamTokenizer.TT_WORD && tok.ttype!='"')
				throw new ParseError("expected: vertex identifier\nfound   : "+tok.toString());
			vertexID=tok.sval;
			tok.nextToken();
			if (tok.ttype!=StreamTokenizer.TT_WORD && tok.ttype!='"')
				throw new ParseError("expected: directory name\nfound   : "+tok.toString());
			dir=tok.sval;
			tok.nextToken();
			if (tok.ttype=='+') {
				unfoldDir=true;
				tok.nextToken();
			} else
				unfoldDir=false;
			if (tok.ttype!=StreamTokenizer.TT_WORD && tok.ttype!='"')
				throw new ParseError("expected: path name\nfound   : "+tok.toString());
			ve1=findVertex(vertexID);
			if (ve1==null) {
				ve1=new NormalVertex("");
				ve1.setID(vertexID);
				ve1.setNumber(index++);
				addVertex(ve1);
			}
			ve1.setPath(tok.sval);
			ve1.setDir(dir);
                        ve1.setLabel(name);
			tn.insertNode(name,dir,tok.sval,ve1.getNumber(),unfoldDir);
			tok.nextToken();
			if (tok.ttype=='<') {
				children=true;
				tok.nextToken();
			} else if (tok.ttype=='>') {
					children=false;
					tok.nextToken();
			} else children=true;
			while (tok.ttype!=';') {
				if (tok.ttype!=StreamTokenizer.TT_WORD && tok.ttype!='"')
					throw new ParseError("expected: child vertex identifier or ';'\nfound   : "+tok.toString());				
				ve2=findVertex(tok.sval);
				if (ve2==null) {
					ve2=new NormalVertex("");
					ve2.setID(tok.sval);
					ve2.setNumber(index++);
					addVertex(ve2);
				}
				if (children)
					ve1.addChild(ve2);
				else
					ve1.addParent(ve2);
				tok.nextToken();
			}
			tok.nextToken();
		}
		vertices2 = new Vertex[vertices.size()];
		vertices.copyInto(vertices2);
	}
	
	/*** Find vertex with identifier vertexID ***/

	public Vertex findVertex(String vertexID) {
		Enumeration e1=vertices.elements();
		Vertex v1;

		while (e1.hasMoreElements()) {
			v1=(Vertex)(e1.nextElement());
			if ((v1.getID()).equals(vertexID))
				return v1;
		}
		return null;
	}
		 
	public void addVertex(Vertex v) {
		vertices.addElement(v);
		v.setGraph(this);
	}

	public void removeVertex(Vertex v) {
		vertices.removeElement(v);
	}

	public Enumeration getVertices() {
		return vertices.elements();
	}

	/********************************************************************/
	/*                          graph layout                            */
	/********************************************************************/

	public void layout(Graphics g) {
		splines.removeAllElements();
		hasseDiagram();
		Vector layers=min_crossings(insert_dummies((Vector)(sort().elementAt(0))));
		setParameters(g);
		init_coordinates(layers);
		pendulum(layers);
		rubberband(layers);
		calcSplines(layers);
		calcBoundingBox();
	}

	/********************************************************************/
	/*                      set layout parameters                       */
	/********************************************************************/

	public void setParameters(Graphics g) {
		Enumeration e1=vertices.elements();
		int h,w;
		h=w=Integer.MIN_VALUE;

		while (e1.hasMoreElements()) {
			Dimension dim=((Vertex)(e1.nextElement())).getLabelSize(g);
			h=Math.max(h,dim.height);
			w=Math.max(w,dim.width);
		}
		box_height=h+4;
		box_height2=box_height/2;
		box_width=w+8;
		box_width2=box_width/2;
		box_hspace=box_width+20;
	}

	/********************************************************************/
	/*                       topological sorting                        */
	/********************************************************************/

	public Vector sort() {
		Vector todo=(Vector)(vertices.clone());
		Vector layers=new Vector(10,10);
		Vector todo2;
		Enumeration e1,e2;
		Vertex v,v2;

		e1=vertices.elements();
		while (e1.hasMoreElements())
			((Vertex)(e1.nextElement())).setDegree(0);

		e1=vertices.elements();
		while (e1.hasMoreElements()) {
			v=(Vertex)(e1.nextElement());
			e2=v.getChildren();
			while (e2.hasMoreElements()) {
				v2=(Vertex)(e2.nextElement());
				todo.removeElement(v2);
				v2.setDegree(1+v2.getDegree());
			}
		}
		while (!todo.isEmpty()) {
			layers.addElement(todo);
			todo2=new Vector(10,10);
			e1=todo.elements();
			while (e1.hasMoreElements()) {
				e2=((Vertex)(e1.nextElement())).getChildren();
				while (e2.hasMoreElements()) {
					v=(Vertex)(e2.nextElement());
					v.setDegree(v.getDegree()-1);
					if (v.getDegree()==0) {
						todo2.addElement(v);
						v.setDegree(layers.size());
					}
				}
			}
			todo=todo2;
		}
		return layers;
	}

	/********************************************************************/
	/*                      compute hasse diagram                       */
	/********************************************************************/

	public void hasseDiagram() {
		Enumeration e1,e2;
		Vertex vx1,vx2;

		/** construct adjacence matrix **/

		int vs=vertices.size();
		boolean adj[][]=new boolean[vs][vs];
		boolean adj2[][]=new boolean[vs][vs];
		int i,j,k;

		e1=getVertices();
		for (i=0;i<vs;i++) {
			vx1=(Vertex)(e1.nextElement());
			e2=vx1.getChildren();
			while (e2.hasMoreElements()) {
				vx2=(Vertex)(e2.nextElement());
				j=vertices.indexOf(vx2);
				adj[i][j]=true;
				adj2[i][j]=true;
			}
		}

		/** compute transitive closure R+ **/

		for (k=0;k<vs;k++)
			for (i=0;i<vs;i++)
				if (adj[i][k])
					for (j=0;j<vs;j++)
						adj[i][j] = adj[i][j] || adj[k][j];

		/** compute R \ (R+)^2 **/

		for (i=0;i<vs;i++)
			for (j=0;j<vs;j++)
				if (adj2[i][j]) {
					vx1=(Vertex)(vertices.elementAt(i));
					vx2=(Vertex)(vertices.elementAt(j));
					for (k=0;k<vs;k++)
						if (adj[i][k] && adj[k][j]) {
							vx1.removeChild(vx2);
							break;
						}
				}
	}
				
	/********************************************************************/
	/*                      insert dummy vertices                       */
	/********************************************************************/

	public Vector insert_dummies(Vector v) {
		Vector layers2=new Vector(10,10);
		int n_edges;

		do {
			Enumeration e1=v.elements(),e2;
			Vector next=new Vector(10,10);

			layers2.addElement(v);
			n_edges=0;
			while (e1.hasMoreElements()) {
				Vertex v1=(Vertex)(e1.nextElement());
				e2=v1.getChildren();
				while (e2.hasMoreElements()) {
					n_edges++;
					Vertex v2=(Vertex)(e2.nextElement());
					if (v2.getDegree()!=v1.getDegree()+1) {
						Vertex v3=new DummyVertex();
						v3.addChild(v2);
						v3.setDegree(v1.getDegree()+1);
						v1.removeChild(v2);
						v1.addChild(v3);
						next.addElement(v3);
						addVertex(v3);
					} else if (next.indexOf(v2)<0) next.addElement(v2);
				}
			}
			v=next;
			numEdges.addElement(new Integer(n_edges));
		} while (!v.isEmpty());
		return layers2;
	}

	/********************************************************************/
	/*                     calculation of crossings                     */
	/********************************************************************/

	public int count_crossings(Vector layers,int oldcr) {
		int i,j,y1,y2,cr=0,l;
		for (l=0;l<layers.size()-1;l++) {
			Vector v1=(Vector)(layers.elementAt(l));
			for (i=0;i<v1.size();i++) {
				Enumeration e2=((Vertex)(v1.elementAt(i))).getChildren();
				while (e2.hasMoreElements()) {
					y1=((Vector)(layers.elementAt(l+1))).indexOf(e2.nextElement());
					for (j=0;j<i;j++) {
						Enumeration e3=((Vertex)(v1.elementAt(j))).getChildren();
						while (e3.hasMoreElements()) {
							y2=((Vector)(layers.elementAt(l+1))).indexOf(e3.nextElement());
							if (y1<y2) {
								cr++;
								if (cr>=oldcr) return cr;
							}
						}
					}
				}
			}
		}
		return cr;
	}

	/********************************************************************/
	/* calculation of crossings where vertices vx1 and vx2 are involved */
	/* vx1 and vx2 must be in same layer and vx1 is left from vx2       */
	/********************************************************************/

	public int count_crossings_2(Vector layers,Vertex vx1,Vertex vx2,int oldcr) {
		int i,cr=0,l=vx1.getDegree();
		Vertex va,vb;
		Vector layer;
		Enumeration e1,e2;

		if (l>0) {
			layer=(Vector)(layers.elementAt(l-1));
			e1=vx1.getParents();
			while (e1.hasMoreElements()) {
				va=(Vertex)(e1.nextElement());
				i=layer.indexOf(va);
				e2=vx2.getParents();
				while (e2.hasMoreElements()) {
					vb=(Vertex)(e2.nextElement());
					if (layer.indexOf(vb)<i) {
						cr++;
						if (cr>=oldcr) return cr;
					}
				}
			}
		}
		if (l<layers.size()-1) {
			layer=(Vector)(layers.elementAt(l+1));
			e1=vx1.getChildren();
			while (e1.hasMoreElements()) {
				va=(Vertex)(e1.nextElement());
				i=layer.indexOf(va);
				e2=vx2.getChildren();
				while (e2.hasMoreElements()) {
					vb=(Vertex)(e2.nextElement());
					if (layer.indexOf(vb)<i) {
						cr++;
						if (cr>=oldcr) return cr;
					}
				}
			}
		}
		return cr;
	}

	/********************************************************************/
	/*       reduction of crossings by exchanging adjacent vertices     */
	/********************************************************************/

	public void exchangeVertices(Vector layers,int oldcr) {
		int i,l,c1,c2;
		Vertex vx1,vx2;
		Vector v1;

		for (l=0;l<layers.size();l++) {
			v1=(Vector)(layers.elementAt(l));
			for (i=0;i<v1.size()-1;i++) {
				vx1=(Vertex)(v1.elementAt(i));
				vx2=(Vertex)(v1.elementAt(i+1));
				c1=count_crossings_2(layers,vx1,vx2,oldcr);
				c2=count_crossings_2(layers,vx2,vx1,c1);
				if (c2<c1) {
					v1.setElementAt(vx2,i);
					v1.setElementAt(vx1,i+1);
				}
			}
		}
	}

	/********************************************************************/
	/*                    minimization of crossings                     */
	/********************************************************************/

	public Vector min_crossings(Vector layers) {
		int n,i,l,k,z=0,cr2,cr=count_crossings(layers,Integer.MAX_VALUE);
		boolean topdown=true,first=true;
		Enumeration e1,e2;
		Vector v1,v2,layers2=null,best=layers;
		Vertex vx1,vx2;
		n=0;
		while (n<3 && cr>0) {
			if (topdown) {
				/** top-down-traversal **/

				layers2=new Vector(10,10);
				for (l=0;l<layers.size();l++) {
					v1=(Vector)(layers.elementAt(l));
					if (l==0) layers2.addElement(v1.clone());
					else {
						v2=new Vector(10,10);
						layers2.addElement(v2);
						e1=v1.elements();
						while (e1.hasMoreElements()) {
							vx1=(Vertex)(e1.nextElement());
							k=0;z=0;
							e2=vx1.getParents();
							while (e2.hasMoreElements()) {
								k+=((Vector)(layers2.elementAt(l-1))).indexOf(e2.nextElement());
								z++;
							}
							if (z>0)
								vx1.setWeight(((double)(k))/z);
							else if (first)
								vx1.setWeight(Double.MAX_VALUE);
							for (i=0;i<v2.size();i++)
								if (vx1.getWeight()<((Vertex)(v2.elementAt(i))).getWeight()) break;
							if (i==v2.size()) v2.addElement(vx1);
							else v2.insertElementAt(vx1,i);
						}
					}
				}
			} else {
				/** bottom-up-traversal **/

				layers2=new Vector(10,10);
				for (l=layers.size()-1;l>=0;l--) {
					v1=(Vector)(layers.elementAt(l));
					if (l==layers.size()-1) layers2.addElement(v1.clone());
					else {
						v2=new Vector(10,10);
						layers2.insertElementAt(v2,0);
						e1=v1.elements();
						while (e1.hasMoreElements()) {
							vx1=(Vertex)(e1.nextElement());
							k=0;z=0;
							e2=vx1.getChildren();
							while (e2.hasMoreElements()) {
								k+=((Vector)(layers2.elementAt(1))).indexOf(e2.nextElement());
								z++;
							}
							if (z>0)
								vx1.setWeight(((double)(k))/z);
							else if (first)
								vx1.setWeight(Double.MAX_VALUE);
							for (i=0;i<v2.size();i++)
								if (vx1.getWeight()<((Vertex)(v2.elementAt(i))).getWeight()) break;
							if (i==v2.size()) v2.addElement(vx1);
							else v2.insertElementAt(vx1,i);
						}
					}
				}
			}
			//exchangeVertices(layers2,cr);
			topdown=!topdown;
			first=false;
			layers=layers2;

			cr2=count_crossings(layers2,cr);
			if (cr2<cr) {
				best=layers2;
				cr=cr2;					
			} else n++;
		}

		while (true) {
			exchangeVertices(best,cr);
			cr2=count_crossings(best,cr);
			if (cr2<cr)
				cr=cr2;
			else
				break;
		}

		return best;
	}

	/********************************************************************/
	/*                   set initial coordinates                        */
	/********************************************************************/

	public void init_coordinates(Vector layers) {
		int y=0;
		Enumeration e1=layers.elements();
		Enumeration e3=numEdges.elements();
		while (e1.hasMoreElements()) {
			Vector v1=(Vector)(e1.nextElement());
			Enumeration e2=v1.elements();
			int x=box_width2;
			while (e2.hasMoreElements()) {
				Vertex ve=(Vertex)(e2.nextElement());
				ve.setX(x);
				ve.setY(y);
				x+=box_hspace;
			}
			y+=box_height+Math.max(35,7*(((Integer)(e3.nextElement())).intValue()));
		}
	}

	/********************************************************************/
	/*                       pendulum method                            */
	/********************************************************************/

	public void pendulum(Vector layers) {
		Vector layers2=new Vector(10,10);
		Enumeration e1=layers.elements(),e2;
		int i,j,d1,d2,k,offset,dsum;
		Region r1,r2;
		boolean change;

		while (e1.hasMoreElements()) {
			e2=((Vector)(e1.nextElement())).elements();
			Vector layer=new Vector(10,10);
			layers2.addElement(layer);
			while (e2.hasMoreElements()) {
				Region r=new Region(this);
				r.addVertex((Vertex)(e2.nextElement()));
				layer.addElement(r);
			}
		}
		for (k=0;k<10;k++) {
			dsum=0;
			for (j=1;j<layers2.size();j++) {
				Vector l=(Vector)(layers2.elementAt(j));
				if (l.size()>=2) {
					do {
						change=false;
						d1=((Region)(l.firstElement())).pred_deflection();
						for (i=0;i<l.size()-1;i++) {
							r1=(Region)(l.elementAt(i));
							r2=(Region)(l.elementAt(i+1));
							d2=r2.pred_deflection();
							if (r1.touching(r2) && (d1 <= 0 && d2 < d1 ||
								d2 > 0 && d1 > d2 || d1 > 0 && d2 < 0)) {
								r1.combine(r2);
								l.removeElement(r2);
								change=true;
								d2=r1.pred_deflection();
							}
							d1=d2;
						}
					} while (change);
				}
				for (i=0;i<l.size();i++) {
					r1=(Region)(l.elementAt(i));
					d1=r1.pred_deflection();
					offset=d1;
					if (d1<0 && i>0) offset=-Math.min(
						((Region)(l.elementAt(i-1))).spaceBetween(r1),-d1);
					if (d1>=0 && i<l.size()-1) offset=Math.min(
						r1.spaceBetween((Region)(l.elementAt(i+1))),d1);
					r1.move(offset);
					dsum+=Math.abs(d1);
				}		
			}
			if (dsum==0) break;
		}
	}		

	/********************************************************************/
	/*                      rubberband method                           */
	/********************************************************************/

	public void rubberband(Vector layers) {
		Enumeration e1,e2;
		int i,n,k,d,d2;
		Vector v;
		Vertex vx;

		for (k=0;k<10;k++) {
			e1=layers.elements();
			while (e1.hasMoreElements()) {
				v=(Vector)(e1.nextElement());
				for (i=0;i<v.size();i++) {
					n=0;d=0;
					vx=(Vertex)(v.elementAt(i));
					e2=vx.getChildren();
					while (e2.hasMoreElements()) {
						d+=((Vertex)(e2.nextElement())).getX()-vx.getX();
						n++;
					}
					e2=vx.getParents();
					while (e2.hasMoreElements()) {
						d+=((Vertex)(e2.nextElement())).getX()-vx.getX();
						n++;
					}
					d2=(n!=0?d/n:0);

					if (d<0 && (i==0 || ((Vertex)(v.elementAt(i-1))).rightX()+box_hspace-box_width < vx.leftX()+d2) ||
						d>0 && (i==v.size()-1 || ((Vertex)(v.elementAt(i+1))).leftX()-box_hspace+box_width > vx.rightX()+d2))
						vx.setX(vx.getX()+d2);
				}
			}
		}
	}

	/**** Intersection point of two lines (auxiliary function for calcSplines)   ****/
	/**** Calculate intersection point of line which is parallel to line (p1,p2) ****/
	/**** and leads through p5, with line (p3,p4)                                ****/

	Point intersect(Point p1,Point p2,Point p3,Point p4,Point p5) {
		float x=0,y=0,s1=0,s2=0;

		if (p1.x!=p2.x)
			s1=((float)(p2.y-p1.y))/(p2.x-p1.x);
		if (p3.x!=p4.x)
			s2=((float)(p4.y-p3.y))/(p4.x-p3.x);
		if (p1.x==p2.x) {
			x=p5.x;
			y=s2*(p5.x-p3.x)+p3.y;
		} else if (p3.x==p4.x) {
			x=p3.x;
			y=s1*(p3.x-p5.x)+p5.y;
		} else {
			x=(p5.x*s1-p3.x*s2+p3.y-p5.y)/(s1-s2);
			y=s2*(x-p3.x)+p3.y;
		}
		return new Point(Math.round(x),Math.round(y));
	}

	/**** Calculate control points (auxiliary function for calcSplines) ****/

	Points calcPoint(Point p1,Point p2,Point p3,int lboxx,int rboxx,int boxy) {

		/*** Points p1 , p2 , p3 define a triangle which encloses the spline.  ***/
		/*** Check if adjacent boxes (specified by lboxx,rboxx and boxy)       ***/
		/*** collide with the spline. In this case p1 and p3 are shifted by an ***/
		/*** appropriate offset before they are returned                       ***/

		int xh1,xh2,bx=0,by=0;
		boolean pt1 = boxy >= p1.y && boxy <= p3.y || boxy >= p3.y && boxy <= p1.y;
		boolean pt2 = boxy+box_height >= p1.y && boxy+box_height <= p3.y ||
                              boxy+box_height >= p3.y && boxy+box_height <= p1.y;
		boolean move = false;
		Point b;

		xh1 = p1.x+(boxy-p1.y)*(p3.x-p1.x)/(p3.y-p1.y);
		xh2 = p1.x+(boxy+box_height-p1.y)*(p3.x-p1.x)/(p3.y-p1.y);

		if (xh1 <= lboxx && pt1 && xh2 <= lboxx && pt2) {
			move = true;
			bx = lboxx;
			by = boxy + (xh1 < xh2 ? 0 : box_height ) ;
		} else if (xh1 >= rboxx && pt1 && xh2 >= rboxx && pt2) {
			move = true;
			bx = rboxx;
			by = boxy + (xh1 > xh2 ? 0 : box_height ) ;
		} else if ( (xh1 <= lboxx || xh1 >= rboxx) && pt1) {
			move = true;
			bx = (xh1 <= lboxx ? lboxx : rboxx ) ;
			by = boxy;
		} else if ( (xh2 <= lboxx || xh2 >= rboxx) && pt2) {
			move = true;
			bx = (xh2 <= lboxx ? lboxx : rboxx ) ;
			by = boxy+box_height;
		}
		b=new Point(bx,by);
		if (move) return new Points(intersect(p1,p3,p1,p2,b),intersect(p1,p3,p2,p3,b));
		else return new Points(p1,p3);
	}

	/********************************************************************/
	/*                        calculate splines                         */
	/********************************************************************/

	public void calcSplines(Vector layers) {
		Enumeration e2,e1=vertices.elements();
		Vertex vx1,vx2,vx3;
		Vector pos,layer;
		int x1,y1,x2,y2,x3,y3,xh,k,leftx,rightx,spc;

		while (e1.hasMoreElements()) {
			vx1=(Vertex)(e1.nextElement());
			if (!vx1.isDummy()) {
				e2=vx1.getChildren();
				while (e2.hasMoreElements()) {
					vx2=(Vertex)(e2.nextElement());
					if (vx2.isDummy()) {
						vx3=vx2;
						/**** convert edge to spline ****/
						pos=new Vector(10,10);
						x1=vx1.getX();
						y1=vx1.getY()+box_height;

						do {
							/*** calculate position of control points ***/
							x2=vx2.getX();
							y2=vx2.getY();
							layer=(Vector)(layers.elementAt(vx2.getDegree()));
							k=layer.indexOf(vx2);
							vx2=(Vertex)((vx2.getChildren()).nextElement());
							x3=vx2.getX();
							y3=vx2.getY();
							// spc=(box_hspace-box_width)/3;
							// spc=box_height*3/4;
							spc=0;
							leftx = k==0 /* || ((Vertex)(layer.elementAt(k-1))).isDummy() */ ?
								Integer.MIN_VALUE:
								((Vertex)(layer.elementAt(k-1))).rightX()+spc;
							rightx = k==layer.size()-1 /* || ((Vertex)(layer.elementAt(k+1))).isDummy() */ ?
								Integer.MAX_VALUE:
								((Vertex)(layer.elementAt(k+1))).leftX()-spc;
							xh=x2+box_height*(x3-x2)/(y3-y2);
							if (!(x2<=x3 && xh>=rightx || x2>x3 && xh<=leftx)) {
								/* top control point */
								pos.addElement(new Integer(1));
								y1=y2;
							} else {
								xh=x1+(y2-y1)*(x2-x1)/(y2+box_height-y1);
								if (!(x2<=x1 && xh>=rightx || x2>x1 && xh<=leftx))
									/* bottom control point */
									pos.addElement(new Integer(2));
								else
									/* two control points needed */
									pos.addElement(new Integer(3));
								y1=y2+box_height;
							}
							x1=x2;
						} while (vx2.isDummy());
						pos.addElement(new Integer(1));

						/**** calculate triangles ****/
						vx2=vx3;

						int pos1,pos2,i=0;
						Vector pts=new Vector(10,10);
						int lboxx,rboxx,boxy;

						x1=vx1.getX();
						y1=vx1.getY()+box_height;
						pts.addElement(new Point(x1,y1)); /** edge starting point **/
						do {
							x2=vx2.getX();
							y2=vx2.getY();
							pos1=((Integer)(pos.elementAt(i))).intValue();
							pos2=((Integer)(pos.elementAt(i+1))).intValue();
							i++;
							layer=(Vector)(layers.elementAt(vx2.getDegree()));
							k=layer.indexOf(vx2);
							boxy=vx2.getY();
							vx2=(Vertex)((vx2.getChildren()).nextElement());
							x3=vx2.getX();
							y3=vx2.getY();
							if (pos1==2) y2+=box_height;
							if (pos2==2) y3+=box_height;

							lboxx = (k==0 /* || ((Vertex)(layer.elementAt(k-1))).isDummy() */ ) ?
								Integer.MIN_VALUE :
								((Vertex)(layer.elementAt(k-1))).rightX();

							rboxx = (k==layer.size()-1 /* || ((Vertex)(layer.elementAt(k+1))).isDummy() */ ) ?
								Integer.MAX_VALUE :
								((Vertex)(layer.elementAt(k+1))).leftX();

							Point p1,p2,p3;
							Points ps;

							p1 = new Point((x1+x2)/2,(y1+y2)/2);

							if (pos1<=2) {
								/** one control point **/
								p2 = new Point(x2,y2);
								ps = calcPoint(p1,p2,new Point((x2+x3)/2,(y2+y3)/2),lboxx,rboxx,boxy);
								pts.addElement(ps.p);
								pts.addElement(p2);
								pts.addElement(ps.q);
							} else {
								/** two control points **/
								p2 = new Point(x2,y2-box_height);
								p3 = new Point(x2,y2+box_height2);
								ps = calcPoint(p1,p2,p3,lboxx,rboxx,boxy);
								pts.addElement(ps.p);
								pts.addElement(p2);
								pts.addElement(ps.q);
								p2 = new Point(x2,y2+box_height*2);
								ps = calcPoint(p3,p2,new Point((p2.x+x3)/2,(p2.y+y3)/2),
								               lboxx,rboxx,boxy);
								pts.addElement(ps.p);
								pts.addElement(p2);
								pts.addElement(ps.q);
							}
							x1=p2.x;
							y1=p2.y;
						} while (vx2.isDummy());

						pts.addElement(new Point(vx2.getX(),vx2.getY())); /** edge end point **/
						splines.addElement(new Spline(pts));
					}
				}
			}
		}
	}

	/********************************************************************/
	/*                      calculate bounding box                      */
	/********************************************************************/

	public void calcBoundingBox() {
		min_y=min_x=Integer.MAX_VALUE;
		max_y=max_x=Integer.MIN_VALUE;

		Enumeration e1=vertices.elements();
		Vertex v;

		while (e1.hasMoreElements()) {
			v=(Vertex)(e1.nextElement());
			min_x=Math.min(min_x,v.leftX());
			max_x=Math.max(max_x,v.rightX());
			min_y=Math.min(min_y,v.getY());
			max_y=Math.max(max_y,v.getY()+box_height);
		}
		min_x-=20;
		min_y-=20;
		max_x+=20;
		max_y+=20;
	}

	/********************************************************************/
	/*                           draw graph                             */
	/********************************************************************/
					 
	public void draw(Graphics g) {
		if (box_height==0) layout(g);

		g.translate(-min_x,-min_y);

		Enumeration e1=vertices.elements();
		while (e1.hasMoreElements())
			((Vertex)(e1.nextElement())).draw(g);

		e1=splines.elements();
		while (e1.hasMoreElements())
			((Spline)(e1.nextElement())).draw(g);
	}

	/********************************************************************/
	/*               return vertex at position (x,y)                    */
	/********************************************************************/

	public Vertex vertexAt(int x,int y) {
		Enumeration e1=vertices.elements();
		while (e1.hasMoreElements()) {
			Vertex v=(Vertex)(e1.nextElement());
			if (v.contains(x,y)) return v;
		}
		return null;
	}

	/********************************************************************/
	/*       encode list of vertices (as array of vertice numbers)      */
	/********************************************************************/

	public Vector encode(Vector v) {
		Vector code=new Vector(10,10);
		Enumeration e1=v.elements();

		while (e1.hasMoreElements()) {
			Vertex vx=(Vertex)(e1.nextElement());
			if (vx.getNumber()>=0)
				code.addElement(new Integer(vx.getNumber()));
		}
		return code;
	}

	/********************************************************************/
	/*                      get vertex with number n                    */
	/********************************************************************/

	public Vertex getVertexByNum(int x) {
		Enumeration e1=vertices.elements();

		while (e1.hasMoreElements()) {
			Vertex vx=(Vertex)(e1.nextElement());
			if (vx.getNumber()==x) return vx;
		}
		return null;
	}

	/********************************************************************/
	/*                      decode list of vertices                     */
	/********************************************************************/

	public Vector decode(Vector code) {
		Enumeration e1=code.elements();
		Vector vec=new Vector(10,10);

		while (e1.hasMoreElements()) {
			int i=((Integer)(e1.nextElement())).intValue();
			//Vertex vx=getVertexByNum(i);
			//if (vx!=null) vec.addElement(vx);
			vec.addElement(vertices2[i]);
		}
		return vec;
	}

	/********************************************************************/
	/*                       collapse vertices                          */
	/********************************************************************/

	public void collapse(Vector vs,String name,Vector inflate) {
		Enumeration e1,e2,e3;
		boolean nonempty=false;
		Vertex vx3,vx2,vx1;
		
		e1=vertices.elements();

		vx1=new NormalVertex(name);
		vx1.setInflate(inflate);

		while (e1.hasMoreElements()) {
			vx2=(Vertex)(e1.nextElement());

			if (vs.indexOf(vx2)<0) {
				e2=vx2.getParents();
				while (e2.hasMoreElements()) {
					vx3=(Vertex)(e2.nextElement());
					if (vs.indexOf(vx3)>=0) {
						if (!vx1.isChild(vx2))
							vx1.addChild(vx2);
						vx3.removeChild(vx2);
					}
				}

				e2=vx2.getChildren();
				while (e2.hasMoreElements()) {
					vx3=(Vertex)(e2.nextElement());
					if (vs.indexOf(vx3)>=0) {
						if (!vx2.isChild(vx1))
							vx2.addChild(vx1);
						vx2.removeChild(vx3);
					}
				}
			} else { nonempty=true; }
		}

		e1=vs.elements();
		while (e1.hasMoreElements())
			try {
				removeVertex((Vertex)(e1.nextElement()));
			} catch (NoSuchElementException exn) {}

		if (nonempty) addVertex(vx1);
	}

	/********************************************************************/
	/*                      PostScript output                           */
	/********************************************************************/

	public void PS(String fname,boolean printable) throws IOException {
		FileOutputStream f = new FileOutputStream(fname);
		PrintStream p = new PrintStream(f);

		if (printable)
			p.println("%!PS-Adobe-2.0\n\n%%BeginProlog");
		else {
			p.println("%!PS-Adobe-2.0 EPSF-2.0\n%%Orientation: Portrait");
			p.println("%%BoundingBox: "+min_x+" "+min_y+" "+max_x+" "+max_y);
			p.println("%%EndComments\n\n%%BeginProlog");
		}
		p.println("/m { moveto } def /l { lineto } def /n { newpath } def");
		p.println("/s { stroke } def /c { curveto } def");
		p.println("/b { n 0 0 m dup true charpath pathbbox 1 index 4 index sub");
		p.println("7 index exch sub 2 div 9 index add 1 index 4 index sub 7 index exch sub");
		p.println("2 div 9 index add 2 index add m pop pop pop pop");
		p.println("1 -1 scale show 1 -1 scale n 3 index 3 index m 1 index 0 rlineto");
		p.println("0 exch rlineto neg 0 rlineto closepath s pop pop } def");
		p.println("%%EndProlog\n");
		if (printable) {
			int hsize=max_x-min_x;
			int vsize=max_y-min_y;
			if (hsize>vsize) {
				// Landscape output
				double scale=Math.min(1,Math.min(750.0/hsize,500.0/vsize));
				double trans_x=50+max_y*scale+(500-scale*vsize)/2.0;
				double trans_y=50+max_x*scale+(750-scale*hsize)/2.0;
				p.println(trans_x+" "+trans_y+" translate");
				p.println("-90 rotate");
				p.println(scale+" "+(-scale)+" scale");
			} else {
				// Portrait output
				double scale=Math.min(1,Math.min(500.0/hsize,750.0/vsize));
				double trans_x=50-min_x*scale+(500-scale*hsize)/2.0;
				double trans_y=50+max_y*scale+(750-scale*vsize)/2.0;
				p.println(trans_x+" "+trans_y+" translate");
				p.println(scale+" "+(-scale)+" scale");
			}
		} else
			p.println("0 "+(max_y+min_y)+" translate\n1 -1 scale");

		p.println("/Helvetica findfont 12 scalefont setfont");
		p.println("0.5 setlinewidth");

		Enumeration e1=vertices.elements();
		while (e1.hasMoreElements())
			((Vertex)(e1.nextElement())).PS(p);

		e1=splines.elements();
		while (e1.hasMoreElements())
			((Spline)(e1.nextElement())).PS(p);

		if (printable) p.println("showpage");

		f.close();
	}
}

/**** Return value of function calcPoint ****/

class Points {
	public Point p,q;

	public Points(Point p1,Point p2) {
		p=p1;q=p2;
	}
}

