/***************************************************************************
  Title:      GraphBrowser/NormalVertex.java
  ID:         $Id$
  Author:     Stefan Berghofer, TU Muenchen
  Copyright   1997  TU Muenchen

  This class represents an ordinary vertex. It contains methods for
  drawing and PostScript output.
***************************************************************************/

package GraphBrowser;

import java.util.*;
import java.awt.*;
import java.io.*;

class NormalVertex extends Vertex {
	String label="",path="",dir="",ID="";
	Vector up,down,inflate=null;

	public Object clone() {
		Vertex ve=new NormalVertex(label);
                ve.setID(ID);
		ve.setNumber(getNumber());
		ve.setUp(getUp());ve.setDown(getDown());
		ve.setX(getX());ve.setY(getY());
		ve.setPath(getPath());
		return ve;
	}

	/*** Constructor ***/

	public NormalVertex(String s) { label=s; }

	public void setInflate(Vector v) { inflate=v; }

	public Vector getInflate() { return inflate; }

	public Vector getUp() { return up; }

	public void setUp(Vector v) { up=v; }

	public Vector getDown() { return down; }

	public void setDown(Vector v) { down=v; }

	public String getLabel() {return label;}

	public void setLabel(String s) {label=s;}

	public void setID(String s) { ID=s; }

        public String getID() { return ID; }

	public String getPath() { return path;}

	public void setPath(String p) { path=p; }

	public String getDir() { return dir; }

	public void setDir(String d) { dir=d; }

	public int leftX() { return getX()-gra.box_width2; }

	public int rightX() { return getX()+gra.box_width2; }

	public void drawBox(Graphics g,Color boxColor) {
		FontMetrics fm=g.getFontMetrics(font);
		g.setFont(font);
		int h=fm.getAscent()+fm.getDescent();

		g.setColor(boxColor);
		g.fillRect(getX()-gra.box_width2,getY(),gra.box_width,gra.box_height);
		g.setColor(Color.black);
		g.drawRect(getX()-gra.box_width2,getY(),gra.box_width,gra.box_height);
		if (getNumber()<0) {
			g.setColor(Color.red);
			label=label.substring(1,label.length()-1);
			while (label.length()>0 && fm.stringWidth("["+label+"]")>gra.box_width-8)
					label=label.substring(0,label.length()-1);
			label="["+label+"]";
		}

		g.drawString(label,
		             (int)Math.round((gra.box_width-fm.stringWidth(label))/2.0)+getX()-gra.box_width2,
				fm.getAscent()+(int)Math.round((gra.box_height-h)/2.0)+getY());
	}

	public void removeButtons(Graphics g) {
		drawBox(g,Color.lightGray);
	}

	public void draw(Graphics g) {
		drawBox(g,Color.lightGray);
		g.setColor(Color.black);
		Enumeration e1=getChildren();
		while (e1.hasMoreElements()) {
			Vertex v=(Vertex)(e1.nextElement());
			if (!v.isDummy())
				g.drawLine(getX(),getY()+gra.box_height,v.getX(),v.getY());
		}
	}

	public boolean contains(int x,int y) {
		return (x>=leftX() && x<=rightX() && y>=getY() &&
                        y<=getY()+gra.box_height);
	}

	public boolean leftButton(int x,int y) {
		return contains(x,y) && x<=leftX()+gra.box_height && getParents().hasMoreElements() && getNumber()>=0;
	}

	public boolean rightButton(int x,int y) {
		return contains(x,y) && x>=rightX()-gra.box_height && getChildren().hasMoreElements() && getNumber()>=0;
	}

	public void drawButtons(Graphics g) {
		if (getNumber()<0) return;

		int l=gra.box_height*2/3,d=gra.box_height/6;
		int up_x[] = { leftX()+d , leftX()+d+l/2 , leftX()+d+l };
		int up_y[] = { getY()+d+l , getY()+d , getY()+d+l };
		int down_x[] = { rightX()-d-l , rightX()-d-l/2 , rightX()-d };
		int down_y[] = { getY()+d , getY()+d+l , getY()+d };

		if (getParents().hasMoreElements()) {
			g.setColor(Color.gray);
			g.fillRect(leftX()+1,getY()+1,gra.box_height-1,gra.box_height-1);
			g.setColor(getUp()!=null ? Color.red : Color.green);
			g.fillPolygon(up_x,up_y,3);
		}
		if (getChildren().hasMoreElements()) {
			g.setColor(Color.gray);
			g.fillRect(rightX()+1-gra.box_height,getY()+1,gra.box_height,gra.box_height-1);
			g.setColor(getDown()!=null ? Color.red : Color.green);
			g.fillPolygon(down_x,down_y,3);
		}
		g.setColor(Color.black);
	}

	public void PS(PrintStream p) {
		p.print(leftX()+" "+getY()+" "+gra.box_width+" "+
		        gra.box_height+" (");
		for (int i=0;i<label.length();i++)
		{
			if (("()\\").indexOf(label.charAt(i))>=0)
				p.print("\\");
			p.print(label.charAt(i));
		}
		p.println(") b");

		Enumeration e1=getChildren();
		while (e1.hasMoreElements()) {
			Vertex v=(Vertex)(e1.nextElement());
			if (!v.isDummy())
				p.println("n "+getX()+" "+(getY()+gra.box_height)+
				" m "+v.getX()+" "+v.getY()+" l s");
		}
	}	
}
		
