/***************************************************************************
  Title:      GraphBrowser/Spline.java
  ID:         $Id$
  Author:     Stefan Berghofer, TU Muenchen
  Copyright   1997  TU Muenchen

  This class is used for drawing spline curves (which are not yet
  supported by the Java AWT).
***************************************************************************/

package GraphBrowser;

import java.awt.*;
import java.util.*;
import java.io.*;

class SplineSection {

	/*** Section of a spline function ***/

	double x_b,x_c,x_d;
	double y_b,y_c,y_d;
	int dx,dy;

	public SplineSection(double xb,double xc,double xd,
		double yb,double yc,double yd,int dx2,int dy2) {
		x_b=xb;x_c=xc;x_d=xd;
		y_b=yb;y_c=yc;y_d=yd;
		dx=dx2;dy=dy2;
	}

	public Point draw(Graphics g,Point s) {
		double m;
		int s_x,s_y,e_x=0,e_y=0;
		int x,y;

		s_x=s.x;s_y=s.y;
		if (dx>=dy) {
			if (dx==0) return s;
			m=1/((double)dx);
			for (x=0;x<dx;x++) {
				e_x=(int)(Math.round((x_b*x*m+x_c)*x*m+x_d));
				e_y=(int)(Math.round((y_b*x*m+y_c)*x*m+y_d));
				g.drawLine(s_x,s_y,e_x,e_y);
				s_x=e_x;s_y=e_y;
			}
		} else {
			m=1/((double)dy);
			for (y=0;y<dy;y++) {
				e_x=(int)(Math.round((x_b*y*m+x_c)*y*m+x_d));
				e_y=(int)(Math.round((y_b*y*m+y_c)*y*m+y_d));
				g.drawLine(s_x,s_y,e_x,e_y);
				s_x=e_x;s_y=e_y;
			}
		}
		return new Point(e_x,e_y);
	}
}

public class Spline {

	Vector sections;
	Vector points;
	Point start,end;

	public Spline(Vector pts) {
		int i;
		double d0,d1,d2,d3;
		Point p0,p1,p2;
		SplineSection s;
		
		start=(Point)(pts.firstElement());
		end=(Point)(pts.lastElement());

		sections=new Vector(10,10);
		for (i=1;i<=pts.size()-4;i+=3) {
			p0=(Point)(pts.elementAt(i));
			p1=(Point)(pts.elementAt(i+1));
			p2=(Point)(pts.elementAt(i+2));
			s=new SplineSection(
				(double)(p2.x-2*p1.x+p0.x),
				2.0*(p1.x-p0.x),
				(double)(p0.x),

				(double)(p2.y-2*p1.y+p0.y),
				2.0*(p1.y-p0.y),
				(double)(p0.y),

				Math.abs(p2.x-p0.x),
				Math.abs(p2.y-p0.y)
			);

			sections.addElement(s);
		}
		points=pts;
	}

	public void draw(Graphics g) {
		Enumeration e1=sections.elements();
		Point p=start;

		while (e1.hasMoreElements())
			p=((SplineSection)(e1.nextElement())).draw(g,p);
		g.drawLine(p.x,p.y,end.x,end.y);
	}

	public void PS(PrintStream p) {
		Point p0,p1,p2;
		int i;

		p.println("n "+start.x+" "+start.y+" m");
		for (i=1;i<=points.size()-4;i+=3) {
			p0=(Point)(points.elementAt(i));
			p1=(Point)(points.elementAt(i+1));
			p2=(Point)(points.elementAt(i+2));
			p.println(p0.x+" "+p0.y+" l");
			p.println(p0.x+" "+p0.y+" "+p1.x+" "+p1.y+" "+p2.x+" "+p2.y+" c");
		}
		p.println(end.x+" "+end.y+" l s");
	}
}
