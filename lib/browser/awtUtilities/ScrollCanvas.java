/***************************************************************************
  Title:      awtUtilities/ScrollCanvas.java
  ID:         $Id$
  Author:     Stefan Berghofer, TU Muenchen
  Copyright   1997  TU Muenchen

  This class contains defines a window with scrollbars, which is not
  supported by the 1.0.2 version of the JDK. To use this class, simply
  derive your own class from it and overwrite the paintCanvas method.
  When a repaint event occurs, ScrollCanvas automatically calls the
  paintCanvas method. The user doesn't have to take care of transposing
  mouse or graphics coordinates.
  Note: In later versions of the JDK, a ScrollPane class will be provided,
  which can be used instead.
***************************************************************************/

package awtUtilities;

import java.awt.*;

class DummyCanvas extends Canvas {
	ScrollCanvas parent;

	public DummyCanvas(ScrollCanvas p) {
		parent=p;
	}

	public void paint(Graphics g) {
		parent.paint(g);
	}

	public void update(Graphics g) {
		parent.update(g);
	}
}

public class ScrollCanvas extends Panel
{
	Scrollbar scrollv,scrollh;
	Canvas can;
	Image img=null;
	int offset_x=0,offset_y=0;
	int size_x=100,size_y=100;
	int old_x=0,old_y=0;

	public boolean handleEvent(Event evt)
	{
		evt.x+=offset_x;
		evt.y+=offset_y;
		if (evt.target instanceof Scrollbar)
		{
			offset_x=scrollh.getValue();
			offset_y=scrollv.getValue();
			Graphics g=can.getGraphics();
			if (old_x!=size_x || old_y!=size_y)
				update(g);
			else {
				g.translate(-offset_x,-offset_y);
				g.drawImage(img,0,0,this);
			}
			return true;
		}
		else return super.handleEvent(evt);
	}

	public void adjust_scrollbars()
	{
		int viewport_v=can.size().height;
		int viewport_h=can.size().width;
		int value_v=scrollv.getValue();
		int value_h=scrollh.getValue();

		scrollv.setValues(value_v,viewport_v,0,size_y-viewport_v);
		scrollh.setValues(value_h,viewport_h,0,size_x-viewport_h);
		scrollv.setLineIncrement(viewport_v/20);
		scrollv.setPageIncrement(viewport_v);
		scrollh.setLineIncrement(viewport_h/20);
		scrollh.setPageIncrement(viewport_h);
		offset_x=scrollh.getValue();
		offset_y=scrollv.getValue();
	}

	public void set_size(int x,int y)
	{
		size_x=x;size_y=y;
		adjust_scrollbars();
	}

	public void focus_to(int x,int y) {
		offset_x=Math.min(scrollh.getMaximum(),Math.max(0,x-can.size().width/2));
		offset_y=Math.min(scrollv.getMaximum(),Math.max(0,y-can.size().height/2));

		scrollh.setValue(offset_x);
		scrollv.setValue(offset_y);
		Graphics g=can.getGraphics();
		if (old_x!=size_x || old_y!=size_y)
			update(g);
		else {
			g.translate(-offset_x,-offset_y);
			g.drawImage(img,0,0,this);
		}
	}		

	public void update(Graphics g) {
		g=can.getGraphics();
		int viewport_v=can.size().height;
		int viewport_h=can.size().width;
		int img_x=Math.max(viewport_h,size_x+1);
		int img_y=Math.max(viewport_v,size_y+1);

		old_x=size_x;old_y=size_y;
		img=createImage(img_x,img_y);
		Graphics g2=img.getGraphics();
		g2.setColor(Color.lightGray);
		g2.fillRect(0,0,img_x,img_y);
		g2.setColor(Color.black);
		paintCanvas(g2);
		adjust_scrollbars();
		g.translate(-offset_x,-offset_y);
		g.drawImage(img,0,0,this);
	}

	public void paint(Graphics g)
	{
		if (img!=null && old_x==size_x && old_y==size_y) {
			g=can.getGraphics();
			adjust_scrollbars();
			g.translate(-offset_x,-offset_y);
			g.drawImage(img,0,0,this);
		} else update(g);
	}

	public Graphics getGraphics() {
		Graphics g=can.getGraphics();

		g.translate(-offset_x,-offset_y);
		return g;
	}	

	public void paintCanvas(Graphics g)
	{}

	public ScrollCanvas()
	{
		can=new DummyCanvas(this);
		GridBagLayout gridbag = new GridBagLayout();
		GridBagConstraints c = new GridBagConstraints();
		scrollv=new Scrollbar(Scrollbar.VERTICAL);
		scrollh=new Scrollbar(Scrollbar.HORIZONTAL);

		setLayout(gridbag);
		c.weightx = 1.0;
		c.weighty = 1.0;
		c.gridwidth=1;
		c.fill = GridBagConstraints.BOTH;
		gridbag.setConstraints(can,c);
		add(can);
		c.weightx=0;
		c.weighty=0;
		c.gridwidth = GridBagConstraints.REMAINDER;
		c.fill = GridBagConstraints.VERTICAL;
		gridbag.setConstraints(scrollv,c);
		add(scrollv);
		c.gridwidth = 1;
		c.fill = GridBagConstraints.HORIZONTAL;
		gridbag.setConstraints(scrollh,c);
		add(scrollh);
	}
}
