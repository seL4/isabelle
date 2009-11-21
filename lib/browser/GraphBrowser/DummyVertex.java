/***************************************************************************
  Title:      GraphBrowser/DummyVertex.java
  Author:     Stefan Berghofer, TU Muenchen

  This class represents a dummy vertex, which is used to simplify the
  layout algorithm.
***************************************************************************/

package GraphBrowser;

import java.awt.*;

class DummyVertex extends Vertex {
	public boolean isDummy() {return true;}

	public Object clone() {
		Vertex ve=new DummyVertex();
		ve.setX(getX());ve.setY(getY());
		return ve;
	}

	public int leftX() { return getX(); }

	public int rightX() { return getX(); }

	public void draw(Graphics g) {}
}

