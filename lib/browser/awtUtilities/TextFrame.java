/***************************************************************************
  Title:      Graph/TextFrame.java
  ID:         $Id$
  Author:     Stefan Berghofer, TU Muenchen
  Copyright   1997  TU Muenchen

  This class defines a simple text viewer.
***************************************************************************/

package awtUtilities;

import java.awt.*;

public class TextFrame extends Frame {
	public boolean action(Event evt,Object obj) {
		if (evt.target instanceof Button)
			hide();
		return true;
	}

	public TextFrame(String title,String text) {
		super(title);
		TextArea ta=new TextArea(text,200,80);
		ta.setEditable(false);
		add("Center",ta);
		add("South",new Button("Dismiss"));
	}
}
