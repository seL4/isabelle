/***************************************************************************
  Title:      Graph/TextFrame.java
  ID:         $Id$
  Author:     Stefan Berghofer, TU Muenchen
  Copyright   1997  TU Muenchen

  This class defines a simple text viewer.
***************************************************************************/

package awtUtilities;

import java.awt.*;
import java.awt.event.*;

public class TextFrame extends Frame implements ActionListener {
	public void actionPerformed(ActionEvent evt) {
		setVisible(false);
	}

	public TextFrame(String title,String text) {
		super(title);
		TextArea ta = new TextArea(text,200,80);
		Button bt = new Button("Dismiss");
		bt.addActionListener(this);
		ta.setEditable(false);
		add("Center", ta);
		add("South", bt);
	}
}
