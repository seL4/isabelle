/***************************************************************************
  Title:      awtUtilities/MessageDialog.java
  ID:         $Id$
  Author:     Stefan Berghofer, TU Muenchen
  Copyright   1997  TU Muenchen

  This class defines a dialog window for displaying messages and buttons.
***************************************************************************/

package awtUtilities;

import java.awt.*;

public class MessageDialog extends Dialog {
	String txt;

	public String getText() { return txt; }

	public boolean action(Event evt, Object arg) {
		if (evt.target instanceof Button) {
			txt=(String)arg;
			hide();
			return true;
		} else return false;
	}

	public MessageDialog(Frame parent,String title,String text,String []buttons) {
		super(parent,title,true);
		int i;
		Panel p1=new Panel(),p2=new Panel();
		p1.setLayout(new FlowLayout(FlowLayout.CENTER,0,0));
		p2.setLayout(new FlowLayout());
		setFont(new Font("Helvetica", Font.PLAIN, 14));
		setLayout(new GridLayout(2,1));

		while (true) {
			int pos=text.indexOf(' ');
			if (pos<0) {
				p1.add(new Label(text));
				break;
			} else {
				p1.add(new Label(text.substring(0,pos)));
				if (pos+1==text.length())
					break;
				else
					text=text.substring(pos+1);
			}
		}

		add(p1);add(p2);
		for (i=0;i<buttons.length;i++)
			p2.add(new Button(buttons[i]));
	}
}
