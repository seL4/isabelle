package GraphBrowser;

import java.util.Vector;

class Directory {
	TreeNode node;
	String name;
	Vector collapsed;

	public Directory(TreeNode nd,String n,Vector col) {
		collapsed=col;
		name=n;
		node=nd;
	}

	public TreeNode getNode() { return node; }

	public String getName() { return name; }

	public Vector getCollapsed() { return collapsed; }
}
