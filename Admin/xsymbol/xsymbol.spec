Summary:	X-Symbol mode for XEmacs to display mathematical symbols
Name:		xsymbol
Version:	3.3d
Release:	1
Group:		Applications/Editors/Emacs
Copyright:	GPL
Url:		http://www.fmi.uni-passau.de/~wedler/x-symbol/
Packager:	Markus Wenzel <wenzelm@in.tum.de>
Prefix:		/usr/share
BuildArchitectures: noarch

%description

X-Symbol is an XEmacs package providing semi-WYSIWYG for LaTeX, HTML
and other ``token languages''.  It uses additional fonts and provide
input methods to insert their characters into your document.

The main purpose of package X-Symbol is to provide some WYSIWYGness in
an area where it greatly enhance the readability of your LaTeX or HTML
source: using "real" characters for "tokens" like \oplus or &#8482;.
It also provides input methods for these characters, both for the
beginner and the expert (some users regard this as the main reason to
use package X-Symbol). WYSIWYG super- and subscripts and
images/figures are also supported.

This distribution of X-Symbol is intended to be used together with
Isabelle and Proof General.  It relies on Isabelle's automatic
configuration of contributed packages.  Please ignore the installation
instructions of X-Symbol!

%prep
find /usr/share/x-symbol -type f -print | xargs perl -pi -e 's:^#!.*/perl:#!usr/bin/perl:'

%files
%attr(-,root,root) /usr/share/x-symbol
