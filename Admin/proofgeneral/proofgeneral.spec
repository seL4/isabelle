Summary:	Proof General, Emacs interface for Proof Assistants
Name:		proofgeneral
Version:	3.2pre000923
Release:	1
Group:		Applications/Editors/Emacs
Copyright:	LFCS, University of Edinburgh
Url:		http://www.lfcs.informatics.ed.ac.uk/proofgen
Packager:	Markus Wenzel <wenzelm@in.tum.de>
Prefix:		/usr/share
BuildArchitectures: noarch

%description
Proof General is a generic Emacs interface for proof assistants,
suitable for use by pacifists and Emacs militants alike.  It is
supplied ready-customized for LEGO, Coq, and Isabelle.

%prep
find /usr/share/ProofGeneral/. -type f -print | xargs perl -pi -e 's:^#!.*/perl:#!usr/bin/perl:'

%files
%attr(-,root,root) /usr/share/ProofGeneral
%attr(-,root,root) /usr/share/ProofGeneral-3.2pre000923
