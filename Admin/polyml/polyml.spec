Summary:	Poly/ML compiler and runtime system
Name:		polyml
Version:	3X
Release:	2
Group:		Development/Languages
Copyright:	Cambridge University Technical Services Limited
Url:		http://www.polyml.org
Packager:	Markus Wenzel <wenzelm@in.tum.de>
Prefix:		/usr/share

%description
Poly/ML is a full implementation of Standard ML available as
open-source.

It currently supports the ML 90 version of the language and a project
is under way to bring this up to the ML 97 version.

%install
ln -sf /usr/share/polyml/bin/polyml /usr/bin/polyml

%post
ln -sf $RPM_INSTALL_PREFIX/polyml/bin/polyml /usr/bin/polyml

%files
/usr/share/polyml
