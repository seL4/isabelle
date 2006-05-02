#!/usr/bin/env python
# -*- coding: Latin-1 -*-

"""
    Obfucatings mail adresses
"""

__author__ = 'Florian Haftmann, florian.haftmann@informatik.tu-muenchen.de'
__revision__ = '$Id$'

import sys
import os
from os import path
import posixpath
import optparse
from cStringIO import StringIO

from xml.sax.saxutils import escape
from xml.sax.saxutils import quoteattr

from xhtmlparse import TransformerHandler, parseWithER

# global configuration
outputEncoding = 'UTF-8'

class FindHandler(TransformerHandler):

    class DevZero(object):

        def write(self, s):

            pass

    def __init__(self, dtd, mails):

        super(FindHandler, self).__init__(self.DevZero(), outputEncoding, dtd)
        self.pending_mail = None
        self.mails = mails

    def startElement(self, name, attrs):

        if name == u'a':
            href = attrs.get(u'href', u'')
            if href.startswith(u'mailto:'):
                self.pending_mail = href[7:]
        super(FindHandler, self).startElement(name, attrs)

    def endElement(self, name):

        if name == u'a':
            if self.pending_mail is not None:
                if self.currentContent() != self.pending_mail:
                    raise Exception("Inconsistent mail address: '%s' vs. '%s'" % (self.currentContent(), self.pending_mail))
                self.mails[self.pending_mail] = True
                self.pending_mail = None
        super(FindHandler, self).endElement(name)

    def processingInstruction(self, target, data):

        pass

class ReplaceHandler(TransformerHandler):

    def __init__(self, out, dtd, mails):

        super(ReplaceHandler, self).__init__(out, outputEncoding, dtd)
        self.pending_mail = None
        self.mails = mails

    def startElement(self, name, attrs):

        if name == u'a':
            href = attrs.get(u'href', u'')
            if href.startswith(u'mailto:'):
                self.pending_mail = href[7:]
                return

        super(ReplaceHandler, self).startElement(name, attrs)

    def endElement(self, name):

        if name == u'a':
            if self.pending_mail is not None:
                self.flushCharacterBuffer()
                self._out.write(self.mails[self.pending_mail])
                self.pending_mail = None
                return

        super(ReplaceHandler, self).endElement(name)

    def characters(self, content):

        if self.pending_mail is None:
            super(ReplaceHandler, self).characters(content)

    def processingInstruction(self, target, data):

        pass

def obfuscate(mailaddr, dsturl, dstfile):

    def mk_line(s):
        return u"document.write('%s');" % s.replace("'", "\\'")
    def mk_script(s):
        return u'<script type="text/javascript">%s</script>' % s

    name, host = mailaddr.split("@", 2)
    imgname = (name + "_" + host).replace(".", "_"). replace("?", "_") + ".png"
    imgfile = path.join(dstfile, imgname)
    os.system("convert label:'%s' '%s'" % (mailaddr, imgfile))
    mailsimple = u"{%s} AT [%s]" % (name, host)
    imgurl = posixpath.join(dsturl, imgname)
    mailscript = u" ".join(map(mk_line, ['<a href="', "mailto:", name, "@", host, '">']));
    mailimg = '<img src=%s style="vertical-align:middle" alt=%s />' % (quoteattr(imgurl), quoteattr(mailsimple))

    return (mk_script(mailscript) + mailimg + mk_script(mk_line("</a>")))

def main():

    # parse command line
    cmdlineparser = optparse.OptionParser(
        usage = '%prog [options] htmlfiles*',
        conflict_handler = "error",
        description = '''Protecting mail adresses in html files by obfuscating''',
        add_help_option = True,
    )
    cmdlineparser.add_option("-d", "--dstroot",
        action="store", dest="dstroot",
        type="string", default=".",
        help="root destination of generated images", metavar='location')
    cmdlineparser.add_option("-D", "--dstdir",
        action="store", dest="dstdir",
        type="string", default=".",
        help="root destination of generated images", metavar='location')
    cmdlineparser.add_option("-t", "--dtd",
        action="store", dest="dtd",
        type="string", default=".",
        help="local mirror of XHTML DTDs", metavar='location')

    options, filenames = cmdlineparser.parse_args(sys.argv[1:])

    # find mails
    mails = {}
    for filename in filenames:
        istream = open(filename, 'r')
        findhandler = FindHandler(options.dtd, mails)
        parseWithER(istream, findhandler)
        istream.close()

    # transform mails
    mails_subst = {}
    for mail in mails.keys():
        mails_subst[mail] = obfuscate(mail, options.dstdir, path.join(options.dstroot, options.dstdir))

    # transform pages
    for filename in filenames:
        istream = StringIO(open(filename, 'r').read())
        ostream = open(filename, 'wb')
        replacehandler = ReplaceHandler(ostream, options.dtd, mails_subst)
        parseWithER(istream, replacehandler)
        ostream.close()
        istream.close()

if __name__ == '__main__':
    main()

__todo__ = '''
'''
