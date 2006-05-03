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

def split_mail(mail):

    mail_arg = mail.split("?", 2)
    if len(mail_arg) == 2:
        mail, arg = mail_arg
    else:
        mail = mail_arg[0]
        arg = None
    name, host = mail.split("@", 2) 

    return ((name, host), arg)

class FindHandler(TransformerHandler):

    class DevZero(object):

        def write(self, s):

            pass

    def __init__(self, dtd, filename, mails, encs):

        super(FindHandler, self).__init__(self.DevZero(), 'UTF-8', dtd)
        self.filename = filename
        self.mails = mails
        self.encs = encs
        self.pending_mail = None

    def startElement(self, name, attrs):

        if name == u'a':
            href = attrs.get(u'href', u'')
            if href.startswith(u'mailto:'):
                self.pending_mail = href[7:]
        super(FindHandler, self).startElement(name, attrs)
        if name == u'meta' and attrs.get(u'http-equiv', u'').lower() == u'content-type':
            content = attrs.get(u'content', u'')
            if content.startswith(u'text/html; charset='):
                self.encs[self.filename] = content[19:]

    def endElement(self, name):

        if name == u'a':
            if self.pending_mail is not None:
                baremail = "%s@%s" % split_mail(self.pending_mail)[0]
                if self.currentContent() != baremail:
                    raise Exception("In '%s', inconsistent mail address: '%s' vs. '%s'" % (self.filename, self.currentContent(), baremail))
                self.mails[(self.filename, self.pending_mail)] = True
                self.pending_mail = None
        super(FindHandler, self).endElement(name)

    def processingInstruction(self, target, data):

        pass

class ReplaceHandler(TransformerHandler):

    def __init__(self, out, dtd, filename, encoding, mails):

        super(ReplaceHandler, self).__init__(out, encoding, dtd)
        self.filename = filename
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
                self._out.write(self.mails[(self.filename, self.pending_mail)])
                self.pending_mail = None
                return

        super(ReplaceHandler, self).endElement(name)

    def characters(self, content):

        if self.pending_mail is None:
            super(ReplaceHandler, self).characters(content)

    def processingInstruction(self, target, data):

        pass

def obfuscate(mailaddr, htmlfile):

    def mk_line(s):
        return u"document.write('%s');" % s.replace("'", "\\'")
    def mk_script(s):
        return u'<script type="text/javascript">/*<![CDATA[*/%s/*]]>*/</script>' % s
    def cmd(s):
        print "[shell cmd] %s" % s
        n = os.system(s)
        if n != 0:
            raise Exception("shell cmd error: %s" % n)

    ((name, host), arg) = split_mail(mailaddr)
    baremail = "%s@%s" % (name, host)
    imgname = (name + "_" + host).replace(".", "_") + ".png"
    imgfile = path.join(path.split(htmlfile)[0], imgname)
    cmd("convert label:'%s' '%s'" % (baremail, imgfile))
    if arg is not None:
        mailsimple = u"{%s} AT [%s] WITH (%s)" % (name, host, arg)
        mailscript = u" ".join(map(mk_line, ['<a href="', "mailto:", name, "@", host, "?", arg, '">']));
    else:
        mailsimple = u"{%s} AT [%s]" % (name, host)
        mailscript = u" ".join(map(mk_line, ['<a href="', "mailto:", name, "@", host, '">']));
    mailimg = '<img src=%s style="vertical-align:middle" alt=%s />' % (quoteattr(imgname), quoteattr(mailsimple))

    return (mk_script(mailscript) + mailimg + mk_script(mk_line("</a>")))

def main():

    # parse command line
    cmdlineparser = optparse.OptionParser(
        usage = '%prog [options] htmlfiles*',
        conflict_handler = "error",
        description = '''Protecting mail adresses in html files by obfuscating''',
        add_help_option = True,
    )
    cmdlineparser.add_option("-t", "--dtd",
        action="store", dest="dtd",
        type="string", default=".",
        help="local mirror of XHTML DTDs", metavar='location')

    options, filenames = cmdlineparser.parse_args(sys.argv[1:])

    # find mails
    mails = {}
    encs = {}
    for filename in filenames:
        istream = open(filename, 'r')
        findhandler = FindHandler(options.dtd, filename, mails, encs)
        parseWithER(istream, findhandler)
        istream.close()

    # transform mails
    mails_subst = {}
    filenames = {}
    for filename, mail in mails.iterkeys():
        filenames[filename] = True
        mails_subst[(filename, mail)] = obfuscate(mail, filename)

    # transform pages
    for filename in filenames.iterkeys():
        istream = StringIO(open(filename, 'r').read())
        ostream = open(filename, 'wb')
        print "writing %s with %s" % (filename, encs.get(filename, outputEncoding))
        replacehandler = ReplaceHandler(ostream, options.dtd, filename, encs.get(filename, outputEncoding), mails_subst)
        parseWithER(istream, replacehandler)
        ostream.close()
        istream.close()

if __name__ == '__main__':
    main()

__todo__ = '''
'''
