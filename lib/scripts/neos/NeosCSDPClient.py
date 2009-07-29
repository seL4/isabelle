#!/usr/bin/env python
import sys
import xmlrpclib
import time
import re

from config import Variables

if len(sys.argv) < 3 or len(sys.argv) > 3:
  sys.stderr.write("Usage: NeosCSDPClient <input_filename> <output_filename>\n")
  sys.exit(1)

neos=xmlrpclib.Server("http://%s:%d" % (Variables.NEOS_HOST, Variables.NEOS_PORT))

xmlfile = open(sys.argv[1],"r")
xml_pre = "<document>\n<category>sdp</category>\n<solver>csdp</solver>\n<inputMethod>SPARSE_SDPA</inputMethod>\n<dat><![CDATA["
xml_post = "]]></dat>\n</document>\n"
xml = xml_pre
buffer = 1
while buffer:
  buffer = xmlfile.read()
  xml += buffer
xmlfile.close()
xml += xml_post

(jobNumber,password) = neos.submitJob(xml)

if jobNumber == 0:
  sys.stdout.write("error submitting job: %s" % password)
  sys.exit(-1)
else:
  sys.stdout.write("jobNumber = %d\tpassword = %s\n" % (jobNumber,password))

offset=0
status="Waiting"
while status == "Running" or status=="Waiting":
  time.sleep(1)
  (msg,offset) = neos.getIntermediateResults(jobNumber,password,offset)
  sys.stdout.write(msg.data)
  status = neos.getJobStatus(jobNumber, password)

msg = neos.getFinalResults(jobNumber, password).data
result = msg.split("Solution:")

sys.stdout.write(result[0])
if len(result) > 1:
  plain_msg = result[1].strip()
  if plain_msg != "":
    output = open(sys.argv[2],"w")
    output.write(plain_msg)
    output.close()
    sys.exit(0)

sys.exit(2)


