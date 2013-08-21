#!/usr/bin/env python
#     Title:      HOL/Tools/Sledgehammer/MaSh/src/mash
#     Author:     Daniel Kuehlwein, ICIS, Radboud University Nijmegen
#     Copyright   2012 - 2013
#
# Entry point for MaSh (Machine Learning for Sledgehammer).

'''
MaSh - Machine Learning for Sledgehammer

MaSh allows to use different machine learning algorithms to predict relevant fact for Sledgehammer.

Created on July 12, 2012

@author: Daniel Kuehlwein
'''

import socket,sys,time,logging

from spawnDaemon import spawnDaemon


import logging,string,os,sys


from theoryStats import TheoryStatistics
from theoryModels import TheoryModels
from dictionaries import Dictionaries
from predefined import Predefined

from parameters import init_parser

def communicate(data,host,port):
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    try:
        sock.connect((host,port))
        sock.sendall(data)
        received = sock.recv(4194304)
    except:
        logger = logging.getLogger('communicate')
        logger.warning('Communication with server failed.')
        received = -1
    finally:
        sock.close()    
    return received

def mash(argv = sys.argv[1:]):
    # Initializing command-line arguments
    args = init_parser(argv)
    
    # Set up logging
    logging.basicConfig(level=logging.DEBUG,
                        format='%(asctime)s %(name)-12s %(levelname)-8s %(message)s',
                        datefmt='%d-%m %H:%M:%S',
                        filename=args.log,
                        filemode='w')    
    logger = logging.getLogger('mash')

    if args.quiet:
        logger.setLevel(logging.WARNING)
        #console.setLevel(logging.WARNING)
    else:
        console = logging.StreamHandler(sys.stdout)
        console.setLevel(logging.INFO)
        formatter = logging.Formatter('# %(message)s')
        console.setFormatter(formatter)
        logging.getLogger('').addHandler(console)
        
    if not os.path.exists(args.outputDir):
        os.makedirs(args.outputDir)

    # Shutdown commands need not start the server fist.
    if args.shutdownServer:
        try:
            communicate('shutdown',args.host,args.port)
        except:
            pass
        return

    # If server is not running, start it.
    startedServer = False
    try:
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        sock.connect((args.host,args.port))       
        sock.close()
    except:
        logger.info('Starting Server.')
        spawnDaemon('server.py')
        # TODO: Make this fault tolerant
        time.sleep(0.5)
        startedServer = True
        
    if args.init or startedServer:
        logger.info('Initializing Server.')
        data = "i "+";".join(argv)
        received = communicate(data,args.host,args.port)
        logger.info(received)     
    
    if args.inputFile == None:
        return
    logger.debug('Using the following settings: %s',args)
    # IO Streams
    OS = open(args.predictions,'w')
    IS = open(args.inputFile,'r')
    for line in IS:    
        received = communicate(line,args.host,args.port)
        if not received == '':
            OS.write('%s\n' % received)
    OS.close()
    IS.close()

    # Statistics
    if args.statistics:
        received = communicate('avgStats',args.host,args.port)
        logger.info(received)
    elif args.saveModels:
        communicate('save',args.host,args.port)


if __name__ == "__main__":
    sys.exit(mash())
