#!/usr/bin/env python
#     Title:      HOL/Tools/Sledgehammer/MaSh/src/server.py
#     Author:     Daniel Kuehlwein, ICIS, Radboud University Nijmegen
#     Copyright   2013
#
# The MaSh Server.

import SocketServer,os,string,logging
from multiprocessing import Manager
from time import time
from dictionaries import Dictionaries
from parameters import init_parser
from sparseNaiveBayes import sparseNBClassifier
from stats import Statistics


class ThreadingTCPServer(SocketServer.ThreadingTCPServer): 
    def __init__(self, *args, **kwargs):
        SocketServer.ThreadingTCPServer.__init__(self,*args, **kwargs)
        self.manager = Manager()
        self.lock = Manager().Lock()

class MaShHandler(SocketServer.BaseRequestHandler):

    def init(self,argv):
        if argv == '':
            self.server.args = init_parser([])
        else:
            argv = argv.split(';')
            self.server.args = init_parser(argv)
        # Pick model
        if self.server.args.algorithm == 'nb':
            self.server.model = sparseNBClassifier(self.server.args.NBDefaultPriorWeight,self.server.args.NBPosWeight,self.server.args.NBDefVal)
        else: # Default case
            self.server.model = sparseNBClassifier(self.server.args.NBDefaultPriorWeight,self.server.args.NBPosWeight,self.server.args.NBDefVal)
        # Load all data
        # TODO: rewrite dicts for concurrency and without sine
        self.server.dicts = Dictionaries()
        if os.path.isfile(self.server.args.dictsFile):
            self.server.dicts.load(self.server.args.dictsFile)            
        elif self.server.args.init:
            self.server.dicts.init_all(self.server.args)
        # Create Model
        if os.path.isfile(self.server.args.modelFile):
            self.server.model.load(self.server.args.modelFile)          
        elif self.server.args.init:
            trainData = self.server.dicts.featureDict.keys()
            self.server.model.initializeModel(trainData,self.server.dicts)
            
        if self.server.args.statistics:
            self.server.stats = Statistics(self.server.args.cutOff)
            self.server.statementCounter = 1
            self.server.computeStats = False

        # Set up logging
        logging.basicConfig(level=logging.DEBUG,
                            format='%(asctime)s %(name)-12s %(levelname)-8s %(message)s',
                            datefmt='%d-%m %H:%M:%S',
                            filename=self.server.args.log+'server',
                            filemode='w')    
        self.server.logger = logging.getLogger('server')
        self.server.logger.debug('Initialized in '+str(round(time()-self.startTime,2))+' seconds.')
        self.request.sendall('Server initialized in '+str(round(time()-self.startTime,2))+' seconds.')
        self.server.callCounter = 1

    def update(self):
        problemId = self.server.dicts.parse_fact(self.data)    
        # Statistics
        if self.server.args.statistics and self.server.computeStats:
            self.server.computeStats = False
            # Assume '!' comes after '?'
            if self.server.args.algorithm == 'predef':
                self.server.predictions = self.server.model.predict(problemId)
            self.server.stats.update(self.server.predictions,self.server.dicts.dependenciesDict[problemId],self.server.statementCounter)
            if not self.server.stats.badPreds == []:
                bp = string.join([str(self.server.dicts.idNameDict[x]) for x in self.server.stats.badPreds], ',')
                self.server.logger.debug('Poor predictions: %s',bp)
            self.server.statementCounter += 1

        # Update Dependencies, p proves p
        self.server.dicts.dependenciesDict[problemId] = [problemId]+self.server.dicts.dependenciesDict[problemId]
        self.server.model.update(problemId,self.server.dicts.featureDict[problemId],self.server.dicts.dependenciesDict[problemId])

    def overwrite(self):
        # Overwrite old proof.
        problemId,newDependencies = self.server.dicts.parse_overwrite(self.data)
        newDependencies = [problemId]+newDependencies
        self.server.model.overwrite(problemId,newDependencies,self.server.dicts)
        self.server.dicts.dependenciesDict[problemId] = newDependencies
        
    def predict(self):
        self.server.computeStats = True
        if self.server.args.algorithm == 'predef':
            return
        name,features,accessibles,hints,numberOfPredictions = self.server.dicts.parse_problem(self.data)  
        if numberOfPredictions == None:
            numberOfPredictions = self.server.args.numberOfPredictions
        if not hints == []:
            self.server.model.update('hints',features,hints)
        
        # Create predictions
        self.server.logger.debug('Starting computation for line %s',self.server.callCounter)
        predictionsFeatures = features                    
        self.server.predictions,predictionValues = self.server.model.predict(predictionsFeatures,accessibles,self.server.dicts)
        assert len(self.server.predictions) == len(predictionValues)
        self.server.logger.debug('Time needed: '+str(round(time()-self.startTime,2)))

        # Output        
        predictionNames = [str(self.server.dicts.idNameDict[p]) for p in self.server.predictions[:numberOfPredictions]]
        predictionValues = [str(x) for x in predictionValues[:numberOfPredictions]]
        predictionsStringList = ['%s=%s' % (predictionNames[i],predictionValues[i]) for i in range(len(predictionNames))]
        predictionsString = string.join(predictionsStringList,' ')
        outString = '%s: %s' % (name,predictionsString)
        self.request.sendall(outString)
    
    def shutdown(self,saveModels=True):
        self.request.sendall('Shutting down server.')
        if saveModels:
            self.save()
        self.server.shutdown()
    
    def save(self):
        # Save Models
        self.server.model.save(self.server.args.modelFile)
        self.server.dicts.save(self.server.args.dictsFile)
        if not self.server.args.saveStats == None:
            statsFile = os.path.join(self.server.args.outputDir,self.server.args.saveStats)
            self.server.stats.save(statsFile)
    
    def handle(self):
        # self.request is the TCP socket connected to the client
        self.data = self.request.recv(4194304).strip()
        self.server.lock.acquire()
        #print "{} wrote:".format(self.client_address[0])
        self.startTime = time()  
        if self.data == 'shutdown':
            self.shutdown()         
        elif self.data == 'save':
            self.save()       
        elif self.data.startswith('i'):            
            self.init(self.data[2:])
        elif self.data.startswith('!'):
            self.update()
        elif self.data.startswith('p'):
            self.overwrite()
        elif self.data.startswith('?'):               
            self.predict()
        elif self.data == '':
            # Empty Socket
            self.server.lock.release()
            return
        elif self.data == 'avgStats':
            self.request.sendall(self.server.stats.printAvg())            
        else:
            self.request.sendall('Unspecified input format: \n%s',self.data)
        self.server.callCounter += 1
        self.server.lock.release()

if __name__ == "__main__":
    HOST, PORT = "localhost", 9255
    #print 'Started Server'
    # Create the server, binding to localhost on port 9999
    SocketServer.TCPServer.allow_reuse_address = True
    server = ThreadingTCPServer((HOST, PORT), MaShHandler)
    #server = SocketServer.TCPServer((HOST, PORT), MaShHandler)

    # Activate the server; this will keep running until you
    # interrupt the program with Ctrl-C
    server.serve_forever()        



    
    
    