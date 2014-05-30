#!/usr/bin/env python
#     Title:      HOL/Tools/Sledgehammer/MaSh/src/server.py
#     Author:     Daniel Kuehlwein, ICIS, Radboud University Nijmegen
#     Copyright   2013
#
# The MaSh Server.

import SocketServer,os,string,logging,sys
from multiprocessing import Manager
from threading import Timer
from time import time
from dictionaries import Dictionaries
from parameters import init_parser
from sparseNaiveBayes import sparseNBClassifier
from KNN import KNN,euclidean
from KNNs import KNNAdaptPointFeatures,KNNUrban
#from bayesPlusMetric import sparseNBPlusClassifier
from predefined import Predefined
from ExpandFeatures import ExpandFeatures
from stats import Statistics


class ThreadingTCPServer(SocketServer.ThreadingTCPServer):
    
    def __init__(self, *args, **kwargs):
        SocketServer.ThreadingTCPServer.__init__(self,*args, **kwargs)
        self.manager = Manager()
        self.lock = Manager().Lock()
        self.idle_timeout = 28800.0 # 8 hours in seconds
        self.idle_timer = Timer(self.idle_timeout, self.shutdown)
        self.idle_timer.start()        
        self.model = None
        self.dicts = None
        self.callCounter = 0
        
    def save(self):
        if self.model == None or self.dicts == None:
            try:
                self.logger.warning('Cannot save nonexisting models.')
            except:
                pass
            return
        # Save Models
        self.model.save(self.args.modelFile)
        self.dicts.save(self.args.dictsFile)
        if not self.args.saveStats == None:
            statsFile = os.path.join(self.args.outputDir,self.args.saveStats)
            self.stats.save(statsFile)   
               
    def save_and_shutdown(self): 
        self.save()          
        self.shutdown()

class MaShHandler(SocketServer.StreamRequestHandler):

    def init(self,argv):
        if argv == '':
            self.server.args = init_parser([])
        else:
            argv = argv.split(';')
            self.server.args = init_parser(argv)

        # Set up logging
        logging.basicConfig(level=logging.DEBUG,
                            format='%(asctime)s %(name)-12s %(levelname)-8s %(message)s',
                            datefmt='%d-%m %H:%M:%S',
                            filename=self.server.args.log+'server',
                            filemode='w')    
        self.server.logger = logging.getLogger('server')
            
        # Load all data
        self.server.dicts = Dictionaries()
        if os.path.isfile(self.server.args.dictsFile):
            self.server.dicts.load(self.server.args.dictsFile)
        #elif not self.server.args.dictsFile == '../tmp/dict.pickle':
        #    raise IOError('Cannot find dictsFile at %s '% self.server.args.dictsFile)        
        elif self.server.args.init:
            self.server.dicts.init_all(self.server.args)
        # Pick model
        if self.server.args.algorithm == 'nb':
            ###TODO: !! 
            self.server.model = sparseNBClassifier(self.server.args.NBDefaultPriorWeight,self.server.args.NBPosWeight,self.server.args.NBDefVal)            
            #self.server.model = sparseNBPlusClassifier(self.server.args.NBDefaultPriorWeight,self.server.args.NBPosWeight,self.server.args.NBDefVal)
        elif self.server.args.algorithm == 'KNN':
            #self.server.model = KNN(self.server.dicts)
            self.server.model = KNNAdaptPointFeatures(self.server.dicts)
        elif self.server.args.algorithm == 'predef':
            self.server.model = Predefined(self.server.args.predef)
        else: # Default case
            self.server.model = sparseNBClassifier(self.server.args.NBDefaultPriorWeight,self.server.args.NBPosWeight,self.server.args.NBDefVal)
        if self.server.args.expandFeatures:
            self.server.expandFeatures = ExpandFeatures(self.server.dicts)
            self.server.expandFeatures.initialize(self.server.dicts)
        # Create Model
        if os.path.isfile(self.server.args.modelFile):
            self.server.model.load(self.server.args.modelFile)          
        #elif not self.server.args.modelFile == '../tmp/model.pickle':
        #    raise IOError('Cannot find modelFile at %s '% self.server.args.modelFile)        
        elif self.server.args.init:
            trainData = self.server.dicts.featureDict.keys()
            self.server.model.initializeModel(trainData,self.server.dicts)
           
        if self.server.args.statistics:
            self.server.stats = Statistics(self.server.args.cutOff)
            self.server.statementCounter = 1
            self.server.computeStats = False

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

        if self.server.args.expandFeatures:
            self.server.expandFeatures.update(self.server.dicts.featureDict[problemId],self.server.dicts.dependenciesDict[problemId])
        # Update Dependencies, p proves p
        if not problemId == 0:
            self.server.dicts.dependenciesDict[problemId] = [problemId]+self.server.dicts.dependenciesDict[problemId]
        ###TODO: 
        self.server.model.update(problemId,self.server.dicts.featureDict[problemId],self.server.dicts.dependenciesDict[problemId])
        #self.server.model.update(problemId,self.server.dicts.featureDict[problemId],self.server.dicts.dependenciesDict[problemId],self.server.dicts)

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
        if self.server.args.expandFeatures:
            features = self.server.expandFeatures.expand(features)
        # Create predictions
        self.server.logger.debug('Starting computation for line %s',self.server.callCounter)
                
        self.server.predictions,predictionValues = self.server.model.predict(features,accessibles,self.server.dicts)
        assert len(self.server.predictions) == len(predictionValues)
        self.server.logger.debug('Time needed: '+str(round(time()-self.startTime,2)))

        # Output        
        predictionNames = [str(self.server.dicts.idNameDict[p]) for p in self.server.predictions[:numberOfPredictions]]
        predictionValues = [str(x) for x in predictionValues[:numberOfPredictions]]
        predictionsStringList = ['%s=%s' % (predictionNames[i],predictionValues[i]) for i in range(len(predictionNames))]
        predictionsString = string.join(predictionsStringList,' ')
        #predictionsString = string.join(predictionNames,' ')        
        outString = '%s: %s' % (name,predictionsString)
        self.request.sendall(outString)
    
    def shutdown(self,saveModels=True):
        self.request.sendall('Shutting down server.')
        if saveModels:
            self.server.save()
        self.server.idle_timer.cancel()
        self.server.idle_timer = Timer(0.5, self.server.shutdown)
        self.server.idle_timer.start()    

    def handle(self):
        # self.request is the TCP socket connected to the client
        self.server.lock.acquire()
        self.data = self.rfile.readline().strip()
        try:
            # Update idle shutdown timer
            self.server.idle_timer.cancel()
            self.server.idle_timer = Timer(self.server.idle_timeout, self.server.save_and_shutdown)
            self.server.idle_timer.start()        

            self.startTime = time()
            if self.data == 'shutdown':
                self.shutdown()         
            elif self.data == 'save':
                self.server.save()       
            elif self.data.startswith('ping'):
                mFile, dFile = self.data.split()[1:]
                if mFile == self.server.args.modelFile and dFile == self.server.args.dictsFile:
                    self.request.sendall('All good.')
                else:
                    self.request.sendall('Files do not match '+' '.join((self.server.args.modelFile,self.server.args.dictsFile)))
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
                return
            elif self.data == 'avgStats':
                self.request.sendall(self.server.stats.printAvg())            
            else:
                self.request.sendall('Unspecified input format: \n%s',self.data)
            self.server.callCounter += 1
            self.request.sendall('stop')                       
        except: # catch exceptions
            #print 'Caught an error. Check %s for more details' % (self.server.args.log+'server')
            logging.exception('')
        finally:
            self.server.lock.release()

if __name__ == "__main__":
    if not len(sys.argv[1:]) == 2:
        print 'No Arguments for HOST and PORT found. Using localhost and 9255'
        HOST, PORT = "localhost", 9255
    else:
        HOST, PORT = sys.argv[1:]
    SocketServer.TCPServer.allow_reuse_address = True
    server = ThreadingTCPServer((HOST, int(PORT)), MaShHandler)
    server.serve_forever()        


    
    
    