#     Title:      HOL/Tools/Sledgehammer/MaSh/src/theoryStats.py
#     Author:     Daniel Kuehlwein, ICIS, Radboud University Nijmegen
#     Copyright   2012
#
# An updatable sparse naive Bayes classifier.

'''
Created on Dec 26, 2012

@author: Daniel Kuehlwein
'''

from cPickle import load,dump
import logging,string

class TheoryStatistics(object):
    '''
    Stores statistics for theory lvl predictions
    '''


    def __init__(self):
        '''
        Constructor
        '''
        self.logger = logging.getLogger('TheoryStatistics')
        self.count = 0
        self.precision = 0.0
        self.recall100 = 0
        self.recall = 0.0
        self.predicted = 0.0
        self.predictedPercent = 0.0
    
    def update(self,currentTheory,predictedTheories,usedTheories,nrAvailableTheories):
        self.count += 1
        allPredTheories = predictedTheories.union([currentTheory])
        if set(usedTheories).issubset(allPredTheories):
            self.recall100 += 1
        localPredicted = len(allPredTheories)
        self.predicted += localPredicted 
        localPredictedPercent = float(localPredicted)/nrAvailableTheories
        self.predictedPercent += localPredictedPercent 
        localPrec = float(len(set(usedTheories).intersection(allPredTheories))) / localPredicted
        self.precision += localPrec
        if len(set(usedTheories)) == 0:
            localRecall = 1.0
        else:
            localRecall = float(len(set(usedTheories).intersection(allPredTheories))) / len(set(usedTheories))
        self.recall += localRecall
        self.logger.info('Theory prediction results:')
        self.logger.info('Problem: %s \t Recall100: %s \t Precision: %s \t Recall: %s \t PredictedTeoriesPercent: %s PredictedTeories: %s',\
                         self.count,self.recall100,round(localPrec,2),round(localRecall,2),round(localPredictedPercent,2),localPredicted)
        
    def printAvg(self):
        self.logger.info('Average theory results:')
        self.logger.info('avgPrecision: %s \t avgRecall100: %s \t avgRecall: %s \t avgPredictedPercent: %s \t avgPredicted: %s', \
                         round(self.precision/self.count,2),\
                         round(float(self.recall100)/self.count,2),\
                         round(self.recall/self.count,2),\
                         round(self.predictedPercent /self.count,2),\
                         round(self.predicted /self.count,2))
        
    def save(self,fileName):
        oStream = open(fileName, 'wb')
        dump((self.count,self.precision,self.recall100,self.recall,self.predicted),oStream)
        oStream.close()
    def load(self,fileName):
        iStream = open(fileName, 'rb')
        self.count,self.precision,self.recall100,self.recall,self.predicted = load(iStream)
        iStream.close()