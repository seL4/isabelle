#     Title:      HOL/Tools/Sledgehammer/MaSh/src/stats.py
#     Author:     Daniel Kuehlwein, ICIS, Radboud University Nijmegen
#     Copyright   2012
#
# Statistics collector.

'''
Created on Jul 9, 2012

@author: Daniel Kuehlwein
'''

import logging,string
from cPickle import load,dump

class Statistics(object):
    '''
    Class for all the statistics
    '''

    def __init__(self,cutOff=500):
        '''
        Constructor
        '''
        self.logger = logging.getLogger('Statistics')
        self.avgAUC = 0.0
        self.avgRecall100 = 0.0
        self.avgAvailable = 0.0
        self.avgDepNr = 0.0
        self.problems = 0.0
        self.cutOff = cutOff
        self.recallData = [0]*cutOff
        self.recall100Median = []
        self.recall100Data = [0]*cutOff
        self.aucData = []
        self.premiseOccurenceCounter = {}
        self.firstDepAppearance = {}
        self.depAppearances = []

    def update(self,predictions,dependencies,statementCounter):
        """
        Evaluates AUC, dependencies, recall100 and number of available premises of a prediction.
        """
        available = len(predictions)
        predictions = predictions[:self.cutOff]
        dependencies = set(dependencies)
        # No Stats for if no dependencies
        if len(dependencies) == 0:
            self.logger.debug('No Dependencies for statement %s' % statementCounter )
            self.badPreds = []
            return
        if len(predictions) < self.cutOff:
            for i in range(len(predictions),self.cutOff):
                self.recall100Data[i] += 1
                self.recallData[i] += 1
        for d in dependencies:
            if self.premiseOccurenceCounter.has_key(d):
                self.premiseOccurenceCounter[d] += 1
            else:
                self.premiseOccurenceCounter[d] = 1
            if self.firstDepAppearance.has_key(d):
                self.depAppearances.append(statementCounter-self.firstDepAppearance[d])
            else:
                self.firstDepAppearance[d] = statementCounter
        depNr = len(dependencies)
        aucSum = 0.
        posResults = 0.
        positives, negatives = 0, 0
        recall100 = 0.0
        badPreds = []
        depsFound = []
        for index,pId in enumerate(predictions):
            if pId in dependencies:        #positive
                posResults+=1
                positives+=1
                recall100 = index+1
                depsFound.append(pId)
                if index > 200:
                    badPreds.append(pId)
            else:
                aucSum += posResults
                negatives+=1
            # Update Recall and Recall100 stats
            if depNr == positives:
                self.recall100Data[index] += 1
            if depNr == 0:
                self.recallData[index] += 1
            else:
                self.recallData[index] += float(positives)/depNr

        if not depNr == positives:
            depsFound = set(depsFound)
            missing = []
            for dep in dependencies:
                if not dep in depsFound:
                    missing.append(dep)
                    badPreds.append(dep)
                    recall100 = len(predictions)+1
                    positives+=1
            self.logger.debug('Dependencies missing for %s in cutoff predictions! Estimating Statistics.',\
                              string.join([str(dep) for dep in missing],','))

        if positives == 0 or negatives == 0:
            auc = 1.0
        else:
            auc = aucSum/(negatives*positives)

        self.aucData.append(auc)
        self.avgAUC += auc
        self.avgRecall100 += recall100
        self.recall100Median.append(recall100)
        self.problems += 1
        self.badPreds = badPreds
        self.avgAvailable += available
        self.avgDepNr += depNr
        self.logger.info('Statement: %s: AUC: %s \t Needed: %s \t Recall100: %s \t Available: %s \t cutOff: %s',\
                          statementCounter,round(100*auc,2),depNr,recall100,available,self.cutOff)

    def printAvg(self):
        self.logger.info('Average results:')
        #self.logger.info('avgAUC: %s \t avgDepNr: %s \t avgRecall100: %s \t cutOff:%s', \
        #                 round(100*self.avgAUC/self.problems,2),round(self.avgDepNr/self.problems,2),round(self.avgRecall100/self.problems,2),self.cutOff)
        # HACK FOR PAPER
        assert len(self.aucData) == len(self.recall100Median)
        nrDataPoints = len(self.aucData)
        if nrDataPoints == 0:
            return "No data points"
        if nrDataPoints % 2 == 1:
            medianAUC = sorted(self.aucData)[nrDataPoints/2 + 1]
        else:
            medianAUC = float(sorted(self.aucData)[nrDataPoints/2] + sorted(self.aucData)[nrDataPoints/2 + 1])/2
        #nrDataPoints = len(self.recall100Median)
        if nrDataPoints % 2 == 1:
            medianrecall100 = sorted(self.recall100Median)[nrDataPoints/2 + 1]
        else:
            medianrecall100 = float(sorted(self.recall100Median)[nrDataPoints/2] + sorted(self.recall100Median)[nrDataPoints/2 + 1])/2

        returnString = 'avgAUC: %s \t medianAUC: %s \t avgDepNr: %s \t avgRecall100: %s \t medianRecall100: %s \t cutOff: %s' %\
                         (round(100*self.avgAUC/self.problems,2),round(100*medianAUC,2),round(self.avgDepNr/self.problems,2),round(self.avgRecall100/self.problems,2),round(medianrecall100,2),self.cutOff)
        self.logger.info(returnString)
        return returnString
    
        """
        self.logger.info('avgAUC: %s \t medianAUC: %s \t avgDepNr: %s \t avgRecall100: %s \t medianRecall100: %s \t cutOff:%s', \
                         round(100*self.avgAUC/self.problems,2),round(100*medianAUC,2),round(self.avgDepNr/self.problems,2),round(self.avgRecall100/self.problems,2),round(medianrecall100,2),self.cutOff)
        """

    def save(self,fileName):
        oStream = open(fileName, 'wb')
        dump((self.avgAUC,self.avgRecall100,self.avgAvailable,self.avgDepNr,self.problems,self.cutOff,self.recallData,self.recall100Data,self.aucData,self.premiseOccurenceCounter),oStream)
        oStream.close()
    def load(self,fileName):
        iStream = open(fileName, 'rb')
        self.avgAUC,self.avgRecall100,self.avgAvailable,self.avgDepNr,self.problems,self.cutOff,self.recallData,self.recall100Data,self.aucData,self.premiseOccurenceCounter = load(iStream)
        iStream.close()
