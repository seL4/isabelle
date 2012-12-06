#     Title:      HOL/Tools/Sledgehammer/MaSh/src/naiveBayes.py
#     Author:     Daniel Kuehlwein, ICIS, Radboud University Nijmegen
#     Copyright   2012
#
# An updatable naive Bayes classifier.

'''
Created on Jul 11, 2012

@author: Daniel Kuehlwein
'''

from cPickle import dump,load
from numpy import array,exp
from math import log

class NBClassifier(object):
    '''
    An updateable naive Bayes classifier.
    '''

    def __init__(self):
        '''
        Constructor
        '''
        self.counts = {}

    def initializeModel(self,trainData,dicts):
        """
        Build basic model from training data.
        """
        for d in trainData:
            dPosCount = 0
            dFeatureCounts = {}
            self.counts[d] = [dPosCount,dFeatureCounts]

        for key in dicts.dependenciesDict.keys():
            # Add p proves p
            keyDeps = [key]+dicts.dependenciesDict[key]

            for dep in keyDeps:
                self.counts[dep][0] += 1
                depFeatures = dicts.featureDict[key]
                for f,_w in depFeatures:
                    if self.counts[dep][1].has_key(f):
                        self.counts[dep][1][f] += 1
                    else:
                        self.counts[dep][1][f] = 1


    def update(self,dataPoint,features,dependencies):
        """
        Updates the Model.
        """
        if not self.counts.has_key(dataPoint):
            dPosCount = 0
            dFeatureCounts = {}
            self.counts[dataPoint] = [dPosCount,dFeatureCounts]
        for dep in dependencies:
            self.counts[dep][0] += 1
            for f,_w in features:
                if self.counts[dep][1].has_key(f):
                    self.counts[dep][1][f] += 1
                else:
                    self.counts[dep][1][f] = 1

    def delete(self,dataPoint,features,dependencies):
        """
        Deletes a single datapoint from the model.
        """
        for dep in dependencies:
            self.counts[dep][0] -= 1
            for f in features:
                self.counts[dep][1][f] -= 1


    def overwrite(self,problemId,newDependencies,dicts):
        """
        Deletes the old dependencies of problemId and replaces them with the new ones. Updates the model accordingly.
        """
        assert self.counts.has_key(problemId)
        oldDeps = dicts.dependenciesDict[problemId]
        features = dicts.featureDict[problemId]
        self.delete(problemId,features,oldDeps)
        self.update(problemId,features,newDependencies)

    def predict(self,features,accessibles):
        """
        For each accessible, predicts the probability of it being useful given the features.
        Returns a ranking of the accessibles.
        """
        predictions = []
        for a in accessibles:
            posA = self.counts[a][0]
            fA = set(self.counts[a][1].keys())
            fWeightsA = self.counts[a][1]
            resultA = log(posA)
            for f,w in features:
                if f in fA:
                    if fWeightsA[f] == 0:
                        resultA -= w*15
                    else:
                        assert fWeightsA[f] <= posA
                        resultA += w*log(float(fWeightsA[f])/posA)
                else:
                    resultA -= w*15
            predictions.append(resultA)
        #expPredictions = array([exp(x) for x in predictions])
        predictions = array(predictions)
        perm = (-predictions).argsort()
        #return array(accessibles)[perm],expPredictions[perm]
        return array(accessibles)[perm],predictions[perm]

    def save(self,fileName):
        OStream = open(fileName, 'wb')
        dump(self.counts,OStream)
        OStream.close()

    def load(self,fileName):
        OStream = open(fileName, 'rb')
        self.counts = load(OStream)
        OStream.close()


if __name__ == '__main__':
    featureDict = {0:[0,1,2],1:[3,2,1]}
    dependenciesDict = {0:[0],1:[0,1]}
    libDicts = (featureDict,dependenciesDict,{})
    c = NBClassifier()
    c.initializeModel([0,1],libDicts)
    c.update(2,[14,1,3],[0,2])
    print c.counts
    print c.predict([0,14],[0,1,2])
    c.storeModel('x')
    d = NBClassifier()
    d.loadModel('x')
    print c.counts
    print d.counts
    print 'Done'
