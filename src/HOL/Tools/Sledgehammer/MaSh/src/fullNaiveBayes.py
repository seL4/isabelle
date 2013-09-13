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
        self.negCounts = {}
    
    def initializeModel(self,trainData,dicts):
        """
        Build basic model from training data.
        """        
        for d in trainData:
            self.counts[d] = [0,{}]
            self.negCounts[d] = [0,{}]
            dAccUnExp = dicts.accessibleDict[d]
            if dicts.expandedAccessibles.has_key(d):
                dAcc = dicts.expandedAccessibles(d)
            else:
                if len(dicts.expandedAccessibles.keys()) >= 100:
                    dicts.expandedAccessibles = {}
                dAcc = dicts.expand_accessibles(dAccUnExp)
                dicts.expandedAccessibles[d] = dAcc 
            dDeps = set(dicts.dependenciesDict[d])
            dFeatures = dicts.featureDict[d]
            # d proves d
            self.counts[d][0] += 1
            for f in dFeatures:
                if self.counts[d][1].has_key(f):
                    self.counts[d][1][f] += 1
                else:
                    self.counts[d][1][f] = 1
            for acc in dAcc:
                if not self.counts.has_key(acc):
                    self.counts[acc] = [0,{}]
                if not self.negCounts.has_key(acc):
                    self.negCounts[acc] = [0,{}]        
                if acc in dDeps:
                    self.counts[acc][0] += 1
                    for f in dFeatures:
                        if self.counts[acc][1].has_key(f):
                            self.counts[acc][1][f] += 1
                        else:
                            self.counts[acc][1][f] = 1
                else:
                    self.negCounts[acc][0] += 1
                    for f in dFeatures:
                        if self.negCounts[acc][1].has_key(f):
                            self.negCounts[acc][1][f] += 1
                        else:
                            self.negCounts[acc][1][f] = 1
    
    def update(self,dataPoint,features,dependencies,dicts):
        """
        Updates the Model.
        """
        if not self.counts.has_key(dataPoint):
            self.counts[dataPoint] = [0,{}]
        if not self.negCounts.has_key(dataPoint):
            self.negCounts[dataPoint] = [0,{}]
        if dicts.expandedAccessibles.has_key(dataPoint):
            dAcc = dicts.expandedAccessibles(dataPoint)
        else:
            if len(dicts.expandedAccessibles.keys()) >= 100:
                dicts.expandedAccessibles = {}
            dAccUnExp = dicts.accessibleDict[dataPoint]
            dAcc = dicts.expand_accessibles(dAccUnExp)
            dicts.expandedAccessibles[dataPoint] = dAcc 
        dDeps = set(dicts.dependenciesDict[dataPoint])
        dFeatures = dicts.featureDict[dataPoint]
        # d proves d
        self.counts[dataPoint][0] += 1
        for f in dFeatures:
            if self.counts[dataPoint][1].has_key(f):
                self.counts[dataPoint][1][f] += 1
            else:
                self.counts[dataPoint][1][f] = 1

        for acc in dAcc:
            if acc in dDeps:
                self.counts[acc][0] += 1
                for f in dFeatures:
                    if self.counts[acc][1].has_key(f):
                        self.counts[acc][1][f] += 1
                    else:
                        self.counts[acc][1][f] = 1
            else:
                self.negCounts[acc][0] += 1
                for f in dFeatures:
                    if self.negCounts[acc][1].has_key(f):
                        self.negCounts[acc][1][f] += 1
                    else:
                        self.negCounts[acc][1][f] = 1

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
            negA = self.negCounts[a][0]
            fPosA = set(self.counts[a][1].keys())
            fNegA = set(self.negCounts[a][1].keys())
            fPosWeightsA = self.counts[a][1]
            fNegWeightsA = self.negCounts[a][1]
            if negA == 0:
                resultA = 0 
            elif posA == 0:
                print a
                print 'xx'
                import sys
                sys.exit(-1)
            else:
                resultA = log(posA) - log(negA) 
                for f in features:
                    if f in fPosA:
                        # P(f | a)
                        if fPosWeightsA[f] == 0:
                            resultA -= 15
                        else:
                            assert fPosWeightsA[f] <= posA
                            resultA += log(float(fPosWeightsA[f])/posA)
                    else:
                        resultA -= 15
                    # P(f | not a)
                    if f in fNegA:
                        if fNegWeightsA[f] == 0:
                            resultA += 15
                        else:
                            assert fNegWeightsA[f] <= negA
                            resultA -= log(float(fNegWeightsA[f])/negA)
                    else: 
                        resultA += 15

            predictions.append(resultA)
        #expPredictions = array([exp(x) for x in predictions])
        predictions = array(predictions)
        perm = (-predictions).argsort()        
        #return array(accessibles)[perm],expPredictions[perm] 
        return array(accessibles)[perm],predictions[perm]
    
    def save(self,fileName):
        OStream = open(fileName, 'wb')
        dump((self.counts,self.negCounts),OStream)        
        OStream.close()
        
    def load(self,fileName):
        OStream = open(fileName, 'rb')
        self.counts,self.negCounts = load(OStream)      
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