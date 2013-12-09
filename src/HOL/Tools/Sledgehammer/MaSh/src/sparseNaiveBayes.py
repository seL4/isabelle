#     Title:      HOL/Tools/Sledgehammer/MaSh/src/sparseNaiveBayes.py
#     Author:     Daniel Kuehlwein, ICIS, Radboud University Nijmegen
#     Copyright   2012
#
# An updatable sparse naive Bayes classifier.

'''
Created on Jul 11, 2012

@author: Daniel Kuehlwein
'''
from cPickle import dump,load
from numpy import array
from math import log

class sparseNBClassifier(object):
    '''
    An updateable naive Bayes classifier.
    '''

    def __init__(self,defaultPriorWeight = 20.0,posWeight = 20.0,defVal = -15.0):
        '''
        Constructor
        '''
        self.counts = {}
        self.defaultPriorWeight = defaultPriorWeight
        self.posWeight = posWeight
        self.defVal = defVal

    def initializeModel(self,trainData,dicts):
        """
        Build basic model from training data.
        """
        for d in trainData:            
            dFeatureCounts = {}
            # Add p proves p with weight self.defaultPriorWeight
            if not self.defaultPriorWeight == 0:            
                for f in dicts.featureDict[d].iterkeys():
                    dFeatureCounts[f] = self.defaultPriorWeight
            self.counts[d] = [self.defaultPriorWeight,dFeatureCounts]

        for key,keyDeps in dicts.dependenciesDict.iteritems():
            keyFeatures = dicts.featureDict[key]
            for dep in keyDeps:
                self.counts[dep][0] += 1
                #depFeatures = dicts.featureDict[key]
                for f in keyFeatures.iterkeys():
                    if self.counts[dep][1].has_key(f):
                        self.counts[dep][1][f] += 1
                    else:
                        self.counts[dep][1][f] = 1


    def update(self,dataPoint,features,dependencies):
        """
        Updates the Model.
        """
        if (not self.counts.has_key(dataPoint)) and (not dataPoint == 0):
            dFeatureCounts = {}            
            # Give p |- p a higher weight
            if not self.defaultPriorWeight == 0:               
                for f in features.iterkeys():
                    dFeatureCounts[f] = self.defaultPriorWeight
            self.counts[dataPoint] = [self.defaultPriorWeight,dFeatureCounts]            
        for dep in dependencies:
            self.counts[dep][0] += 1
            for f in features.iterkeys():
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
            for f,_w in features.items():
                self.counts[dep][1][f] -= 1
                if self.counts[dep][1][f] == 0:
                    del self.counts[dep][1][f]


    def overwrite(self,problemId,newDependencies,dicts):
        """
        Deletes the old dependencies of problemId and replaces them with the new ones. Updates the model accordingly.
        """
        try:
            assert self.counts.has_key(problemId)
        except:
            raise LookupError('Trying to overwrite dependencies for unknown fact: %s. Facts need to be introduced before overwriting them.' % dicts.idNameDict[problemId])
        oldDeps = dicts.dependenciesDict[problemId]
        features = dicts.featureDict[problemId]
        self.delete(problemId,features,oldDeps)
        self.update(problemId,features,newDependencies)

    def predict(self,features,accessibles,dicts):
        """
        For each accessible, predicts the probability of it being useful given the features.
        Returns a ranking of the accessibles.
        """
        tau = 0.05 # Jasmin, change value here
        predictions = []
        observedFeatures = features.keys()
        for fVal in features.itervalues():
            _w,alternateF = fVal
            observedFeatures += alternateF
            
        for a in accessibles:
            posA = self.counts[a][0]
            fA = set(self.counts[a][1].keys())
            fWeightsA = self.counts[a][1]
            resultA = log(posA)
            for f,fVal in features.iteritems():
                w,alternateF = fVal
                # DEBUG
                #w = 1.0
                # Test for multiple features
                isMatch = False
                matchF = None
                if f in fA:
                    isMatch = True
                    matchF = f
                elif len(alternateF) > 0:
                    inter = set(alternateF).intersection(fA)
                    if len(inter) > 0:
                        isMatch = True
                        for mF in inter:
                            ### TODO: matchF is randomly selected
                            matchF = mF
                            break
                 
                if isMatch:
                #if f in fA:
                    if fWeightsA[matchF] == 0:
                        resultA += w*self.defVal
                    else:
                        assert fWeightsA[matchF] <= posA
                        resultA += w*log(float(self.posWeight*fWeightsA[matchF])/posA)
                else:
                    resultA += w*self.defVal
            if not tau == 0.0:
                missingFeatures = list(fA.difference(observedFeatures))
                #sumOfWeights = sum([log(float(fWeightsA[x])/posA) for x in missingFeatures])  # slower
                sumOfWeights = sum([log(float(fWeightsA[x])) for x in missingFeatures]) - log(posA) * len(missingFeatures) #DEFAULT
                #sumOfWeights = sum([log(float(fWeightsA[x])/self.totalFeatureCounts[x]) for x in missingFeatures]) - log(posA) * len(missingFeatures)
                resultA -= tau * sumOfWeights
            predictions.append(resultA)
        predictions = array(predictions)
        perm = (-predictions).argsort()
        return array(accessibles)[perm],predictions[perm]

    def save(self,fileName):
        OStream = open(fileName, 'wb')
        dump((self.counts,self.defaultPriorWeight,self.posWeight,self.defVal),OStream)
        OStream.close()

    def load(self,fileName):
        OStream = open(fileName, 'rb')
        self.counts,self.defaultPriorWeight,self.posWeight,self.defVal = load(OStream)
        OStream.close()


if __name__ == '__main__':
    featureDict = {0:[0,1,2],1:[3,2,1]}
    dependenciesDict = {0:[0],1:[0,1]}
    libDicts = (featureDict,dependenciesDict,{})
    c = sparseNBClassifier()
    c.initializeModel([0,1],libDicts)
    c.update(2,[14,1,3],[0,2])
    print c.counts
    print c.predict([0,14],[0,1,2])
    c.storeModel('x')
    d = sparseNBClassifier()
    d.loadModel('x')
    print c.counts
    print d.counts
    print 'Done'
