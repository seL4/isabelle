#     Title:      HOL/Tools/Sledgehammer/MaSh/src/singleNaiveBayes.py
#     Author:     Daniel Kuehlwein, ICIS, Radboud University Nijmegen
#     Copyright   2012
#
# An updatable sparse naive Bayes classifier.

'''
Created on Jul 11, 2012

@author: Daniel Kuehlwein
'''

from cPickle import dump,load
from math import log,exp


class singleNBClassifier(object):
    '''
    An updateable naive Bayes classifier.
    '''

    def __init__(self,defValPos = -7.5,defValNeg = -15.0,posWeight = 10.0):
        '''
        Constructor
        '''
        self.neg = 0.0
        self.pos = 0.0
        self.counts = {} # Counts is the tuple poscounts,negcounts
        self.defValPos = defValPos       
        self.defValNeg = defValNeg
        self.posWeight = posWeight        
    
    def update(self,features,label):
        """
        Updates the Model.
        
        @param label: True or False, True if the features belong to a positive label, false else.
        """
        #print label,self.pos,self.neg,self.counts
        if label:
            self.pos += 1
        else:
            self.neg += 1
        
        for f,_w in features:
            if not self.counts.has_key(f):
                if label:
                    fPosCount = 0.0
                    fNegCount = 0.0
                    self.counts[f] = [fPosCount,fNegCount]
                else:
                    continue
            posCount,negCount = self.counts[f]
            if label:
                posCount += 1
            else:
                negCount += 1
            self.counts[f] = [posCount,negCount]
        #print label,self.pos,self.neg,self.counts
                
 
    def delete(self,features,label):
        """
        Deletes a single datapoint from the model.
        """
        if label:
            self.pos -= 1
        else:
            self.neg -= 1
        for f,_w in features:
            posCount,negCount = self.counts[f]
            if label:
                posCount -= 1
            else:
                negCount -= 1
            self.counts[f] = [posCount,negCount]

            
    def overwrite(self,features,labelOld,labelNew):
        """
        Deletes the old dependencies of problemId and replaces them with the new ones. Updates the model accordingly.
        """
        self.delete(features,labelOld)
        self.update(features,labelNew)
    
    def predict_sparse(self,features):
        """
        Returns 1 if the probability of + being the correct label is greater than the probability that - is the correct label.
        """
        if self.neg == 0:
            return 1
        elif self.pos ==0:
            return 0
        logneg = log(self.neg)
        lognegprior=log(float(self.neg)/5)
        logpos = log(self.pos)
        prob = logpos - lognegprior
        
        for f,_w in features:
            if self.counts.has_key(f):
                posCount,negCount = self.counts[f]
                if posCount > 0:
                    prob += (log(self.posWeight * posCount) - logpos)
                else:
                    prob += self.defValPos
                if negCount > 0:
                    prob -= (log(negCount) - logneg)
                else:
                    prob -= self.defValNeg 
        if prob >= 0 : 
            return 1
        else:
            return 0
    
    def predict(self,features):    
        """
        Returns 1 if the probability is greater than 50%.
        """
        if self.neg == 0:
            return 1
        elif self.pos ==0:
            return 0
        defVal = -15.0       
        expDefVal = exp(defVal)
        
        logneg = log(self.neg)
        logpos = log(self.pos)
        prob = logpos - logneg
        
        for f in self.counts.keys():
            posCount,negCount = self.counts[f]
            if f in features:
                if posCount == 0:
                    prob += defVal
                else:
                    prob += log(float(posCount)/self.pos)
                if negCount == 0:
                    prob -= defVal
                else:
                    prob -= log(float(negCount)/self.neg)
            else:
                if posCount == self.pos:
                    prob += log(1-expDefVal)
                else:
                    prob += log(1-float(posCount)/self.pos)
                if negCount == self.neg:
                    prob -= log(1-expDefVal)
                else:
                    prob -= log(1-float(negCount)/self.neg)

        if prob >= 0 : 
            return 1
        else:
            return 0        
        
    def save(self,fileName):
        OStream = open(fileName, 'wb')
        dump(self.counts,OStream)        
        OStream.close()
        
    def load(self,fileName):
        OStream = open(fileName, 'rb')
        self.counts = load(OStream)      
        OStream.close()

if __name__ == '__main__':
    x = singleNBClassifier()
    x.update([0], True)
    assert x.predict([0]) == 1
    x = singleNBClassifier()
    x.update([0], False)
    assert x.predict([0]) == 0    
    
    x.update([0], True)
    x.update([1], True)
    print x.pos,x.neg,x.predict([0,1])