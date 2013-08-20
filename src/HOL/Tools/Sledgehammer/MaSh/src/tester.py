'''
Created on Jan 11, 2013

Searches for the best parameters.

@author: Daniel Kuehlwein
'''

import logging,sys,os
from multiprocessing import Process,Queue,current_process,cpu_count
from mash import mash

def worker(inQueue, outQueue):
    for func, args in iter(inQueue.get, 'STOP'):        
        result = func(*args)
        #print '%s says that %s%s = %s' % (current_process().name, func.__name__, args, result)
        outQueue.put(result)

def run_mash(runId,inputDir,logFile,predictionFile,predef,\
             learnTheories,theoryDefValPos,theoryDefValNeg,theoryPosWeight,\
             NBDefaultPriorWeight,NBDefVal,NBPosWeight,\
             sineFeatures,sineWeight,quiet=True):
    # Init
    runId = str(runId)
    predictionFile = predictionFile + runId
    args = ['--statistics','--init','--inputDir',inputDir,'--log',logFile,'--theoryFile','../tmp/t'+runId,'--modelFile','../tmp/m'+runId,'--dictsFile','../tmp/d'+runId,
            '--theoryDefValPos',str(theoryDefValPos),'--theoryDefValNeg',str(theoryDefValNeg),'--theoryPosWeight',str(theoryPosWeight),\
            '--NBDefaultPriorWeight',str(NBDefaultPriorWeight),'--NBDefVal',str(NBDefVal),'--NBPosWeight',str(NBPosWeight)]    
    if learnTheories:
        args += ['--learnTheories']    
    if sineFeatures:
        args += ['--sineFeatures','--sineWeight',str(sineWeight)]
    if not predef == '':
        args += ['--predef',predef]
    if quit:
        args += ['-q']
    #print args
    mash(args)
    # Run
    args = ['-i',inputFile,'-p',predictionFile,'--statistics','--cutOff','1024','--log',logFile,'--theoryFile','../tmp/t'+runId,'--modelFile','../tmp/m'+runId,'--dictsFile','../tmp/d'+runId,\
            '--theoryDefValPos',str(theoryDefValPos),'--theoryDefValNeg',str(theoryDefValNeg),'--theoryPosWeight',str(theoryPosWeight),\
            '--NBDefaultPriorWeight',str(NBDefaultPriorWeight),'--NBDefVal',str(NBDefVal),'--NBPosWeight',str(NBPosWeight)]
    if learnTheories:
        args += ['--learnTheories']    
    if sineFeatures:
        args += ['--sineFeatures','--sineWeight',str(sineWeight)]
    if not predef == '':
        args += ['--predef',predef]
    if quit:
        args += ['-q']
    #print args
    mash(args)

    # Get Results
    IS = open(logFile,'r')
    lines =  IS.readlines()
    tmpRes = lines[-1].split()
    avgAuc = tmpRes[5]
    medianAuc = tmpRes[7]
    avgRecall100 = tmpRes[11]
    medianRecall100 = tmpRes[13]
    tmpTheoryRes = lines[-3].split()
    if learnTheories:
        avgTheoryPrecision = tmpTheoryRes[5] 
        avgTheoryRecall100 = tmpTheoryRes[7]
        avgTheoryRecall = tmpTheoryRes[9]
        avgTheoryPredictedPercent = tmpTheoryRes[11]
    else:
        avgTheoryPrecision = 'NA' 
        avgTheoryRecall100 = 'NA'
        avgTheoryRecall = 'NA'
        avgTheoryPredictedPercent = 'NA'    
    IS.close()
    
    # Delete old models
    os.remove(logFile)
    os.remove(predictionFile)
    if learnTheories:
        os.remove('../tmp/t'+runId)
    os.remove('../tmp/m'+runId)
    os.remove('../tmp/d'+runId)
    
    outFile = open('tester','a')
    #print 'avgAuc %s avgRecall100 %s avgTheoryPrecision %s avgTheoryRecall100 %s avgTheoryRecall %s avgTheoryPredictedPercent %s'
    outFile.write('\t'.join([str(learnTheories),str(theoryDefValPos),str(theoryDefValNeg),str(theoryPosWeight),\
                             str(NBDefaultPriorWeight),str(NBDefVal),str(NBPosWeight),str(sineFeatures),str(sineWeight),\
                             str(avgAuc),str(medianAuc),str(avgRecall100),str(medianRecall100),str(avgTheoryPrecision),\
                             str(avgTheoryRecall100),str(avgTheoryRecall),str(avgTheoryPredictedPercent)])+'\n')
    outFile.close()
    print learnTheories,'\t',theoryDefValPos,'\t',theoryDefValNeg,'\t',theoryPosWeight,'\t',\
        NBDefaultPriorWeight,'\t',NBDefVal,'\t',NBPosWeight,'\t',\
        sineFeatures,'\t',sineWeight,'\t',\
        avgAuc,'\t',medianAuc,'\t',avgRecall100,'\t',medianRecall100,'\t',\
        avgTheoryPrecision,'\t',avgTheoryRecall100,'\t',avgTheoryRecall,'\t',avgTheoryPredictedPercent    
    return learnTheories,theoryDefValPos,theoryDefValNeg,theoryPosWeight,\
             NBDefaultPriorWeight,NBDefVal,NBPosWeight,\
             sineFeatures,sineWeight,\
             avgAuc,avgRecall100,avgTheoryPrecision,avgTheoryRecall100,avgTheoryRecall,avgTheoryPredictedPercent 

def update_best_params(avgRecall100,bestAvgRecall100,\
                       bestNBDefaultPriorWeight,bestNBDefVal,bestNBPosWeight,bestSineFeatures,bestSineWeight,\
                       bestlearnTheories,besttheoryDefValPos,besttheoryDefValNeg,besttheoryPosWeight,\
                       NBDefaultPriorWeight,NBDefVal,NBPosWeight,sineFeatures,sineWeight,\
                       learnTheories,theoryDefValPos,theoryDefValNeg,theoryPosWeight):
                        if avgRecall100 > bestAvgRecall100:
                            bestAvgRecall100 = avgRecall100
                            bestNBDefaultPriorWeight = NBDefaultPriorWeight
                            bestNBDefVal = NBDefVal
                            bestNBPosWeight = NBPosWeight
                            bestSineFeatures = sineFeatures
                            bestSineWeight = sineWeight  
                        return bestlearnTheories,besttheoryDefValPos,besttheoryDefValNeg,besttheoryPosWeight,bestNBDefaultPriorWeight,bestNBDefVal,bestNBPosWeight,bestSineFeatures,bestSineWeight

if __name__ == '__main__':
    cores = cpu_count()
    #cores = 1
    # Options
    depFile = 'mash_dependencies'
    predef = ''
    outputDir = '../tmp/'
    numberOfPredictions = 1024
    
    learnTheoriesRange = [True,False]
    theoryDefValPosRange = [-x for x in range(1,20)]
    theoryDefValNegRange = [-x for x in range(1,20)]
    theoryPosWeightRange = [x for x in range(1,10)]
    
    NBDefaultPriorWeightRange = [10*x for x in range(10)]
    NBDefValRange = [-x for x in range(1,20)]
    NBPosWeightRange = [10*x for x in range(1,10)]
    sineFeaturesRange = [True,False]    
    sineWeightRange = [0.1,0.25,0.5,0.75,1.0]
    
    """
    # Test 1
    inputFile = '../data/20121227b/Auth/mash_commands'
    inputDir = '../data/20121227b/Auth/'
    predictionFile = '../tmp/auth.pred'
    logFile = '../tmp/auth.log'
    learnTheories = True
    theoryDefValPos = -7.5
    theoryDefValNeg = -15.0
    theoryPosWeight = 10.0
    NBDefaultPriorWeight = 20.0
    NBDefVal =- 15.0
    NBPosWeight = 10.0
    sineFeatures = True
    sineWeight =  0.5

    task_queue = Queue()
    done_queue = Queue()

    runs = 0
    for inputDir in ['../data/20121227b/Auth/']:
        problemId = inputDir.split('/')[-2]
        inputFile = os.path.join(inputDir,'mash_commands')
        predictionFile = os.path.join('../tmp/',problemId+'.pred')
        logFile = os.path.join('../tmp/',problemId+'.log')
        learnTheories = True
        theoryDefValPos = -7.5
        theoryDefValNeg = -15.0
        theoryPosWeight = 10.0
        
        bestAvgRecall100 = 0.0
        bestNBDefaultPriorWeight = 1.0
        bestNBDefVal = 1.0
        bestNBPosWeight = 1.0
        bestSineFeatures = False
        bestSineWeight = 0.0
        bestlearnTheories = True
        besttheoryDefValPos = 1.0 
        besttheoryDefValNeg = -15.0
        besttheoryPosWeight = 5.0
        for theoryPosWeight in theoryPosWeightRange:
            for theoryDefValNeg in theoryDefValNegRange:
                for NBDefaultPriorWeight in NBDefaultPriorWeightRange:
                    for NBDefVal in NBDefValRange:
                        for NBPosWeight in NBPosWeightRange:
                            for sineFeatures in sineFeaturesRange:
                                if sineFeatures:
                                    for sineWeight in sineWeightRange:  
                                        localLogFile = logFile+str(runs)                           
                                        task_queue.put((run_mash,(runs,inputDir, localLogFile, predictionFile, learnTheories, theoryDefValPos, theoryDefValNeg, theoryPosWeight, NBDefaultPriorWeight, NBDefVal, NBPosWeight, sineFeatures, sineWeight)))
                                        runs += 1
                                else:
                                    localLogFile = logFile+str(runs)
                                    task_queue.put((run_mash,(runs,inputDir, localLogFile, predictionFile, learnTheories, theoryDefValPos, theoryDefValNeg, theoryPosWeight, NBDefaultPriorWeight, NBDefVal, NBPosWeight, sineFeatures, sineWeight)))
                                    runs += 1
        # Start worker processes
        processes = []
        for _i in range(cores):
            process = Process(target=worker, args=(task_queue, done_queue))
            process.start()
            processes.append(process)
    
        for _i in range(runs):      
            learnTheories,theoryDefValPos,theoryDefValNeg,theoryPosWeight,\
             NBDefaultPriorWeight,NBDefVal,NBPosWeight,\
             sineFeatures,sineWeight,\
             avgAuc,avgRecall100,avgTheoryPrecision,avgTheoryRecall100,avgTheoryRecall,avgTheoryPredictedPercent  = done_queue.get()
            bestlearnTheories,besttheoryDefValPos,besttheoryDefValNeg,besttheoryPosWeight,bestNBDefaultPriorWeight,bestNBDefVal,bestNBPosWeight,bestSineFeatures,bestSineWeight = update_best_params(avgRecall100,bestAvgRecall100,\
                       bestNBDefaultPriorWeight,bestNBDefVal,bestNBPosWeight,bestSineFeatures,bestSineWeight,\
                       bestlearnTheories,besttheoryDefValPos,besttheoryDefValNeg,besttheoryPosWeight,\
                       NBDefaultPriorWeight,NBDefVal,NBPosWeight,sineFeatures,sineWeight,\
                       learnTheories,theoryDefValPos,theoryDefValNeg,theoryPosWeight)              
        print 'bestAvgRecall100 %s bestNBDefaultPriorWeight %s bestNBDefVal %s bestNBPosWeight %s bestSineFeatures %s bestSineWeight %s',bestAvgRecall100,bestNBDefaultPriorWeight,bestNBDefVal,bestNBPosWeight,bestSineFeatures,bestSineWeight
    
    """
    # Test 2
    #inputDir = '../data/20130118/Jinja'
    inputDir = '../data/notheory/Prob'
    inputFile = inputDir+'/mash_commands'
    #inputFile = inputDir+'/mash_prover_commands'
    
    #depFile = 'mash_prover_dependencies'
    depFile = 'mash_dependencies'    
    outputDir = '../tmp/'
    numberOfPredictions = 1024
    predictionFile = '../tmp/auth.pred'
    logFile = '../tmp/auth.log'
    learnTheories = False
    theoryDefValPos = -7.5
    theoryDefValNeg = -10.0
    theoryPosWeight = 2.0
    NBDefaultPriorWeight = 20.0
    NBDefVal =- 15.0
    NBPosWeight = 10.0
    sineFeatures = False
    sineWeight =  0.5    
    quiet = False
    print inputDir
    
    #predef = inputDir+'/mash_prover_suggestions'
    predef = inputDir+'/mash_suggestions'    
    print 'Mash Isar'
    run_mash(0,inputDir,logFile,predictionFile,predef,\
             learnTheories,theoryDefValPos,theoryDefValNeg,theoryPosWeight,\
             NBDefaultPriorWeight,NBDefVal,NBPosWeight,\
             sineFeatures,sineWeight,quiet=quiet)

    #"""
    predef = inputDir+'/mesh_suggestions'
    #predef = inputDir+'/mesh_prover_suggestions'
    print 'Mesh Isar'
    run_mash(0,inputDir,logFile,predictionFile,predef,\
             learnTheories,theoryDefValPos,theoryDefValNeg,theoryPosWeight,\
             NBDefaultPriorWeight,NBDefVal,NBPosWeight,\
             sineFeatures,sineWeight,quiet=quiet)
    #"""
    predef = inputDir+'/mepo_suggestions'
    print 'Mepo Isar'
    run_mash(0,inputDir,logFile,predictionFile,predef,\
             learnTheories,theoryDefValPos,theoryDefValNeg,theoryPosWeight,\
             NBDefaultPriorWeight,NBDefVal,NBPosWeight,\
             sineFeatures,sineWeight,quiet=quiet)    
    
    """
    inputFile = inputDir+'/mash_prover_commands'
    depFile = 'mash_prover_dependencies'
    
    predef = inputDir+'/mash_prover_suggestions'    
    print 'Mash Prover Isar'
    run_mash(0,inputDir,logFile,predictionFile,predef,\
             learnTheories,theoryDefValPos,theoryDefValNeg,theoryPosWeight,\
             NBDefaultPriorWeight,NBDefVal,NBPosWeight,\
             sineFeatures,sineWeight,quiet=quiet)

    predef = inputDir+'/mesh_prover_suggestions'
    print 'Mesh Prover Isar'
    run_mash(0,inputDir,logFile,predictionFile,predef,\
             learnTheories,theoryDefValPos,theoryDefValNeg,theoryPosWeight,\
             NBDefaultPriorWeight,NBDefVal,NBPosWeight,\
             sineFeatures,sineWeight,quiet=quiet)

    predef = inputDir+'/mepo_suggestions'
    print 'Mepo Prover Isar'
    run_mash(0,inputDir,logFile,predictionFile,predef,\
             learnTheories,theoryDefValPos,theoryDefValNeg,theoryPosWeight,\
             NBDefaultPriorWeight,NBDefVal,NBPosWeight,\
             sineFeatures,sineWeight,quiet=quiet)
    #"""