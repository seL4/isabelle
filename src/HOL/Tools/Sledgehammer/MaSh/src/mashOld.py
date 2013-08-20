#!/usr/bin/python
#     Title:      HOL/Tools/Sledgehammer/MaSh/src/mash.py
#     Author:     Daniel Kuehlwein, ICIS, Radboud University Nijmegen
#     Copyright   2012
#
# Entry point for MaSh (Machine Learning for Sledgehammer).

'''
MaSh - Machine Learning for Sledgehammer

MaSh allows to use different machine learning algorithms to predict relevant fact for Sledgehammer.

Created on July 12, 2012

@author: Daniel Kuehlwein
'''

import logging,datetime,string,os,sys
from argparse import ArgumentParser,RawDescriptionHelpFormatter
from time import time
from stats import Statistics
from theoryStats import TheoryStatistics
from theoryModels import TheoryModels
from dictionaries import Dictionaries
#from fullNaiveBayes import NBClassifier
from sparseNaiveBayes import sparseNBClassifier
from snow import SNoW
from predefined import Predefined

# Set up command-line parser
parser = ArgumentParser(description='MaSh - Machine Learning for Sledgehammer.  \n\n\
MaSh allows to use different machine learning algorithms to predict relevant facts for Sledgehammer.\n\n\
--------------- Example Usage ---------------\n\
First initialize:\n./mash.py -l test.log -o ../tmp/ --init --inputDir ../data/Jinja/ \n\
Then create predictions:\n./mash.py -i ../data/Jinja/mash_commands -p ../data/Jinja/mash_suggestions -l test.log -o ../tmp/ --statistics\n\
\n\n\
Author: Daniel Kuehlwein, July 2012',formatter_class=RawDescriptionHelpFormatter)
parser.add_argument('-i','--inputFile',help='File containing all problems to be solved.')
parser.add_argument('-o','--outputDir', default='../tmp/',help='Directory where all created files are stored. Default=../tmp/.')
parser.add_argument('-p','--predictions',default='../tmp/%s.predictions' % datetime.datetime.now(),
                    help='File where the predictions stored. Default=../tmp/dateTime.predictions.')
parser.add_argument('--numberOfPredictions',default=200,help="Number of premises to write in the output. Default=200.",type=int)

parser.add_argument('--init',default=False,action='store_true',help="Initialize Mash. Requires --inputDir to be defined. Default=False.")
parser.add_argument('--inputDir',default='../data/20121212/Jinja/',\
                    help='Directory containing all the input data. MaSh expects the following files: mash_features,mash_dependencies,mash_accessibility')
parser.add_argument('--depFile', default='mash_dependencies',
                    help='Name of the file with the premise dependencies. The file must be in inputDir. Default = mash_dependencies')
parser.add_argument('--saveModel',default=False,action='store_true',help="Stores the learned Model at the end of a prediction run. Default=False.")

parser.add_argument('--learnTheories',default=False,action='store_true',help="Uses a two-lvl prediction mode. First the theories, then the premises. Default=False.")
# Theory Parameters
parser.add_argument('--theoryDefValPos',default=-7.5,help="Default value for positive unknown features. Default=-7.5.",type=float)
parser.add_argument('--theoryDefValNeg',default=-10.0,help="Default value for negative unknown features. Default=-15.0.",type=float)
parser.add_argument('--theoryPosWeight',default=2.0,help="Weight value for positive features. Default=2.0.",type=float)

parser.add_argument('--nb',default=False,action='store_true',help="Use Naive Bayes for learning. This is the default learning method.")
# NB Parameters
parser.add_argument('--NBDefaultPriorWeight',default=20.0,help="Initializes classifiers with value * p |- p. Default=20.0.",type=float)
parser.add_argument('--NBDefVal',default=-15.0,help="Default value for unknown features. Default=-15.0.",type=float)
parser.add_argument('--NBPosWeight',default=10.0,help="Weight value for positive features. Default=10.0.",type=float)
# TODO: Rename to sineFeatures
parser.add_argument('--sineFeatures',default=False,action='store_true',help="Uses a SInE like prior for premise lvl predictions. Default=False.")
parser.add_argument('--sineWeight',default=0.5,help="How much the SInE prior is weighted. Default=0.5.",type=float)

parser.add_argument('--snow',default=False,action='store_true',help="Use SNoW's naive bayes instead of Naive Bayes for learning.")
parser.add_argument('--predef',help="Use predefined predictions. Used only for comparison with the actual learning. Argument is the filename of the predictions.")
parser.add_argument('--statistics',default=False,action='store_true',help="Create and show statistics for the top CUTOFF predictions.\
                    WARNING: This will make the program a lot slower! Default=False.")
parser.add_argument('--saveStats',default=None,help="If defined, stores the statistics in the filename provided.")
parser.add_argument('--cutOff',default=500,help="Option for statistics. Only consider the first cutOff predictions. Default=500.",type=int)
parser.add_argument('-l','--log', default='../tmp/%s.log' % datetime.datetime.now(), help='Log file name. Default=../tmp/dateTime.log')
parser.add_argument('-q','--quiet',default=False,action='store_true',help="If enabled, only print warnings. Default=False.")
parser.add_argument('--modelFile', default='../tmp/model.pickle', help='Model file name. Default=../tmp/model.pickle')
parser.add_argument('--dictsFile', default='../tmp/dict.pickle', help='Dict file name. Default=../tmp/dict.pickle')
parser.add_argument('--theoryFile', default='../tmp/theory.pickle', help='Model file name. Default=../tmp/theory.pickle')

def mash(argv = sys.argv[1:]):
    # Initializing command-line arguments
    args = parser.parse_args(argv)
    
    # Set up logging
    logging.basicConfig(level=logging.DEBUG,
                        format='%(asctime)s %(name)-12s %(levelname)-8s %(message)s',
                        datefmt='%d-%m %H:%M:%S',
                        filename=args.log,
                        filemode='w')    
    logger = logging.getLogger('main.py')
    
    """
    # remove old handler for tester
    # TODO: Comment out for Jasmins version. This crashes python 2.6.1
    logger.root.handlers[0].stream.close()
    logger.root.removeHandler(logger.root.handlers[0])
    file_handler = logging.FileHandler(args.log)
    file_handler.setLevel(logging.DEBUG)
    formatter = logging.Formatter('%(asctime)s %(name)-12s %(levelname)-8s %(message)s')
    file_handler.setFormatter(formatter)
    logger.root.addHandler(file_handler)
    #"""
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

    logger.info('Using the following settings: %s',args)
    # Pick algorithm
    if args.nb:
        logger.info('Using sparse Naive Bayes for learning.')
        model = sparseNBClassifier(args.NBDefaultPriorWeight,args.NBPosWeight,args.NBDefVal)
    elif args.snow:
        logger.info('Using naive bayes (SNoW) for learning.')
        model = SNoW()
    elif args.predef:
        logger.info('Using predefined predictions.')
        model = Predefined(args.predef)
    else:
        logger.info('No algorithm specified. Using sparse Naive Bayes.')
        model = sparseNBClassifier(args.NBDefaultPriorWeight,args.NBPosWeight,args.NBDefVal)

    # Initializing model
    if args.init:
        logger.info('Initializing Model.')
        startTime = time()

        # Load all data
        dicts = Dictionaries()
        dicts.init_all(args)
        
        # Create Model
        trainData = dicts.featureDict.keys()
        model.initializeModel(trainData,dicts)

        if args.learnTheories:
            depFile = os.path.join(args.inputDir,args.depFile)
            theoryModels = TheoryModels(args.theoryDefValPos,args.theoryDefValNeg,args.theoryPosWeight)
            theoryModels.init(depFile,dicts)
            theoryModels.save(args.theoryFile)
            
        model.save(args.modelFile)
        dicts.save(args.dictsFile)

        logger.info('All Done. %s seconds needed.',round(time()-startTime,2))
        return 0
    # Create predictions and/or update model
    else:
        lineCounter = 1
        statementCounter = 1
        computeStats = False
        dicts = Dictionaries()
        theoryModels = TheoryModels(args.theoryDefValPos,args.theoryDefValNeg,args.theoryPosWeight)
        # Load Files
        if os.path.isfile(args.dictsFile):
            #logger.info('Loading Dictionaries')
            #startTime = time()
            dicts.load(args.dictsFile)            
            #logger.info('Done %s',time()-startTime)
        if os.path.isfile(args.modelFile):
            #logger.info('Loading Model')
            #startTime = time()
            model.load(args.modelFile)            
            #logger.info('Done %s',time()-startTime)
        if os.path.isfile(args.theoryFile) and args.learnTheories:
            #logger.info('Loading Theory Models')
            #startTime = time()
            theoryModels.load(args.theoryFile)
            #logger.info('Done %s',time()-startTime)
        logger.info('All loading completed')

        # IO Streams
        OS = open(args.predictions,'w')
        IS = open(args.inputFile,'r')

        # Statistics
        if args.statistics:
            stats = Statistics(args.cutOff)
            if args.learnTheories:
                theoryStats = TheoryStatistics()

        predictions = None
        predictedTheories = None
        #Reading Input File
        for line in IS:
#           try:
            if True:
                if line.startswith('!'):
                    problemId = dicts.parse_fact(line)    
                    # Statistics
                    if args.statistics and computeStats:
                        computeStats = False
                        # Assume '!' comes after '?'
                        if args.predef:
                            predictions = model.predict(problemId)
                        if args.learnTheories:
                            tmp = [dicts.idNameDict[x] for x in dicts.dependenciesDict[problemId]]
                            usedTheories = set([x.split('.')[0] for x in tmp]) 
                            theoryStats.update((dicts.idNameDict[problemId]).split('.')[0],predictedTheories,usedTheories,len(theoryModels.accessibleTheories))                        
                        stats.update(predictions,dicts.dependenciesDict[problemId],statementCounter)
                        if not stats.badPreds == []:
                            bp = string.join([str(dicts.idNameDict[x]) for x in stats.badPreds], ',')
                            logger.debug('Bad predictions: %s',bp)

                    statementCounter += 1
                    # Update Dependencies, p proves p
                    dicts.dependenciesDict[problemId] = [problemId]+dicts.dependenciesDict[problemId]
                    if args.learnTheories:
                        theoryModels.update(problemId,dicts.featureDict[problemId],dicts.dependenciesDict[problemId],dicts)
                    if args.snow:
                        model.update(problemId,dicts.featureDict[problemId],dicts.dependenciesDict[problemId],dicts)
                    else:
                        model.update(problemId,dicts.featureDict[problemId],dicts.dependenciesDict[problemId])
                elif line.startswith('p'):
                    # Overwrite old proof.
                    problemId,newDependencies = dicts.parse_overwrite(line)
                    newDependencies = [problemId]+newDependencies
                    model.overwrite(problemId,newDependencies,dicts)
                    if args.learnTheories:
                        theoryModels.overwrite(problemId,newDependencies,dicts)
                    dicts.dependenciesDict[problemId] = newDependencies
                elif line.startswith('?'):               
                    startTime = time()
                    computeStats = True
                    if args.predef:
                        continue
                    name,features,accessibles,hints = dicts.parse_problem(line)  
                        
                    # Create predictions
                    logger.info('Starting computation for problem on line %s',lineCounter)
                    # Update Models with hints
                    if not hints == []:
                        if args.learnTheories:
                            accessibleTheories = set([(dicts.idNameDict[x]).split('.')[0] for x in accessibles])
                            theoryModels.update_with_acc('hints',features,hints,dicts,accessibleTheories)
                        if args.snow:
                            pass
                        else:
                            model.update('hints',features,hints)

                    # Predict premises
                    if args.learnTheories:
                        predictedTheories,accessibles = theoryModels.predict(features,accessibles,dicts)

                    # Add additional features on premise lvl if sine is enabled
                    if args.sineFeatures:
                        origFeatures = [f for f,_w in features]
                        secondaryFeatures = []
                        for f in origFeatures:
                            if dicts.featureCountDict[f] == 1:
                                continue
                            triggeredFormulas = dicts.featureTriggeredFormulasDict[f]                                
                            for formula in triggeredFormulas: 
                                tFeatures = dicts.triggerFeaturesDict[formula]                                
                                #tFeatures = [ff for ff,_fw in dicts.featureDict[formula]]
                                newFeatures = set(tFeatures).difference(secondaryFeatures+origFeatures)
                            for fNew in newFeatures:
                                secondaryFeatures.append((fNew,args.sineWeight))
                        predictionsFeatures = features+secondaryFeatures
                    else:
                        predictionsFeatures = features                    
                    predictions,predictionValues = model.predict(predictionsFeatures,accessibles,dicts)
                    assert len(predictions) == len(predictionValues)
                    
                    # Delete hints
                    if not hints == []:
                        if args.learnTheories:
                            theoryModels.delete('hints',features,hints,dicts)
                        if args.snow:
                            pass
                        else:
                            model.delete('hints',features,hints)

                    logger.info('Done. %s seconds needed.',round(time()-startTime,2))
                    # Output        
                    predictionNames = [str(dicts.idNameDict[p]) for p in predictions[:args.numberOfPredictions]]
                    predictionValues = [str(x) for x in predictionValues[:args.numberOfPredictions]]
                    predictionsStringList = ['%s=%s' % (predictionNames[i],predictionValues[i]) for i in range(len(predictionNames))]
                    predictionsString = string.join(predictionsStringList,' ')
                    outString = '%s: %s' % (name,predictionsString)
                    OS.write('%s\n' % outString)
                else:
                    logger.warning('Unspecified input format: \n%s',line)
                    sys.exit(-1)
                lineCounter += 1
            """
            except:
                logger.warning('An error occurred on line %s .',line)
                lineCounter += 1
                continue
            """
        OS.close()
        IS.close()

        # Statistics
        if args.statistics:
            if args.learnTheories:
                theoryStats.printAvg()
            stats.printAvg()

        # Save
        if args.saveModel:
            model.save(args.modelFile)
            if args.learnTheories:
                theoryModels.save(args.theoryFile)
        dicts.save(args.dictsFile)
        if not args.saveStats == None:
            if args.learnTheories:
                theoryStatsFile = os.path.join(args.outputDir,'theoryStats')
                theoryStats.save(theoryStatsFile)
            statsFile = os.path.join(args.outputDir,args.saveStats)
            stats.save(statsFile)
    return 0

if __name__ == '__main__':
    # Cezary Auth  
    args = ['--statistics', '--init', '--inputDir', '../data/20130118/Jinja', '--log', '../tmp/auth.log', '--theoryFile', '../tmp/t0', '--modelFile', '../tmp/m0', '--dictsFile', '../tmp/d0','--NBDefaultPriorWeight', '20.0', '--NBDefVal', '-15.0', '--NBPosWeight', '10.0']
    mash(args)
    args = ['-i', '../data/20130118/Jinja/mash_commands', '-p', '../tmp/auth.pred0', '--statistics', '--cutOff', '500', '--log', '../tmp/auth.log','--modelFile', '../tmp/m0', '--dictsFile', '../tmp/d0']
    mash(args)   

    #sys.exit(mash(args))
    sys.exit(mash())
