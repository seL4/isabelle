#!/usr/bin/python
#     Title:      HOL/Tools/Sledgehammer/MaSh/src/compareStats.py
#     Author:     Daniel Kuehlwein, ICIS, Radboud University Nijmegen
#     Copyright   2012
#
# Tool that compares MaSh statistics and displays a comparison.

'''
Created on Jul 13, 2012

@author: Daniel Kuehlwein
'''

import sys
from argparse import ArgumentParser,RawDescriptionHelpFormatter
from matplotlib.pyplot import plot,figure,show,legend,xlabel,ylabel,axis,hist
from stats import Statistics

parser = ArgumentParser(description='Compare Statistics.  \n\n\
Loads different statistics and displays a comparison. Requires the matplotlib module.\n\n\
-------- Example Usage ---------------\n\
./compareStats.py --statFiles ../tmp/natISANB.stats ../tmp/natATPNB.stats -b 30\n\n\
Author: Daniel Kuehlwein, July 2012',formatter_class=RawDescriptionHelpFormatter)
parser.add_argument('--statFiles', default=None, nargs='+',
                    help='The names of the saved statistic files.')
parser.add_argument('-b','--bins',default=50,help="Number of bins for the AUC histogram. Default=50.",type=int)

def main(argv = sys.argv[1:]):
    args = parser.parse_args(argv)
    if args.statFiles == None:
        print 'Filenames missing.'
        sys.exit(-1)

    aucData = []
    aucLabels = []
    for statFile in args.statFiles:
        s = Statistics()
        s.load(statFile)
        avgRecall = [float(x)/s.problems for x in s.recallData]
        figure('Recall')
        plot(range(s.cutOff),avgRecall,label=statFile)
        legend(loc='lower right')
        ylabel('Average Recall')
        xlabel('Highest ranked premises')
        axis([0,s.cutOff,0.0,1.0])
        figure('100%Recall')
        plot(range(s.cutOff),s.recall100Data,label=statFile)
        legend(loc='lower right')
        ylabel('100%Recall')
        xlabel('Highest ranked premises')
        axis([0,s.cutOff,0,s.problems])
        aucData.append(s.aucData)
        aucLabels.append(statFile)
    figure('AUC Histogram')
    hist(aucData,bins=args.bins,label=aucLabels,histtype='bar')
    legend(loc='upper left')
    ylabel('Problems')
    xlabel('AUC')

    show()

if __name__ == '__main__':
    #args = ['--statFiles','../tmp/natISANB.stats','../tmp/natATPNB.stats','-b','30']
    #sys.exit(main(args))
    sys.exit(main())
