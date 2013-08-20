'''
Created on Aug 20, 2013

@author: daniel
'''
from mash import mash

if __name__ == "__main__":
    args = ['--statistics', '--init', '--inputDir', '../data/20130118/Jinja', '--log', '../tmp/auth.log', '--modelFile', '../tmp/m0', '--dictsFile', '../tmp/d0','--NBDefaultPriorWeight', '20.0', '--NBDefVal', '-15.0', '--NBPosWeight', '10.0']
    mash(args)
    args = ['-i', '../data/20130118/Jinja/mash_commands', '-p', '../tmp/auth.pred0', '--statistics', '--cutOff', '500', '--log', '../tmp/auth.log','--modelFile', '../tmp/m0', '--dictsFile', '../tmp/d0']
    mash(args) 