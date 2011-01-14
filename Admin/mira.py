"""
    Test configuration descriptions for mira.
"""

import os
from os import path
from glob import glob
import subprocess
import re

import util


# build and evaluation tools

def prepare_isabelle_repository(loc_isabelle, loc_contrib, loc_dependency_heaps, parallelism = True):

    loc_contrib = path.expanduser(loc_contrib)
    if not path.exists(loc_contrib):
        raise IOError('Bad file: %s' % loc_contrib)
    subprocess.check_call(['ln', '-s', loc_contrib, '%s/contrib' % loc_isabelle])

    contributed_components = path.join(loc_isabelle, 'Admin', 'contributed_components')
    if path.exists(contributed_components):
        components = []
        for component in util.readfile_lines(contributed_components):
            loc_component = path.join(loc_isabelle, component)
            if path.exists(loc_component):
                components.append(loc_component)
        writer = open(path.join(loc_isabelle, 'etc', 'components'), 'a')
        for component in components:
            writer.write(component + '\n')
        writer.close()

    if loc_dependency_heaps:
        isabelle_path = loc_dependency_heaps + '/$ISABELLE_IDENTIFIER:$ISABELLE_OUTPUT'
    else:
        isabelle_path = '$ISABELLE_OUTPUT'

    if parallelism:
        parallelism_options = '-M max'
    else:
        parallelism_options = '-M 1 -q 0'

    extra_settings = '''
ISABELLE_HOME_USER="$ISABELLE_HOME/home_user"
ISABELLE_OUTPUT="$ISABELLE_HOME/heaps"
ISABELLE_BROWSER_INFO="$ISABELLE_HOME/browser_info"
ISABELLE_PATH="%s"

ISABELLE_USEDIR_OPTIONS="$ISABELLE_USEDIR_OPTIONS %s -t true -v true -d pdf -g true -i true"
''' % (isabelle_path, parallelism_options)

    writer = open(path.join(loc_isabelle, 'etc', 'settings'), 'a')
    writer.write(extra_settings)
    writer.close()


def extract_isabelle_run_timing(logdata):

    def to_secs(h, m, s):
        return (int(h) * 60 + int(m)) * 60 + int(s)
    pat = r'Finished (\S+) \((\d+):(\d+):(\d+) elapsed time, (\d+):(\d+):(\d+) cpu time'
    pat2 = r'Timing (\S+) \((\d+) threads, (\d+\.\d+)s elapsed time, (\d+\.\d+)s cpu time, (\d+\.\d+)s GC time\)'
    t = dict((name, {'elapsed': to_secs(eh,em,es), 'cpu': to_secs(ch,cm,cs)})
             for name, eh, em, es, ch, cm, cs in re.findall(pat, logdata))
    for name, threads, elapsed, cpu, gc in re.findall(pat2, logdata):

        if name not in t:
            t[name] = {}

        t[name]['threads'] = int(threads)
        t[name]['elapsed_inner'] = elapsed
        t[name]['cpu_inner'] = cpu
        t[name]['gc'] = gc

    return t


def extract_isabelle_run_summary(logdata):

    re_error = re.compile(r'^\*\*\* (.*)$', re.MULTILINE)
    summary = '\n'.join(re_error.findall(logdata))
    if summary == '':
        summary = 'ok'

    return summary


def isabelle_usedir(env, isa_path, isabelle_usedir_opts, base_image, dir_name):

    return env.run_process('%s/bin/isabelle' % isa_path, 'usedir',
        isabelle_usedir_opts, base_image, dir_name)


def isabelle_dependency_only(env, case, paths, dep_paths, playground):

    p = paths[0]
    result = path.join(p, 'heaps')
    os.makedirs(result)
    for dep_path in dep_paths:
        subprocess.check_call(['cp', '-R'] + glob(dep_path + '/*') + [result])

    return (True, 'ok', {}, {}, result)


def build_isabelle_image(subdir, base, img, env, case, paths, dep_paths, playground):

    p = paths[0]
    dep_path = dep_paths[0]
    prepare_isabelle_repository(p, env.settings.contrib, dep_path)
    os.chdir(path.join(p, 'src', subdir))

    (return_code, log) = isabelle_usedir(env, p, '-b', base, img)

    result = path.join(p, 'heaps')
    return (return_code == 0, extract_isabelle_run_summary(log),
      {'timing': extract_isabelle_run_timing(log)}, {'log': log}, result)


def isabelle_makeall(env, case, paths, dep_paths, playground):

    p = paths[0]
    dep_path = dep_paths[0]
    prepare_isabelle_repository(p, env.settings.contrib, dep_path)
    os.chdir(p)

    (return_code, log) = env.run_process('%s/bin/isabelle' % p, 'makeall', '-k', 'all')

    return (return_code == 0, extract_isabelle_run_summary(log),
      {'timing': extract_isabelle_run_timing(log)}, {'log': log}, None)


# Isabelle configurations

@configuration(repos = [Isabelle], deps = [])
def Pure(env, case, paths, dep_paths, playground):
    """Pure image"""

    p = paths[0]
    prepare_isabelle_repository(p, env.settings.contrib, '')
    os.chdir(path.join(p, 'src', 'Pure'))

    (return_code, log) = env.run_process('%s/bin/isabelle' % p, 'make', 'Pure')

    result = path.join(p, 'heaps')
    return (return_code == 0, extract_isabelle_run_summary(log),
      {'timing': extract_isabelle_run_timing(log)}, {'log': log}, result)

@configuration(repos = [Isabelle], deps = [(Pure, [0])])
def FOL(*args):
    """FOL image"""
    return build_isabelle_image('FOL', 'Pure', 'FOL', *args)

@configuration(repos = [Isabelle], deps = [(Pure, [0])])
def HOL(*args):
    """HOL image"""
    return build_isabelle_image('HOL', 'Pure', 'HOL', *args)

@configuration(repos = [Isabelle], deps = [(HOL, [0])])
def HOL_HOLCF(*args):
    """HOL-HOLCF image"""
    return build_isabelle_image('HOL/HOLCF', 'HOL', 'HOLCF', *args)

@configuration(repos = [Isabelle], deps = [(HOL, [0])])
def HOL_Nominal(*args):
    """HOL-Nominal image"""
    return build_isabelle_image('HOL/Nominal', 'HOL', 'HOL-Nominal', *args)

@configuration(repos = [Isabelle], deps = [(HOL, [0])])
def HOL_Word(*args):
    """HOL-Word image"""
    return build_isabelle_image('HOL/Word', 'HOL', 'HOL-Word', *args)

@configuration(repos = [Isabelle], deps = [
    (HOL, [0]),
    (HOL_HOLCF, [0]),
    (HOL_Nominal, [0]),
    (HOL_Word, [0])
  ])
def AFP_images(*args):
    """Isabelle images needed for the AFP"""
    return isabelle_dependency_only(*args)

@configuration(repos = [Isabelle], deps = [
    (AFP_images, [0])
  ])
def Isabelle_makeall(*args):
    """Isabelle makeall"""
    return isabelle_makeall(*args)


# Mutabelle configurations

def invoke_mutabelle(theory, env, case, paths, dep_paths, playground):

    """Mutant testing for counterexample generators in Isabelle"""

    (loc_isabelle,) = paths
    (dep_isabelle,) = dep_paths
    prepare_isabelle_repository(loc_isabelle, env.settings.contrib, dep_isabelle)
    os.chdir(loc_isabelle)
    
    (return_code, log) = env.run_process('bin/isabelle',
      'mutabelle', '-O', playground, theory)
    
    try:
        mutabelle_log = util.readfile(path.join(playground, 'log'))
    except IOError:
        mutabelle_log = ''

    attachments = { 'log': log, 'mutabelle_log': mutabelle_log}

    return (return_code == 0 and mutabelle_log != '', extract_isabelle_run_summary(log),
      {'timing': extract_isabelle_run_timing(log)}, {'log': log}, None)

@configuration(repos = [Isabelle], deps = [(HOL, [0])])
def Mutabelle_Relation(*args):
    """Mutabelle regression suite on Relation theory"""
    return invoke_mutabelle('Relation', *args)

@configuration(repos = [Isabelle], deps = [(HOL, [0])])
def Mutabelle_List(*args):
    """Mutabelle regression suite on List theory"""
    return invoke_mutabelle('List', *args)

@configuration(repos = [Isabelle], deps = [(HOL, [0])])
def Mutabelle_Set(*args):
    """Mutabelle regression suite on Set theory"""
    return invoke_mutabelle('Set', *args)

@configuration(repos = [Isabelle], deps = [(HOL, [0])])
def Mutabelle_Map(*args):
    """Mutabelle regression suite on Map theory"""
    return invoke_mutabelle('Map', *args)

@configuration(repos = [Isabelle], deps = [(HOL, [0])])
def Mutabelle_Divides(*args):
    """Mutabelle regression suite on Divides theory"""
    return invoke_mutabelle('Divides', *args)

@configuration(repos = [Isabelle], deps = [(HOL, [0])])
def Mutabelle_MacLaurin(*args):
    """Mutabelle regression suite on MacLaurin theory"""
    return invoke_mutabelle('MacLaurin', *args)

@configuration(repos = [Isabelle], deps = [(HOL, [0])])
def Mutabelle_Fun(*args):
    """Mutabelle regression suite on Fun theory"""
    return invoke_mutabelle('Fun', *args)
