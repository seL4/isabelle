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

def prepare_isabelle_repository(loc_isabelle, loc_contrib, loc_dependency_heaps, parallelism = True, more_settings=''):

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
Z3_NON_COMMERCIAL="yes"
%s
''' % (isabelle_path, parallelism_options, more_settings)

    writer = open(path.join(loc_isabelle, 'etc', 'settings'), 'a')
    writer.write(extra_settings)
    writer.close()


def extract_isabelle_run_timing(logdata):

    def to_secs(h, m, s):
        return (int(h) * 60 + int(m)) * 60 + int(s)
    pat = r'Finished (\S+) \((\d+):(\d+):(\d+) elapsed time, (\d+):(\d+):(\d+) cpu time'
    pat2 = r'Timing (\S+) \((\d+) threads, (\d+\.\d+)s elapsed time, (\d+\.\d+)s cpu time, (\d+\.\d+)s GC time, factor (\d+\.\d+)\)'
    t = dict((name, {'elapsed': to_secs(eh,em,es), 'cpu': to_secs(ch,cm,cs)})
             for name, eh, em, es, ch, cm, cs in re.findall(pat, logdata))
    for name, threads, elapsed, cpu, gc, factor in re.findall(pat2, logdata):

        if name not in t:
            t[name] = {}

        t[name]['threads'] = int(threads)
        t[name]['elapsed_inner'] = elapsed
        t[name]['cpu_inner'] = cpu
        t[name]['gc'] = gc
        t[name]['factor'] = factor

    return t


def extract_isabelle_run_summary(logdata):

    re_error = re.compile(r'^(?:make: )?\*\*\* (.*)$', re.MULTILINE)
    summary = '\n'.join(re_error.findall(logdata))
    if summary == '':
        summary = 'ok'

    return summary


def isabelle_usedir(env, isa_path, isabelle_usedir_opts, base_image, dir_name):

    return env.run_process('%s/bin/isabelle' % isa_path, 'usedir',
        isabelle_usedir_opts, base_image, dir_name)


def isabelle_dependency_only(env, case, paths, dep_paths, playground):

    isabelle_home = paths[0]
    result = path.join(isabelle_home, 'heaps')
    os.makedirs(result)
    for dep_path in dep_paths:
        subprocess.check_call(['cp', '-R'] + glob(dep_path + '/*') + [result])

    return (True, 'ok', {}, {}, result)


def build_isabelle_image(subdir, base, img, env, case, paths, dep_paths, playground, more_settings=''):

    isabelle_home = paths[0]
    dep_path = dep_paths[0]
    prepare_isabelle_repository(isabelle_home, env.settings.contrib, dep_path, more_settings=more_settings)
    os.chdir(path.join(isabelle_home, 'src', subdir))

    (return_code, log) = isabelle_usedir(env, isabelle_home, '-b', base, img)

    result = path.join(isabelle_home, 'heaps')
    return (return_code == 0, extract_isabelle_run_summary(log),
      {'timing': extract_isabelle_run_timing(log)}, {'log': log}, result)


def isabelle_make(subdir, env, case, paths, dep_paths, playground, more_settings='', target='all', keep_results=False):

    isabelle_home = paths[0]
    dep_path = dep_paths[0] if dep_paths else None
    prepare_isabelle_repository(isabelle_home, env.settings.contrib, dep_path, more_settings=more_settings)
    os.chdir(path.join(isabelle_home, subdir))

    (return_code, log) = env.run_process('%s/bin/isabelle' % isabelle_home, 'make', '-k', target)

    result = path.join(isabelle_home, 'heaps') if keep_results else None
    return (return_code == 0, extract_isabelle_run_summary(log),
      {'timing': extract_isabelle_run_timing(log)}, {'log': log}, result)


def isabelle_makeall(env, case, paths, dep_paths, playground, more_settings='', target='all', make_options=()):

    isabelle_home = paths[0]
    dep_path = dep_paths[0] if dep_paths else None
    prepare_isabelle_repository(isabelle_home, env.settings.contrib, dep_path, more_settings=more_settings)
    os.chdir(isabelle_home)

    (return_code, log) = env.run_process('%s/bin/isabelle' % isabelle_home, 'makeall', '-k', *(make_options + (target,)))

    return (return_code == 0, extract_isabelle_run_summary(log),
      {'timing': extract_isabelle_run_timing(log)}, {'log': log}, None)


# Isabelle configurations

@configuration(repos = [Isabelle], deps = [])
def Pure(env, case, paths, dep_paths, playground):
    """Pure image"""

    isabelle_home = paths[0]
    prepare_isabelle_repository(isabelle_home, env.settings.contrib, '')
    os.chdir(path.join(isabelle_home, 'src', 'Pure'))

    (return_code, log) = env.run_process('%s/bin/isabelle' % isabelle_home, 'make', 'Pure')

    result = path.join(isabelle_home, 'heaps')
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

    return (return_code == 0 and mutabelle_log != '', extract_isabelle_run_summary(log),
      {'timing': extract_isabelle_run_timing(log)},
      {'log': log, 'mutabelle_log': mutabelle_log}, None)

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


# Judgement Day configurations

judgement_day_provers = ('e', 'spass', 'vampire', 'z3', 'cvc3', 'yices')

def judgement_day(base_path, theory, opts, env, case, paths, dep_paths, playground):
    """Judgement Day regression suite"""

    isa = paths[0]
    dep_path = dep_paths[0]

    os.chdir(path.join(playground, '..', base_path)) # Mirabelle requires specific cwd
    prepare_isabelle_repository(isa, env.settings.contrib, dep_path)

    output = {}
    success_rates = {}
    some_success = False

    for atp in judgement_day_provers:

        log_dir = path.join(playground, 'mirabelle_log_' + atp)
        os.makedirs(log_dir)

        cmd = ('%s/bin/isabelle mirabelle -q -O %s sledgehammer[prover=%s,%s] %s.thy'
               % (isa, log_dir, atp, opts, theory))

        os.system(cmd)
        output[atp] = util.readfile(path.join(log_dir, theory + '.log'))

        percentages = list(re.findall(r'Success rate: (\d+)%', output[atp]))
        if len(percentages) == 2:
            success_rates[atp] = {
                'sledgehammer': int(percentages[0]),
                'metis': int(percentages[1])}
            if success_rates[atp]['sledgehammer'] > 0:
                some_success = True
        else:
            success_rates[atp] = {}


    data = {'success_rates': success_rates}
    raw_attachments = dict((atp + "_output", output[atp]) for atp in judgement_day_provers)
    # FIXME: summary?
    return (some_success, '', data, raw_attachments, None)


@configuration(repos = [Isabelle], deps = [(HOL, [0])])
def JD_NS(*args):
    """Judgement Day regression suite NS"""
    return judgement_day('Isabelle/src/HOL/Auth', 'NS_Shared', 'prover_timeout=10', *args)

@configuration(repos = [Isabelle], deps = [(HOL, [0])])
def JD_FTA(*args):
    """Judgement Day regression suite FTA"""
    return judgement_day('Isabelle/src/HOL/Library', 'Fundamental_Theorem_Algebra', 'prover_timeout=10', *args)

@configuration(repos = [Isabelle], deps = [(HOL, [0])])
def JD_Hoare(*args):
    """Judgement Day regression suite Hoare"""
    return judgement_day('Isabelle/src/HOL/IMPP', 'Hoare', 'prover_timeout=10', *args)

@configuration(repos = [Isabelle], deps = [(HOL, [0])])
def JD_SN(*args):
    """Judgement Day regression suite SN"""
    return judgement_day('Isabelle/src/HOL/Proofs/Lambda', 'StrongNorm', 'prover_timeout=10', *args)


# SML/NJ

smlnj_settings = '''
ML_SYSTEM=smlnj
ML_HOME="/home/smlnj/110.72/bin"
ML_OPTIONS="@SMLdebug=/dev/null @SMLalloc=256"
ML_PLATFORM=$(eval $("$ML_HOME/.arch-n-opsys" 2>/dev/null); echo "$HEAP_SUFFIX")
'''

@configuration(repos = [Isabelle], deps = [])
def SML_HOL(*args):
    """HOL image built with SML/NJ"""
    return isabelle_make('src/HOL', *args, more_settings=smlnj_settings, target='HOL', keep_results=True)

@configuration(repos = [Isabelle], deps = [])
def SML_makeall(*args):
    """Makeall built with SML/NJ"""
    return isabelle_makeall(*args, more_settings=smlnj_settings, target='smlnj', make_options=('-j', '3'))
