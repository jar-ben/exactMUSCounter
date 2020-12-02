import os
from random import randint
rid = str(randint(1,10000000))

def negate(cl):
    return [-1 * l for l in cl]

## input: l: a list of lists of numbers
## output: a maximum number in l
def maxVar(l):
    maximum = 0
    for i in l:
        maximum = max(maximum, max([abs(j) for j in i]))
    return maximum

def variables(cls):
    vrs = []
    for cl in cls:
        for l in cl:
            if l < 0: l *= -1
            vrs += [l]
    return list(set(vrs))

## input: cube: a cube, i.e. conjunction of literals, represented as list of ints
## input actLit: a literal
## output: cnf formula (written as a list of lists) representing (cube <==> actLit)
def CubeActLitEq(cube, actLit):
    res = []
    for l in cube:
        res.append([-actLit,l])
    res.append([actLit] + [-l for l in cube])
    return res

## input: clause: a clause, i.e. disjunction of literals, represented as list of ints
## input actLit: a literal
## output: cnf formula (written as a list of lists) representing (clause <==> actLit)
def ClauseActLitEq(clause, actLit):
    res = []
    for l in clause:
        res.append([actLit,-l])
    res.append([-actLit] + [l for l in clause])
    return res

def dnfToCnf(dnf, current):
    activators = []
    acts = []
    res = []
    for cl in dnf:
        activators.append(current)
        res += CubeActLitEq(cl,current)
        acts.append(current)
        current += 1
    res.append([-current] + activators)
    for a in activators:
        res.append([-a,current])
    acts.append(current)
    return res, acts

def cnfToCnf(cnf, current):
    activators = []
    acts = []
    res = []
    for cl in cnf:
        activators.append(current)
        res += ClauseActLitEq(cl,current)
        acts.append(current)
        current += 1

    for a in activators:
        res.append([a,-current])
    res.append([current] + negate(activators))    
    acts.append(current)
    return res, acts

def qdimacs(cnf, a, e):
    result = "p cnf {} {}\n".format(maxVar(cnf), len(cnf))
    result += "a " + " ".join([str(i) for i in a]) + " 0\n"
    result += "e " + " ".join([str(i) for i in e]) + " 0\n"
    for cl in cnf:
        result += " ".join([str(l) for l in cl]) + " 0\n"
    return result

def nvars(cls):
    vrs = []
    for cl in cls:
        for l in cl:
            if l < 0: l *= -1
            vrs += [l]
    return set(vrs)


def complement(S,C):
    cm = []
    for cl in C:
        if cl not in S: cm.append(cl)
    return cm

def prime(cl, n):
    primed = []
    for l in cl:
        if l > 0:
            primed.append(l + n)
        else:
            primed.append(l - n)
    return primed

def renderCnf(cls):
    nvariables = max(variables(cls))
    clauses = len(cls)
    result = "p cnf {} {}\n".format(nvariables, clauses)
    for cl in cls:
        result += " ".join([str(l) for l in cl]) + " 0\n"
    return result

import subprocess as sp
def getMUS(filepath):
    cmd = "./muser2-para -ichk -comp {}".format(filepath)
    proc = sp.Popen([cmd], stdout=sp.PIPE, shell=True)
    (out, err) = proc.communicate()
    out = out.decode("utf-8")
    assert "UNSATISFIABLE" in out
    reading = False
    for line in out.splitlines():
        if "UNSATISFIABLE" in line:
            reading = True
            continue
        if reading:
            line = line.split(" ")
            assert line[0] == "v"
            return [int(l) - 1 for l in line[1:-1]]
    
def export(overApprox, C):
    for i in range(len(overApprox)):
        if not overApprox[i]:
            print(i)

def findUnion(filename, verbose = False):
    C = parse(filename)
    if len(C) > 20000: 
        print("over 20000")
        return
    print("below 20000")
    Vars = list(nvars(C))
    n = len(Vars)
    primeVars = [v + n for v in Vars]
    activators = [2*n + i + 1 for i in range(len(C))]

    sat = 0
    unsat = 0
    known = [False for _ in range(len(C))]
    overApprox = [True for _ in range(len(C))]
    underApprox = [False for _ in range(len(C))]
    timeouts = 0 
    for d in range(len(C)):
        if known[d]: continue
        #X - {d} is unsat
        fst = []
        for i in range(len(C)):
            if overApprox[i]:
                if i != d:
                    fst.append(prime(negate(C[i]),n) + [activators[i]])
                else:
                    fst.append(prime(negate(C[i]),n) + [-activators[i]])
        fst, actsFst = dnfToCnf(fst, activators[-1] + 1)

        #X is sat
        snd = []
        for i in range(len(C)):
            if overApprox[i]:
                snd.append(C[i] + [-activators[i]])
        activationWiseSnd, actsSnd = cnfToCnf(snd,actsFst[-1] + 1)    

        actFst = actsFst[-1] #activator for the whole fst
        actSnd = actsSnd[-1] #activator for the whole snd
        mainAct = actSnd + 1 #activator for the disjunction of fst and snd
        completeCnf = fst + activationWiseSnd + [[-mainAct, actFst, actSnd], [-actFst, mainAct], [-actSnd, mainAct], [mainAct]]                           

        a = primeVars + activators
        e = Vars + actsSnd + actsFst + [mainAct]

        tf = "enc" + rid + ".qdimacs"
        with open(tf, "w") as f:
            f.write(qdimacs(completeCnf, a, e))
        if verbose: print("start of compute")
        s, M = compute(tf, activators, verbose)
        #os.remove(tf)
        if verbose: print("end of compute", s)
        if s == "sat":
            sat += 1
            overApprox[d] = False
        elif s == "unsat":
            unsat += 1
            with open("unsat.cnf", "w") as f:
                presented = [i for i in range(len(activators)) if activators[i] in M]
                presented += [d]
                f.write(renderCnf([C[i] for i in presented]))
            MUS = [presented[i] for i in getMUS("unsat.cnf")]
            for c in MUS:
                known[c] = True
                underApprox[c] = True
        if s == "timeouted": timeouts += 1
        if s == "sat" or s == "unsat" or True:
            known[d] = True
            print("sat: {}, unsat: {}, underApprox: {}, overApprox: {}, known: {} percent, timeouts: {}".format(sat, unsat, underApprox.count(True), overApprox.count(True), (float(known.count(True))/len(C)) * 100, timeouts ))
    export(overApprox, C)

def parse(file):
    with open(file, "r") as f:
        lines = f.readlines()
        C = []
        for line in lines[1:]:
            line = line.split(" ")
            if line[0] not in ["c", "p"]:
                if line[0][0] == "{" and line[0][-1] == "}":
                    line = line[1:] #handle the group clauses
                line = [int(i) for i in line[:-1]]
                C.append(line)
        return C

def simplify(filename, result):
    cmd = "/home/xbendik/bin/qbfrelay/qbfrelay.sh -p {} {} > /dev/null 2>&1".format(result, filename)
    cmd = "/home/xbendik/bin/qratpreplus/qratpre+ --print-formula {} > {}".format(filename, result)
    print(cmd)
    proc = sp.Popen([cmd], stdout=sp.PIPE, shell=True)
    (out, err) = proc.communicate()
    out = out.decode("utf-8")

def compute(filename, acts, verbose = False):
    simpl = "simpl_" + filename
    simplify(filename, simpl)
    #simpl = filename
    cmd = "timeout 120 /home/xbendik/bin/cadet/cadet {}".format(simpl)
    print(cmd)
    if verbose: print("starting cadet (QBF solver)")
    proc = sp.Popen([cmd], stdout=sp.PIPE, shell=True)
    (out, err) = proc.communicate()
    if verbose: print("cadet has finished")
    out = out.decode("utf-8")
    if not "SAT" in out:
        return "timeouted", None
    if not "UNSAT" in out:
        if verbose: print("SAT, i.e., there is no MUS containing the clause")
        return "sat", None
    if verbose: print("SAT, i.e. there is a MUS containing the clause")
    S = []
    used = []
    for line in out.splitlines():
        line = line.rstrip().split()
        if line[0] == "V":
            for x in [int(l) for l in line[1:]]:
                if x > 0 and x in acts:
                    S.append(x)
                    used.append(x)
                if x < 0 and -x in acts:
                    used.append(-x)
    #if we use simplification (qratpre+), some of the universal quantifiers (activators) might be eliminated
    #therefore, we get an incomplete assignment from cadet (it is complete w.r.t. the simplified formula but not w.r.t. the original one)
    #here we conservatively complete the assignment by setting the remaining activators to True
    #note that this might (we are not sure actually) lead to an assignment that actually does not satisfy the original formula, 
    #however we have a guarantee that the assignment corresponds to an unsatisfiable subset.
    #We also have the guarantee that "d" is indeed contained in some MUS. 
    for a in acts:
        if a not in used:
            S.append(a)
    return "unsat", S

import sys
if __name__ == "__main__":
    assert len(sys.argv) > 1
    filename = sys.argv[1]
    findUnion(filename, verbose = True)
