import sys
from math import log
import subprocess as sp
import random
import time
from statistics import median
from random import randint
import argparse
import os
from functools import partial
import signal
from pysat.card import *
import glob
import itertools

sys.path.insert(0, "/home/xbendik/bin/pysat")
from pysat.formula import CNF
from pysat.solvers import Solver, Minisat22


def tseitinCube(cube, current):
    current += 1
    res = []
    for l in cube:
        res.append([-current,l])
    res.append([current] + [-l for l in cube])
    return res, current

def tseitinClause(clause, current):
    current += 1
    res = []
    for l in clause:
        res.append([current,-l])
    res.append([-current] + [l for l in clause])
    return res, current

def receiveSignal(tempFiles, signalNumber, frame):
    print(tempFiles, signalNumber, frame)
    print('Received signal:', signalNumber)
    print('Cleaning tmp files')
    for f in tempFiles:
        if os.path.exists(f):
            print("removing", f, "...", end="")
            os.remove(f)
            print("removed")
    sys.exit()

def variables(C):
    v = set()
    for cl in C:
        for l in cl:
            v.add(abs(l))
    return v

def maxVar(C):
    return max(variables(C))

def randomBool():                                                                                                                                                               return bool(random.getrandbits(1))

def renderWcnf(Hard, Soft):
    nvariables = maxVar(Hard + Soft)
    clauses = len(Hard) + len(Soft)
    hardWeight = len(Soft) + 1
    softWeight = 1

    result = "p wcnf {} {} {}\n".format(nvariables, clauses, hardWeight)
    for cl in Hard:
        result += str(hardWeight) + " " + " ".join([str(l) for l in cl]) + " 0\n"
    for cl in Soft:
        result += str(softWeight) + " " + " ".join([str(l) for l in cl]) + " 0\n"

    return result

def run(cmd, timeout, ttl = 3, silent = False):
    if not silent:                                                                                                                                                                  print("Executing:", cmd)
    proc = sp.Popen([cmd], stdout=sp.PIPE, stderr=sp.PIPE, shell=True)
    try:
        (out, err) = proc.communicate(timeout = int(timeout * 1.1) + 1)
        out = out.decode("utf-8")
    except sp.TimeoutExpired:
        proc.kill()
        try:
            (out, err) = proc.communicate()
            out = out.decode("utf-8")
        except ValueError:
            if ttl > 0:
                return run(cmd, timeout, ttl - 1)
            out = ""
    return out

def exportOPB(clauses, filename, ind = [], cards = None):
    with open(filename, "w") as f:
        maxVar = max([max(abs(l) for l in cl) for cl in clauses])
        f.write("* #variables= {} #constraints= {}\n".format(maxVar, len(clauses) + len(cards)))
        if len(ind) > 0:
            f.write("* ind " + " ".join([str(i) for i in ind]) + " 0\n")

        for c in cards:
            f.write(c + ";\n")

        for cl in clauses:
            f.write(" ".join([("1 x" + str(l)) if l > 0 else ("1 ~x" + str(-l)) for l in cl]) + " >= 1 ;\n")

    print("exported {}, clauses: {}, maxVar: {}, cards: {}".format(filename, len(clauses), maxVar, len(cards)))

def exportCNF(clauses, filename, ind = [], varFile = None, cards = None):
    with open(filename, "w") as f:
        if len(ind) > 0:
            f.write("c ind " + " ".join([str(i) for i in ind]) + " 0\n")
        maxVar = max([max(abs(l) for l in cl) for cl in clauses])
        f.write("p cnf {} {}\n".format(maxVar, len(clauses)))
        for cl in clauses:
            f.write(" ".join([str(l) for l in cl]) + " 0\n")

    print("exported {}, clauses: {}, maxVar: {}".format(filename, len(clauses), maxVar))
    if (varFile is not None) and (len(ind) > 0):
        with open(varFile, "w") as f:
            f.write(",".join ([str(v) for v in ind]))

def exportGCNF(hard, soft, filename):
    with open(filename, "w") as f:
        maxVar = max([max(abs(l) for l in cl) for cl in hard + soft])
        f.write("p gcnf {} {} {}\n".format(maxVar, len(soft + hard), len(soft)))
        for cl in hard:
            f.write("{0} " + " ".join([str(l) for l in cl]) + " 0\n")
        for i in range(1, len(soft) + 1):
            f.write("{{{}}} ".format(i) + " ".join([str(l) for l in soft[i - 1]]) + " 0\n")

    print("exported {}, hard clauses: {}, soft clauses: {}, maxVar: {}".format(filename, len(hard), len(soft), maxVar))

#parse .gcnf instance,
#returns a pair C,B where B contains the base (hard) clauses and C the other clauses
def parse(filename):
    C = []
    B = []
    with open(filename, "r") as f:
        lines = f.readlines()
        if filename[-5:] == ".gcnf":
            for line in lines[1:]:
                if line[0] in ["p","c"]: continue
                line = line.split(" ")
                cl = [int(i) for i in line[1:-1]]
                if len(cl) > 0:
                    if line[0] == "{0}":
                        B.append(cl)
                    else:
                        C.append(cl)
        else:
            for line in lines[1:]:
                if line[0] in ["p","c"]: continue
                line = line.split(" ")
                cl = [int(i) for i in line[:-1]]
                if len(cl) > 0:
                    C.append(cl)
    return C,B

def offset(a, off):
    if a > 0:
        return a + off
    return a - off

def offsetClause(cl, off):
    return [offset(l, off) for l in cl]

def maxSat(Hard, Soft):
    satTimeout = 300
    wcnf = renderWcnf(Hard, Soft)
    file = "./tmp/maxsat_{}.wcnf".format(randint(1,100000000))
    with open(file, "w") as f:
        f.write(wcnf)

    cmd = 'timeout {} ./tools/uwrmaxsat -m {}'.format(satTimeout, file)
    out = run(cmd, satTimeout)
    model = []
    if os.path.exists(file):
        os.remove(file)

    model = {}
    for line in out.splitlines():
        if line[:2] == "v ":
            for l in line[2:].split(" "):
                l = int(l)
                var = l if l > 0 else -l
                assert var not in model
                model[var] = l > 0
    #print(model)
    if model == {}: return -1 #failed to load the model

    satisfied = 0
    for cl in Soft:
        for l in cl:
            if (l > 0 and model[l]) or (l < 0 and not model[-l]):
                satisfied += 1
                break
    print("max sat value", satisfied)
    return satisfied if satisfied > 0 else -1

def getAutarky(C = [], filename = None):
    keep = filename != None
    if filename == None:
        filename = "./tmp/autarky{}.cnf".format(randint(1,10000000))
        exportCNF(C, filename)
    cmd = "timeout 3600 python3 autarky.py {}".format(filename)
    out = run(cmd, 3600)
    if not keep: os.remove(filename)
    if "autarky vars" in out:
        for line in out.splitlines():
            line = line.rstrip()
            if line[:2] == "v ":
                return [int(c) - 1 for c in line.split()[1:]]
    else: return [i for i in range(len(C))]

def getImu(C = [], filename = []):
    keep = filename != None
    if filename == None:
        filename = "./tmp/imu{}.cnf".format(randint(1,10000000))
        exportCNF(C, filename)
    cmd = "timeout 3600 python3 gimu.py {}".format(filename)
    out = run(cmd, 3600)
    if "imu size" in out and not "imu size: 0" in out:
        for line in out.splitlines():
            line = line.rstrip()
            if line[:2] == "v ":
                return [int(c) - 1 for c in line.split()[1:]]
    else: return []

def rime(C, hard = [], excluded = [], limit = 0, auxiliaryHard = [], timelimit = 3600):
    if checkSAT(C, excluded):
        return [[]]

    H = []
    S = []
    mapa = []
    for i in range(len(C)):
        if i in excluded: continue
        elif i in hard:
            H.append(C[i])
        else:
            mapa.append(i)
            S.append(C[i])

    for h in auxiliaryHard:
        H.append(h)

    if len(S) == 0:
        return []

    filename = "./tmp/rime{}.wcnf".format(randint(1,10000000))
    open(filename, "w").write(renderWcnf(H,S))
    cmd = "./tools/rime -v 1 {}".format(filename)
    out = run(cmd, 3600)
    os.remove(filename)
    assert "Number of MSSes" in out
    out = out.splitlines()
    assert "Number of MSSes" in out[-1]
    mssesCount = int(out[-1].rstrip().split()[-1])

    mcses = []
    for line in out:
        if line[:4] == "MCS ":
            line = line.rstrip().split(" ")[1:]
            mcs = [int(c) for c in line if int(c) < len(C)] #0-based indexing
            mcses.append(mcs)
    assert mssesCount == len(mcses)
    return mcses

def checkSAT(C, excluded = []):
    s = Solver(name = "g4")
    for i in range(len(C)):
        if not i in excluded:
            s.add_clause(C[i])
    return s.solve()

def isMCS(C, N):
    D = [C[i] for i in range(len(C)) if i not in N]
    if not checkSAT(D):
        print("not even a CS")
        return False

    for n in N:
        D = [C[i] for i in range(len(C)) if i not in N]
        D.append(C[n])
        if checkSAT(D): 
            print("adding {}, {} makes it sat".format(n, C[n]))
            return False
    return True


def printMCSes(mcses):
    return
    for mcs in mcses:
        print("MCS~", mcs)

def mcsls(C, hard, excluded, limit = 0, auxiliaryHard = []):
    if checkSAT(C, excluded):
        return [[]]

    H = []
    S = []
    mapa = []
    for i in range(len(C)):
        if i in excluded: continue
        elif i in hard:
            H.append(C[i])
        else:
            mapa.append(i)
            S.append(C[i])

    for h in auxiliaryHard:
        H.append(h)

    if len(S) == 0:
        return []

    filename = "./tmp/mcsls{}.wcnf".format(randint(1,10000000))
    open(filename, "w").write(renderWcnf(H,S))
    cmd = "timeout {} ./mcsls -num {} {}".format(3600, limit, filename)
    print(cmd)
    out = run(cmd, 3600)
    os.remove(filename)
    mcses = []
    for line in out.splitlines():
        if line[:7] == "c MCS: ":
            mcs = [int(c) for c in line[7:].rstrip().split(" ")] #1 based indexing
            mcses.append([mapa[i - (1 + len(H))] for i in mcs])

    return mcses

def projection(source, target):
    return [i for i in source if i in target]


