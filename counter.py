import sys
from math import log
from math import floor
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


def run(cmd, timeout, ttl = 3, silent = False):
    if not silent:
        print("Executing:", cmd)
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

def maxVar(C):
    m = 0
    for cl in C:
        for l in cl:
            m = max(m,abs(l))
    return m

def randomBool():
    return bool(random.getrandbits(1))

def exportCNF(clauses, filename, ind = [], varFile = None):
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

class Counter:
    def __init__(self, filename, useAutarky, useImu):
        self.filename = filename
        self.C, self.B = parse(filename)
        self.imu = useImu
        self.autarky = useAutarky
        self.rid = randint(1,10000000)
        self.debug = False

        if self.imu or self.autarky:
            self.imuAutarkyTrim()

        self.dimension = len(self.C)
        flatten = []
        for cl in (self.B + self.C):
            flatten += cl
        self.lits = set([l for l in flatten])
        self.hitmapC = {}
        self.hitmapB = {}
        for l in self.lits:
            self.hitmapC[l] = []
            self.hitmapC[-l] = []
            self.hitmapB[l] = []
            self.hitmapB[-l] = []
        for i in range(len(self.C)):
            for l in self.C[i]:
                assert l in self.lits
                self.hitmapC[l].append(i + 1) #+1 offset
        for i in range(len(self.B)):
            for l in self.B[i]:
                assert l in self.lits
                self.hitmapB[l].append(i) #note that here we store 0-based index as opposed to hitmapC

        self.mcses = []

        self.WrapperFile = "./tmp/wrapper_{}.cnf".format(self.rid)
        self.WrapperIndFile = self.WrapperFile[:-4] + "_ind.cnf"
        self.RemainderFile = "./tmp/remainder_{}.cnf".format(self.rid)
        self.RemainderIndFile = self.RemainderFile[:-4] + "_ind.cnf"
        self.rimeFile = "./tmp/rime_{}.cnf".format(self.rid)
        self.rimeFileW = "./tmp/rime_{}.wcnf".format(self.rid)
        self.tmpFiles = [self.WrapperFile, self.WrapperIndFile, self.RemainderFile, self.RemainderIndFile, self.rimeFile]

        self.activators = [i + 1 for i in range(self.dimension)]

        self.maxMUSCard = 40
        self.selectors = [] #self.selectors[i] = j means that the variable set i is assigned to the clause j (while building the evidence)
        for i in range(self.dimension):
            self.selectors.append([self.dimension + i*self.maxMUSCard + j for j in range(1, self.maxMUSCard + 1)])

        self.FvarsOffset = self.selectors[-1][-1] 
        self.evidenceVarsOffsets = []
        CBmaxVar = maxVar(self.C + self.B)
        for i in range(1, self.maxMUSCard + 1):
            self.evidenceVarsOffsets.append(self.FvarsOffset + i*CBmaxVar)

        self.act = self.evidenceVarsOffsets[-1] + CBmaxVar #curently maximal used variable 

        if self.debug: 
            print("activators:", self.activators)
            print()
            print("selectors:", self.selectors)
            print()
            print("F's variables offset:", self.FvarsOffset)
            print()
            print("evidence variables' offsets:", self.evidenceVarsOffsets)
            print()
            print("self.act", self.act)

        #selection variables for individual wrappers. True means selected. Multiple wrappers can be selected and composed
        self.w4 = True
        self.w5 = True
        self.w6 = True
        self.w7 = False
        self.w8 = True
        self.w9 = True
        self.w10 = True
        self.w11 = False
        self.rimeTimeout = 10

    def sccDFS(self, visitedC, visitedB, Ci, Bi, component):
        assert min(Ci, Bi) < 0 and max(Ci, Bi) >= 0
        if Ci >= 0 and not visitedC[Ci]:
            visitedC[Ci] = True
            self.sccC[Ci] = component
            for l in self.C[Ci]:
                for d in self.hitmapC[-l]: #clauses that contain the negated literal (offset +1!)
                    self.sccDFS(visitedC, visitedB, d - 1, -1, component)
                for d in self.hitmapB[-l]: #clauses that contain the negated literal (offset +1!)
                    self.sccDFS(visitedC, visitedB, -1, d, component)
        if Bi >= 0 and not visitedB[Bi]:
            visitedB[Bi] = True
            self.sccB[Bi] = component
            for l in self.B[Bi]:
                for d in self.hitmapC[-l]: #clauses that contain the negated literal (offset +1!)
                    self.sccDFS(visitedC, visitedB, d - 1, -1, component)
                for d in self.hitmapB[-l]: #clauses that contain the negated literal (no offset here!)
                    self.sccDFS(visitedC, visitedB, -1, d, component)

    def sccs(self):
        visitedC = [False for _ in range(len(self.C))]
        visitedB = [False for _ in range(len(self.B))]
        self.sccC = [-1 for _ in range(len(self.C))]
        self.sccB = [-1 for _ in range(len(self.B))]
        
        component = 0
        for i in range(len(self.C)):
            if visitedC[i]: continue
            component += 1
            self.sccDFS(visitedC, visitedB, i, -1, component)
        for i in range(len(self.B)):
            if visitedB[i]: continue
            component += 1
            self.sccDFS(visitedC, visitedB, -1, i, component)
        print("-- Number of components after decomposition:", component)
       
        self.components = component 

    # RIME currently handles only .cnf instances. For .gcnf (.wcnf) instances, we employ MCSLS
    def rimeMCSes(self):
        if self.filename[-5:] == ".gcnf":
            return self.rimeWMCSes()
        exportCNF(self.C + self.B, self.rimeFile)        
        cmd = "timeout {} ./tools/rime -v 1 --mcs-limit {} {}".format(self.rimeTimeout, self.rimeMCSLimit, self.rimeFile)
        out = run(cmd, self.rimeTimeout)
        for line in out.splitlines():
            if line[:4] == "MCS ":
                line = line.rstrip().split(" ")[1:]
                mcs = [int(c) for c in line if int(c) < len(self.C)]
                self.mcses.append(mcs)
        print("identified MCSes: ", len(self.mcses))
        if os.path.exists(self.rimeFile) and not self.keep_files:
            os.remove(self.rimeFile)

    def rimeWMCSes(self):
        hard = self.B[:]
        soft = self.C[:]
        open(self.rimeFileW, "w").write(renderWcnf(hard, soft))
        cmd = "timeout {} ./tools/rime -v 1 --mcs-limit {} {}".format(self.rimeTimeout, self.rimeMCSLimit, self.rimeFileW)
        out = run(cmd, self.rimeTimeout)
        mcses = []
        for line in out.splitlines():
            if line[:4] == "MCS ":
                mcs = [int(c) - (len(hard) + 1) for c in line.rstrip().split(" ")[1:]] #0 based indexing
                self.mcses.append(mcs)
        print("identified MCSes: ", len(self.mcses))
        if os.path.exists(self.rimeFileW) and not self.keep_files:
            os.remove(self.rimeFileW)

    def imuAutarkyTrim(self):
        if self.filename[-5:] == ".gcnf":
            print("-- WARNING: The computation of the intersection of MUSes and the autarky is currently not supported for .gcnf instances.")
            print("--- I am keeping the original input (no trim based on the intersection nor autarky).")
            return
        autarky = self.getAutarky() if self.autarky else [i for i in range(len(self.C))]
        imu = self.getImu() if self.imu else []

        C = [self.C[c] for c in sorted(set(autarky) - set(imu))]
        B = [self.C[c] for c in imu]
        if self.autarky: print("autarky size: {} of {} clauses".format(len(autarky), len(self.C)))
        if self.imu: print("imu size:", len(imu))
        self.C, self.B = C, B

    def getAutarky(self):
        cmd = "timeout 3600 python3 autarky.py {}".format(self.filename)
        print(cmd)
        out = run(cmd, 3600)
        if "autarky vars" in out:
            for line in out.splitlines():
                line = line.rstrip()
                if line[:2] == "v ":
                    return [int(c) - 1 for c in line.split()[1:]]
        else: return [i for i in range(len(self.C))]

    def getImu(self):
        cmd = "timeout 3600 python3 gimu.py {}".format(self.filename)
        print(cmd)
        out = run(cmd, 3600)
        if "imu size" in out and not "imu size: 0" in out:
            for line in out.splitlines():
                line = line.rstrip()
                if line[:2] == "v ":
                    return [int(c) - 1 for c in line.split()[1:]]
        else: return []

    def wrapper(self):
        clauses = self.W1()
        if self.w4:
            self.W4() #internally sets up self.min_size
        if self.w6:
            act = maxVar(clauses)
            clauses += self.W6(act)
        if self.w7:
            clauses += self.W7()
        if self.w8:
                self.W8()
        if self.w9:
                self.W9()
        if self.w10:
            act = maxVar(clauses)
            clauses += self.W10(act)
        if self.w11:
            clauses += self.W11()

        #Maximum cardinality wrapper
        #this goes last since it uses the clauses generated by all the wrappers
        if self.w5:
            hard = clauses[:]
            soft = [[self.activators[i]] for i in range(self.dimension)]
            self.max_size = maxSat(hard, soft)
            print("----MAX:", self.max_size)

        if self.min_size > 0:
            act = maxVar(clauses)
            clauses += CardEnc.atleast(lits=self.activators, bound=self.min_size, encoding=8, top_id=act)
            print("-- Using a lower-bound on MUS cardinality:", self.min_size)
        if self.max_size > 0:
            act = maxVar(clauses)
            clauses += CardEnc.atmost(lits=self.activators, bound=self.max_size, encoding=8, top_id=act)
            print("-- Using an upper-bound on MUS cardinality:", self.max_size)

        inds = [i for i in range(1, self.dimension + 1)]
        return clauses, inds

    def remainder(self):
        clauses, inds = self.wrapper()
#        act = max(self.maxVar, maxVar(clauses))
        clauses += self.allSAT()
        return clauses, inds

    def allSAT(self):
        clauses = []

        i = 1
        for cl in self.C:
            renumCl = offsetClause(cl, self.FvarsOffset)
            renumCl.append(-i)
            clauses.append(renumCl)
            i += 1
        for cl in self.B:
            clauses.append(offsetClause(cl, self.FvarsOffset))
        return clauses

    #only self.maxMUSCard copies of Vars(F) used
    def W1(self):   
        clauses = []

        #encode the evidence (removing one clause from the activated set of clauses yields a satisfiable set of clauses)
        for j in range(self.maxMUSCard):
            cls, self.act = tseitinClause([self.selectors[k][j]  for k in range(self.dimension)], self.act) #tseitin for "at last one clause of F is mapped to j-th variable set
            clauses += cls
            t = self.act
            for i in range(self.dimension):
                clauses.append([-t, -self.activators[i], self.selectors[i][j]] + offsetClause(self.C[i], self.evidenceVarsOffsets[j]))
            for cl in self.B:
                clauses.append(offsetClause(cl, self.evidenceVarsOffsets[j]))

        assert self.act == maxVar(clauses)

        enc = 1
        #encode that every clause is selected (assigned to a variable set) at most once
        for i in range(self.dimension):
            crd = CardEnc.atmost(lits=self.selectors[i], bound=1, encoding=enc, top_id=self.act)
            self.act = maxVar(crd) 
            clauses += crd

        #encode that every variable set is assigned to at most one clause
        for j in range(self.maxMUSCard):
            crd = CardEnc.atmost(lits=[self.selectors[k][j] for k in range(self.dimension)], bound=1, encoding=enc, top_id=self.act)
            self.act = maxVar(crd) 
            clauses += crd

        #if f_i is selected then f_i is assigned to a variable set
        for i in range(self.dimension):
            clauses.append([-self.activators[i]] + self.selectors[i])

        return clauses 

    #|F|*Vars(F) variables as used in the CAV'21 paper
    def W1CAV21(self):   
        clauses = []
        for i in range(self.dimension):
            for j in range(self.dimension):
                if j == i: continue
                clauses.append(offsetClause(self.C[j], self.evidenceVarsOffsets[i]) + [-self.activators[j], -self.activators[i]])
            for cl in self.B:
                clauses.append(offsetClause(cl, self.evidenceVarsOffsets[i]) + [-self.activators[i]])
        return clauses 

    # minimum MUS cardinality lower-bound, based on MCS enumeration via RIME
    def W4(self):
        if len(self.mcses) == 0:
            self.rimeMCSes()
        if len(self.mcses) > 0:
            hard = []
            for mcs in self.mcses:
                hard.append([c + 1 for c in mcs]) #+1 indexing for the max sat (we cannot have "0" variables)

            universe = []
            for mcs in hard:
                universe += mcs
            soft = [[-c] for c in set(universe)] #we maximize the number of non-selected clauses
            maxSatValue = maxSat(hard, soft)
            if maxSatValue >= 0:
                self.min_size = len(set(universe)) - maxSatValue #activated = all - non-selected
            else:
                self.min_size = -1

    #SCC based decomposition
    def W6(self, current):
        self.sccs()                                                          
        clauses = []
        acts = []
        for component in range(1, self.components + 1):
            cube = []
            for i in range(len(self.C)):
                if self.sccC[i] != component:
                    cube.append(-(i + 1)) #offset indexing
            cls, current = tseitinCube(cube, current)
            clauses += cls
            acts.append(current)
        clauses.append([a for a in acts])
        return clauses

    #RIME, MCS enumeration 
    def W7(self):
        clauses = []
        if len(self.mcses) == 0:
            self.rimeMCSes()
        if len(self.mcses) > 0:
            for mcs in self.mcses:
                clauses.append([self.activators[c] for c in mcs])
        return clauses

    #Literal negation cover
    def W8(self):
        clauses = []
        for i in range(len(self.C)):
            for l in self.C[i]:
                if len(self.hitmapB[-l]) == 0:
                    clauses.append([-(i + 1)] + self.hitmapC[-l])
        return clauses

    #non-extendable evidence models
    #for each 1<=i<=n we encode that the valuation I_i 
    #does not satisfy the clase f_i
    def W9(self):
        clauses = []
        #max model
        for i in range(len(self.C)):
            renumCl = []
            for l in self.C[i]:
                if l > 0:
                    clauses.append([-(l + self.evidenceVarsOffsets[i])])
                else:
                    clauses.append([-(l - self.evidenceVarsOffsets[i])])
        return clauses

    #enforced evidence models
    #for each 1<=i<=n we encode that the model I_i of E_i
    #is enforced to falsify the clase f_i, 
    #i.e., if we flip an assignemnt to any literal of f_i in I_i, then I_i no longer models E_i
    def W10(self, act):
        clauses = []
        for i in range(len(self.C)):
            for l in self.C[i]:
                cl = [-i]
                acts = []
                for d in self.hitmapC[-l]:                    
                    dAct = self.activators[d - 1]
                    act += 1
                    acts.append(act)
                    cube = [dAct] + [-offset(k, self.evidenceVarsOffsets[i]) for k in self.C[d - 1] if k != -l] #C[d] is activated and l is the only literal of C[d] satisfied by the model
                    #eq encodes that act is equivalent to the cube
                    eq = [[act] + [-x for x in cube]] # one way implication
                    for c in cube: #the other way implication
                        eq += [[-act, c]]
                    clauses += eq
                for d in self.hitmapB[-l]:
                    act += 1
                    acts.append(act)
                    cube = [-offset(k, self.evidenceVarsOffsets[i]) for k in self.B[d] if k != -l] #B[d] is activated and l is the only literal of B[d] satisfied by the model
                    #eq encodes that act is equivalent to the cube
                    eq = [[act] + [-x for x in cube]] # one way implication
                    for c in cube: #the other way implication
                        eq += [[-act, c]]
                    clauses += eq
                cl = [-self.activators[i]] + acts #either C[i] is activated or the literal -l is enforced by one of the activated clauses
                clauses.append(cl)
            #break  
        return clauses

    def W11(self):
        clauses = []
        singletons = 0
        for i in range(self.dimension):
            if len(self.C[i]) == 1: #singleton clause
                singletons += 1
                l = self.C[i][0]
                for j in self.hitmapC[l]:
                    if i + 1 != j: #distinct clause
                        clauses.append([-(i + 1), -j]) #a_(i+1) -> \neg a_j
        print("singletons: {}, clauses: {}".format(singletons, len(clauses)))
        return clauses

    def parseGanak(self, out):
        if "# END" not in out: return -1
        reading = False
        for line in out.splitlines():
            if reading:
                return int(line.rstrip().split()[-1])
            if "# solutions" in line: reading = True

    def parseProjMC(self, out):
        for line in out.splitlines():
            if line[:2] == "s ":
                return int(line.rstrip().split()[1])

    def runExact(self):
        self.ganak = True #currently, we support only ganak (we do not distribute projMC)
        WrapperClauses, WrapperInd = self.wrapper()
        if len(WrapperClauses) > 5200000:
            print("Too large wrapper,", str(len(WrapperClauses)), "terminating")
            sys.exit()
        exportCNF(WrapperClauses, self.WrapperFile, WrapperInd, self.WrapperIndFile)
        
        RemainderClauses, RemainderInd = WrapperClauses + self.allSAT(), WrapperInd
        if len(RemainderClauses) > 5200000:
            print("Too large wrapper,", str(len(RemainderClauses)), "terminating")
            sys.exit()
        exportCNF(RemainderClauses, self.RemainderFile, RemainderInd, self.RemainderIndFile)

        timeout = 3600
        if self.ganak:
            cmd = "timeout {} ./tools/ganak -noIBCP {}".format(timeout, self.RemainderFile)
            cmd = "timeout {} ./tools/ganak -cs 16000 {}".format(timeout, self.RemainderFile)
            remainderSize = self.parseGanak(run(cmd, timeout))
            print("Remainder size:", remainderSize)
            
            cmd = "timeout {} ./tools/ganak -noIBCP {}".format(timeout, self.WrapperFile)
            cmd = "timeout {} ./tools/ganak -cs 16000 {}".format(timeout, self.WrapperFile)
            wrapperSize = self.parseGanak(run(cmd, timeout))
            print("Wrapper size:", wrapperSize)
        else:
            cmd = "timeout {} ./tools/projMC_linux {} -fpv=\"{}\"".format(timeout, self.WrapperFile, self.WrapperIndFile)
            wrapperSize = self.parseProjMC(run(cmd, timeout))
            print("Wrapper size:", wrapperSize)

            cmd = "timeout {} ./tools/projMC_linux {} -fpv=\"{}\"".format(timeout, self.RemainderFile, self.RemainderIndFile)
            remainderSize = self.parseProjMC(run(cmd, timeout))
            print("Remainder size:", remainderSize)
         
        count = -1
        if (wrapperSize >= 0) and (remainderSize >= 0): count = wrapperSize - remainderSize
        print("MUS count:", count)
        if not self.keep_files:
            os.remove(self.RemainderFile)
            os.remove(self.RemainderIndFile)
            os.remove(self.WrapperFile)
            os.remove(self.WrapperIndFile)

import sys
if __name__ == "__main__":
    startTime = time.time()
    parser = argparse.ArgumentParser("MUS counter")
    parser.add_argument("--verbose", "-v", action="count", help = "Use the flag to increase the verbosity of the outputs. The flag can be used repeatedly.")
    parser.add_argument("input_file", help = "A path to the input file. Either a .cnf or a .gcnf instance. See ./examples/")
    parser.add_argument("--w2", action='store_false', help = "Disable the wrapper W2, i.e., computation of the intersection of MUSes.")
    parser.add_argument("--w3", action='store_false', help = "Disable the wrapper W3, i.e., computation of the autarky (overapproximation of the union of MUSes).")
    parser.add_argument("--w4", action='store_false', help = "Disable the wrapper W4, i.e., minimum MUS cardinality.")
    parser.add_argument("--w5", action='store_false', help = "Disable the wrapper W5, i.e., maximum MUS cardinality.")
    parser.add_argument("--w6", action='store_false', help = "Disable the wrapper W6, i.e., component partitioning.")
    parser.add_argument("--w7", action='store_true', help = "Enable the wrapper W7, i.e., MCS enumeration for minimal hitting set duality.")
    parser.add_argument("--w8", action='store_false', help = "Disable the wrapper W8, i.e., literal negation cover.")
    parser.add_argument("--w9", action='store_true', help = "Enable the wrapper W9, i.e., non-extendable evidence models.")
    parser.add_argument("--w10", action='store_true', help = "Enable the wrapper W10, i.e., enforced evidence models.")
    parser.add_argument("--w11", action='store_true', help = "Enable the wrapper W11, i.e., prevent simple implications between activated clauses.")
    parser.add_argument("--rime-timeout", type=int, default=10, help = "Set timeout for RIME (MCS enumeration).")
    parser.add_argument("--rime-mcs-limit", type=int, default=100000, help = "Limit the number of MCSes identified by RIME.")
    parser.add_argument("--min-size", type=int, default=-1, help = "Specify the minimum size (cardinality) of the counted MUSes.")
    parser.add_argument("--max-size", type=int, default=-1, help = "Specify the maximum size (cardinality) of the counted MUSes.")
    parser.add_argument("--keep-files", action='store_true', help = "Do not delete auxiliary files at the end of the computation (for debugging purposes).")
    args = parser.parse_args()


    counter = Counter(args.input_file, args.w3, args.w2)

    if args.keep_files:
        print("-- The flag --keep-files was set. Auxiliary files created during the computation will not be deleted. The created files might include:")
        print("---", counter.tmpFiles)
    else:
        signal.signal(signal.SIGHUP, partial(receiveSignal, counter.tmpFiles))
        signal.signal(signal.SIGINT, partial(receiveSignal, counter.tmpFiles))
        signal.signal(signal.SIGTERM, partial(receiveSignal, counter.tmpFiles))
    
    counter.w4 = args.w4
    counter.w5 = args.w5
    counter.w6 = args.w6
    counter.w7 = args.w7
    counter.w8 = args.w8
    counter.w9 = args.w9
    counter.w10 = args.w10
    counter.w11 = args.w11

    counter.max_size = args.max_size
    counter.min_size = args.min_size
    counter.rimeTimeout = args.rime_timeout
    counter.rimeMCSLimit = args.rime_mcs_limit
    counter.keep_files = args.keep_files
    counter.runExact()
    print("Total execution (clock) time in seconds:", time.time() - startTime) 
