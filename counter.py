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


def run(cmd, timeout, ttl = 3):
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

def exportCNF(clauses, filename, ind, varFile):
    print("running export for ", filename)
    with open(filename, "w") as f:
        if len(ind) > 0:
            f.write("c ind " + " ".join([str(i) for i in ind]) + " 0\n")
        maxVar = max([max(abs(l) for l in cl) for cl in clauses])
        f.write("p cnf {} {}\n".format(maxVar, len(clauses)))
        for cl in clauses:
            f.write(" ".join([str(l) for l in cl]) + " 0\n")

    print(varFile)
    with open(varFile, "w") as f:
        f.write(",".join ([str(v) for v in ind]))

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

class Counter:
    def __init__(self, filename, useAutarky, useImu):
        self.filename = filename
        self.C, self.B = parse(filename)
        self.imuSize = 0
        self.imu = useImu
        self.autarky = useAutarky
        if self.autarky and filename[-4:] == ".cnf":
            self.autarkyTrim()
        self.dimension = len(self.C)
        self.rid = randint(1,10000000)
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


        self.WrapperFile = "/var/tmp/wrapper_{}.cnf".format(self.rid)
        self.WrapperIndFile = self.WrapperFile[:-4] + "_ind.cnf"
        self.RemainderFile = "/var/tmp/remainder_{}.cnf".format(self.rid)
        self.RemainderIndFile = self.RemainderFile[:-4] + "_ind.cnf"
        self.tmpFiles = [self.WrapperFile, self.WrapperIndFile, self.RemainderFile, self.RemainderIndFile]

        self.activators = [i + 1 for i in range(self.dimension)]
        self.evidenceActivators = []
        for i in range(1, self.dimension + 1):
            self.evidenceActivators.append([i*self.dimension + j  for j in range(1, self.dimension + 1)])
        self.FvarsOffset = (self.dimension + 1) * self.dimension
        self.evidenceVarsOffsets = []
        CBmaxVar = maxVar(self.C + self.B)
        for i in range(1, self.dimension + 1):
            self.evidenceVarsOffsets.append(self.FvarsOffset + i*CBmaxVar)
        print("activators:", self.activators)
        print()
        print("evidence activators:", self.evidenceActivators)
        print()
        print("F's variables offset:", self.FvarsOffset)
        print()
        print("evidence variables' offsets:", self.evidenceVarsOffsets)


    def autarkyTrim(self):
        assert self.B == []
        cmd = "timeout 3600 python3 autarky.py {}".format(self.filename)
        print(cmd)
        out = run(cmd, 3600)
        if "autarky vars" in out:
            for line in out.splitlines():
                line = line.rstrip()
                if line[:2] == "v ":
                    autarky = [int(c) - 1 for c in line.split()[1:]]
        else: return

        imu = self.getImu() if self.imu else []
        self.imuSize = len(imu)

        coAutarky = [i for i in range(len(self.C)) if i not in autarky]
        C = [self.C[c] for c in sorted(set(autarky) - set(imu))]
        B = [self.C[c] for c in coAutarky + imu]
        print("autarky size: {} of {} clauses".format(len(autarky), len(self.C)))
        print("imu size:", len(imu))
        self.C, self.B = C, B

    def getImu(self):
        cmd = "timeout 3600 python3 gimu.py {}".format(self.filename)
        print(cmd)
        out = run(cmd, 3600)
        if "imu size" in out:
            for line in out.splitlines():
                line = line.rstrip()
                if line[:2] == "v ":
                    return [int(c) - 1 for c in line.split()[1:]]
        else: return []

    def wrapper(self):
        clauses = self.W1()
#        if self.w4:
#            clauses += self.W4()
#        if self.w5:
#            act = max(self.maxVar, maxVar(clauses))
#            clauses += self.W5(act)

        inds = [i for i in range(1, self.dimension + 1)]
        return clauses, inds

    def remainder(self):
        clauses, inds = self.wrapper()
#        act = max(self.maxVar, maxVar(clauses))
        clauses += self.allSAT()
        return clauses, inds

    def W1(self):   
        clauses = []
        for i in range(self.dimension):
            #the first conjunct, i.e., A - {f_i} = E_i - {f_i}
            for j in range(self.dimension):
                if j == i: continue
                clauses.append([-self.activators[j], self.evidenceActivators[i][j]]) 
                clauses.append([self.activators[j], -self.evidenceActivators[i][j]]) 

            #the second conjunct
            clauses.append([-self.evidenceActivators[i][i]]) 

            #the third conjunct
            sat = []
            actId = 0
            for cl in self.C:
                renumCl = offsetClause(cl, self.evidenceVarsOffsets[i])
                renumCl.append(-self.evidenceActivators[i][actId])
                sat.append(renumCl)
                actId += 1
            for cl in self.B:
                sat.append(offsetClause(cl, self.evidenceVarsOffsets[i]))
            for cl in sat:
                clauses.append([-self.activators[i]] + cl) 

        return clauses 

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


    def W4(self):
        clauses = []
        #max model
        i = 1
        for cl in self.C:
            renumCl = []
            for l in cl:
                if l > 0:
                    clauses.append([-i, -(l + 2*self.dimension)])
                else:
                    clauses.append([-i, -(l - 2*self.dimension)])
            i += 1

        return clauses

    def W5(self, act):
        clauses = []
        for i in range(len(self.C)):
            for l in self.C[i]:
                cl = [-i]
                acts = []
                for d in self.hitmapC[-l]:
                    act += 1
                    acts.append(act)
                    cube = [-d] + [-offset(k, 2*self.dimension) for k in self.C[d - 1] if k != -l] #C[d] is activated and l is the only literal of C[d] satisfied by the model
                    #eq encodes that act is equivalent to the cube
                    eq = [[act] + [-x for x in cube]] # one way implication
                    for c in cube: #the other way implication
                        eq += [[-act, c]]
                    clauses += eq
                for d in self.hitmapB[-l]:
                    act += 1
                    acts.append(act)
                    cube = [-offset(k, 2*self.dimension) for k in self.B[d] if k != -l] #B[d] is activated and l is the only literal of B[d] satisfied by the model
                    #eq encodes that act is equivalent to the cube
                    eq = [[act] + [-x for x in cube]] # one way implication
                    for c in cube: #the other way implication
                        eq += [[-act, c]]
                    clauses += eq
                cl = [-(i + 1)] + acts #either C[i] is activated or the literal -l is enforced by one of the activated clauses
                clauses.append(cl)
            #break  
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
        self.ganak = True
        WrapperClauses, WrapperInd = self.wrapper()
        if len(WrapperClauses) > 1200000:
            print("Too large wrapper,", str(len(WrapperClauses)), "terminating")
            sys.exit()
        exportCNF(WrapperClauses, self.WrapperFile, WrapperInd, self.WrapperIndFile)
        print(self.WrapperFile)
        
        RemainderClauses, RemainderInd = self.remainder()
        if len(RemainderClauses) > 1200000:
            print("Too large wrapper,", str(len(RemainderClauses)), "terminating")
            sys.exit()
        exportCNF(RemainderClauses, self.RemainderFile, RemainderInd, self.RemainderIndFile)
        print(self.RemainderFile)

        timeout = 3600
        if self.ganak:
            cmd = "timeout {} /home/xbendik/bin/ganak/build/ganak {}".format(timeout, self.WrapperFile)
            print(cmd)
            wrapperSize = self.parseGanak(run(cmd, timeout))
            print("Wrapper size:", wrapperSize)

            cmd = "timeout {} /home/xbendik/bin/ganak/build/ganak {}".format(timeout, self.RemainderFile)
            print(cmd)
            remainderSize = self.parseGanak(run(cmd, timeout))
            print("Remainder size:", remainderSize)
        else:
            cmd = "timeout {} ./projMC_linux {} -fpv=\"{}\"".format(timeout, self.WrapperFile, self.WrapperIndFile)
            print(cmd)
            wrapperSize = self.parseProjMC(run(cmd, timeout))
            print("Wrapper size:", wrapperSize)

            cmd = "timeout {} ./projMC_linux {} -fpv=\"{}\"".format(timeout, self.RemainderFile, self.RemainderIndFile)
            print(cmd)
            wrapperSize = self.parseProjMC(run(cmd, timeout))
            print("Remainder size:", remainderSize)
         
        count = -1
        if (wrapperSize >= 0) and (remainderSize >= 0): count = wrapperSize - remainderSize
        print("MUS count:", count)
        os.remove(self.RemainderFile)
        os.remove(self.RemainderIndFile)
        os.remove(self.WrapperFile)
        os.remove(self.WrapperIndFile)

import sys
if __name__ == "__main__":
    parser = argparse.ArgumentParser("MUS counter")
    parser.add_argument("--verbose", "-v", action="count", help = "Use the flag to increase the verbosity of the outputs. The flag can be used repeatedly.")
    parser.add_argument("input_file", help = "A path to the input file. Either a .cnf or a .gcnf instance. See ./examples/")
    parser.add_argument("--imu", action='store_true', help = "Use IMU.")
    parser.add_argument("--autarky", action='store_true', help = "Use autarky to trim the input formula.")
    args = parser.parse_args()

    counter = Counter(args.input_file, args.autarky, args.imu)
    signal.signal(signal.SIGHUP, partial(receiveSignal, counter.tmpFiles))
    signal.signal(signal.SIGINT, partial(receiveSignal, counter.tmpFiles))
    signal.signal(signal.SIGTERM, partial(receiveSignal, counter.tmpFiles))

    counter.runExact()
