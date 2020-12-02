import sys
from math import log
import subprocess as sp
sys.path.insert(0, "/home/xbendik/usr/lib/lib/python3.7/site-packages")
import random
import time
from statistics import median
from random import randint
from z3 import *

def maxVar(C):
    m = 0
    for cl in C:
        for l in cl:
            if l < 0: l *= -1
            m = max(m,l)
    return m

def sign(a):
    if a > 0: return 1
    else: return -1

class CSSolver:
    def __init__(self, A, B):
        self.A = A
        self.B = B
        self.vars = []
        for i in range(0,maxVar(A+B) + 1):
            self.vars.append(Bool('x' + str(len(self.vars))))
        
        self.acts = []
        for i in range(len(A)):
            self.acts.append(Bool('a' + str(len(self.acts))))
        self.s = Solver()
        #add the base (hard) clauses to the solver
        for cl in B:        
            clb = self.makeCl(cl)
            self.s.add(Or(clb))
        
        #add the soft clauses to the solver
        for i in range(len(A)):
            clb = self.makeCl(A[i])
            self.s.add(Or(clb + [self.acts[i]]))

        self.hitmap_pos = {}
        self.hitmap_neg = {}
        self.build_hitmaps(A, B)

    def build_hitmaps(self,A,B):
        for i in range(len(A + B)):
            cl = (A + B)[i]
            for l in cl:
                if l > 0:
                    var = str(self.vars[l - 1])
                    if var not in self.hitmap_pos: self.hitmap_pos[var] = []
                    self.hitmap_pos[var].append(i)
                else:
                    var = str(self.vars[-1 * (l + 1)])
                    if var not in self.hitmap_neg: self.hitmap_neg[var] = []
                    self.hitmap_neg[var].append(i)
            

    def makeCl(self, cl):
        clb = []
        for l in cl:
            if l > 0: 
                clb.append(self.vars[l - 1])
            else:
                clb.append(Not(self.vars[-1 * (l + 1)]))
        return clb

    def solve(self, N = []):
        assumptions = []
        for i in range(len(N)):
            if N[i]: assumptions.append(Not(self.acts[i]))
        return self.s.check(assumptions) == sat 

    def getCore(self):
        core = []
        for c in self.s.unsat_core():
            c = str(c)
            assert c[:4] == "Not("
            a = int(c[5:-1]) 
            core.append(a)
        return core

    def satisfies(self, model, cid):
        cl = self.A[cid] if cid < len(self.A) else self.B[cid]
        for l in cl:
            if l > 0:
                var = str(self.vars[l - 1])
                if var not in model:
                    model[var] = True
                if model[var]: return True
            else:
                var = str(self.vars[-1 * (l + 1)])
                if var not in model:
                    model[var] = False
                if not model[var]: return True
        return False

    def revealConflict(self, K, model, var, polarity):
        violated = []
        if polarity:
            for cid in self.hitmap_pos[var]:
                if not self.satisfies(model, cid):
                    violated.append(cid)
        else:
            for cid in self.hitmap_neg[var]:
                if not self.satisfies(model, cid):
                    violated.append(cid)
        assert len(violated) > 0
        if len(violated) > 1 or violated[0] >= len(self.A) or violated[0] in K:
            return None
        return violated[0]
    
    def rotation_rec(self, K, f, model):
        assert f not in K
        K.append(f)
        for l in self.A[f]:
            if l > 0:
                var = str(self.vars[l - 1])
                model[var] = True
                cid = self.revealConflict(K, model, var, False)
                if cid is not None:
                    assert cid not in K
                    self.rotation_rec(K, cid, model)
                model[var] = False
            else:
                var = str(self.vars[-1 * (l + 1)])
                model[var] = False
                cid = self.revealConflict(K, model, var, True)
                if cid is not None:
                    assert cid not in K
                    self.rotation_rec(K, cid, model)
                model[var] = True
            
    
    def rotation(self, K, f):        
        m = self.s.model()
        model = {}
        for x in m:
            model[str(x)] = is_true(m[x])
        self.rotation_rec(K, f, model)

#parse .gcnf or .cnf instance,
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

def getIMU(A,B,M = []):
    print("hard:", len(B))
    print("soft:", len(A))
    K = []
    C = [i for i in range(len(A))]
    s = CSSolver(A,B)
    whole = [True for _ in A]
    while len(C) > 0:
        print("clauses left:", len(C))
        f = C.pop()
        whole[f] = False
        if s.solve(whole):
            s.rotation(K, f)
            C = list(set(C) - set(K))
        else:
            core = s.getCore()
            C = list(set(C).intersection(set(core)))
        whole[f] = True
    print("imu size: {}".format(len(K)))
    print("imu size: {}".format(len(C)))
    print("hard:", len(B))
    print("soft:", len(A))

    imu = ["v"] + [str(f + 1) for f in sorted(K)]
    print(" ".join(imu))

import sys
if __name__ == "__main__":
    assert len(sys.argv) == 2
    filename = sys.argv[1]
    C,B = parse(filename)
    getIMU(C,B)
