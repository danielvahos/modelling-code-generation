#!/usr/bin/env python3

import satispy
from satispy.solver import Minisat
from functools import reduce

def maxvar(clauses):
    m = 0
    for c in clauses:
        for l in c.literals:
            m = max(m, l.id)
    return m

class Cnf(object):
    '''Represents a Boolean formula in conjunctive normal form (CNF) or
    product of sum form (POS).
    '''

    def __init__(self, clauses = []):
        '''Constructor. If defined, the CNF is initialized with the given set of clauses.'''

        self.clauses = [cl for cl in clauses]
        self.variables = set()
        for c in clauses:
            self.variables |= {l.name for l in c.literals}
        self.maxVar = maxvar(clauses)

    def className(self):
        return 'Cnf'

    def __and__(self, other):
        if type(other) is Cnf:
            return Cnf([l for l in self.clauses + other.clauses])
        elif other.className() == 'Clause':
            return Cnf([l for l in self.clauses + [other]])
        elif other.className() == 'SatVar':
            return Cnf(self.clauses + [Clause([other])])
        else:
            raise TypeError('incompatible types')

    def __iand__(self, other):
        if type(other) is Cnf:
            self.clauses += [l for l in other.clauses]
            self.variables |= other.variables
            self.maxVar = max(self.maxVar, other.maxVar)
            return self
        elif other.className() == 'Clause':
            self.clauses.append(other)
            self.variables |= {l.name for l in other.literals}
            self.maxVar = max(self.maxVar, maxvar([other]))
            return self
        elif other.className() == 'SatVar':
            self.clauses.append(Clause([other]))
            self.variables.add(other.name)
            self.maxVar = max(self.maxVar, other.id)
            return self
        else:
            raise TypeError('incompatible types')
        return self

    def dimacs(self):
        '''Dump CNF in DIMACS format'''

        s = 'p cnf %d %d\n' % (self.maxVar, len(self.clauses))
        cls = [c.dimacs() for c in self.clauses]
        s += '\n'.join(cls)
        return s

    def __repr__(self):
        cls = [str(c) for c in self.clauses]
        s = ' & '.join(cls)
        return s


class Clause(object):
    '''Represents a clause, which is a disjunction of literals.'''

    def __init__(self, literals = []):
        self.literals = [l for l in literals]

    def className(self):
        return 'Clause'

    def __and__(self, other):
        if type(other) == Clause:
            return Cnf([self, other])
        else:
            return Cnf([self]) & Cnf([Clause([other])])

    def __or__(self, other):
        if type(other) is Clause:
            return Clause([l for l in self.literals + other.literals])
        elif other.className() == 'SatVar':
            return Clause([l for l in self.literals + [other]])
        else:
            raise TypeError('incompatible types')

    def __ior__(self, other):
        if type(other) is Clause:
            self.literals += [l for l in other.literals]
            return self
        elif other.className() == 'SatVar':
            self.literals.append(other)
            return self
        else:
            raise TypeError('incompatible types')

    def __repr__(self):
        lits = [str(l) for l in self.literals]
        return '(' + ' | '.join(lits) + ')'

    # def __eq__(self, other):
    #     return self.literals == other.literals

    # def __hash__(self):
    #     h = 0
    #     for x in sorted(self.literals):
    #         h += x.__hash__()
    #         h *= 3
    #     return h

    def dimacs(self):
        '''Dump the clause in DIMACS format'''

        lits = [l.dimacs() for l in self.literals]
        return ' '.join(lits) + ' 0'


class SatVar(object):
    '''Represents a variable used to construct a CNF. The declared
    variables are given a unique integer identifier, starting with
    1. The identifier is global, so multiple CNF instances will share
    the same identifier. There is (currently?) no way to reset the
    next identifier to 1. As long as the internal Solver interface is
    used, this does not pose any problem, since the integer ids are
    only used for DIMACS dumping.

    There is no difference between "variables" and "literals". The
    phase is actually stored in this class, so a positive literal is
    just a variable and a negative literal is an inverted
    variable. Use the overloaded ~ operator to negate a literal.

    Use the constructor SatVar() to get a fresh variable.
    '''

    __nextid__ = 1
    __vartable__ = dict()

    def __init__(self, name=None, phase=True):
        '''Constructs a SAT variable. If phase is False, constructs a negative
        literal, otherwise a positive one.'''

        if name is None:
            name = 'SatVar__{}'.format(SatVar.__nextid__)

        self.name = str(name)
        self.phase = phase
        try:
            self.id = SatVar.__vartable__[self.name]
        except KeyError:
            self.id = SatVar.__nextid__
            SatVar.__nextid__ += 1
            SatVar.__vartable__[self.name] = self.id
            # print ('{} -> {}'.format(name, self.id))

    def className(self):
        return 'SatVar'

    def dimacs(self):
        '''Dump variable/literal in DIMACS format.'''

        if self.phase:
            return str(self.id)
        else:
            return '-%s' % str(self.id)

    def __repr__(self):
        if self.phase:
            return self.name
        else:
            return '~%s' % self.name

    def __bool__(self):
        return self.phase

    def __lt__(self, other):
        x = self.id
        if not self.phase:
            x = -x
        y = other.id
        if not other.phase:
            y = -y
        return x < y

    def __invert__(self):
        return SatVar(self.name, not self.phase)

    def __or__(self, other):
        if type(other) is SatVar:
            return Clause([self, other])
        elif type(other) is Clause:
            return other | self
        else:
            raise TypeError('incompatible types')

    def __and__(self, other):
        if type(other) is SatVar:
            return Clause([self]) & Clause([other])
        elif type(other) is Clause:
            return other & self
        elif type(other) is Cnf:
            return other & self
        else:
            raise TypeError('incompatible types')

    def __eq__(self, other):
        return type(other) == SatVar and other.id == self.id and other.phase == self.phase

    def __hash__(self):
        return self.id if self.phase else -self.id


class Solution:
    '''Represents the solution of a SAT problem, which is either UNSAT or
    SAT. In the latter case, an assignment is stored an can be
    accessed by standard item access [] or with an item() iterator.
    '''

    def __init__(self, sat, assignment = None):
        self.assignment = assignment
        self.sat = sat

    def __repr__(self):
        if not self.sat:
            return "UNSAT"
        else:
            return "SAT " + str(self.assignment)

    def __getitem__(self, v):
        if type(v) is SatVar:
            return self.assignment[v.name]
        else:
            return self.assignment[str(v)]

    def items(self):
        return self.assignment.items()

    def keys(self):
        return self.assignment.keys()

    def project(self, variables):
        '''Project the solution on a subset of variables (destructive)'''

        projection = dict()
        for v in variables:
            try:
                if type(v) is SatVar:
                    projection[v.name] = self.assignment[v.name]
                else:
                    projection[v] = self.assignment[v]
            except KeyError:
                print ("[WARNING] Non-existent variable '{}' ignored in projection.".format(v))
        self.assignment = projection
        return self

    def __bool__(self):
        return self.sat

    def __invert__(self):
        '''Returns a blocking clause for this solution.'''
        if not self.sat:
            return None
        bc = None
        for x, b in self.assignment.items():
            l = ~SatVar(x) if b else SatVar(x)
            if bc is None:
                bc = l
            else:
                bc |= l
        return bc


class Solver:
    '''SAT solver interface. Call solve() on a CNF object to solve it.'''

    def __init__(self):
        self.solver = Minisat()

    def solve(self, cnf):
        '''Solve a SAT problem in CNF form. Internally calls Minisat. Returns
        a Solution object.'''

        if type(cnf) is Clause:
            return self.solve(Cnf({cnf}))
        elif type(cnf) is SatVar:
            return self.solve(Clause({cnf}))
        def literal(lit):
            v = satispy.Variable(lit.name)
            if lit:
                return v
            else:
                return -v
        def clause(cls):
            lits = [literal(l) for l in cls.literals]
            c = lits.pop()
            for l in lits:
                c = c | l
            return c
        clauses = [clause(c) for c in cnf.clauses]
        expr = clauses.pop()
        for c in clauses:
            expr = expr & c
        solution = self.solver.solve(expr)
        if solution.success:
            assignment = {x: solution[satispy.Variable(x)] for x in cnf.variables}
            return Solution(True, assignment)
        else:
            return Solution(False)


    def allSAT(self, cnf, blockVars = None):
        '''Returns a generator function that can be used to enumerate all solutions of a CNF wrt to a set of variables (blockVars). '''
        while True:
            solution = self.solve(cnf)
            if not solution:
                return
            yield solution
            if blockVars:
                solution.project(blockVars)
            block = ~solution
            cnf &= block

# ================================================================= TEST CODE

if __name__ == '__main__':

    # Declare SAT variables
    a = SatVar('a')
    b = SatVar('b')
    c = SatVar('c')
    d = SatVar('d')

    # Use overloaded operators to build CNF
    cnf = (a | c) & ~a & d & (~a | ~b | ~c | ~d)
    print (cnf)

    # Dump DIMACS format, which can be fed to any standard SAT solver
    print ("DIMACS FORMAT: -------------------")
    print (cnf.dimacs())
    print ("----------------------------------")

    # Use the solver interface (uses Minisat internally)
    solver = Solver()
    solution = solver.solve(cnf)

    # Examine solution
    print ("SOLUTION:")

    # This prints UNSAT or SAT and the found assignment
    print (solution)

    # In the Boolean context, True corresponds to a satisfiable solution
    if solution:

        # Use SAT variable as index to retrieve solution (True or False)
        print ('a = %s' % str(solution[a]))

        # Use variable name (string) as index to retrieve solution
        print ('b = %s' % str(solution['b']))

        # Iterate over all solutions (v is a string, x a Boolean)
        for v, x in solution.items():
            print ('%s = %s' % (v, str(x)))
