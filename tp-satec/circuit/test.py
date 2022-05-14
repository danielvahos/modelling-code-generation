import unittest
import circuit.circuit as circ
from circuit.cnf import Solver, Cnf, SatVar

class CircuitTest(unittest.TestCase):

    def checkCNF(self, cnf, checker, nSolutions):
        solver = Solver()
        solutions = solver.allSAT(cnf)
        n = 0
        for solution in solutions:
            try:
                result = checker(solution)
                self.assertTrue( result, "Solution is inconsistent with gate function: {}".format(solution) )
            except KeyError:
                self.assertFalse( True, "Incomplete solution {}".format(solution) )
            n += 1
        self.assertEqual( n,  nSolutions, "Expected {} solutions, found {}".format(nSolutions, n) )


    def checkTransform(self, transform, filename, max_tests):
        c = circ.parse(filename)
        cnf = transform(c)
        inputs = c.getInputs()
        outputs = c.getOutputs()
        def validate(sol):
            invalues = dict()
            for i in inputs:
                try:
                    invalues[i] = sol[i]
                except KeyError:
                    self.assertTrue(False, "Did not find value for input signal '%s' in solution" % i)
            result = c.simulate(invalues)
            for o in outputs:
                try:
                    oval = sol[o]
                except KeyError:
                    self.assertTrue(False, "Did not find value for output signal '%s' in solution" % i)
                    self.assertEqual(oval, result[o],
                                     "Inconsistent output value for signal '%s'" % o)
            return True
        tests = 0
        good = 0
        solver = Solver()
        solutions = solver.allSAT(cnf, c.getInputs())
        while tests < max_tests:
            try:
                solution = next(solutions)
            except StopIteration:
                break
            if validate(solution):
                good += 1
            tests += 1
        self.assertEqual(max_tests, tests,
                          "Expected at least {} solutions, found only {}.".format(max_tests, tests))
        self.assertEqual(good, tests,
                          "There were some wrong solutions")


    def checkEquivalence(self, check, file1, file2, expected):
        c1 = circ.parse(file1)
        c2 = circ.parse(file2)
        result, cex = check(c1, c2)
        if expected:
            self.assertTrue(result,
                            "Circuits are equivalent, but reported different.")
        else:
            self.assertFalse(result,
                             "Circuits are different, but reported equivalent.")
            if cex:
                inputValues = {s: cex[s] for s in c1.getInputs()}
                outputValues1 = c1.simulate(inputValues)
                outputValues2 = c2.simulate(inputValues)
                outputs = c1.getOutputs()
                self.assertTrue( any(outputValues1[s] != outputValues2[s] for s in outputs),
                                 "Circuit outputs do not differ for given counterexample.")


