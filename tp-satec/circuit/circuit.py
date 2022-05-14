#!/usr/bin/env python3

class BrokenCircuitException(Exception):
    '''This exception is thrown by the constructor of the Cicruit class if
    it detects either undefined signals or combinational loops.
    '''
    pass

class Node(object):
    '''Base class for circuit nodes'''

    __nextid__ = 0

    def __init__(self):
        self.kids = []
        self.id = Node.__nextid__
        Node.__nextid__ += 1

    def __lt__(self, other):
        return self.id < other.id

    def __hash__(self):
        return hash(7879 + self.id) * hash(type(self))

    def getID(self):
        '''Get unique node id (as int)'''
        return self.id

    def getChildren(self):
        '''Get child nodes of this node'''
        return self.kids

    def getChild(self, i):
        '''Get i-th child of this node'''
        return self.kids[i]

    def setChild(self, i, nd):
        '''Set i-th child of this node'''
        self.kids[i] = nd

    def support(self):
        return set()

class Literal(Node):
    '''A circuit node representing a constant Boolean value, which is
    either True or False.
    '''

    def __init__(self, b):
        Node.__init__(self)
        self.value = b

    def __repr__(self):
        if self.value:
            return '1'
        else:
            return '0'

    def getValue(self):
        '''Get the literal's value'''
        return self.value

    def support(self):
        return set()

class Variable(Node):
    '''A circuit node representing a named internal or input signal.'''

    def __init__(self, name):
        Node.__init__(self)
        self.name = name

    def __repr__(self):
        return ('%s' % self.name)

    def getName(self):
        '''Get the name of the signal'''
        return self.name

    def support(self):
        return {self.name}

class OpNode(Node):
    '''Abstract base class for unary and binary logic gates.'''

    def getOp(self):
        '''Get a string representation of the node's function'''
        return self.opstr

    def getFun(self):
        '''Get the gate function of the node'''
        return self.f

class BinOp(OpNode):
    '''A circuit node representing a binary logic gate.'''

    def __init__(self, f, opstr, x, y):
        Node.__init__(self)
        self.kids = [x, y]
        self.f = f
        self.opstr = opstr

    def __repr__(self):
        return ('(%s %s %s)' % (self.kids[0], self.opstr, self.kids[1]))

    def eval(self, x, y):
        '''Evaluate the node's function with the given inputs'''
        return self.f(x, y)

    def support(self):
        return self.getChild(0).support() | self.getChild(1).support()

class UnOp(OpNode):
    '''A circuit node representing a unary logic gate.'''

    def __init__(self, f, opstr, x):
        Node.__init__(self)
        self.kids = [x]
        self.f = f
        self.opstr = opstr

    def __repr__(self):
        return ('(%s %s)' % (self.opstr, self.kids[0]))

    def eval(self, x):
        '''Evaluate the node's function with the given input'''
        return self.f(x)

    def support(self):
        return self.getChild(0).support()


class Circuit(object):
    '''Class representing a logic circuit.'''

    def __init__(self, name, inputs, outputs, eqs):
        self.name = name
        self.inputs = {x.name for x in inputs}
        self.outputs = {x.name for x in outputs}
        self.equations = dict()
        for (x,e) in eqs:
            self.equations[x.name] = e
        self.check()

    def check(self):
        '''Perform sanity checks on the circuit: all outputs defined, all
        inputs unconstrained, no undefined signals, no combinational
        loops. This function is called by the constructor.
        '''

        # Check that all outputs are defined
        for x in self.outputs:
            if not x in self.equations.keys():
                raise BrokenCircuitException("Undefined output '%s'" % x)

        # Check that inputs are unconstrained
        for x in self.inputs:
            if x in self.equations.keys():
                raise BrokenCircuitException("Over-constrained input '%s' " % x)

        # Check that only defined signals are used
        deps = {x: self.equations[x].support() for x in self.equations.keys()}
        signals = self.inputs | self.outputs | self.equations.keys()
        for x,ys in deps.items():
            for y in ys:
                if not y in signals:
                    raise BrokenCircuitException("Undefined signal '%s'" % y)

        # Check that there are no combinational loops in the circuit
        for x in deps.keys():
            stack = []
            def visit(y):
                if y in stack:
                    raise BrokenCircuitException("Combinational loop detected: %s -> %s" % (' -> '.join(stack), y))
                if not y in deps.keys():
                    return
                stack.append(y)
                for z in deps[y]:
                    visit(z)
                stack.pop()
            visit(x)

    def clean(self):
        '''Clean up the structure of the circuit: Collapse nodes with single
        fanout, remove dead nodes.
        '''

        # Collapse non-fanout nodes
        signals = self.outputs | self.equations.keys() | self.inputs
        fanout = {s: set() for s in signals}
        deps = {x: self.equations[x].support() for x in self.equations.keys()}
        for x, ys in deps.items():
            for y in ys:
                fanout[y].add(x)
        collapse = {x for x,ys in fanout.items() if len(ys) == 1}.difference(self.inputs)
        print ("======================")
        print ("COLLAPSE:")
        print (collapse)
        print ("======================")
        def eval(nd, a, b):
            f = nd.getFun()
            return Literal(f(a.getValue(), b.getValue()))
        for x in self.getFanoutSignals():
            def subst(nd):
                if type(nd) == Variable:
                    y = nd.getName()
                    if y in collapse:
                        return subst(self.equations[y])
                    else:
                        return nd
                elif type(nd) == UnOp:
                    nd.setChild(0, subst(nd.getChild(0)))
                    return nd
                elif type(nd) == BinOp:
                    c1 = subst(nd.getChild(0))
                    c2 = subst(nd.getChild(1))
                    if type(c1) is Literal and type(c2) is Literal:
                        return eval(nd, c1, c2)
                    else:
                        nd.setChild(0, c1)
                        nd.setChild(1, c2)
                        return nd
                else:
                    return nd
            e = self.equations[x]
            self.equations[x] = subst(e)

        # Remove dead nodes
        deps = {x: self.equations[x].support() for x in self.equations.keys()}
        def dependencies(x):
            try:
                return deps[x]
            except KeyError:
                return set()
        reachable = {x for x in self.outputs}
        while True:
            imgs = [dependencies(x) for x in reachable]
            nextReachable = {y for dep in imgs for y in dep}
            if nextReachable.issubset(reachable):
                break
            reachable |= nextReachable
        dead = signals.difference(reachable).difference(self.inputs)
        print ("DEAD:")
        print (dead)
        print ("======================")
        for s in dead:
            del self.equations[s]

    def getInputs(self):
        '''Returns the set of input identifiers.
        '''
        return self.inputs

    def getOutputs(self):
        '''Returns the set of output identifiers.
        '''
        return self.outputs

    def getInternalSignals(self):
        '''Returns the set of internal fanout signals.
        '''
        return self.getFanoutSignals() - self.getOutputs()

    def getFanoutSignals(self):
        '''Returns the set of identifiers for which a logic equation is
        defined. This includes the circuit's outputs and any internal
        signals.
        '''
        return set(self.equations.keys())

    def getNode(self, x):
        '''Returns the root node of the logic expression assigned to signal x,
        where x is either an output or an internal signal.
        '''
        try:
            return self.equations[x]
        except KeyError:
            raise BrokenCircuitException("Undefined signal '%s'" % s)

    def simulate(self, inputs):
        '''Simulate the circuit. Takes as input a dictionary, mapping input
        names to Boolean values. Returns a dictionary mapping input, output
        and internal signal names to Boolean values.
        '''

        value = {i: x for (i,x) in inputs.items()}

        def sim(node):
            if type(node) == Literal:
                return node.value
            elif type(node) == Variable:
                x = node.name
                try:
                    return value[x]
                except KeyError:
                    y = sim(self.getNode(x))
                    value[x] = y
                    return y
            elif type(node) == UnOp:
                y = sim(node.getChild(0))
                return node.eval(y)
            elif type(node) == BinOp:
                y = sim(node.getChild(0))
                z = sim(node.getChild(1))
                return node.eval(y, z)
            else:
                raise "Invalid node type."

        signals = self.getFanoutSignals()
        for x in signals:
            value[x] = sim(self.getNode(x))
        return {s: x for (s,x) in value.items() if s in signals | self.inputs}

    def dot(self):
        s = 'digraph %s {\n' % self.name
        s += '  rankdir="LR";\n'
        for x in self.getInputs():
            s += '  %s [label=\"%s\", shape=circle];\n' % (x, x)
        for x in self.getOutputs():
            s += '  %s [label=\"%s\", shape=diamond];\n' % (x, x)
        for x in self.getInternalSignals():
            s += '  %s [label=\"%s\", shape=hexagon];\n' % (x, x)
        drawn = dict()
        def draw(nd):
            if nd in drawn.keys():
                return ''
            elif type(nd) is Literal:
                s = '\t%d [label="%d", shape=rect];\n' % (nd.getID(), nd.getValue())
                drawn[nd] = str(nd.getID())
                return s
            elif type(nd) is Variable:
                drawn[nd] = nd.getName()
                return ''
            elif type(nd) is UnOp:
                s = draw(nd.getChild(0))
                cid = drawn[nd.getChild(0)]
                myid = str(nd.getID())
                s += '  %s [label="%s", shape=square, style=filled, color=gray];\n' % (myid, nd.getOp())
                s += '  %s -> %s;\n' % (cid, myid)
                drawn[nd] = myid
                return s
            elif type(nd) is BinOp:
                s = draw(nd.getChild(0))
                s += draw(nd.getChild(1))
                myid = str(nd.getID())
                lid = drawn[nd.getChild(0)]
                rid = drawn[nd.getChild(1)]
                s += '  %s [label="%s", shape=square, style=filled, color=gray];\n' % (myid, nd.getOp())
                s += '  %s -> %s;\n' % (lid, myid)
                s += '  %s -> %s;\n' % (rid, myid)
                drawn[nd] = myid
                return s
            else:
                raise TypeError('invalid node')
        for x in self.getFanoutSignals():
            e = self.getNode(x)
            s += draw(e)
            s += '  %s -> %s' % (drawn[e], x)
        s += '}'
        return s

    def __repr__(self):
        s = 'circ %s {\n' % self.name
        s += '\tinputs: %s\n' % ', '.join(sorted(self.inputs))
        s += '\toutputs: %s\n' % ', '.join(sorted(self.outputs))
        for x, e in self.equations.items():
            s += '\t%s = %s\n' % (x, e)
        s += '}'
        return s

# ========================================================================= Parser

from funcparserlib.parser import *
from funcparserlib.parser import with_forward_decls
from tokenize import generate_tokens, TokenInfo
from io import StringIO
from functools import reduce

import token

# FIXME: There seems to be an inconsistency between the token.type and
# the type constants defined in token!
MY_NEWLINE = 58
MY_NEWLINE2 = 56
MY_NEWLINE3 = 61

def tokenize(s):
    return [t for t in  generate_tokens(StringIO(s).readline)
            if t.type not in [token.ENDMARKER, token.NEWLINE, MY_NEWLINE, MY_NEWLINE2, MY_NEWLINE3]]

def tokval(tok):
    return tok.string

def make_bool(s):
    return s == '1'

# @RULE:
# boolean ::= '1' | '0'
boolean = (
    some(lambda tok: tok.type == token.NUMBER and tok.string in ['1','0'])
    >> tokval
    >> make_bool
    >> Literal
)

# @RULE
# variable ::= NAME (as Variable)
variable = (
    some(lambda tok: tok.type == token.NAME)
    >> tokval
    >> Variable
)

# @RULE
# variable ::= NAME (as string)
name = (
    some(lambda tok: tok.type == token.NAME)
    >> tokval
)

# Operator functor
op = (
    lambda s: some(lambda tok: tok.type == token.OP and tok.string == s)
    >> tokval
)

comma = op(',')

# Keyword functor
keyword = (
    lambda s: some(lambda tok: tok.type == token.NAME and tok.string == s)
    >> tokval
    )

# @KEYWORD 'inputs'
inp = keyword('inputs')

# @KEYWORD 'outputs'
outp = keyword('outputs')

# @KEYWORD 'circ'
circ = keyword('circ')

const = lambda x: lambda _: x

# Functor for operator construction. Returns a parser functor that
# results in the second argument f, the function associated with the
# operator.
makeop = lambda s, f: op(s) >> const(f)

# Functor constructing a binary node
def make_node(f, opstr):
    return lambda x, y: BinOp(f, opstr, x, y)

# Functor constructing a unary node
def make_unode(f, opstr):
    return lambda x: UnOp(f, opstr, x)

# Functor constructing an output, which is just a pair of a variable
# and an expression
def make_output(x, e):
    return (x, e)

# Binary operators
import operator
and_ = makeop('&', make_node(operator.and_, '&'))
or_  = makeop('|', make_node(operator.or_,'|'))
xor  = makeop('^', make_node(operator.xor,'^'))
not_ = makeop('~', make_unode(operator.not_,'~'))
asgn = makeop('=', make_output)

# Evaluate a tree-ish expression by folding (reducing) it
def eval_expr(z, l):
    return reduce(lambda s, y: y[0](s, y[1]), l, z)

# Evaluate a unary expression
def eval_uexpr(f, x):
    return f(x)

# Evaluate a binary expression
def eval_binexpr(x, f, y):
    return f(x, y)

# Assemble nested list
def assemble(x, y):
    if type(y) is list:
        return [x] + y
    else:
        return [x, y]

# Currying
unarg = lambda f: lambda x: f(*x)

# Curried functors for evaluation functions and constructors
f = unarg(eval_expr)
g = unarg(eval_uexpr)
h = unarg(eval_binexpr)
collect = unarg(assemble)
make_circ = unarg(Circuit)

# @RULE:
# primary ::= boolean | variable | '(' expr ')'
@with_forward_decls
def primary():
    return boolean | variable | ((op('(') + expr + op(')')) >> (lambda x: x[1]))

# @RULE
# literal ::= not primary | primary
literal = not_ + primary >> g | primary

# @RULE
# minterm ::= literal (and literal)*
minterm = literal + many(and_ + literal) >> f

# @RULE
# esop ::= minterm (xor minterm)*
esop = minterm + many(xor + minterm) >> f

# @RULE
# expr ""= esop (or esop)*
expr = esop + many(or_ + esop) >> f

# @RULE
# assign = variable '=' expr
assign = variable + asgn + expr >> h

# @RULE
# varlist ::= variable (',' variable)*
varlist = variable + many(skip(comma) + variable) >> collect

# @RULE
# inputs ::= 'inputs' ':' varlist
inputs = skip(inp) + skip(op(':')) + varlist

# @RULE
# outputs ::= 'outputs' ':' varlist
outputs = skip(outp) + skip(op(':')) + varlist

# @RULE
# body ::= (assign)*
body = many(assign)

# @RULE
# circuit ::= 'circ' name '{' inputs outputs body '}' EOF
circuit =  (skip(circ) + name
            + skip(op('{'))
            + inputs
            + outputs
            + body
            + skip(op('}'))
            + skip(finished)) >> make_circ


red = '\033[31m'
blue = '\033[34;1m'
green = '\033[32m'
cyan = '\033[36m'
normal = '\033[0m'

def print_info(message):
    print (cyan + "[INFO ] " + normal + message)

def print_error(message):
    print (red + "[ERROR] " + normal + message)


# main parse function
def parse(filename):
    '''Parse a circuit from a given file'''

    # print_debug("Parsing file '%s'" % filename)
    try:
        with open(filename, 'r') as f:
            s = f.read()
            tok = tokenize(s)
            return circuit.parse(tok)
    except FileNotFoundError as e:
        print_error("Could not open file '%s'" % filename)
        raise e
    except BrokenCircuitException as e:
        print_error("%s" % e)
        raise e
    except NoParseError as e:
        epos = e.state.pos
        etok = tok[epos]
        line = etok.line
        start = etok.start[1]
        end = etok.end[1]
        lineNo = etok.start[0]
        print_error("Syntax error in line %d:" % lineNo)
        print_error("%s" % line.replace('\n',''))
        print_error((' '*start) + ('~'*(end-start+1)))
        raise e
