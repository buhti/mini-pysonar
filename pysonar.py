# pysonar.py - a Python version of PySonar static analyzer for Python
# Copyright (C) 2011 Yin Wang (yinwang0@gmail.com)


# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.

# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.

# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.



import re
from ast import *
from lists import *




####################################################################
## global parameters
####################################################################
IS = isinstance



####################################################################
## utilities
####################################################################
def iter_fields(node):
    """Iterate over all existing fields, excluding 'ctx'."""
    for field in node._fields:
        try:
            if field <> 'ctx':
                yield field, getattr(node, field)
        except AttributeError:
            pass

# for debugging
def sz(s):
    return nodeSize(parse(s), True)

def dp(s):
    return map(dump, parse(s).body)

def pf(file):
    import cProfile
    cProfile.run("sonar(" + file + ")", sort="cumulative")



####################################################################
## test on AST nodes
####################################################################
def isAtom(x):
    return type(x) in [int, str, bool, float]

def isDef(node):
    return IS(node, FunctionDef) or IS(node, ClassDef)




##################################################################
# per-node information store
##################################################################
history = {}
def putType(exp, item):
    if history.has_key(exp):
        seen = history[exp]
    else:
        seen = []
    history[exp] = union([seen, item])


def getType(exp):
    return history[exp]




##################################################################
# types used by pysonar
##################################################################
class Type:
    pass



unknown_counter = 0
class UnknownType(Type):
    def __init__(self, name=None):
        global unknown_counter
        if name <> None:
            self.name = name + str(unknown_counter)
        else:
            self.name = '_' + str(unknown_counter)
        unknown_counter += 1
    def __repr__(self):
        return str(self.name)




class PrimType(Type):
    def __init__(self, name):
        self.name = name
    def __repr__(self):
        return str(self.name)
    def __eq__(self, other):
        if IS(other, PrimType):
            return self.name == other.name
        else:
            return False
    def __ne__(self, other):
        return not self.__eq__(other)




class ClassType(Type):
    def __init__(self, name):
        self.name = name
    def __repr__(self):
        return "class:" + self.name
    def __eq__(self, other):
        if IS(other, ClassType):
            return self.name == other.name
        else:
            return False
    def __ne__(self, other):
        return not self.__eq__(other)




class FuncType(Type):
    def __init__(self, fromtype, totype):
        self.fromtype = fromtype
        self.totype = totype
    def __repr__(self):
        return str(self.fromtype) + " -> " + str(self.totype)
    def __eq__(self, other):
        if IS(other, FuncType):
            return ((self.fromtype == other.fromtype) and
                    self.totype == other.totype)
        else:
            return False
    def __ne__(self, other):
        return not self.__eq__(other)




class Closure(Type):
    def __init__(self, func, env):
        self.func = func
        self.env = env
        self.defaults = []
    def __repr__(self):
        return "clo:" + str(self.func)




class TupleType(Type):
    def __init__(self, elts):
        self.elts = elts
    def __repr__(self):
        return "tup:" + str(self.elts)
    def __eq__(self, other):
        if IS(other, TupleType):
            if len(self.elts) <> len(other.elts):
                return False
            else:
                for i in xrange(len(self.elts)):
                    if self.elts[i] <> other.elts[i]:
                        return False
                return True
        else:
            return False
    def __ne__(self, other):
        return not self.__eq__(other)



class ListType(Type):
    def __init__(self, elts):
        self.elts = elts
    def __repr__(self):
        return "list:" + str(self.elts)
    def __eq__(self, other):
        if IS(other, ListType):
            if len(self.elts) <> len(other.elts):
                return False
            else:
                for i in xrange(len(self.elts)):
                    if self.elts[i] <> other.elts[i]:
                        return False
                return True
        else:
            return False
    def __ne__(self, other):
        return not self.__eq__(other)



class DictType(Type):
    def __init__(self, dic):
        self.dic = dic
    def __repr__(self):
        return "dict:" + str(self.dic)

    # any hashable value can be used as keys
    # any object can be used as values
    # so we can know almost nothing about the dictionaries
    def __eq__(self, other):
        if IS(other, DictType):
            return True
        else:
            return False
    def __ne__(self, other):
        return not self.__eq__(other)


# singleton primtive types
contType = PrimType('cont')
bottomType = PrimType('_|_')




# need to rewrite this when we have recursive types
def typeEqual(t1, t2):
#    print "typeEqual:", t1, t2, t1 == t2
    if IS(t1, list) and IS(t2, list):
        for bd1 in t1:
            if bd1 not in t2:
                return False
        return True
    else:
        return t1 == t2




def subtypeBindings(rec1, rec2):
#    print "subtypeBindings:", rec1, rec2
    def find(a, rec2):
        for b in rec2:
            if a.fst == b.fst and typeEqual(a.snd, b.snd):
                return True
        return False
    for a in rec1:
        if not find(a, rec2):
            return False
    return True




def union(bds):
    u = []
    locs = []
    for bd in bds:
        if IS(bd, list):                 # already a union (list)
            for b in bd:
                if b not in u:
                    u.append(b)
        else:
            if bd not in u:
                u.append(bd)
    return u





####################################################################
## type inferencer
####################################################################
class Bind:
    def __init__(self, typ, loc):
        self.typ = typ
        self.loc = loc
    def __repr__(self):
        return "B:" + str(self.typ) + "=" + str(self.loc)
    def __iter__(self):
        return BindIterator(self)
    def __eq__(self, other):
        return (IS(other, Bind) and
                self.typ == other.typ and
                self.loc == other.loc)



class BindIterator:
    def __init__(self, p):
        self.p = p
        self.cur = 0
    def next(self):
        if self.cur == 2:
            raise StopIteration
        elif self.cur == 0:
            self.cur += 1
            return self.p.typ
        else:
            self.cur += 1
            return self.p.loc




def stripType(t):
    return union(map(lambda b: b.typ, t))



def hasType(t, u):
    for t2, loc in u:
        if t == t2:
            return True
    return False



def removeType(t, u):
    ret = []
    for t2, loc in u:
        if t2 <> t:
            ret.append(Bind(t2, loc))
    return ret




# combine two environments, make unions when necessary
# only assocs appear in both envs are preserved
def mergeEnv(env1, env2):
    ret = nil
    for p1 in env1:
        p2 = assq(p1.fst, env2)
        if p2 <> None:
            ret = ext(p1.fst, union([p1.snd, p2.snd]), ret)
    return ret



# compare both str's and Name's for equivalence, because
# keywords are str's (bad design of the parser)
def getId(x):
    if IS(x, Name):
        return x.id
    else:
        return x



# ctx : for error reporting only
def bind(target, value, env, ctx=None):
#    print "bind:", target, value

    if IS(target, Name) or IS(target, str):
        u = stripType(value)
        if u <> []:
            putType(target, [Bind(u, target)])
            return ext(getId(target), map(lambda x: Bind(x, target), u), env)
        else:
            return env

    elif IS(target, Tuple) or IS(target, List):
        if IS(value, TupleType) or IS(target, List):
            if len(target.elts) == len(value.elts):
                for i in xrange(len(value.elts)):
                    env = bind(target.elts[i], value.elts[i], env, ctx)
                return env
            elif len(target.elts) < len(value.elts):
                putType(ctx, ValueError('too many values to unpack',
                                             target, value))
                return env
            else:
                putType(ctx, ValueError('too few values to unpack',
                                            target, value))
                return env
        else:
            putType(ctx, TypeError('non-iterable object', value))
            return env
    else:
        putType(ctx, SyntaxError("can't assign to ", target))
        return env




def onStack(call, args, stk):
    for p1 in stk:
        call2 = p1.fst
        args2 = p1.snd
        if call == call2 and subtypeBindings(args, args2):
            return True
    return False




# invoke ONE closure in the union (list)
def invoke1(call, clo, env, stk):

    # Even if operator is not a closure, resolve the
    # arguments for partial information.
    if not IS(clo, Closure):
        for a in call.args:
            t1 = infer(a, env, stk)
        for k in call.keywords:
            t2 = infer(k.value, env, stk)
        err = TypeError('calling non-callable', clo, call.func, call.args)
        putType(call, err)
        return [Bind(err, call)]

    func = clo.func
    fenv = clo.env
    pos = nil
    kwarg = nil

    # bind positionals first
    poslen = min(len(func.args.args), len(call.args))
    for i in xrange(poslen):
        t = infer(call.args[i], env, stk)
        pos = bind(func.args.args[i], t, pos, call)


    # put extra positionals into vararg if provided
    # report error and go on otherwise
    if len(call.args) > len(func.args.args):
        if func.args.vararg == None:
            err = TypeError('excess arguments to function',
                            len(call.args), call.func, call.args)
            putType(call, err)
            return [Bind(err, call)]
        else:
            varg = []
            for i in xrange(len(func.args.args), len(call.args)):
                t = infer(call.args[i], env, stk)
                varg = varg + t
            pos = bind(func.args.vararg, varg, pos, call)


    # bind keywords, collect kwarg
    ids = map(getId, func.args.args)
    for k in call.keywords:
        vt = infer(k.value, env, stk)
        tloc1 = lookup(k.arg, pos)
        if tloc1 <> None:
            putType(call, TypeError('multiple values for keyword argument',
                                     k.arg, loc))
        elif k.arg not in ids:
            kwarg = bind(k.arg, vt, kwarg, call)
        else:
            pos = bind(k.arg, vt, pos, call)


    # put extras in kwarg or report them
    if kwarg <> nil:
        if func.args.kwarg <> None:
            pos = bind(func.args.kwarg, [Bind(DictType(reverse(kwarg)), call)],
                       pos, call)
        else:
            putType(call, TypeError("unexpected keyword arguements", kwarg))
    elif func.args.kwarg <> None:
        pos = bind(func.args.kwarg, [Bind(DictType(nil), call)], pos, call)


    # bind defaults, avoid overwriting bound vars
    i = len(func.args.args) - len(func.args.defaults)
    ndefaults = len(func.args.args)
    for j in xrange(len(clo.defaults)):
        t, loc = lookup(getId(func.args.args[i]), pos)
        if t == None:
            pos = bind(func.args.args[i], clo.defaults[j], pos, call)
            i += 1

    fromtype = maplist(lambda p: Pair(p.fst, stripType(p.snd)), pos)

    if onStack(call, fromtype, stk):
        return [Bind(bottomType, None)]

    stk = ext(call, fromtype, stk)
    fenv = append(pos, fenv)
    to = infer(func.body, fenv, stk)
    totype = stripType(to)
    putType(func, FuncType(reverse(fromtype), totype))
    return [Bind(totype, call)]



def invoke(call, env, stk):
    clos = infer(call.func, env, stk)
    totypes = []
    for clo, loc in clos:
        t2 = invoke1(call, clo, env, stk)
        totypes = totypes + t2

    # currently we return the last state
    # need to consider bundling the state into the union of types
    return totypes



def inferSeq(exp, env, stk):
    if exp == []:                       # reached end without return
        return ([Bind(contType, None)], env)

    e = exp[0]

    if IS(e, If):
        tt = infer(e.test, env, stk)
        (t1, env1) = inferSeq(e.body, env, stk)
        (t2, env2) = inferSeq(e.orelse, env, stk)

        if not hasType(contType, t1) and not hasType(contType, t2):
            # both terminates
            (t3, env3) = inferSeq(exp[1:], env, stk)
            return (union([t1, t2]), env)

        elif not hasType(contType, t1):          # t1 terminates
            (t3, env3) = inferSeq(exp[1:], env2, stk)
            t2 = removeType(contType, t2)
            return (union([t1, t2, t3]), env3)

        elif not hasType(contType, t2):          # t2 terminates
            (t3, env3) = inferSeq(exp[1:], env1, stk)
            t1 = removeType(contType, t1)
            return (union([t1, t2, t3]), env3)

        else:                                    # both non-terminating
            (t3, env3) = inferSeq(exp[1:], mergeEnv(env1, env2), stk)
            t1 = removeType(contType, t1)
            t2 = removeType(contType, t2)
            return (union([t1, t2, t3]), env3)

    elif IS(e, Assign):
        t = infer(e.value, env, stk)
        for target in e.targets:
            env = bind(target, t, env, e)
        env = ext(e, Bind(contType, e), env)
        return inferSeq(exp[1:], env, stk)

    elif IS(e, FunctionDef):
        clo = Closure(e, None)
        env = ext(e.name, [Bind(clo, e)], env)
        clo.env = env                   # create circular env
        for d in e.args.defaults:
            dt = infer(d, env, stk)
            clo.defaults.append(dt)
        return inferSeq(exp[1:], env, stk)        

    elif IS(e, Return):
        t1 = infer(e.value, env, stk)
        (t2, env2) = inferSeq(exp[1:], env, stk)
        for e2 in exp[1:]:
            err = TypeError('unreachable code', e2)
            putType(e2, err)
        return (t1, env)

    elif IS(e, Expr):
        t1 = infer(e.value, env, stk)
        return inferSeq(exp[1:], env, stk)        

    else:
        raise TypeError('recognized node in effect context', e)




env0 = nil

def infer(exp, env, stk):

    #    print 'infering:', exp

    if IS(exp, list):
        # env ignored because output scope
        (t, ignoreEnv) = inferSeq(exp, env, stk)
        return t    

    elif IS(exp, Num):
        return [Bind(PrimType(type(exp.n)), exp)]

    elif IS(exp, Str):
        return [Bind(PrimType(type(exp.s)), exp)]

    elif IS(exp, Name):
        b = lookup(exp.id, env)
        if (b <> None):
            putType(exp, b)
            return b
        else:
            try:                        # use Python's help
                t = type(eval(exp.id))
                return [Bind(PrimType(t), None)]
            except NameError as err:
                putType(exp, err)
                return [Bind(err, exp)]

    elif IS(exp, Lambda):
        clo = Closure(exp, env)
        for d in exp.args.defaults:
            dt = infer(d, env, stk)
            clo.defaults.append(dt)
        return [Bind(clo, exp)]

    elif IS(exp, Call):
        return invoke(exp, env, stk)

    ## ignore complex types for now    
    # elif IS(exp, List):
    #     eltTypes = []
    #     for e in exp.elts:
    #         t = infer(e, env, stk)
    #         eltTypes.append(t)
    #     return [Bind(ListType(eltTypes), exp)]

    # elif IS(exp, Tuple):
    #     eltTypes = []
    #     for e in exp.elts:
    #         t = infer(e, env, stk)
    #         eltTypes.append(t)
    #     return [Bind(TupleType(eltTypes), exp)]


    elif IS(exp, Module):
        return infer(exp.body, env, stk)

    else:
        return [Bind(UnknownType(), exp)]






##################################################################
# drivers(wrappers)
##################################################################
def parseFile(filename):
    f = open(filename, 'r');
    return parse(f.read())




# clean up globals
def clear():
    history.clear()
    global unknown_counter
    unknown_counter = 0


def nodekey(node):
    if hasattr(node, 'lineno'):
        return node.lineno
    else:
        return 1000000


# check a single (parsed) expression
def son(exp):
    clear()
    ret = infer(exp, env0, nil)
    if history.keys() <> []:
        print "---------------------------- history ----------------------------"
        for k in sorted(history.keys(), key=nodekey):
            print k, ":", history[k]
        print "\n"



# check a string
def so(s):
    return son(parse(s))



# check a file
def sonar(filename):
    f = open(filename, 'r');
    so(f.read())




###################################################################
# printing support
###################################################################
def dump(node, annotate_fields=True, include_attributes=False):
    def _format(node):
        if isinstance(node, AST):
            fields = [(a, _format(b)) for a, b in iter_fields(node)]
            rv = '%s(%s' % (node.__class__.__name__, ', '.join(
                ('%s=%s' % field for field in fields)
                if annotate_fields else
                (b for a, b in fields)
            ))
            if include_attributes and node._attributes:
                rv += fields and ', ' or ' '
                rv += ', '.join('%s=%s' % (a, _format(getattr(node, a)))
                                for a in node._attributes)
            return rv + ')'
        elif isinstance(node, list):
            return '[%s]' % ', '.join(_format(x) for x in node)
        return repr(node)
    if not isinstance(node, AST):
        raise TypeError('expected AST, got %r' % node.__class__.__name__)
    return _format(node)



def printList(ls):
    if (ls == None or ls == []):
        return ""
    elif (len(ls) == 1):
        return str(ls[0])
    else:
        return str(ls)



def printAst(node):
    if (IS(node, Module)):
        ret = "module:" + str(node.body)
    elif (IS(node, FunctionDef)):
        ret = "fun:" + str(node.name)
    elif (IS(node, ClassDef)):
        ret = "class:" + str(node.name)
    elif (IS(node, Call)):
        ret = "call:" + str(node.func) + ":(" + printList(node.args) + ")"
    elif (IS(node, Assign)):
        ret = "(" + printList(node.targets) + " <- " + printAst(node.value) + ")"
    elif (IS(node, If)):
        ret = "if " + str(node.test) + ":" + printList(node.body) + ":" + printList(node.orelse)
    elif (IS(node, Compare)):
        ret = str(node.left) + ":" + printList(node.ops) + ":" + printList(node.comparators)
    elif (IS(node, Name)):
        ret = str(node.id)
    elif (IS(node, Num)):
        ret = str(node.n)
    elif (IS(node, Str)):
        ret = '"' + str(node.s) + '"'
    elif (IS(node, Return)):
        ret = "return " + repr(node.value)
    elif (IS(node, Print)):
        ret = "print(" + (str(node.dest) + ", " if (node.dest!=None) else "") + printList(node.values) + ")"
    elif (IS(node, Expr)):
        ret = "expr:" + str(node.value)
    elif (IS(node, BinOp)):
        ret = str(node.left) + " " + str(node.op) + " " + str(node.right)
    elif (IS(node, Mult)):
        ret = '*'
    elif (IS(node, Add)):
        ret = '+'
    elif (IS(node, Pass)):
        ret = "pass"
    elif IS(node,list):
        ret = printList(node)
    else:
        ret = str(type(node))

    if hasattr(node, 'lineno'):
        return re.sub("@[0-9]+", '', ret) + "@" + str(node.lineno)
    else:
        return ret


def installPrinter():
    import inspect
    import ast
    for name, obj in inspect.getmembers(ast):
        if (inspect.isclass(obj) and not (obj == AST)):
            obj.__repr__ = printAst

installPrinter()



sonar('tests/chain.py')

