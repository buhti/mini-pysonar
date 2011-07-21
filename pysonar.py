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
class Error:
    def __init__(self, exp, msg):
        self.exp = exp
        self.msg = msg
    def __repr__(self):
        return "Error:" + str(self.exp) + '"' + str(self.msg) + '"'


locations = {}
def putLocation(exp, item, kind):
    if locations.has_key(exp):
        types = locations[exp]
    else:
        types = []

    locations[exp] = union([types, item])



def getLocation(exp):
    return locations[exp]



def putType(exp, type):
    putLocation(exp, type, 'type')



def getType(exp):
    if locations.has_key(exp):
        (types, errs) = getLocation(exp)
        return types
    else:
        return None


def putError(exp, err):
    putLocation(exp, err, 'type')
    return (err, exp)



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
        return "pm:" + str(self.name)
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
#    print "union:", bds, "loc:", inloc
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
def bind(target, value, env, s, ctx=None):
#    print "bind:", target, value

    if IS(target, Name) or IS(target, str):
        u = stripType(value)
        if u <> []:
            putType(target, [Bind(u, target)])
            return (ext(getId(target), [Bind(u, target)], env), s)
        else:
            return (env, s)

    elif IS(target, Tuple) or IS(target, List):
        if IS(value, TupleType) or IS(target, List):
            if len(target.elts) == len(value.elts):
                for i in xrange(len(value.elts)):
                    (env, s) = bind(target.elts[i], value.elts[i], env, s, ctx)
                return (env, s)
            elif len(target.elts) < len(value.elts):
                putError(ctx, ValueError('too many values to unpack',
                                             target, value))
                return (env, s)
            else:
                putError(ctx, ValueError('too few values to unpack',
                                            target, value))
                return (env, s)
        else:
            putError(ctx, TypeError('non-iterable object', value))
            return (env, s)
    else:
        putError(ctx, SyntaxError("can't assign to ", target))
        return (env, s)




def onStack(call, args, stk):
    for p1 in stk:
        call2 = p1.fst
        args2 = p1.snd
        if call == call2 and subtypeBindings(args, args2):
            return True
    return False




# invoke ONE closure in the union (list)
def invoke1(call, clo, env, s, stk):

    # Even if operator is not a closure, resolve the
    # arguments for partial information.
    if not IS(clo, Closure):
        for a in call.args:
            (t1, s) = infer(a, env, s, stk)
        for k in call.keywords:
            (t2, s) = infer(k.value, env, s, stk)
        err = TypeError('calling non-callable', clo, call.func, call.args)
        putError(call, err)
        return ([Bind(err, call)], s)

    func = clo.func
    fenv = clo.env
    pos = nil
    kwarg = nil

    # bind positionals first
    poslen = min(len(func.args.args), len(call.args))
    for i in xrange(poslen):
        (t, s) = infer(call.args[i], env, s, stk)
        pos, s = bind(func.args.args[i], t, pos, s, call)


    # put extra positionals into vararg if provided
    # report error and go on otherwise
    if len(call.args) > len(func.args.args):
        if func.args.vararg == None:
            err = TypeError('excess arguments to function',
                            len(call.args), call.func, call.args)
            putError(call, err)
            return ([Bind(err, call)], s)
        else:
            varg = []
            for i in xrange(len(func.args.args), len(call.args)):
                (t, s) = infer(call.args[i], env, s, stk)
                varg.append(t)
            pos, s = bind(func.args.vararg, varg, pos, s, call)


    # bind keywords, collect kwarg
    ids = map(getId, func.args.args)
    for k in call.keywords:
        (vt, s) = infer(k.value, env, s, stk)
        t1, loc1 = lookup(k.arg, pos)
        if t1 <> None:
            putError(call, TypeError('multiple values for keyword argument',
                                     k.arg, loc))
        elif k.arg not in ids:
            kwarg, s = bind(k.arg, vt, kwarg, s, call)
        else:
            pos, s = bind(k.arg, vt, pos, s, call)


    # put extras in kwarg or report them
    if kwarg <> nil:
        if func.args.kwarg <> None:
            pos, s = bind(func.args.kwarg, [Bind(DictType(reverse(kwarg)), call)],
                          pos, s, call)
        else:
            putError(call, TypeError("unexpected keyword arguements", kwarg))
    elif func.args.kwarg <> None:
        pos, s = bind(func.args.kwarg, [Bind(DictType(nil), call)], pos, s, call)


    # bind defaults, avoid overwriting bound vars
    i = len(func.args.args) - len(func.args.defaults)
    ndefaults = len(func.args.args)
    for j in xrange(len(clo.defaults)):
        t, loc = lookup(getId(func.args.args[i]), pos)
        if t == None:
            pos, s = bind(func.args.args[i], clo.defaults[j], pos, s, call)
            i += 1

    # Check if we are back to the same call and the same types.
    # need to rethink whether to use func or call..
    # answer: should use call because we may have multiple calls to the same func
    # and recursion occurs only if we wind up in the same call before


    fromtype = maplist(lambda p: Pair(p.fst, stripType(p.snd)), pos)

    if onStack(func, fromtype, stk):
        return ([Bind(bottomType, None)], s)

    stk = ext(func, fromtype, stk)
    fenv = append(pos, fenv)
    (to, s) = infer(func.body, fenv, s, stk)
    totype = stripType(to)
    putType(func, FuncType(reverse(fromtype), totype))
    return ([Bind(totype, call)], s)


def stripType(t):
    return union(map(lambda b: b.typ, t))


def invoke(call, env, s, stk):
    clos, s = infer(call.func, env, s, stk)
    totypes = []
    for clo, loc in clos:
        t2, s = invoke1(call, clo, env, s, stk)
        totypes = totypes + t2

    # currently we return the last state
    # need to consider bundling the state into the union of types
    return (totypes, s)




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




def inferSeq(exp, env, s, stk):
    if exp == []:                       # reached end without return
        return ([Bind(contType, None)], env, s)

    e = exp[0]

    if IS(e, If):
        (tt, s) = infer(e.test, env, s, stk)
        (t1, env1, s1) = inferSeq(e.body, env, s, stk)
        (t2, env2, s2) = inferSeq(e.orelse, env, s, stk)

        if not hasType(contType, t1) and not hasType(contType, t2):
            # both terminates
            (t3, env3, s3) = inferSeq(exp[1:], env, append(s1, s2), stk)
            return (union([t1, t2]), env, s)

        elif not hasType(contType, t1):          # t1 terminates
            (t3, env3, s3) = inferSeq(exp[1:], env2, append(s1, s2), stk)
            t2 = removeType(contType, t2)
            return (union([t1, t2, t3]), env3, s3)

        elif not hasType(contType, t2):          # t2 terminates
            (t3, env3, s3) = inferSeq(exp[1:], env1, append(s1, s2), stk)
            t1 = removeType(contType, t1)
            return (union([t1, t2, t3]), env3, s3)        

        else:                                    # both non-terminating
            (t3, env3, s3) = inferSeq(exp[1:], mergeEnv(env1, env2),
                                      append(s1, s2), stk)
            t1 = removeType(contType, t1)
            t2 = removeType(contType, t2)
            return (union([t1, t2, t3]), env3, s3)

    elif IS(e, Assign):
        (t, s) = infer(e.value, env, s, stk)
        for target in e.targets:
            (env, s) = bind(target, t, env, s, e)
        env = ext(e, Bind(contType, e), env)
        return inferSeq(exp[1:], env, s, stk)

    elif IS(e, FunctionDef):
        clo = Closure(e, None)
        env = ext(e.name, [Bind(clo, e)], env)
        clo.env = env                   # create circular env
        for d in e.args.defaults:
            (dt, s) = infer(d, env, s, stk)
            clo.defaults.append(dt)
        return inferSeq(exp[1:], env, s, stk)        

    elif IS(e, ClassDef):
        cls = ClassType(e.name)
        env = ext(e.name, [Bind(cls, e)], env)
        return inferSeq(exp[1:], env, s, stk)

    elif IS(e, Return):
        (t1, s1) = infer(e.value, env, s, stk)
        (t2, env2, s2) = inferSeq(exp[1:], env, s, stk)
        for e2 in exp[1:]:
            err = Error('unreachable code', e2)
            putError(e2, err)
        return (t1, env, s1)

    elif IS(e, Expr):
        (t1, s1) = infer(e.value, env, s, stk)
        return inferSeq(exp[1:], env, s, stk)        

    else:
        raise TypeError('recognized node in effect context', e)





env0 = nil
s0   = nil

def infer(exp, env, s, stk):

    #    print 'infering:', exp

    if IS(exp, list):
        (t, env, s) = inferSeq(exp, env, s, stk)
        return (t, s)    # ignores env (this is inside body)

    elif IS(exp, Num):
        return ([Bind(PrimType(type(exp.n)), exp)], s)

    elif IS(exp, Str):
        return ([Bind(PrimType(type(exp.s)), exp)], s)

    elif IS(exp, List):
        eltTypes = []
        for e in exp.elts:
            (t, s) = infer(e, env, s, stk)
            eltTypes.append(t)
        return ([Bind(ListType(eltTypes), exp)], s)

    elif IS(exp, Tuple):
        eltTypes = []
        for e in exp.elts:
            (t, s) = infer(e, env, s, stk)
            eltTypes.append(t)
        return ([Bind(TupleType(eltTypes), exp)], s)

    elif IS(exp, Name):
        bds = lookup(exp.id, env)
        if bds == None:
            try:
                prim = type(eval(exp.id))
                return ([Bind(PrimType(prim), None)], s)
            except NameError as e:
                err = e
                putError(exp, err)
                return ([Bind(err, exp)], s)
        else:
            putType(exp, bds)
            return (bds, s)

    elif IS(exp, Call):
        return invoke(exp, env, s, stk)

    elif IS(exp, Module):
        return infer(exp.body, env, s, stk)

    else:
        return ([Bind(UnknownType(), exp)], s)






##################################################################
# drivers(wrappers)
##################################################################
def parseFile(filename):
    f = open(filename, 'r');
    return parse(f.read())




# clean up globals
def clear():
    locations.clear()
    global unknown_counter
    unknown_counter = 0




def son(exp):
    clear()
    ret = infer(exp, env0, s0, nil)
    if locations.keys() <> []:
        print "---------------------------- locations ----------------------------"
        for k in sorted(locations.keys(), key=lambda k: k.lineno):
            print k, ":", locations[k]
        print "\n"




def so(s):
    return son(parse(s))




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

