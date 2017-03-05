#!/usr/bin/env python
# Author:       Carl Londahl
# Date:         12.03.2008
# Purpose:      Automatic Theorem Prover

import string
import time

# set maximum used memory according to installed RAM
MAX_SIZE                = 3000000

RUSSEL_AND_WHITEHEAD    = 0
HILBERT_AND_ACKERMANN   = 1
MENDELSON               = 2 # empty set
KLEENE                  = 3
RASIOWA_AND_SIKORSKI    = 4

USE_DISTANCE_FUNCTION	= 0 # 1 = YES, other = NO

#Axiomsystems
axiom_systems = [["((AvA)>A)", "(A>(BvA))", "((AvB)>(BvA))", "((Av(BvC))>(Bv(AvC)))","((A>B)>((CvA)>(CvB)))"], 
["((AvA)>A)", "(A>(AvB))", "((AvB)>(BvA))", "((A>B)>((CvA)>(CvB)))"], [], 
["(A>(B>A))","(((A>(B>C))>((A>B)>(A>C)))","((-((-A)v(-B)))>A)","((-((-A)v(-B)))>B)","(A>(B>(-((-A)v(-B)))))","(A>(AvB))","(B>(AvB))","((A>C)>((B>C)>((AvB)>C)))","((A>B)>((A>(-B))>(-A)))","((-(-A))>A)"], 
["((A>B)>((B>C)>(A>C)))","(A>(AvB))","(B>(AvB))","((A>B)>((A>(-B))>(-A)))","((-((-A)v(-B)))>A)","((-((-A)v(-B)))>B)","((C>A)>(C>B)>(C>(-((-A)v(-B)))))","((A>(B>C))>((-((-A)v(-B)))>C))", 
"(((-((-A)v(-B)))>C)>(A>(B>C)))", "((-((-A)v(-(A))))>B)","((A>(-((-A)v(-(A)))))>(-A))","(Av(-A))"]]

axiom = axiom_systems[RUSSEL_AND_WHITEHEAD]

# Theorem to prove
#exp = "((p>(-p))>(-p))"			# 2.01
exp = "(p>(pvq))"					# 2.02
#exp = "((p>q)>((q>r)>(p>r)))"		# 2.06
#exp = "(p>(pvp))"					# 2.07
#exp = "((-p)v(qvp))"				
#exp = "((pvq)>(qv(pvq)))"
#exp = "(p>(-(-p)))"				# 2.12
#exp = "(((-p)>q)>((-q)>p))"		# 2.15
#exp = "((p>q)>((-q)>(-p)))"		# 2.16
#exp = "(((-q)>(-p))>(q>p))"		# 2.17
#exp = "((pv(qvr))>((pvq)vr))"		# 2.31
#exp = "((-(pvq))>(-p))"			# 2.45
#exp = "(p>p)"
#exp = "((-p)vp)"
#exp = "(p>(-(-p)))"
#exp = "(pv(-(-(-p))))"
#exp = "((-(-p))>p)"

# create a variable list from an expression
def createVariableList(exp):
        variables = []
        for i in range(len(exp)):
                if not (exp[i] == "(" or exp[i] == ")" or exp[i] == " " or exp[i] == "-" or exp[i] == "=" or exp[i] == 
">" or exp[i] == "^" or exp[i] == "v"): variables.append(exp[i])
        return dict.fromkeys(variables).keys()

# create a variable permutation list from a variable list
def possibleSubstitutions(exp_var):
        possible = []
        for item in exp_var:
                possible.append(item)
                possible.append("".join(["(-",item,")"]))
        for item1 in exp_var:
                for item2 in exp_var:
                        possible.append("".join(["(",item1,'v',item2,")"]))
                        possible.append("".join(["(",item1,'v',item2,")"]))
        return possible

# create an initial set of axioms with variables permutation
def createSubstituteList(exp_var, axiom, ax_var, ax_index, maxlen):
        if len(axiom) > maxlen:
                return {}
        kb_list = {}
        tmp = {}
        kb_list[axiom] = "".join(["# ", `ax_index`])
        for ax_item in ax_var:
                for item in kb_list:
                        for exp_item in exp_var:
                                tmp[(item.replace(ax_item, exp_item))] = "".join([kb_list[item]," s ",ax_item," ",exp_item])
                kb_list = tmp
                tmp = {}
        return kb_list

# further substitution, applied only once per axiom entry
def SubstituteList(exp_var, axiom, hist, ax_var, maxlen):
        if len(axiom) > maxlen:
                return {}
        kb_list = {}
        for ax_item in ax_var:
                for exp_item in exp_var:
                	if not ax_item == exp_item:
                         kb_list[axiom.replace(ax_item, exp_item)] = "".join([hist," s ",ax_item," ",exp_item])
        return kb_list

# find an implication from which we can possibly draw conclusions
def findDividingImplication(exp):
        list_exp = list(exp)
        lowest = 999
        lowest_index = None
        level = 0
        w = 0
        for i in range(len(list_exp)):
                if list_exp[i] == "(":
                        level += 1
                if list_exp[i] == ")":
                        level -= 1
                if level < lowest:
                        lowest = level
                        w = 1
                if list_exp[i] == ">" and level == lowest and w == 1:
                        lowest_index = i
                        w = 0
        return lowest_index

# convert an implication to connective form
def ImplicationToConnective(exp, hist, maxlen, found = None):
        if len(exp) > maxlen:
                return {}
        list_exp = list(exp)
        stack = []
        lastlevel_index = 0
        w = 0
        returnlist = {}
        for i in range(len(list_exp)):
                if list_exp[i] == "(":
                        stack.append(i)
                        w = 0
                if list_exp[i] == ")":
                        lastlevel_index = stack[len(stack)-1]
                        del stack[len(stack)-1]
                        w = 1
                if list_exp[i] == ">" and (found == None or i == found):
                        if w == 1:
                                sfrom = lastlevel_index
                        else:
                                sfrom = i-1
                        w = 0
                        returned = []
                        returned.extend(list_exp[0:sfrom])
                        returned.append("(-")
                        returned.extend(list_exp[sfrom:i])
                        returned.append(")v")
                        returned.extend(list_exp[i+1:len(list_exp)])
                        returnlist["".join(returned)] = "".join([hist," $ ", `i`])
        return returnlist

# convert an or to implicative form
def ConnectiveToImplication(exp, hist, maxlen, found = None):
        if len(exp) > maxlen:
                return {}
        list_exp = list(exp)
        stack = []
        lastlevel_index = 0
        w = 0
        returnlist = {}
        for i in range(len(list_exp)):
                if list_exp[i] == "(":
                        stack.append(i)
                        w = 0
                if list_exp[i] == ")":

                        lastlevel_index = stack[len(stack)-1]
                        del stack[len(stack)-1]
                        w = 1
                if list_exp[i] == "v" and (found == None or i == found):
                        if w == 1:
                                sfrom = lastlevel_index
                                w = 0
                                if(sfrom > 0 and list_exp[sfrom+1] == "-"):
                                        returned = []
                                        returned.extend(list_exp[0:sfrom])
                                        returned.extend(list_exp[sfrom+2:i-1])
                                        returned.append(">")
                                        returned.extend(list_exp[i+1:len(list_exp)])
                                        returnlist[("".join(returned))] = "".join([hist," @ ", `i`])
        return returnlist



# find new implications to draw possible conclusions from
def updateMPList (fromlist, modus_ponens_list):
        for item in fromlist:
                c = 0
                for i in range(len(item)):
                        if item[i] == "(":
                                c +=1
                        elif item[i] == ")":
                                c -=1
                        elif item[i] == ">":
                                if c == 1:
                                        c = i
                                        break
                len_item = len(item)
                key = item[1:c] 
                val = item[c+1:len_item-1]
                if not modus_ponens_list.has_key(key):
                        modus_ponens_list[key] = {}
                        modus_ponens_list[key][val] = "".join([fromlist[item]])
                else:
                        modus_ponens_list[key][val] = "".join([fromlist[item]])

# draw conclusions from modus ponens list with current knowledge
def applyMPList (fromlist, modus_ponens_list):
        tolist = {}
        for item in fromlist:
                if modus_ponens_list.has_key(item):
                        for m in modus_ponens_list[item]:
                                tolist[m] = "".join([fromlist[item], " MP ", modus_ponens_list[item][m], " |"])
        return tolist
        
def getHammingDistance(exp, string):
	# if strings are of equal length, find the Hamming distance between them
	# otherwise we use Levenshtein distance
    if len(string) == len(exp):
    	return sum(ch1 != ch2 for ch1, ch2 in zip(exp, string))
    else:
	n, m = len(exp), len(string)
	l = 0
	if n > m:
		exp,string = string,exp
		n,m = m,n
	current = range(n+1)
	for i in range(1,m+1):
		previous, current = current, [i]+[0]*n
		for j in range(1,n+1):
			add, delete = previous[j]+1, current[j-1]+1
			change = previous[j-1]
			if exp[j-1] != string[i-1]:
				change = change + 1
			current[j] = min(add, delete, change)
	# if the distance is bigger than 3 units
	# we might assume that there is a sub-
	# expression which has a smaller distance
	if current[n] > 3:
		l = findDividingImplication(string)
		if l == None or string[l+1:m-1] == None:
			return current[n]
        l = getHammingDistance(exp, string[l+1:m-1])
        if l < current[n]:
        	return l
        return current[n]
        	
        			 
    			

# initialize containers
exp_var = createVariableList(exp)
p_exp_var = possibleSubstitutions(exp_var)

kb = {}
towards_connective = {}
towards_implication = {}
modus_ponens_list = {}

new_imp = {}
new_con = {}
new_sub = {}
new_mod = {}

# do a initial substitution of axiom variables
axiom_index = 1
for current_axiom in axiom:
        ax_var = createVariableList(current_axiom)
        new_kb = createSubstituteList(p_exp_var, current_axiom, ax_var, axiom_index, 30)
        axiom_index += 1
        kb.update(new_kb)

updateMPList(kb, modus_ponens_list)

print "Proving",exp,"from axiom set:", axiom

# do definition substitution
for item in kb:
        towards_connective.update(ImplicationToConnective(item, kb[item], 25))
        towards_implication.update(ConnectiveToImplication(item, kb[item], 25))

# add new definition substituted theorems to MP
updateMPList(towards_connective, modus_ponens_list)
updateMPList(towards_implication, modus_ponens_list)

# apply MP on knowledge
kb.update(applyMPList(kb, modus_ponens_list))
towards_connective.update(applyMPList(kb, modus_ponens_list))
towards_implication.update(applyMPList(kb, modus_ponens_list))

# move knowledge to KB
kb.update(towards_connective)
kb.update(towards_implication)

r = 0
while r < 100:
        new_sub = {}
        r+=1
		
        print "RUN",r
        print "Performing definition substitutions..."
		
        t1 = time.clock()
		
		# do definition substitution
        for item in towards_connective:
                if (USE_DISTANCE_FUNCTION != 1 or getHammingDistance(exp, item) < 3):
                        new_imp.update(ImplicationToConnective(item, towards_connective[item], len(exp)+r))
        for item in towards_implication:
                if (USE_DISTANCE_FUNCTION != 1 or getHammingDistance(exp, item) < 3):
                        new_con.update(ConnectiveToImplication(item, towards_implication[item], len(exp)+r))
							
        if (new_imp.has_key(exp) or new_con.has_key(exp)): 
        	break
		
        print "\rPerforming varible substitutions..."

        # do variable substitutions
        for item in kb:
                if (USE_DISTANCE_FUNCTION != 1 or getHammingDistance(exp, item) < 3):
                        new_sub.update(SubstituteList(p_exp_var, item, kb[item], exp_var, len(exp)+r))
                
        # add new theorems to MP
        updateMPList(new_imp, modus_ponens_list)
        updateMPList(new_con, modus_ponens_list)
        updateMPList(new_sub, modus_ponens_list)

        # add new knowledge to KB
        kb.update(new_sub)
        kb.update(towards_connective)
        kb.update(towards_implication)

        towards_connective = new_con
        towards_connective.update(new_sub)
        towards_implication = new_imp
        towards_implication.update(new_sub)

        if (new_sub.has_key(exp)): break

        print "Updating and performing modus ponens..."

        # Do a modus ponens
        new_mod.update(applyMPList(kb, modus_ponens_list))
        updateMPList(new_mod, modus_ponens_list)
        kb.update(new_mod)

        # free memory
        new_sub = {}
        new_imp = {}
        new_con = {}
        new_mod = {}

        t2 = time.clock()
        print "*** Total operation took", (t2-t1)*1000,"ms"

        if kb.has_key(exp): break
        if len(kb) + len(modus_ponens_list) + len(towards_connective) + len(towards_implication) > MAX_SIZE:
                print "Assigned memory space exceeded"
                break

        print "KB:", len(kb), "MP:", len(modus_ponens_list), "TC:", len(towards_connective),"TI:", len(towards_implication)

if kb.has_key(exp) or new_imp.has_key(exp) or new_con.has_key(exp) or new_sub.has_key(exp):
        kb.update(new_imp)
        kb.update(new_con)
        kb.update(new_sub)
        k = kb[exp].split(" ")
        texp = ""
        line = 1
        mp = []

        print "\n\n\n### Theorem has been proven!\n"
       
        for i in range(len(k)):

            if texp == exp:
        			break
            if k[i] == "#":
                    texp = axiom[int(k[i+1])-1]
                    print line, "%-25s" % texp,"\tAxiom",k[i+1]
                    line += 1
                    i += 1
            if k[i] == "s":
                    texp = texp.replace(k[i+1],k[i+2])
                    print line, "%-25s" % texp,"\tSubstitution",k[i+1],"->",k[i+2]
                    line += 1
                    i += 2
            if k[i] == "$":
                    print line, "%-25s" % ImplicationToConnective(texp,"",999, int(k[i+1])).keys()[0],"\tDefinition substitution >"
                    line += 1
                    i += 1
            if k[i] == "@":
                    print line, "%-25s" % ConnectiveToImplication(texp,"",999, int(k[i+1])).keys()[0],"\tDefinition substitution v"
                    line += 1
                    i += 1
            if k[i] == "MP":
                    mp.append(`line-1`)
            if k[i] == "|":
                    texp = texp[findDividingImplication(texp)+1:len(texp)-1]
                    print line, "%-25s" % texp, "\tModus Ponens",mp.pop(),",", line-1
                    line += 1    
        print "QED"