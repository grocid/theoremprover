# Theorem Prover

This is an old project I wrote back in 2008 (obviously, it is lightyears from state-of-the-art theorem provers such as Z3). As an example, to prove `((-p)v(pvq))` using Russel & Whiteheads' five-axiom system from Principia Mathematica, it generates the following:

```
1 (A>(BvA))                 	Axiom 2
2 (p>(Bvp))                 	Substitution A -> p
3 (p>(qvp))                 	Substitution B -> q
4 ((-p)v(qvp))              	Definition substitution >
5 ((AvB)>(BvA))             	Axiom 3
6 (((-p)vB)>(Bv(-p)))       	Substitution A -> (-p)
7 (((-p)v(qvp))>((qvp)v(-p))) 	Substitution B -> (qvp)
8 ((qvp)v(-p))              	Modus Ponens 4 , 7
9 ((AvB)>(BvA))             	Axiom 3
10 (((qvp)vB)>(Bv(qvp)))     	Substitution A -> (qvp)
11 (((qvp)v(-p))>((-p)v(qvp))) 	Substitution B -> (-p)
12 ((-p)v(qvp))              	Modus Ponens 8 , 11
13 ((AvB)>(BvA))             	Axiom 3
14 (((-p)vB)>(Bv(-p)))       	Substitution A -> (-p)
15 (((-p)v(qvp))>((qvp)v(-p))) 	Substitution B -> (qvp)
16 ((qvp)v(-p))              	Modus Ponens 12 , 15
17 ((AvB)>(BvA))             	Axiom 3
18 (((qvp)vB)>(Bv(qvp)))     	Substitution A -> (qvp)
19 (((qvp)v(-p))>((-p)v(qvp))) 	Substitution B -> (-p)
20 ((-p)v(qvp))              	Modus Ponens 16 , 19
21 ((AvB)>(BvA))             	Axiom 3
22 ((qvB)>(Bvq))             	Substitution A -> q
23 ((qvp)>(pvq))             	Substitution B -> p
24 ((A>B)>((CvA)>(CvB)))     	Axiom 5
25 (((qvp)>B)>((Cv(qvp))>(CvB))) 	Substitution A -> (qvp)
26 (((qvp)>B)>(((-p)v(qvp))>((-p)vB))) 	Substitution C -> (-p)
27 (((qvp)>(pvq))>(((-p)v(qvp))>((-p)v(pvq)))) 	Substitution B -> (pvq)
28 (((-p)v(qvp))>((-p)v(pvq))) 	Modus Ponens 23 , 27
29 ((-p)v(pvq))              	Modus Ponens 20 , 28
30 ((AvB)>(BvA))             	Axiom 3
31 (((-p)vB)>(Bv(-p)))       	Substitution A -> (-p)
32 (((-p)v(pvq))>((pvq)v(-p))) 	Substitution B -> (pvq)
33 ((pvq)v(-p))              	Modus Ponens 29 , 32
34 ((AvB)>(BvA))             	Axiom 3
35 ((qvB)>(Bvq))             	Substitution A -> q
36 ((qv(-p))>((-p)vq))       	Substitution B -> (-p)
37 ((qv(-p))>(p>q))          	Definition substitution v
38 (((pvq)v(-p))>((-p)v(pvq))) 	Substitution q -> (pvq)
39 ((-p)v(pvq))              	Modus Ponens 33 , 38
QED
```