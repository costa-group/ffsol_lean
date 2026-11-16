# Prime field setting:

We are working over a prime filed p, and numbers are treated as
negative and positive according to the following rules:

- midpoint: p / 2 + 1 
- Positive: 0,1,...,midpoint-1
- Negative: midpoint (int: -(midpoint-1)),...,p-1 (int: -1)

Prime field constants are integer constnats withing the field
(negative or positive)

# Prime field (and other?) constraints

* An atom can be on of the following:

  - q(x)=0  where q is a polynomial
  - q(x)<>0 where q is a polynomial
  - range(q(x),v1,v2) meaning p(x) is a polynomial and v1 and v2 are prime field constants, meaning v1 <= q(x) v2 
  - v1 <= int( q(x) ) <= v2   --- integer constraints
  - v  <= int( q(x) )         --- integer constraints
  - int( q(x) ) <= v          --- integer constraints

* A fact is a disjunction of atoms

* A context is a list of facts (where the position is the identifier
  of the fact)
  
# Inference rules

We have a database of fixed inference rules. We assume all have been
demostrated correct.

## Eq zero (R1)

  e1*e2=0
  ----------------
  e1=0 \/ e2=0

## Distrib (R2)

  a*b+a*c=0
  ----------------
  a*(b+c)=0

## Distrib Eq zero (R3)

  a*b+a*c=0
  ----------------
  a=0 \/ b+c=0

## Lightweight conflict (R4)

  x=a    x=b
  -------------  (a <> b)
      false

  x=a    x<>a
  ------------
      false

## Domain propagation (R5)

     x=a
  -----------  (a <> b)
     x<>b

## Monomial zero (R6)

  v=m    x=0
  --------------  (m is a monomial containing x)
      v=0

## Monomial value (R7)

  v=m    x1=a1 ... xn=an
  ----------------------  (m is a monomial over x1,...,xn)
      v=m(a1,...,an)

## Equivalence (R8)

  x1=x1' ... xn=xn'
  y=f(x1,...,xn)    y'=f(x1',...,xn')
  -----------------------------------
                 y=y'

## Binary (R9)

     x*x-x=0
  -------------
     0<=x<=1

## Constant (R10)

       x-v=0
  ----------------
  signed(v)<=x<=signed(v)

## Merge roots (R11)

  a1<=x<=a2    b1<=x<=b2
  -----------------------
  max(a1,b1)<=x<=min(a2,b2)

## Exp (R12)

       l<=x<=u
  ------------------  (k=0)
       1<=x^k<=1

       l<=x<=u
  ------------------  (k odd)
     l^k<=x^k<=u^k

       l<=x<=u
  ------------------  (k even, u<0)
     u^k<=x^k<=l^k

       l<=x<=u
  --------------------------------  (k even, l<0<=u)
     0<=x^k<=max(l^k,u^k)

       l<=x<=u
  ------------------  (k even, 0<=l)
     l^k<=x^k<=u^k

# The problem:

  We are given a context and a conclusion, and we want to guanatee
  that the conclusion is ineed implied by the context.
  
# Interface

  The user provides:
  
   - A context (Ctx) as a list of facts, where the Ctx[i] refers to the fact at position i
   - A conclusion Phi.
   - A list of explanations as described below.
  
  An explnations is of the following form:
  
     Ri, [Fid_0,...,Fid_n], 
	 
  and the consclusion of Ri is added to the context and can be used in
  the next explanation. The last step should provide Phi as a
  conclusion.
  
# Example:

  Add an example
  
  Input:
  
  Ctx: a*a-a=0
  Con: a=0\/a=1
  Exp:
    
	 R2, 0  (should a add a new fact with id 1)
	 R1, 1
     Con 2
	 
  

# What we are providing:

  1. A checker such that when it says yes, then Ctx => Con
  2. A theorem:
  
     Theorem: Ctx => Con := by ....
	 
  
  
