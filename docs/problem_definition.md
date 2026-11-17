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
  - range_ff(q(x),v1,v2) 
  
    meaning p(x) is a polynomial and v1 and v2 are prime field
    constants, meaning v1 <= q(x) <= v2
	
  - range(q(x),v1,v2) 
  
    meaning v1 <= int( q(x) ) <= v2 with v1 and v2 integer
    constnats. int( q(x)) meaning evaluating q(x) over the integers,
    and not over the ff.
  

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

## Domain propagation (R5) -- parametrized by b

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
  signed(v)<=signed(x)<=signed(v)

## Merge roots (R11)

ai, bi and x are signed

  a1<=x<=a2    b1<=x<=b2
  -----------------------
  max(a1,b1)<=x<=min(a2,b2)

## Exp (R12) -- parametrized by k

This rule is parametrized by k

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

## R13
	
  TBD

  - Mult rule: in case we have two expressions E1, E2 such that min1 <= E1 <= max1 and min2 <= E2 <= max2 then:
              * Case min1, min2 positive:
                            min1 * min2 <= E1 * E2 <= max1 * max2
              * Case max1, max2 negative:
                            max1 * max2 <= E1 * E2 <= min1 * min2
              * General case:
                            new_min = min{min1 * min2, min1 * max2, max1 * min2, max1 * max2}
                            new_max = max{min1 * min2, min1 * max2, max1 * min2, max1 * max2}
                            new_min <= E1 * E2 <= new_max
                 

## R14

  TBD
  
  - Sum rule: in case we have two expressions E1, E2 such that min1 <= E1 <= max1 and min2 <= E2 <= max2 then:
              min1 + min2 <= E1 + E2 <= max1 + max2


## R15

   TBD

   The inference rule related to roots -- see discussion in the
   problems section below.
   
      p(x)=0, p(x)=(x-v1) * ... * (x-vn)
    ----------------------------------
    min{v1, ..., vn} <= x <= max{v1, ..., vn}
  
## R16

   TBD
   
RULES FOR UPDATING SIGNAL BOUNDS

   - If we have a constraint of the form x - E = 0 and -p/2 < min <= E <= max < P/2 then we can infer that min <= x <= max 
   

# The problem:

  We are given a context and a conclusion, and we want to guanatee
  that the conclusion is ineed implied by the context.
  
# Interface

  The user provides:
  
   - A context (Ctx) as a list of facts, where the Ctx[i] refers to the fact at position i
   - A conclusion Phi.
   - A list of explanations as described below.
  
  An explnations is of the following form:
  
     Ri Param*, [Fid_0,...,Fid_n], 
	 Param is of th form (var=value)
	 
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
	 
	 
   TODO: add an example with a parametrized rule	 
	 
	 
  

# What we are providing:

  1. A checker such that when it says yes, then Ctx => Con
  2. A theorem:
  
     Theorem: Ctx => Con := by ....
	 
  
  
# Doubts and questions:

## Roots of a polynomial

Clara says:

  * We also detect (syntactic analysis on the input) if they are of
    the form (x-v1) * ... * (x-vn) and if so we store the values of
    the possible roots.

  ...
  
  * Known roots:

    If we know that the constraint was originally of the form 
	
	   (x-v1) * ... * (x-vn), 
	   
    then min{v1, ..., vn} <= x <= max{v1, ..., vn}

Question/Problem:

  In our settings this is a rule of the following form:
  
    p(x)=0, p(x)=(x-v1) * ... * (x-vn)
    ----------------------------------
    min{v1, ..., vn} <= x <= max{v1, ..., vn}
  
  So the doubt is:
  
   Do you have p(x)=(x-v1) * ... * (x-vn) in the CONTEXT? Otherwise we
   do not know how to relate p(x) to its roots.
   
## Parametrized rules

   The are rules like (assuming u and l are positive)
   
       l<=x<=u
     -------------
     l^k <= x^k <= u^k

   The queston is: when you use this rule, you use it for a concrete
   value of k, so we expect this value to be provide, for example to
   tell us somthing like
   
     R12 with k=4, H2
	 
   meaning: use the rule with k=4 and the assumption H2 (refer to
   l<=x<=u)
   
   The same happens for R5
	 
     x=a
     -----------  (a <> b)
     x<>b

   We expect b to be given a a parameter.
   
   Another possibility, is to force explanation to include the
   conclusion at every step, and then we can synthesize these
   parameters. WE PREFER THE FIRST SOLUTION.
