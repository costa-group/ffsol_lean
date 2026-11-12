# Prime field setting:

We are working over a prime filed p, and numbers are treated as
negative and positive according to the following rules:

- midpoint: p / 2 + 1 
- Positive: 0,1,...,midpoint-1
- Negative: midpoint (int: -(midpoint-1)),...,p-1 (int: -1)

Prime filed constants are integer constnats withing the field
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

## Boolean inference (R1)

	a*(a-1)=0
    -------
    a=0\/a-1=0
	
## Boolean inference aux (R2)
     
	a*a-a=0 
    -------
    a*(a-1)=0


# The problem:

  We are given a context and a conclusion, and we want to guanatee
  that the conclusion is ineed implied by the context.
  
# Interface

  The use provide:
  
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
	 
  
  
