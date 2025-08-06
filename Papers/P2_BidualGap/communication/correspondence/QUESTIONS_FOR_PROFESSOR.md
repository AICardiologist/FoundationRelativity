# Questions for Professor on WLPO ↔ ASP

## Context
We're implementing the crucial WLPO ↔ ASP equivalence following Ishihara's work. This is the bridge that enables constructive Hahn-Banach.

## Question 1: ASP → WLPO Direction

In the proof, we encode a WLPO sequence α as:
```
s(n) = 1 - 1/(n+1) if α(n) = true
s(n) = 0 if α(n) = false
```

We get sup S via ASP. Our approach:
1. Use ASP's approximation property to get x ∈ S with sup - 1/3 < x ≤ sup
2. This x = s(n₀) for some n₀
3. Since s(n₀) ∈ {0} ∪ [1/2, 1), we can decide using rational comparison

**Question**: Is this the right approach? We're using that our specific sequence has a "gap" between 0 and 1/2, making the decision possible with rational arithmetic. But this feels like we're using special properties of our encoding rather than ASP in general.

## Question 2: WLPO → ASP Direction

To construct the supremum given WLPO, we need to:
1. Decide for any b whether b is an upper bound for S
2. Use binary search to approximate sup

**Question**: How do we encode "b is an upper bound for S" as a binary sequence to apply WLPO? S is an arbitrary set of CReals, not necessarily countable or with any nice structure.

## Question 3: Constructive Completeness

Both directions seem to require that CReal is "complete" in some constructive sense. 

**Question**: What completeness properties of CReal can we assume? We have:
- Cauchy sequences with modulus converge (by construction)
- Monotone bounded sequences converge (we proved this)

Is this sufficient for the WLPO ↔ ASP proof?

## Current Status

The proof skeleton is in WLPO_ASP.lean with critical steps marked as sorry. We cannot proceed without clarifying these foundational issues.