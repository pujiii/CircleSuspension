# `Circle` and `Suspension Two` Equivalence

The following repository contains formalised proof that the basic definition of the circle, that is
```coq
Inductive S¹ : Set :=
| base : S¹
| loop : base = base.
```
is equal to the definition of the circle using a suspension, that is, `Suspension Two`, where `Two` is the two-point type and `Suspension` is defined as 
```coq
Inductive Suspension (A : Type) : Set :=
| North : Suspension A
| South : Suspension A
| merid : A -> North = South.
```

The informal proof can be found in section 6.4 of [the HoTT book](https://hott.github.io/book/hott-online-15-ge428abf.pdf).

## Overview

Firstly, a hard-coded definition of the circle of the suspension is defined. Both the definition of the regular circle and of this hard-coded definition can be found in `Circle.v`. The equivalence between the two is proved in `Circle_Equiv.v`. 

Secondly, a generalised definition of the Suspension is defined in `Suspension.v`, as well as the two-point type. The equivalence between the basic definition of the circle and the suspension-definition of the circle is given in `Circle_Suspension_Equiv.v`.

## How to run
The proofs are written in Coq 8.17 and Coq must thus be used for running the code. Other version could work too, but it has only been tested in 8.17. Furthermore, it uses the version of UniMath as given in that Coq version.

In order to run `Circle_Equiv.v`, `Circle.v` must be compiled. In order to run and `Circle_Suspension_Equiv.v`, both `Circle.v` and `Circle_Suspension_Equiv.v` must be compiled. Everything can be run either using the Coq IDE or using the Coq add-on in VSCode.