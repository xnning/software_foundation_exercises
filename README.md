# Exercise Solutions For SF

## Basic

Book: [Software Foundation](https://www.cis.upenn.edu/~bcpierce/sf/current/)
Version: 3.2

Coq Version: 8.5pl1

### Compatibility

- `Poly.v`: `Set Asymmetric Patterns.` is needed to use `nil` directly in patterns.
- `Prop.v`: Prop is no longer an available name in Coq 8.5. Rename it.
- `Imp.v`:
`Require Coq.omega.Omega.`
`Ltac omega := Coq.omega.Omega.omega.`
is requested in Coq 8.5 to directly use `omega`.
- `Auto.v`: `into_auto` does not print trace anymore and use `Info 1 auto` instead. But it seems to keep giving unknown...

## Progress

- [x] Basics
- [x] Induction: Proof by Induction
- [x] Lists: Working with Structured Data
- [x] Poly: Polymorphism and Higher-Order Functions
- [x] MoreCoq: More About Coq's Tactics
- [x] Logic: Logic in Coq
- [x] Prop: Propositions and Evidence
- [x] MoreLogic: More on Logic in Coq
- [ ] ProofObjects: Working with Explicit Evidence in Coq
- [ ] MoreInd: More on Induction
- [x] SfLib: Software Foundations Library
- [ ] Rel: Properties of Relations
- [x] Imp: Simple Imperative Programs
  - [ ] Additional Exercises
- [ ] Equiv: Program Equivalence
- [ ] Hoare: Hoare Logic, Part I
- [ ] Hoare2: Hoare Logic, Part II
- [x] Smallstep: Small-step Operational Semantics
  - [ ] A Small-Step Stack Machine
- [x] Auto: More Automation
- [x] Types: Type Systems
  - [ ] Additional Exercises
