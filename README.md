# Exercise Solutions

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
- `Auto.v`: `info_auto` does not print trace anymore and use `Info 1 auto` instead. But it seems to keep giving unknown...

## Progress

Following blue arrows, which is recommended path for one-semester course.

- [x] [Basics](./exercises/Basics.v)
- [x] [Induction: Proof by Induction](./exercises/Induction.v)
- [x] [Lists: Working with Structured Data](./exercises/Lists.v)
- [x] [Poly: Polymorphism and Higher-Order Functions](./exercises/Poly.v)
- [x] [MoreCoq: More About Coq's Tactics](./exercises/MoreCoq.v)
- [x] [Logic: Logic in Coq](./exercises/Logic.v)
- [x] [Prop: Propositions and Evidence](./exercises/Prop1.v)
- [x] [MoreLogic: More on Logic in Coq](./exercises/MoreLogic.v)
- [ ] [SfLib: Software Foundations Library](./exercises/SfLib.v)
- [x] [Imp: Simple Imperative Programs](./exercises/Imp.v)
  - [ ] Additional Exercises
- [x] [Equiv: Program Equivalence](./exercises/Equiv.v)
  - [ ] Additional Exercises
- [x] Hoare: Hoare Logic, Part I
- [ ] Hoare2: Hoare Logic, Part II
- [x] [Smallstep: Small-step Operational Semantics](./exercises/Smallstep.v)
  - [ ] A Small-Step Stack Machine
- [x] [Auto: More Automation](./exercises/Auto.v)
- [x] [Types: Type Systems](./exercises/Types.v)
  - [ ] Additional Exercises
- [x] [Stlc: The Simply Typed Lambda-Calculus](./exercises/Stlc.v)
- [x] [StlcProp: Properties of STLC](./exercises/StlcProp.v)
  - [ ] Additional Exercises
