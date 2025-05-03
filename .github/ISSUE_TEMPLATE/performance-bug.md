---
name: Performance Bug
about: No proof found, or taking longer than 1s to solve.
title: ''
labels: performance
assignees: ''

---

# Desired proof term

Please construct the proof **term** that Canonical should generate, such that the goal is closed. The term should not contain let definitions, and should be [fewer than 100 "words"](https://wordcounter.net). For example:

```
def zero_add (n : Nat) : 0 + n = n :=
  Nat.rec (motive := fun t ↦ 0 + t = t) (Eq.refl 0) 
    (fun n n_ih ↦ Eq.rec (motive := fun a t ↦ (0 + n).succ = a.succ)
      (Eq.refl (0 + n).succ) n_ih) n
```

As a starting point, you can use the `show_term` tactic on a tactic-based proof.
```
import Lean.Elab.Tactic.ShowTerm

def zero_add (n : Nat) : 0 + n = n := by
  show_term
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]
```
Then, you can use Canonical to minimize segments of the proof. 

# Canonical invocation

Please show the invocation of `canonical` used, with the `+debug` flag. Check the message in the InfoView containing the problem sent to Canonical, and ensure that the constant symbols in the desired proof term are present and do not have type `*`. You can add constant symbols to the `canonical` invocation with a list. For example:

```
canonical +debug [Nat.zero_add]
```

The output shows the constant symbol with the correct type:
```
Nat.zero_add : (n.124 : Nat) → Eq Nat (Nat.add 0 n.124) n.124
```

# Observations

Let us know if you believe a particular aspect of the problem is responsible for the failure. Common issues include:
1. Reasoning with the "arrow" type constructor (add `+pi`).
2. Canonical does not currently support the Eta law for structures.
3. Speculative use of a function with reduction behavior (add `+synth` once stable).
