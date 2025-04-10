# Canonical

[Canonical](https://chasenorman.com) exhaustively searches for terms in dependent type theory. The `canonical` tactic proves theorems, synthesizes programs, and constructs objects in Lean.

https://github.com/user-attachments/assets/ec13ad85-7d09-4a32-9c73-3b5b501722a4

## Installation

Canonical is available for Lean `v4.18.0`.

Add the following dependency to your `lakefile.toml`:
```
[[require]]
name = "Canonical"
git = "https://github.com/chasenorman/CanonicalLean"
```
Or, if you are using a `lakefile.lean`:
```
require Canonical from git
  "https://github.com/chasenorman/CanonicalLean.git"
```

On Windows, an additional line at the top of your `lakefile.toml` is necessary:
```
moreGlobalServerArgs = [ "--load-dynlib", "./.lake/packages/Canonical/.lake/build/lib/canonical.dll" ]
```

## Usage

Basic examples:

```lean
import Canonical

-- prove properties by induction
def add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := 
  by canonical

-- enumerate over elements of a type
example : List Nat := by canonical (count := 10)

-- supply premises
def Set (X : Type) := X → Prop
axiom P_ne_not_P : P ≠ ¬ P
theorem Cantor (f : X → Set X) : ¬ ∀ y, ∃ x, f x = y :=
  by canonical [P_ne_not_P, congrFun]
```
