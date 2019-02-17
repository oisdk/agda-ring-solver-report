\begin{code}
module ReflexiveProcessRings where

open import Data.Nat as ℕ using (ℕ)

open import Polynomial.Simple.AlmostCommutativeRing
open import Polynomial.Simple.AlmostCommutativeRing.Instances
open import Polynomial.Simple.Solver
open import Data.Vec as Vec using (Vec; _∷_; [])
open AlmostCommutativeRing Nat.ring hiding (zero)
open Ops Nat.ring
open import Data.Fin as Fin using (Fin)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Data.Nat.Literals
open import Agda.Builtin.FromNat

instance
  numberNat : Number ℕ
  numberNat = Data.Nat.Literals.number
    where import Data.Nat.Literals

instance
  numberFin : ∀ {n} → Number (Fin n)
  numberFin {n} = Data.Fin.Literals.number n
    where import Data.Fin.Literals

lhs : ∀ x y → ⟦
\end{code}
%<*lhs-ast>
\begin{code}
 Ι 0 ⊕ Ι 1 ⊗ Κ 1 ⊕ Κ 3
\end{code}
%</lhs-ast>
\begin{code}
 ⟧ (x ∷ y ∷ []) ≡
\end{code}
%<*lhs-nonnorm>
\begin{code}
 x + y * 1 + 3
\end{code}
%</lhs-nonnorm>
\begin{code}
lhs _ _ = ≡.refl

rhs : ∀ x y → ⟦
\end{code}
%<*rhs-ast>
\begin{code}
 Κ 2 ⊕ Κ 1 ⊕ Ι 1 ⊕ Ι 0
\end{code}
%</rhs-ast>
\begin{code}
 ⟧ (x ∷ y ∷ []) ≡
\end{code}
%<*rhs-nonnorm>
\begin{code}
 2 + 1 + y + x
\end{code}
%</rhs-nonnorm>
\begin{code}
rhs _ _ = ≡.refl

norms : ∀ x y → ⟦ Ι 0 ⊕ Ι 1 ⊗ Κ 1 ⊕ Κ 3 ⇓⟧ (x ∷ y ∷ []) ≡
\end{code}
%<*norm>
\begin{code}
 x * 1 + (y * 1 + 3)
\end{code}
%</norm>
\begin{code}
norms _ _ = ≡.refl
\end{code}
