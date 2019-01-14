\begin{code}
module Introduction where

open import Polynomial.Simple.AlmostCommutativeRing
open import Polynomial.Simple.Reflection
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Nat.Properties
open import Level using (0ℓ)

NatRing : AlmostCommutativeRing 0ℓ 0ℓ
NatRing = fromCommutativeSemiring *-+-commutativeSemiring ℕ._≟_

open AlmostCommutativeRing NatRing

\end{code}
%<*lemma>
\begin{code}
lemma : ∀ x y →
  x + y * 1 + 3 ≈ 2 + 1 + y + x
lemma = solve NatRing
\end{code}
%</lemma>
