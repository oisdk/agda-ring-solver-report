\begin{code}
module Introduction where

open import Polynomial.Simple.AlmostCommutativeRing
open import Polynomial.Simple.Reflection
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Nat.Properties using (*-+-commutativeSemiring)
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
\begin{code}
open import Relation.Binary.Reasoning.Setoid setoid
open import Function
\end{code}
%<*proof>
\begin{code}
proof : ∀ x y → x + y * 1 + 3 ≈ 2 + 1 + y + x
proof x y =
  begin
    x + y * 1 + 3
                  ≈⟨ refl ⟨ +-cong ⟩ *-identityʳ y ⟨ +-cong ⟩ refl {x = 3} ⟩
    x + y + 3
                  ≈⟨ +-comm x y ⟨ +-cong ⟩ refl ⟩
    y + x + 3
                  ≈⟨ +-comm (y + x) 3 ⟩
    3 + (y + x)
                  ≈⟨ sym (+-assoc 3 y x) ⟩
    2 + 1 + y + x
  ∎
\end{code}
%</proof>
