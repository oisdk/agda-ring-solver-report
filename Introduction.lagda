\begin{code}
module Introduction where

module OldSolver where
 open import Relation.Binary.PropositionalEquality
 open import Data.Nat
 open import Data.Nat.Solver using (module +-*-Solver)
 open +-*-Solver

 lemma : ∀ x y → x + y * 1 + 3 ≡ 2 + 1 + y + x
\end{code}
%<*old-solver>
\begin{code}
 lemma = +-*-Solver.solve 2 (λ x y → x :+ y :* con 1 :+ con 3 := con 2 :+ con 1 :+ y :+ x) refl
\end{code}
%</old-solver>
\begin{code}
open import Polynomial.Simple.AlmostCommutativeRing
open import Polynomial.Simple.Reflection
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Nat.Properties using (*-+-commutativeSemiring)
open import Level using (0ℓ)
open import Data.Maybe
import Relation.Binary.PropositionalEquality as ≡

NatRing : AlmostCommutativeRing 0ℓ 0ℓ
NatRing = fromCommutativeSemiring *-+-commutativeSemiring λ { zero → just ≡.refl ; (suc x) → nothing}

open AlmostCommutativeRing NatRing
module WithSolver where
\end{code}
%<*lemma>
\begin{code}
 lemma : ∀ x y → x + y * 1 + 3 ≈ 2 + 1 + y + x
\end{code}
%</lemma>
%<*solver>
\begin{code}
 lemma = solve NatRing
\end{code}
%</solver>
\begin{code}
open import Relation.Binary.Reasoning.Setoid setoid
open import Function
module Manual where
 lemma : ∀ x y → x + y * 1 + 3 ≈ 2 + 1 + y + x
\end{code}
%<*proof>
\begin{code}
 lemma x y = begin
    x + y * 1 + 3  ≈⟨ refl ⟨ +-cong ⟩ *-identityʳ y ⟨ +-cong ⟩ refl {3} ⟩
    x + y + 3      ≈⟨ +-comm x y ⟨ +-cong ⟩ refl ⟩
    y + x + 3      ≈⟨ +-comm (y + x) 3 ⟩
    3 + (y + x)    ≈⟨ sym (+-assoc 3 y x) ⟩
    2 + 1 + y + x  ∎
\end{code}
%</proof>

