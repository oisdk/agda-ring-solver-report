\begin{code}
{-# OPTIONS --without-K #-}

open import Algebra
open import Relation.Binary
open import Algebra.FunctionProperties
open import Algebra.Solver.Ring.AlmostCommutativeRing

module Reasoning
  {a ℓ}
  (ring : AlmostCommutativeRing a ℓ)
  where

open AlmostCommutativeRing ring
import Relation.Binary.PropositionalEquality as ≡
open import Relation.Nullary
open import Relation.Binary.EqReasoning setoid public
\end{code}
%<*cong-combinators>
\begin{code}
infixr 1 ≪+_ +≫_ ≪*_ *≫_
≪+_ : ∀ {x₁ x₂ y}
    → x₁ ≈ x₂ → x₁ + y ≈ x₂ + y
≪+ prf = +-cong prf refl

+≫_ : ∀ {x y₁ y₂}
    → y₁ ≈ y₂ → x + y₁ ≈ x + y₂
+≫_ = +-cong refl

≪*_ : ∀ {x₁ x₂ y}
    → x₁ ≈ x₂ → x₁ * y ≈ x₂ * y
≪* prf = *-cong prf refl

*≫_ : ∀ {x y₁ y₂}
    → y₁ ≈ y₂ → x * y₁ ≈ x * y₂
*≫_ = *-cong refl
\end{code}
%</cong-combinators>
%<*cong-example>
\begin{code}
example
  : ∀ {a b c d x y}
  → x ≈ y
  → (a * (b * (x * c))) + d ≈
           (a * (b * (y * c))) + d
example prf = ≪+ *≫ *≫ ≪* prf
\end{code}
%</cong-example>
\begin{code}
infixr 0 _︔_
_︔_ : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
_︔_ = trans

infixr 2 _≅⟨_⟩_
_≅⟨_⟩_ : ∀ w {x y z} → (y ≈ z → w ≈ x) → y IsRelatedTo z → w IsRelatedTo x
_ ≅⟨ congruence ⟩ relTo y~z = relTo (congruence y~z)
\end{code}
