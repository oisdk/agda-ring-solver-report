\begin{code}
open import Relation.Unary
open import Relation.Nullary
open import Level using (_⊔_)
open import Data.List as List using (List; _∷_; []; foldr)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Product using (_×_; _,_; map₁; map₂; proj₁; proj₂)
\end{code}
%<*opening>
\begin{code}
open import Algebra

module EliminatingRedundancy
  {c ℓ}
  (coeffs : RawRing c)
  (Zero : Pred (RawRing.Carrier coeffs) ℓ)
  (zero? : Decidable Zero) where

open RawRing coeffs
\end{code}
%</opening>
%<*decl>
\begin{code}
infixl 6 _≠0
record Coeff : Set (c ⊔ ℓ) where
  constructor _≠0
  field
    coeff : Carrier
    .{coeff≠0} : ¬ Zero coeff
open Coeff

infixl 6 _Δ_
record PowInd {c} (C : Set c) : Set c where
  constructor _Δ_
  field
    coeff : C
    power : ℕ
open PowInd

Poly : Set (c ⊔ ℓ)
Poly = List (PowInd Coeff)
\end{code}
%</decl>
%<*norm-cons>
\begin{code}
infixr 8 _⍓_
_⍓_ : Poly → ℕ → Poly
[] ⍓ i = []
(x Δ j ∷ xs) ⍓ i = x Δ (j ℕ.+ i) ∷ xs

infixr 5 _∷↓_
_∷↓_ : PowInd Carrier → Poly → Poly
x Δ i ∷↓ xs with zero? x
... | yes p = xs ⍓ suc i
... | no ¬p = _≠0 x {¬p} Δ i ∷ xs
\end{code}
%</norm-cons>
