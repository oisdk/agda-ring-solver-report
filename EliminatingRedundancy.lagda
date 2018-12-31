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
\begin{code}
open import Data.Nat using (compare; less; equal; greater; Ordering)
module NonTerminating where

 infixl 6 _⊞_
 {-# TERMINATING #-}
\end{code}
%<*nonterm-add>
\begin{code}
 _⊞_ : Poly → Poly → Poly
 []  ⊞  ys  = ys
 xs  ⊞  []  = xs
 (x Δ i ∷ xs) ⊞ (y Δ j ∷ ys) with compare i j
 ... | less     i k  = x Δ i ∷ xs ⊞ (y Δ k ∷ ys)
 ... | greater  j k  = y Δ j ∷ (x Δ k ∷ xs) ⊞ ys
 ... | equal i = coeff x + coeff y Δ i ∷↓ xs ⊞ ys
\end{code}
%</nonterm-add>
%<*term-add>
\begin{code}
infixl 6 _⊞_
_⊞_ : Poly → Poly → Poly
[] ⊞ ys = ys
(x ∷ xs) ⊞ ys = ⟨ x ∷ xs ⊞ ys ⟩
  where
  ⟨_∷_⊞_⟩ : PowInd Coeff → Poly → Poly → Poly
  _⊢⟨_∷_⊞_∷_⟩ : ∀ {i j} → Ordering i j → Coeff → Poly → Coeff → Poly → Poly

  less     i  k  ⊢⟨ x ∷ xs ⊞ y ∷ ys ⟩ = x Δ i ∷ ⟨ y Δ k ∷ ys ⊞ xs ⟩
  greater  j  k  ⊢⟨ x ∷ xs ⊞ y ∷ ys ⟩ = y Δ j ∷ ⟨ x Δ k ∷ xs ⊞ ys ⟩
  equal       k  ⊢⟨ x ∷ xs ⊞ y ∷ ys ⟩ = coeff x + coeff y Δ k ∷↓ xs ⊞ ys

  ⟨ x ∷ xs ⊞ [] ⟩ = x ∷ xs
  ⟨ x Δ i ∷ xs ⊞ y Δ j ∷ ys ⟩ = compare i j ⊢⟨ x ∷ xs ⊞ y ∷ ys ⟩
\end{code}
%</term-add>
