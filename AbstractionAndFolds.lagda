\begin{code}
module AbstractionAndFolds where

open import Relation.Unary
open import Relation.Nullary
open import Level using (_⊔_; lift; lower)
open import Data.List as List using (List; _∷_; []; foldr)
open import Data.Nat as ℕ using (ℕ; suc; zero; _≤′_; ≤′-step; ≤′-refl)
open import Data.Nat.Properties as ℕ-Prop using (≤′-trans)
open import Data.Product using (_×_; _,_; map₁; map₂; proj₁; proj₂)
open import Algebra
open import Function
open import Data.Unit using (⊤; tt)

module Main
  {c ℓ}
  (coeffs : RawRing c)
  (Zero-C : Pred (RawRing.Carrier coeffs) ℓ)
  (zero-c? : Decidable Zero-C) where

  open RawRing coeffs
  open import FinalPolyDefinition coeffs Zero-C

  -- Inject a polynomial into a larger polynomoial with more variables
  _Π↑_ : ∀ {n m} → Poly n → (suc n ≤′ m) → Poly m
  (xs Π i≤n) Π↑ n≤m = xs Π (≤′-step i≤n ⟨ ≤′-trans ⟩ n≤m)

  z≤′n : ∀ {n} → zero ≤′ n
  z≤′n {zero} = ≤′-refl
  z≤′n {suc n} = ≤′-step z≤′n

  -- NormalForm.sing Π
  infixr 4 _Π↓_
  _Π↓_ : ∀ {i n} → Coeffs i → suc i ≤′ n → Poly n
  []                       Π↓ i≤n = Κ 0# Π z≤′n
  (x ≠0 Δ zero  ∷ [])      Π↓ i≤n = x Π↑ i≤n
  (x₁   Δ zero  ∷ x₂ ∷ xs) Π↓ i≤n = Σ (x₁ Δ zero  ∷ x₂ ∷ xs) Π i≤n
  (x    Δ suc j ∷ xs)      Π↓ i≤n = Σ (x  Δ suc j ∷ xs) Π i≤n

  -- Decision procedure for Zero
  zero? : ∀ {n} → (p : Poly n) → Dec (Zero p)
  zero? (Σ []      Π _) = yes (lift tt)
  zero? (Σ (_ ∷ _) Π _) = no lower
  zero? (Κ x       Π _) = zero-c? x

  -- Exponentiate the first variable of a polynomial
  infixr 8 _⍓_
  _⍓_ : ∀ {n} → Coeffs n → ℕ → Coeffs n
  [] ⍓ i = []
  (x Δ j ∷ xs) ⍓ i = x Δ (j ℕ.+ i) ∷ xs

  infixr 5 _∷↓_
  _∷↓_ : ∀ {n} → PowInd (Poly n) → Coeffs n → Coeffs n
  x Δ i ∷↓ xs with zero? x
  ... | yes p = xs ⍓ suc i
  ... | no ¬p = _≠0 x {¬p} Δ i ∷ xs


  module Simple where
\end{code}
%<*simple>
\begin{code}
    ⊟_ : ∀ {n} → Poly n → Poly n
    ⊟ (Κ x   Π i≤n) = Κ (- x) Π i≤n
    ⊟ (Σ xs  Π i≤n) = go xs Π↓ i≤n
      where
      go : ∀ {n} → Coeffs n → Coeffs n
      go [] = []
      go (x ≠0 Δ i ∷ xs) = ⊟ x Δ i ∷↓ go xs
\end{code}
%</simple>
\begin{code}
  module Foldr where
  {-# TERMINATING #-}
\end{code}
%<*with-foldr>
\begin{code}
  ⊟_ : ∀ {n} → Poly n → Poly n
  ⊟ (Κ x   Π i≤n) = Κ (- x) Π i≤n
  ⊟ (Σ xs  Π i≤n) = foldr go [] xs Π↓ i≤n
    where
    go = λ { (x ≠0 Δ i) xs → ⊟ x Δ i ∷↓ xs }
\end{code}
%</with-foldr>
\begin{code}
open import Polynomial.Parameters

module Semantics
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where

  open import Data.Nat     using (ℕ; suc; zero)
  open import Data.Vec     using (Vec; []; _∷_)
  open import Data.List    using ([]; _∷_)
  open import Data.Product using (_,_; _×_)

  open import Polynomial.NormalForm.InjectionIndex
  open Homomorphism homo
  open import Polynomial.NormalForm.Definition coeffs

  open import Polynomial.Exponentiation rawRing

  drop : ∀ {i n} → i ≤′ n → Vec Carrier n → Vec Carrier i
  drop ≤′-refl ρs = ρs
  drop (≤′-step si≤n) (_ ∷ ρs) = drop si≤n ρs

  vec-uncons : ∀ {n} → Vec Carrier (suc n) → Carrier × Vec Carrier n
  vec-uncons (x ∷ xs) = x , xs

  drop-1 : ∀ {i n} → suc i ≤′ n → Vec Carrier n → Carrier × Vec Carrier i
  drop-1 si≤n xs = vec-uncons (drop si≤n xs)

  mutual
\end{code}
%<*semantics>
\begin{code}
    _⟦∷⟧_  : ∀ {n}
           → Poly n × Coeffs n
           → Carrier × Vec Carrier n
           → Carrier
    (x , xs) ⟦∷⟧ (ρ , ρs) =
      ⟦ x ⟧ ρs + Σ⟦ xs ⟧ (ρ , ρs) * ρ

    Σ⟦_⟧  : ∀ {n}
          → Coeffs n
          → Carrier × Vec Carrier n
          → Carrier
    Σ⟦ [] ⟧ _ = 0#
    Σ⟦ x ≠0 Δ i ∷ xs ⟧ (ρ , ρs) =
      (x , xs) ⟦∷⟧ (ρ , ρs) * ρ ^ i

    ⟦_⟧  : ∀ {n}
         → Poly n
         → Vec Carrier n
         → Carrier
    ⟦ Κ x   Π i≤n ⟧ _  = ⟦ x ⟧ᵣ
    ⟦ Σ xs  Π i≤n ⟧ ρ  = Σ⟦ xs ⟧ (drop-1 i≤n ρ)
\end{code}
%</semantics>
\begin{code}
  open import Polynomial.NormalForm.Construction coeffs
  postulate
\end{code}
%<*lemmas>
\begin{code}
    Π↓-hom
      : ∀ {n m}
      → (xs : Coeffs n)
      → (sn≤m : suc n ≤′ m)
      → ∀ ρ
      → ⟦  xs Π↓ sn≤m ⟧ ρ
           ≈ Σ⟦ xs ⟧ (drop-1 sn≤m ρ)

    ∷↓-hom
      : ∀ {n}
      → (x : Poly n)
      → ∀ i xs ρ ρs
      → Σ⟦  x Δ i ∷↓ xs ⟧ (ρ , ρs)
            ≈ ((x , xs) ⟦∷⟧ (ρ , ρs)) * ρ ^ i
\end{code}
%</lemmas>
%<*poly-mapR>
\begin{code}
    poly-mapR
      : ∀ {n} ρ ρs
      → ([f] : Poly n → Poly n)
      → (f : Carrier → Carrier)
      → (∀ x y → f x * y ≈ f (x * y))
      → (∀ x y → f (x + y) ≈ f x + f y)
      → (∀ y → ⟦ [f] y ⟧ ρs ≈ f (⟦ y ⟧ ρs))
      → (f 0# ≈ 0#)
      → ∀ xs
      → Σ⟦  poly-map [f] xs ⟧ (ρ , ρs)
            ≈ f (Σ⟦ xs ⟧ (ρ , ρs))
\end{code}
%</poly-mapR>
