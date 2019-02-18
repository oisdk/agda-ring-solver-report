\begin{code}
module AbstractionAndFolds where

open import Relation.Unary
open import Relation.Nullary
open import Level using (_⊔_; lift; lower)
open import Data.List as List using (List; _∷_; []; foldr)
open import Data.Nat as ℕ using (ℕ; suc; zero; _≤′_; ≤′-step; ≤′-refl; _<′_)
open import Data.Nat.Properties as ℕ-Prop using (≤′-trans)
open import Data.Product using (_×_; _,_; map₁; map₂; proj₁; proj₂; curry; uncurry)
open import Algebra
open import Function
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false)

module Main
  {c}
  (coeffs : RawRing c)
  (Zero? : RawRing.Carrier coeffs → Bool)
  where

  open RawRing coeffs
  open import FinalPolyDefinition coeffs Zero?
  open import Data.List.Kleene

  -- Inject a polynomial into a larger polynomoial with more variables
  _Π↑_ : ∀ {n m} → Poly n → (suc n ≤′ m) → Poly m
  (xs Π i≤n) Π↑ n≤m = xs Π (≤′-step i≤n ⟨ ≤′-trans ⟩ n≤m)

  z≤′n : ∀ {n} → zero ≤′ n
  z≤′n {zero} = ≤′-refl
  z≤′n {suc n} = ≤′-step z≤′n

  -- NormalForm.sing Π
  infixr 4 _Π↓_
  _Π↓_ : ∀ {i n} → Coeff i ⋆ → suc i ≤′ n → Poly n
  []                          Π↓ i≤n = Κ 0# Π z≤′n
  [ x ≠0 Δ zero  & []      ]  Π↓ i≤n = x Π↑ i≤n
  [ x    Δ zero  & [ xs ]  ]  Π↓ i≤n = Σ (x Δ zero  & [ xs ]) Π i≤n
  [ x    Δ suc j & xs      ]  Π↓ i≤n = Σ (x Δ suc j & xs) Π i≤n

  -- Decision procedure for Zero
  zero? : ∀ {n} → (p : Poly n) → Dec (Zero p)
  zero? (Σ _ Π _) = no (λ z → z)
  zero? (Κ x Π _) with Zero? x
  zero? (Κ x Π _) | false = no (λ z → z)
  zero? (Κ x Π _) | true = yes tt

  -- Exponentiate the first variable of a polynomial

  infixr 8 _⍓⋆_ _⍓⁺_
  _⍓⋆_ : ∀ {n} → Coeff n ⋆ → ℕ → Coeff n ⋆
  _⍓⁺_ : ∀ {n} → Coeff n ⁺ → ℕ → Coeff n ⁺

  [] ⍓⋆ _ = []
  [ xs ] ⍓⋆ i = [ xs ⍓⁺ i ]

  (x Δ j & xs) ⍓⁺ i = x Δ (j ℕ.+ i) & xs

  infixr 5 _∷↓_
  _∷↓_ : ∀ {n} → PowInd (Poly n) → Coeff n ⋆ → Coeff n ⋆
  x Δ i ∷↓ xs with zero? x
  ... | yes p = xs ⍓⋆ suc i
  ... | no ¬p = [ _≠0 x {¬p} Δ i & xs ]


  module Simple where
\end{code}
%<*simple>
\begin{code}
    ⊟_ : ∀ {n} → Poly n → Poly n
    ⊟ (Κ x   Π i≤n) = Κ (- x) Π i≤n
    ⊟ (Σ xs  Π i≤n) = go [ xs ] Π↓ i≤n
      where
      go : ∀ {n} → Coeff n ⋆ → Coeff n ⋆
      go [] = []
      go [ x ≠0 Δ i & xs ] = ⊟ x Δ i ∷↓ go xs
\end{code}
%</simple>
\begin{code}
  module Metar where
    {-# TERMINATING #-}
\end{code}
%<*with-foldr>
\begin{code}
    ⊟_ : ∀ {n} → Poly n → Poly n
    ⊟ (Κ x   Π i≤n) = Κ (- x) Π i≤n
    ⊟ (Σ xs  Π i≤n) = foldr⁺ go [] xs Π↓ i≤n
      where
      go = λ { (x ≠0 Δ i) xs → ⊟ x Δ i ∷↓ xs }
\end{code}
%</with-foldr>
%<*fold-def>
\begin{code}
  Meta : ℕ → Set c
  Meta n = Poly n × Coeff n ⋆ → Poly n × Coeff n ⋆
\end{code}
%</fold-def>
%<*para>
\begin{code}
  para : ∀ {i} → Meta i → Coeff i ⁺ → Coeff i ⋆
  para f =
    foldr⁺
    (λ { (x ≠0 Δ i) →
         uncurry (_∷↓_ ∘ (_Δ i)) ∘ curry f x })
    []
\end{code}
%</para>
\begin{code}
  module AccDef where
\end{code}
%<*acc-def>
\begin{code}
    data Acc  {a r}
              {A : Set a}
              (_<_ : A → A → Set r)
              (x : A) : Set (a ⊔ r) where
      acc
        : (∀ y → y < x → Acc _<_ y)
        → Acc _<_ x

\end{code}
%</acc-def>
%<*acc-impl>
\begin{code}
    mutual
      <′-wellFounded : ∀ n → Acc _<′_ n
      <′-wellFounded n = acc (go n)

      go : ∀ n m → m <′ n → Acc _<′_ m
      go zero     _ ()
      go (suc n) .n ≤′-refl       = <′-wellFounded n
      go (suc n)  m (≤′-step m<n) = go n m m<n
\end{code}
%</acc-impl>
\begin{code}
  module Terminating where
    open import Induction.WellFounded using (Acc; acc)
    open import Induction.Nat using (<′-wellFounded)
\end{code}
%<*terminating>
\begin{code}
    ⊟′ : ∀ {n} → Acc _<′_ n → Poly n → Poly n
    ⊟′ (acc wf) (Κ x   Π i≤n) = Κ (- x) Π i≤n
    ⊟′ (acc wf) (Σ xs  Π i≤n) =
        foldr⁺ go [] xs Π↓ i≤n
      where
      go = λ  { (x ≠0 Δ i) xs
              → ⊟′ (wf _ i≤n) x Δ i ∷↓ xs  }

    ⊟_ : ∀ {n} → Poly n → Poly n
    ⊟_ = ⊟′ (<′-wellFounded _)
\end{code}
%</terminating>
\begin{code}
open import Polynomial.Parameters

module Semantics
  {r₁ r₂ r₃}
  (homo : Homomorphism r₁ r₂ r₃)
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
           → Poly n × Coeff n ⋆
           → Carrier × Vec Carrier n
           → Carrier
    (x , []) ⟦∷⟧ (ρ , ρs) = ⟦ x ⟧ ρs
    (x , [ xs ]) ⟦∷⟧ (ρ , ρs) =
      ρ * Σ⟦ xs ⟧ (ρ , ρs) + ⟦ x ⟧ ρs

    Σ⟦_⟧  : ∀ {n}
          → Coeff n ⁺
          → Carrier × Vec Carrier n
          → Carrier
    Σ⟦ x ≠0 Δ i & xs ⟧ (ρ , ρs) =
      ρ ^ i * (x , xs) ⟦∷⟧ (ρ , ρs)

    ⟦_⟧  : ∀ {n}
         → Poly n
         → Vec Carrier n
         → Carrier
    ⟦ Κ x   Π i≤n ⟧ _  = ⟦ x ⟧ᵣ
    ⟦ Σ xs  Π i≤n ⟧ ρ  = Σ⟦ xs ⟧ (drop-1 i≤n ρ)
\end{code}
%</semantics>
%<*sigma-q>
\begin{code}
  Σ?⟦_⟧ : ∀ {n} (xs : Coeff n ⋆) → Carrier × Vec Carrier n → Carrier
  Σ?⟦ [] ⟧ _ = 0#
  Σ?⟦ [ x ] ⟧ = Σ⟦ x ⟧
\end{code}
%</sigma-q>
\begin{code}
  open import Polynomial.NormalForm.Construction coeffs renaming (Fold to Meta)
  postulate
\end{code}
%<*lemmas>
\begin{code}
    Π↓-hom
      : ∀ {n m}
      → (xs : Coeff n ⋆)
      → (sn≤m : suc n ≤′ m)
      → ∀ ρ
      → ⟦  xs Π↓ sn≤m ⟧ ρ
           ≈ Σ?⟦ xs ⟧ (drop-1 sn≤m ρ)

    ∷↓-hom
      : ∀ {n}
      → (x : Poly n)
      → ∀ i xs ρ ρs
      → Σ?⟦  x Δ i ∷↓ xs ⟧ (ρ , ρs)
            ≈ ((x , xs) ⟦∷⟧ (ρ , ρs)) * ρ ^ i
\end{code}
%</lemmas>
%<*poly-mapR>
\begin{code}
    poly-mapR
      : ∀ {n} ρ ρs
      → ([f] : Poly n → Poly n)
      → (f : Carrier → Carrier)
      → (∀ x y → x * f y ≈ f (x * y))
      → (∀ x y → f (x + y) ≈ f x + f y)
      → (∀ y → ⟦ [f] y ⟧ ρs ≈ f (⟦ y ⟧ ρs))
      → (f 0# ≈ 0#)
      → ∀ xs
      → Σ?⟦ poly-map [f] xs ⟧ (ρ , ρs)
            ≈ f (Σ⟦ xs ⟧ (ρ , ρs))
\end{code}
%</poly-mapR>
%<*poly-foldR>
\begin{code}
    poly-foldR
      : ∀ {n} ρ
      → ([f] : Meta n)
      → (f : Carrier → Carrier)
      → (∀ x y → x * f y ≈ f (x * y))
      → ( ∀ y {ys} zs
          → Σ?⟦ ys ⟧ ρ ≈ f (Σ?⟦ zs ⟧ ρ)
          → [f] (y , ys) ⟦∷⟧ ρ ≈ f ((y , zs) ⟦∷⟧ ρ))
      → (f 0# ≈ 0#)
      → ∀ xs
      → Σ?⟦ para [f] xs ⟧ ρ ≈ f (Σ⟦ xs ⟧ ρ)
\end{code}
%</poly-foldR>
