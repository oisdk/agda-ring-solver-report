\begin{code}
{-# OPTIONS --without-K #-}

open import Algebra
open import Algebra.Solver.Ring.AlmostCommutativeRing
open import Relation.Binary hiding (Decidable)
open import Relation.Nullary
open import Relation.Unary
open import Level using (_⊔_; Lift; lift; lower)
open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.List as List using (_∷_; []; List)
open import Data.Vec as Vec using (_∷_; []; Vec)
open import Data.Nat as ℕ using (ℕ; suc; zero; compare)
open import Function
open import Data.Fin as Fin using (Fin)

module Poly
  {a ℓ}
  (coeffs : RawRing a)
  (Zero-C : Pred (RawRing.Carrier coeffs) ℓ)
  (zero-c? : Decidable Zero-C)
  where

open RawRing coeffs

module Slime where
  FlatPoly : ℕ → Set
  FlatPoly _ = ⊤
\end{code}
%<*poly-slime>

\begin{code}
  data Poly : ℕ → Set (a ⊔ ℓ) where
    _Π_  : ∀ i {j}
         → FlatPoly j
         → Poly (suc (i ℕ.+ j))
\end{code}
%</poly-slime>
\begin{code}
infix 4 _≤_
data _≤_ (m : ℕ) : ℕ → Set where
  m≤m : m ≤ m
  ≤-s : ∀ {n} → (m≤n : m ≤ n) → m ≤ suc n

infixl 6 _⋈_
_⋈_ : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
xs ⋈ m≤m = xs
xs ⋈ (≤-s ys) = ≤-s (xs ⋈ ys)

data Ordering {n : ℕ} : ∀ {i j}
                      → (i≤n : i ≤ n)
                      → (j≤n : j ≤ n)
                      → Set
                      where
  _<_ : ∀ {i j-1}
      → (i≤j-1 : i ≤ j-1)
      → (j≤n : suc j-1 ≤ n)
      → Ordering (≤-s i≤j-1 ⋈ j≤n) j≤n
  _>_ : ∀ {i-1 j}
      → (i≤n : suc i-1 ≤ n)
      → (j≤i-1 : j ≤ i-1)
      → Ordering i≤n (≤-s j≤i-1 ⋈ i≤n)
  eq : ∀ {i} → (i≤n : i ≤ n) → Ordering i≤n i≤n

_∺_ : ∀ {i j n}
    → (x : i ≤ n)
    → (y : j ≤ n)
    → Ordering x y
m≤m ∺ m≤m = eq m≤m
m≤m ∺ ≤-s y = m≤m > y
≤-s x ∺ m≤m = x < m≤m
≤-s x ∺ ≤-s y with x ∺ y
≤-s .(≤-s i≤j-1 ⋈ y) ∺ ≤-s y                | i≤j-1 < .y = i≤j-1 < ≤-s y
≤-s x                ∺ ≤-s .(≤-s j≤i-1 ⋈ x) | .x > j≤i-1 = ≤-s x > j≤i-1
≤-s x                ∺ ≤-s .x               | eq .x = eq (≤-s x)

z≤n : ∀ {n} → zero ≤ n
z≤n {zero} = m≤m
z≤n {suc n} = ≤-s z≤n

module Full where
  mutual
\end{code}
%<*poly>
\begin{code}
    infixl 6 _Π_
    record Poly (n : ℕ) : Set (a ⊔ ℓ) where
      inductive
      constructor _Π_
      field
        {i}   : ℕ
        flat  : FlatPoly i
        i≤n   : i ≤ n
\end{code}
%</poly>
\begin{code}
    data FlatPoly : ℕ → Set (a ⊔ ℓ) where
      Κ : Carrier → FlatPoly 0
      Σ : ∀ {n} → (xs : Coeffs n) → .{xn : Norm xs} → FlatPoly (suc n)

    infixl 6 _Δ_
    record CoeffExp (i : ℕ) : Set (a ⊔ ℓ) where
      inductive
      constructor _Δ_
      field
        coeff : Coeff i
        pow   : ℕ

    Coeffs : ℕ → Set (a ⊔ ℓ)
    Coeffs n = List (CoeffExp n)

    infixl 6 _≠0
    record Coeff (i : ℕ) : Set (a ⊔ ℓ) where
      inductive
      constructor _≠0
      field
        poly : Poly i
        .{poly≠0} : ¬ Zero poly

    Zero : ∀ {n} → Poly n → Set ℓ
    Zero (Κ x       Π _) = Zero-C x
    Zero (Σ []      Π _) = Lift ℓ ⊤
    Zero (Σ (_ ∷ _) Π _) = Lift ℓ ⊥

    Norm : ∀ {i} → Coeffs i → Set
    Norm []                  = ⊥
    Norm (_ Δ zero  ∷ [])    = ⊥
    Norm (_ Δ zero  ∷ _ ∷ _) = ⊤
    Norm (_ Δ suc _ ∷ _)     = ⊤
\end{code}
