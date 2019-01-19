\begin{code}
module SparseMulti where
\end{code}
\begin{code}
open import Algebra
open import Relation.Unary
open import Relation.Nullary
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Level using (_⊔_; Lift; lift)
open import Data.List as List using (List; _∷_; [])
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false; T)
module Flat
  {c}
  (coeffs : RawRing c)
  (Zero? : RawRing.Carrier coeffs → Bool)
  where

  open RawRing coeffs
  mutual
\end{code}
%<*dense-poly>
\begin{code}
    record Coeff n : Set c where
      inductive
      constructor _≠0
      field
        coeff : Poly n
        .{coeff≠0} : ¬ Zero coeff

    record PowInd {c} (C : Set c) : Set c where
      inductive
      constructor _Δ_
      field
        coeff : C
        power : ℕ

    Poly : ℕ → Set c
    Poly zero = Carrier
    Poly (suc n) = List (PowInd (Coeff n))

    Zero : ∀ {n} → Poly n → Set
    Zero {zero} x = T (Zero? x)
    Zero {suc n} [] = ⊤
    Zero {suc n} (x ∷ xs) = ⊥
\end{code}
%</dense-poly>
\begin{code}
module Sparse
  {c}
  (coeffs : RawRing c)
  (Zero? : RawRing.Carrier coeffs → Bool)
  where
  open RawRing coeffs
  open import Data.Nat using (_≤_)
  open import Function
\end{code}
%<*sparse-poly>
\begin{code}
  infixl 6 _Δ_
  record PowInd {c} (C : Set c) : Set c where
    inductive
    constructor _Δ_
    field
      coeff : C
      pow   : ℕ

  mutual
    infixl 6 _Π_
    data Poly : ℕ → Set c where
      _Π_  : ∀ {j}
           → FlatPoly j
           → ∀ i
           → Poly (suc (i ℕ.+ j))

    data FlatPoly : ℕ → Set c where
      Κ  : Carrier → FlatPoly zero
      Σ  : ∀ {n}
         → (xs : Coeffs n)
         → .{xn : Norm xs}
         → FlatPoly (suc n)

    Coeffs : ℕ → Set c
    Coeffs = List ∘ PowInd ∘ NonZero

    infixl 6 _≠0
    record NonZero (i : ℕ) : Set c where
      inductive
      constructor _≠0
      field
        poly : Poly i
        .{poly≠0} : ¬ ZeroPoly poly
\end{code}
%</sparse-poly>
\begin{code}
    ZeroPoly : ∀ {n} → Poly n → Set
    ZeroPoly (Κ x       Π _) = T (Zero? x)
    ZeroPoly (Σ []      Π _) = ⊤
    ZeroPoly (Σ (_ ∷ _) Π _) = ⊥

    Norm : ∀ {i} → Coeffs i → Set
    Norm []                  = ⊥
    Norm (_ Δ zero  ∷ [])    = ⊥
    Norm (_ Δ zero  ∷ _ ∷ _) = ⊤
    Norm (_ Δ suc _ ∷ _) = ⊤
\end{code}
