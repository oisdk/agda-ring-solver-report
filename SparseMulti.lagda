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
open import Data.Unit using (⊤)
module Flat
  {c ℓ}
  (coeffs : RawRing c)
  (Zero : Pred (RawRing.Carrier coeffs) ℓ)
  (zero? : Decidable Zero) where

  open RawRing coeffs
  mutual
\end{code}
%<*dense-poly>
\begin{code}
    record Coeff n : Set (c ⊔ ℓ) where
      inductive
      constructor _≠0
      field
        coeff : Poly n
        .{coeff≠0} : ¬Zero coeff

    record PowInd {c} (C : Set c) : Set c where
      inductive
      constructor _Δ_
      field
        coeff : C
        power : ℕ

    Poly : ℕ → Set (c ⊔ ℓ)
    Poly zero = Lift ℓ Carrier
    Poly (suc n) = List (PowInd (Coeff n))

    ¬Zero : ∀ {n} → Poly n → Set ℓ
    ¬Zero {zero} (lift lower) = ¬ Zero lower
    ¬Zero {suc n} [] = Lift _ ⊥
    ¬Zero {suc n} (x ∷ xs) = Lift _ ⊤
\end{code}
%</dense-poly>
\begin{code}
module Sparse
  {c ℓ}
  (coeffs : RawRing c)
  (Zero : Pred (RawRing.Carrier coeffs) ℓ)
  (zero? : Decidable Zero) where
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
    record Poly (n : ℕ) : Set (c ⊔ ℓ) where
      inductive
      constructor _Π_
      field
        {i}   : ℕ
        flat  : FlatPoly i
        i≤n   : i ≤ n

    data FlatPoly : ℕ → Set (c ⊔ ℓ) where
      Κ : Carrier → FlatPoly zero
      Σ  : ∀ {n}
         → (xs : Coeffs n)
         → .{xn : Norm xs}
         → FlatPoly (suc n)

    Coeffs : ℕ → Set (c ⊔ ℓ)
    Coeffs = List ∘ PowInd ∘ NonZero

    infixl 6 _≠0
    record NonZero (i : ℕ) : Set (c ⊔ ℓ) where
      inductive
      constructor _≠0
      field
        poly : Poly i
        .{poly≠0} : ¬ ZeroPoly poly
\end{code}
%</sparse-poly>
\begin{code}
    ZeroPoly : ∀ {n} → Poly n → Set ℓ
    ZeroPoly (Κ x       Π _) = Zero x
    ZeroPoly (Σ []      Π _) = Lift _ ⊤
    ZeroPoly (Σ (_ ∷ _) Π _) = Lift _ ⊥

    Norm : ∀ {i} → Coeffs i → Set
    Norm []                  = ⊥
    Norm (_ Δ zero  ∷ [])    = ⊥
    Norm (_ Δ zero  ∷ _ ∷ _) = ⊤
    Norm (_ Δ suc _ ∷ _) = ⊤
\end{code}
