\begin{code}
open import Algebra

module FinalPolyDefinition {a ℓ} (coeffs : RawRing a) (Zero-C : RawRing.Carrier coeffs → Set ℓ)  where

open RawRing coeffs

open import Relation.Nullary using (¬_)
open import Level            using (_⊔_; Lift)
open import Data.Empty       using (⊥)
open import Data.Unit        using (⊤)
open import Data.List        using (_∷_; []; List)
open import Data.Nat         using (ℕ; suc; zero; _≤′_)
open import Function         using (_∘_)

\end{code}
%<*final-poly-def>
\begin{code}
infixl 6 _Δ_
record PowInd {c} (C : Set c) : Set c where
  inductive
  constructor _Δ_
  field
    coeff  : C
    pow    : ℕ

mutual
  infixl 6 _Π_
  record Poly (n : ℕ) : Set (a ⊔ ℓ) where
    inductive
    constructor _Π_
    field
      {i}   : ℕ
      flat  : FlatPoly i
      i≤n   : i ≤′ n

  data FlatPoly : ℕ → Set (a ⊔ ℓ) where
    Κ  : Carrier → FlatPoly zero
    Σ  : ∀ {n}
       → (xs : Coeffs n)
       → .{xn : Norm xs}
       → FlatPoly (suc n)

  Coeffs : ℕ → Set (a ⊔ ℓ)
  Coeffs = List ∘ PowInd ∘ NonZero

  infixl 6 _≠0
  record NonZero (i : ℕ) : Set (a ⊔ ℓ) where
    inductive
    constructor _≠0
    field
      poly : Poly i
      .{poly≠0} : ¬ Zero poly

  Zero : ∀ {n} → Poly n → Set ℓ
  Zero (Κ x        Π _) = Zero-C x
  Zero (Σ []       Π _) = Lift _ ⊤
  Zero (Σ (_ ∷ _)  Π _) = Lift _ ⊥

  Norm : ∀ {i} → Coeffs i → Set
  Norm []                    = ⊥
  Norm (_ Δ zero   ∷ [])     = ⊥
  Norm (_ Δ zero   ∷ _ ∷ _)  = ⊤
  Norm (_ Δ suc _  ∷ _)      = ⊤
\end{code}
%</final-poly-def>
