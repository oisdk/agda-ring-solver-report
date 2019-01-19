\begin{code}
open import Algebra
open import Data.Bool using (Bool; true; false; T)

module FinalPolyDefinition {a}
  (coeffs : RawRing a)
  (Zero? : RawRing.Carrier coeffs → Bool)  where

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
  record Poly (n : ℕ) : Set a where
    inductive
    constructor _Π_
    field
      {i}   : ℕ
      flat  : FlatPoly i
      i≤n   : i ≤′ n

  data FlatPoly : ℕ → Set a where
    Κ  : Carrier → FlatPoly zero
    Σ  : ∀ {n}
       → (xs : Coeffs n)
       → .{xn : Norm xs}
       → FlatPoly (suc n)

  Coeffs : ℕ → Set a
  Coeffs = List ∘ PowInd ∘ NonZero

  infixl 6 _≠0
  record NonZero (i : ℕ) : Set a where
    inductive
    constructor _≠0
    field
      poly : Poly i
      .{poly≠0} : ¬ Zero poly

  Zero : ∀ {n} → Poly n → Set
  Zero (Κ x        Π _) = T (Zero? x)
  Zero (Σ []       Π _) = ⊤
  Zero (Σ (_ ∷ _)  Π _) = ⊥

  Norm : ∀ {i} → Coeffs i → Set
  Norm []                    = ⊥
  Norm (_ Δ zero   ∷ [])     = ⊥
  Norm (_ Δ zero   ∷ _ ∷ _)  = ⊤
  Norm (_ Δ suc _  ∷ _)      = ⊤
\end{code}
%</final-poly-def>
