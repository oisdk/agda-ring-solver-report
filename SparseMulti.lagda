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
%<*sparse-poly>
%</sparse-poly>
