\begin{code}
{-# OPTIONS --without-K #-}

open import Algebra.Solver.Ring.AlmostCommutativeRing

module CorrectByConstruction
  {a ℓ}
  (coeffs : AlmostCommutativeRing a ℓ)
  where


module Vects where
 open import Data.Nat
\end{code}
%<*vec-def>
\begin{code}
 data Vec {a} (A : Set a) : ℕ → Set a where
   []   : Vec A zero
   _∷_  : ∀ {n}
        → A
        → Vec A n
        → Vec A (suc n)
\end{code}
%</vec-def>
\begin{code}
 module _ {a} {A : Set a} where
\end{code}
%<*vec-app>
\begin{code}
  _++_  : ∀ {n m}
        → Vec A m
        → Vec A n
        → Vec A (m + n)
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)
\end{code}
%</vec-app>
\begin{code}
module Lists where
 open import Data.Nat
 open import Relation.Binary.PropositionalEquality
\end{code}
%<*list-def>
\begin{code}
 data List {a} (A : Set a) : Set a where
   []   : List A
   _∷_  : A
        → List A
        → List A
\end{code}
%</list-def>
\begin{code}
 module _ {a} {A : Set a} where
\end{code}
%<*list-app>
\begin{code}
  _++_ : List A
       → List A
       → List A
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)
\end{code}
%</list-app>
%<*list-proof>
\begin{code}
  length : List A → ℕ
  length [] = zero
  length (x ∷ xs) = suc (length xs)

  length-+
    : (xs ys : List A)
    → length xs + length ys ≡ length (xs ++ ys)
  length-+ [] ys = refl
  length-+ (x ∷ xs) ys =
    cong suc (length-+ xs ys)
\end{code}
%</list-proof>
\begin{code}

open import Level
open import Function



module Context where
  open AlmostCommutativeRing coeffs
  open import Relation.Binary

  Fn : Set a
  Fn = Carrier → Carrier

  infix 4 _≋_
  _≋_ : Fn → Fn → Set (a ⊔ ℓ)
  x ≋ y = ∀ ρ → x ρ ≈ y ρ

  ≋-equiv : IsEquivalence _≋_
  ≋-equiv = record
    { refl = λ ρ → refl
    ; sym  = λ x≈y ρ → sym (x≈y ρ)
    ; trans = λ x≈y y≈z ρ → trans (x≈y ρ) (y≈z ρ)
    }

  exprRing : AlmostCommutativeRing a (a ⊔ ℓ)
  exprRing = record
    { Carrier = Fn
    ; _≈_     = _≋_
    ; _+_     = λ x y ρ → x ρ + y ρ
    ; _*_     = λ x y ρ → x ρ * y ρ
    ; -_      = λ x ρ → - x ρ
    ; 0#      = λ _ → 0#
    ; 1#      = λ _ → 1#
    ; isAlmostCommutativeRing = record
      { -‿cong                = λ xρ≈yρ ρ → -‿cong (xρ≈yρ ρ)
      ; -‿*-distribˡ          = λ x y ρ → -‿*-distribˡ (x ρ) (y ρ)
      ; -‿+-comm              = λ x y ρ → -‿+-comm (x ρ) (y ρ)
      ; isCommutativeSemiring = record
        { zeroˡ = λ x ρ → zeroˡ (x ρ)
        ; distribʳ = λ x y z ρ → distribʳ (x ρ) (y ρ) (z ρ)
        ; +-isCommutativeMonoid = record
          { identityˡ = λ x ρ → +-identityˡ (x ρ)
          ; comm = λ x y ρ → +-comm (x ρ) (y ρ)
          ; isSemigroup = record
            { assoc = λ x y z ρ → +-assoc (x ρ) (y ρ) (z ρ)
            ; isMagma = record
              { ∙-cong = λ x₁≈x₂ y₁≈y₂ ρ → +-cong (x₁≈x₂ ρ) (y₁≈y₂ ρ)
              ; isEquivalence = ≋-equiv
              }
            }
          }
        ; *-isCommutativeMonoid = record
          { identityˡ = λ x ρ → *-identityˡ (x ρ)
          ; comm = λ x y ρ → *-comm (x ρ) (y ρ)
          ; isSemigroup = record
            { assoc = λ x y z ρ → *-assoc (x ρ) (y ρ) (z ρ)
            ; isMagma = record
              { ∙-cong = λ x₁≈x₂ y₁≈y₂ ρ → *-cong (x₁≈x₂ ρ) (y₁≈y₂ ρ)
              ; isEquivalence = ≋-equiv
              }
            }
          }
        }
      }
    }

module Lemmas where
  open AlmostCommutativeRing coeffs
  open import Relation.Binary.EqReasoning setoid

  +-distrib : ∀ {x xs y ys} ρ → (x + ρ * xs) + (y + ρ * ys) ≈ x + y + ρ * (xs + ys)
  +-distrib {x} {xs} {y} {ys} ρ =
    begin
      (x + ρ * xs) + (y + ρ * ys)
    ≈⟨ +-assoc x _ _ ⟩
      x + (ρ * xs + (y + ρ * ys))
    ≈⟨ refl ⟨ +-cong ⟩ (sym (+-assoc _ y _) ⟨ trans ⟩ ( +-comm _ y ⟨ +-cong ⟩ refl ⟨ trans ⟩ +-assoc _ _ _)) ⟩
      x + (y + (ρ * xs + ρ * ys))
    ≈⟨ sym (+-assoc x y _) ⟩
      x + y + (ρ * xs + ρ * ys)
    ≈⟨ refl ⟨ +-cong ⟩ sym (distribˡ ρ xs ys) ⟩
      x + y + ρ * (xs + ys)
    ∎

open Lemmas
open Context
open AlmostCommutativeRing exprRing
module Coeff = AlmostCommutativeRing coeffs
open import Relation.Binary.EqReasoning setoid
\end{code}
%<*constr-def>
\begin{code}
data Poly : Carrier → Set (a ⊔ ℓ) where
  ⟦⟧ : Poly 0#
  ⟦_∷_⟧
    : ∀ x {xs}
    → Poly xs
    → Poly (λ ρ → x Coeff.+ ρ Coeff.* xs ρ)

infixr 0 _⇐_
record Expr (expr : Carrier) : Set (a ⊔ ℓ) where
  constructor _⇐_
  field
    {norm} : Carrier
    poly   : Poly norm
    proof  : expr ≋ norm
\end{code}
%</constr-def>
%<*constr-add>
\begin{code}
infixr 0 _⟸_
_⟸_ : ∀ {x y} → x ≋ y → Expr y → Expr x
x≋y ⟸ xs ⇐ xp = xs ⇐ x≋y ⟨ trans ⟩ xp

_⊞_ : ∀ {x y}
    → Expr x
    → Expr y
    → Expr (x + y)
(x ⇐ xp) ⊞ (y ⇐ yp) =
  xp ⟨ +-cong ⟩ yp ⟸ x ⊕ y
  where
  _⊕_ : ∀ {x y}
      → Poly x
      → Poly y
      → Expr (x + y)
  ⟦⟧ ⊕ ys = ys ⇐ +-identityˡ _
  ⟦ x ∷ xs ⟧ ⊕ ⟦⟧ = ⟦ x ∷ xs ⟧ ⇐ +-identityʳ _
  ⟦ x ∷ xs ⟧ ⊕ ⟦ y ∷ ys ⟧ with xs ⊕ ys
  ... | zs ⇐ zp = ⟦ x Coeff.+ y ∷ zs ⟧ ⇐
      (λ ρ → +-distrib ρ)
    ⟨ trans ⟩
      (refl ⟨ +-cong ⟩ (refl ⟨ *-cong ⟩ zp))
\end{code}
%</constr-add>
\begin{code}
\end{code}
