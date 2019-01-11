\begin{code}
module EfficiencyInIndexedTypes where
\end{code}
\begin{code}
open import Algebra
open import Relation.Unary
open import Relation.Nullary
open import Data.Nat as ℕ using (ℕ; suc; zero; _+_; _∸_)
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
%<*ord-type>
\begin{code}
data Ordering : ℕ → ℕ → Set where
  less     : ∀ m k  → Ordering m (suc (m + k))
  equal    : ∀ m    → Ordering m m
  greater  : ∀ m k  → Ordering (suc (m + k)) m
\end{code}
%</ord-type>
\begin{code}
module LinearCompare where
\end{code}
%<*cmp-impl>
\begin{code}
  compare : ∀ m n → Ordering m n
  compare zero     zero     = equal    zero
  compare (suc m)  zero     = greater  zero m
  compare zero     (suc n)  = less     zero n
  compare (suc m)  (suc n) with compare m n
  ... | less     m   k  = less     (suc m)  k
  ... | equal    m      = equal    (suc m)
  ... | greater  n   k  = greater  (suc n)  k
\end{code}
%</cmp-impl>

\begin{code}
module FastCompare where
  open import Agda.Builtin.Nat using (_<_; _==_; _+_)
  open import Data.Bool using (Bool; true; false)
  open import Relation.Binary.PropositionalEquality
  open import Relation.Binary.PropositionalEquality.TrustMe
\end{code}
%<*fast-cmp-hom>
\begin{code}
  lt-hom  : ∀ n m
          → ((n < m) ≡ true)
          → m ≡ suc (n + (m ∸ n ∸ 1))
  lt-hom zero     zero     ()
  lt-hom zero     (suc m)  _    = refl
  lt-hom (suc n)  zero     ()
  lt-hom (suc n)  (suc m)  n<m  =
    cong suc (lt-hom n m n<m)

  eq-hom : ∀ n m
         → ((n == m) ≡ true)
         → n ≡ m
  eq-hom zero      zero     _    = refl
  eq-hom zero      (suc m)  ()
  eq-hom (suc n)   zero     ()
  eq-hom (suc n)   (suc m)  n≡m  =
    cong suc (eq-hom n m n≡m)

  gt-hom : ∀ n m
         → ((n < m) ≡ false)
         → ((n == m) ≡ false)
         → n ≡ suc (m + (n ∸ m ∸ 1))
  gt-hom zero       zero     n<m  ()
  gt-hom zero       (suc m)  ()   n≡m
  gt-hom (suc n)    zero     n<m  n≡m  = refl
  gt-hom (suc n)    (suc m)  n<m  n≡m  =
    cong suc (gt-hom n m n<m n≡m)
\end{code}
%</fast-cmp-hom>
%<*fast-cmp>
\begin{code}
  compare : ∀ n m → Ordering n m
  compare n m with n < m  | inspect (n <_) m
  ... | true   | [ n<m  ] rewrite erase (lt-hom n m n<m)      = less n (m ∸ n ∸ 1)
  ... | false  | [ n≮m  ] with n == m | inspect (n ==_) m
  ... | true   | [ n≡m  ] rewrite erase (eq-hom n m n≡m)      = equal m
  ... | false  | [ n≢m  ] rewrite erase (gt-hom n m n≮m n≢m)  = greater m (n ∸ m ∸ 1)
\end{code}
%</fast-cmp>
\begin{code}
module Slime
  {a ℓ}
  (coeffs : RawRing a)
  (Zero-C : Pred (RawRing.Carrier coeffs) ℓ)
  (zero-c? : Decidable Zero-C)
  where
  open RawRing coeffs
  open import Data.Nat using (_≤_)

  FlatPoly : ℕ → Set
  FlatPoly _ = ⊤
\end{code}
%<*sparse-poly>
\begin{code}
  record Poly (i : ℕ) : Set (a ⊔ ℓ) where
    inductive
    constructor _Π_
    field
      {j}   : ℕ
      flat  : FlatPoly j
      j≤i   : j ≤ i
\end{code}
%</sparse-poly>
\begin{code}
module LEQ1 where
\end{code}
%<*leq-1>
\begin{code}
  data _≤_ : ℕ → ℕ → Set where
    z≤n  : ∀ {n} → zero  ≤ n
    s≤s  : ∀ {m n}
         → (m≤n : m ≤ n)
         → suc m ≤ suc n
\end{code}
%</leq-1>
\begin{code}
module LEQ2 where
  open import Relation.Binary.PropositionalEquality
  open import Data.Nat using (_+_)
\end{code}
%<*leq-2>
\begin{code}
  record _≤_ (m n : ℕ) : Set where
    constructor less-than-or-equal
    field
      {k}   : ℕ
      proof : m + k ≡ n
\end{code}
%</leq-2>
\begin{code}
open import Function
infix 4 _≤_
\end{code}
%<*leq-3>
\begin{code}
data _≤_ (m : ℕ) : ℕ → Set where
  m≤m  : m ≤ m
  ≤-s  : ∀ {n}
        → (m≤n : m ≤ n)
        → m ≤ suc n
\end{code}
%</leq-3>
%<*leq-trans>
\begin{code}
≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
≤-trans x≤y m≤m = x≤y
≤-trans x≤y (≤-s y≤z) = ≤-s (≤-trans x≤y y≤z)
\end{code}
%</leq-trans>
%<*leq-compare>
\begin{code}
data ≤-Ordering {n : ℕ}  : ∀ {i j}
                         → (i≤n : i ≤ n)
                         → (j≤n : j ≤ n)
                         → Set
    where
  ≤-lt  : ∀ {i j-1}
        → (i≤j-1 : i ≤ j-1)
        → (j≤n : suc j-1 ≤ n)
        → ≤-Ordering  (≤-trans (≤-s i≤j-1) j≤n)
                      j≤n
  ≤-gt  : ∀ {i-1 j}
        → (i≤n : suc i-1 ≤ n)
        → (j≤i-1 : j ≤ i-1)
        → ≤-Ordering  i≤n
                      (≤-trans (≤-s j≤i-1) i≤n)
  ≤-eq  : ∀ {i}
        → (i≤n : i ≤ n)
        → ≤-Ordering  i≤n
                      i≤n

≤-compare  : ∀ {i j n}
           → (x : i ≤ n)
           → (y : j ≤ n)
           → ≤-Ordering x y
≤-compare m≤m      m≤m      = ≤-eq m≤m
≤-compare m≤m      (≤-s y)  = ≤-gt m≤m y
≤-compare (≤-s x)  m≤m      = ≤-lt x m≤m
≤-compare (≤-s x)  (≤-s y)
  with ≤-compare x y
... | ≤-lt i≤j-1 _  = ≤-lt i≤j-1 (≤-s y)
... | ≤-gt _ j≤i-1  = ≤-gt (≤-s x) j≤i-1
... | ≤-eq _        = ≤-eq (≤-s x)
\end{code}
%</leq-compare>
