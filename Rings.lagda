\begin{code}
module Rings where
open import Relation.Unary
open import Level using (_⊔_)
open import Relation.Nullary
open import Data.List as List using (List; _∷_; []; map)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
\end{code}
%<*dense-opening>
\begin{code}
open import Algebra

module Dense {ℓ} (coeff : RawRing ℓ) where
  open RawRing coeff
\end{code}
%</dense-opening>
%<*dense-impl>
\begin{code}

  Poly : Set ℓ
  Poly = List Carrier

  _⊞_ : Poly → Poly → Poly
  [] ⊞ ys = ys
  (x ∷ xs) ⊞ [] = x ∷ xs
  (x ∷ xs) ⊞ (y ∷ ys) = x + y ∷ xs ⊞ ys

  _⊠_ : Poly → Poly → Poly
  [] ⊠ ys = []
  (x ∷ xs) ⊠ [] = []
  (x ∷ xs) ⊠ (y ∷ ys) =
    x * y ∷ (map (x *_) ys ⊞ (xs ⊠ (y ∷ ys)))
\end{code}
%</dense-impl>
\begin{code}
module UnsafeCompare where
  open import Agda.Builtin.Nat using (_<_; _-_; _+_; _==_)
  open import Data.Nat using (Ordering; less; equal; greater)
  open import Relation.Binary.PropositionalEquality
  open import Relation.Binary.PropositionalEquality.TrustMe
  open import Data.Bool
\end{code}
%<*unsafe-compare>
\begin{code}
  less-hom  : ∀ n m
            → ((n < m) ≡ true)
            → m ≡ suc (n + (m - n - 1))
  less-hom zero zero ()
  less-hom zero (suc m) _ = refl
  less-hom (suc n) zero ()
  less-hom (suc n) (suc m) n<m =
    cong suc (less-hom n m n<m)

  eq-hom  : ∀ n m
          → ((n == m) ≡ true)
          → n ≡ m
  eq-hom zero zero _ = refl
  eq-hom zero (suc m) ()
  eq-hom (suc n) zero ()
  eq-hom (suc n) (suc m) n≡m =
    cong suc (eq-hom n m n≡m)

  gt-hom  : ∀ n m
          → ((n < m) ≡ false)
          → ((n == m) ≡ false)
          → n ≡ suc (m + (n - m - 1))
  gt-hom zero zero n<m ()
  gt-hom zero (suc m) () n≡m
  gt-hom (suc n) zero n<m n≡m = refl
  gt-hom (suc n) (suc m) n<m n≡m =
    cong suc (gt-hom n m n<m n≡m)

  compare : (n m : ℕ) → Ordering n m
  compare n m with n < m  | inspect (_<_ n) m
  ... | true   | [ n<m ]
    rewrite erase (less-hom n m n<m) =
      less n (m - n - 1)
  ... | false  | [ n≮m ]
    with n == m | inspect (_==_ n) m
  ... | true   | [ n≡m ]
    rewrite erase (eq-hom n m n≡m) =
      equal m
  ... | false  | [ n≢m ]
    rewrite erase (gt-hom n m n≮m n≢m) =
      greater m (n - m - 1)
\end{code}
%</unsafe-compare>
%<*compare>
\begin{code}
data Ordering : ℕ → ℕ → Set where
  less     : ∀ m k
           → Ordering m (suc (m ℕ.+ k))
  equal    : ∀ m
           → Ordering m m
  greater  : ∀ m k
           → Ordering (suc (m ℕ.+ k)) m

compare : ∀ m n → Ordering m n
compare zero     zero     = equal zero
compare (suc m)  zero     = greater zero m
compare zero     (suc n)  = less zero n
compare (suc m)  (suc n) with compare m n
compare (suc .m) (suc .(suc m ℕ.+ k))
  | less m k = less (suc m) k
compare (suc .m) (suc .m)
  | equal m = equal (suc m)
compare (suc .(suc m ℕ.+ k)) (suc .m)
  | greater m k = greater (suc m) k
\end{code}
%</compare>
%<*sparse-opening>
\begin{code}
module Sparse
  {a ℓ}
  (coeffs : RawRing a)
  (Zero : Pred (RawRing.Carrier coeffs) ℓ)
  (zero? : Decidable Zero)
  where
  open RawRing coeffs
\end{code}
%</sparse-opening>
%<*sparse-decl>
\begin{code}
  infixl 6 _≠0
  record Coeff : Set (a ⊔ ℓ) where
    inductive
    constructor _≠0
    field
      coeff : Carrier
      .{coeff≠0} : ¬ Zero coeff
  open Coeff

  Poly : Set (a ⊔ ℓ)
  Poly = List (Coeff × ℕ)
\end{code}
%</sparse-decl>
%<*sparse-norm>
\begin{code}
  infixr 8 _⍓_
  _⍓_ : Poly → ℕ → Poly
  [] ⍓ i = []
  ((x , j) ∷ xs) ⍓ i = (x , j ℕ.+ i) ∷ xs

  infixr 5 _∷↓_
  _∷↓_ : Carrier × ℕ → Poly → Poly
  (x , i) ∷↓ xs with zero? x
  ... | yes p = xs ⍓ suc i
  ... | no ¬p = (_≠0 x {¬p} , i) ∷ xs
\end{code}
%</sparse-norm>
\begin{code}
  module NonTerminating where
\end{code}
%<*nonterminating-addition>
\begin{code}
    {-# NON_TERMINATING #-}
    _⊞_ : Poly → Poly → Poly
    [] ⊞ ys = ys
    (x ∷ xs) ⊞ [] = x ∷ xs
    ((x , i) ∷ xs) ⊞ ((y , j) ∷ ys) with compare i j
    ... | less .i k = (x , i) ∷ xs ⊞ ((y , k) ∷ ys)
    ... | greater .j k = (y , j) ∷ ((x , k) ∷ xs) ⊞ ys
    ... | equal .i =
      (coeff x + coeff y , i) ∷↓ (xs ⊞ ys)
\end{code}
%</nonterminating-addition>
%<*addition>
\begin{code}
  mutual
    infixl 6 _⊞_
    _⊞_ : Poly → Poly → Poly
    [] ⊞ ys = ys
    ((x , i) ∷ xs) ⊞ ys = ⊞-zip-r x i xs ys

    ⊞-zip-r : Coeff → ℕ → Poly → Poly → Poly
    ⊞-zip-r x i xs [] = (x , i) ∷ xs
    ⊞-zip-r x i xs ((y , j) ∷ ys) =
      ⊞-zip (compare i j) x xs y ys

    ⊞-zip : ∀ {p q}
          → Ordering p q
          → Coeff
          → Poly
          → Coeff
          → Poly
          → Poly
    ⊞-zip (less i k) x xs y ys =
      (x , i) ∷ ⊞-zip-r y k ys xs
    ⊞-zip (greater j k) x xs y ys =
      (y , j) ∷ ⊞-zip-r x k xs ys
    ⊞-zip (equal i) x xs y ys =
      (coeff x + coeff y , i) ∷↓ (xs ⊞ ys)
\end{code}
%</addition>
