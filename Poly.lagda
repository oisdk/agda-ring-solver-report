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
open import Data.List as List using (_∷_; []; List; foldr)
open import Data.Vec as Vec using (_∷_; []; Vec)
open import Data.Nat as ℕ using (ℕ; suc; zero; compare)
open import Function
open import Data.Fin as Fin using (Fin)
open import Data.Product hiding (Σ)

module Poly where

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

module Slime
  {a ℓ}
  (coeffs : RawRing a)
  (Zero-C : Pred (RawRing.Carrier coeffs) ℓ)
  (zero-c? : Decidable Zero-C)
  where
  open RawRing coeffs
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
module LEQ3 where
\end{code}
%<*leq-3>
\begin{code}
  infix 4 _≤_
  data _≤_ (m : ℕ) : ℕ → Set where
    m≤m  : m ≤ m
    ≤-s  : ∀ {n}
         → (m≤n : m ≤ n)
         → m ≤ suc n
\end{code}
%</leq-3>
%<*leq-3-cmp>
\begin{code}
  data Ordering : ℕ → ℕ → Set where
    less  : ∀ {n m}
          → n ≤ m
          → Ordering n (suc m)
    greater  : ∀ {n m}
             → m ≤ n
             → Ordering (suc n) m
    equal  : ∀ {n}
           → Ordering n n

  ≤-compare   : ∀ {i j n}
              → (i≤n : i ≤ n)
              → (j≤n : j ≤ n)
              → Ordering i j
  ≤-compare m≤m        m≤m        = equal
  ≤-compare m≤m        (≤-s m≤n)  = greater m≤n
  ≤-compare (≤-s m≤n)  m≤m        = less m≤n
  ≤-compare (≤-s i≤n)  (≤-s j≤n)  =
    ≤-compare i≤n j≤n
\end{code}
%</leq-3-cmp>
\begin{code}
open import Data.Nat using () renaming (_≤′_ to _≤_; ≤′-refl to m≤m; ≤′-step to ≤-s)
\end{code}
%<*trans>
\begin{code}
infixl 6 _⋈_
_⋈_ : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
xs ⋈ m≤m = xs
xs ⋈ (≤-s ys) = ≤-s (xs ⋈ ys)
\end{code}
%</trans>
%<*ind-ordering>
\begin{code}
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
\end{code}
%</ind-ordering>
\begin{code}
_cmp_ : ∀ {i j n}
    → (x : i ≤ n)
    → (y : j ≤ n)
    → Ordering x y
m≤m cmp m≤m = eq m≤m
m≤m cmp ≤-s y = m≤m > y
≤-s x cmp m≤m = x < m≤m
≤-s x cmp ≤-s y with x cmp y
≤-s .(≤-s i≤j-1 ⋈ y) cmp ≤-s y                | i≤j-1 < .y = i≤j-1 < ≤-s y
≤-s x                cmp ≤-s .(≤-s j≤i-1 ⋈ x) | .x > j≤i-1 = ≤-s x > j≤i-1
≤-s x                cmp ≤-s .x               | eq .x = eq (≤-s x)

z≤n : ∀ {n} → zero ≤ n
z≤n {zero} = m≤m
z≤n {suc n} = ≤-s z≤n

module SparseNesting
  {a ℓ}
  (coeffs : RawRing a)
  (Zero-C : Pred (RawRing.Carrier coeffs) ℓ)
  (zero-c? : Decidable Zero-C)
  where
  open RawRing coeffs
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
%<*flat-poly>
\begin{code}
    data FlatPoly : ℕ → Set (a ⊔ ℓ) where
      Κ  : Carrier → FlatPoly zero
      Σ  : ∀ {n}
         → (xs : Coeffs n)
         → .{xn : Norm xs}
         → FlatPoly (suc n)
\end{code}
%</flat-poly>
%<*poly-types>
\begin{code}
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
    Zero (Κ x        Π _) = Zero-C x
    Zero (Σ []       Π _) = Lift ℓ ⊤
    Zero (Σ (_ ∷ _)  Π _) = Lift ℓ ⊥
\end{code}
%</poly-types>
%<*poly-norm>
\begin{code}
    Norm : ∀ {i} → Coeffs i → Set
    Norm []                    = ⊥
    Norm (_ Δ zero   ∷ [])     = ⊥
    Norm (_ Δ zero   ∷ _ ∷ _)  = ⊤
    Norm (_ Δ suc _  ∷ _)      = ⊤
\end{code}
%</poly-norm>
\begin{code}
  zero? : ∀ {n} → (p : Poly n) → Dec (Zero p)
  zero? (Κ x       Π _) = zero-c? x
  zero? (Σ []      Π _) = yes (lift tt)
  zero? (Σ (_ ∷ _) Π _) = no lower

  infixr 8 _⍓_
  _⍓_ : ∀ {n} → Coeffs n → ℕ → Coeffs n
  [] ⍓ i = []
  (x Δ j ∷ xs) ⍓ i = x Δ (j ℕ.+ i) ∷ xs

  infixr 5 _^_∷↓_
  _^_∷↓_ : ∀ {n} → Poly n → ℕ → Coeffs n → Coeffs n
  x ^ i ∷↓ xs with zero? x
  ... | yes p = xs ⍓ suc i
  ... | no ¬p = _≠0 x {¬p} Δ i ∷ xs
\end{code}
%<*poly-norm-inj>
\begin{code}
  _Π↑_ : ∀ {n m} → Poly n → (suc n ≤ m) → Poly m
  (xs Π i≤n) Π↑ n≤m = xs Π (≤-s i≤n ⋈ n≤m)

  infixr 4 _Π↓_
  _Π↓_ : ∀ {i n} → Coeffs i → suc i ≤ n → Poly n
  []                         Π↓ i≤n = Κ 0#                     Π   z≤n
  (x ≠0 Δ zero   ∷ [])       Π↓ i≤n = x                        Π↑  i≤n
  (x₁   Δ zero   ∷ x₂ ∷ xs)  Π↓ i≤n = Σ (x₁ Δ zero ∷ x₂ ∷ xs)  Π   i≤n
  (x    Δ suc j  ∷ xs)       Π↓ i≤n = Σ (x Δ suc j ∷ xs)       Π   i≤n
\end{code}
%</poly-norm-inj>
\begin{code}
  module Neg1 where
\end{code}
%<*nonterminating-negation>
\begin{code}
    {-# TERMINATING #-}
    mutual
      ⊟_ : ∀ {n} → Poly n → Poly n
      ⊟ (Κ x  Π i≤n) = Κ (- x) Π i≤n
      ⊟ (Σ xs Π i≤n) =
        foldr ⊟-cons [] xs Π↓ i≤n

      ⊟-cons : ∀ {n}
            → CoeffExp n
            → Coeffs n
            → Coeffs n
      ⊟-cons (x ≠0 Δ i) xs =
        ⊟ x ^ i ∷↓ xs
\end{code}
%</nonterminating-negation>
\begin{code}
  module Neg2 where
\end{code}
%<*no-higher-order>
\begin{code}
    mutual
      ⊟_ : ∀ {n} → Poly n → Poly n
      ⊟ (Κ x  Π i≤n) = Κ (- x) Π i≤n
      ⊟ (Σ xs Π i≤n) = ⊟-cons xs Π↓ i≤n

      ⊟-cons : ∀ {n}
             → Coeffs n
             → Coeffs n
      ⊟-cons [] = []
      ⊟-cons (x ≠0 Δ i ∷ xs) =
        ⊟ x ^ i ∷↓ ⊟-cons xs
\end{code}
%</no-higher-order>
\begin{code}
  module Neg3 where
\end{code}
%<*with-acc>
\begin{code}
  open import Induction.Nat
  open import Induction.WellFounded

  ⌊_⌋ : ℕ → Set
  ⌊_⌋ = Acc ℕ._<′_

  ⌊↓⌋ : ∀ {n} → ⌊ n ⌋
  ⌊↓⌋ {n} = <′-wellFounded n

  mutual
    ⊟-step : ∀ {n} → ⌊ n ⌋ → Poly n → Poly n
    ⊟-step _         (Κ x   Π i≤n) = Κ (- x) Π i≤n
    ⊟-step (acc wf)  (Σ xs  Π i≤n) =
      foldr (⊟-cons (wf _ i≤n)) [] xs Π↓ i≤n

    ⊟-cons : ∀ {n}
           → ⌊ n ⌋
           → CoeffExp n
           → Coeffs n
           → Coeffs n
    ⊟-cons ac (x ≠0 Δ i) xs =
      ⊟-step ac x ^ i ∷↓ xs

  ⊟_ : ∀ {n} → Poly n → Poly n
  ⊟_ = ⊟-step ⌊↓⌋
\end{code}
%</with-acc>
\begin{code}
  mutual
    infixl 6 _⊞_
    _⊞_ : ∀ {n} → Poly n → Poly n → Poly n
    (xs Π i≤n) ⊞ (ys Π j≤n) = ⊞-match (i≤n cmp j≤n) xs ys

    ⊞-match : ∀ {i j n}
          → {i≤n : i ≤ n}
          → {j≤n : j ≤ n}
          → Ordering i≤n j≤n
          → FlatPoly i
          → FlatPoly j
          → Poly n
    ⊞-match (eq i&j≤n)    (Κ x)  (Κ y)  = Κ (x + y)         Π  i&j≤n
    ⊞-match (eq i&j≤n)    (Σ xs) (Σ ys) = ⊞-coeffs    xs ys Π↓ i&j≤n
    ⊞-match (i≤j-1 < j≤n)  xs    (Σ ys) = ⊞-inj i≤j-1 xs ys Π↓ j≤n
    ⊞-match (i≤n > j≤i-1) (Σ xs)  ys    = ⊞-inj j≤i-1 ys xs Π↓ i≤n

    ⊞-inj : ∀ {i k}
        → (i ≤ k)
        → FlatPoly i
        → Coeffs k
        → Coeffs k
    ⊞-inj i≤k xs [] = xs Π i≤k ^ zero ∷↓ []
    ⊞-inj i≤k xs (y Π j≤k ≠0 Δ zero ∷ ys) =
      ⊞-match (j≤k cmp i≤k) y xs ^ zero ∷↓ ys
    ⊞-inj i≤k xs (y Δ suc j ∷ ys) =
      xs Π i≤k ^ zero ∷↓ y Δ j ∷ ys

    ⊞-coeffs : ∀ {n} → Coeffs n → Coeffs n → Coeffs n
    ⊞-coeffs [] ys = ys
    ⊞-coeffs (x Δ i ∷ xs) = ⊞-zip-r x i xs

    ⊞-zip : ∀ {p q n}
          → ℕ.Ordering p q
          → Coeff n
          → Coeffs n
          → Coeff n
          → Coeffs n
          → Coeffs n
    ⊞-zip (ℕ.less    i k) x xs y ys = x Δ i ∷ ⊞-zip-r y k ys xs
    ⊞-zip (ℕ.greater j k) x xs y ys = y Δ j ∷ ⊞-zip-r x k xs ys
    ⊞-zip (ℕ.equal   i  ) (x ≠0) xs (y ≠0) ys =
      (x ⊞ y) ^ i ∷↓ ⊞-coeffs xs ys

    ⊞-zip-r : ∀ {n} → Coeff n → ℕ → Coeffs n → Coeffs n → Coeffs n
    ⊞-zip-r x i xs [] = x Δ i ∷ xs
    ⊞-zip-r x i xs (y Δ j ∷ ys) = ⊞-zip (compare i j) x xs y ys
\end{code}
%<*poly-mult>
\begin{code}
  mutual
    infixl 7 _⊠_
    _⊠_ : ∀ {n}
        → Poly n
        → Poly n
        → Poly n
    (xs Π i≤n) ⊠ (ys Π j≤n) =
      ⊠-match (i≤n cmp j≤n) xs ys

    ⊠-inj : ∀ {i k}
          → i ≤ k
          → FlatPoly i
          → Coeffs k
          → Coeffs k
    ⊠-inj _ _ [] = []
    ⊠-inj i≤k x (y Π j≤k ≠0 Δ p ∷ ys) =
      ⊠-match (i≤k cmp j≤k) x y ^ p ∷↓
        ⊠-inj i≤k x ys

    ⊠-match : ∀ {i j n}
            → {i≤n : i ≤ n}
            → {j≤n : j ≤ n}
            → Ordering i≤n j≤n
            → FlatPoly i
            → FlatPoly j
            → Poly n
    ⊠-match (eq i&j≤n)     (Κ x)   (Κ y)   = Κ (x * y)          Π   i&j≤n
    ⊠-match (eq i&j≤n)     (Σ xs)  (Σ ys)  = ⊠-coeffs xs ys     Π↓  i&j≤n
    ⊠-match (i≤j-1 < j≤n)  xs      (Σ ys)  = ⊠-inj i≤j-1 xs ys  Π↓  j≤n
    ⊠-match (i≤n > j≤i-1)  (Σ xs)  ys      = ⊠-inj j≤i-1 ys xs  Π↓  i≤n

    ⊠-coeffs : ∀ {n}
             → Coeffs n
             → Coeffs n
             → Coeffs n
    ⊠-coeffs _ [] = []
    ⊠-coeffs xs (y ≠0 Δ j ∷ ys) = ⊠-step y ys xs ⍓ j

    ⊠-step : ∀ {n}
           → Poly n
           → Coeffs n
           → Coeffs n
           → Coeffs n
    ⊠-step y ys [] = []
    ⊠-step y ys (x Π j≤n ≠0 Δ i ∷ xs) =
      (x Π j≤n) ⊠ y ^ i ∷↓
        ⊞-coeffs (⊠-inj j≤n x ys) (⊠-step y ys xs)
\end{code}
%</poly-mult>
%<*poly-fold>
\begin{code}
  PolyF : ℕ → Set (a ⊔ ℓ)
  PolyF i = Poly i × Coeffs i

  Fold : ℕ → Set (a ⊔ ℓ)
  Fold i = PolyF i → PolyF i
\end{code}
%</poly-fold>
%<*run-fold>
\begin{code}
  fold : ∀ {i} → Fold i → Coeffs i → Coeffs i
  fold f =
    foldr (λ { (x ≠0 Δ i) →
                  uncurry (λ y ys → y ^ i ∷↓ ys) ∘
                  curry f x
              }) []
\end{code}
%</run-fold>
%<*semantics-opening>
\begin{code}
module Semantics
  {r₁ r₂ r₃ r₄}
  (coeffs : RawRing r₁)
  (Zero : Pred (RawRing.Carrier coeffs) r₂)
  (zero? : Decidable Zero)
  (ring : AlmostCommutativeRing r₃ r₄)
  (morphism :
    coeffs -Raw-AlmostCommutative⟶ ring)
  where

  open AlmostCommutativeRing ring
  open SparseNesting coeffs Zero zero?
  open _-Raw-AlmostCommutative⟶_
    morphism
    using ()
    renaming (⟦_⟧ to ⟦_⟧ᵣ)
\end{code}
%</semantics-opening>
%<*semantics>
\begin{code}
  infixr 8 _^_
  _^_ : Carrier → ℕ → Carrier
  x ^ zero = 1#
  x ^ suc n = x * x ^ n

  drop : ∀ {i n}
       → i ≤ n
       → Vec Carrier n
       → Vec Carrier i
  drop m≤m Ρ = Ρ
  drop (≤-s si≤n) (_ ∷ Ρ) = drop si≤n Ρ

  vec-uncons : ∀ {n}
             → Vec Carrier (suc n)
             → Carrier × Vec Carrier n
  vec-uncons (x ∷ xs) = x , xs

  drop-1 : ∀ {i n}
         → suc i ≤ n
         → Vec Carrier n
         → Carrier × Vec Carrier i
  drop-1 si≤n xs = vec-uncons (drop si≤n xs)

  mutual
    Σ⟦_⟧ : ∀ {n}
        → Coeffs n
        → Carrier × Vec Carrier n
        → Carrier
    Σ⟦ [] ⟧ _ = 0#
    Σ⟦ x ≠0 Δ i ∷ xs ⟧ (ρ , Ρ) =
      (⟦ x ⟧ Ρ + Σ⟦ xs ⟧ (ρ , Ρ) * ρ) * ρ ^ i

    ⟦_⟧ : ∀ {n}
        → Poly n
        → Vec Carrier n
        → Carrier
    ⟦ Κ x   Π i≤n ⟧ _  = ⟦ x ⟧ᵣ
    ⟦ Σ xs  Π i≤n ⟧ Ρ  = Σ⟦ xs ⟧ (drop-1 i≤n Ρ)
\end{code}
%</semantics>
%<*aopa>
\begin{code}
foldR : ∀ {a b r}
          {A : Set a}
          {B : Set b}
      → (_R_ : B → List A → Set r)
      → {f : A → B → B}
      → {b : B}
      → (∀ y {ys zs}
         → ys R zs
         → f y ys R (y ∷ zs))
      → b R []
      → ∀ xs
      → foldr f b xs R xs
foldR _ f b [] = b
foldR P f b (x ∷ xs) = f x (foldR P f b xs)
\end{code}
%</aopa>
%<*acc-def>
\begin{code}
data Acc {a ℓ}
         {A : Set a}
         (_<_ : Rel A ℓ)
         (x : A) : Set (a ⊔ ℓ) where
  acc : (∀ y → y < x → Acc _<_ y)
      → Acc _<_ x
\end{code}
%</acc-def>
