\begin{code}
module Binary where
open import Data.List as List using (List; []; _∷_; foldr)
open import Data.Nat as ℕ using (ℕ; zero; suc; compare; Ordering; less; equal; greater)
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
\end{code}
%<*binary-def>
\begin{code}
Bin : Set
Bin = List ℕ
\end{code}
%</binary-def>
\begin{code}
incr′ : ℕ → Bin → Bin
incr″ : ℕ → ℕ → Bin → Bin

incr′ i [] = i ∷ []
incr′ i (x ∷ xs) = incr″ i x xs

incr″ i zero xs = incr′ (suc i) xs
incr″ i (suc x) xs = i ∷ x ∷ xs

incr : Bin → Bin
incr = incr′ 0

infixl 6 _+_
_+_ : Bin → Bin → Bin
[] + ys = ys
(x ∷ xs) + ys = +-zip-r x xs ys
  where
  +-zip   :     ∀ {x y} → Ordering x y → Bin → Bin → Bin
  ∔-zip   : ℕ → ∀ {i j} → Ordering i j → Bin → Bin → Bin
  +-zip-r :     ℕ → Bin → Bin → Bin
  ∔-zip-r : ℕ → ℕ → Bin → Bin → Bin
  ∔-cin   : ℕ → Bin → Bin → Bin
  ∔-zip-c : ℕ → ℕ → ℕ → Bin → Bin → Bin

  +-zip (less    i k) xs ys = i ∷ +-zip-r k ys xs
  +-zip (equal   k  ) xs ys = ∔-cin (suc k) xs ys
  +-zip (greater j k) xs ys = j ∷ +-zip-r k xs ys

  +-zip-r x xs [] = x ∷ xs
  +-zip-r x xs (y ∷ ys) = +-zip (compare x y) xs ys

  ∔-cin i [] = incr′ i
  ∔-cin i (x ∷ xs) = ∔-zip-r i x xs

  ∔-zip-r i x xs [] = incr″ i x xs
  ∔-zip-r i x xs (y ∷ ys) = ∔-zip i (compare y x) ys xs

  ∔-zip-c c zero k xs ys = ∔-zip-r (suc c) k xs ys
  ∔-zip-c c (suc i) k xs ys = c ∷ i ∷ +-zip-r k xs ys

  ∔-zip c (less    i k) xs ys = ∔-zip-c c i k ys xs
  ∔-zip c (greater j k) xs ys = ∔-zip-c c j k xs ys
  ∔-zip c (equal     k) xs ys = c ∷ ∔-cin k xs ys
\end{code}
%<*binary-mul>
\begin{code}
pow : ℕ → Bin → Bin
pow i [] = []
pow i (x ∷ xs) = (x ℕ.+ i) ∷ xs

infixl 7 _*_
_*_ : Bin → Bin → Bin
_*_ [] _ = []
_*_ (x ∷ xs) =
  pow x ∘ foldr (λ y ys → y ∷ xs + ys) []
\end{code}
%</binary-mul>
