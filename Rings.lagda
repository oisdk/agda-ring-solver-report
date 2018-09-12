\begin{code}
module Rings where
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
    open import Data.List as List
      using (List; _∷_; []; map)

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
