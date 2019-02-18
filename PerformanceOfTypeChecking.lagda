\begin{code}
module PerformanceOfTypeChecking where

open import Data.Nat hiding (_^_)
open import Relation.Binary.PropositionalEquality
open import Data.Product

Carrier : Set
Carrier = ℕ
module P where
\end{code}
%<*pow-bad>
\begin{code}
 _^_ : Carrier → ℕ → Carrier
 x ^ zero   = 1
 x ^ suc i  = x * (x ^ i)
\end{code}
%</pow-bad>
%<*pow-ident>
\begin{code}
_^_+1 : Carrier → ℕ → Carrier
x ^ zero   +1 = x
x ^ suc i  +1 = (x ^ i +1) * x

_^_ : Carrier → ℕ → Carrier
x ^ zero   = 1
x ^ suc i  = x ^ i +1
\end{code}
%</pow-ident>
\begin{code}
_*⟨_⟩^_ : Carrier → Carrier → ℕ → Carrier
ρ *⟨ xs ⟩^ zero  = xs
ρ *⟨ xs ⟩^ suc i = (ρ ^ i +1) * xs
\end{code}
%<*dense-term-small>
\begin{code}
obligation : ∀ x →
  x * (x * (x * 0 + 1) + 0) + 2 ≡
  x * (x * (x * 0 + 1) + 0) + 2
obligation _ = refl
\end{code}
%</dense-term-small>
\begin{code}
dense-term : ∀ x →
  x * (x * (x * (x * (x * (x * (x * (x * 0 + 2) + 0) + 4) + 0) + 0) + 2) + 0) + 3 ≡
\end{code}
%<*dense-term>
\begin{code}
  x *
   (x *
     (x *
       (x *
         (x *
           (x *
             (x *
               (x *
                    0
               + 2)
             + 0)
           + 4)
         + 0)
       + 0)
     + 2)
   + 0)
  + 3
\end{code}
%</dense-term>
\begin{code}
dense-term _ = refl
sparse-term : ∀ x →
  x ^ 0 * (x * (x ^ 1 * (x * (x ^ 2 * (x * (x ^ 1 * (x * 0 + 2)) + 4)) + 2)) + 3) ≡
\end{code}
%<*sparse-term>
\begin{code}
 x ^ 0 * (x *
  (x ^ 1 * (x *
    (x ^ 2 * (x *
      (x ^ 1 * (x *
        0
       + 2))
     + 4))
   + 2))
 + 3)
\end{code}
%</sparse-term>
\begin{code}
sparse-term _ = refl
module Rev where
 open import Data.List as List using (List; _∷_; []; foldr)
 open ≡-Reasoning

 Poly : Set
 Poly = List Carrier
 ⟦_⟧ᵣ : Poly → Carrier → Carrier
\end{code}
%<*backwards-eval>
\begin{code}
 ⟦ xs ⟧ᵣ ρ = foldr (λ y ys → y + ys * ρ) 0 xs
\end{code}
%</backwards-eval>
\begin{code}
 back-progress : ∀ x → ⟦ 2 ∷ 0 ∷ 1 ∷ [] ⟧ᵣ x ≡ suc (suc ((x + 0) * x))
 back-progress x = begin
\end{code}
%<*back-progress>
\begin{code}
  ⟦ 2 ∷ 0 ∷ 1 ∷ [] ⟧ᵣ x          ≡⟨⟩
  2 + (0 + (1 + 0 * x) * x) * x  ≡⟨⟩
  suc (suc ((x + 0) * x))        ∎
\end{code}
%</back-progress>
\begin{code}
module For where
 open import Data.List as List using (List; _∷_; []; foldr)
 open ≡-Reasoning
 Poly : Set
 Poly = List Carrier
 ⟦_⟧ₗ : Poly → Carrier → Carrier
\end{code}
%<*forwards-eval>
\begin{code}
 ⟦ xs ⟧ₗ ρ = foldr (λ y ys → ρ * ys + y) 0 xs
\end{code}
%</forwards-eval>
\begin{code}
 for-progress : ∀ x → ⟦ 2 ∷ 0 ∷ 1 ∷ [] ⟧ₗ x ≡ x * (x * (x * 0 + 1) + 0) + 2
 for-progress x = begin
\end{code}
%<*for-progress>
\begin{code}
  ⟦ 2 ∷ 0 ∷ 1 ∷ [] ⟧ₗ x          ≡⟨⟩
  x * (x * (x * 0 + 1) + 0) + 2  ≡⟨⟩
  x * (x * (x * 0 + 1) + 0) + 2  ∎
\end{code}
%</for-progress>
\begin{code}
\end{code}

%<*reduction>
\begin{code}
progress : ∀ x →
 2 + (0 + (1 + 0 * x) * x) * x ≡
 suc (suc ((x + 0) * x))
progress _ = refl
\end{code}
%</reduction>
%<*kleene>
\begin{code}
mutual
  data _⋆ {a} (A : Set a) : Set a where
    [] : A ⋆
    [_] : A ⁺ → A ⋆

  infixr 3 _&_
  record _⁺ {a} (A : Set a) : Set a where
    inductive
    constructor _&_
    field
      head : A
      tail : A ⋆
\end{code}
%</kleene>
%<*no-ident>
\begin{code}
Poly : Set
Poly = (Carrier × ℕ) ⋆

⟦_⟧ : Poly → Carrier → Carrier
⟦ [] ⟧ _ = 0
⟦ [ xs ] ⟧ = ⟦ xs ⟧⁺
  where
  ⟦_⟧⁺ : (Carrier × ℕ) ⁺ → Carrier → Carrier
  ⟦ x , i & [] ⟧⁺ ρ = ρ *⟨ x ⟩^ i
  ⟦ x , i & [ xs ] ⟧⁺ ρ =
    ρ *⟨ ρ * ⟦ xs ⟧⁺ ρ + x ⟩^ i

infixr 3 _∷_
pattern _∷_ x xs = [ x & xs ]
\end{code}
%</no-ident>
\begin{code}
small′ : ∀ x →
  ⟦ 3 , 0 ∷ 2 , 1 ∷ 4 , 2 ∷ 2 , 1 ∷ [] ⟧ x ≡
\end{code}
%<*small-eval>
\begin{code}
 x *⟨ x *
   (x *⟨ x *
     (x *⟨ x *
       (x *⟨ 2 ⟩^ 1)
     + 4 ⟩^ 2)
   + 2 ⟩^ 1)
 + 3 ⟩^ 0
\end{code}
%</small-eval>
\begin{code}
small′ _ = refl
\end{code}
\begin{code}
small : ∀ x → ⟦ 3 , 0 ∷ 2 , 1 ∷ 4 , 2 ∷ 2 , 1 ∷ [] ⟧ x ≡
\end{code}
%<*small-force>
\begin{code}
 x *
   (x * (x *
     ((x * x) * (x *
       (x * 2)
     + 4))
   + 2))
 + 3
\end{code}
%</small-force>
\begin{code}
small _ = refl
\end{code}
%<*syntactic>
\begin{code}
syntactic : ∀ x → 2 + x ≡ 2 + x
syntactic _ = refl
\end{code}
%</syntactic>
%<*definitional>
\begin{code}
definitional : ∀ x → 2 + x ≡ suc (suc x)
definitional _ = refl
\end{code}
%</definitional>
