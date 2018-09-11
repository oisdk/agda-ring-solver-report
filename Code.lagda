\begin{code}
module Code where
module OnLists where
  open import Data.List as List using (List; []; _∷_; foldr; [_]; map)
  open import Data.Product using (_×_; _,_)
  open import Function
\end{code}

%<*times>
\begin{code}
  conv : {A B : Set} → List A → List B → List (List (A × B))
  conv _ [] = []
  conv {A} {B} xs (yh ∷ ys) = foldr f [] xs
    where
    g  : A
       → B
       → (List (List (A × B)) → List (List (A × B)))
       → List (List (A × B))
       → List (List (A × B))
    g x y a (z ∷ zs) = ((x , y) ∷ z) ∷ a zs
    g x y a [] = [(x , y)] ∷ a []
    f : A → List (List (A × B)) → List (List (A × B))
    f x zs = [ x , yh ] ∷ foldr (g x) id ys zs
\end{code}
%</times>

%<*add>
\begin{code}
  add : ∀ {A : Set} → List A → List A → List (List A)
  add [] ys = map [_] ys
  add (x ∷ xs) [] = [ x ] ∷ map [_] xs
  add (x ∷ xs) (y ∷ ys) = (x ∷ y ∷ []) ∷ add xs ys
\end{code}
%</add>
\begin{code}
module ListDef where
  open import Relation.Binary.PropositionalEquality
  open import Algebra
  open import Level using (0ℓ)
  open Monoid {{...}} public hiding (refl)
\end{code}

%<*list>
\begin{code}
  infixr 5 _∷_
  data List (A : Set) : Set where
    []   : List A
    _∷_  : A → List A → List A
\end{code}
%</list>

%<*list-add>
\begin{code}
  infixr 5 _++_
  _++_ : ∀ {A} → List A → List A → List A
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)
\end{code}
%</list-add>

%<*list-nil>
\begin{code}
  lzero : ∀ {A} (xs : List A) → [] ++ xs ≡ xs
  lzero _ = refl

  rzero : ∀ {A} (xs : List A) → xs ++ [] ≡ xs
  rzero [] = refl
  rzero (x ∷ xs) = cong (x ∷_) (rzero xs)
\end{code}
%</list-nil>

%<*list-homo>
\begin{code}
  η : ∀ {A} → A → List A
  η x = x ∷ []

  μ : {{_ : Monoid 0ℓ 0ℓ}} → List Carrier → Carrier
  μ [] = ε
  μ (x ∷ xs) = x ∙ μ xs
\end{code}
%</list-homo>
\begin{code}
module Equality where
  open import Relation.Binary.PropositionalEquality
  open import Data.Nat using (ℕ; zero; suc)
\end{code}

%<*nat-plus>
\begin{code}
  _+_ : ℕ → ℕ → ℕ
  zero + y = y
  suc x + y = suc (x + y)
\end{code}
%</nat-plus>
%<*nat-plus-proof>
\begin{code}
  +-identityˡ : ∀ x → 0 + x ≡ x
  +-identityˡ _ = refl

  +-identityʳ : ∀ x → x + 0 ≡ x
  +-identityʳ zero = refl
  +-identityʳ (suc x) = cong suc (+-identityʳ x)
\end{code}
%</nat-plus-proof>
\begin{code}
import Algebra
module ComplexProp {ℓ₁ ℓ₂} (monoid : Algebra.Monoid ℓ₁ ℓ₂) where
  open Algebra.Monoid monoid
  open import Function
\end{code}
%<*complex-prop>
\begin{code}
  prop : ∀ w x y z →  w ∙ (((x ∙ ε) ∙ y) ∙ z) ≈ (w ∙ x) ∙ (y ∙ z)
\end{code}
%</complex-prop>
%<*complex-proof>
\begin{code}
  prop w x y z =
    (refl ⟨ ∙-cong ⟩ assoc (x ∙ ε) y z)
      ⟨ trans ⟩
    (sym (assoc w (x ∙ ε) (y ∙ z)))
      ⟨ trans ⟩
    (refl ⟨ ∙-cong ⟩ identityʳ x ⟨ ∙-cong ⟩ refl)
\end{code}
%</complex-proof>

\begin{code}
module ListProof where
  open ListDef
  open import Relation.Binary.PropositionalEquality
\end{code}
%<*list-proof-obvious>
\begin{code}
  prop : ∀ {A} {w x y z : A}
       →  η w ++ (((η x ++ []) ++ η y) ++ η z)
       ≡ (η w ++ η x) ++ (η y ++ η z)
  prop = refl
\end{code}
%</list-proof-obvious>
