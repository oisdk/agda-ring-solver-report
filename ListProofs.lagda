\begin{code}
module ListProofs where

open import Data.List as List using (List; _∷_; []; foldr)
open import Relation.Binary
import Level
open import Function

module _
 {a r b c}
 {A : Set a}
 {R : Rel A r}
 {B : Set b}
 {C : Set c}
 where

 infix 4 _≲_
 _≲_ = R

 open import Algebra.FunctionProperties _≲_
\end{code}
%<*fusion>
\begin{code}
 universal
   :  Transitive _≲_
   →  ∀ (h : List B → A) f e
   →  (∀ {x y z} → y ≲ z → f x y ≲ f x z)
   →  (h [] ≲ e)
   →  (∀ x xs → h (x ∷ xs) ≲ f x (h xs))
   →  ∀ xs → h xs ≲ foldr f e xs
 universal trans h f e resp base step [] = base
 universal trans h f e resp base step (x ∷ xs) =
   trans (step x xs) (resp (universal trans h f e resp base step xs))

 fusion
   :  Transitive  _≲_
   →  Reflexive   _≲_
   →  ∀ (f : C → A) _⊕_ (_⊗_ : B → A → A) e
   →  (∀ {x y z} → y ≲ z → x ⊗ y ≲ x ⊗ z)
   →  (∀ x y → f (x ⊕ y) ≲ x ⊗ f y)
   →  ∀ xs → f (foldr _⊕_ e xs) ≲ foldr _⊗_ (f e) xs
 fusion trans refl f _⊕_ _⊗_ e resp step =
   universal
     trans
     (f ∘ foldr _⊕_ e) _⊗_ (f e)
     resp refl (λ _ _ → step _ _)
\end{code}
%</fusion>
