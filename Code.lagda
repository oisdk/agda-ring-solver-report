\begin{code}
module Code where
module Mul where
  open import Data.List as List using (List; []; _∷_; foldr; [_])
  open import Data.Product
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
