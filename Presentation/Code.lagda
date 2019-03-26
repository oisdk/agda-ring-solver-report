\begin{code}
module Presentation.Code where
open import Data.List as List using (List; _∷_; []; _++_)
\end{code}
%<*reverse>
\begin{code}
reverse : ∀ {a} {A : Set a} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ x ∷ []

\end{code}
%</reverse>
