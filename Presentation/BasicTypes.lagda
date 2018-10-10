\begin{code}
module Presentation.BasicTypes where

open import Data.Nat
\end{code}
%<*xint>
\begin{code}
x : ℕ
\end{code}
%</xint>
%<*xprf>
\begin{code}
x = 1
\end{code}
%</xprf>
\begin{code}
open import Data.List
head-type : Set₁
head-type =
\end{code}
%<*headty>
\begin{code}
  {A : Set} → List A → A
\end{code}
%</headty>
