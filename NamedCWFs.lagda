Here we try to define a version of CWFs that has names in it.

Modelled on Palmgren's work, from
\url{https://staff.math.su.se/palmgren/Named_variables_in_cwfs_v02.pdf}.

\begin{code}
module NamedCWFs where

open import Data.Char using (Char) -- to have 1-letter variables names...
import Data.Nat as ℕ
import Data.Fin as Fin
import Data.List as List
open import Data.List.Fresh
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; proj₁; proj₂; _,_)
open import Data.Unit using (tt)
open import Level
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Unary using (∁; Pred)
open import Relation.Binary using (Decidable; Setoid)
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_; _≢_; refl)
open import Relation.Nary using (⌊_⌋)

open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.Sets -- ?
open import Categories.Functor.Core using (Functor)
open import Categories.Object.Terminal
\end{code}

One of the first things we need is a "theory of names". We don't quite
know all we will need, so separate it out.

We definitely need a 'set' of variables. You would think that it
would need to be discrete (i.e. have decidable equality), but this in
fact is not needed anywhere in the definition of CwFN below.
\begin{code}
record Variables {v : Level} : Set (suc v) where
  field
    V : Set v

  V# : Set v
  V# = List# V _≢_
\end{code}

And now we try to define CWF.

\begin{code}
private
  variable
    o ℓ e v o′ o″ : Level

record CwFN (Var : Variables {v}) : Set (suc (v ⊔ o ⊔ ℓ ⊔ e ⊔ o′ ⊔ o″)) where
  open Setoid renaming (_≈_ to _≈S_)
  field
    C : Category o ℓ e
    T : Terminal C
  open Category C
  open Variables Var public
  open Terminal T public
  field
    names : Obj → V#
    names-⊤ : names ⊤ ≡ []
\end{code}

The variables that are free in a context are then 'easily' definable using
fresh lists:
\begin{code}
  free : Obj → Set v
  free Γ = Σ V (λ v → fresh V _≢_ v (names Γ))
\end{code}

We have types, modeled as functors into the category of ``Sets''.
\begin{code}
  field
    TyF : Functor op (Sets o′)

  open Functor TyF
\end{code}

Since we want to model context as objects of |C|, it is convenient to define
some abbreviations that make this more apparent.

\begin{code}
  Ctx : Set o
  Ctx = Obj
  Sub : Ctx → Ctx → Set ℓ
  Sub = _⇒_

  Ty : Obj → Set o′
  Ty = F₀
  _⦅_⦆ : {Γ Δ : Obj} (A : Ty Γ) (f : Sub Δ Γ) → Ty Δ
  A ⦅ f ⦆ = F₁ f A
\end{code}

And now we get to context extensions, which represent adding a new name to a context.

\begin{code}
  infixl 10 Ext
  field
    Ext : (Γ : Ctx) (A : Ty Γ) (x : free Γ) → Ctx
  syntax Ext Γ A x = Γ ∙ x ⦂ A

  field
    names-Ext : {Γ : Ctx} {x : free Γ} {A : Ty Γ} → names (Γ ∙ x ⦂ A) ≡ cons (proj₁ x) (names Γ) (proj₂ x)
\end{code}

It comes with an inverse operation, which projects out the variable.
\begin{code}
    p : {Γ : Ctx} (x : free Γ) (A : Ty Γ) → Sub (Γ ∙ x ⦂ A) Γ
\end{code}

We also have terms. We're not going to be able to have things hold definitionally, so we'll make
these into a Setoid of sorts, with a heterogeneous equality, but between convertible types,
for which we'll ask for evidence.

\begin{code}
  field
    Tm : {Γ : Ctx} (A : Ty Γ) → Set o″
  infix 4 _≋_[_]
  _≋_[_] : {Γ : Ctx} {A B : Ty Γ} → (a : Tm A) (b : Tm B) → A ≡ B → Set o″
  _≋_[_] {_} {A} a b = λ { refl → a ≡ b}
\end{code}

This lets us define term-level substitution, which is functorial.
\begin{code}
  field
    _⟦_⟧ : {Γ Δ : Obj} {A : Ty Γ} → Tm A → (f : Sub Δ Γ) → Tm (A ⦅ f ⦆)

    a⟦id⟧ : {Γ : Obj} {A : Ty Γ} {a : Tm A} → a ⟦ id ⟧ ≋ a [ identity ]
    a⟦∘⟧ : {Γ Δ Θ : Obj} {A : Ty Γ} {f : Sub Δ Γ} {g : Sub Θ Δ} {a : Tm A} →
      a ⟦ f ∘ g ⟧ ≋ a ⟦ f ⟧ ⟦ g ⟧ [ homomorphism ]
\end{code}

There is also a |var| element at each type, which basically represents a
variable of type |A|.

\begin{code}
    var : {Δ : Ctx} {A : Ty Δ} {x : free Δ} → Tm {Δ ∙ x ⦂ A} (A ⦅ p x A ⦆)
\end{code}

Then we have a means by which to extend morphisms too, by a term in context.
\begin{code}
    <_,_⦂=_> : {Γ Δ : Ctx} {A : Ty Δ} (f : Sub Γ Δ) (x : free Δ) (a : Tm (A ⦅ f ⦆)) → Sub Γ (Δ ∙ x ⦂ A)
\end{code}

It has to satisfy a number of laws.
\begin{enumerate}
\item if we extend then project out, we have not done anything.
\item substituting |< f , x ⦂= a > | in a variable is the same as |a|.
\item we can 'expand' the meaning of substitution into a context (two cases, one
  with a variable at the end of the substitution, and the general case).
  Unfortunately, the latter isn't quite 'right', it needs its type slightly adjusted.
\end{enumerate}
So, to deal with that, we introduce a generic fixer for the fact that homomorphisms of
|TyF| are not definitionally strict.
\begin{code}
  TmHom : {Γ Δ Θ : Ctx} {A : Ty Θ} {f : Sub Γ Δ} {g : Sub Δ Θ} → Tm (A ⦅ g ⦆ ⦅ f ⦆ ) → Tm (A ⦅ g ∘ f ⦆ )
  TmHom a = ≡.subst Tm (≡.sym homomorphism) a
  field
    p∘<f,->≡f : {Γ Δ : Ctx} {A : Ty Δ} {f : Sub Γ Δ} (x : free Δ) (a : Tm (A ⦅ f ⦆)) → p x A ∘ < f , x ⦂= a > ≈ f
    var∘<f,x⦂=a>≡a : {Γ Δ : Ctx} {A : Ty Δ} {f : Sub Γ Δ} (x : free Δ) (a : Tm (A ⦅ f ⦆)) →
      var ⟦ < f , x ⦂= a > ⟧ ≋ a [ ≡.trans (≡.sym homomorphism) (F-resp-≈ (p∘<f,->≡f x a)) ]
    explicit-subs-var : {Γ Δ : Ctx} {A : Ty Δ} {f : Sub Γ Δ} (x : free Δ) (h : Sub Γ (Δ ∙ x ⦂ A)) →
      < p x A ∘ h , x ⦂= TmHom (var ⟦ h ⟧) > ≈ h
    explicit-subs : {Γ Δ Θ : Ctx} {A : Ty Δ} {f : Sub Γ Δ} (x : free Δ) (a : Tm (A ⦅ f ⦆)) (g : Sub Θ Γ) →
      < f , x ⦂= a > ∘ g ≈ < f ∘ g , x ⦂= TmHom (a ⟦ g ⟧) >
\end{code}

And lastly we can define what it means to apply a substitution to an extended context.

\begin{code}
  q : {Θ Γ : Ctx} (f : Sub Θ Γ) (A : Ty Γ) (y : free Θ) (x : free Γ) → Sub (Θ ∙ y ⦂ (A ⦅ f ⦆)) (Γ ∙ x ⦂ A)
  q {Θ} {Γ} f A y x = < f ∘ p y (A ⦅ f ⦆) , x ⦂= TmHom var >
\end{code}
