{-# OPTIONS --without-K #-}

module Groupoid.Core.Base where

open import Agda.Primitive
open import Common public
import Setoid as S
open import Type as T
  using (_,_)

record t d ..(ℓᵒ ℓˢᵒ ℓˢʰ : _) : Set (lsuc (ℓᵒ ⊔ ℓˢᵒ ⊔ ℓˢʰ)) where
  no-eta-equality
  field
    obj
      : Set ℓᵒ
    homˢ
      : obj T.∐.⊗ obj T.Π.⇒₀ S.t Dir.≈ ℓˢᵒ ℓˢʰ
    idnˢ
      : ∀ {a}
      → S.𝟙.s⁰ S.Π.⇒₀ᵗ homˢ (a , a)
    cmpˢ
      : ∀ {a b c}
      → homˢ (b , c) S.∐.⊗ homˢ (a , b) S.Π.⇒₀ᵗ homˢ (a , c)
    {invˢ}
      : ∀ {a b}
      → Dir.el d T.𝟙.t (homˢ (a , b) S.Π.⇒₀ᵗ homˢ (b , a))

  private
    invˢ≡
      : ∀ {a b}
      → (ϕ : d T.≡.t S.Dir.≈)
      → homˢ (a , b) S.Π.⇒₀ᵗ homˢ (b , a)
    invˢ≡ {a}{b} ϕ =
      T.≡.subst
        (λ d′ → Dir.el d′ T.𝟙.t (homˢ (a , b) S.Π.⇒₀ᵗ homˢ (b , a))) ϕ
        invˢ

  field
    .idn-lhs
      : ∀ {a b}
      → (f : S.obj (homˢ (a , b)))
      → S.homᵗ (homˢ (a , b))
          ( cmpˢ S.Π.$₀ (idnˢ S.Π.$₀ T.𝟙.* , f)
          , f
          )
    .idn-rhs
      : ∀ {a b}
      → (f : S.obj (homˢ (a , b)))
      → S.homᵗ (homˢ (a , b))
          ( cmpˢ S.Π.$₀ (f , idnˢ S.Π.$₀ T.𝟙.*)
          , f
          )
    .cmp-ass
      : ∀ {a b c d}
      → (f : S.obj (homˢ (a , b)))
      → (g : S.obj (homˢ (b , c)))
      → (h : S.obj (homˢ (c , d)))
      → S.homᵗ (homˢ (a , d))
          ( cmpˢ S.Π.$₀ (cmpˢ S.Π.$₀ (h , g) , f)
          , cmpˢ S.Π.$₀ (h , cmpˢ S.Π.$₀ (g , f))
          )
    .{inv-lhs}
      : ∀ {a b}
      → (f : S.obj (homˢ (a , b)))
      → Dir.el {Φ = λ d′ → d T.≡.t d′ → Set _} d (T.Π.! T.𝟙.t) (λ ϕ →
          S.homᵗ (homˢ (a , a))
            ( cmpˢ S.Π.$₀ (invˢ≡ ϕ S.Π.$₀ f , f)
            , idnˢ S.Π.$₀ T.𝟙.*
            ))
        T.≡.refl
    .{inv-rhs}
      : ∀ {a b}
      → (f : S.obj (homˢ (a , b)))
      → Dir.el {Φ = λ d′ → d T.≡.t d′ → Set _} d (T.Π.! T.𝟙.t) (λ ϕ →
          S.homᵗ (homˢ (b , b))
            ( idnˢ S.Π.$₀ T.𝟙.*
            , cmpˢ S.Π.$₀ (f , invˢ≡ ϕ S.Π.$₀ f)
            ))
        T.≡.refl
open t public

module _ {d} ..{ℓᵒ ℓˢᵒ ℓˢʰ} (A : t d ℓᵒ ℓˢᵒ ℓˢʰ) where
  infixr 0 ⊢_[_∘₀_]

  hom₀ : obj A → obj A → Set _
  hom₀ a b = S.obj (homˢ A (a , b))

  hom₁ : ∀ {a b} (f g : hom₀ a b) → Set _
  hom₁ {a}{b} f g = S.homᵗ (homˢ A (a , b)) (f , g)

  idn₀ : ∀ {a} → hom₀ a a
  idn₀ {a} = idnˢ A {a} S.Π.$₀ T.𝟙.*

  cmp₀
    : ∀ {a b c}
    → hom₀ b c
    → hom₀ a b
    → hom₀ a c
  cmp₀ {a}{b}{c} g f = cmpˢ A {a}{b}{c} S.Π.$₀ (g , f)

  ⊢_[_∘₀_]
    : ∀ {a b c}
    → hom₀ b c
    → hom₀ a b
    → hom₀ a c
  ⊢_[_∘₀_] {a}{b}{c} g f = cmpˢ A {a}{b}{c} S.Π.$₀ (g , f)

inv₀
  : ∀ ..{ℓᵒ ℓˢᵒ ℓˢʰ}
  → ∀ (A : t Dir.≈ ℓᵒ ℓˢᵒ ℓˢʰ) {a b}
  → hom₀ A a b → hom₀ A b a
inv₀ A = invˢ A S.Π.$₀_

S↑G : ∀ {d} ..{ℓᵒ ℓʰ}
  → (A : S.t d ℓᵒ ℓʰ)
  → t d _ _ lzero
obj (S↑G A) =
  S.obj A
S.obj (homˢ (S↑G A) (a , b)) =
  S.homᵗ A (a , b)
S.homᵗ (homˢ (S↑G A) (a , b)) _ =
  T.𝟙.t
S.idnᵗ (homˢ (S↑G A) (a , b)) =
  _
S.cmpᵗ (homˢ (S↑G A) (a , b)) =
  _
S.invᵗ (homˢ (S↑G A) (a , b)) =
  _
S.Π._$₀_ (idnˢ (S↑G A)) =
  S.idnᵗ A
S.Π._$₁_ (idnˢ (S↑G A)) =
  _
S.Π._$₀_ (cmpˢ (S↑G A)) =
  S.cmpᵗ A
S.Π._$₁_ (cmpˢ (S↑G {ℓʰ = ℓʰ} A) ) =
  _
invˢ (S↑G {Dir.≤} A) =
  _
S.Π._$₀_ (invˢ (S↑G {Dir.≈} A)) =
  S.invᵗ A
S.Π._$₁_ (invˢ (S↑G {Dir.≈} {ℓʰ = ℓʰ} A)) =
  _
idn-lhs (S↑G A) =
  _
idn-rhs (S↑G A) =
  _
cmp-ass (S↑G A) =
  _
inv-lhs (S↑G {Dir.≤} A) =
  _
inv-lhs (S↑G {Dir.≈} A) =
  _
inv-rhs (S↑G {Dir.≤} A) =
  _
inv-rhs (S↑G {Dir.≈} A) =
  _

G↓S : ∀ {d} ..{ℓᵒ ℓˢᵒ ℓˢʰ}
  → (A : t d ℓᵒ ℓˢᵒ ℓˢʰ)
  → S.t d _ _
S.obj (G↓S A) =
  obj A
S.homᵗ (G↓S A) (a , b) =
  hom₀ A a b
S.idnᵗ (G↓S A) {a} _ =
  idn₀ A
S.cmpᵗ (G↓S A ) (g , f) =
  cmp₀ A g f
S.invᵗ (G↓S {Dir.≤} A) =
  _
S.invᵗ (G↓S {Dir.≈} A) f =
  inv₀ A f
