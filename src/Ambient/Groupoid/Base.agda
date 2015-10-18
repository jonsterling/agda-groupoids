{-# OPTIONS --without-K #-}

module Ambient.Groupoid.Base where

open import Agda.Primitive
open import Common public
import Setoid as S
open import Type as T

record 𝔊₂,₀ d ..(ℓᵒ ℓˢᵒ ℓˢʰ : _) : Set (lsuc (ℓᵒ ⊔ ℓˢᵒ ⊔ ℓˢʰ)) where
  no-eta-equality
  field
    obj
      : Set ℓᵒ
    homˢ
      : obj ×₀ obj ⇒₀,₀ S.𝔊₁ Dir.≈ ℓˢᵒ ℓˢʰ
    idnˢ
      : ∀ {a}
      → S.𝟙.s⁰ S.Map.⇒₀ᵗ homˢ (a , a)
    cmpˢ
      : ∀ {a b c}
      → homˢ (b , c) S.Ten.⊗ homˢ (a , b) S.Map.⇒₀ᵗ homˢ (a , c)
    {invˢ}
      : ∀ {a b}
      → Dir.el d 𝟙₀ (homˢ (a , b) S.Map.⇒₀ᵗ homˢ (b , a))

  private
    invˢ≡
      : ∀ {a b}
      → (ϕ : d T.≡₀ S.Dir.≈)
      → homˢ (a , b) S.Map.⇒₀ᵗ homˢ (b , a)
    invˢ≡ {a}{b} ϕ =
      ≡₀.subst
        (λ d′ → Dir.el d′ 𝟙₀ (homˢ (a , b) S.Map.⇒₀ᵗ homˢ (b , a))) ϕ
        invˢ

  field
    .idn-lhs
      : ∀ {a b}
      → (f : S.cell₀ (homˢ (a , b)))
      → S.cell₁ (homˢ (a , b))
          ( cmpˢ S.Map.$₀ (idnˢ S.Map.$₀ * , f)
          , f
          )
    .idn-rhs
      : ∀ {a b}
      → (f : S.cell₀ (homˢ (a , b)))
      → S.cell₁ (homˢ (a , b))
          ( cmpˢ S.Map.$₀ (f , idnˢ S.Map.$₀ *)
          , f
          )
    .cmp-ass
      : ∀ {a b c d}
      → (f : S.cell₀ (homˢ (a , b)))
      → (g : S.cell₀ (homˢ (b , c)))
      → (h : S.cell₀ (homˢ (c , d)))
      → S.cell₁ (homˢ (a , d))
          ( cmpˢ S.Map.$₀ (cmpˢ S.Map.$₀ (h , g) , f)
          , cmpˢ S.Map.$₀ (h , cmpˢ S.Map.$₀ (g , f))
          )
    .{inv-lhs}
      : ∀ {a b}
      → (f : S.cell₀ (homˢ (a , b)))
      → Dir.el {Φ = λ d′ → d T.≡₀ d′ → Set _} d (⇒₀.elm₀ 𝟙₀) (λ ϕ →
          S.cell₁ (homˢ (a , a))
            ( cmpˢ S.Map.$₀ (invˢ≡ ϕ S.Map.$₀ f , f)
            , idnˢ S.Map.$₀ *
            ))
        ≡₀.refl
    .{inv-rhs}
      : ∀ {a b}
      → (f : S.cell₀ (homˢ (a , b)))
      → Dir.el {Φ = λ d′ → d T.≡₀ d′ → Set _} d (⇒₀.elm₀ 𝟙₀) (λ ϕ →
          S.cell₁ (homˢ (b , b))
            ( idnˢ S.Map.$₀ *
            , cmpˢ S.Map.$₀ (f , invˢ≡ ϕ S.Map.$₀ f)
            ))
        ≡₀.refl
open 𝔊₂,₀ public

module _ {d} ..{ℓᵒ ℓˢᵒ ℓˢʰ}
  (A : 𝔊₂,₀ d ℓᵒ ℓˢᵒ ℓˢʰ)
  where

  infixr 0 ⊢_[_∘₀_]

  hom₀ : obj A → obj A → Set _
  hom₀ a b = S.cell₀ (homˢ A (a , b))

  hom₁ : ∀ {a b} (f g : hom₀ a b) → Set _
  hom₁ {a}{b} f g = S.cell₁ (homˢ A (a , b)) (f , g)

  idn₀ : ∀ {a} → hom₀ a a
  idn₀ {a} = idnˢ A {a} S.Map.$₀ *

  cmp₀
    : ∀ {a b c}
    → hom₀ b c
    → hom₀ a b
    → hom₀ a c
  cmp₀ {a}{b}{c} g f = cmpˢ A {a}{b}{c} S.Map.$₀ (g , f)

  ⊢_[_∘₀_]
    : ∀ {a b c}
    → hom₀ b c
    → hom₀ a b
    → hom₀ a c
  ⊢_[_∘₀_] {a}{b}{c} g f = cmpˢ A {a}{b}{c} S.Map.$₀ (g , f)

inv₀
  : ∀ ..{ℓᵒ ℓˢᵒ ℓˢʰ}
  → ∀ (A : 𝔊₂,₀ Dir.≈ ℓᵒ ℓˢᵒ ℓˢʰ) {a b}
  → hom₀ A a b → hom₀ A b a
inv₀ A = invˢ A S.Map.$₀_

S↑G : ∀ {d} ..{ℓᵒ ℓʰ}
  → (A : S.𝔊₁ d ℓᵒ ℓʰ)
  → 𝔊₂,₀ d _ _ lzero
obj (S↑G A) =
  S.cell₀ A
S.cell₀ (homˢ (S↑G A) (a , b)) =
  S.cell₁ A (a , b)
S.cell₁ (homˢ (S↑G A) (a , b)) _ =
  𝟙₀
S.idn (homˢ (S↑G A) (a , b)) =
  _
S.cmp (homˢ (S↑G A) (a , b)) =
  _
S.inv (homˢ (S↑G A) (a , b)) =
  _
S.Map._$₀_ (idnˢ (S↑G A)) =
  S.idn A
S.Map._$₁_ (idnˢ (S↑G A)) =
  _
S.Map._$₀_ (cmpˢ (S↑G A)) =
  S.cmp A
S.Map._$₁_ (cmpˢ (S↑G {ℓʰ = ℓʰ} A) ) =
  _
invˢ (S↑G {Dir.≤} A) =
  _
S.Map._$₀_ (invˢ (S↑G {Dir.≈} A)) =
  S.inv A
S.Map._$₁_ (invˢ (S↑G {Dir.≈} {ℓʰ = ℓʰ} A)) =
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
  → (A : 𝔊₂,₀ d ℓᵒ ℓˢᵒ ℓˢʰ)
  → S.𝔊₁ d _ _
S.cell₀ (G↓S A) =
  obj A
S.cell₁ (G↓S A) (a , b) =
  hom₀ A a b
S.idn (G↓S A) {a} _ =
  idn₀ A
S.cmp (G↓S A ) (g , f) =
  cmp₀ A g f
S.inv (G↓S {Dir.≤} A) =
  _
S.inv (G↓S {Dir.≈} A) f =
  inv₀ A f
