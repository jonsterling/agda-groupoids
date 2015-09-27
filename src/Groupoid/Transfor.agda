{-# OPTIONS --without-K #-}

module Groupoid.Transfor where

open import Agda.Primitive
import Groupoid.Base as G
import Groupoid.Exponential.Boot as Π
import Setoid as S
import Setoid.Reasoning
open import Type as T
  using (_,_)

infixr 0 _⇒₁ᵗ_

record _⇒₁ᵗ_
  {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  (F G : A Π.⇒₀ᵗ B)
    : Set ((ℓ₀ᵒ ⊔ ℓ₀ˢᵒ) ⊔ (ℓ₁ˢᵒ ⊔ ℓ₁ˢʰ)) where
  no-eta-equality
  field
    com₁
      : ∀ {a}
      → S.obj (G.homˢ B (F Π.$₀ a , G Π.$₀ a))
  field
    .nat₁
      : ∀ {a b}
      → (f : S.obj (G.homˢ A (a , b)))
      → S.homᵗ (G.homˢ B (F Π.$₀ a , G Π.$₀ b))
          ( G.cmpˢᵐ B S.Π.$₀ (com₁ {b} , F Π.$₁ f)
          , G.cmpˢᵐ B S.Π.$₀ (G Π.$₁ f , com₁ {a})
          )
open _⇒₁ᵗ_ public

record _⇒₂_
  {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  {F G : A Π.⇒₀ᵗ B}
  (α β : F ⇒₁ᵗ G)
    : Set (ℓ₀ᵒ ⊔ (ℓ₁ˢᵒ ⊔ ℓ₁ˢʰ)) where
  no-eta-equality
  field
    .com₂
      : ∀ {a}
      → S.homᵗ (G.homˢ B (F Π.$₀ a , G Π.$₀ a)) (com₁ α {a} , com₁ β {a})
open _⇒₂_ public

_⇒₁ˢ_
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → (F G : A Π.⇒₀ᵗ B)
  → S.t S.Dir.≈ _ _
S.obj (_⇒₁ˢ_ F G) =
  F ⇒₁ᵗ G
S.homᵗ (_⇒₁ˢ_ F G) =
  λ {(α , β) → α ⇒₂ β}
com₂ (S.idnᵗᵐ (_⇒₁ˢ_ {B = B} F G) _) = λ {a} →
  S.idnᵗᵐ (G.homˢ B (F Π.$₀ a , G Π.$₀ a)) _
com₂ (S.cmpᵗᵐ (_⇒₁ˢ_ {B = B} F G) (g⇒₂ , f⇒₂)) = λ {a} →
  S.cmpᵗᵐ (G.homˢ B (F Π.$₀ a , G Π.$₀ a))
    (com₂ g⇒₂ {a} , com₂ f⇒₂ {a})
com₂ (S.invᵗᵐ (_⇒₁ˢ_ {B = B} F G) f⇒₂) = λ {a} →
  S.invᵗᵐ (G.homˢ B (F Π.$₀ a , G Π.$₀ a))
    (com₂ f⇒₂ {a})

idnˢᵐ
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → (F : A Π.⇒₀ᵗ B)
  → S.𝟙.s S.Π.⇒₀ᵗ (F ⇒₁ˢ F)
com₁ (S.Π._$₀_ (idnˢᵐ {B = B} F) x) =
  G.idnˢᵐ B S.Π.$₀ x
nat₁ (S.Π._$₀_ (idnˢᵐ {B = B} F) x) = λ {a b} f →
  S.cmpᵗᵐ (G.homˢ B (F Π.$₀ a , F Π.$₀ b))
    ( G.idn-rhs B (F Π.$₁ f)
    , G.idn-lhs B (F Π.$₁ f) )
com₂ (S.Π._$₁_ (idnˢᵐ {B = B} F) x) =
  G.idnˢᵐ B S.Π.$₁ x

cmpˢᵐ
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {F G H : A Π.⇒₀ᵗ B}
  → ((G ⇒₁ˢ H) S.∐.⊗ (F ⇒₁ˢ G)) S.Π.⇒₀ᵗ (F ⇒₁ˢ H)
com₁ (S.Π._$₀_ (cmpˢᵐ {B = B}) (β , α)) =
  G.cmpˢᵐ B S.Π.$₀ (com₁ β , com₁ α)
nat₁ (S.Π._$₀_ (cmpˢᵐ {B = B}) (β , α)) = λ f →
  S.cmpᵗᵐ (G.homˢ B _)
  ( G.cmp-ass B _ _ _
  , S.cmpᵗᵐ (G.homˢ B _)
    ( G.cmpˢᵐ B S.Π.$₁ (nat₁ β _ , S.idnᵗᵐ (G.homˢ B _) _)
    , S.cmpᵗᵐ (G.homˢ B _)
      ( S.invᵗᵐ (G.homˢ B _) (G.cmp-ass B _ _ _)
      , S.cmpᵗᵐ (G.homˢ B _)
        ( G.cmpˢᵐ B S.Π.$₁ (S.idnᵗᵐ (G.homˢ B _) _ , nat₁ α _)
        , G.cmp-ass B _ _ _ ))))
com₂ (S.Π._$₁_ (cmpˢᵐ {B = B}) (β , α)) =
  G.cmpˢᵐ B S.Π.$₁ (com₂ β , com₂ α)

invˢᵐ
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t S.Dir.≈ ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t S.Dir.≈ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → (F ⇒₁ˢ G) S.Π.⇒₀ᵗ (G ⇒₁ˢ F)
com₁ (S.Π._$₀_ (invˢᵐ {B = B}) α) =
  G.invˢᵐ B S.Π.$₀ (com₁ α)
com₂ (S.Π._$₁_ (invˢᵐ {B = B}) α) =
  G.invˢᵐ B S.Π.$₁ (com₂ α)
nat₁ (S.Π._$₀_ (invˢᵐ {A = A}{B = B}{F}{G}) α) = λ {a b} f →
  -- FIXME: normalize
  let open Setoid.Reasoning (G.homˢ B (G Π.$₀ a , F Π.$₀ b)) in
      proof

  G.cmpˢᵐ B S.Π.$₀ (G.invˢᵐ B S.Π.$₀ com₁ α , G Π.$₁ _)

      ≈⟨ G.idn-rhs B _ ⟩

  G.cmpˢᵐ B S.Π.$₀
    ( G.cmpˢᵐ B S.Π.$₀ (G.invˢᵐ B S.Π.$₀ com₁ α , G Π.$₁ _)
    , G.idnˢᵐ B S.Π.$₀ _ )

      ≈⟨ G.cmpˢᵐ B S.Π.$₁ (S.idnᵗᵐ (G.homˢ B _) _ , G.inv-rhs B _) ⟩

  G.cmpˢᵐ B S.Π.$₀
    ( G.cmpˢᵐ B S.Π.$₀ (G.invˢᵐ B S.Π.$₀ com₁ α , G Π.$₁ _)
    , G.cmpˢᵐ B S.Π.$₀ (com₁ α , G.invˢᵐ B S.Π.$₀ com₁ α) )

      ≈⟨ G.cmp-ass B _ _ _ ⟩

  G.cmpˢᵐ B S.Π.$₀
    ( G.invˢᵐ B S.Π.$₀ com₁ α
    , G.cmpˢᵐ B S.Π.$₀ (G Π.$₁ _ , G.cmpˢᵐ B S.Π.$₀ (com₁ α , G.invˢᵐ B S.Π.$₀ com₁ α)) )

      ≈⟨ G.cmpˢᵐ B S.Π.$₁ (S.idnᵗᵐ (G.homˢ B _) _ , S.invᵗᵐ (G.homˢ B _) (G.cmp-ass B _ _ _)) ⟩

  G.cmpˢᵐ B S.Π.$₀
    ( G.invˢᵐ B S.Π.$₀ com₁ α
    , G.cmpˢᵐ B S.Π.$₀ (G.cmpˢᵐ B S.Π.$₀ (G Π.$₁ _ , com₁ α) , G.invˢᵐ B S.Π.$₀ com₁ α) )

      ≈⟨ S.invᵗᵐ (G.homˢ B _) (G.cmp-ass B _ _ _) ⟩

  G.cmpˢᵐ B S.Π.$₀
    ( G.cmpˢᵐ B S.Π.$₀ (G.invˢᵐ B S.Π.$₀ com₁ α , G.cmpˢᵐ B S.Π.$₀ (G Π.$₁ _ , com₁ α))
    , G.invˢᵐ B S.Π.$₀ com₁ α )

      ≈⟨ G.cmpˢᵐ B S.Π.$₁
         ( G.cmpˢᵐ B S.Π.$₁ (S.idnᵗᵐ (G.homˢ B _) _ , S.invᵗᵐ (G.homˢ B _) (nat₁ α _))
         , S.idnᵗᵐ (G.homˢ B _) _ ) ⟩

  G.cmpˢᵐ B S.Π.$₀
    ( G.cmpˢᵐ B S.Π.$₀ (G.invˢᵐ B S.Π.$₀ com₁ α , G.cmpˢᵐ B S.Π.$₀ (com₁ α , F Π.$₁ _))
    , G.invˢᵐ B S.Π.$₀ com₁ α )

      ≈⟨ G.cmpˢᵐ B S.Π.$₁
         ( S.invᵗᵐ (G.homˢ B _) (G.cmp-ass B _ _ _)
         , S.idnᵗᵐ (G.homˢ B _) _ ) ⟩

  G.cmpˢᵐ B S.Π.$₀
    ( G.cmpˢᵐ B S.Π.$₀ (G.cmpˢᵐ B S.Π.$₀ (G.invˢᵐ B S.Π.$₀ com₁ α , com₁ α) , F Π.$₁ _)
    , G.invˢᵐ B S.Π.$₀ com₁ α )

      ≈⟨ G.cmpˢᵐ B S.Π.$₁
         ( G.cmpˢᵐ B S.Π.$₁ (G.inv-lhs B _ , S.idnᵗᵐ (G.homˢ B _) _)
         , S.idnᵗᵐ (G.homˢ B _) _ ) ⟩

  G.cmpˢᵐ B S.Π.$₀
    ( G.cmpˢᵐ B S.Π.$₀ (G.idnˢᵐ B S.Π.$₀ _ , F Π.$₁ _)
    , G.invˢᵐ B S.Π.$₀ com₁ α )

      ≈⟨ G.cmpˢᵐ B S.Π.$₁ (G.idn-lhs B _ , S.idnᵗᵐ (G.homˢ B _) _) ⟩

  G.cmpˢᵐ B S.Π.$₀ (F Π.$₁ _ , G.invˢᵐ B S.Π.$₀ com₁ α)

      ≈⟨ S.idnᵗᵐ (G.homˢ B _) _ ⟩

  G.cmpˢᵐ B S.Π.$₀ (F Π.$₁ _ , com₁ (invˢᵐ S.Π.$₀ α))

      ∎

-- FIXME: cmp-w₀ and cmp-w₀ are problematic because of Hα/βF dependency

cmp-w₀
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → (Hα : (B Π.⇒₀ᵗ C) T.∐.⊗ (F ⇒₁ᵗ G))
  → (T.∐.π₀ Hα Π.∘ᵗᵐ F) ⇒₁ᵗ (T.∐.π₀ Hα Π.∘ᵗᵐ G)
com₁ (cmp-w₀ (H , α)) =
  H Π.$₁ com₁ α
nat₁ (cmp-w₀ {C = C} (H , α)) = λ {a}{b} f →
  S.cmpᵗᵐ (G.homˢ C _)
  ( Π.cmp H _ _
  , S.cmpᵗᵐ (G.homˢ C _)
    ( H Π.$₂ (nat₁ α f)
    , S.invᵗᵐ (G.homˢ C _) (Π.cmp H _ _)))

cmp-w₁
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {G H : B Π.⇒₀ᵗ C}
  → (βF : (G ⇒₁ᵗ H) T.∐.⊗ (A Π.⇒₀ᵗ B))
  → (G Π.∘ᵗᵐ T.∐.π₁ βF) ⇒₁ᵗ (H Π.∘ᵗᵐ T.∐.π₁ βF)
com₁ (cmp-w₁ (β , F)) =
  com₁ β
nat₁ (cmp-w₁ (β , F)) =
  nat₁ β T.Π.∘ F Π.$₁_

cmpˢᵐ-h₀
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → {H K : B Π.⇒₀ᵗ C}
  → ((H ⇒₁ˢ K) S.∐.⊗ (F ⇒₁ˢ G)) S.Π.⇒₀ᵗ ((H Π.∘ᵗᵐ F) ⇒₁ˢ (K Π.∘ᵗᵐ G))
com₁ (S.Π._$₀_ (cmpˢᵐ-h₀ {C = C} {K = K}) (β , α)) =
  G.cmpˢᵐ C S.Π.$₀ (K Π.$₁ com₁ α , com₁ β)
com₂ (S.Π._$₁_ (cmpˢᵐ-h₀ {C = C} {K = K}) (β , α)) =
  G.cmpˢᵐ C S.Π.$₁ (K Π.$₂ com₂ α , com₂ β)
nat₁ (S.Π._$₀_ (cmpˢᵐ-h₀ {B = B}{C}{F}{G}{H}{K}) (β , α)) = λ {a}{b} f →
  let open Setoid.Reasoning (G.homˢ C ((H Π.∘ᵗᵐ F) Π.$₀ a , (K Π.∘ᵗᵐ G) Π.$₀ b)) in
        proof

  G.cmpˢᵐ C S.Π.$₀ (com₁ (cmpˢᵐ-h₀ S.Π.$₀ (β , α)) , (H Π.∘ᵗᵐ F) Π.$₁ _)

      ≈⟨ S.idnᵗᵐ (G.homˢ C _) _ ⟩

  G.cmpˢᵐ C S.Π.$₀ (G.cmpˢᵐ C S.Π.$₀ (K Π.$₁ com₁ α , com₁ β) , H Π.$₁ F Π.$₁ _)

      ≈⟨ G.cmp-ass C _ _ _ ⟩

  G.cmpˢᵐ C S.Π.$₀ (K Π.$₁ com₁ α , G.cmpˢᵐ C S.Π.$₀ (com₁ β , H Π.$₁ F Π.$₁ _))

      ≈⟨ G.cmpˢᵐ C S.Π.$₁ (S.idnᵗᵐ (G.homˢ C _) _ , nat₁ β (F Π.$₁ _)) ⟩

  G.cmpˢᵐ C S.Π.$₀ (K Π.$₁ com₁ α , G.cmpˢᵐ C S.Π.$₀ (K Π.$₁ F Π.$₁ _ , com₁ β))

      ≈⟨ S.invᵗᵐ (G.homˢ C _) (G.cmp-ass C _ _ _) ⟩

  G.cmpˢᵐ C S.Π.$₀ (G.cmpˢᵐ C S.Π.$₀ (K Π.$₁ com₁ α , K Π.$₁ F Π.$₁ f) , com₁ β)

      ≈⟨ G.cmpˢᵐ C S.Π.$₁
         ( S.invᵗᵐ (G.homˢ C _) (Π.cmp K (com₁ α) (F Π.$₁ _))
         , S.idnᵗᵐ (G.homˢ C _) _) ⟩

  G.cmpˢᵐ C S.Π.$₀ (K Π.$₁ G.cmpˢᵐ B S.Π.$₀ (com₁ α , F Π.$₁ _) , com₁ β)

      ≈⟨ G.cmpˢᵐ C S.Π.$₁ (K Π.$₂ nat₁ α _ , S.idnᵗᵐ (G.homˢ C _) _) ⟩

  G.cmpˢᵐ C S.Π.$₀ (K Π.$₁ G.cmpˢᵐ B S.Π.$₀ (G Π.$₁ _ , com₁ α) , com₁ β)

      ≈⟨ G.cmpˢᵐ C S.Π.$₁ (Π.cmp K (G Π.$₁ _) (com₁ α) , S.idnᵗᵐ (G.homˢ C _) _) ⟩

  G.cmpˢᵐ C S.Π.$₀ (G.cmpˢᵐ C S.Π.$₀ (K Π.$₁ G Π.$₁ _ , K Π.$₁ com₁ α) , com₁ β)

      ≈⟨ G.cmp-ass C _ _ _ ⟩

  G.cmpˢᵐ C S.Π.$₀ (K Π.$₁ G Π.$₁ _ , G.cmpˢᵐ C S.Π.$₀ (K Π.$₁ com₁ α , com₁ β))

      ≈⟨ S.idnᵗᵐ (G.homˢ C _) _ ⟩

  G.cmpˢᵐ C S.Π.$₀ ((K Π.∘ᵗᵐ G) Π.$₁ _ , com₁ (cmpˢᵐ-h₀ S.Π.$₀ (β , α)))

      ∎

cmpˢᵐ-h₁
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → {H K : B Π.⇒₀ᵗ C}
  → ((H ⇒₁ˢ K) S.∐.⊗ (F ⇒₁ˢ G)) S.Π.⇒₀ᵗ ((H Π.∘ᵗᵐ F) ⇒₁ˢ (K Π.∘ᵗᵐ G))
com₁ (S.Π._$₀_ (cmpˢᵐ-h₁ {C = C} {H = H}) (β , α)) =
  G.cmpˢᵐ C S.Π.$₀ (com₁ β , H Π.$₁ com₁ α)
com₂ (S.Π._$₁_ (cmpˢᵐ-h₁ {C = C} {H = H}) (β , α)) =
  G.cmpˢᵐ C S.Π.$₁ (com₂ β , H Π.$₂ com₂ α)
nat₁ (S.Π._$₀_ (cmpˢᵐ-h₁ {B = B}{C}{F}{G}{H}{K}) (β , α)) = λ {a}{b} f →
  let open Setoid.Reasoning (G.homˢ C ((H Π.∘ᵗᵐ F) Π.$₀ a , (K Π.∘ᵗᵐ G) Π.$₀ b)) in
      proof

  G.cmpˢᵐ C S.Π.$₀ (com₁ (cmpˢᵐ-h₁ S.Π.$₀ (β , α)) , (H Π.∘ᵗᵐ F) Π.$₁ _)

      ≈⟨ S.idnᵗᵐ (G.homˢ C _) _ ⟩

  G.cmpˢᵐ C S.Π.$₀ (G.cmpˢᵐ C S.Π.$₀ (com₁ β , H Π.$₁ com₁ α) , H Π.$₁ F Π.$₁ _)

      ≈⟨ G.cmp-ass C _ _ _ ⟩

  G.cmpˢᵐ C S.Π.$₀ (com₁ β , G.cmpˢᵐ C S.Π.$₀ (H Π.$₁ com₁ α , H Π.$₁ F Π.$₁ _))

      ≈⟨ G.cmpˢᵐ C S.Π.$₁ (S.idnᵗᵐ (G.homˢ C _) _ , S.invᵗᵐ (G.homˢ C _) (Π.cmp H _ _)) ⟩

  G.cmpˢᵐ C S.Π.$₀ (com₁ β , H Π.$₁ G.cmpˢᵐ B S.Π.$₀ (com₁ α , F Π.$₁ _))

      ≈⟨ G.cmpˢᵐ C S.Π.$₁ (S.idnᵗᵐ (G.homˢ C _) _ , H Π.$₂ nat₁ α _) ⟩

  G.cmpˢᵐ C S.Π.$₀ (com₁ β , H Π.$₁ G.cmpˢᵐ B S.Π.$₀ (G Π.$₁ _ , com₁ α))

      ≈⟨ G.cmpˢᵐ C S.Π.$₁ (S.idnᵗᵐ (G.homˢ C _) _ , Π.cmp H _ _) ⟩

  G.cmpˢᵐ C S.Π.$₀ (com₁ β , G.cmpˢᵐ C S.Π.$₀ (H Π.$₁ G Π.$₁ _ , H Π.$₁ com₁ α))

      ≈⟨ S.invᵗᵐ (G.homˢ C _) (G.cmp-ass C _ _ _) ⟩

  G.cmpˢᵐ C S.Π.$₀ (G.cmpˢᵐ C S.Π.$₀ (com₁ β , H Π.$₁ G Π.$₁ _) , H Π.$₁ com₁ α)

      ≈⟨ G.cmpˢᵐ C S.Π.$₁ (nat₁ β _ , S.idnᵗᵐ (G.homˢ C _) _) ⟩

  G.cmpˢᵐ C S.Π.$₀ (G.cmpˢᵐ C S.Π.$₀ (K Π.$₁ G Π.$₁ _ , com₁ β) , H Π.$₁ com₁ α)

      ≈⟨ G.cmp-ass C _ _ _ ⟩

  G.cmpˢᵐ C S.Π.$₀ (K Π.$₁ G Π.$₁ _ , G.cmpˢᵐ C S.Π.$₀ (com₁ β , H Π.$₁ com₁ α))

      ≈⟨ S.idnᵗᵐ (G.homˢ C _) _ ⟩

  G.cmpˢᵐ C S.Π.$₀ ((K Π.∘ᵗᵐ G) Π.$₁ _ , com₁ (cmpˢᵐ-h₁ S.Π.$₀ (β , α)))

      ∎
