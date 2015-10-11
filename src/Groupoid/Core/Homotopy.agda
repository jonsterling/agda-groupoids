{-# OPTIONS --without-K #-}

module Groupoid.Core.Homotopy where

open import Agda.Primitive
import Groupoid.Core.Base as G
import Groupoid.Core.Hom.Boot as Π
import Setoid as S
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
      → S.homᵗ (G.homˢ B (F Π.$₀ _ , G Π.$₀ _))
          ( G.cmpˢ B S.Π.$₀ (com₁ , F Π.$₁ f)
          , G.cmpˢ B S.Π.$₀ (G Π.$₁ f , com₁)
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
com₂ (S.idnᵗ (_⇒₁ˢ_ {B = B} F G) _) =
  S.idnᵗ (G.homˢ B (F Π.$₀ _ , G Π.$₀ _)) _
com₂ (S.cmpᵗ (_⇒₁ˢ_ {B = B} F G) (g⇒₂ , f⇒₂)) =
  S.cmpᵗ (G.homˢ B (F Π.$₀ _ , G Π.$₀ _))
    (com₂ g⇒₂ , com₂ f⇒₂)
com₂ (S.invᵗ (_⇒₁ˢ_ {B = B} F G) f⇒₂) =
  S.invᵗ (G.homˢ B (F Π.$₀ _ , G Π.$₀ _))
    (com₂ f⇒₂)

idn₁ˢ
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → (F : A Π.⇒₀ᵗ B)
  → S.𝟙.s S.Π.⇒₀ᵗ (F ⇒₁ˢ F)
com₁ (S.Π._$₀_ (idn₁ˢ {B = B} F) _) =
  G.idnˢ B S.Π.$₀ _
nat₁ (S.Π._$₀_ (idn₁ˢ {B = B} F) _) _ =
  S.cmpᵗ (G.homˢ B (F Π.$₀ _ , F Π.$₀ _))
    ( G.idn-rhs B (F Π.$₁ _)
    , G.idn-lhs B (F Π.$₁ _) )
com₂ (S.Π._$₁_ (idn₁ˢ {B = B} F) _) =
  G.idnˢ B S.Π.$₁ _

cmp₁ˢ
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {F G H : A Π.⇒₀ᵗ B}
  → ((G ⇒₁ˢ H) S.∐.⊗ (F ⇒₁ˢ G)) S.Π.⇒₀ᵗ (F ⇒₁ˢ H)
com₁ (S.Π._$₀_ (cmp₁ˢ {B = B}) (β , α)) =
  G.cmpˢ B S.Π.$₀ (com₁ β , com₁ α)
nat₁ (S.Π._$₀_ (cmp₁ˢ {B = B}) (β , α)) _ =
  S.cmpᵗ (G.homˢ B _)
  ( G.cmp-ass B _ _ _
  , S.cmpᵗ (G.homˢ B _)
    ( G.cmpˢ B S.Π.$₁
      ( nat₁ β _
      , S.idnᵗ (G.homˢ B _) _ )
    , S.cmpᵗ (G.homˢ B _)
      ( S.invᵗ (G.homˢ B _) (G.cmp-ass B _ _ _)
      , S.cmpᵗ (G.homˢ B _)
        ( G.cmpˢ B S.Π.$₁
          ( S.idnᵗ (G.homˢ B _) _
          , nat₁ α _ )
        , G.cmp-ass B _ _ _ ))))
com₂ (S.Π._$₁_ (cmp₁ˢ {B = B}) (β , α)) =
  G.cmpˢ B S.Π.$₁ (com₂ β , com₂ α)

inv₁ˢ
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t S.Dir.≈ ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t S.Dir.≈ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → (F ⇒₁ˢ G) S.Π.⇒₀ᵗ (G ⇒₁ˢ F)
com₁ (S.Π._$₀_ (inv₁ˢ {B = B}) α) =
  G.invˢ B S.Π.$₀ (com₁ α)
com₂ (S.Π._$₁_ (inv₁ˢ {B = B}) α) =
  G.invˢ B S.Π.$₁ (com₂ α)
nat₁ (S.Π._$₀_ (inv₁ˢ {A = A}{B = B}) α) _ =
  S.cmpᵗ (G.homˢ B _)
    ( S.cmpᵗ (G.homˢ B _)
      ( S.cmpᵗ (G.homˢ B _)
        ( S.cmpᵗ (G.homˢ B _)
          ( S.cmpᵗ (G.homˢ B _)
            ( G.cmpˢ B S.Π.$₁
              ( S.cmpᵗ (G.homˢ B _)
                ( S.cmpᵗ (G.homˢ B _)
                  ( S.cmpᵗ (G.homˢ B _)
                    ( G.idn-lhs B _
                    , G.cmpˢ B S.Π.$₁
                      ( G.inv-lhs B _
                      , S.idnᵗ (G.homˢ B _) _ ) )
                  , S.invᵗ (G.homˢ B _) (G.cmp-ass B _ _ _) )
                , G.cmpˢ B S.Π.$₁
                  ( S.idnᵗ (G.homˢ B _) _
                  , S.invᵗ (G.homˢ B _) (nat₁ α _) ))
              , S.idnᵗ (G.homˢ B _) _ )
            , S.invᵗ (G.homˢ B _) (G.cmp-ass B _ _ _) )
          , G.cmpˢ B S.Π.$₁
            ( S.idnᵗ (G.homˢ B _) _
            , S.invᵗ (G.homˢ B _) (G.cmp-ass B _ _ _) ) )
        , G.cmp-ass B _ _ _)
      , G.cmpˢ B S.Π.$₁ (S.idnᵗ (G.homˢ B _) _ , G.inv-rhs B _))
    , G.idn-rhs B _)

record _≅_
  {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  (F G : A Π.⇒₀ᵗ B)
    : Set ((ℓ₀ᵒ ⊔ ℓ₀ˢᵒ) ⊔ (ℓ₁ˢᵒ ⊔ ℓ₁ˢʰ)) where
  no-eta-equality
  field
    fwd : F ⇒₁ᵗ G
    bwd : G ⇒₁ᵗ F
  field
    .iso-fwd : S.homᵗ (F ⇒₁ˢ F) (cmp₁ˢ S.Π.$₀ (bwd , fwd) , idn₁ˢ F S.Π.$₀ _)
    .iso-bwd : S.homᵗ (G ⇒₁ˢ G) (cmp₁ˢ S.Π.$₀ (fwd , bwd) , idn₁ˢ G S.Π.$₀ _)

-- FIXME: cmp-w₀ and cmp-w₀ are problematic because of Hα/βF dependency

cmp₁ᵗ-w₀
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → (Hα : (B Π.⇒₀ᵗ C) T.∐.⊗ (F ⇒₁ᵗ G))
  → (T.∐.π₀ Hα Π.∘₀ᵗ F) ⇒₁ᵗ (T.∐.π₀ Hα Π.∘₀ᵗ G)
com₁ (cmp₁ᵗ-w₀ (H , α)) =
  H Π.$₁ com₁ α
nat₁ (cmp₁ᵗ-w₀ {C = C} (H , α)) f =
  S.cmpᵗ (G.homˢ C _)
  ( Π.cmp H _ _
  , S.cmpᵗ (G.homˢ C _)
    ( H Π.$₂ (nat₁ α f)
    , S.invᵗ (G.homˢ C _) (Π.cmp H _ _)))

cmp₁ᵗ-w₁
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {G H : B Π.⇒₀ᵗ C}
  → (βF : (G ⇒₁ᵗ H) T.∐.⊗ (A Π.⇒₀ᵗ B))
  → (G Π.∘₀ᵗ T.∐.π₁ βF) ⇒₁ᵗ (H Π.∘₀ᵗ T.∐.π₁ βF)
com₁ (cmp₁ᵗ-w₁ (β , F)) = com₁ β
nat₁ (cmp₁ᵗ-w₁ (β , F)) = nat₁ β T.Π.∘ F Π.$₁_

cmp₀ˢ-h₀
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → {H K : B Π.⇒₀ᵗ C}
  → ((H ⇒₁ˢ K) S.∐.⊗ (F ⇒₁ˢ G)) S.Π.⇒₀ᵗ ((H Π.∘₀ᵗ F) ⇒₁ˢ (K Π.∘₀ᵗ G))
com₁ (S.Π._$₀_ (cmp₀ˢ-h₀ {C = C} {K = K}) (β , α)) =
  G.cmpˢ C S.Π.$₀ (K Π.$₁ com₁ α , com₁ β)
com₂ (S.Π._$₁_ (cmp₀ˢ-h₀ {C = C} {K = K}) (β , α)) =
  G.cmpˢ C S.Π.$₁ (K Π.$₂ com₂ α , com₂ β)
nat₁ (S.Π._$₀_ (cmp₀ˢ-h₀ {C = C}{K = K}) (β , α)) _ =
  S.cmpᵗ (G.homˢ C _)
    ( S.cmpᵗ (G.homˢ C _)
      ( S.cmpᵗ (G.homˢ C _)
        ( S.cmpᵗ (G.homˢ C _)
          ( G.cmp-ass C _ _ _
          , G.cmpˢ C S.Π.$₁
            ( S.cmpᵗ (G.homˢ C _)
              ( S.cmpᵗ (G.homˢ C _)
                ( Π.cmp K _ _
                , K Π.$₂ nat₁ α _ )
              , S.invᵗ (G.homˢ C _) (Π.cmp K _ _) )
            , S.idnᵗ (G.homˢ C _) _) )
        , S.invᵗ (G.homˢ C _) (G.cmp-ass C _ _ _) )
      , G.cmpˢ C S.Π.$₁ (S.idnᵗ (G.homˢ C _) _ , nat₁ β _) )
    , G.cmp-ass C _ _ _ )

cmp₀ˢ-h₁
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → {H K : B Π.⇒₀ᵗ C}
  → ((H ⇒₁ˢ K) S.∐.⊗ (F ⇒₁ˢ G)) S.Π.⇒₀ᵗ ((H Π.∘₀ᵗ F) ⇒₁ˢ (K Π.∘₀ᵗ G))
com₁ (S.Π._$₀_ (cmp₀ˢ-h₁ {C = C}{H = H}) (β , α)) =
  G.cmpˢ C S.Π.$₀ (com₁ β , H Π.$₁ com₁ α)
com₂ (S.Π._$₁_ (cmp₀ˢ-h₁ {C = C}{H = H}) (β , α)) =
  G.cmpˢ C S.Π.$₁ (com₂ β , H Π.$₂ com₂ α)
nat₁ (S.Π._$₀_ (cmp₀ˢ-h₁ {C = C}{H = H}) (β , α)) _ =
  S.cmpᵗ (G.homˢ C _)
    ( S.cmpᵗ (G.homˢ C _)
      ( S.cmpᵗ (G.homˢ C _)
        ( S.cmpᵗ (G.homˢ C _)
          ( G.cmp-ass C _ _ _
          , G.cmpˢ C S.Π.$₁
            ( nat₁ β _
            , S.idnᵗ (G.homˢ C _) _ ) )
        , S.invᵗ (G.homˢ C _) (G.cmp-ass C _ _ _) )
      , G.cmpˢ C S.Π.$₁
        ( S.idnᵗ (G.homˢ C _) _
        , S.cmpᵗ (G.homˢ C _)
          ( S.cmpᵗ (G.homˢ C _)
            ( Π.cmp H _ _
            , H Π.$₂ nat₁ α _ )
          , S.invᵗ (G.homˢ C _) (Π.cmp H _ _) ) ) )
    , G.cmp-ass C _ _ _ )
