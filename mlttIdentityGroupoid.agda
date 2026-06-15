{-# OPTIONS --without-K #-}
module mlttIdentityGroupoid where 

data _id_ {A : Set} (x : A) : A → Set where
  refl : x id x

jRule :
  {A : Set} (x : A) (B : (y : A) (p : x id y) → Set) →
  B x refl → (y : A) (p : x id y) → B y p
jRule x B b y refl = b

-- Usando somente a regra J nas provas 
-- ponto de partida → afirmacao → caso base → destino → caminho

sym-purista : {A : Set} {x y : A} → x id y → y id x
sym-purista {A} {x} {y} p = jRule x (λ z _ → z id x) refl y p

trans-purista : {A : Set} {x y z : A} → x id y → y id z → x id z

trans-purista {A} {x} {y} {z} p1 p2 =  jRule y (λ u _ → x id u) p1 z p2 

cong : ∀ {A B : Set} (f : A → B) {x y : A}
  → x id y
  → f x id f y
cong {A} {B} f {x} {y} path =  jRule x (λ u _ → f x id f u) refl y path

subst : {A : Set} {x y : A} (P : A → Set) → x id y → P x → P y
subst {A} {x} {y} P id1 px = (jRule x (λ u _ → (P x → P u)) (λ px → px) y id1) px

-- provas sobre provas (contruindo caminhos de caminhos)

sym-sym : {A : Set} {x y : A} (p : x id y) → sym-purista (sym-purista p) id p
sym-sym {A} {x} {y} p = jRule x (λ u p_gen → sym-purista (sym-purista p_gen) id p_gen) refl y p

trans-left-id : {A : Set} {x y : A} (p : x id y) → trans-purista refl p id p
trans-left-id {A} {x} {y} p = jRule x (λ u p_gen → (trans-purista refl p_gen) id p_gen) refl y p

trans-right-id : {A : Set} {x y : A} (p : x id y) → trans-purista p refl id p
trans-right-id {A} {x} {y} p = jRule x (λ u p_gen → (trans-purista p_gen refl) id p_gen) refl y p

trans-right-inv : {A : Set} {x y : A} (p : x id y) → trans-purista p (sym-purista p) id refl
trans-right-inv {A} {x} {y} p = jRule x (λ u p_gen → trans-purista p_gen (sym-purista p_gen) id refl) refl y p  

trans-left-inv : {A : Set} {x y : A} (p : x id y) → trans-purista (sym-purista p) p id refl
trans-left-inv {A} {x} {y} p = jRule x (λ u p_gen → trans-purista (sym-purista p_gen) p_gen id refl) refl y p  

assoc-purista : {A : Set} {x y z w : A} (p : x id y) (q : y id z) (r : z id w) → (trans-purista (trans-purista p q) r) id (trans-purista p (trans-purista q r))
assoc-purista {A} {x} {y} {z} {w} p q r = jRule z (λ u p_gen → (trans-purista (trans-purista p q) p_gen) id (trans-purista p (trans-purista q p_gen))) refl w r

-- provas usando os mecanismos da linguagem

sym : ∀ {A : Set} {x y : A}
  → x id y
  → y id x
sym refl = refl

trans : ∀ {A : Set} {x y z : A}
  → x id y
  → y id z
  → x id z
trans refl refl = refl

trans-right-inv1 : {A : Set} {x y : A} (p : x id y) → trans p (sym p) id refl
trans-right-inv1 refl = refl   

trans-left-inv2 : {A : Set} {x y : A} (p : x id y) → trans (sym p) p id refl
trans-left-inv2 refl = refl

assoc : {A : Set} {x y z w : A} (p : x id y) (q : y id z) (r : z id w) → (trans (trans p q) r) id (trans p (trans q r))
assoc refl refl refl = refl

congr : ∀ {A B : Set} {x y : A} (p : A → B)
  → x id y
  → p x id p y 
congr p refl = refl
