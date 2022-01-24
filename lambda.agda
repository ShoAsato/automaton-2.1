module lambda ( A B : Set) (a : A ) (b : B ) where

--   λ-intro 
--
--      A
--   -------- id
--      A
--   -------- λ-intro ( =  λ ( x : A ) → x )
--    A → A 

A→A : A → A 
A→A = λ ( x : A ) → x

A→A'' : A → A 
A→A'' = λ x  → x

A→A' : A → A 
A→A' x = x


lemma2 : (A : Set ) →  A → A   --  これは  A → ( A  → A ) とは違う
lemma2 A a = a  

λ-intro : {A B : Set } →  A →  B  → ( A → B )  -- {} implicit variable
λ-intro  a b = λ a → b    -- _ anonymous variable

-- λ-intro {A} {B} a b = λ a → b    

--   λ-elim
--
--      A     A → B
--   ----------------- λ-elim 
--          B

→elim : A → ( A → B ) → B
→elim a f = f a




ex1 : {A B : Set} → Set 
ex1 {A} {B} = A → B   -- ( A → B ) → A → B

--ex1 証明図
--      A 
--      :
--      B 
--  ---------
--    A → B



ex2 : {A : Set} → Set 
ex2 {A} = A → ( A → A ) 

--ex2, proof2 証明図
--          A
--          :
--          A
--  -----------------
--     A → ( A → A ) 

proof2 : {A : Set } → ex2 {A}
proof2 {A} = p1 where  ---{A} a = λ a → a  where
  p1 : ex2{A}  --- ex2 {A} を C-C C-N する
  p1 a = λ a → a




ex3 :  A → B     -- インチキの例
ex3 a = b 

--ex3 証明図
--    A
--  -----
--    B



ex4 : {A B : Set} → A → (B → B)  -- 仮定を無視してる
ex4 {A}{B} a b = b



--ex4, 4' 証明図
---           [A]₁               not used   --- a
---         ────────────────────
---                 [B]₂                    --- b
---         ──────────────────── (₂)
---             B → B
---         ──────────────────── (₁)  λ-intro
---              A → (B → B) 


ex4' : A → (B → B)   -- インチキできる / 仮定を使える
ex4' a = λ b → b 




ex5 : {A B : Set} → A → B → A
ex5 {A}{B} a b = a


--ex5 証明図
--     
--    A → B    B → A
--   ---------------
--      A → B → A

postulate
  Domain : Set   --  Range Domain : Set
  Range : Set    -- codomain     Domain → Range, coRange ← coDomain
  r : Range 

ex6 : Domain → Range
ex6 a = r

--ex6 証明図
--       Domain
--          :
--        Range
--  ------------------
--    Domain → Range






--ex11, 12, 13, 14 証明図
---                   A → B
--                     :
---                   A → B
---         ─────────────────────────── 
---              ( A → B ) → A → B
---
---              [A]₁     [A → B ]₂
---         ───────────────────────────  λ-elim
---                    B
---         ───────────────────────────  ₁
---                   A → B
---         ───────────────────────────  ₂
---              ( A → B ) → A → B

--
--  上の二つの図式に対応する二つの証明に対応するラムダ項がある
--
ex11 : ( A → B ) → A → B
ex11 f = f  

ex12 : (A B : Set) → ( A → B ) → A → B
ex12 A B a b = a b

ex13 : {A B : Set} → ( A → B ) → A → B
ex13 {A} {B} a b = a b 

ex14 : {A B : Set} → ( A → B ) → A → B
ex14 x = x


 