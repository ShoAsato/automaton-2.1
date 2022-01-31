module equality where


data _==_ {A : Set } : A → A → Set where
   refl :  {x : A} → x == x

ex1 : {A : Set} {x : A } → x == x
ex1 {A} {x}  = refl

--ex1 証明図
--    { x : A }
--  -------------
--     x == x


ex2 : {A : Set} {x y : A } → x == y → y == x
ex2 {A} {x} {y} refl = refl   

--ex2 証明図
--      { x y : A }
--   -----------------
--     x == y  y == x
--   -----------------
--     x == y → y == x 


ex3 : {A : Set} {x y z : A } → x == y → y == z → x == z
ex3 {A} {x} {y} {z} a refl = a   

--ex3 証明図
--                { x y z : A }
--   ----------------------------------------
--     x == y  y == z        y == z  x == z
--   -----------------     -------------------
--     x == y → y == z       y == z → x == z
--   -----------------------------------------
--           x == y → y == z → x == z


ex4 : {A B : Set} {x y : A } { f : A → B } →   x == y → f x == f y
ex4 {A} {B} {x} {y} refl = refl 

--ex4 証明図
--                   {x y : A } { f : A → B }
--  ---------------------------------------------------------
--      x == y       f x y             x == y       f y x
 --  ----------------------------  ---------------------------
--            f x x                           f y y
--  ----------------------------------------------------------
--                     x == y → f x == f y
--  


subst : {A : Set } → { x y : A } → ( f : A → Set ) → x == y → f x → f y
subst {A} {x} {y} f refl fx = fx



--ex5 :   {A : Set} {x y z : A } →  x == y → y == z → x == z
--ex5 {A} {x} {y} {z} x==y y==z = subst (λ refl  → {!!} ) x==y {!!}



 