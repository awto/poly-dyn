module First where

import Data.Dynamic.Poly

idt = runTM (var >>>= \v -> ret (v ~> v))
showt = runTM (var >>>= \v -> ret (showTy v ~> v ~> strTy))

showC :: ProxyC (Show a) -> a -> String
showC ProxyC = show

showTy :: Ty a a' -> Ty (ProxyC (Show a)) (ProxyC (Show a')) 
showTy t = pcTy $$ ks "Show" $$ t

pcTy :: TyG Dict
pcTy = ks "Dict"

strTy :: TyG String 
strTy = kt

infixr 3 ==>

(==>) :: Ty i o -> Ty i' o' -> Ty (ProxyC i -> i') (ProxyC o -> o')
l ==> r = pcTy $$ l ~> r

t1 :: Maybe String
t1 = do
  p  <- dynApply (toDyn idt (\k -> k)) (toDynG (4 :: Int))
  p' <- dynApply (toDyn showt showC)
        (toDyn (showTy kt) (ProxyC :: ProxyC (Show Int)))
  p'' <- dynApply p' p
  fromDynamicG p''
