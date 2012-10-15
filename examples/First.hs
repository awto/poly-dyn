module First where

import Data.Dynamic.Poly
import Data.Typeable

idt = runTM (var >>>= \v -> ret (v ~> v))
showt = runTM (var >>>= \v -> ret (showTy v ~> v ~> strTy))

showC :: Dict (Show a) -> a -> String
showC Dict = show

showTy :: Ty a a' -> Ty (Dict (Show a)) (Dict (Show a')) 
showTy t = dictTy $$ (ks "Show" $$ t)

dictTy :: TyG Dict
dictTy = ks "Dict"

strTy :: TyG String 
strTy = kt

t1 :: Maybe String
t1 = do
  p  <- dynApply (toDyn idt (\k -> k)) (toDynG (4 :: Int))
  p' <- dynApply (toDyn showt showC)
        (toDyn (showTy kt) (Dict :: Dict (Show Int)))
  p'' <- dynApply p' p
  fromDynamic kt p''

fmapC :: Dict (Functor f) -> (a -> b) -> f a -> f b
fmapC Dict = fmap

functTy :: TyG Functor
functTy = ks "Functor"

fmapTy = runTM $ var >>>= \f -> var >>>= \a -> var >>>= \b ->
         ret (dictTy $$ (functTy $$ f) ~> (a ~> b) ~> f $$ a ~> f $$ b)

fmapDyn = toDyn fmapTy fmapC

lstTy :: TyG []
lstTy = kr (typeOf1 (undefined :: [()]))

t2 :: Maybe [String]
t2 = do
  m <- dynApply fmapDyn (toDyn (dictTy $$ (functTy $$ lstTy)) Dict)
  s <- dynApply (toDyn showt showC) (toDyn (showTy kt) (Dict :: Dict (Show Int)))
  f <- dynApply m s
  r <- dynApply f (toDyn kt i)
  fromDynamic kt r 
  where
  i = [1 :: Int,2,3,4,5]
