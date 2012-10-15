{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE EmptyDataDecls #-}
module Data.Dynamic.Poly(
    -- * "Data.Dynamic"-like interface
    Dynamic,fromDyn,fromDynamic,toDyn,dynApply,toDynG,
    -- * Explicit type representation
    Ty,TyG,TM,runTM,ret,(>>>=),var,varf,pvar,(~>),($$),kr,ks,kt,
    -- * Helpers
    Fin(..),toInt,Proxy(..),unProxy,N(..),Dict(..),
    -- * Variable names
    A,B,C,D,E,F,G,K,L,M
    ) where

import Data.Foldable
import Data.Traversable
import Control.Arrow(left)
import Control.Monad.Error
import Control.Monad.Identity
import Control.Unification
import Control.Unification.IntVar
import Data.Maybe
import Data.Typeable
import Unsafe.Coerce

data N = Z | S N 

data Proxy a = Proxy

-- | Constraint kind proxy
data Dict a where
    Dict :: a => Dict a

unProxy :: Proxy a -> a
unProxy = error "unProxy"

data Fin :: N -> * where
     Zero :: Fin n
     Succ :: Fin n -> Fin (S n)

toInt :: Fin n -> Int 
toInt Zero     = 0
toInt (Succ s) = toInt s + 1

-- | Typed type's pattern
--
--       * 'i' - input type parameter which is unified type system 
--         on packing ('toDyn')
--
--       * 'o' - output parameter which is unified on 
--         unpacking ('fromDyn' and 'fromDynamic')
data Ty (i :: k) (o :: k) = Ty TyU

data Dynamic where
    Dynamic :: TyU -> a -> Dynamic
    deriving (Typeable)

fromDyn :: Ty i o -> Dynamic -> o -> o
fromDyn t v d = fromMaybe d (fromDynamic t v)

fromDynamic :: Ty i o -> Dynamic -> Maybe o
fromDynamic (Ty t) (Dynamic t' v) = either (const Nothing) Just $ runUniM 
                                    $ do
                                      f <- freshen t
                                      f' <- freshen t'
                                      s <- subsumes f f'
                                      unless s $ fail "incompatible types"
                                      return (unsafeCoerce v)

toDyn :: Ty i o -> i -> Dynamic
toDyn (Ty t) v = Dynamic t v

toDynG :: Typeable a => a -> Dynamic
toDynG v = Dynamic (UTerm (K (typeOf v))) v

dynApply :: Dynamic -> Dynamic -> Maybe Dynamic
dynApply (Dynamic ft@(UTerm (Arr _ _)) fv) (Dynamic a av) 
    = either (const Nothing) Just $ runUniM 
      $ do
        (UTerm (Arr fd fc)) <- freshen ft
        at <- freshen a
        _ <- unifyOccurs fd at
        fc' <- applyBindings fc
        return $ Dynamic fc' (unsafeCoerce fv $ av)
dynApply _ _ = Nothing

-- | An indexed monad for generating fresh type variables
data TM s s' a = TM (Fin s -> (Fin s', a)) 

runTM :: TM Z s a -> a
runTM (TM f) = case f Zero of (_, v) -> v

-- | return for 'TM'
ret :: a -> TM env env a
ret a = TM $ \e -> (e, a)

type UniM = ErrorT (UnificationFailure TyU' IntVar) 
                   (IntBindingT TyU' Identity)

-- | runs 'TM' computation
runUniM :: UniM a -> Either String a
runUniM = left show . runIdentity . evalIntBindingT . runErrorT 

-- | bind for 'TM'
(>>>=) :: TM s s' a -> (a -> TM s' s'' b) -> TM s s'' b
TM a >>>= f = TM $ \e -> case a e of (e',a') -> case f a' of TM b -> b e'

infixl 1 >>>=

-- | Untyped type's pattern (suitable for unification-fd)
data TyU' a = K TypeRep
         | KS String
         | App a a
         | Arr a a -- ^ for faster application
         deriving (Show,Functor,Foldable,Traversable)

instance Unifiable TyU' where
    zipMatch (K k)     (K k')      = if k == k' then Just (K k) else Nothing
    zipMatch (KS n)    (KS n')     = if n == n' then Just (KS n) else Nothing 
    zipMatch (App f a) (App f' a') = Just (App (Right (f,f')) (Right (a, a')))
    zipMatch (Arr d c) (Arr d' c') = Just (Arr (Right (d,d')) (Right (c, c')))
    zipMatch _         _           = Nothing

type TyU = UTerm TyU' IntVar

data A 
data B
data C
data D
data E
data F :: * -> *
data G :: * -> *
data K :: * -> *
data L :: * -> *
data M :: * -> *

-- | an environment for rigid variable names (splited into * and k -> * kinds 
--   for better result types readability)
type FunVarNames = (Proxy F,(Proxy G,(Proxy L,(Proxy K,(Proxy M,())))))

type StarVarNames = (A,(B,(C,(D,(E,())))))

type family TyVar (f :: k) (n :: N) env :: k
type instance TyVar (f :: * -> *) Z (Proxy f', t) = f' 
type instance TyVar (f :: k) (S n) (h, t) = TyVar f n t 
type instance TyVar (a :: *) Z (a', t) = a'

-- | Returns a type variable representation 
-- it is not pure, it adds variable in an environment, whence
-- the type is an indexed-monad computation
var ::  TM n (S n) (Ty (TyVar a n StarVarNames) a)
var = TM $ \e -> (Succ e, Ty (UVar (IntVar (toInt e))))

varf :: forall (f :: * -> *) n . TM n (S n) (Ty (TyVar f n FunVarNames) f)
varf = TM $ \e -> (Succ e, Ty (UVar (IntVar (toInt e))))

-- | Returns a type variable representation
-- Pure version of 'var' with explicit variable's type and an index.
pvar :: Proxy f -> Fin n -> Ty (TyVar f n FunVarNames) f
pvar _ e = Ty (UVar (IntVar (toInt e)))

-- | Builds an arrow type
(~>) :: Ty i o -> Ty i' o' -> Ty (i -> i') (o -> o')
Ty l ~> Ty r = Ty (UTerm (Arr l r))

-- | Shortcut for ground types
type TyG a = Ty a a

-- | Ground type from 'TypeRep'
kr :: TypeRep -> Ty a a
kr = Ty . mk
      where mk r = case splitTyConApp r of
                     (n, t) -> foldl' (\n' -> UTerm . App n' . mk) (UTerm (KS (show n))) t

-- | Ground type for any 'Typeable'
kt :: Typeable a => TyG a
kt = hlp (error "k")
      where
        hlp :: Typeable a => a -> TyG a
        hlp v = kr (typeOf v) 

-- | Ground type by type's string (useful for quick type's definitions which 
--   don't have 'Typeable' instances yet, such as constraint kinds)
ks :: String -> TyG a
ks n = Ty (UTerm (KS n))

-- | Builds type's application patterns
($$) :: Ty f f' -> Ty a a' -> Ty (f a) (f' a')
Ty f $$ Ty a = Ty (UTerm (App f a))

infixr 5 $$
infixr 3 ~>


instance Show Dynamic where
    show (Dynamic t _) = show t