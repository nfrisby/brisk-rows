{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -fplugin=BriskRows.Internal.Plugin #-}

module Test (module Test) where

import           Data.Kind (Type)
import           GHC.Exts (Proxy#, proxy#)

import           BriskRows

{-
badABC x = extend# (proxy# @"A") x . extend# (proxy# @"B") x . extend# (proxy# @"C") x

badCBA x = extend# (proxy# @"C") x . extend# (proxy# @"B") x . extend# (proxy# @"A") x

badA x = extend# (proxy# @"A") x

bad_ x = extend# (proxy# @"A") x $ extend# proxy# x $ emp


bad2 :: a -> Proxy# l -> Proxy# r -> Rcd (Insert l a (Insert r a Nil)) -> Rcd (Insert "A" a (Insert l a (Insert r a Nil)))
bad2 x _l _r = extend# (proxy# @"A") x


bad1 :: a -> Proxy# l -> Rcd (Insert l a Nil) -> Rcd (Insert "A" a (Insert l a Nil))
bad1 x _l = extend# (proxy# @"A") x
-}

good1 = emp .* #world 'w' .* #hello 'h'

good2 = ext @"hello" 'h' $ ext @"world" 'w' $ emp

good3 = good1 ./ #world

good4 = unmerge good2 `asTypeOf` (good1, good3)

-----

plugin_test = unextend @"hello" $ ext @"please" False good2

-----

data Term :: ROW -> Type -> Type where
  Var ::                    Proxy# nm -> Proxy# a               -> Term (Nil :& nm ::: a) a
  App :: Agree env1 env2 => Term env1 (a -> b) -> Term env2 a   -> Term (Union env1 env2) b
  Lam :: Present nm env  => Proxy# nm -> Term env b             -> Term (env :# nm) (Lookup nm env -> b)
  Wkn :: Absent  nm env  => Proxy# nm -> Proxy# a -> Term env b -> Term (env :& nm ::: a) b

interpret :: Rcd env -> Term env a -> a
interpret rho = \case
    Var nm _a  -> project# nm rho
    App e1 e2  ->
        let (rho1, rho2) = unmerge rho
        in (interpret rho1 e1) (interpret rho2 e2)
    Lam nm e   -> \a -> interpret (unremove# nm rho a) e
    Wkn nm a e -> interpret (snd' a $ unextend# nm rho) e

snd' :: Proxy# a -> (a, b) -> b
snd' _ = snd

composition () =
    Lam (proxy# @"f") $ Lam (proxy# @"g") $ Lam (proxy# @"x")
  $ Var (proxy# @"f") proxy# `App`
    (Var (proxy# @"g") proxy# `App` Var (proxy# @"x") proxy#)

-- \m n f x. m f (n f x)
churchAdd () =
    Lam (proxy# @"m") $ Lam (proxy# @"n") $ Lam (proxy# @"f") $ Lam (proxy# @"x")
  $ Var (proxy# @"m") proxy# `App` Var (proxy# @"f") proxy# `App`
    (Var (proxy# @"n") proxy# `App` Var (proxy# @"f") proxy# `App` Var (proxy# @"x") proxy#)

example = interpret empty (composition ()) (+1) (+2) 0
