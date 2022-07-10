module BriskRows.Internal.Plugin (plugin) where

import           Constraint (Ct)
import qualified GhcPlugins
import qualified TcRnTypes

plugin :: GhcPlugins.Plugin
plugin = GhcPlugins.defaultPlugin
  { GhcPlugins.tcPlugin = \_ -> Just TcRnTypes.TcPlugin
    { TcRnTypes.tcPluginInit  = pure ()
    , TcRnTypes.tcPluginSolve = solve
    , TcRnTypes.tcPluginStop  = \() -> pure ()
    }
  }

solve :: () -> [Ct] -> [Ct] -> [Ct] -> TcRnTypes.TcPluginM TcRnTypes.TcPluginResult
solve () _given _derived _wanted = pure $ TcRnTypes.TcPluginOk [] []
