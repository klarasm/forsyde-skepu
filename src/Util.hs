module Util (compileToCore, showPpr) where

import Data.Data
import Data.Generics
import GHC
import GHC.Driver.Main
import GHC.Paths
import GHC.Plugins
import GHC.Tc.Types
import System.FilePath

compileToCore :: Maybe FilePath -> FilePath -> IO (CoreProgram, DynFlags)
compileToCore forSyDePath filePath = runGhc (Just libdir) $ do
  dflags <- getSessionDynFlags
  let newDflags = makeDynFlags dflags
  _ <- setSessionDynFlags $ newDflags
  target <- guessTarget filePath Nothing Nothing
  setTargets [target]
  _ <- load LoadAllTargets
  let modName = mkModuleName (takeBaseName filePath)
  summary <- getModSummary modName
  env <- getSession
  parsed <- liftIO $ hscParse env summary
  (tcg', _) <- liftIO $ hscTypecheckRename env summary parsed
  let tcg = noInlineTypecheck tcg'
  desugared <- liftIO $ hscDesugar env summary tcg
  -- simplified <- liftIO $ hscSimplify env [] desugared
  return $ (mg_binds desugared, newDflags)
 where
  makeDynFlags dflags =
    let newDynFlags =
          dflags
            { ghcLink = NoLink
            , ghcMode = CompManager
            , backend = interpreterBackend
            , verbosity = 0
            , debugLevel = 0
            }
     in case forSyDePath of
          Just path ->
            newDynFlags
              { packageDBFlags = [PackageDB $ PkgDbPath $ path]
              , packageFlags = [ExposePackage "forsyde-atom" (PackageArg "forsyde-atom") (ModRenaming True [])]
              }
          Nothing -> newDynFlags

{- | Updates all bindings within the function called `system` and adds NOINLINE
pragmas. Prevents the pre optimisier run during desugaring from inlining
bindings relating to variables and functions within the compiled netlist.

Solution is inspired by discussions from the GHC API issue:
https://gitlab.haskell.org/ghc/ghc/-/issues/24386
-}
noInlineTypecheck :: TcGblEnv -> TcGblEnv
noInlineTypecheck tcg = tcg {tcg_binds = noInline (tcg_binds tcg)}
  where
    noInline :: (Data a) => a -> a
    noInline =
      gmapT
        ( noInline
            `extT` noInlineBinds
            `extT` noInlinePat
            `extT` noInlineExpr
        )

    noInlineId :: Id -> Id
    noInlineId var = var `setInlinePragma` neverInlinePragma

    noInlineBinds :: HsBind GhcTc -> HsBind GhcTc
    noInlineBinds bind = case bind of
      VarBind {var_id = var, var_rhs = rhs} ->
        bind {var_id = noInlineId var, var_rhs = noInline rhs}
      FunBind {fun_id = var, fun_matches = matches} ->
        bind {fun_id = noInlineId <$> var, fun_matches = noInline matches}
      PatBind {pat_lhs = lhs, pat_rhs = rhs} ->
        bind {pat_lhs = noInline lhs, pat_rhs = noInline rhs}
      XHsBindsLR absBinds ->
        XHsBindsLR (noInlineAbsBinds absBinds)
      _ -> bind

    noInlinePat :: Pat GhcTc -> Pat GhcTc
    noInlinePat pattern = case pattern of
      VarPat ext var -> VarPat ext (noInlineId <$> var)
      _ -> gmapT noInline pattern

    noInlineExpr :: HsExpr GhcTc -> HsExpr GhcTc
    noInlineExpr expr = case expr of
      HsCase x scrutiny matches ->
        HsCase x (noInline scrutiny) (noInline matches)
      HsLet x binds inner ->
        HsLet x (noInline binds) (noInline inner)
      _ -> gmapT noInline expr

    noInlineAbsBinds :: AbsBinds -> AbsBinds
    noInlineAbsBinds absBinds@AbsBinds {abs_binds = binds, abs_exports = exports} =
      absBinds
        { abs_binds = fmap skipFirstHsBind <$> binds,
          abs_exports = map noInlineABE exports
        }
      where
        skipFirstHsBind :: HsBind GhcTc -> HsBind GhcTc
        skipFirstHsBind bind = case bind of
          XHsBindsLR b -> XHsBindsLR (noInlineAbsBinds b)
          _ -> gmapT noInline bind

        noInlineABE :: ABExport -> ABExport
        noInlineABE abe@ABE {abe_poly = poly, abe_mono = mono} =
          abe {abe_poly = noInlineId poly, abe_mono = noInlineId mono}
