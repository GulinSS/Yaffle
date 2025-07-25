module Core.Context.Data

import Core.Context
import Core.Context.Log
import Core.Evaluate

import Data.List
import Data.Maybe
import Libraries.Data.WithDefault

-- If a name appears more than once in an argument list, only the first is
-- considered a parameter
dropReps : List (Maybe (Term vars)) -> List (Maybe (Term vars))
dropReps [] = []
dropReps {vars} (Just (Local fc x p) :: xs)
    = Just (Local fc x p) :: assert_total (dropReps (map toNothing xs))
  where
    toNothing : Maybe (Term vars) -> Maybe (Term vars)
    toNothing tm@(Just (Local _ v' _))
        = if x == v' then Nothing else tm
    toNothing tm = tm
dropReps (x :: xs) = x :: dropReps xs

updateParams : {auto _ : Ref Ctxt Defs} -> {vars : _} ->
               Maybe (List (Maybe (Term vars))) ->
                  -- arguments to the type constructor which could be
                  -- parameters
                  -- Nothing, as an argument, means this argument can't
                  -- be a parameter position
               List (Term vars) ->
                  -- arguments to an application
               Core (List (Maybe (Term vars)))
updateParams Nothing args = dropReps <$> traverse couldBeParam args
  where
    couldBeParam : Term vars -> Core (Maybe (Term vars))
    couldBeParam tm = pure $ case !(etaContract tm) of
      Local fc v p => Just (Local fc v p)
      _ => Nothing
updateParams (Just args) args' = pure $ dropReps $ zipWith mergeArg args args'
  where
    mergeArg : Maybe (Term vars) -> Term vars -> Maybe (Term vars)
    mergeArg (Just (Local fc x p)) (Local _ y _)
        = if x == y then Just (Local fc x p) else Nothing
    mergeArg _ _ = Nothing

getPs : {auto _ : Ref Ctxt Defs} -> {vars : _} ->
        Maybe (List (Maybe (Term vars))) -> Name -> Term vars ->
        Core (Maybe (List (Maybe (Term vars))))
getPs acc tyn (Bind _ x (Pi _ _ _ ty) sc)
      = do scPs <- getPs (map (map (map weaken)) acc) tyn sc
           pure $ map (map shrink) scPs
  where
    shrink : Maybe (Term (vars :< x)) -> Maybe (Term vars)
    shrink Nothing = Nothing
    shrink (Just tm) = shrinkTerm tm (DropCons SubRefl)
getPs acc tyn tm
    = case getFnArgs tm of
           (Ref _ _ n, args) =>
              if n == tyn
                 then Just <$> updateParams acc args
                 else pure acc
           _ => pure acc

toPos : Maybe (List (Maybe a)) -> List Nat
toPos Nothing = []
toPos (Just ns) = justPos 0 ns
  where
    justPos : Nat -> List (Maybe a) -> List Nat
    justPos i [] = []
    justPos i (Just x :: xs) = i :: justPos (1 + i) xs
    justPos i (Nothing :: xs) = justPos (1 + i) xs

getConPs : {auto _ : Ref Ctxt Defs} -> {vars : _} ->
           Maybe (List (Maybe (Term vars))) -> Name -> Term vars ->
           Core (List Nat)
getConPs acc tyn (Bind _ x (Pi _ _ _ ty) sc)
    = do bacc <- getPs acc tyn ty
         getConPs (map (map (map weaken)) bacc) tyn sc
getConPs acc tyn (Bind _ x (Let _ _ v ty) sc)
    = getConPs acc tyn (subst v sc)
getConPs acc tyn tm = toPos <$> getPs acc tyn tm

paramPos : {auto _ : Ref Ctxt Defs} -> Name -> (dcons : List ClosedTerm) ->
           Core (Maybe (List Nat))
paramPos tyn [] = pure Nothing -- no constructor!
paramPos tyn dcons = do
  candidates <- traverse (getConPs Nothing tyn) dcons
  pure $ Just $ intersectAll candidates

export
addData : {auto c : Ref Ctxt Defs} ->
          SnocList Name -> Visibility -> Int -> DataDef -> Core Int
addData vars vis tidx (MkData (MkCon dfc tyn arity tycon) datacons)
    = do defs <- get Ctxt
         let allPos = allDet arity
         -- In case there are no constructors, all the positions are parameter positions!
         let paramPositions = fromMaybe allPos !(paramPos (Resolved tidx) (map type datacons))
         log "declare.data.parameters" 20 $
            "Positions of parameters for datatype" ++ show tyn ++
            ": [" ++ showSep ", " (map show paramPositions) ++ "]"
         let tydef = newDef dfc tyn top vars tycon (specified vis)
                            (TCon (MkTyConInfo paramPositions allPos []
                                               (map name datacons) Nothing
                                               False False) arity)
         (idx, gam') <- addCtxt tyn tydef (gamma defs)
         gam'' <- addDataConstructors 0 datacons gam'
         put Ctxt ({ gamma := gam'' } defs)
         pure idx
  where
    allDet : Nat -> List Nat
    allDet Z = []
    allDet (S k) = [0..k]

    conVisibility : Visibility -> Visibility
    conVisibility Export = Private
    conVisibility x = x

    readQs : NF [<] -> Core (List RigCount)
    readQs (VBind fc x (Pi _ c _ _) sc)
        = do rest <- readQs !(expand !(sc (pure (VErased fc Placeholder))))
             pure (c :: rest)
    readQs _ = pure []

    addDataConstructors : (tag : Int) -> List Constructor ->
                          Context -> Core Context
    addDataConstructors tag [] gam = pure gam
    addDataConstructors tag (MkCon fc n a ty :: cs) gam
        = do qs <- readQs !(expand !(nf [<] ty))
             let condef = newDef fc n top vars ty (specified $ conVisibility vis)
                                 (DCon (defaultDataConInfo qs) tag a)
             -- Check 'n' is undefined
             Nothing <- lookupCtxtExact n gam
                 | Just gdef => throw (AlreadyDefined fc n)
             (idx, gam') <- addCtxt n condef gam
             addDataConstructors (tag + 1) cs gam'
