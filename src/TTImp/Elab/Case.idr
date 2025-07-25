module TTImp.Elab.Case

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Metadata
import Core.Evaluate
import Core.Unify
import Core.TT

import TTImp.Elab.Check
import TTImp.Elab.Delayed
import TTImp.Elab.ImplicitBind
import TTImp.Elab.Utils
import TTImp.ProcessFnOpt
import TTImp.TTImp
import TTImp.Utils

import Data.List
import Data.Maybe
import Data.String
import Libraries.Data.NameMap
import Libraries.Data.WithDefault

%default covering

findLater : (x : Name) -> (newer : SnocList Name) -> Var (older :< x ++ newer)
findLater x [<] = MkVar First
findLater {older} x (xs :< _)
    = let MkVar p = findLater {older} x xs in
          MkVar (Later p)

toRig1 : {idx : Nat} -> (0 p : IsVar nm idx vs) -> Env Term vs -> Env Term vs
toRig1 First (bs :< b)
    = if isErased (multiplicity b)
         then bs :< setMultiplicity b linear
         else bs :< b
toRig1 (Later p) (bs :< b) = toRig1 p bs :< b

toRig0 : {idx : Nat} -> (0 p : IsVar nm idx vs) -> Env Term vs -> Env Term vs
toRig0 First (bs :< b) = bs :< setMultiplicity b erased
toRig0 (Later p) (bs :< b) = toRig0 p bs :< b

-- When we abstract over the evironment, pi needs to be explicit
explicitPi : Env Term vs -> Env Term vs
explicitPi (env :< Pi fc c _ ty)  = explicitPi env :< Pi fc c Explicit ty
explicitPi (env :< b) = explicitPi env :< b
explicitPi [<] = [<]

allow : Maybe (Var vs) -> Env Term vs -> Env Term vs
allow Nothing env = env
allow (Just (MkVar p)) env = toRig1 p env

-- If the name is used elsewhere, update its multiplicity so it's
-- not required to be used in the case block
updateMults : List (Var vs) -> Env Term vs -> Env Term vs
updateMults [] env = env
updateMults (MkVar p :: us) env = updateMults us (toRig0 p env)

findImpsIn : {vars : _} ->
             FC -> Env Term vars -> List (Name, Term vars) -> Term vars ->
             Core ()
findImpsIn fc env ns (Bind _ n b@(Pi _ _ Implicit ty) sc)
    = findImpsIn fc (env :< b)
                 ((n, weaken ty) :: map (\x => (fst x, weaken (snd x))) ns)
                 sc
findImpsIn fc env ns (Bind _ n b sc)
    = findImpsIn fc (env :< b)
                 (map (\x => (fst x, weaken (snd x))) ns)
                 sc
findImpsIn fc env ns ty
    = when (not (isNil ns)) $
           throw (TryWithImplicits fc env (reverse ns))

findScrutinee : {vs : _} ->
                Env Term vs -> RawImp -> Maybe (Var vs)
findScrutinee {vs = _ :< n'} (bs :< b) (IVar loc' n)
    = if n' == n && not (isLet b)
         then Just (MkVar First)
         else do MkVar p <- findScrutinee bs (IVar loc' n)
                 Just (MkVar (Later p))
findScrutinee _ _ = Nothing

getNestData : (Name, (Maybe Name, List (Var vars), a)) ->
              (Name, Maybe Name, List (Var vars))
getNestData (n, (mn, enames, _)) = (n, mn, enames)

bindCaseLocals : FC -> List (Name, Maybe Name, List (Var vars)) ->
                 List (Name, Name)-> RawImp -> RawImp
bindCaseLocals fc [] args rhs = rhs
bindCaseLocals fc ((n, mn, envns) :: rest) argns rhs
    = -- trace ("Case local " ++ show (n,mn,envns) ++ " from " ++ show argns) $
        ICaseLocal fc n (fromMaybe n mn)
                 (map getNameFrom envns)
                 (bindCaseLocals fc rest argns rhs)
  where
    getArg : List (Name, Name) -> Nat -> Maybe Name
    getArg [] _ = Nothing
    getArg ((_, x) :: xs) Z = Just x
    getArg (x :: xs) (S k) = getArg xs k

    getNameFrom : Var vars -> Name
    getNameFrom (MkVar {i} _)
        = case getArg argns i of
               Nothing => n
               Just n' => n'

export
caseBlock : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            {auto e : Ref EST (EState vars)} ->
            RigCount ->
            ElabInfo -> FC ->
            NestedNames vars ->
            Env Term vars ->
            List FnOpt ->
            RawImp -> -- original scrutinee
            Term vars -> -- checked scrutinee
            Term vars -> -- its type
            RigCount -> -- its multiplicity
            List ImpClause -> Maybe (Glued vars) ->
            Core (Term vars, Glued vars)
caseBlock {vars} rigc elabinfo fc nest env opts scr scrtm scrty caseRig alts expected
    = do -- TODO (or to decide): Blodwen allowed ambiguities in the scrutinee
         -- to be delayed, but now I think it's better to have simpler
         -- resolution rules, and not delay

         est <- get EST
         fullImps <- getToBind fc (elabMode elabinfo)
                               (implicitMode elabinfo) env []
         log "elab.case" 5 $ "Doing a case under unbound implicits " ++ show fullImps

         scrn <- genVarName "scr"
         casen <- genCaseName !(prettyName !(toFullNames (Resolved (defining est))))

         -- Update environment so that linear bindings which were used
         -- (esp. in the scrutinee!) are set to 0 in the case type
         let env = updateMults (linearUsed est) env
         defs <- get Ctxt
         parentDef <- lookupCtxtExact (Resolved (defining est)) (gamma defs)
         let vis = specified $ case parentDef of
                                    Just gdef =>
                                         if collapseDefault (visibility gdef) == Public
                                            then Public
                                            else Private
                                    Nothing => Public

         -- if the scrutinee is ones of the arguments in 'env' we should
         -- split on that, rather than adding it as a new argument
         let splitOn = findScrutinee env scr

         caseretty_in <- case expected of
                           Just ty => quote env ty
                           _ =>
                              do nmty <- genName "caseTy"
                                 u <- uniVar fc
                                 metaVar fc erased env nmty (TType fc u)

         u <- uniVar fc
         (caseretty, _) <- bindImplicits fc (implicitMode elabinfo) defs env
                                         fullImps caseretty_in (TType fc u)
         let casefnty
               = abstractFullEnvType fc (allow splitOn (explicitPi env))
                            (maybe (Bind fc scrn (Pi fc caseRig Explicit scrty)
                                       (weaken caseretty))
                                   (const caseretty) splitOn)
         (erasedargs, _) <- findErased casefnty

         logEnv "elab.case" 10 "Case env" env
         logTermNF "elab.case" 2 ("Case function type: " ++ show casen) [<] casefnty
         traverse_ addToSave (keys (getMetas casefnty))

         -- If we've had to add implicits to the case type (because there
         -- were unbound implicits) then we're in a bit of a mess. Easiest
         -- way out is to throw an error and try again with the implicits
         -- actually bound! This is rather hacky, but a lot less fiddly than
         -- the alternative of fixing up the environment
         when (not (isNil fullImps)) $ findImpsIn fc [<] [] casefnty
         cidx <- addDef casen ({ eraseArgs := erasedargs }
                                (newDef fc casen (if isErased rigc then erased else top)
                                      [<] casefnty vis None))

         traverse_ (processFnOpt fc False casen) opts
         -- set the totality of the case block to be the same as that
         -- of the parent function
         let tot = fromMaybe PartialOK $ do findSetTotal (flags !parentDef)
         log "elab.case" 5 $
           unwords [ "Setting totality requirement for", show casen
                   , "to", show tot]
         setFlag fc (Resolved cidx) (SetTotal tot)
         let caseRef : Term vars = Ref fc Func (Resolved cidx)

         let applyEnv = applyToFull fc caseRef env
         let appTm : Term vars
                   = maybe (Bind fc (MN "sc" 0)
                                 (Let fc caseRig scrtm scrty)
                                 (App fc (weaken applyEnv) caseRig
                                         (Local fc _ First)))
                           (const applyEnv)
                           splitOn

         let alts' = map (updateClause casen splitOn nest env) alts
         log "elab.case" 2 $ "Nested: " ++ show (map getNestData (names nest))
         log "elab.case" 2 $ "Generated alts: " ++ show alts'
         logTermNF "elab.case" 2 "Case application" env appTm

         -- Start with empty nested names, since we've extended the rhs with
         -- ICaseLocal so they'll get rebuilt with the right environment
         let nest' = MkNested []
         ust <- get UST
         -- We don't want to keep rechecking delayed elaborators in the
         -- case block, because they're not going to make progress until
         -- we come out again, so save them
         let olddelayed = delayedElab ust
         put UST ({ delayedElab := [] } ust)
         processDecl [InCase] nest' [<] (IDef fc casen alts')

         -- Set the case block to always reduce, so we get the core 'Case'
         updateDef casen
            (\d => case d of
                        Function fi ct rt cs =>
                          Just (Function ({ alwaysReduce := True } fi) ct rt cs)
                        _ => Nothing)

         ust <- get UST
         put UST ({ delayedElab := olddelayed } ust)

         pure (appTm, !(nf env caseretty))
  where
    mkLocalEnv : Env Term vs -> Env Term vs
    mkLocalEnv [<] = [<]
    mkLocalEnv (bs :< b)
        = let b' = if isLinear (multiplicity b)
                      then setMultiplicity b erased
                      else b in
              mkLocalEnv bs :< b'

    -- Return the original name in the environment, and what it needs to be
    -- called in the case block. We need to mapping to build the ICaseLocal
    -- so that it applies to the right original variable
    getBindName : Int -> Name -> List Name -> (Name, Name)
    getBindName idx n@(UN un) vs
       = if n `elem` vs then (n, MN (displayUserName un) idx) else (n, n)
    getBindName idx n vs
       = if n `elem` vs then (n, MN "_cn" idx) else (n, n)

    -- Returns a list of names that nestednames should be applied to, mapped
    -- to what the name has become in the case block, and a list of terms for
    -- the LHS of the case to be applied to.
    addEnv : {vs : _} ->
             Int -> Env Term vs -> List Name -> (List (Name, Name), List RawImp)
    addEnv idx [<] used = ([], [])
    addEnv idx {vs = vs :< v} (bs :< b) used
        = let n = getBindName idx v used
              (ns, rest) = addEnv (idx + 1) bs (snd n :: used)
              ns' = n :: ns in
              (ns', IAs fc EmptyFC UseLeft (snd n) (Implicit fc True) :: rest)

    -- Replace a variable in the argument list; if the reference is to
    -- a variable kept in the outer environment (therefore not an argument
    -- in the list) don't consume it
    replace : (idx : Nat) -> RawImp -> List RawImp -> List RawImp
    replace Z lhs (old :: xs)
       = let lhs' = case old of
                         IAs loc' nameLoc' side n _ => IAs loc' nameLoc' side n lhs
                         _ => lhs in
             lhs' :: xs
    replace (S k) lhs (x :: xs)
        = x :: replace k lhs xs
    replace _ _ xs = xs

    mkSplit : Maybe (Var vs) ->
              RawImp -> List RawImp ->
              List RawImp
    mkSplit Nothing lhs args = reverse (lhs :: args)
    mkSplit (Just (MkVar {i} prf)) lhs args
        = reverse (replace i lhs args)

    -- Names used in the pattern we're matching on, so don't bind them
    -- in the generated case block
    usedIn : RawImp -> List Name
    usedIn (IBindVar _ n) = [UN $ Basic n]
    usedIn (IApp _ f a) = usedIn f ++ usedIn a
    usedIn (IAs _ _ _ n a) = n :: usedIn a
    usedIn (IAlternative _ _ alts) = concatMap usedIn alts
    usedIn _ = []

    -- Get a name update for the LHS (so that if there's a nested data declaration
    -- the constructors are applied to the environment in the case block)
    nestLHS : FC -> (Name, (Maybe Name, List (Var vars), a)) -> (Name, RawImp)
    nestLHS fc (n, (mn, ns, t))
        = (n, apply (IVar fc (fromMaybe n mn))
                    (map (const (Implicit fc False)) ns))

    applyNested : NestedNames vars -> RawImp -> RawImp
    applyNested nest lhs
        = let fc = getFC lhs in
              substNames [] (map (nestLHS fc) (names nest)) lhs

    updateClause : Name -> Maybe (Var vars) ->
                   NestedNames vars ->
                   Env Term vars -> ImpClause -> ImpClause
    updateClause casen splitOn nest env (PatClause loc' lhs rhs)
        = let (ns, args) = addEnv 0 env (usedIn lhs)
              args' = mkSplit splitOn lhs args
              lhs' = apply (IVar loc' casen) args' in
              PatClause loc' (applyNested nest lhs')
                        (bindCaseLocals loc' (map getNestData (names nest))
                                        ns rhs)
    -- With isn't allowed in a case block but include for completeness
    updateClause casen splitOn nest env (WithClause loc' lhs rig wval prf flags cs)
        = let (_, args) = addEnv 0 env (usedIn lhs)
              args' = mkSplit splitOn lhs args
              lhs' = apply (IVar loc' casen) args' in
              WithClause loc' (applyNested nest lhs') rig wval prf flags cs
    updateClause casen splitOn nest env (ImpossibleClause loc' lhs)
        = let (_, args) = addEnv 0 env (usedIn lhs)
              args' = mkSplit splitOn lhs args
              lhs' = apply (IVar loc' casen) args' in
              ImpossibleClause loc' (applyNested nest lhs')

export
checkCase : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            {auto e : Ref EST (EState vars)} ->
            RigCount -> ElabInfo ->
            NestedNames vars -> Env Term vars ->
            FC -> List FnOpt -> (scr : RawImp) -> (ty : RawImp) -> List ImpClause ->
            Maybe (Glued vars) ->
            Core (Term vars, Glued vars)
checkCase rig elabinfo nest env fc opts scr scrty_in alts exp
    = delayElab fc rig elabinfo env exp CaseBlock $
        do scrty_exp <- case scrty_in of
                             Implicit _ _ => guessScrType alts
                             _ => pure scrty_in
           u <- uniVar fc
           (scrtyv, scrtyt) <- check erased elabinfo nest env scrty_exp
                                     (Just (VType fc u))
           logTerm "elab.case" 10 "Expected scrutinee type" scrtyv
           -- Try checking at the given multiplicity; if that doesn't work,
           -- try checking at Rig1 (meaning that we're using a linear variable
           -- so the scrutinee should be linear)
           let chrig = if isErased rig then erased else top
           log "elab.case" 5 $ "Checking " ++ show scr ++ " at " ++ show chrig

           (scrtm_in, gscrty, caseRig) <- handle
              (do c <- runDelays (const True) $ check chrig elabinfo nest env scr (Just !(nf env scrtyv))
                  pure (fst c, snd c, chrig))
            $ \case
                e@(LinearMisuse _ _ r _)
                  => branchOne
                     (do c <- runDelays (const True) $ check linear elabinfo nest env scr
                              (Just !(nf env scrtyv))
                         pure (fst c, snd c, linear))
                     (throw e)
                     r
                e => throw e

           scrty <- quote env gscrty
           logTermNF "elab.case" 5 "Scrutinee type" env scrty
           defs <- get Ctxt
           checkConcrete !(expand !(nf env scrty))
           caseBlock rig elabinfo fc nest env opts scr scrtm_in scrty caseRig alts exp
  where
    -- For the moment, throw an error if we haven't been able to work out
    -- the type of the case scrutinee, because we'll need it to build the
    -- type of the case block. But (TODO) consider delaying on failure?
    checkConcrete : NF vs -> Core ()
    checkConcrete (VMeta{})
        = throw (GenericMsg fc "Can't infer type for case scrutinee")
    checkConcrete _ = pure ()

    applyTo : Defs -> RawImp -> NF [<] -> Core RawImp
    applyTo defs ty (VBind fc _ (Pi _ _ Explicit _) sc)
        = applyTo defs (IApp fc ty (Implicit fc False))
               !(expand !(sc (pure (VErased fc Placeholder))))
    applyTo defs ty (VBind _ x (Pi _ _ _ _) sc)
        = applyTo defs (INamedApp fc ty x (Implicit fc False))
               !(expand !(sc (pure (VErased fc Placeholder))))
    applyTo defs ty _ = pure ty

    -- Get the name and type of the family the scrutinee is in
    getRetTy : Defs -> NF [<] -> Core (Maybe (Name, NF [<]))
    getRetTy defs (VBind fc _ (Pi _ _ _ _) sc)
        = getRetTy defs !(expand !(sc (pure (VErased fc Placeholder))))
    getRetTy defs (VTCon _ n arity _)
        = do Just ty <- lookupTyExact n (gamma defs)
                  | Nothing => pure Nothing
             pure (Just (n, !(expand !(nf [<] ty))))
    getRetTy _ _ = pure Nothing

    -- Guess a scrutinee type by looking at the alternatives, so that we
    -- have a hint for building the case type
    guessScrType : List ImpClause -> Core RawImp
    guessScrType [] = pure $ Implicit fc False
    guessScrType (PatClause _ x _ :: xs)
        = case getFn x of
               IVar _ n =>
                  do defs <- get Ctxt
                     [(n', (_, ty))] <- lookupTyName n (gamma defs)
                         | _ => guessScrType xs
                     Just (tyn, tyty) <- getRetTy defs !(expand !(nf [<] ty))
                         | _ => guessScrType xs
                     applyTo defs (IVar fc tyn) tyty
               _ => guessScrType xs
    guessScrType (_ :: xs) = guessScrType xs
