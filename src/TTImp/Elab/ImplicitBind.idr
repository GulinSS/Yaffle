module TTImp.Elab.ImplicitBind
-- Machinery needed for handling implicit name bindings (either pattern
-- variables or unbound implicits as type variables)

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Coverage
import Core.Env
import Core.Metadata
import Core.Evaluate
import Core.Unify
import Core.Unify.State
import Core.TT

import TTImp.Elab.Check
import TTImp.Elab.Delayed
import TTImp.TTImp

import Data.List
import Data.Vect
import Libraries.Data.NameMap

%default covering

-- Make a hole for an unbound implicit in the outer environment
export
mkOuterHole : {vars : _} ->
              {auto e : Ref EST (EState vars)} ->
              {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              FC -> RigCount ->
              Name -> Env Term vars -> Maybe (Glued vars) ->
              Core (Term vars, Term vars)
mkOuterHole loc rig n topenv (Just expty_in)
    = do est <- get EST
         let sub = subEnv est
         expected <- quote topenv expty_in
         case shrinkTerm expected sub of
              -- Can't shrink so rely on unification with expected type later
              Nothing => mkOuterHole loc rig n topenv Nothing
              Just exp' =>
                  do let env = outerEnv est
                     tm <- implBindVar loc rig env n exp'
                     pure (embedSub sub tm, embedSub sub exp')
mkOuterHole loc rig n topenv Nothing
    = do est <- get EST
         let sub = subEnv est
         let env = outerEnv est
         nm <- genName ("type_of_" ++ nameRoot n)
         u <- uniVar loc
         ty <- metaVar loc erased env nm (TType loc u)
         log "elab.implicits" 10 $ "Made metavariable for type of " ++ show n ++ ": " ++ show nm
         put EST (addBindIfUnsolved nm rig Explicit topenv (embedSub sub ty) (TType loc u) est)
         tm <- implBindVar loc rig env n ty
         pure (embedSub sub tm, embedSub sub ty)

-- Make a hole standing for the pattern variable, which we'll instantiate
-- with a bound pattern variable later.
-- Returns the hole term, its expected type (this is the type we'll use when
-- we see the name later) and the type the binder will need to be when we
-- instantiate it.
export
mkPatternHole : {vars' : _} ->
                {auto e : Ref EST (EState vars')} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                FC -> RigCount -> Name -> Env Term vars' -> BindMode ->
                Maybe (Glued vars') ->
                Core (Term vars', Term vars', Term vars')
mkPatternHole loc rig n env (PI _) exp
    = do (tm, exp) <- mkOuterHole loc rig n env exp
         pure (tm, exp, exp)
mkPatternHole {vars'} loc rig n topenv imode (Just expty_in)
    = do est <- get EST
         let sub = subEnv est
         let env = outerEnv est
         expected <- quote topenv expty_in
         case bindInner topenv expected sub of
              Nothing => mkPatternHole loc rig n topenv imode Nothing
              Just exp' =>
                  do tm <- implBindVar loc rig env n exp'
                     pure (apply loc (embedSub sub tm) (mkArgs topenv sub),
                           expected,
                           embedSub sub exp')
  where
    mkArgs : {vs : _} -> Env Term vs -> SubVars newvars vs ->
             List (RigCount, Term vs)
    mkArgs env SubRefl = []
    mkArgs (env :< b) (DropCons p)
        = (multiplicity b, Local loc 0 First) ::
             map (\ (c, t) => (c, weaken t)) (mkArgs env p)
    mkArgs _ _ = []

    -- This is for the specific situation where we're pattern matching on
    -- function types, which is realistically the only time we'll legitimately
    -- encounter a type variable under a binder
    bindInner : {vs : _} ->
                Env Term vs -> Term vs -> SubVars newvars vs ->
                Maybe (Term newvars)
    bindInner env ty SubRefl = Just ty
    bindInner {vs = _ :< x} (env :< b) ty (DropCons p)
        = bindInner env (Bind loc x b ty) p
    bindInner _ _ _ = Nothing

mkPatternHole loc rig n env _ _
    = throw (GenericMsg loc ("Unknown type for pattern variable " ++ show n))

export
normaliseType : {auto c : Ref Ctxt Defs} ->
                {free : _} ->
                Env Term free -> Term free -> Core (Term free)
normaliseType = normaliseHoles

-- For any of the 'bindIfUnsolved' - these were added as holes during
-- elaboration, but are as yet unsolved, so create a pattern variable for
-- them and unify.
-- (This is only when we're in a mode that allows unbound implicits)
bindUnsolved : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto e : Ref EST (EState vars)} ->
               {auto u : Ref UST UState} ->
               FC -> ElabMode -> BindMode -> Core ()
bindUnsolved fc elabmode NONE = pure ()
bindUnsolved {vars} fc elabmode _
    = do est <- get EST
         defs <- get Ctxt
         let bifs = bindIfUnsolved est
         log "elab.implicits" 5 $ "Bindable unsolved implicits: " ++ show (map fst bifs)
         traverse_ (mkImplicit defs (outerEnv est) (subEnv est)) (bindIfUnsolved est)
  where
    makeBoundVar : {outer, vs : _} ->
                   Name -> RigCount -> PiInfo (Term vs) -> Env Term outer ->
                   SubVars outer vs -> SubVars outer vars ->
                   Term vs -> Core (Term vs)
    makeBoundVar n rig p env sub subvars expected
        = case shrinkTerm expected sub of
               Nothing => do tmn <- toFullNames expected
                             throw (GenericMsg fc ("Can't bind implicit " ++ show n ++ " of type " ++ show tmn))
               Just exp' =>
                    do impn <- genVarName (nameRoot n)
                       tm <- metaVar fc rig env impn exp'
                       let p' : PiInfo (Term vars) = forgetDef p
                       update EST { toBind $= ((impn, NameBinding rig p'
                                                        (embedSub subvars tm)
                                                        (embedSub subvars exp')) ::) }
                       pure (embedSub sub tm)

    mkImplicit : {outer : _} ->
                 Defs -> Env Term outer -> SubVars outer vars ->
                 (Name, RigCount, (vars' **
                     (Env Term vars', PiInfo (Term vars'), Term vars', Term vars', SubVars outer vars'))) ->
                 Core ()
    mkImplicit defs outerEnv subEnv (n, rig, (vs ** (env, p, tm, exp, sub)))
        = do Just (Hole _ _) <- lookupDefExact n (gamma defs)
                  | _ => pure ()
             bindtm <- makeBoundVar n rig p outerEnv
                                    sub subEnv
                                    !(normaliseHoles env exp)
             logTerm "elab.implicits" 5 ("Added unbound implicit") bindtm
             ignore $ unify (case elabmode of
                         InLHS _ => inLHS
                         _ => inTerm)
                   fc env tm bindtm

swapIsVarH : {idx : Nat} -> (0 p : IsVar nm idx (xs :< y :< x)) ->
             Var (xs :< x :< y)
swapIsVarH First = MkVar (Later First)
swapIsVarH (Later p) = swapP p -- it'd be nice to do this all at the top
                               -- level, but that will need an improvement
                               -- in erasability checking
  where
    swapP : forall name . {idx : _} -> (0 p : IsVar name idx (xs :< y)) ->
            Var (xs :< x :< y)
    swapP First = MkVar First
    swapP (Later x) = MkVar (Later (Later x))

swapIsVar : (vs : SnocList Name) ->
            {idx : Nat} -> (0 p : IsVar nm idx (xs :< y :< x ++ vs)) ->
            Var (xs :< x :< y ++ vs)
swapIsVar [<] prf = swapIsVarH prf
swapIsVar (xs :< x) First = MkVar First
swapIsVar (xs :< x) (Later p)
    = let MkVar p' = swapIsVar xs p in MkVar (Later p')

swapVars : {vs : SnocList Name} ->
           Term (ys :< y :< x ++ vs) ->
           Term (ys :< x :< y ++ vs)
swapVars (Local fc idx p)
    = let MkVar p' = swapIsVar _ p in Local fc _ p'
swapVars (Ref fc x name) = Ref fc x name
swapVars (Meta fc n i xs)
    = Meta fc n i (map (\ (c, t) => (c, swapVars t)) xs)
swapVars {vs} (Bind fc x b scope)
    = Bind fc x (map swapVars b) (swapVars {vs = vs :< x} scope)
swapVars (App fc fn c arg) = App fc (swapVars fn) c (swapVars arg)
swapVars (As fc s as pat) = As fc s (swapVars as) (swapVars pat)
swapVars (Case fc ct c sc scty alts)
    = Case fc ct c (swapVars sc) (swapVars scty) (map swapAlt alts)
  where
    swapForced : {vs : _} -> forall ys, x, y .
                 (Var (ys :< y :< x ++ vs), Term (ys :< y :< x ++ vs)) ->
                 (Var (ys :< x :< y ++ vs), Term (ys :< x :< y ++ vs))
    swapForced (MkVar v, tm)
        = (swapIsVar _ v, swapVars tm)

    swapScope : {vs : _} -> forall ys, x, y .
              CaseScope (ys :< y :< x ++ vs) ->
              CaseScope (ys :< x :< y ++ vs)
    swapScope (RHS fs tm) = RHS (map swapForced fs) (swapVars tm)
    swapScope {vs} (Arg c x sc) = Arg c x (swapScope {vs = vs :< x} sc)

    swapAlt : {vs : _} -> forall ys, x, y .
              CaseAlt (ys :< y :< x ++ vs) ->
              CaseAlt (ys :< x :< y ++ vs)
    swapAlt (ConCase fc n t sc) = ConCase fc n t (swapScope sc)
    swapAlt {vs} (DelayCase fc t a tm)
        = DelayCase fc t a (swapVars {vs = vs :< t :< a} tm)
    swapAlt (ConstCase fc c tm) = ConstCase fc c (swapVars tm)
    swapAlt (DefaultCase fc tm) = DefaultCase fc (swapVars tm)

swapVars (TDelayed fc x tm) = TDelayed fc x (swapVars tm)
swapVars (TDelay fc x ty tm) = TDelay fc x (swapVars ty) (swapVars tm)
swapVars (TForce fc r tm) = TForce fc r (swapVars tm)
swapVars (PrimVal fc c) = PrimVal fc c
swapVars (PrimOp fc f args) = PrimOp fc f (map swapVars args)
swapVars (Erased fc Impossible) = Erased fc Impossible
swapVars (Erased fc Placeholder) = Erased fc Placeholder
swapVars (Erased fc (Dotted t)) = Erased fc $ Dotted (swapVars t)
swapVars (Unmatched fc s) = Unmatched fc s
swapVars (TType fc u) = TType fc u

-- Push an explicit pi binder as far into a term as it'll go. That is,
-- move it under implicit binders that don't depend on it, and stop
-- when hitting any non-implicit binder
push : {vs : _} ->
       FC -> (n : Name) -> Binder (Term vs) -> Term (vs :< n) -> Term vs
push ofc n b tm@(Bind fc (PV x i) (Pi fc' c Implicit ty) sc) -- only push past 'PV's
    = case shrinkTerm ty (DropCons SubRefl) of
           Nothing => -- needs explicit pi, do nothing
                      Bind ofc n b tm
           Just ty' => Bind fc (PV x i) (Pi fc' c Implicit ty')
                            (push ofc n (map weaken b) (swapVars {vs = [<]} sc))
push ofc n b tm = Bind ofc n b tm

-- Move any implicit arguments as far to the left as possible - this helps
-- with curried applications
-- We only do this for variables named 'PV', since they are the unbound
-- implicits, and we don't want to move any given by the programmer
liftImps : {vars : _} ->
           BindMode -> (Term vars, Term vars) -> (Term vars, Term vars)
liftImps (PI _) (tm, TType fc u) = (liftImps' tm, TType fc u)
  where
    liftImps' : {vars : _} ->
                Term vars -> Term vars
    liftImps' (Bind fc (PV n i) b@(Pi _ _ Implicit _) sc)
        = Bind fc (PV n i) b (liftImps' sc)
    liftImps' (Bind fc n b@(Pi _ _ _ _) sc)
        = push fc n b (liftImps' sc)
    liftImps' tm = tm
liftImps _ x = x

-- Bind implicit arguments, returning the new term and its updated type
bindImplVars : FC -> BindMode ->
               Env Term vars ->
               List (Name, ImplBinding vars) ->
               Term vars -> Term vars -> (Term vars, Term vars)
bindImplVars fc NONE env imps_in scope scty = (scope, scty)
bindImplVars {vars} fc mode env imps_in scope scty
    = let imps = map (\ (x, bind) => (tidyName x, x, bind)) imps_in in
          getBinds imps None scope scty
  where
    -- Turn the pattern variable name into the user's original choice,
    -- now that there's no longer a risk of clash
    tidyName : Name -> Name
    tidyName (NS _ n) = tidyName n
    tidyName (PV n _) = tidyName n
    tidyName (Nested n inner) = tidyName inner
    tidyName n = n

    getBinds : (imps : List (Name, Name, ImplBinding vs)) ->
               Bounds new -> (tm : Term vs) -> (ty : Term vs) ->
               (Term (vs ++ new), Term (vs ++ new))
    getBinds [] bs tm ty = (refsToLocals bs tm, refsToLocals bs ty)
    getBinds {new} ((n, metan, NameBinding c p _ bty) :: imps) bs tm ty
        = let (tm', ty') = getBinds imps (Add n metan bs) tm ty
              bty' = refsToLocals bs bty in
              case mode of
                   PI c =>
                      (Bind fc _ (Pi fc c Implicit bty') tm',
                       TType fc (MN "top" 0))
                   _ =>
                      (Bind fc _ (PVar fc c (map (weakenNs (sizeOf bs)) p) bty') tm',
                       Bind fc _ (PVTy fc c bty') ty')
    getBinds ((n, metan, AsBinding c _ _ bty bpat) :: imps) bs tm ty
        = let (tm', ty') = getBinds imps (Add n metan bs) tm ty
              bty' = refsToLocals bs bty
              bpat' = refsToLocals bs bpat in
              (Bind fc _ (PLet fc c bpat' bty') tm',
               Bind fc _ (PLet fc c bpat' bty') ty')

export
bindImplicits : {auto c : Ref Ctxt Defs} ->
                {vars : _} ->
                FC -> BindMode ->
                Defs -> Env Term vars ->
                List (Name, ImplBinding vars) ->
                Term vars -> Term vars -> Core (Term vars, Term vars)
bindImplicits fc NONE defs env hs tm ty = pure (tm, ty)
bindImplicits {vars} fc mode defs env hs tm ty
   = pure $ liftImps mode $ bindImplVars fc mode env hs tm ty

export
implicitBind : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               Name -> Core ()
implicitBind n
    = do defs <- get Ctxt
         Just (Hole _ _) <- lookupDefExact n (gamma defs)
             | _ => pure ()
         updateDef n (const (Just ImpBind))
         removeHoleName n

-- 'toBind' are the names which are to be implicitly bound (pattern bindings and
-- unbound implicits).
-- Return the names in the order they should be bound: i.e. respecting
-- dependencies between types, and putting @-patterns last because their
-- value is determined from the patterns
export
getToBind : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto e : Ref EST (EState vars)} ->
            {auto u : Ref UST UState} ->
            FC -> ElabMode -> BindMode ->
            Env Term vars -> (excepts : List Name) ->
            Core (List (Name, ImplBinding vars))
getToBind fc elabmode NONE env excepts
    = pure [] -- We should probably never get here, but for completeness...
getToBind {vars} fc elabmode impmode env excepts
    = do solveConstraints (case elabmode of
                                InLHS _ => inLHS
                                _ => inTerm) Normal
         bindUnsolved fc elabmode impmode
         solveConstraints (case elabmode of
                                InLHS _ => inLHS
                                _ => inTerm) Normal
         defs <- get Ctxt
         est <- get EST
         let tob = reverse $ filter (\x => not (fst x `elem` excepts)) $
                             toBind est
         -- Make sure all the hole names are normalised in the implicitly
         -- bound types, because otherwise we'll bind them too
         res <- normImps defs [] tob
         let hnames = map fst res
         -- Return then in dependency order
         let res' = depSort hnames res
         log "elab.implicits" 10 $ "Bound names: " ++ show res
         log "elab.implicits" 10 $ "Sorted: " ++ show res'
         pure res'
  where
    normBindingTy : Defs -> ImplBinding vars -> Core (ImplBinding vars)
    normBindingTy defs (NameBinding c p tm ty)
        = do case impmode of
                  COVERAGE => do tynf <- expand !(nf env ty)
                                 when !(isEmpty defs env tynf) $
                                    throw (InternalError "Empty pattern in coverage check")
                  _ => pure ()
             pure $ NameBinding c p tm !(normaliseType env ty)
    normBindingTy defs (AsBinding c p tm ty pat)
        = do case impmode of
                  COVERAGE => do tynf <- expand !(nf env ty)
                                 when !(isEmpty defs env tynf) $
                                    throw (InternalError "Empty pattern in coverage check")
                  _ => pure ()
             pure $ AsBinding c p tm !(normaliseType env ty)
                                     !(normaliseHoles env pat)

    normImps : Defs -> List Name -> List (Name, ImplBinding vars) ->
               Core (List (Name, ImplBinding vars))
    normImps defs ns [] = pure []
    normImps defs ns ((PV n i, bty) :: ts)
        = do logTermNF "elab.implicits" 10 ("Implicit pattern var " ++ show (PV n i)) env
                       (bindingType bty)
             if PV n i `elem` ns
                then normImps defs ns ts
                else do rest <- normImps defs (PV n i :: ns) ts
                        pure ((PV n i, !(normBindingTy defs bty)) :: rest)
    normImps defs ns ((n, bty) :: ts)
        = do tmnf <- normaliseHoles env (bindingTerm bty)
             logTerm "elab.implicits" 10 ("Normalising implicit " ++ show n) tmnf
             case getFnArgs tmnf of
                -- n reduces to another hole, n', so treat it as that as long
                -- as it isn't already done
                (Meta _ n' i margs, args) =>
                    do hole <- isCurrentHole i
                       if hole && not (n' `elem` ns)
                          then do rest <- normImps defs (n' :: ns) ts
                                  btynf <- normBindingTy defs bty
                                  pure ((n', btynf) :: rest)
                          else normImps defs ns ts
                _ => -- Unified to something concrete, so drop it
                     normImps defs ns ts

    -- Insert the hole/binding pair into the list before the first thing
    -- which refers to it
    insert : (Name, ImplBinding vars) -> List Name -> List Name ->
             List (Name, ImplBinding vars) ->
             List (Name, ImplBinding vars)
    insert h ns sofar [] = [h]
    insert (hn, bty) ns sofar ((hn', bty') :: rest)
        = let used = filter (\n => elem n ns) (keys (bindingMetas bty')) in
              -- 'used' is to make sure we're only worrying about metavariables
              -- introduced in *this* expression (there may be others unresolved
              -- from elsewhere, for type inference purposes)
              if hn `elem` used
                 then (hn, bty) ::
                      (hn', bty') :: rest
                 else (hn', bty') ::
                          insert (hn, bty) ns (hn' :: sofar) rest

    -- Sort the list of implicits so that each binding is inserted *after*
    -- all the things it depends on (assumes no cycles)
    depSort : List Name -> List (Name, ImplBinding vars) ->
              List (Name, ImplBinding vars)
    depSort hnames [] = []
    depSort hnames (h :: hs) = insert h hnames [] (depSort hnames hs)

export
checkBindVar : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto m : Ref MD Metadata} ->
               {auto u : Ref UST UState} ->
               {auto e : Ref EST (EState vars)} ->
               RigCount -> ElabInfo ->
               NestedNames vars -> Env Term vars ->
               FC -> UserName -> -- username is base of the pattern name
               Maybe (Glued vars) ->
               Core (Term vars, Glued vars)
checkBindVar rig elabinfo nest env fc str topexp
    = do let elabmode = elabMode elabinfo
         -- In types, don't rebind if the name is already in scope;
         -- Below, return True if we don't need to implicitly bind the name
         let False = case implicitMode elabinfo of
                          PI _ => maybe False (const True) (defined (UN str) env)
                          _ => False
               | _ => check rig elabinfo nest env (IVar fc (UN str)) topexp
         est <- get EST
         let n = PV (UN str) (defining est)
         noteLHSPatVar elabmode (UN str)
         notePatVar n
         est <- get EST

         whenJust (isConcreteFC fc) $ \nfc => do
           log "ide-mode.highlight" 7 $ "getNameType is adding Bound: " ++ show n
           addSemanticDecorations [(nfc, Bound, Just n)]


         case lookup n (boundNames est) of
              Nothing =>
                do (tm, exp, bty) <- mkPatternHole fc rig n env
                                              (implicitMode elabinfo)
                                              topexp
                   -- In PI mode, it's invertible like any other pi bound thing
                   case implicitMode elabinfo of
                        PI _ => setInvertible fc n
                        _ => pure ()
                   log "elab.implicits" 5 $ "Added Bound implicit " ++ show (n, (rig, tm, exp, bty))
                   update EST { boundNames $= ((n, NameBinding rig Explicit tm exp) ::),
                                toBind $= ((n, NameBinding rig Explicit tm bty) :: ) }

                   log "metadata.names" 7 $ "checkBindVar is adding ↓"
                   addNameType fc (UN str) env exp
                   addNameLoc fc (UN str)

                   checkExp rig elabinfo env fc tm !(nf env exp) topexp
              Just bty =>
                do -- Check rig is consistent with the one in bty, and
                   -- update if necessary
                   combine (UN str) rig (bindingRig bty)
                   let tm = bindingTerm bty
                   let ty = bindingType bty

                   log "metadata.names" 7 $ "checkBindVar is adding ↓"
                   addNameType fc (UN str) env ty
                   addNameLoc fc (UN str)

                   checkExp rig elabinfo env fc tm !(nf env ty) topexp
  where
    updateRig : Name -> RigCount -> List (Name, ImplBinding vars) ->
                List (Name, ImplBinding vars)
    updateRig n c [] = []
    updateRig n c ((bn, r) :: bs)
        = if n == bn
             then case r of
                  NameBinding _ p tm ty => (bn, NameBinding c p tm ty) :: bs
                  AsBinding _ p tm ty pat => (bn, AsBinding c p tm ty pat) :: bs
             else (bn, r) :: updateRig n c bs

    -- Two variables are incompatble if at least one of them appears in a linear position
    -- and their sum is bigger than 1
    isIncompatible : RigCount -> RigCount -> Bool
    isIncompatible l r = (isLinear l || isLinear r) && linear < l |+| r

    combine : Name -> RigCount -> RigCount -> Core ()
    combine n l r = when (isIncompatible l r)
                         (throw (LinearUsed fc 2 n))

checkPolyConstraint :
            {auto c : Ref Ctxt Defs} ->
            PolyConstraint -> Core ()
checkPolyConstraint (MkPolyConstraint fc env arg x y)
    = do -- If 'x' is a metavariable and 'y' is concrete, that means we've
         -- ended up putting something too concrete in for a polymorphic
         -- argument
         xnf <- expand !(nf env !(quote env x))
         case xnf of
              VMeta _ _ _ _ _ _ =>
                   do ynf <- expand !(nf env y)
                      if !(concrete env ynf)
                         then throw (MatchTooSpecific fc env arg)
                         else pure ()
              _ => pure ()

solvePolyConstraint :
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            PolyConstraint -> Core ()
solvePolyConstraint (MkPolyConstraint fc env arg x y)
    = do defs <- get Ctxt
         -- If the LHS of the constraint isn't a metavariable, we can solve
         -- the constraint
         case !(expand !(nf env !(quote env x))) of
              xnf@(VMeta _ _ _ _ _ _) => pure ()
              t => do res <- unify inLHS fc env t !(nf env y)
                      -- If there's any constraints, it just means we didn't
                      -- solve anything and it won't help the check
                      pure ()

export
checkBindHere : {vars : _} ->
                {auto c : Ref Ctxt Defs} ->
                {auto m : Ref MD Metadata} ->
                {auto u : Ref UST UState} ->
                {auto e : Ref EST (EState vars)} ->
                RigCount -> ElabInfo ->
                NestedNames vars -> Env Term vars ->
                FC -> BindMode -> RawImp ->
                Maybe (Glued vars) ->
                Core (Term vars, Glued vars)
checkBindHere rig elabinfo nest env fc bindmode tm exp
    = do est <- get EST
         let oldenv = outerEnv est
         let oldsub = subEnv est
         let oldbif = bindIfUnsolved est
         let dontbind = map fst (toBind est)
         -- Set the binding environment in the elab state - unbound
         -- implicits should have access to whatever is in scope here
         put EST (updateEnv env SubRefl [] est)
         constart <- getNextEntry
         (tmv, tmt) <- check rig ({ implicitMode := bindmode,
                                    bindingVars := True }
                                  elabinfo)
                             nest env tm exp
         let solvemode = case elabMode elabinfo of
                              InLHS c => inLHS
                              _ => inTerm
         solveConstraints solvemode Normal

         ust <- get UST
         catch (retryDelayed solvemode (delayedElab ust))
               (\err =>
                  do update UST { delayedElab := [] }
                     throw err)

         -- Check all the patterns standing for polymorphic variables are
         -- indeed polymorphic
         ust <- get UST
         let cons = polyConstraints ust
         put UST ({ polyConstraints := [] } ust)
         traverse_ solvePolyConstraint cons
         traverse_ checkPolyConstraint cons

         solveConstraintsAfter constart
                          (case elabMode elabinfo of
                                InLHS c => inLHS
                                _ => inTerm) Defaults
         checkDots -- Check dot patterns unifying with the claimed thing
                   -- before binding names

         logTerm "elab.implicits" 5 "Binding names" tmv
         defs <- get Ctxt
         logTermNF "elab.implicits" 5 "Normalised" env tmv
         argImps <- getToBind fc (elabMode elabinfo)
                              bindmode env dontbind
         clearToBind dontbind
         update EST $ updateEnv oldenv oldsub oldbif . { boundNames := [] }
         ty <- quote env tmt
         defs <- get Ctxt
         (bv, bt) <- bindImplicits fc bindmode
                                   defs env argImps
                                   !(normaliseLHS env tmv)
                                   !(normaliseHoles env ty)
         traverse_ implicitBind (map fst argImps)
         checkExp rig elabinfo env fc bv !(nf env bt) exp
