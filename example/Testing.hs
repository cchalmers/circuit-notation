{-# LANGUAGE Arrows  #-}
{-# LANGUAGE BlockArguments  #-}
{-# LANGUAGE GADTs  #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}

-- {-# LANGUAGE ScopedTypeVariables  #-}

{-# OPTIONS -fplugin=CircuitNotation #-}
{-# OPTIONS -Wno-unused-local-binds #-}
{-# OPTIONS -Wno-missing-signatures #-}

module Example where

import Circuit

-- yes :: Int ~ Int => ()

-- yes = let a :: Int ~ Int => ()
--           a  = ()
--       in a

-- swapC :: Circuit (a,b) (b,a)
-- swapC = circuit \(a,b) -> do
--   -- let a :: not a real ty
--   idC -< (b,a)

no c =
  let
    inferenceHelper ::
      aTy ~ Int =>
      Circuit (aTy, bTy) (b'Ty, a'Ty)
      -> (Circuit aTy a'Ty -> CircuitT aTy a'Ty,
          Circuit bTy b'Ty -> CircuitT bTy b'Ty)
    cir
      = Circuit
          \ ((a_M2S, b_M2S), (b'_S2M, a'_S2M))
            -> let
                (a'_M2S, a_S2M) = run0 c (a_M2S, a'_S2M)
                (b'_M2S, b_S2M) = run1 c (b_M2S, b'_S2M)
              in ((b'_M2S, a'_M2S), (a_S2M, b_S2M))
    inferenceHelper = const (runCircuit, runCircuit)
    (run0, run1) = inferenceHelper cir
  in cir

-- swapC :: Circuit (a,b) (b,a)
-- swapC = circuit \(a,b) -> do
--   a' <- idC -< a
--   b' <- idC -< b
--   idC -< (b',a')

swapIC :: Circuit Int Char -> Circuit (Int, Int) (Char, Char)
swapIC c = circuit \(a :: Int ,b) -> do
  a' <- c -< a :: int
  b' <- c -< b
  idC -< (b',a')


-- -- swapC :: (( (a,b) -> (b,a) ))
-- -- swapC :: Circuit (a,b) (b,a)
-- -- swapC = circuit \(a :: a, b) -> (b, a :: a)

-- swapT :: Circuit (Signal Int, b) (b, Signal Int)
-- swapT =
--   let inferenceHelper
--          -- :: Circuit
--          :: aTy ~ Signal Int
--          => Circuit (aTy, bTy) cTy
--          -> (Circuit (aTy, bTy) cTy -> CircuitT (aTy, bTy) cTy)
--       inferenceHelper _ = runCircuit
--       run1 = inferenceHelper cir
--       -- cir = circuit \ (a, b) -> do
--       --   swapC_helped -< (a,b)
--       cir = Circuit \ ((aM2S, bM2S), finalstmtS2M)
--         -> let
--             (finalstmtM2S, (aS2M, bS2M))
--               = run1 swapC ((aM2S, bM2S), finalstmtS2M)
--           in (finalstmtM2S, (aS2M, bS2M))
--   in cir

-- -- circuit \(a,b) -> do
-- --   swapC -< (a,b)

-- -- L ({abstract:SrcSpan})
-- -- (TypeSig (NoExt)
-- --   ((:) (L ({abstract:SrcSpan}) (Unqual ({abstract:OccName}))) ([]))
-- --   (HsWC (NoExt)
-- --     (HsIB (NoExt)
-- --       (L ({abstract:SrcSpan})
-- --         (HsQualTy (NoExt)
-- --           (L ({abstract:SrcSpan})
-- --           ((:) (L ({abstract:SrcSpan})
-- --             (HsOpTy (NoExt)
-- --               (L ({abstract:SrcSpan}) (HsTyVar (NoExt) (NotPromoted) (L ({abstract:SrcSpan}) (Unqual ({abstract:OccName})))))
-- --               (L ({abstract:SrcSpan}) (Orig ({abstract:Module}) ({abstract:OccName})))
-- --               (L ({abstract:SrcSpan}) (HsAppTy (NoExt) (L ({abstract:SrcSpan}) (HsTyVar (NoExt) (NotPromoted) (L ({abstract:SrcSpan}) (Unqual ({abstract:OccName}))))) (L ({abstract:SrcSpan}) (HsTyVar (NoExt) (NotPromoted) (L ({abstract:SrcSpan}) (Unqual ({abstract:OccName}))))))
-- --               ))
-- --           ) ([])))
-- --           (L ({abstract:SrcSpan}) (HsFunTy (NoExt) (L ({abstract:SrcSpan}) (HsAppTy (NoExt) (L ({abstract:SrcSpan}) (HsAppTy (NoExt) (L ({abstract:SrcSpan}) (HsTyVar (NoExt) (NotPromoted) (L ({abstract:SrcSpan}) (Unqual ({abstract:OccName}))))) (L ({abstract:SrcSpan}) (HsTupleTy (NoExt) (HsBoxedOrConstraintTuple) ((:) (L ({abstract:SrcSpan}) (HsTyVar (NoExt) (NotPromoted) (L ({abstract:SrcSpan}) (Unqual ({abstract:OccName}))))) ((:) (L ({abstract:SrcSpan}) (HsTyVar (NoExt) (NotPromoted) (L ({abstract:SrcSpan}) (Unqual ({abstract:OccName}))))) ([]))))))) (L ({abstract:SrcSpan}) (HsTyVar (NoExt) (NotPromoted) (L ({abstract:SrcSpan}) (Unqual ({abstract:OccName})))))))
-- --           (L ({abstract:SrcSpan}) (HsParTy (NoExt) (L ({abstract:SrcSpan}) (HsFunTy (NoExt) (L ({abstract:SrcSpan}) (HsAppTy (NoExt) (L ({abstract:SrcSpan}) (HsAppTy (NoExt) (L ({abstract:SrcSpan}) (HsTyVar (NoExt) (NotPromoted) (L ({abstract:SrcSpan}) (Unqual ({abstract:OccName}))))) (L ({abstract:SrcSpan}) (HsTupleTy (NoExt) (HsBoxedOrConstraintTuple) ((:) (L ({abstract:SrcSpan}) (HsTyVar (NoExt) (NotPromoted) (L ({abstract:SrcSpan}) (Unqual ({abstract:OccName}))))) ((:) (L ({abstract:SrcSpan}) (HsTyVar (NoExt) (NotPromoted) (L ({abstract:SrcSpan}) (Unqual ({abstract:OccName}))))) ([]))))))) (L ({abstract:SrcSpan}) (HsTyVar (NoExt) (NotPromoted) (L ({abstract:SrcSpan}) (Unqual ({abstract:OccName}))))))) (L ({abstract:SrcSpan}) (HsAppTy (NoExt) (L ({abstract:SrcSpan}) (HsAppTy (NoExt) (L ({abstract:SrcSpan}) (HsTyVar (NoExt) (NotPromoted) (L ({abstract:SrcSpan}) (Unqual ({abstract:OccName}))))) (L ({abstract:SrcSpan}) (HsTupleTy (NoExt) (HsBoxedOrConstraintTuple) ((:) (L ({abstract:SrcSpan}) (HsTyVar (NoExt) (NotPromoted) (L ({abstract:SrcSpan}) (Unqual ({abstract:OccName}))))) ((:) (L ({abstract:SrcSpan}) (HsTyVar (NoExt) (NotPromoted) (L ({abstract:SrcSpan}) (Unqual ({abstract:OccName}))))) ([]))))))) (L ({abstract:SrcSpan}) (HsTyVar (NoExt) (NotPromoted) (L ({abstract:SrcSpan}) (Unqual ({abstract:OccName})))))))))))
-- --           ))
-- --         ))
-- --     ))
-- --   )
