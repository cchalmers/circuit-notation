% Source plugin DSL for Circuits
% Christopher Chalmers
% 2020-08-28 CHECK THE DATE

# Introduction

This is about a plugin I wrote for Myrtle.ai for combining circuits. I'll talk about

  - why we need a DSL
  - the different options available
  - what the implementation looks like

---

# Example problem

Clash is a language with Haskell syntax that uses GHC to compile Haskell to HDL.

https://clash-lang.org/

---

# Example problem


```
  Axi4Lite    |------| Axi4
 control -----|      |----- ddr1
  Axi4        | FPGA |----- ddr2
     DMA -----|      |----- ddr3
              |------|----- ddr4
```

- In hardware, interfaces are often bidirectional (backpressure, request and response)
- Haskell doesn't have a good way of modeling this when dealing with multiple interfaces
- Having inputs and outputs not connected very quickly becomes unwieldy

::: backpressure - only accept data/requests/responses when you're ready for it
    Axi is a standard memory mapped communication interface. It consists of signals in both directions.

---

# Haskell code


Typical interface:

```
topEntity
  :: "control fwd" ::: Signal domain AxiLiteFwd
  -> "dma fwd"     ::: Signal domain Axi4Fwd
  -> "ddr1 bwd"    ::: Signal domain Axi4Bwd
  -> "ddr2 bwd"    ::: Signal domain Axi4Bwd
  -> "ddr3 bwd"    ::: Signal domain Axi4Bwd
  -> "ddr4 bwd"    ::: Signal domain Axi4Bwd
  ( "control bwd" ::: Signal domain AxiLiteFwd
  , "dma bwd"     ::: Signal domain Axi4Bwd
  , "ddr1 fwd"    ::: Signal domain Axi4Fwd
  , "ddr2 fwd"    ::: Signal domain Axi4Fwd
  , "ddr3 fwd"    ::: Signal domain Axi4Fwd
  , "ddr4 fwd"    ::: Signal domain Axi4Fwd
  )

Nothing at the type level to say that these interfaces are tied together. A lot of manual 

```

```
type (name :: k) ::: a = a
```

---

# The circuit type


```
newtype Circuit a b = Circuit { (Fwd a :-> Bwd b) -> (Bwd a :-> Fwd b) }

type instance Fwd Axi = AxiFwd
type instance Bwd Axi = AxiBwd

(>>>) ::: Circuit a b -> Circuit b c -> Circuit a c
```

::: The circuit type lets us have both directions as a single type

---

# Manually writing out with Circuit

```
Circuit
  ( "control" ::: AxiLite
  , "dma" ::: Axi4
  )
  ( "ddr1" ::: Axi4
  , "ddr2" ::: Axi4
  , "ddr3" ::: Axi4
  , "ddr4" ::: Axi4
  )
myCircuit = Circuit ((controlFwd, dmaFwd) :-> (ddr1Bwd, ddr2Bwd, ddr3Bwd, ddr4Bwd)) ->
  let (dmaBwd :-> (ddr1Fwd, ddr2Fwd, ddr3Fwd, ddr4Fwd)) =
        runCircuit interconnect (dmaFwd :-> (ddr1Fwd, ddr2Fwd, ddr3Fwd, ddr4Fwd))


still messy
```

---

# Arrow notation

```
{-# Arrows #-}

proc x -> do
  a <- arr -< b
```


Good for describing circuit graphs but can't use native version:

- not bidirectional
- not recursive

---

# Custom arrow notation


```
\(a,b) -> do
  a' <- c -< a
  b' <- c -< b
  idC -< (a', b')
```

Custom translation. (

::: Proc syntax removed because

---

# Extending GHC

- preprocessors
- frontend plugins!?!?
- parsed (`GhcPs`)
- template Haskell
- renamer plugin
- type checker
- constraint solver
- core

https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/extending_ghc.html

---

# Plugins

```
data Plugin {
    installCoreToDos :: CorePlugin
    -- ^ Modify the Core pipeline that will be used for compilation.

    tcPlugin :: TcPlugin
    -- ^ used to be called "type checker plugins", not called constraint solver plugin

    pluginRecompile :: [CommandLineOption] -> IO PluginRecompile
    -- ^ when to recompile

    parsedResultAction :: [CommandLineOption] -> ModSummary -> HsParsedModule -> Hsc HsParsedModule
    -- ^ source plugin

    renamedResultAction :: [CommandLineOption] -> TcGblEnv -> HsGroup GhcRn -> TcM (TcGblEnv, HsGroup GhcRn)
    -- ^ renamer

    typeCheckResultAction :: [CommandLineOption] -> ModSummary -> TcGblEnv -> TcM TcGblEnv
    -- ^ type checked

    spliceRunAction :: [CommandLineOption] -> LHsExpr GhcTc -> TcM (LHsExpr GhcTc)
    -- ^ modify the TH splice or quasiqoute before it is run

    interfaceLoadAction :: forall lcl. [CommandLineOption] -> ModIface -> IfM lcl ModIface
    -- ^ modify loaded interface files
}

defaultPlugin :: Plugin

module CircuitNotation (plugin) where
```

::: A plugin is a datatype you expose at the top level. A plugin can execute during multiple stages
    of the ghc pipeline.
    --
    You can use IORefs to save state between stages. THINK OF AN EXAMPLE FOR WHEN YOU MIGHT WANT TO
    DO THIS.

    

---

# preprocessors

Used in testing frameworks to descover tests

```
{-# OPTIONS_GHC -F -pgmF hspec-discover #-}
```

Have to parse the entire source yourself. Not ideal for embedded DSLs.

Useful for processing tasks that you can't handle otherweise.

---

# Template Haskell / QuasiQuotes


- Much lower level than source plugins -- easier to get started
- Have to parse yourself (although there are packages to do this)
- Can to convert to a template haskell Expr yourself
- Type errors on generated code just point to start of slice

---

# parsed source plugin

- Can accept anything that GHC can parse
- Can produce any valid haskell program
- Access to GHCs internals (things like error messages)
- Type errors point to relevant source
- Can't generate documentation
- Can't be used in ghci?


--

# Template Haskell example

The *old* way
- `haskell-src-ext`
- `haskell-src-meta`

- `ghc-lib`
- `ghc-lib-parser`

**Is there a way to go from GHC.HsExpr GhcPs -> TH.Expr?**

--

# Renamer and beyond

Can be used in conjunction with other parts but since all names have to be already resolved this can
make it more difficult for a DSL.

# Conclustion

GHC is highly extensible
