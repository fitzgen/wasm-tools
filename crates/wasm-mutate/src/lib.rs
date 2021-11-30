//! A WebAssembly test case mutator.
//!
//! `wasm-mutate` takes in an existing Wasm module and then applies a
//! pseudo-random transformation to it, producing a new, mutated Wasm
//! module. This new, mutated Wasm module can be fed as a test input to your
//! Wasm parser, validator, compiler, or any other Wasm-consuming
//! tool. `wasm-mutate` can serve as a custom mutator for mutation-based
//! fuzzing.

#![allow(warnings)]

#![cfg_attr(not(feature = "structopt"), deny(missing_docs))]
mod error;
pub(crate) mod info;
pub(crate) mod module;
pub mod mutators;
use crate::mutators::{
    codemotion::CodemotionMutator, function_body_unreachable::FunctionBodyUnreachable,
    peephole::PeepholeMutator, remove_export::RemoveExportMutator,
    rename_export::RenameExportMutator, snip_function::SnipMutator,
};
use info::ModuleInfo;
use mutators::Mutator;
use rand::seq::SliceRandom;
use rand::{rngs::SmallRng, Rng, SeedableRng};
use std::hash::Hasher;
use std::{
    cell::{Cell, RefCell},
    rc::Rc,
    sync::Arc,
};

#[cfg(feature = "structopt")]
use structopt::StructOpt;

pub use error::{Error, Result};

// NB: only add this doc comment if we are not building the CLI, since otherwise
// it will override the main CLI's about text.
#[cfg_attr(
    not(feature = "structopt"),
    doc = r###"
A WebAssembly test case mutator.

This is the main entry point into this crate. It provides various methods
for configuring what kinds of mutations might be applied to the input
Wasm. Once configured, you can apply a transformation to the input Wasm via
the [`run`][wasm_mutate::WasmMutate::run] method.

# Example

```
# fn _foo() -> anyhow::Result<()> {
use wasm_mutate::WasmMutate;

let input_wasm = wat::parse_str(r#"
           (module
            (func (export "hello") (result i32)
             (i32.const 1234)
            )
           )
           "#)?;

// Create a `WasmMutate` builder, configure its seed, and then run it on the
// input Wasm!
let mutated_wasm = WasmMutate::default()
    .seed(42)
    .run(&input_wasm)?;

// Feed `mutated_wasm` into your tests...
# Ok(())
# }
```
"###
)]
#[cfg_attr(feature = "structopt", derive(StructOpt))]
pub struct WasmMutate<'wasm> {
    /// The RNG seed used to choose which transformation to apply. Given the
    /// same input Wasm and same seed, `wasm-mutate` will always generate the
    /// same output Wasm.
    #[cfg_attr(feature = "structopt", structopt(short, long))]
    seed: u64,

    /// Only perform semantics-preserving transformations on the Wasm module.
    #[cfg_attr(feature = "structopt", structopt(long))]
    preserve_semantics: bool,

    /// Fuel to control the time of the mutation.
    #[cfg_attr(feature = "structopt", structopt(skip = Cell::new(u64::MAX)))]
    fuel: Cell<u64>,
    /// Only perform size-reducing transformations on the Wasm module. This
    /// allows `wasm-mutate` to be used as a test case reducer.
    #[cfg_attr(feature = "structopt", structopt(long))]
    reduce: bool,

    // Note: this is only exposed via the programmatic interface, not via the
    // CLI.
    #[cfg_attr(feature = "structopt", structopt(skip = None))]
    raw_mutate_func: Option<Arc<dyn Fn(&mut Vec<u8>) -> Result<()>>>,

    #[cfg_attr(feature = "structopt", structopt(skip = None))]
    rng: Option<SmallRng>,

    #[cfg_attr(feature = "structopt", structopt(skip = None))]
    info: Option<ModuleInfo<'wasm>>,
}

impl Default for WasmMutate<'_> {
    fn default() -> Self {
        let seed = 3;
        WasmMutate {
            seed,
            preserve_semantics: false,
            reduce: false,
            raw_mutate_func: None,
            fuel: Cell::new(u64::MAX),
            rng: None,
            info: None,
        }
    }
}

impl<'wasm> WasmMutate<'wasm> {
    /// Set the RNG seed used to choose which transformation to apply.
    ///
    /// Given the same input Wasm and same seed, `wasm-mutate` will always
    /// generate the same output Wasm.
    pub fn seed(&mut self, seed: u64) -> &mut Self {
        self.seed = seed;
        self
    }

    /// Configure whether we will only perform semantics-preserving
    /// transformations on the Wasm module.
    pub fn preserve_semantics(&mut self, preserve_semantics: bool) -> &mut Self {
        self.preserve_semantics = preserve_semantics;
        self
    }

    /// Configure the fuel used during the mutation
    pub fn fuel(&mut self, fuel: u64) -> &mut Self {
        self.fuel = Cell::new(fuel);
        self
    }

    /// Configure whether we will only perform size-reducing transformations on
    /// the Wasm module.
    ///
    /// Setting this to `true` allows `wasm-mutate` to be used as a test case
    /// reducer.
    pub fn reduce(&mut self, reduce: bool) -> &mut Self {
        self.reduce = reduce;
        self
    }

    /// Set a custom raw mutation function.
    ///
    /// This is used when we need some underlying raw bytes, for example when
    /// mutating the contents of a data segment.
    ///
    /// You can override this to use `libFuzzer`'s `LLVMFuzzerMutate` function
    /// to get raw bytes from `libFuzzer`, for example.
    pub fn raw_mutate_func(
        &mut self,
        raw_mutate_func: Option<Arc<dyn Fn(&mut Vec<u8>) -> Result<()>>>,
    ) -> &mut Self {
        self.raw_mutate_func = raw_mutate_func;
        self
    }

    pub(crate) fn consume_fuel(&self, qt: u64) -> Result<()> {
        if qt > self.fuel.get() {
            log::info!("Resource limits reached!");
            return Err(crate::Error::NoMutationsApplicable); // Replace by a TimeoutError type
        }
        self.fuel.set(self.fuel.get() - qt);
        Ok(())
    }

    /// Run this configured `WasmMutate` on the given input Wasm.
    pub fn run<'a>(
        &'a mut self,
        input_wasm: &'wasm [u8],
    ) -> Result<Box<dyn Iterator<Item = Result<Vec<u8>>> + 'a>> {
        self.info = Some(ModuleInfo::new(input_wasm)?);
        self.rng = Some(SmallRng::seed_from_u64(self.seed));

        let mut mutators = vec![
            //Box::new(RenameExportMutator { max_name_size: 100 }),
            //Box::new(RemoveExportMutator),
            //Box::new(SnipMutator),
            //Box::new(FunctionBodyUnreachable),
            Box::new(PeepholeMutator::new(2)),
            //Box::new(CodemotionMutator),
        ]
        .into_iter()
        .filter(|m| m.can_mutate(&self))
        .collect::<Vec<_>>();

        while !mutators.is_empty() {
            let i = self.rng().gen_range(0, mutators.len());
            let mutator = mutators.swap_remove(i);
            match mutator.mutate(self) {
                Ok(iter) => return Ok(Box::new(iter.into_iter().map(|r| r.map(|m| m.finish())))),
                Err(e) => {
                    log::info!("mutator failed: {}; will try again", e);
                    continue;
                }
            }
        }

        Err(crate::Error::NoMutationsApplicable)
    }

    pub(crate) fn rng(&mut self) -> &mut SmallRng {
        self.rng.as_mut().unwrap()
    }

    pub(crate) fn info(&self) -> &ModuleInfo<'wasm> {
        self.info.as_ref().unwrap()
    }
}

#[cfg(test)]
pub(crate) fn validate(validator: &mut wasmparser::Validator, bytes: &[u8]) {
    let err = match validator.validate_all(bytes) {
        Ok(()) => return,
        Err(e) => e,
    };
    drop(std::fs::write("test.wasm", &bytes));
    if let Ok(text) = wasmprinter::print_bytes(bytes) {
        drop(std::fs::write("test.wat", &text));
    }

    panic!("wasm failed to validate {:?}", err);
}
