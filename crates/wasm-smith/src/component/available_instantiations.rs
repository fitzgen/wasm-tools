use std::{
    collections::{BTreeMap, HashMap, HashSet},
    rc::Rc,
};

use super::{ComponentContext, Entity, EntityCounts, Instance};
use arbitrary::{Result, Unstructured};

/// The set of potential instantiations that we can make at any given time while
/// generating a particular component.
///
/// This compares which entities are available in their various index spaces
/// within the component and which entities are needed to instantiate various
/// modules and components, and then computes the list of instantiations that we
/// could make right now. This computation is relatively costly to recompute
/// whenever we define a new entity, so it is done incrementally rather than
/// from scratch. Because new entities are always defined at the end of their
/// associated index spaces, we keep track of the count of entities we saw last
/// and the new entities are exactly the entities in the index spaces after our
/// last-seen counts.
pub(super) struct AvailableInstantiations {
    /// Potential core module instantiations that are available.
    module_choices: Vec<ModuleInstantiationChoices>,

    /// Indices of modules that we already have an entry for in
    /// `module_choices`.
    modules_in_choices: HashSet<u32>,

    /// Potential component instantiation choices that are available.
    component_choices: Vec<ComponentInstantiationChoices>,

    /// Indices of components that we already have an entry for in
    /// `component_choices`.
    components_in_choices: HashSet<u32>,

    /// The entity counts we last saw for the component this
    /// `AvailableInstantiations` object is associated with.
    counts: EntityCounts,
}

impl AvailableInstantiations {
    /// Choose an arbitrary available instantiation to instantiate into an
    /// `Instance`.
    pub fn choose(&self, u: &mut Unstructured) -> Result<Option<Instance>> {
        let mut choices: Vec<fn(&mut Unstructured, &AvailableInstantiations) -> Result<Instance>> =
            vec![];

        if !self.module_choices.is_empty() {
            choices.push(|u, me| {
                let insts = u.choose(&me.module_choices)?;
                insts.choose(u)
            });
        }

        if !self.component_choices.is_empty() {
            choices.push(|u, me| {
                let insts = u.choose(&me.component_choices)?;
                insts.choose(u)
            });
        }

        if choices.is_empty() {
            return Ok(None);
        }

        let f = u.choose(&choices)?;
        f(u, self).map(Some)
    }

    /// Incrementally update the available instantiations for the current state
    /// of our component.
    pub fn update(&mut self, component: &ComponentContext) {
        let new_counts = component.counts();

        // If there aren't any new entities, then there aren't any new potential
        // instantiations.
        if self.counts == new_counts {
            return;
        }

        // We have new entities, and therefore potentially have new available
        // instantiations.
        //
        // First, update our existing `module_choices` and `component_choices`
        // for any new available instantiations of modules and components that
        // we could already instantiate. This only needs to look at new entities
        // since `*_choices` already contains all the available instantiations
        // for the old entities.

        for insts in &mut self.module_choices {
            let (imports, _exports) = component.module_type(insts.module).imports_exports();
            for ((name, candidates), (import_name, export_types)) in
                insts.args.iter_mut().zip(imports)
            {
                debug_assert_eq!(*name, import_name);
                debug_assert!(!candidates.is_empty());
                candidates.extend(component.core_instance_subtypes(&self.counts, &export_types));
            }
        }

        for insts in &mut self.component_choices {
            let (import_types, _export_types) =
                component.component_type(insts.component).imports_exports();
            for ((name, candidates), (import_name, export_type)) in
                insts.args.iter_mut().zip(import_types)
            {
                debug_assert_eq!(*name, import_name);
                debug_assert!(!candidates.is_empty());
                candidates
                    .extend(component.component_subtypes(&EntityCounts::default(), &export_type));
            }
        }

        // Second, consider all modules and components that we couldn't
        // previously instantiate. Maybe they can be instantiated now that we
        // have some new entities? This has to consider all entities in the
        // component, since instantiating a module might require a mix of old
        // and new entities as its instantiation arguments.

        'module_loop: for module in 0..new_counts.modules {
            let module = u32::try_from(module).unwrap();
            if self.modules_in_choices.contains(&module) {
                // Handled above in the first `update` phase.
                continue;
            }

            let mut args = vec![];
            let (imports, _exports) = component.module_type(module).imports_exports();
            for (name, import_ty) in imports {
                let candidates =
                    component.core_instance_subtypes(&EntityCounts::default(), &import_ty);
                if candidates.is_empty() {
                    continue 'module_loop;
                }
                args.push((name.to_string(), candidates));
            }
            self.module_choices
                .push(ModuleInstantiationChoices { module, args })
        }

        'component_loop: for component_idx in 0..new_counts.components {
            let component_idx = u32::try_from(component_idx).unwrap();
            if self.components_in_choices.contains(&component_idx) {
                // Handled above in the first `update` phase.
                continue;
            }

            let mut args = vec![];
            let (imports, _exports) = component.component_type(component_idx).imports_exports();
            for (name, import_ty) in imports {
                let candidates =
                    component.component_subtypes(&EntityCounts::default(), &*import_ty);
                if candidates.is_empty() {
                    continue 'component_loop;
                }
                args.push((name.to_string(), candidates));
            }
            self.component_choices.push(ComponentInstantiationChoices {
                component: component_idx,
                args,
            });
        }
    }
}

fn is_core_module_subtype(
    a: &crate::component::ModuleType,
    b: &crate::component::ModuleType,
) -> bool {
    let (a_imports, a_exports) = a.imports_exports();
    let (b_imports, b_exports) = b.imports_exports();

    is_core_set_subtype(&a_exports, &b_exports)
        && b_imports
            .iter()
            .all(|(name, b_imp)| match a_imports.get(name) {
                // NB: imports are contravariant (we swap the order of B's and
                // A's imports here).
                Some(a_imp) => is_core_set_subtype(b_imp, a_imp),
                None => false,
            })
}

// https://github.com/WebAssembly/component-model/blob/main/design/mvp/Subtyping.md
fn is_subtype(a: &crate::component::Type, b: &crate::component::Type) -> bool {
    use crate::component::Type;
    match (a, b) {
        (Type::Module(a), Type::Module(b)) => is_core_module_subtype(a, b),
        (Type::Component(a), Type::Component(b)) => is_component_subtype(a, b),
        (Type::Instance(a), Type::Instance(b)) => is_component_instance_subtype(a, b),
        (Type::Func(a), Type::Func(b)) => is_component_func_subtype(a, b),
        (Type::Value(a), Type::Value(b)) => is_component_value_subtype(a, b),
        (Type::Interface(_), Type::Interface(_)) => unreachable!(),
        _ => false,
    }
}

fn is_component_subtype(
    a: &crate::component::ComponentType,
    b: &crate::component::ComponentType,
) -> bool {
    let (a_imports, a_exports) = a.imports_exports();
    let (b_imports, b_exports) = b.imports_exports();

    // NB: imports are contravariant (we swap the order of B's and
    // A's imports here).
    is_component_set_subtype(&b_imports, &a_imports)
        && is_component_set_subtype(&a_exports, &b_exports)
}

fn is_component_set_subtype(
    a: &BTreeMap<&str, &Rc<crate::component::Type>>,
    b: &BTreeMap<&str, &Rc<crate::component::Type>>,
) -> bool {
    let mut a_iter = a.iter().peekable();

    for (b_name, b_ty) in b {
        // Advance `a_iter` to its entry for key `b_name`, if it has such an
        // entry.
        while a_iter.peek().map_or(false, |(k, _)| *k != b_name) {
            a_iter.next();
        }

        match a_iter.next() {
            None => return false,
            Some((a_name, a_ty)) => {
                debug_assert_eq!(a_name, b_name);
                if !is_subtype(a_ty, b_ty) {
                    return false;
                }
            }
        }
    }

    true
}

fn is_component_instance_subtype(
    a: &crate::component::InstanceType,
    b: &crate::component::InstanceType,
) -> bool {
    let a_exports = a.exports();
    let b_exports = b.exports();
    is_component_set_subtype(&a_exports, &b_exports)
}

fn is_component_func_subtype(
    a: &crate::component::FuncType,
    b: &crate::component::FuncType,
) -> bool {
    // TODO: "parameter names must match in order"
    //
    // TODO: "superfluous parameters can be ignored in the subtype; option
    // parameters can be ignored in the supertype; covariant result subtyping"
    a.params.len() == b.params.len()
        && a.params.iter().zip(&b.params).all(|(a, b)| {
            // NB: params are contravariant (we swap the A and B arguments
            // here).
            is_component_intertyperef_subtype(&b.ty, &a.ty)
        })
        && is_component_intertyperef_subtype(&a.result, &b.result)
}

fn is_component_value_subtype(
    a: &crate::component::ValueType,
    b: &crate::component::ValueType,
) -> bool {
    is_component_intertyperef_subtype(&a.0, &b.0)
}

fn is_component_intertyperef_subtype(
    a: &crate::component::InterfaceTypeRef,
    b: &crate::component::InterfaceTypeRef,
) -> bool {
    use crate::component::InterfaceTypeRef::*;
    match (a, b) {
        // TODO: (tuple T ...) <: T
        // TODO: T <: (option T)
        // TODO: T <: (expected T _)
        // TODO: T <: (union ... T ...)
        (_, Primitive(crate::component::PrimitiveInterfaceType::Unit)) => true,
        (Primitive(a), Primitive(b)) => is_component_primitive_subtype(a, b),
        (Type(a), Type(b)) => match (&**a.ty(), &**b.ty()) {
            (crate::component::Type::Interface(a), crate::component::Type::Interface(b)) => {
                is_component_intertype_subtype(a, b)
            }
            _ => unreachable!(),
        },
        _ => false,
    }
}

fn is_component_primitive_subtype(
    a: &crate::component::PrimitiveInterfaceType,
    b: &crate::component::PrimitiveInterfaceType,
) -> bool {
    use crate::component::PrimitiveInterfaceType::*;
    match (a, b) {
        (a, b) if a == b => true,
        (_, Unit) => true,
        (S8, S16) | (S8, S32) | (S8, S64) => true,
        (S16, S32) | (S16, S64) => true,
        (S32, S64) => true,
        (U8, U16) | (U8, U32) | (U8, U64) => true,
        (U16, U32) | (U16, U64) => true,
        (U32, U64) => true,
        (Float32, Float64) => true,
        _ => false,
    }
}

fn is_component_intertype_subtype(
    a: &crate::component::InterfaceType,
    b: &crate::component::InterfaceType,
) -> bool {
    use crate::component::InterfaceType::*;
    match (a, b) {
        // TODO: (tuple T ...) <: T
        // TODO: T <: (option T)
        // TODO: T <: (expected T _)
        // TODO: T <: (union ... T ...)
        (_, Primitive(crate::component::PrimitiveInterfaceType::Unit)) => true,
        (Primitive(a), Primitive(b)) => is_component_primitive_subtype(a, b),
        (Record(a), Record(b)) => is_component_record_subtype(a, b),
        (Variant(a), Variant(b)) => is_component_variant_subtype(a, b),
        (List(a), List(b)) => is_component_list_subtype(a, b),
        (Tuple(a), Tuple(b)) => is_component_tuple_subtype(a, b),
        (Flags(a), Flags(b)) => is_component_flags_subtype(a, b),
        (Enum(a), Enum(b)) => is_component_enum_subtype(a, b),
        (Union(a), Union(b)) => is_component_union_subtype(a, b),
        (Option(a), Option(b)) => is_component_option_subtype(a, b),
        (Expected(a), Expected(b)) => is_component_expected_subtype(a, b),
        _ => false,
    }
}

fn is_component_record_subtype(
    a: &crate::component::RecordType,
    b: &crate::component::RecordType,
) -> bool {
    let a_fields: HashMap<_, _> = a.fields.iter().map(|f| (f.name.as_str(), &f.ty)).collect();
    b.fields
        .iter()
        .all(|b_field| match a_fields.get(b_field.name.as_str()) {
            Some(a_ty) => is_component_intertyperef_subtype(a_ty, &b_field.ty),
            None => false,
        })
}

fn is_component_variant_subtype(
    a: &crate::component::VariantType,
    b: &crate::component::VariantType,
) -> bool {
    // TODO: handle default cases
    let b_cases: HashMap<_, _> = b
        .cases
        .iter()
        .map(|c| (c.0.name.as_str(), &c.0.ty))
        .collect();
    a.cases
        .iter()
        .all(|a_case| match b_cases.get(a_case.0.name.as_str()) {
            Some(b_ty) => is_component_intertyperef_subtype(&a_case.0.ty, b_ty),
            None => false,
        })
}

fn is_component_list_subtype(
    a: &crate::component::ListType,
    b: &crate::component::ListType,
) -> bool {
    is_component_intertyperef_subtype(&a.elem_ty, &b.elem_ty)
}

fn is_component_tuple_subtype(
    a: &crate::component::TupleType,
    b: &crate::component::TupleType,
) -> bool {
    a.fields.len() >= b.fields.len()
        && a.fields
            .iter()
            .zip(&b.fields)
            .all(|(a, b)| is_component_intertyperef_subtype(a, b))
}

fn is_component_flags_subtype(
    a: &crate::component::FlagsType,
    b: &crate::component::FlagsType,
) -> bool {
    let a_fields: HashSet<_> = a.fields.iter().collect();
    b.fields.iter().all(|b_field| a_fields.contains(b_field))
}

fn is_component_enum_subtype(
    a: &crate::component::EnumType,
    b: &crate::component::EnumType,
) -> bool {
    let b_variants: HashSet<_> = b.variants.iter().collect();
    a.variants
        .iter()
        .all(|a_variant| b_variants.contains(a_variant))
}

fn is_component_union_subtype(
    a: &crate::component::UnionType,
    b: &crate::component::UnionType,
) -> bool {
    let b_variants: HashSet<_> = b.variants.iter().collect();
    a.variants
        .iter()
        .all(|a_variant| b_variants.contains(a_variant))
}

fn is_component_option_subtype(
    a: &crate::component::OptionType,
    b: &crate::component::OptionType,
) -> bool {
    is_component_intertyperef_subtype(&a.inner_ty, &b.inner_ty)
}

fn is_component_expected_subtype(
    a: &crate::component::ExpectedType,
    b: &crate::component::ExpectedType,
) -> bool {
    is_component_intertyperef_subtype(&a.ok_ty, &b.ok_ty)
        && is_component_intertyperef_subtype(&a.err_ty, &b.err_ty)
}

impl ComponentContext {
    fn core_subtypes(
        &self,
        counts: &EntityCounts,
        ty: crate::core::EntityType,
    ) -> Vec<wasm_encoder::Export> {
        todo!();
    }

    fn core_instance_subtypes(
        &self,
        counts: &EntityCounts,
        exports: &BTreeMap<&str, &crate::core::EntityType>,
    ) -> Vec<u32> {
        let mut subtypes = vec![];

        for (idx, inst) in self.instances.iter().enumerate() {
            let idx = u32::try_from(idx).unwrap();
            let inst_ty = self.core_instance_type(idx);
            if is_core_instance_subtype(&inst_ty, exports) {
                subtypes.push(idx);
            }
        }

        subtypes
    }

    fn component_subtypes(
        &self,
        counts: &EntityCounts,
        ty: &crate::component::Type,
    ) -> Vec<crate::component::Entity> {
        let mut subs = vec![];
        match ty {
            crate::component::Type::Module(module_ty) => subs.extend(
                (counts.modules..self.modules.len())
                    .map(|idx| u32::try_from(idx).unwrap())
                    .filter(|idx| is_core_module_subtype(self.module_type(*idx), module_ty))
                    .map(crate::component::Entity::Module),
            ),
            crate::component::Type::Component(_) => todo!(),
            crate::component::Type::Instance(_) => todo!(),
            crate::component::Type::Func(_) => todo!(),
            crate::component::Type::Value(_) => todo!(),
            crate::component::Type::Interface(_) => {
                unreachable!("interface types aren't exported/imported by components")
            }
        }
        subs
    }
}

fn is_core_instance_subtype(
    a: &BTreeMap<&str, &crate::core::EntityType>,
    b: &BTreeMap<&str, &crate::core::EntityType>,
) -> bool {
    is_core_set_subtype(a, b)
}

fn is_core_set_subtype(
    a: &BTreeMap<&str, &crate::core::EntityType>,
    b: &BTreeMap<&str, &crate::core::EntityType>,
) -> bool {
    let mut a_iter = a.iter().peekable();

    for (b_name, b_ty) in b {
        // Advance `a_iter` to its entry for key `b_name`, if it has such an
        // entry.
        while a_iter.peek().map_or(false, |(k, _)| *k != b_name) {
            a_iter.next();
        }

        match a_iter.next() {
            None => return false,
            Some((a_name, a_ty)) => {
                debug_assert_eq!(a_name, b_name);
                if !is_core_subtype(a_ty, b_ty) {
                    return false;
                }
            }
        }
    }

    true
}

// https://webassembly.github.io/spec/core/valid/types.html#import-subtyping
fn is_core_subtype(a: &crate::core::EntityType, b: &crate::core::EntityType) -> bool {
    use crate::core::EntityType;
    match (a, b) {
        (EntityType::Global(a), EntityType::Global(b)) => is_global_subtype(*a, *b),
        (EntityType::Table(a), EntityType::Table(b)) => is_table_subtype(*a, *b),
        (EntityType::Memory(a), EntityType::Memory(b)) => is_memory_subtype(*a, *b),
        (EntityType::Tag(a), EntityType::Tag(b)) => is_tag_subtype(a, b),
        (EntityType::Func(_, a), EntityType::Func(_, b)) => is_func_subtype(a, b),
        _ => false,
    }
}

// https://webassembly.github.io/spec/core/valid/types.html#globals
fn is_global_subtype(a: crate::core::GlobalType, b: crate::core::GlobalType) -> bool {
    a == b
}

// https://webassembly.github.io/spec/core/valid/types.html#tables
fn is_table_subtype(a: crate::core::TableType, b: crate::core::TableType) -> bool {
    a.element_type == b.element_type
        && is_limits_subtype(a.minimum, a.maximum, b.minimum, b.maximum)
}

// https://webassembly.github.io/spec/core/valid/types.html#match-limits
fn is_limits_subtype<T: Into<u64>>(a_min: T, a_max: Option<T>, b_min: T, b_max: Option<T>) -> bool {
    a_min.into() >= b_min.into()
        && match b_max {
            Some(b_max) => match a_max {
                Some(a_max) => a_max.into() <= b_max.into(),
                None => false,
            },
            None => true,
        }
}

// https://webassembly.github.io/spec/core/valid/types.html#memories
fn is_memory_subtype(a: crate::core::MemoryType, b: crate::core::MemoryType) -> bool {
    is_limits_subtype(a.minimum, a.maximum, b.minimum, b.maximum)
}

fn is_tag_subtype(a: &crate::core::TagType, b: &crate::core::TagType) -> bool {
    is_func_subtype(&a.func_type, &b.func_type)
}

// https://webassembly.github.io/spec/core/valid/types.html#functions
fn is_func_subtype(a: &crate::core::FuncType, b: &crate::core::FuncType) -> bool {
    a == b
}

/// A set of available instantiations for a specific module.
///
/// Note that this is different from `super::Instance::Module` in that it
/// represents *all* available instantiations for a module.
///
/// For example, if module `4` could be instantiated in two ways as either:
///
/// 1. `Instance::Module { module: 4, args: vec![("x".into(), 5)] }`, or
/// 2. `Instance::Module { module: 4, args: vec![("x".into(), 6)] }`
///
/// then we would represent that as
///
/// ```
/// InstantiationChoices::Module {
///     module: 4,
///     args: vec![("x".into(), vec![5, 6])],
/// };
/// ```
///
/// Specifically, note that rather than choosing one argument for the module's
/// `x` parameter, we have the set of all arguments that could be passed as the
/// module's `x` parameter.
struct ModuleInstantiationChoices {
    /// The module to instantiate.
    module: u32,

    /// The set of all core instance arguments that could instantiate
    /// `module`.
    ///
    // TODO: have `enum { Instance(u32), Parts(Vec<EntityType>) }` here for
    // either an instance (all that is currently supported) or a tupling of
    // other entities (would need to inject the tupled instance as well; have to
    // worry about configured maximums too).
    args: Vec<(String, Vec<u32>)>,
}

impl ModuleInstantiationChoices {
    fn choose(&self, u: &mut Unstructured) -> Result<Instance> {
        Ok(Instance::Module {
            module: self.module,
            args: self
                .args
                .iter()
                .map(|(name, choices)| {
                    debug_assert!(!choices.is_empty());
                    Ok((name.clone(), u.choose(choices).copied()?))
                })
                .collect::<Result<_>>()?,
        })
    }
}

struct ComponentInstantiationChoices {
    /// The component to instantiate.
    component: u32,
    /// The set of all entity arguments that could instantiate `component`.
    args: Vec<(String, Vec<Entity>)>,
}

impl ComponentInstantiationChoices {
    fn choose(&self, u: &mut Unstructured) -> Result<Instance> {
        Ok(Instance::Component {
            component: self.component,
            args: self
                .args
                .iter()
                .map(|(name, choices)| {
                    debug_assert!(!choices.is_empty());
                    Ok((name.clone(), u.choose(choices).copied()?))
                })
                .collect::<Result<_>>()?,
        })
    }
}
