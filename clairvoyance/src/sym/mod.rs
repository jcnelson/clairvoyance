// Copyright (C) 2026 Trust Machines
// 
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
// 
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.
// 
// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

pub mod command;

use std::fs;
use std::fmt;
use std::io;
use std::rc::Rc;
use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::collections::BTreeMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, LazyLock};
use std::collections::BTreeSet;
use std::borrow::Borrow;
use std::hash::{Hash, Hasher};
use std::convert::TryFrom;

use clarity_types::Value;
use clarity_types::ClarityName;
use clarity_types::types::TypeSignature;
use clarity_types::types::{PrincipalData, StandardPrincipalData};
use clarity_types::representations::SymbolicExpressionType;
use clarity_types::representations::SymbolicExpression;
use clarity_types::types::QualifiedContractIdentifier;

use clarity::vm::ContractContext;
use clarity::vm::contexts::GlobalContext;
use clarity::vm::costs::LimitedCostTracker;
use clarity::vm::eval_all;
use clarity::vm::errors::ClarityEvalError;
use clarity::vm::errors::VmExecutionError;
use clarity::vm::errors::RuntimeError;
use clarity::vm::analysis::errors::SyntaxBindingErrorType;
use clarity::vm::types::signatures::parse_name_type_pairs;
use clarity::vm::analysis::type_checker::contexts::TypeMap;
use clarity::vm::types::TypeSignatureExt;

use clarity_types::types::SequencedValue;
use clarity_types::types::signatures::{SequenceSubtype, TupleTypeSignature, CallableSubtype, StringSubtype, ListTypeData};
use clarity_types::types::TraitIdentifier;
use clarity_types::types::TupleData;
use clarity::vm::types::{
    ASCIIData, BuffData, CharType, SequenceData, UTF8Data,
};
use clarity_types::types::ListData;

use stacks_common::consts::CHAIN_ID_MAINNET;
use stacks_common::address::C32_ADDRESS_VERSION_MAINNET_SINGLESIG;
use crate::core::BackingStore;
use crate::core::Error;
use crate::core::ast;
use crate::core::{DEFAULT_STACKS_EPOCH, DEFAULT_CLARITY_VERSION};
use crate::core::ProofFailures;
use crate::sym::command::{Command, CommandContext, Halt};

use num::integer;
use num::integer::Integer;

pub fn is_debug() -> bool {
    stacks_common::util::log::get_loglevel() == slog::Level::Debug
}

/// Symbol ID
#[derive(Debug, PartialEq, Eq, Clone, Hash, PartialOrd, Ord)]
pub struct SymId(String);

impl fmt::Display for SymId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", self.0)
    }
}

impl From<ClarityName> for SymId {
    fn from(cn: ClarityName) -> Self {
        Self(cn.as_str().to_string())
    }
}

impl From<&ClarityName> for SymId {
    fn from(cn: &ClarityName) -> Self {
        Self(cn.as_str().to_string())
    }
}

impl From<&str> for SymId {
    fn from(s: &str) -> Self {
        Self(s.to_string())
    }
}

impl From<String> for SymId {
    fn from(s: String) -> Self {
        Self(s)
    }
}

impl SymId {
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

/// Value symbols
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Sym {
    Int(SymId),
    UInt(SymId),
    Bool(SymId),
    Sequence(SymId, SequenceSubtype),
    Principal(SymId),
    Tuple(SymId, TupleTypeSignature),
    Optional(SymId, TypeSignature),
    Response(SymId, TypeSignature, TypeSignature),
    Callable(SymId, CallableSubtype),
    ListUnion(SymId, BTreeSet<CallableSubtype>),
    TraitReference(SymId, TraitIdentifier)
}

impl Sym {
    pub fn id(&self) -> &str {
        match self {
            Self::Int(s) => &s.0,
            Self::UInt(s) => &s.0,
            Self::Bool(s) => &s.0,
            Self::Sequence(s, ..) => &s.0,
            Self::Principal(s) => &s.0,
            Self::Tuple(s, ..) => &s.0,
            Self::Optional(s, ..) => &s.0,
            Self::Response(s, ..) => &s.0,
            Self::Callable(s, ..) => &s.0,
            Self::ListUnion(s, ..) => &s.0,
            Self::TraitReference(s, ..) => &s.0,
        }
    }

    pub fn type_sig(&self) -> TypeSignature {
        match self {
            Self::Int(_s) => TypeSignature::IntType,
            Self::UInt(_s) => TypeSignature::UIntType,
            Self::Bool(_s) => TypeSignature::BoolType,
            Self::Sequence(_s, stype) => TypeSignature::SequenceType(stype.clone()),
            Self::Principal(_s) => TypeSignature::PrincipalType,
            Self::Tuple(_s, ttype) => TypeSignature::TupleType(ttype.clone()),
            Self::Optional(_s, otype) => TypeSignature::OptionalType(Box::new(otype.clone())),
            Self::Response(_s, oktype, errtype) => TypeSignature::ResponseType(Box::new((oktype.clone(), errtype.clone()))),
            Self::Callable(_s, ctype) => TypeSignature::CallableType(ctype.clone()),
            Self::ListUnion(_s, utypes) => TypeSignature::ListUnionType(utypes.clone()),
            Self::TraitReference(_s, ttype) => TypeSignature::TraitReferenceType(ttype.clone())
        }
    }

    pub fn type_str(&self) -> String {
        match self.type_sig() {
            TypeSignature::ListUnionType(utypes) => {
                let mut union_type_strs = vec![];
                for utype in utypes.iter() {
                    match utype {
                        CallableSubtype::Trait(trait_id) => {
                            union_type_strs.push(format!("<{}>", trait_id));
                        }
                        CallableSubtype::Principal(contract_id) => {
                            union_type_strs.push(format!("(principal {})", contract_id));
                        }
                    }
                }
                let union_type = union_type_strs.join(" ");
                format!("(union {})", union_type)
            },
            x => format!("{}", &x)
        }
    }
}

impl fmt::Display for Sym {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::Int(s) => write!(f, "({} {})", s, TypeSignature::IntType),
            Self::UInt(s) => write!(f, "({} {})", s, TypeSignature::UIntType),
            Self::Bool(s) => write!(f, "({} {})", s, TypeSignature::BoolType),
            Self::Sequence(s, stype) => write!(f, "({} {})", s, TypeSignature::SequenceType(stype.clone())),
            Self::Principal(s) => write!(f, "({} {})", s, TypeSignature::PrincipalType),
            Self::Tuple(s, _ttype) => {
                write!(f, "({} {{ .. }}))", s)
            }
            Self::Optional(s, otype) => write!(f, "({} {})", s, TypeSignature::OptionalType(Box::new(otype.clone()))),
            Self::Response(s, oktype, errtype) => write!(f, "({} {})", s, TypeSignature::ResponseType(Box::new((oktype.clone(), errtype.clone())))),
            Self::Callable(s, ctype) => write!(f, "({} {})", s, TypeSignature::CallableType(ctype.clone())),
            Self::ListUnion(s, _utypes) => write!(f, "({} {})", s, self.type_str()),
            Self::TraitReference(s, ttype) => write!(f, "({} {})", s, TypeSignature::TraitReferenceType(ttype.clone()))
        }
    }
}

impl Sym {
    pub fn from_name_and_type_signature(name: &ClarityName, type_signature: &TypeSignature) -> Self {
        match type_signature {
            TypeSignature::NoType => {
                panic!("Could not create symbol without type data");
            }
            TypeSignature::IntType => Self::Int(name.into()),
            TypeSignature::UIntType => Self::UInt(name.into()),
            TypeSignature::BoolType => Self::Bool(name.into()),
            TypeSignature::SequenceType(subtype) => Self::Sequence(name.into(), subtype.clone()),
            TypeSignature::PrincipalType => Self::Principal(name.into()),
            TypeSignature::TupleType(type_sig) => Self::Tuple(name.into(), type_sig.clone()),
            TypeSignature::OptionalType(type_sig) => Self::Optional(name.into(), *(*type_sig).clone()),
            TypeSignature::ResponseType(type_sig_ok_err) => {
                let (type_sig_ok, type_sig_err) = &**type_sig_ok_err;
                Self::Response(name.into(), type_sig_ok.clone(), type_sig_err.clone())
            },
            TypeSignature::CallableType(callable_type) => Self::Callable(name.into(), callable_type.clone()),
            TypeSignature::ListUnionType(subtypes) => Self::ListUnion(name.into(), subtypes.clone()),
            TypeSignature::TraitReferenceType(trait_id) => Self::TraitReference(name.into(), trait_id.clone())
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FullName(pub QualifiedContractIdentifier, pub ClarityName);

impl fmt::Display for FullName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}.{}", &self.0, &self.1)
    }
}

impl FullName {
    pub fn name(&self) -> &ClarityName {
        &self.1
    }

    pub fn contract_id(&self) -> &QualifiedContractIdentifier {
        &self.0
    }

    pub fn root(contract_id: QualifiedContractIdentifier) -> Self {
        Self(contract_id, "root_-_-_-_-_-_-_-_-_-_-_-root".try_into().expect("infallible"))
    }
}

impl TryFrom<&str> for FullName {
    type Error = Error;
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        let mut parts =  s.split(".");
        let Some(contract_addr_str) = parts.next() else {
            return Err(Error::Invalid("Missing contract address".into()));
        };
        let Some(contract_name_str) = parts.next() else {
            return Err(Error::Invalid("Missing contract name".into()));
        };
        let Some(func_name_str) = parts.next() else {
            return Err(Error::Invalid("Missing function name".into()));
        };
        if let Some(extra_str) = parts.next() {
            return Err(Error::Invalid(format!("Extra name component '{extra_str}' in '{contract_addr_str}.{contract_name_str}.{func_name_str}'")));
        }

        let Ok(contract_id) = QualifiedContractIdentifier::parse(&format!("{contract_addr_str}.{contract_name_str}")) else {
            return Err(Error::Invalid("Failed to parse qualified contract identifier".into()));
        };
        let Ok(func_name) = ClarityName::try_from(func_name_str) else {
            return Err(Error::Invalid("Failed to parse function name".into()));
        };
        Ok(Self(contract_id, func_name))
    }
}

impl TryFrom<&String> for FullName {
    type Error = Error;
    fn try_from(s: &String) -> Result<Self, Self::Error> {
        Self::try_from(s.as_str())
    }
}

impl TryFrom<String> for FullName {
    type Error = Error;
    fn try_from(s: String) -> Result<Self, Self::Error> {
        Self::try_from(s.as_str())
    }
}

/// computations over symbols.
/// not all relations are well-defined here; we rely on the Clarity type-checker for this.
#[derive(Debug, Clone, Eq)]
pub enum SymOp {
    Constant(Value),
    Variable(Sym),
    LoadedDataVariable(FullName, Box<SymOp>),
    Add(Vec<Box<SymOp>>),
    Subtract(Vec<Box<SymOp>>),
    Multiply(Vec<Box<SymOp>>),
    Divide(Vec<Box<SymOp>>),
    ToInt(Box<SymOp>),
    ToUInt(Box<SymOp>),
    Modulo(Box<SymOp>, Box<SymOp>),
    Power(Box<SymOp>, Box<SymOp>),
    Sqrti(Box<SymOp>),
    Log2(Box<SymOp>),
    And(Vec<Box<SymOp>>),
    Or(Vec<Box<SymOp>>),
    Not(Box<SymOp>),
    Greater(Box<SymOp>, Box<SymOp>),
    Geq(Box<SymOp>, Box<SymOp>),
    Equals(Vec<Box<SymOp>>),
    Leq(Box<SymOp>, Box<SymOp>),
    Less(Box<SymOp>, Box<SymOp>),
    Append(Box<SymOp>, Box<SymOp>),
    Concat(Vec<Box<SymOp>>),
    AsMaxLen(Box<SymOp>, Box<SymOp>),
    Len(Box<SymOp>),
    ElementAt(Box<SymOp>, Box<SymOp>),
    IndexOf(Box<SymOp>, Box<SymOp>),
    BuffToIntLe(Box<SymOp>),
    BuffToUIntLe(Box<SymOp>),
    BuffToIntBe(Box<SymOp>),
    BuffToUIntBe(Box<SymOp>),
    IsStandard(Box<SymOp>),
    PrincipalDestruct(Box<SymOp>),
    PrincipalConstruct(Box<SymOp>, Box<SymOp>, Option<Box<SymOp>>),
    StringToInt(Box<SymOp>),
    StringToUInt(Box<SymOp>),
    IntToAscii(Box<SymOp>),
    IntToUtf8(Box<SymOp>),
    ListCons(Vec<Box<SymOp>>),
    FetchVar(FullName),
    SetVar(FullName, Box<SymOp>),
    FetchEntry(FullName, Box<SymOp>),
    LoadedMapEntry(FullName, Box<SymOp>, Option<Box<SymOp>>),
    SetEntry(FullName, Box<SymOp>, Box<SymOp>),
    InsertEntry(FullName, Box<SymOp>, Box<SymOp>),
    DeleteEntry(FullName, Box<SymOp>),
    TupleCons(Vec<(ClarityName, Box<SymOp>)>),
    TupleGet(ClarityName, Box<SymOp>),
    TupleMerge(Box<SymOp>, Box<SymOp>),
    Hash160(Box<SymOp>),
    Sha256(Box<SymOp>),
    Sha512(Box<SymOp>),
    Sha512Trunc256(Box<SymOp>),
    Keccak256(Box<SymOp>),
    Secp256k1Recover(Box<SymOp>, Box<SymOp>),
    Secp256k1Verify(Box<SymOp>, Box<SymOp>, Box<SymOp>),
    ContractOf(Box<SymOp>),
    PrincipalOf(Box<SymOp>),
    GetBurnBlockInfo(ClarityName, Box<SymOp>),
    IsOkay(Box<SymOp>),
    IsErr(Box<SymOp>),
    IsSome(Box<SymOp>),
    IsNone(Box<SymOp>),
    UnwrapPanic(Box<SymOp>),
    UnwrapErrPanic(Box<SymOp>),
    ConsError(Box<SymOp>),
    ConsOkay(Box<SymOp>),
    ConsSome(Box<SymOp>),
    GetTokenBalance(FullName, Box<SymOp>),
    GetNftOwner(FullName, Box<SymOp>),
    TransferToken(FullName, Box<SymOp>, Box<SymOp>, Box<SymOp>),
    TransferNft(FullName, Box<SymOp>, Box<SymOp>, Box<SymOp>),
    MintToken(FullName, Box<SymOp>, Box<SymOp>),
    MintNft(FullName, Box<SymOp>, Box<SymOp>),
    GetTokenSupply(FullName),
    BurnToken(FullName, Box<SymOp>),
    BurnNft(FullName, Box<SymOp>, Box<SymOp>),
    GetStxBalance(Box<SymOp>),
    StxTransfer(Box<SymOp>, Box<SymOp>, Box<SymOp>),
    StxTransferMemo(Box<SymOp>, Box<SymOp>, Box<SymOp>, Box<SymOp>),
    StxBurn(Box<SymOp>),
    StxGetAccount(Box<SymOp>),
    BitwiseAnd(Vec<Box<SymOp>>),
    BitwiseOr(Vec<Box<SymOp>>),
    BitwiseXor(Vec<Box<SymOp>>),
    BitwiseNot(Box<SymOp>),
    BitwiseLShift(Box<SymOp>, Box<SymOp>),
    BitwiseRShift(Box<SymOp>, Box<SymOp>),
    Slice(Box<SymOp>, Box<SymOp>, Box<SymOp>),
    ToConsensusBuff(Box<SymOp>),
    FromConsensusBuff(TypeSignature, Box<SymOp>),
    ReplaceAt(Box<SymOp>, Box<SymOp>, Box<SymOp>),
    GetStacksBlockInfo(ClarityName, Box<SymOp>),
    GetTenureInfo(ClarityName, Box<SymOp>),
    ContractHash(Box<SymOp>),
    ToAscii(Box<SymOp>),
    // TODO: are these just symbolic sugar?
    RestrictAssets(Box<SymOp>, Box<SymOp>, Box<SymOp>),
    AsContractSafe(Box<SymOp>, Box<SymOp>),
    AllowanceWithStx(Box<SymOp>),
    AllowanceWithFt(Box<SymOp>, ClarityName, Box<SymOp>),
    AllowanceWithNft(Box<SymOp>, ClarityName, Box<SymOp>),
    AllowanceWithStacking(Box<SymOp>),
    AllowanceAll,
    Secp256r1Verify(Box<SymOp>, Box<SymOp>, Box<SymOp>),
    VerifyMerkleProof(Box<SymOp>, Box<SymOp>, Box<SymOp>, Box<SymOp>, Box<SymOp>),
    GetBitcoinTxOutput(Box<SymOp>, Box<SymOp>),
    // INTERNAL -- symbolic execution detected an unconditional panic
    Panic,
    // INTERNAL -- a "stub" function call that will not be explored.
    FunctionCall(FullName, Vec<Box<SymOp>>),
}

/// Compare two vectors of symops, as part of comparing a commutative operation where order doesn't
/// matter.  Unfortunately, we can't sort these since PartialOrd isn't implementable for Value
/// (precluding PartialOrd for SymOp::Constant), so for now, we cheat by comparing the string
/// representations (which uniquely identify a symop) 
fn cmp_commutative_symop(s1: &[Box<SymOp>], s2: &[Box<SymOp>]) -> bool {
    if s1.len() != s2.len() {
        return false;
    }

    let mut terms_1 : Vec<_> = s1
        .iter()
        .map(|s| s.to_string())
        .collect();

    let mut terms_2 : Vec<_> = s2
        .iter()
        .map(|s| s.to_string())
        .collect();

    terms_1.sort();
    terms_2.sort();
    terms_1 == terms_2
}

/// Equality implementation that takes into account commutativity
/// TODO: do full polynomial comparison
impl PartialEq for SymOp {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Constant(v1), Self::Constant(v2)) => v1 == v2,
            (Self::Variable(s1), Self::Variable(s2)) => s1 == s2,
            (Self::LoadedDataVariable(n1, s1), Self::LoadedDataVariable(n2, s2)) => n1 == n2 && s1 == s2,
            (Self::Add(s1), Self::Add(s2)) => cmp_commutative_symop(s1, s2),
            (Self::Subtract(s1), Self::Subtract(s2)) => s1 == s2,
            (Self::Multiply(s1), Self::Multiply(s2)) => cmp_commutative_symop(s1, s2),
            (Self::Divide(s1), Self::Divide(s2)) => s1 == s2,
            (Self::And(s1), Self::And(s2)) => cmp_commutative_symop(s1, s2),
            (Self::Or(s1), Self::Or(s2)) => cmp_commutative_symop(s1, s2),
            (Self::Equals(s1), Self::Equals(s2)) => cmp_commutative_symop(s1, s2),
            (Self::BitwiseAnd(s1), Self::BitwiseAnd(s2)) => cmp_commutative_symop(s1, s2),
            (Self::BitwiseOr(s1), Self::BitwiseOr(s2)) => cmp_commutative_symop(s1, s2),
            (Self::BitwiseXor(s1), Self::BitwiseXor(s2)) => cmp_commutative_symop(s1, s2),
            (Self::BitwiseNot(s1), Self::BitwiseNot(s2)) => s1 == s2,
            (Self::ToInt(s1), Self::ToInt(s2)) => s1 == s2,
            (Self::ToUInt(s1), Self::ToUInt(s2)) => s1 == s2,
            (Self::Modulo(s11, s12), Self::Modulo(s21, s22)) => s11 == s21 && s12 == s22,
            (Self::Power(s11, s12), Self::Power(s21, s22)) => s11 == s21 && s12 == s22,
            (Self::Sqrti(s1), Self::Sqrti(s2)) => s1 == s2,
            (Self::Log2(s1), Self::Log2(s2)) => s1 == s2,
            (Self::Not(s1), Self::Not(s2)) => s1 == s2,
            (Self::Greater(s11, s12), Self::Greater(s21, s22)) => s11 == s21 && s12 == s22,
            (Self::Geq(s11, s12), Self::Geq(s21, s22)) => s11 == s21 && s12 == s22,
            (Self::Leq(s11, s12), Self::Leq(s21, s22)) => s11 == s21 && s12 == s22,
            (Self::Less(s11, s12), Self::Less(s21, s22)) => s11 == s21 && s12 == s22,
            (Self::Append(s11, s12), Self::Append(s21, s22)) => s11 == s21 && s12 == s22,
            (Self::Concat(vs1), Self::Concat(vs2)) => vs1 == vs2,
            (Self::AsMaxLen(s11, s12), Self::AsMaxLen(s21, s22)) => s11 == s21 && s12 == s22,
            (Self::Len(s1), Self::Len(s2)) => s1 == s2,
            (Self::ElementAt(s11, s12), Self::ElementAt(s21, s22)) => s11 == s21 && s12 == s22,
            (Self::IndexOf(s11, s12), Self::IndexOf(s21, s22)) => s11 == s21 && s12 == s22,
            (Self::BuffToIntLe(s1), Self::BuffToIntLe(s2)) => s1 == s2,
            (Self::BuffToUIntLe(s1), Self::BuffToUIntLe(s2)) => s1 == s2,
            (Self::BuffToIntBe(s1), Self::BuffToIntBe(s2)) => s1 == s2,
            (Self::BuffToUIntBe(s1), Self::BuffToUIntBe(s2)) => s1 == s2,
            (Self::IsStandard(s1), Self::IsStandard(s2)) => s1 == s2,
            (Self::PrincipalDestruct(s1), Self::PrincipalDestruct(s2)) => s1 == s2,
            (Self::PrincipalConstruct(s11, s12, s13_opt), Self::PrincipalConstruct(s21, s22, s23_opt)) => s11 == s21 && s12 == s22 && s13_opt == s23_opt,
            (Self::StringToInt(s1), Self::StringToInt(s2)) => s1 == s2,
            (Self::StringToUInt(s1), Self::StringToUInt(s2)) => s1 == s2,
            (Self::IntToAscii(s1), Self::IntToAscii(s2)) => s1 == s2,
            (Self::IntToUtf8(s1), Self::IntToUtf8(s2)) => s1 == s2,
            (Self::ListCons(l1), Self::ListCons(l2)) => l1 == l2,
            (Self::FetchVar(n1), Self::FetchVar(n2)) => n1 == n2,
            (Self::SetVar(n1, s1), Self::SetVar(n2, s2)) => n1 == n2 && s1 == s2,
            (Self::FetchEntry(n1, s1), Self::FetchEntry(n2, s2)) => n1 == n2 && s1 == s2,
            (Self::LoadedMapEntry(n1, s11, o1), Self::LoadedMapEntry(n2, s21, o2)) => n1 == n2 && s11 == s21 && o1 == o2,
            (Self::SetEntry(n1, s11, s12), Self::SetEntry(n2, s21, s22)) => n1 == n2 && s11 == s21 && s12 == s22,
            (Self::InsertEntry(n1, s11, s12), Self::InsertEntry(n2, s21, s22)) => n1 == n2 && s11 == s21 && s12 == s22,
            (Self::DeleteEntry(n1, s1), Self::DeleteEntry(n2, s2)) => n1 == n2 && s1 == s2,
            (Self::TupleCons(t1), Self::TupleCons(t2)) => {
                // equal if sorted
                let mut t1_sorted = t1.clone();
                t1_sorted.sort_by(|a, b| a.0.cmp(&b.0));

                let mut t2_sorted = t2.clone();
                t2_sorted.sort_by(|a, b| a.0.cmp(&b.0));

                t1_sorted.eq(&t2_sorted)
            }
            (Self::TupleGet(n1, s1), Self::TupleGet(n2, s2)) => n1 == n2 && s1 == s2,
            (Self::TupleMerge(s11, s12), Self::TupleMerge(s21, s22)) => s11 == s21 && s12 == s22,
            (Self::Hash160(s1), Self::Hash160(s2)) => s1 == s2,
            (Self::Sha256(s1), Self::Sha256(s2)) => s1 == s2,
            (Self::Sha512(s1), Self::Sha512(s2)) => s1 == s2,
            (Self::Sha512Trunc256(s1), Self::Sha512Trunc256(s2)) => s1 == s2,
            (Self::Keccak256(s1), Self::Keccak256(s2)) => s1 == s2,
            (Self::Secp256k1Recover(s11, s12), Self::Secp256k1Recover(s21, s22)) => s11 == s21 && s12 == s22,
            (Self::Secp256k1Verify(s11, s12, s13), Self::Secp256k1Verify(s21, s22, s23)) => s11 == s21 && s12 == s22 && s13 == s23,
            (Self::ContractOf(s1), Self::ContractOf(s2)) => s1 == s2,
            (Self::PrincipalOf(s1), Self::PrincipalOf(s2)) => s1 == s2,
            (Self::GetBurnBlockInfo(n1, s1), Self::GetBurnBlockInfo(n2, s2)) => n1 == n2 && s1 == s2,
            (Self::IsOkay(s1), Self::IsOkay(s2)) => s1 == s2,
            (Self::IsErr(s1), Self::IsErr(s2)) => s1 == s2,
            (Self::IsSome(s1), Self::IsSome(s2)) => s1 == s2,
            (Self::IsNone(s1), Self::IsNone(s2)) => s1 == s2,
            (Self::UnwrapPanic(s1), Self::UnwrapPanic(s2)) => s1 == s2,
            (Self::UnwrapErrPanic(s1), Self::UnwrapErrPanic(s2)) => s1 == s2,
            (Self::ConsError(s1), Self::ConsError(s2)) => s1 == s2,
            (Self::ConsOkay(s1), Self::ConsOkay(s2)) => s1 == s2,
            (Self::ConsSome(s1), Self::ConsSome(s2)) => s1 == s2,
            (Self::GetTokenBalance(n1, s1), Self::GetTokenBalance(n2, s2)) => n1 == n2 && s1 == s2,
            (Self::GetNftOwner(n1, s1), Self::GetNftOwner(n2, s2)) => n1 == n2 && s1 == s2,
            (Self::TransferToken(n1, s11, s12, s13), Self::TransferToken(n2, s21, s22, s23)) => n1 == n2 && s11 == s21 && s12 == s22 && s13 == s23,
            (Self::TransferNft(n1, s11, s12, s13), Self::TransferNft(n2, s21, s22, s23)) => n1 == n2 && s11 == s21 && s12 == s22 && s13 == s23,
            (Self::MintToken(n1, s11, s12), Self::MintToken(n2, s21, s22)) => n1 == n2 && s11 == s21 && s12 == s22,
            (Self::MintNft(n1, s11, s12), Self::MintNft(n2, s21, s22)) => n1 == n2 && s11 == s21 && s12 == s22,
            (Self::GetTokenSupply(n1), Self::GetTokenSupply(n2)) => n1 == n2,
            (Self::BurnToken(n1, s1), Self::BurnToken(n2, s2)) => n1 == n2 && s1 == s2,
            (Self::BurnNft(n1, s11, s12), Self::BurnNft(n2, s21, s22)) => n1 == n2 && s11 == s21 && s12 == s22,
            (Self::GetStxBalance(s1), Self::GetStxBalance(s2)) => s1 == s2,
            (Self::StxTransfer(s11, s12, s13), Self::StxTransfer(s21, s22, s23)) => s11 == s21 && s12 == s22 && s13 == s23,
            (Self::StxTransferMemo(s11, s12, s13, s14), Self::StxTransferMemo(s21, s22, s23, s24)) => s11 == s21 && s12 == s22 && s13 == s23 && s14 == s24,
            (Self::StxBurn(s1), Self::StxBurn(s2)) => s1 == s2,
            (Self::StxGetAccount(s1), Self::StxGetAccount(s2)) => s1 == s2,
            (Self::BitwiseLShift(s11, s12), Self::BitwiseLShift(s21, s22)) => s11 == s21 && s12 == s22,
            (Self::BitwiseRShift(s11, s12), Self::BitwiseRShift(s21, s22)) => s11 == s21 && s12 == s22,
            (Self::Slice(s11, s12, s13), Self::Slice(s21, s22, s23)) => s11 == s21 && s12 == s22 && s13 == s23,
            (Self::ToConsensusBuff(s1), Self::ToConsensusBuff(s2)) => s1 == s2,
            (Self::FromConsensusBuff(tp1, s1), Self::FromConsensusBuff(tp2, s2)) => tp1 == tp2 && s1 == s2,
            (Self::ReplaceAt(s11, s12, s13), Self::ReplaceAt(s21, s22, s23)) => s11 == s21 && s12 == s22 && s13 == s23,
            (Self::GetStacksBlockInfo(n1, s1), Self::GetStacksBlockInfo(n2, s2)) => n1 == n2 && s1 == s2,
            (Self::GetTenureInfo(n1, s1), Self::GetTenureInfo(n2, s2)) => n1 == n2 && s1 == s2,
            (Self::ContractHash(s1), Self::ContractHash(s2)) => s1 == s2,
            (Self::ToAscii(s1), Self::ToAscii(s2)) => s1 == s2,
            (Self::RestrictAssets(s11, s12, s13), Self::RestrictAssets(s21, s22, s23)) => s11 == s21 && s12 == s22 && s13 == s23,
            (Self::AsContractSafe(s11, s12), Self::AsContractSafe(s21, s22)) => s11 == s21 && s12 == s22,
            (Self::AllowanceWithStx(s1), Self::AllowanceWithStx(s2)) => s1 == s2,
            (Self::AllowanceWithFt(s11, n1, s12), Self::AllowanceWithFt(s21, n2, s22)) => s11 == s21 && n1 == n2 && s12 == s22,
            (Self::AllowanceWithNft(s11, n1, s12), Self::AllowanceWithNft(s21, n2, s22)) =>  s11 == s21 && n1 == n2 && s12 == s22,
            (Self::AllowanceWithStacking(s1), Self::AllowanceWithStacking(s2)) => s1 == s2,
            (Self::AllowanceAll, Self::AllowanceAll) => true,
            (Self::Secp256r1Verify(s11, s12, s13), Self::Secp256r1Verify(s21, s22, s23)) => s11 == s21 && s12 == s22 && s13 == s23,
            (Self::VerifyMerkleProof(s11, s12, s13, s14, s15), Self::VerifyMerkleProof(s21, s22, s23, s24, s25)) => s11 == s21 && s12 == s22 && s13 == s23 && s14 == s24 && s15 == s25,
            (Self::GetBitcoinTxOutput(s11, s12), Self::GetBitcoinTxOutput(s21, s22)) => s11 == s21 && s12 == s22,
            (Self::Panic, Self::Panic) => true,
            (Self::FunctionCall(n1, args1), Self::FunctionCall(n2, args2)) => n1 == n2 && args1 == args2,
            (_, _) => false
        }
    }
}

pub struct SymOpPrettyPrint<'a> {
    inner: &'a SymOp,
    depth: usize
}

impl<'a> SymOpPrettyPrint<'a> {
    pub fn new(inner: &'a SymOp, depth: usize) -> Self {
        Self {
            inner,
            depth
        }
    }
    
    pub fn pretty_print(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let tab = "   ".repeat(self.depth);

        let mut write_ops = |name: &str, ops: &[Box<SymOp>]| {
            writeln!(f, "{tab}({name}")?;
            
            let t : HashMap<String, &Box<SymOp>> = ops.iter().map(|op| (op.to_string(), op)).collect();
            let mut ks : Vec<_> = t.keys().collect();
            ks.sort();
            for k in ks {
                let op = t.get(k).expect("infallible");
                let pp = SymOpPrettyPrint::new(op, self.depth + 1);
                pp.pretty_print(f)?;
            }
            writeln!(f, "{tab})")?;
            Ok::<_, fmt::Error>(())
        };

        match self.inner {
            SymOp::And(ops) => write_ops("and", ops)?,
            SymOp::Or(ops) => write_ops("or", ops)?,
            x => writeln!(f, "{tab}{x}")?
        }

        Ok(())
    }
}

impl<'a> fmt::Display for SymOpPrettyPrint<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        self.pretty_print(f)
    }
}

impl SymOp {
    pub fn to_pretty_string(&self, depth: usize) -> String {
        let pp = SymOpPrettyPrint::new(self, depth);
        let s = format!("{}", &pp);
        s
    }

    fn ops_to_strings(list: &[Box<SymOp>], sort: bool) -> Vec<String> {
        let mut symop_strs : Vec<_> = list
            .iter()
            .map(|symop| format!("{}", symop))
            .collect();

        if sort {
            symop_strs.sort();
        }
        symop_strs
    }

    fn inner_format_prefix(func: &str, list: &[Box<SymOp>], sort: bool, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let symop_strs = Self::ops_to_strings(list, sort);
        let symop_str = symop_strs.join(" ");

        write!(f, "({func} {symop_str})")
    }
    
    fn format_prefix(func: &str, list: &[Box<SymOp>], f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        Self::inner_format_prefix(func, list, false, f)
    }

    fn format_prefix_sorted(func: &str, list: &[Box<SymOp>], f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        Self::inner_format_prefix(func, list, true, f)
    }

    /// Is this symop free of I/O?
    fn is_pure(&self) -> bool {
        match self {
            Self::SetVar(..)
            | Self::FetchVar(..)
            | Self::InsertEntry(..)
            | Self::FetchEntry(..)
            | Self::SetEntry(..)
            | Self::DeleteEntry(..) => false,
            _ => true
        }
    }
    
    /// Is this symop read-only?
    fn is_read_only(&self) -> bool {
        match self {
            Self::SetVar(..)
            | Self::InsertEntry(..)
            | Self::SetEntry(..)
            | Self::DeleteEntry(..) => false,
            _ => true
        }
    }
}

impl Hash for SymOp {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // hack: use .to_string() to guarantee hash equality modulo commutativity
        let self_s = self.to_string();
        self_s.hash(state);
    }
}


/// NOTE: this impl _must_ guarantee that any two distinct symops a and b have distinct string
/// representations!  That is, if a.to_string() == b.to_string(), then a == b.
impl fmt::Display for SymOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::Constant(v) => write!(f, "{}", v),
            Self::Variable(s) => write!(f, "{}", s),
            Self::LoadedDataVariable(name, symop) => {
                if is_debug() {
                    match &**symop {
                        Self::Constant(c) => write!(f, "(loaded-var-const {} {})", name, c),
                        | Self::Variable(v) => write!(f, "(loaded-var-type {} {})", name, v.type_str()),
                        x => write!(f, "(loaded-var-sym {} {})", name, x)
                    }
                }
                else {
                    write!(f, "(loaded-var {} {})", name, symop)
                }
            }
            Self::Add(symops) => Self::format_prefix_sorted("+", symops, f),
            Self::Subtract(symops) => Self::format_prefix("-", symops, f),
            Self::Multiply(symops) => Self::format_prefix_sorted("*", symops, f),
            Self::Divide(symops) => Self::format_prefix("/", symops, f),
            Self::Modulo(op1, op2) => write!(f, "(mod {op1} {op2})"),
            Self::ToInt(op) => write!(f, "(to-int {op})"),
            Self::ToUInt(op) => write!(f, "(to-uint {op})"),
            Self::Power(op1, op2) => write!(f, "(pow {op1} {op2})"),
            Self::Sqrti(op1) => write!(f, "(sqrti {op1})"),
            Self::Log2(op1) => write!(f, "(log2 {op1})"),
            Self::And(symops) => Self::format_prefix_sorted("and", symops, f),
            Self::Or(symops) => Self::format_prefix_sorted("or", symops, f),
            Self::Not(op1) => write!(f, "(not {op1})"),
            Self::Greater(op1, op2) => write!(f, "(> {op1} {op2})"),
            Self::Geq(op1, op2) => write!(f, "(>= {op1} {op2})"),
            Self::Equals(symops) => Self::format_prefix_sorted("is-eq", symops, f),
            Self::Leq(op1, op2) => write!(f, "(<= {op1} {op2})"),
            Self::Less(op1, op2) => write!(f, "(< {op1} {op2})"),
            Self::Append(op1, op2) => write!(f, "(append {op1} {op2})"),
            Self::Concat(ops) => {
                let ops_strs : Vec<_> = ops
                    .iter()
                    .map(|op| op.to_string())
                    .collect();

                let ops_str = ops_strs.join(" ");

                write!(f, "(concat {ops_str})")
            }
            Self::AsMaxLen(op1, op2) => write!(f, "(as-max-len? {op1} {op2})"),
            Self::Len(op1) => write!(f, "(len {op1})"),
            Self::ElementAt(op1, op2) => write!(f, "(element-at {op1} {op2})"),
            Self::IndexOf(op1, op2) => write!(f, "(index-of {op1} {op2})"),
            Self::BuffToIntLe(op1) => write!(f, "(buff-to-int-le {op1})"),
            Self::BuffToUIntLe(op1) => write!(f, "(buff-to-uint-le {op1})"),
            Self::BuffToIntBe(op1) => write!(f, "(buff-to-int-be {op1})"),
            Self::BuffToUIntBe(op1) => write!(f, "(buff-to-uint-be {op1})"),
            Self::IsStandard(op1) => write!(f, "(is-standard {op1})"),
            Self::PrincipalDestruct(op1) => write!(f, "(principal-destruct {op1})"),
            Self::PrincipalConstruct(op1, op2, op3_opt) => match op3_opt {
                Some(op3) => write!(f, "(principal-construct {op1} {op2} {op3})"),
                None => write!(f, "(principal-construct {op1} {op2})"),
            },
            Self::StringToInt(op1) => write!(f, "(string-to-int? {op1})"),
            Self::StringToUInt(op1) => write!(f, "(string-to-uint? {op1})"),
            Self::IntToAscii(op1) => write!(f, "(int-to-ascii {op1})"),
            Self::IntToUtf8(op1) => write!(f, "(int-to-utf8 {op1})"),
            Self::ListCons(symops) => Self::format_prefix("list", symops, f),
            Self::FetchVar(name) => write!(f, "(var-get {name})"),
            Self::SetVar(name, op1) => write!(f, "(var-set {name} {op1})"),
            Self::FetchEntry(name, op1) => write!(f, "(map-get? {name} {op1})"),
            Self::LoadedMapEntry(name, key_op, value_op_opt) => {
                if is_debug() {
                    if let Some(value_op) = value_op_opt.as_ref() {
                        match &**value_op {
                            Self::Constant(c) => write!(f, "(map-entry-const {} {} {})", name, key_op, c),
                            | Self::Variable(v) => write!(f, "(map-entry-type {} {} {} {})", name, key_op, Self::Variable(v.clone()), v.type_str()),
                            x => write!(f, "(map-entry-sym {} {} {})", name, key_op, x),
                        }
                    }
                    else {
                        write!(f, "(map-entry {} {})", name, key_op)
                    }
                }
                else {
                    match value_op_opt.as_ref() {
                        Some(x) => write!(f, "(map-entry {} {} {})", name, key_op, x),
                        None => write!(f, "(map-entry {} {})", name, key_op)
                    }
                }
            }
            Self::SetEntry(name, op1, op2) => write!(f, "(map-set {name} {op1} {op2})"),
            Self::InsertEntry(name, op1, op2) => write!(f, "(map-insert {name} {op1} {op2})"),
            Self::DeleteEntry(name, op1) => write!(f, "(map-delete {name} {op1})"),
            Self::TupleCons(fields) => {
                let mut frags : Vec<_> = fields.iter().map(|(name, op)| format!("{name}: {op}")).collect();
                frags.sort();
                let inner = frags.join(", ");
                write!(f, "{{ {inner} }}")
            }
            Self::TupleGet(name, op1) => write!(f, "(get {name} {op1})"),
            Self::TupleMerge(op1, op2) => write!(f, "(merge {op1} {op2})"),
            Self::Hash160(op1) => write!(f, "(hash160 {op1})"),
            Self::Sha256(op1) => write!(f, "(sha256 {op1})"),
            Self::Sha512(op1) => write!(f, "(sha512 {op1})"),
            Self::Sha512Trunc256(op1) => write!(f, "(sha512/256 {op1})"),
            Self::Keccak256(op1) => write!(f, "(keccak256 {op1})"),
            Self::Secp256k1Recover(op1, op2) => write!(f, "(secp256k1-recover? {op1} {op2})"),
            Self::Secp256k1Verify(op1, op2, op3) => write!(f, "(secp256k1-verify {op1} {op2} {op3})"),
            Self::ContractOf(op1) => write!(f, "(contract-of {op1})"),
            Self::PrincipalOf(op1) => write!(f, "(principal-of {op1})"),
            Self::GetBurnBlockInfo(prop, op1) => write!(f, "(get-burn-block-info {prop} {op1})"),
            Self::IsOkay(op1) => write!(f, "(is-ok {op1})"),
            Self::IsErr(op1) => write!(f, "(is-err {op1})"),
            Self::IsSome(op1) => write!(f, "(is-some {op1})"),
            Self::IsNone(op1) => write!(f, "(is-none {op1})"),
            Self::UnwrapPanic(op1) => write!(f, "(unwrap-panic {op1})"),
            Self::UnwrapErrPanic(op1) => write!(f, "(unwrap-err-panic {op1})"),
            Self::ConsError(op1) => write!(f, "(err {op1})"),
            Self::ConsOkay(op1) => write!(f, "(ok {op1})"),
            Self::ConsSome(op1) => write!(f, "(some {op1})"),
            Self::GetTokenBalance(name, op1) => write!(f, "(ft-get-balance {name} {op1})"),
            Self::GetNftOwner(name, op1) => write!(f, "(nft-get-owner? {name} {op1})"),
            Self::TransferToken(name, op1, op2, op3) => write!(f, "(ft-transfer? {name} {op1} {op2} {op3})"),
            Self::TransferNft(name, op1, op2, op3) => write!(f, "(nft-transfer? {name} {op1} {op2} {op3})"),
            Self::MintToken(name, op1, op2) => write!(f, "(ft-mint? {name} {op1} {op2})"),
            Self::MintNft(name, op1, op2) => write!(f, "(nft-mint? {name} {op1} {op2})"),
            Self::GetTokenSupply(name) => write!(f, "(ft-get-supply {name})"),
            Self::BurnToken(name, op1) => write!(f, "(ft-burn? {name} {op1})"),
            Self::BurnNft(name, op1, op2) => write!(f, "(nft-burn? {name} {op1} {op2})"),
            Self::GetStxBalance(op1) => write!(f, "(stx-get-balance {op1})"),
            Self::StxTransfer(op1, op2, op3) => write!(f, "(stx-transfer? {op1} {op2} {op3})"),
            Self::StxTransferMemo(op1, op2, op3, op4) => write!(f, "(stx-transfer-memo? {op1} {op2} {op3} {op4})"),
            Self::StxBurn(op1) => write!(f, "(stx-burn? {op1})"),
            Self::StxGetAccount(op1) => write!(f, "(stx-account {op1})"),
            Self::BitwiseAnd(symops) => Self::format_prefix_sorted("bit-and", symops, f),
            Self::BitwiseOr(symops) => Self::format_prefix_sorted("bit-or", symops, f),
            Self::BitwiseXor(symops) => Self::format_prefix_sorted("bit-xor", symops, f),
            Self::BitwiseNot(op1) => write!(f, "(bit-not {op1})"),
            Self::BitwiseLShift(op1, op2) => write!(f, "(bit-shift-left {op1} {op2})"),
            Self::BitwiseRShift(op1, op2) => write!(f, "(bit-shift-right {op1} {op2})"),
            Self::Slice(op1, op2, op3) => write!(f, "(slice? {op1} {op2} {op3})"),
            Self::ToConsensusBuff(op1) => write!(f, "(to-consensus-buff? {op1})"),
            Self::FromConsensusBuff(ts, op1) => write!(f, "(from-consensus-buff? {ts} {op1})"),
            Self::ReplaceAt(op1, op2, op3) => write!(f, "(replace-at? {op1} {op2} {op3})"),
            Self::GetStacksBlockInfo(name, op1) => write!(f, "(get-stacks-block-info? {name} {op1})"), 
            Self::GetTenureInfo(name, op1) => write!(f, "(get-tenure-info? {name} {op1})"),
            Self::ContractHash(op1) => write!(f, "(contract-hash {op1})"),
            Self::ToAscii(op1) => write!(f, "(to-ascii? {op1})"),
            Self::Secp256r1Verify(op1, op2, op3) => write!(f, "(secp256r1-verify? {op1} {op2} {op3})"),
            Self::VerifyMerkleProof(op1, op2, op3, op4, op5) => write!(f, "(verify-merkle-proof {op1} {op2} {op3} {op4} {op5})"),
            Self::GetBitcoinTxOutput(op1, op2) => write!(f, "(get-bitcoin-tx-output? {op1} {op2})"),
            Self::Panic => write!(f, "(unconditional panic detected!)"),
            Self::FunctionCall(name, args) => {
                let frags : Vec<_> = args.iter().map(|op| op.to_string()).collect();
                let inner = frags.join(" ");
                write!(f, "({name} {inner})")
            }
            x => {
                error!("formmatter not implemented yet for {:?}", x);
                todo!()
            }
        }
    }
}

impl SymOp {
    pub fn True() -> Self {
        Self::Constant(Value::Bool(true))
    }

    pub fn False() -> Self {
        Self::Constant(Value::Bool(false))
    }

    pub fn none() -> Self {
        Self::Constant(Value::none())
    }
    
    pub fn some(self) -> Self {
        Self::ConsSome(Box::new(self))
    }

    /// get the innermost loaded symop
    fn inner_loaded(&self) -> Option<SymOp> {
        match self {
            Self::LoadedDataVariable(_, op) => op.inner_loaded(),
            Self::LoadedMapEntry(_, _, op_opt) => op_opt.as_ref().and_then(|op| op.inner_loaded()),
            Self::UnwrapPanic(op) => match &**op {
                Self::LoadedDataVariable(_, op) => op.inner_loaded(),
                Self::LoadedMapEntry(_, _, op_opt) => op_opt.as_ref().and_then(|op| op.inner_loaded()),
                Self::UnwrapPanic(op) => op.inner_loaded(),
                Self::UnwrapErrPanic(op) => op.inner_loaded(),
                Self::ConsSome(op) => op.inner_loaded(),
                Self::TupleGet(name, op) => Self::TupleGet(name.clone(), op.clone()).inner_loaded(),
                _ => None,
            },
            Self::UnwrapErrPanic(op) => op.inner_loaded(),
            Self::TupleGet(name, op) => match &**op {
                Self::LoadedDataVariable(_, op) => op.inner_loaded(),
                Self::LoadedMapEntry(_, _, Some(op)) => op.inner_loaded(),
                Self::UnwrapPanic(op) => Self::UnwrapPanic(op.clone()).inner_loaded(),
                Self::UnwrapErrPanic(op) => op.inner_loaded(),
                Self::TupleGet(name, op) => Self::TupleGet(name.clone(), op.clone()).inner_loaded(),
                Self::TupleCons(op_list) => op_list.iter().find(|(op_name, _op_val)| op_name == name).and_then(|(_op_name, op_val)| op_val.inner_loaded()),
                Self::TupleMerge(tuple_op, merge_op) => {
                    if let Self::TupleCons(op_list) = &**merge_op && let Some((_inner_name, inner_op)) = op_list.iter().find(|(op_name, _op_val)| op_name == name) {
                        return inner_op.inner_loaded();
                    }
                    if let Self::TupleCons(op_list) = &**tuple_op && let Some((_inner_name, inner_op)) = op_list.iter().find(|(op_name, _op_val)| op_name == name) {
                        return inner_op.inner_loaded();
                    }
                    merge_op.inner_loaded().or_else(|| tuple_op.inner_loaded())
                },
                Self::ConsSome(op) => op.inner_loaded(),
                _ => None,
            }
            Self::Constant(..) => Some(self.clone()),
            Self::Variable(..) => Some(self.clone()),
            _ => None
        }
    }

    /// Some(true) == uint
    /// Some(false) == int
    /// None == unknown
    pub fn is_unsigned(&self) -> Option<bool> {
        match self {
            Self::Constant(Value::Int(..)) => Some(false),
            Self::Constant(Value::UInt(..)) => Some(true),
            Self::Variable(Sym::Int(..)) => Some(false),
            Self::Variable(Sym::UInt(..)) => Some(true),
            Self::LoadedDataVariable(_, op) => op.is_unsigned(),
            Self::Add(ops) 
            | Self::Subtract(ops)
            | Self::Multiply(ops)
            | Self::Divide(ops)
            | Self::BitwiseAnd(ops)
            | Self::BitwiseOr(ops)
            | Self::BitwiseXor(ops) => {
                for op in ops.iter() {
                    if let Some(s) = op.is_unsigned() {
                        return Some(s);
                    }
                }
                None
            }
            Self::Modulo(op, ..) => op.is_unsigned(),
            Self::Power(op, ..) => op.is_unsigned(),
            Self::Sqrti(op)
            | Self::Log2(op)
            | Self::BitwiseNot(op) => op.is_unsigned(),
            Self::Len(..) => Some(true),
            Self::ElementAt(op, ..) => {
                if let Self::ListCons(inners) = &**op {
                    for inner in inners.iter() {
                        if let Some(s) = inner.is_unsigned() {
                            return Some(s);
                        }
                    }
                    None
                }
                else {
                    op.is_unsigned()
                }
            }
            Self::IndexOf(..) => Some(true),
            Self::ToInt(..)
            | Self::BuffToIntLe(..)
            | Self::BuffToIntBe(..)
            | Self::StringToInt(..) => Some(false),
            Self::ToUInt(..)
            | Self::BuffToUIntLe(..)
            | Self::BuffToUIntBe(..)
            | Self::StringToUInt(..) => Some(true),
            Self::TupleGet(_name, op) => op.inner_loaded().and_then(|op| op.is_unsigned()),
            Self::UnwrapPanic(op) => op.inner_loaded().and_then(|op| op.is_unsigned()),
            Self::UnwrapErrPanic(op) => op.inner_loaded().and_then(|op| op.is_unsigned()),
            Self::LoadedMapEntry(_, _, Some(op)) => op.is_unsigned(),
            _ => None
        }
    }

    pub fn is_constant(&self) -> bool {
        if let Self::Constant(..) = self {
            true
        }
        else {
            false
        }
    }

    /// Could some form of this symbol produce (optional (tuple ..))?
    pub fn maybe_produces_optional_tuple(&self) -> bool {
        match self {
            Self::Constant(Value::Optional(..))
            | Self::Variable(Sym::Optional(..))
            | Self::ElementAt(..)
            | Self::FetchEntry(..)
            | Self::LoadedMapEntry(..)
            | Self::ConsSome(..)
            | Self::FromConsensusBuff(..) => true,
            Self::LoadedDataVariable(_, sym) => sym.maybe_produces_optional_tuple(),
            _ => false
        }
    }

    pub fn add(self, other: SymOp) -> Self {
        match self {
            Self::Add(mut ops) => {
                ops.push(Box::new(other));
                Self::Add(ops)
            }
            x => {
                Self::Add(vec![Box::new(x), Box::new(other)])
            }
        }
    }
    
    pub fn subtract(self, other: SymOp) -> Self {
        match self {
            Self::Subtract(mut ops) => {
                ops.push(Box::new(other));
                Self::Subtract(ops)
            }
            x => {
                Self::Subtract(vec![Box::new(x), Box::new(other)])
            }
        }
    }
    
    pub fn multiply(self, other: SymOp) -> Self {
        match self {
            Self::Multiply(mut ops) => {
                ops.push(Box::new(other));
                Self::Multiply(ops)
            }
            x => {
                Self::Multiply(vec![Box::new(x), Box::new(other)])
            }
        }
    }
    
    pub fn divide(self, other: SymOp) -> Self {
        match self {
            Self::Divide(mut ops) => {
                ops.push(Box::new(other));
                Self::Divide(ops)
            }
            x => {
                Self::Divide(vec![Box::new(x), Box::new(other)])
            }
        }
    }

    pub fn concat(self, other: SymOp) -> Self {
        match self {
            Self::Concat(mut ops) => {
                ops.push(Box::new(other));
                Self::Concat(ops)
            }
            x => {
                Self::Concat(vec![Box::new(x), Box::new(other)])
            }
        }
    }
    
    pub fn bitwise_and(self, other: SymOp) -> Self {
        match self {
            Self::BitwiseAnd(mut ops) => {
                ops.push(Box::new(other));
                Self::BitwiseAnd(ops)
            }
            x => {
                Self::BitwiseAnd(vec![Box::new(x), Box::new(other)])
            }
        }
    }
    
    pub fn bitwise_or(self, other: SymOp) -> Self {
        match self {
            Self::BitwiseOr(mut ops) => {
                ops.push(Box::new(other));
                Self::BitwiseOr(ops)
            }
            x => {
                Self::BitwiseOr(vec![Box::new(x), Box::new(other)])
            }
        }
    }

    pub fn bitwise_xor(self, other: SymOp) -> Self {
        match self {
            Self::BitwiseXor(mut ops) => {
                ops.push(Box::new(other));
                Self::BitwiseXor(ops)
            }
            x => {
                Self::BitwiseXor(vec![Box::new(x), Box::new(other)])
            }
        }
    }

    pub fn and(self, other: SymOp) -> Self {
        match self {
            Self::And(mut ops) => {
                ops.push(Box::new(other));
                Self::And(ops)
            }
            x => {
                Self::And(vec![Box::new(x), Box::new(other)])
            }
        }
    }
    
    pub fn or(self, other: SymOp) -> Self {
        match self {
            Self::And(mut ops) => {
                ops.push(Box::new(other));
                Self::And(ops)
            }
            x => {
                Self::And(vec![Box::new(x), Box::new(other)])
            }
        }
    }

    pub fn not(self) -> Self {
        Self::Not(Box::new(self))
    }

    pub fn equals(self, other: SymOp) -> Self {
        match self {
            Self::Equals(mut ops) => {
                ops.push(Box::new(other));
                Self::Equals(ops)
            }
            x => {
                Self::Equals(vec![Box::new(x), Box::new(other)])
            }
        }
    }

    pub fn list_cons(self, other: SymOp) -> Self {
        match self {
            Self::ListCons(mut ops) => {
                ops.push(Box::new(other));
                Self::ListCons(ops)
            },
            Self::Constant(Value::Sequence(SequenceData::List(mut list_data))) => {
                let mut items : Vec<_> = list_data
                    .take_items()
                    .into_iter()
                    .map(|v| Box::new(SymOp::Constant(v)))
                    .collect();

                items.push(Box::new(other));
                Self::ListCons(items)
            },
            x => {
                Self::ListCons(vec![Box::new(x)])
            }
        }
    }
    
    /// If this is a boolean SymOp, try to convert it into a Predicate
    pub fn try_as_predicate(&self) -> Result<Predicate, Error> {
        match self {
            Self::Constant(Value::Bool(true)) => {
                Ok(Predicate::True)
            }
            Self::Constant(Value::Bool(false)) => {
                Ok(Predicate::False)
            }
            Self::LoadedDataVariable(name, symop) => {
                Ok(Predicate::Identity(Self::LoadedDataVariable(name.clone(), symop.clone())))
            }
            Self::Greater(symop1, symop2) => {
                Ok(Predicate::Greater((**symop1).clone(), (**symop2).clone()))
            }
            Self::Geq(symop1, symop2) => {
                Ok(Predicate::Geq((**symop1).clone(), (**symop2).clone()))
            }
            Self::Less(symop1, symop2) => {
                Ok(Predicate::Less((**symop1).clone(), (**symop2).clone()))
            }
            Self::Leq(symop1, symop2) => {
                Ok(Predicate::Leq((**symop1).clone(), (**symop2).clone()))
            }
            Self::Equals(symops) => {
                // the typechecker will have determined that there are at least two symops
                Ok(Predicate::Equals(symops.clone().into_iter().map(|s| *s).collect()))
            }
            Self::And(symops) => {
                // the typechecker will have determined that there are at least two symops
                let first = symops.get(0).ok_or_else(|| Error::Bug("And has 0 arguments".into()))?;
                let mut pred = first.try_as_predicate()?;
                for next in symops.get(1..).ok_or_else(|| Error::Bug("And has 1 argument".into()))?.iter() {
                    pred = pred.and(next.try_as_predicate()?);
                }
                Ok(pred)
            }
            Self::Or(symops) => {
                // the typechecker will have determined that there are at least two symops
                let first = symops.get(0).ok_or_else(|| Error::Bug("is-eq has 0 arguments".into()))?;
                let mut pred = first.try_as_predicate()?;
                for next in symops.get(1..).ok_or_else(|| Error::Bug("is-eq has 1 argument".into()))?.iter() {
                    pred = pred.or(next.try_as_predicate()?);
                }
                Ok(pred)
            }
            Self::Not(symop) => {
                let p = symop.try_as_predicate()?;
                Ok(Predicate::Not(Box::new(p)))
            }
            x => {
                Ok(Predicate::Identity(x.clone()))
            }
        }
    }

    /// Fold an *associative* variadic function over inner symops that simplify to constants
    /// Only works for context-free native functions
    fn simplify_assoc_variadic<I, D, C>(func_name: &str, ops: Vec<Box<SymOp>>, is_identity: I, destruct: D, construct: C) -> Result<SymOp, Error>
    where
        I: Fn(&SymOp) -> bool,
        D: Fn(SymOp) -> Option<Vec<Box<SymOp>>>,
        C: Fn(Vec<Box<SymOp>>) -> SymOp
    {
        let mut consolidated_ops = vec![];
        for op in ops.into_iter() {
            if let Some(inner_ops) = destruct((*op).clone()) {
                for inner_op in inner_ops.into_iter() {
                    let inner_op = inner_op.simplify()?;
                    consolidated_ops.push(Box::new(inner_op));
                }
            }
            else {
                consolidated_ops.push(op);
            }
        }

        let mut identities = vec![];
        let mut non_identities = vec![];
        for cop in consolidated_ops.into_iter() {
            if is_identity(&cop) {
                identities.push(cop);
            }
            else {
                non_identities.push(cop);
            }
        }
        if let Some(i) = identities.pop() {
            if non_identities.len() == 0 {
                consolidated_ops = vec![i];
            }
            else if non_identities.len() == 1 {
                let non_ident = non_identities.pop().expect("unreachable -- failed to pop non_ident from non-empty list");
                return Ok(*non_ident);
            }
            else {
                consolidated_ops = non_identities;
            }
        }
        else {
            consolidated_ops = non_identities;
        }
         
        let mut new_ops = vec![];
        let mut folded = None;
        for op in consolidated_ops {
            let op = op.clone().simplify()?;
            if let Self::Constant(v) = op {
                if let Some(Self::Constant(folded_value)) = folded {
                    let v = Self::context_free_clarity_eval_mainnet(vec![
                        SymbolicExpression::atom(func_name.try_into()?),
                        SymbolicExpression::literal_value(v),
                        SymbolicExpression::literal_value(folded_value),
                    ])?
                    .ok_or_else(|| Error::Bug("Clarity VM evaluated to None".into()))?;
                    folded = Some(Self::Constant(v));
                }
                else {
                    folded = Some(Self::Constant(v));
                }
            }
            else {
                new_ops.push(Box::new(op));
            }
        }
        if let Some(folded) = folded {
            if new_ops.len() > 0 {
                new_ops.insert(0, Box::new(folded));
            }
            else {
                return Ok(folded);
            }
        }
        Ok(construct(new_ops))
    }

    /// Combine constants in a Subtract(..), and remove `- 0`s
    fn combine_sub_constants(ops: Vec<Box<SymOp>>) -> Result<Vec<Box<SymOp>>, Error> {
        let mut constants = vec![];
        let mut syms = vec![];
        for (i, op) in ops.into_iter().enumerate() {
            let op = (*op).simplify()?;
            if let Self::Constant(v) = op {
                if i > 0 && (v == Value::UInt(0) || v == Value::Int(0)) {
                    // x - 0 == x
                    continue;
                }
                constants.push((v, i == 0));
            }
            else {
                syms.push(Box::new(op));
            }
        }

        let mut first = None;
        let mut sum = None;
        for (c, is_first) in constants.into_iter() {
            if is_first {
                first = Some(c);
            }
            else {
                sum = Some(match (sum, c) {
                    (None, x) => x, 
                    (Some(Value::Int(f)), Value::Int(c)) => Value::Int(f.checked_add(c).ok_or_else(|| Error::Arithmetic(format!("{f} + {c}")))?),
                    (Some(Value::UInt(f)), Value::UInt(c)) => Value::UInt(f.checked_add(c).ok_or_else(|| Error::Arithmetic(format!("{f} + {c}")))?),
                    (x, y) => {
                        return Err(Error::Bug(format!("Cannot compute {x:?} and {y:?} (in a subtraction)")));
                    }
                });
            }
        }

        if let Some(v) = first {
            // (- u1 x u2) remains (- u1 x u2)
            // (- u3 x u1) becomes (- u2 x)
            match (v, sum) {
                (f, None) => {
                    syms.insert(0, Box::new(Self::Constant(f)));
                    Ok(syms)
                },
                (Value::UInt(f), Some(Value::UInt(c))) => {
                    if f >= c {
                        syms.insert(0, Box::new(Self::Constant(Value::UInt(f.checked_sub(c).ok_or_else(|| Error::Arithmetic(format!("{f} - {c}")))?))));
                        Ok(syms)
                    }
                    else {
                        // no simplification is possible
                        syms.insert(0, Box::new(Self::Constant(Value::UInt(f))));
                        syms.push(Box::new(Self::Constant(Value::UInt(c))));
                        Ok(syms)
                    }
                },
                (Value::Int(f), Some(Value::Int(c))) => {
                    syms.insert(0, Box::new(Self::Constant(Value::Int(f.checked_sub(c).ok_or_else(|| Error::Arithmetic(format!("{f} - {c}")))?))));
                    Ok(syms)
                },
                (x, y) => {
                    return Err(Error::Bug(format!("Could not combine subtraction constants for {x:?} and {y:?}")));
                }
            }
        }
        else if let Some(v) = sum {
            syms.push(Box::new(Self::Constant(v)));
            Ok(syms)
        }
        else {
            Ok(syms)
        }
    }
   
    /// Make a table to map the string representation of a term to both the term itself, and the
    /// number of times it occurs in `terms`.  This is used to find terms to consolidate.
    /// If a term has a constant multiplier, like k * x for symbol x and constant k, then use k as
    /// the count.
    /// The return value maps the String representation of a term to the term itself, its sign
    /// (i8), and its count (u128).
    fn make_term_count_table(terms: Vec<Box<SymOp>>) -> Result<HashMap<String, (Box<SymOp>, i8, u128)>, Error> {
        let mut table = HashMap::new();
        for term in terms.into_iter() {
            // split k * x, and use x as the symbol identifier and k as the count
            let (sign, count, term) = if let Self::Multiply(inner) = *term {
                let mut constants_uint = vec![];
                let mut constants_int = vec![];
                let mut terms = vec![];
                for term in inner.into_iter() {
                    if let SymOp::Constant(Value::UInt(k)) = *term {
                        constants_uint.push(k);
                    }
                    else if let SymOp::Constant(Value::Int(k)) = *term {
                        constants_int.push(k);
                    }
                    else {
                        terms.push(term);
                    }
                }
                if constants_uint.len() > 0 && constants_int.len() > 0 {
                    return Err(Error::Bug("Type checker admitted a product of signed and unsigned integers".into()));
                }
                let (sign, count) = if constants_uint.len() > 0 {
                    let mut count = 1u128;
                    for k in constants_uint.iter() {
                        count = count.checked_mul(*k).ok_or_else(|| Error::Bug("Integer overflow: could not combine multiplicative constants".into()))?;
                    }
                    (1, count)
                }
                else if constants_int.len() > 0 {
                    let mut count = 1i128;
                    for k in constants_int.iter() {
                        count = count.checked_mul(*k).ok_or_else(|| Error::Bug("Integer overflow: could not combine multiplicative constants".into()))?;
                    }
                    if count >= 0 {
                        let count = u128::try_from(count).map_err(|_e| Error::Bug("Could not convert positive i128 to u128".into()))?;
                        (1, count)
                    }
                    else {
                        let count = u128::try_from(-count).map_err(|_e| Error::Bug("Could not convert negated negative i128 to u128".into()))?;
                        (-1, count)
                    }
                }
                else {
                    // no constants, so there's just one of these, and there's no apparent sign
                    (1i8, 1u128)
                };
                let sym_term = if terms.len() == 0 {
                    // all terms were constants, so this is just 1
                    if constants_uint.len() > 0 {
                        SymOp::Constant(Value::UInt(1))
                    }
                    else if constants_int.len() > 0 {
                        SymOp::Constant(Value::Int(1))
                    }
                    else {
                        // there were no terms, but this is unreachable
                        return Err(Error::Bug("unreachable -- no terms in a multiply".into()));
                    }
                }
                else if terms.len() == 1 {
                    // lift out
                    let inner_term = terms.pop().ok_or_else(|| Error::Bug("unreachable: failed to pop inner_term from non-empty terms".into()))?;
                    *inner_term
                }
                else {
                    // still multiplying
                    SymOp::Multiply(terms)
                };
                (sign, count, sym_term)
            }
            else {
                (1i8, 1u128, *term)
            };

            if let Some((_, _, term_count)) = table.get_mut(&term.to_string()) {
                *term_count += count;
            }
            else {
                table.insert(term.to_string(), (Box::new(term), sign, count));
            }
        }
        Ok(table)
    }

    /// Given a table that maps a term's string representation to the term itself and the number of
    /// times it has been seen in a list of terms, and given a _difference_ which maps a term's
    /// string representation to the number of times the term occurs, compute the _difference_
    /// between the two.  For each term in both tables, subtract the count in `diff` from that in
    /// `term_table`.  This is used to reduce a formula like (a + b) - (a + c) to (b - c)
    fn remove_terms(term_table: &mut HashMap<String, (Box<SymOp>, u128)>, diff: HashMap<String, u128>) {
        for (op_s, (_, count)) in term_table.iter() {
            trace!("remove_terms: term_table: count {count} of term {op_s}");
        }
        for (op_s, count) in diff.iter() {
            trace!("remove_terms: diff: count {count} of term {op_s}");
        }

        for (term, diff) in diff.into_iter() {
            let del = if let Some((_, add_count)) = term_table.get_mut(&term) {
                if diff == *add_count {
                    true
                }
                else {
                    if diff > *add_count {
                        panic!("for term {term}, diff = {diff}, add_count = {}", add_count);
                    }
                    *add_count -= diff;
                    false
                }
            }
            else {
                false
            };
            if del {
                term_table.remove(&term);
            }
        }
       
        trace!("remove_terms: {} terms remaining", term_table.len());
        for (op_s, (_, count)) in term_table.iter() {
            trace!("remove_terms: updated term_table: count {count} of term {op_s}");
        }
    }

    fn make_add_sub_term_counts(adds: Vec<Box<SymOp>>, subs: Vec<Box<SymOp>>) -> Result<(HashMap<String, (Box<SymOp>, u128)>, HashMap<String, (Box<SymOp>, u128)>), Error> {
        let add_signed_table = Self::make_term_count_table(adds)?;
        let sub_signed_table = Self::make_term_count_table(subs)?;
    
        for (op_s, (_, sign, count)) in add_signed_table.iter() {
            trace!("add_signed_table: count {count} of term {sign} * {op_s}");
        }
        for (op_s, (_, sign, count)) in sub_signed_table.iter() {
            trace!("sub_signed_table: count {count} of term {sign} * {op_s}");
        }

        // consolidate by sign
        let mut add_table = HashMap::new();
        let mut sub_table = HashMap::new();
        for (term_s, (term, sign, count)) in add_signed_table.into_iter() {
            if sign > 0 {
                add_table.insert(term_s, (term, count));
            }
            else {
                sub_table.insert(term_s, (term, count));
            }
        }
        for (term_s, (term, sign, count)) in sub_signed_table.into_iter() {
            if sign > 0 {
                sub_table.insert(term_s, (term, count));
            }
            else {
                add_table.insert(term_s, (term, count));
            }
        }
        
        Ok((add_table, sub_table))
    }

    fn make_add_sub_term_diffs(add_table: &HashMap<String, (Box<SymOp>, u128)>, sub_table: &HashMap<String, (Box<SymOp>, u128)>) -> (HashMap<String, u128>, HashMap<String, u128>) {
        let mut add_diff = HashMap::new();
        let mut sub_diff = HashMap::new();
        for (add_term, (_, add_count)) in add_table.iter() {
            if let Some((_, sub_count)) = sub_table.get(add_term) {
                trace!("add/sub term {add_term}: add {add_count}, sub {sub_count}");
                if add_count > sub_count {
                    add_diff.insert(add_term.clone(), *sub_count);
                    sub_diff.insert(add_term.clone(), *sub_count);
                }
                else if add_count == sub_count {
                    add_diff.insert(add_term.clone(), *add_count);
                    sub_diff.insert(add_term.clone(), *sub_count);
                }
                else {
                    add_diff.insert(add_term.clone(), *add_count);
                    sub_diff.insert(add_term.clone(), *add_count);
                }
            }
        }
        (add_diff, sub_diff)
    }

    fn reconstitute_adds_subs(add_table: HashMap<String, (Box<SymOp>, u128)>, sub_table: HashMap<String, (Box<SymOp>, u128)>, unsigned: Option<bool>) -> Result<SymOp, Error> {
        let mut new_adds = vec![];
        let mut new_subs = vec![];

        if add_table.len() == 0 {
            // all subtractions
            for (_, (op, count)) in sub_table.into_iter() {
                // NOTE: we don't need to restore negations, since they're already accounted for by
                // the fact that all negated terms were put into the subs table
                if count > 1 {
                    let count = u128::try_from(count).map_err(|_| Error::Bug("Could not cast usize to u128".into()))?;
                    let count_op = Box::new(SymOp::Constant(
                            if unsigned == Some(true) {
                                Value::UInt(count)
                            }
                            else {
                                let count = i128::try_from(count).map_err(|_| Error::Bug("Could not cast usize to i128".into()))?;
                                Value::Int(count)
                            }
                        ));
                    new_subs.push(Box::new(SymOp::Multiply(vec![count_op, op.clone()])));
                }
                else {
                    new_subs.push(op.clone());
                }
            }
        }
        else {
            for (_, (op, count)) in add_table.into_iter() {
                let count = u128::try_from(count).map_err(|_| Error::Bug("Could not cast usize to u128".into()))?;
                let count_op = Box::new(SymOp::Constant(
                        if unsigned == Some(true) {
                            Value::UInt(count)
                        }
                        else {
                            let count = i128::try_from(count).map_err(|_| Error::Bug("Could not cast usize to i128".into()))?;
                            Value::Int(count)
                        }
                    ));
                if count > 1 {
                    new_adds.push(Box::new(SymOp::Multiply(vec![count_op, op.clone()])));
                }
                else {
                    new_adds.push(op.clone());
                }
            }
            for (_, (op, count)) in sub_table.into_iter() {
                let count = u128::try_from(count).map_err(|_| Error::Bug("Could not cast usize to u128".into()))?;
                let count_op = Box::new(SymOp::Constant(
                        if unsigned == Some(true) {
                            Value::UInt(count)
                        }
                        else {
                            let count = i128::try_from(count).map_err(|_| Error::Bug("Could not cast usize to i128".into()))?;
                            Value::Int(count)
                        }
                    ));
                if count > 1 {
                    new_subs.push(Box::new(SymOp::Multiply(vec![count_op, op.clone()])));
                }
                else {
                    new_subs.push(op.clone());
                }
            }
        }
        
        if new_adds.len() == 0 && new_subs.len() == 0 {
            if let Some(unsigned) = unsigned {
                // at least one term
                if unsigned {
                    return Ok(SymOp::Constant(Value::UInt(0)));
                }
                else {
                    return Ok(SymOp::Constant(Value::Int(0)));
                }
            }
            else {
                panic!("Got zero add terms");
            }
        }
        else if new_adds.len() == 0 && new_subs.len() > 0 {
            if let Some(unsigned) = unsigned {
                // at least one term
                if unsigned {
                    new_adds.push(Box::new(SymOp::Constant(Value::UInt(0))));
                }
                else {
                    new_adds.push(Box::new(SymOp::Constant(Value::Int(0))));
                }
            }
            else {
                panic!("Got zero terms");
            }
        }
        
        trace!("reconstitute_add_sub_terms: adds = {:?}", &new_adds);
        trace!("reconstitute_add_sub_terms: subs = {:?}", &new_subs);
        
        if new_adds.len() == 0 && new_subs.len() == 0 {
            panic!("new_adds.len() == 0 and new_subs.len() == 0");
        }

        if new_subs.len() == 0 {
            if new_adds.len() > 1 {
                Ok(SymOp::Add(new_adds))
            }
            else {
                Ok(*new_adds.pop().ok_or_else(|| Error::Bug("unreachable -- adds.len() == 0 and subs.len() == 0".into()))?)
            }
        }
        else {
            if new_adds.len() == 1 {
                let Some(add) = new_adds.pop() else {
                    return Err(Error::Bug("unreachable -- adds.len() == 1 and pop failed".into()));
                };
                if new_subs.len() == 1 {
                    let Some(sub) = new_subs.pop() else {
                        return Err(Error::Bug("unreachable -- subs.len() == 1 and pop failed".into()));
                    };
                    Ok(SymOp::Subtract(vec![add, sub]))
                }
                else {
                    Ok(SymOp::Subtract(vec![add, Box::new(SymOp::Add(new_subs))]))
                }
            }
            else {
                if new_subs.len() == 1 {
                    let Some(sub) = new_subs.pop() else {
                        return Err(Error::Bug("unreachable -- subs.len() == 1 and pop failed".into()));
                    };
                    Ok(SymOp::Subtract(vec![Box::new(SymOp::Add(new_adds)), sub]))
                }
                else {
                    Ok(SymOp::Subtract(vec![Box::new(SymOp::Add(new_adds)), Box::new(SymOp::Add(new_subs))]))
                }
            }
        }
    }

    fn check_add_sub_unsigned(adds: &[Box<SymOp>], subs: &[Box<SymOp>]) -> Option<bool> {
        let mut unsigned = None;
        for i in 0..adds.len() {
            if *adds[i] == SymOp::Constant(Value::UInt(0)) {
                unsigned = Some(true);
            }
            else if *adds[i] == SymOp::Constant(Value::Int(0)) {
                unsigned = Some(false);
            }
            else if let Some(s) = adds[i].is_unsigned() {
                unsigned = Some(s);
            }
            if unsigned.is_some() {
                return unsigned;
            }
        }

        for i in 0..subs.len() {
            if *subs[i] == SymOp::Constant(Value::UInt(0)) {
                unsigned = Some(true);
            }
            else if *subs[i] == SymOp::Constant(Value::Int(0)) {
                unsigned = Some(false);
            }
            else if let Some(s) = subs[i].is_unsigned() {
                unsigned = Some(s);
            }
            if unsigned.is_some() {
                return unsigned;
            }
        }
        unsigned
    }

    /// Combine terms in the form of (a + b + c + ...) - (x + y + z + ...)
    /// `adds` are terms that are to be added together (i.e. a, b, c. ..)
    /// `subs` are terms that are to be summed, and then subtracted from `adds` (i.e. x, y, z, ...)
    fn combine_add_sub_terms(mut adds: Vec<Box<SymOp>>, mut subs: Vec<Box<SymOp>>) -> Result<SymOp, Error> {
        // remove identity elements
        let mut filtered_adds = vec![];
        let unsigned = Self::check_add_sub_unsigned(&adds, &subs);
        for i in 0..adds.len() {
            if *adds[i] == SymOp::Constant(Value::UInt(0)) {
                continue;
            }
            if *adds[i] == SymOp::Constant(Value::Int(0)) {
                continue;
            }
            filtered_adds.push(adds[i].clone());
        }
        adds = filtered_adds;

        let mut filtered_subs = vec![];
        for i in 0..subs.len() {
            if *subs[i] == SymOp::Constant(Value::UInt(0)) {
                continue;
            }
            if *subs[i] == SymOp::Constant(Value::Int(0)) {
                continue;
            }
            filtered_subs.push(subs[i].clone());
        }
        subs = filtered_subs;

        if adds.len() == 0 && subs.len() == 0 {
            if let Some(unsigned) = unsigned {
                // at least one term
                if unsigned {
                    return Ok(SymOp::Constant(Value::UInt(0)));
                }
                else {
                    return Ok(SymOp::Constant(Value::Int(0)));
                }
            }
            else {
                panic!("Got zero add terms");
            }
        }
        else if adds.len() == 0 && subs.len() > 0 {
            if let Some(unsigned) = unsigned {
                // at least one term
                if unsigned {
                    adds.push(Box::new(SymOp::Constant(Value::UInt(0))));
                }
                else {
                    adds.push(Box::new(SymOp::Constant(Value::Int(0))));
                }
            }
            else {
                panic!("Got zero terms");
            }
        }

        let (mut add_table, mut sub_table) = Self::make_add_sub_term_counts(adds, subs)?;
        let (add_diff, sub_diff) = Self::make_add_sub_term_diffs(&add_table, &sub_table);

        trace!("remove add terms");
        Self::remove_terms(&mut add_table, add_diff);
        
        trace!("remove sub terms");
        Self::remove_terms(&mut sub_table, sub_diff);

        Self::reconstitute_adds_subs(add_table, sub_table, unsigned)
    }

    /// flatten a Subtract(..)'s ops to extract constants and combine terms.
    /// Any inner Add(..) and Subtract(..) ops will be removed.
    /// This transforms ops into the form (a + b + c ...) - (x + y + z ...)
    fn flatten_subtractions(ops: Vec<Box<SymOp>>) -> Result<SymOp, Error> {
        // (- (- a b) (+ c d) (- e f) g)
        // ((a - b) - (c + d) - (e - f) - g)
        // (a + f) - (b + c + d + e + g)
        //
        // adds: a, f
        // subs: b, (+ c d), e, g
        
        trace!("flatten_subs original ops: {:?}", &ops);
        
        // special case -- if there's just one op, then this is a negation
        if ops.len() == 1 {
            if let SymOp::Constant(Value::UInt(0)) = &*ops[0] {
                // special special case: drop the negation for zero
                return Ok((*ops[0]).clone());
            }
            if let SymOp::Constant(Value::Int(0)) = &*ops[0] {
                // special special case: drop the negation for zero
                return Ok((*ops[0]).clone());
            }

            return Ok(Self::Subtract(ops));
        }

        let mut adds = vec![];
        let mut subs = vec![];
        
        for (i, op) in ops.into_iter().enumerate() {
            match *op {
                Self::Add(inner) => {
                    if i == 0 {
                        adds.extend(inner.into_iter());
                    }
                    else {
                        subs.extend(inner.into_iter());
                    }
                },
                Self::Subtract(inner) => {
                    let Some(first) = inner.get(0).cloned() else {
                        return Err(Error::Bug("empty subtraction".into()));
                    };
                    let Some(rest) = inner.get(1..) else {
                        return Err(Error::Bug("empty subtraction".into()));
                    };
                    if i == 0 {
                        if rest.len() == 0 {
                            // the first term is a negation
                            subs.push(first);
                        }
                        else {
                            // the first term is a subtraction
                            adds.push(first);
                            subs.extend(rest.to_vec().into_iter());
                        }
                    }
                    else {
                        if rest.len() == 0 {
                            // a subsequent term is a negation.
                            // subtracting a negation is an addition
                            adds.push(first);
                        }
                        else {
                            // a subsequent term is a subtraction
                            subs.push(first);
                            adds.extend(rest.to_vec().into_iter());
                        }
                    }
                }
                x => {
                    if i == 0 {
                        adds.push(Box::new(x));
                    }
                    else {
                        subs.push(Box::new(x));
                    }
                }
            }
        }
        trace!("flatten_subs adds = {:?}", &adds);
        trace!("flatten_subs subs = {:?}", &subs);
       
        let combined = Self::combine_add_sub_terms(adds, subs)?;
        trace!("combine_subs: combined = {:?}", &combined);

        Ok(combined)
    }


    /// flatten additions to extract constants.
    /// Inner Add(..) and Subtract(..) will be removed.
    /// This transforms ops into the form (a + b + c ...) - (x + y + z ...)
    fn flatten_additions(ops: Vec<Box<SymOp>>) -> Result<SymOp, Error> {
        // (+ (- (+ a b) (+ c d) (- e f)) (+ g h))
        //
        // adds: (+ a b), (+ g h)
        // subs: (+ c d), (- e f)
        // 
        // 
        // (a + b - (c + d) - (e - f) + (g + h)
        //
        // (a + b - c - d - e + f + g + h)
        // (a + b + f + g + h) - (c + d + e)
        // (- (+ a b f g h) (+ c d e))
        trace!("flatten_adds: original ops: {:?}", &ops);
        let mut adds = vec![];
        let mut subs = vec![];
        for op in ops.into_iter() {
            match *op {
                Self::Add(inner) => {
                    adds.extend(inner.into_iter());
                },
                Self::Subtract(inner) => {
                    let Some(first) = inner.get(0).cloned() else {
                        return Err(Error::Bug("empty subtraction".into()));
                    };
                    let Some(rest) = inner.get(1..) else {
                        return Err(Error::Bug("empty subtraction".into()));
                    };
                    if rest.len() == 0 {
                        // adding a negation 
                        // adds.push(Box::new(Self::Subtract(inner)));
                        subs.push(first);
                    }
                    else {
                        adds.push(first);
                        subs.extend(rest.to_vec().into_iter())
                    }
                }
                x => {
                    adds.push(Box::new(x));
                }
            }
        }

        trace!("flatten_adds: combine_add_sub_terms adds = {:?}", &adds);
        trace!("flatten_adds: combine_add_sub_terms subs = {:?}", &subs);

        let combined = Self::combine_add_sub_terms(adds, subs)?;
        trace!("flatten_adds: combine_add_sub_terms: combined = {:?}", &combined);

        Ok(combined)
    }

    /// fold constants in subtraction and combine terms
    fn simplify_subtraction(ops: Vec<Box<SymOp>>) -> Result<SymOp, Error> {
        let sub = Self::Subtract(ops.clone());  // for debugging
        let flattened_op = Self::flatten_subtractions(ops)?;

        trace!("{} becomes {}", &sub, &flattened_op);
        let Self::Subtract(ops) = flattened_op else {
            return Ok(flattened_op);
        };

        if ops.len() == 1 {
            // this is a negation
            return Ok(Self::Subtract(ops));
        }
        let Some(first) = ops.get(0) else {
            return Err(Error::Bug("unreachable: Subtract(ops) should have more than one item".into()));
        };
        let Some(rest) = ops.get(1..) else {
            return Err(Error::Bug("unreachable: Subtract(ops) should have at least two items".into()));
        };

        let first = first.clone().simplify()?;

        if rest.len() > 1 {
            // inductive case: `rest` has at least two items.
            // since (x - y - z) == ((x - y) - z), just combine terms
            let mut new_ops = vec![Box::new(first), Box::new(rest[0].clone().simplify()?)];
            for i in 1..rest.len() {
                new_ops = vec![Box::new(Self::Subtract(new_ops)), Box::new(rest[i].clone().simplify()?)];
            }
            return Ok(Self::Subtract(new_ops));
        }

        // base case: `rest` is one item.
        let Some(next) = rest.get(0) else {
            return Err(Error::Bug("unreachable: Subtract(ops): rest should be non-empty".into()));
        };

        let next = next.clone().simplify()?;
        Ok(match (first, next) {
            (Self::Constant(v1), Self::Constant(v2)) => {
                // fold constants
                let diff = match (v1, v2) {
                    (Value::UInt(f), Value::UInt(c)) => Value::UInt(f.checked_sub(c).ok_or_else(|| Error::Arithmetic(format!("{f} - {c}")))?),
                    (Value::Int(f), Value::Int(c)) => Value::Int(f.checked_sub(c).ok_or_else(|| Error::Arithmetic(format!("{f} - {c}")))?),
                    (x, y) => {
                        return Err(Error::Bug(format!("Cannot compute {x} - {y}")));
                    }
                };
                Self::Constant(diff)
            },
            (Self::Add(add_ops), Self::Constant(v1)) => {
                // lift constants out and subtract v1
                let no_const_add_ops = add_ops.clone();
                let (mut consts, mut syms) : (Vec<Box<SymOp>>, Vec<Box<SymOp>>) = add_ops.into_iter().partition(|addand| if let Self::Constant(..) = &**addand { true } else { false });
                if consts.len() > 1 {
                    return Err(Error::Bug(format!("Got multiple constants from simplified Add(..): {consts:?}")));
                }

                if let Some(Self::Constant(const_op)) = consts.pop().map(|c| *c) {
                    // had a constant symop. Try to combine it with `next` if it
                    // won't underflow.  For example:
                    // (x + u1) - u1000 ==> x - u999
                    // (x + u1000) - u1 ==> x + u999
                    match (const_op, v1) {
                        (Value::UInt(f), Value::UInt(c)) => {
                            if f >= c {
                                syms.push(Box::new(Self::Constant(Value::UInt(f.checked_sub(c).ok_or_else(|| Error::Arithmetic(format!("{f} - {c}")))?))));
                                Self::Add(syms)
                            }
                            else {
                                syms.push(Box::new(Self::Constant(Value::UInt(c.checked_sub(f).ok_or_else(|| Error::Arithmetic(format!("{c} - {f}")))?))));
                                Self::Subtract(syms)
                            }
                        }
                        (Value::Int(f), Value::Int(c)) => {
                            if f >= c {
                                syms.push(Box::new(Self::Constant(Value::Int(f.checked_sub(c).ok_or_else(|| Error::Arithmetic(format!("{f} - {c}")))?))));
                                Self::Add(syms)
                            }
                            else {
                                syms.push(Box::new(Self::Constant(Value::Int(c.checked_sub(f).ok_or_else(|| Error::Arithmetic(format!("{f} - {c}")))?))));
                                Self::Subtract(syms)
                            }
                        }
                        (x, y) => {
                            return Err(Error::Bug(format!("Cannot compute {x} - {y}")));
                        }
                    }
                }
                else {
                    // no constant symops in add_ops
                    Self::Subtract(vec![Box::new(Self::Add(no_const_add_ops)), Box::new(Self::Constant(v1))])
                }
            }
            (Self::Constant(v1), Self::Add(add_ops)) => {
                // lift constants out and subtract from v1
                let no_const_add_ops = add_ops.clone();
                let (mut consts, mut syms) : (Vec<Box<SymOp>>, Vec<Box<SymOp>>) = add_ops.into_iter().partition(|addand| if let Self::Constant(..) = &**addand { true } else { false });
                if consts.len() > 1 {
                    return Err(Error::Bug(format!("Got multiple constants from simplified Add(..): {consts:?}")));
                }
                if let Some(Self::Constant(const_op)) = consts.pop().map(|c| *c) {
                    // had a constant symop. Try to combine it with `next` if it
                    // won't underflow.  For example:
                    // u1000 - (x + u1) ==> u999 - x
                    // u1 - (x + u1000) doens't reduce, since -x cannot be a uint
                    match (v1, const_op) {
                        (Value::UInt(f), Value::UInt(c)) => {
                            if f >= c {
                                syms.insert(0, Box::new(Self::Constant(Value::UInt(f.checked_sub(c).ok_or_else(|| Error::Arithmetic(format!("{f} - {c}")))?))));
                                Self::Subtract(syms)
                            }
                            else {
                                Self::Subtract(vec![Box::new(Self::Constant(Value::UInt(f))), Box::new(Self::Add(no_const_add_ops))])
                            }
                        }
                        (Value::Int(f), Value::Int(c)) => {
                            syms.insert(0, Box::new(Self::Constant(Value::Int(f.checked_sub(c).ok_or_else(|| Error::Arithmetic(format!("{f} - {c}")))?))));
                            Self::Subtract(syms)
                        }
                        (x, y) => {
                            return Err(Error::Bug(format!("Cannot compute {x} - {y}")));
                        }
                    }
                }
                else {
                    // no constant symops in add_ops
                    Self::Subtract(vec![Box::new(Self::Constant(v1)), Box::new(Self::Add(no_const_add_ops))])
                }
            }
            (Self::Subtract(mut sub_ops), Self::Constant(v1)) => {
                // (x - u100) - u200 becomes
                // (x - u100 - u200) becomes
                // (x - u300)
                sub_ops.push(Box::new(Self::Constant(v1)));
                let mut syms = Self::combine_sub_constants(sub_ops)?;
                if syms.len() == 1 {
                    let Some(c) = syms.pop() else { unreachable!() };
                    *c
                }
                else {
                    Self::Subtract(syms)
                }
            }
            (Self::Constant(v1), Self::Subtract(sub_ops)) => {
                // (u100 - (x - u200)) becomes
                // (u100 + u200) - x becomes
                // u300 - x
                let Some(first_subop) = sub_ops.get(0) else {
                    return Err(Error::Bug("No subtraction operands".into()));
                };
                if let Some(rest) = sub_ops.get(1..) {
                    let mut addands = vec![Box::new(Self::Constant(v1.clone()))];
                    addands.extend(rest.to_vec().into_iter());

                    let sum = Self::Add(addands).simplify()?;
                    Self::Subtract(vec![Box::new(sum), first_subop.clone()])
                }
                else {
                    Self::Subtract(vec![Box::new(Self::Constant(v1)), first_subop.clone()])
                }
            }
            (x, y) => {
                Self::Subtract(vec![Box::new(x), Box::new(y)])
            }
        })
    }

    /// Get a vector of 1i8 and -1i8 of signs for the inner ops of either an Add(..) or
    /// Subtract(..)
    fn get_op_signs(op: SymOp) -> Vec<(i8, Box<SymOp>)> {
        let signs : Vec<_> = if let Self::Add(inner) = op {
            inner.into_iter()
                .map(|op| (1i8, op))
                .collect()
        }
        else if let Self::Subtract(inner) = op {
            let mut signs = vec![];
            for op in inner.into_iter() {
                if signs.len() == 0 {
                    signs.push((1i8, op));
                }
                else {
                    signs.push((-1i8, op));
                }
            }
            signs
        }
        else {
            unreachable!()
        };
        signs
    }

    /// Flatten a multiply.  Multiply out any inner Add(..) or Subtract(..),
    /// and lift any inner Multiply(..) terms out
    pub(crate) fn flatten_multiply(ops: Vec<Box<SymOp>>) -> Result<SymOp, Error> {
        let mut multiplied_out = vec![];
        let mut adds = vec![];
        let mut subs = vec![];
        for op in ops.into_iter() {
            if let Self::Add(..) = *op {
                adds.push(op);
            }
            else if let Self::Subtract(..) = *op {
                subs.push(op);
            }
            else {
                multiplied_out.push(op);
            }
        }
        
        // lift all Multiply(..) out of multipled_out
        loop {
            let mut new_multiplied_out = vec![];
            let mut found_multiply = false;
            for op in multiplied_out.into_iter() {
                if let Self::Multiply(inner) = *op {
                    new_multiplied_out.extend(inner.into_iter());
                    found_multiply = true;
                }
                else {
                    new_multiplied_out.push(op);
                }
            }
            multiplied_out = new_multiplied_out;
            if !found_multiply {
                break;
            }
        }
        
        trace!("flatten_multiply: adds = {}", &adds.iter().map(|o| o.to_string()).collect::<Vec<_>>().join(", "));
        trace!("flatten_multiply: subs = {}", &subs.iter().map(|o| o.to_string()).collect::<Vec<_>>().join(", "));

        let mut accum_opt : Option<Box<SymOp>> = None;
        for op in adds.into_iter().chain(subs.into_iter()) {
            if let Some(accum) = accum_opt.take() {
                trace!("flatten_multiply: accum = {}", &accum);

                let mut prod_adds = vec![];
                let mut prod_subs = vec![];
                let accum_signs = Self::get_op_signs(*accum);
                let op_signs = Self::get_op_signs(*op);

                for (accum_sign, accum_op) in accum_signs.into_iter() {
                    for (op_sign, op) in op_signs.clone().into_iter() {
                        let sign = accum_sign * op_sign;
                        let p = Self::Multiply(vec![accum_op.clone(), op]);

                        trace!("flatten_multiply: prod = {}", &p);

                        if sign > 0 {
                            prod_adds.push(Box::new(p));
                        }
                        else {
                            prod_subs.push(Box::new(p));
                        }
                    }
                }
        
                trace!("flatten_multiply: prod_adds = {}", &prod_adds.iter().map(|o| o.to_string()).collect::<Vec<_>>().join(", "));
                trace!("flatten_multiply: prod_subs = {}", &prod_subs.iter().map(|o| o.to_string()).collect::<Vec<_>>().join(", "));

                let prod = if prod_subs.len() > 0 && prod_adds.len() > 0 {
                    Self::Subtract(vec![Box::new(SymOp::Add(prod_adds)), Box::new(SymOp::Add(prod_subs))])
                }
                else if prod_subs.len() > 0 && prod_adds.len() == 0 {
                    // negate the first term, and subtract the rest
                    let first = prod_subs.pop().ok_or_else(|| Error::Bug("Unreachable -- prod_subs.len() > 0 and pop failed".into()))?;
                    let rest = prod_subs.get(1..).ok_or_else(|| Error::Bug("Unreachable -- prod_subs.len() > 1 and get(1..) failed".into()))?;
                    let first = SymOp::Subtract(vec![first]);
                    let mut all = vec![Box::new(first)];
                    for r in rest.iter() {
                        all.push(r.clone());
                    }
                    Self::Subtract(all)
                }
                else if prod_subs.len() == 0 && prod_adds.len() > 0 {
                    Self::Add(prod_adds)
                }
                else {
                    return Err(Error::Bug("Unreachable -- no terms to multiply".into()));
                };

                trace!("flatten_multiply: prod = {}", &prod);
                accum_opt = Some(Box::new(prod));
            }
            else {
                accum_opt = Some(op);
            }
        }

        // multiply out the remaining terms
        match accum_opt.map(|a| *a) {
            None => {
                Ok(Self::Multiply(multiplied_out))
            }
            Some(Self::Subtract(inner)) => {
                if multiplied_out.len() > 0 {
                    let mult : Vec<_> = inner
                        .into_iter()
                        .map(|op| {
                            let mut prod = multiplied_out.clone();
                            prod.push(op);
                            Box::new(Self::Multiply(prod))
                        })
                        .collect();

                    Ok(Self::Subtract(mult))
                }
                else {
                    Ok(Self::Subtract(inner))
                }
            },
            Some(Self::Add(inner)) => {
                if multiplied_out.len() > 0 {
                    let mult : Vec<_> = inner
                        .into_iter()
                        .map(|op| {
                            let mut prod = multiplied_out.clone();
                            prod.push(op);
                            Box::new(Self::Multiply(prod))
                        })
                        .collect();

                    Ok(Self::Add(mult))
                }
                else {
                    Ok(Self::Add(inner))
                }
            }
            _x => {
                Err(Error::Bug("accum is not an add or subtract".into()))
            }
        }
    }

    /// Fold and propagate constants in a Divide(..)
    /// TODO: polynomial division?
    fn simplify_divide(ops: Vec<Box<SymOp>>) -> Result<SymOp, Error> {
        // don't do fraction reduction, but do remove constant multiplication if the
        // numerator is a multiple of the denominator
        let Some(numer) = ops.get(0) else {
            return Err(Error::Bug("No operands in divide".into()));
        };
        let Some(rest) = ops.get(1..) else {
            return Err(Error::Bug("Divide has only one operand".into()));
        };

        if rest.len() > 1 {
            // inductive case
            // (/ x y z) is equal to (/ (/ x y) z), so group up
            let mut new_ops = vec![Box::new(numer.clone().simplify()?), Box::new(rest[0].clone().simplify()?)];
            for i in 1..rest.len() {
                new_ops = vec![Box::new(Self::Divide(new_ops)), Box::new(rest[i].clone().simplify()?)];
            }
            return Ok(Self::Divide(new_ops));
        }

        // base case
        let Some(denom) = rest.get(0) else {
            return Err(Error::Bug("unreachable -- rest.get(0) is None".into()));
        };

        match (numer.clone().simplify()?, denom.clone().simplify()?) {
            (Self::Constant(v1), Self::Constant(v2)) => {
                let v = Self::context_free_clarity_eval_mainnet(vec![
                    SymbolicExpression::atom("/".try_into()?),
                    SymbolicExpression::literal_value(v1),
                    SymbolicExpression::literal_value(v2),
                ])?
                .ok_or_else(|| Error::Bug("Clarity VM evaluated to None".into()))?;
                Ok(Self::Constant(v))
            },
            (Self::Multiply(numer_ops), Self::Constant(Value::UInt(c))) => {
                if c == 0 {
                    return Err(Error::Arithmetic(format!("(...) / {c}")));
                }
                if c == 1 {
                    // x / 1 == x
                    return Ok(Self::Multiply(numer_ops));
                }
                let numer_ops_no_factoring = numer_ops.clone();
                let (mut consts, mut syms) : (Vec<Box<SymOp>>, Vec<Box<SymOp>>) = numer_ops.into_iter().partition(|n| if let Self::Constant(..) = &**n { true } else { false });
                if consts.len() > 1 {
                    return Err(Error::Bug(format!("Got multiple constants from simplified Multiply(..): {consts:?}")));
                }
                if consts.len() == 0 {
                    // no factoring
                    Ok(Self::Divide(vec![Box::new(Self::Multiply(numer_ops_no_factoring)), Box::new(Self::Constant(Value::UInt(c)))]))
                }
                else {
                    let Some(Self::Constant(Value::UInt(f))) = consts.pop().map(|c| *c) else { unreachable!() };
                    let gcd = integer::gcd(f, c);
                    if gcd == c {
                        // denominator cancels
                        syms.push(Box::new(Self::Constant(Value::UInt(f / gcd))));
                        Ok(Self::Multiply(syms))
                    }
                    else {
                        // numerator and denominator factor
                        syms.push(Box::new(Self::Constant(Value::UInt(f / gcd))));
                        let factored_syms = if syms.len() == 1 {
                            syms.pop().expect("unreachable")
                        }
                        else {
                            Box::new(Self::Multiply(syms))
                        };
                        Ok(Self::Divide(vec![factored_syms, Box::new(Self::Constant(Value::UInt(c / gcd)))]))
                    }
                }
            },
            (Self::Multiply(numer_ops), Self::Constant(Value::Int(c))) => {
                if c == 0 {
                    return Err(Error::Arithmetic(format!("(...) / {c}")));
                }
                if c == 1 {
                    // x / 1 == x
                    return Ok(Self::Multiply(numer_ops));
                }
                let numer_ops_no_factoring = numer_ops.clone();
                let (mut consts, mut syms) : (Vec<Box<SymOp>>, Vec<Box<SymOp>>) = numer_ops.into_iter().partition(|n| if let Self::Constant(..) = &**n { true } else { false });
                if consts.len() > 1 {
                    return Err(Error::Bug(format!("Got multiple constants from simplified Multiply(..): {consts:?}")));
                }
                if consts.len() == 0 {
                    // no factoring
                    Ok(Self::Divide(vec![Box::new(Self::Multiply(numer_ops_no_factoring)), Box::new(Self::Constant(Value::Int(c)))]))
                }
                else {
                    let Some(Self::Constant(Value::Int(f))) = consts.pop().map(|c| *c) else { unreachable!() };
                    let gcd = integer::gcd(f, c);
                    if gcd == c {
                        // denominator cancels
                        syms.push(Box::new(Self::Constant(Value::Int(f / gcd))));
                        Ok(Self::Multiply(syms))
                    }
                    else {
                        // numerator and denominator factor
                        syms.push(Box::new(Self::Constant(Value::Int(f / gcd))));
                        let factored_syms = if syms.len() == 1 {
                            syms.pop().expect("unreachable")
                        }
                        else {
                            Box::new(Self::Multiply(syms))
                        };
                        Ok(Self::Divide(vec![factored_syms, Box::new(Self::Constant(Value::Int(c / gcd)))]))
                    }
                }
            },
            (Self::Constant(Value::UInt(f)), Self::Multiply(denom_ops)) => {
                let denom_ops_no_factoring = denom_ops.clone();
                let (mut consts, mut syms) : (Vec<Box<SymOp>>, Vec<Box<SymOp>>) = denom_ops.into_iter().partition(|n| if let Self::Constant(..) = &**n { true } else { false });
                if consts.len() > 1 {
                    return Err(Error::Bug(format!("Got multiple constants from simplified Multiply(..): {consts:?}")));
                }
                if consts.len() == 0 {
                    // no factoring
                    Ok(Self::Divide(vec![Box::new(Self::Constant(Value::UInt(f))), Box::new(Self::Multiply(denom_ops_no_factoring))]))
                }
                else {
                    let Some(Self::Constant(Value::UInt(c))) = consts.pop().map(|c| *c) else { unreachable!() };
                    if c == 0 {
                        return Err(Error::Arithmetic(format!("{f} / {c}")));
                    }
                    let gcd = integer::gcd(f, c);
                    if gcd == f {
                        // numerator cancels
                        syms.push(Box::new(Self::Constant(Value::UInt(c / gcd))));
                        Ok(Self::Divide(vec![Box::new(Self::Constant(Value::UInt(1))), Box::new(Self::Multiply(syms))]))
                    }
                    else {
                        // numerator and denominator factor
                        syms.push(Box::new(Self::Constant(Value::UInt(c / gcd))));
                        let factored_syms = if syms.len() == 1 {
                            syms.pop().expect("unreachable")
                        }
                        else {
                            Box::new(Self::Multiply(syms))
                        };
                        Ok(Self::Divide(vec![Box::new(Self::Constant(Value::UInt(f / gcd))), factored_syms]))
                    }
                }
            }
            (Self::Constant(Value::Int(f)), Self::Multiply(denom_ops)) => {
                let denom_ops_no_factoring = denom_ops.clone();
                let (mut consts, mut syms) : (Vec<Box<SymOp>>, Vec<Box<SymOp>>) = denom_ops.into_iter().partition(|n| if let Self::Constant(..) = &**n { true } else { false });
                if consts.len() > 1 {
                    return Err(Error::Bug(format!("Got multiple constants from simplified Multiply(..): {consts:?}")));
                }
                if consts.len() == 0 {
                    // no factoring
                    Ok(Self::Divide(vec![Box::new(Self::Constant(Value::Int(f))), Box::new(Self::Multiply(denom_ops_no_factoring))]))
                }
                else {
                    let Some(Self::Constant(Value::Int(c))) = consts.pop().map(|c| *c) else { unreachable!() };
                    if c == 0 {
                        return Err(Error::Arithmetic(format!("{f} / {c}")));
                    }
                    let gcd = integer::gcd(f, c);
                    if gcd == f {
                        // numerator cancels
                        syms.push(Box::new(Self::Constant(Value::Int(c / gcd))));
                        Ok(Self::Divide(vec![Box::new(Self::Constant(Value::Int(1))), Box::new(Self::Multiply(syms))]))
                    }
                    else {
                        // numerator and denominator factor
                        syms.push(Box::new(Self::Constant(Value::Int(c / gcd))));
                        let factored_syms = if syms.len() == 1 {
                            syms.pop().expect("unreachable")
                        }
                        else {
                            Box::new(Self::Multiply(syms))
                        };
                        Ok(Self::Divide(vec![Box::new(Self::Constant(Value::Int(f / gcd))), factored_syms]))
                    }
                }
            }
            (x, y) => {
                Ok(Self::Divide(vec![Box::new(x), Box::new(y)]))
            }
        }
    }
    
    /// Fold and propagate constants through modulus, and do basic factoring
    fn simplify_modulus(numer: Box<SymOp>, denom: Box<SymOp>) -> Result<SymOp, Error> {
        // don't do fraction reduction, but do remove constant multiplication if the
        // numerator is a multiple of the denominator
        match (numer.simplify()?, denom.simplify()?) {
            (Self::Constant(v1), Self::Constant(v2)) => {
                let v = Self::context_free_clarity_eval_mainnet(vec![
                    SymbolicExpression::atom("mod".try_into()?),
                    SymbolicExpression::literal_value(v1),
                    SymbolicExpression::literal_value(v2),
                ])?
                .ok_or_else(|| Error::Bug("Clarity VM evaluated to None".into()))?;
                Ok(Self::Constant(v))
            },
            (Self::Multiply(numer_ops), Self::Constant(Value::UInt(c))) => {
                if c == 0 {
                    return Err(Error::Arithmetic(format!("(...) / {c}")));
                }
                if c == 1 {
                    return Ok(Self::Constant(Value::UInt(0)));
                }
                let numer_ops_no_factoring = numer_ops.clone();
                let mut consts : Vec<Box<SymOp>> = numer_ops.into_iter().filter(|n| if let Self::Constant(..) = &**n { true } else { false }).collect();
                if consts.len() > 1 {
                    return Err(Error::Bug(format!("Got multiple constants from simplified Multiply(..): {consts:?}")));
                }
                if let Some(Self::Constant(Value::UInt(f))) = consts.pop().map(|c| *c) {
                    if f % c == 0 {
                        // (f * x) % c == 0 for any x, so this reduces to 0
                        return Ok(Self::Constant(Value::UInt(0)));
                    }
                }
                // no factoring
                Ok(Self::Modulo(Box::new(Self::Multiply(numer_ops_no_factoring)), Box::new(Self::Constant(Value::UInt(c)))))
            },
            (Self::Multiply(numer_ops), Self::Constant(Value::Int(c))) => {
                if c == 0 {
                    return Err(Error::Arithmetic(format!("(...) / {c}")));
                }
                if c == 1 {
                    return Ok(Self::Constant(Value::Int(0)));
                }
                let numer_ops_no_factoring = numer_ops.clone();
                let mut consts : Vec<Box<SymOp>> = numer_ops.into_iter().filter(|n| if let Self::Constant(..) = &**n { true } else { false }).collect();
                if consts.len() > 1 {
                    return Err(Error::Bug(format!("Got multiple constants from simplified Multiply(..): {consts:?}")));
                }
                if let Some(Self::Constant(Value::Int(f))) = consts.pop().map(|c| *c) {
                    if f % c == 0 {
                        // (f * x) % c == 0 for any x, so this reduces to 0
                        return Ok(Self::Constant(Value::Int(0)));
                    }
                }
                // no factoring
                Ok(Self::Modulo(Box::new(Self::Multiply(numer_ops_no_factoring)), Box::new(Self::Constant(Value::Int(c)))))
            },
            (x, Self::Constant(Value::UInt(c))) => {
                if c == 1 {
                    Ok(Self::Constant(Value::UInt(0)))
                }
                else {
                    Ok(Self::Modulo(Box::new(x), Box::new(Self::Constant(Value::UInt(c)))))
                }
            }
            (x, Self::Constant(Value::Int(c))) => {
                if c == 1 {
                    Ok(Self::Constant(Value::Int(0)))
                }
                else {
                    Ok(Self::Modulo(Box::new(x), Box::new(Self::Constant(Value::Int(c)))))
                }
            }
            (x, y) => {
                Ok(Self::Modulo(Box::new(x), Box::new(y)))
            }
        }
    }

    /// Compute a maximum sequence length, in order to eliminate impossible or tautological comparisons between
    /// `(len X)` and a constant
    fn compute_max_sequence_len(seq_op: &Box<SymOp>) -> Result<usize, Error> {
        let l = match *seq_op {
            Self::Constant(v) => {
                let v = Self::context_free_clarity_eval_mainnet(vec![
                    SymbolicExpression::atom("len".try_into()?),
                    SymbolicExpression::literal_value(v)
                ])?
                .ok_or_else(|| Error::Bug("Clarity VM evaluated to None".into()))?
                .expect_u128()?;
                usize::try_from(v).map_err(|_| Error::Bug("Constant with length greater than usize::MAX".into()))?
            }
            Self::ListCons(inner_ops) => {
                inner_ops.len()
            }
            Self::Append(inner_list, new_item) => {
                let sz = Self::compute_max_sequence_len(inner_list)?;
                sz + 1
            }
            Self::Concat(inner_ops) => {
                let inner_max_lens : Vec<Result<_, _> = inner_ops
                    .iter()
                    .map(|op| Self::compute_max_sequence_len(op))
                    .collect();

                let mut max = 0;
                for inner_max_res in inner_max_lens.into_iter() {
                    max += inner_max_res?;
                }
                max
            },
            Self::AsMaxLen(_, max_len_op) => {
                // max_len_op must be a constant
                let Self::Constant(Value::UInt(v)) = max_len_op else {
                    return Err(Error::Bug("Clarity VM allowed a non-constant maximum length in `as-max-len?`".into()));
                };
                usize::try_from(v).map_err(|_| Error::Bug("Constant with length greater than usize::MAX".into()))?
            }
            Self::LoadedDataVariable(_, inner_op) => {
                Self::compute_max_sequence_len(inner_op)
            }
            Self::UnwrapPanic(inner_op) => {
                Self::compute_max_sequence_len(inner_op)
            }
            Self::UnwrapErrPanic(inner_op) => {
                Self::compute_max_sequence_len(inner_op)
            }
            Self::TupleGet(key, tuple_op) => {

            }
            Self::Hash160(_) => {
                20
            }
            Self::Sha256(_) => {
                32
            }
            Self::Sha512(_) => {
                32
            }
            Self::Sha512Trunc256(_) => {
                32
            }
            Self::Keccak256(_) => {
                32
            }

        }
    }

    /// Combine all inner Self::Equals(..) and Self::Not(Self::Equals(..)) statements that share at
    /// least one non-constant term.
    ///
    /// The terms in op must have been simplifed. In particular, each term is either a constant, or
    /// a symbolic operation with at least one variable (i.e. no symbolic operation over just
    /// constants)
    fn and_flatten_equals(ops: Vec<Box<SymOp>>) -> Result<Vec<Box<SymOp>>, Error> {
        // (and (is-eq a1 b1 c1 ...) (is-eq a1 b2 c2 ...)) becomes
        // (and (is-eq a1 b1 c1 b2 c2)), since both (is-eq ..) lists
        // contain at least one such term a1.
      
        // debug output
        let before_s : Vec<_> = ops.iter().map(|s| s.to_string()).collect();

        // map which terms are found in which ops (identified by op index and term index)
        let mut terms : HashMap<String, Vec<(usize, usize)>> = HashMap::new();
        
        // list of recombined terms
        let mut combined_terms : Vec<Box<SymOp>> = vec![];

        for (i, op) in ops.iter().enumerate() {
            if let Self::Equals(inner) = &**op {
                for (j, term) in inner.iter().enumerate() {
                    let term_s = term.to_string();
                    if let Some(eq_ops) = terms.get_mut(&term_s) {
                        eq_ops.push((i, j));
                    }
                    else {
                        terms.insert(term_s, vec![(i, j)]);
                    }
                }
            }
            else {
                combined_terms.push(op.clone());
            }
        }

        // combine unique terms across multiple (is-eq ..).
        // If a term is present in at least two (is-eq ..), then it only needs to be present in the
        // combined one.
        // All of the terms in the (is-eq ..) lists that this term was present in
        // can be combined into a single (is-eq ..).
        let mut combined_eqs : HashMap<usize, Vec<Box<SymOp>>> = HashMap::new();
        let mut consumed = HashSet::new();

        // sort terms from most-represented to least-represented, so we cull terms that appear in
        // multiple (is-eq ..) lists before those that appear in only one.
        let mut terms_list : Vec<_> = terms
            .into_iter()
            .map(|(term_s, op_idx_list)| (term_s, op_idx_list))
            .collect();

        terms_list.sort_by(|a, b| a.1.len().cmp(&b.1.len()));
        terms_list.reverse();

        for (_term_s, mut op_idx_list) in terms_list.into_iter() {
            let eq_set : HashSet<_> = op_idx_list
                .iter()
                .map(|(op_idx, _)| *op_idx)
                .collect();

            if eq_set.len() == 1 {
                // this term only appears in one (is-eq ..), so put it with the same combined
                // (is-eq ..) list from which it came.
                let (op_idx, term_idx) = op_idx_list.pop().ok_or_else(|| Error::Bug("unreachable -- op_idx_list.len() == 1 and pop failed".into()))?;
                if consumed.contains(&(op_idx, term_idx)) {
                    continue;
                }

                let Self::Equals(inner) = &*ops[op_idx] else {
                    return Err(Error::Bug("index is not an is-eq".into()));
                };
                let op = inner.get(term_idx).ok_or_else(|| Error::Bug("term index is not in is-eq terms".into()))?;
                if let Some(eq_ops) = combined_eqs.get_mut(&op_idx) {
                    eq_ops.push(op.clone());
                }
                else {
                    combined_eqs.insert(op_idx, vec![op.clone()]);
                }
                consumed.insert((op_idx, term_idx));
                trace!("{} combined_eqs = {:?}", &_term_s, &combined_eqs);
            }
            else {
                // this term appears in more than one (is-eq ..), so put all of the other terms in
                // each of its (is-eq ..) list into the same combined (is-eq ..) list, along with
                // this one.
                trace!("{} appears in terms {:?}", &_term_s, &op_idx_list);
                let mut combined_idx = None;
                for (op_idx, term_idx) in op_idx_list.into_iter() {
                    if consumed.contains(&(op_idx, term_idx)) {
                        continue;
                    }
                    let Self::Equals(inner) = &*ops[op_idx] else {
                        return Err(Error::Bug("index is not an is-eq".into()));
                    };
                    let mut retained_inner = vec![];
                    for (j, inner_op) in inner.iter().enumerate() {
                        consumed.insert((op_idx, j));
                        retained_inner.push(inner_op.clone());
                    }

                    let idx = *combined_idx.as_ref().unwrap_or(&op_idx);
                    if let Some(eq_ops) = combined_eqs.get_mut(&idx) {
                        eq_ops.extend(retained_inner.into_iter());
                    }
                    else {
                        combined_eqs.insert(idx, retained_inner);
                    }
                    if combined_idx.is_none() {
                        combined_idx = Some(op_idx);
                    }

                    trace!("{} combined_eqs = {:?}", &_term_s, &combined_eqs);
                }
            }
        }

        trace!("combined_eqs = {:?}", &combined_eqs);
        let combined_eqs : Vec<_> = combined_eqs
            .into_iter()
            .map(|(_, ops)| {
                let uniq : HashMap<String, Box<SymOp>> = ops
                    .into_iter()
                    .map(|op| (op.to_string(), op))
                    .collect();

                let op_uniq : Vec<Box<SymOp>> = uniq
                    .into_iter()
                    .map(|(_, op)| op)
                    .collect();

                Box::new(Self::Equals(op_uniq))
            })
            .collect();

        let after_s : Vec<_> = combined_eqs.iter().map(|s| s.to_string()).collect();
        trace!("and_flatten_equals: before:        {:?}", &before_s);
        trace!("and_flatten_equals: combined_eqs:  {:?}", &after_s);
        
        combined_terms.extend(combined_eqs.into_iter());
       
        trace!("and_flatten_equals: combined_terms:  {:?}", &combined_terms);
        Ok(combined_terms)
    }

    /// Detect and reduce and-equality contradictions in the form of
    /// (and (is-eq a b ...) (not (is-eq a b ...))).
    ///
    /// NOTE: The terms in combined_terms must have been simplifed.
    ///
    /// NOTE: all terms in each (is-eq ..) in `combined_terms` must be unique!
    fn and_equals_contradiction(combined_terms: Vec<Box<SymOp>>) -> Result<Vec<Box<SymOp>>, Error> {
        let mut terms : HashMap<String, Vec<(usize, usize)>> = HashMap::new();
        let mut not_terms : HashMap<String, Vec<(usize, usize)>> = HashMap::new();

        // search for contradictions.
        //   (and (is-eq a b c d e) (not (is-eq a b f g h))) is a contradiction
        for (i, op) in combined_terms.iter().enumerate() {
            if let Self::Equals(inner) = &**op {
                for (j, term) in inner.iter().enumerate() {
                    let term_s = term.to_string();
                    if let Some(eq_ops) = terms.get_mut(&term_s) {
                        eq_ops.push((i, j));
                    }
                    else {
                        terms.insert(term_s, vec![(i, j)]);
                    }
                }
            }
            else if let Self::Not(neq) = &**op {
                if let Self::Equals(inner) = &**neq {
                    for (j, term) in inner.iter().enumerate() {
                        let term_s = term.to_string();
                        if let Some(eq_ops) = not_terms.get_mut(&term_s) {
                            eq_ops.push((i, j));
                        }
                        else {
                            not_terms.insert(term_s, vec![(i, j)]);
                        }
                    }
                }
            }
        }

        trace!("and_eq_contradiction: not_terms = {:?}", &not_terms);

        // map a (is-eq ..) operation in combined_terms to the set of (not (is-eq ..)) operations in combined_terms which
        // contain one of this operation's inner terms.
        let mut negated : HashMap<usize, HashSet<usize>> = HashMap::new();

        // find contradictions in the form of (and (is-eq a b ..) (not (is-eq a b ..)))
        for (i, eq) in combined_terms.iter().enumerate() {
            let Self::Equals(inner) = &**eq else {
                continue;
            };

            for term in inner.iter() {
                let term_s = term.to_string();

                // is this term explicitly _not_ equal to other terms?
                let Some(neq_idx) = not_terms.get(&term_s) else {
                    continue;
                };

                for (op_idx, term_idx) in neq_idx.iter() {
                    let Self::Not(neq) = &*combined_terms[*op_idx] else {
                        continue;
                    };
                    let Self::Equals(not_inner) = &**neq else {
                        continue;
                    };
                    let Some(not_term) = not_inner.get(*term_idx) else {
                        continue;
                    };
                    if term_s == not_term.to_string() {
                        if let Some(neg_set) = negated.get_mut(&i) {
                            if neg_set.contains(&op_idx) {
                                // at least two terms in this (is-eq ..) list have appeared in the
                                // same (not (is-eq ..)) list (i.e. we have 
                                // (and (is-eq a b ...) (not (is-eq a b ..)) ..)), so this is a
                                // contradiction.
                                trace!("and_eq_contradiction: contradiction detected");
                                trace!("and_eq_contradiction: {i}: {}", combined_terms[i]);
                                for neg_op_idx in neg_set.clone().iter() {
                                    trace!("and_eq_contradiction: {neg_op_idx}: {}", combined_terms[*neg_op_idx]);
                                }

                                return Ok(vec![Box::new(Self::Constant(Value::Bool(false)))]);
                            }
                            neg_set.insert(*op_idx);
                        }
                        else {
                            let mut neg_set = HashSet::new();
                            neg_set.insert(*op_idx);
                            negated.insert(i, neg_set);
                        }
                    }
                }
            }
        }
        Ok(combined_terms)
    }
   
    /// Eliminate redundant (not (is-eq a k2)) in (and (is-eq a k1) (not (is-eq a k2))) where
    /// k1 != k2.  These conjunctions can get generated by an evaluation of (filter ..), and can
    /// often be simplified.
    ///
    /// NOTE: all terms in combined_terms must have been simplified
    fn and_equals_redundant(combined_terms: Vec<Box<SymOp>>) -> Result<Vec<Box<SymOp>>, Error> {
        // eliminate redundant terms.
        // If we have (and (is-eq x k1) (not (is-eq x k2))) and k1 != k2, then reduce to
        // (is-eq x k1) if k1 != k2
        //
        // (is-eq x k1)        (not (is-eq x k2))       (and ..)      (is-eq x k1)
        //   T (x == k1)           T (x != k2)             T               T
        //   F (x != k1)           T (x != k2)             F               F
        //   T (x == k1)           F (x == k2)             F               F (iff k1 != k2)
        //   F (x != k1)           F (x == k2)             F               F

        trace!("and_eqs_redundant: combined_terms = {:?}", &combined_terms);

        // expand combined terms.  If we have (is-eq (a b c k1)), where k1 constant, split into
        // (and (is-eq a k1) (is-eq b k1) (is-eq c k1))
        let mut expanded_eq = vec![];
        let mut expanded_neq = vec![];
        let mut untouched = vec![];

        let mut term_eqs : HashMap<String, Vec<usize>> = HashMap::new();
        let mut term_neqs : HashMap<String, Vec<usize>> = HashMap::new();
        for (op_i, op) in combined_terms.clone().into_iter().enumerate() {
            if let Self::Equals(inner) = &*op {
                // find all constants (even if there's more than one).
                let mut constants = HashSet::new();
                let mut last_constant = None;
                for inner_op in inner.iter() {
                    if let SymOp::Constant(..) = **inner_op {
                        last_constant = Some(inner_op.clone());
                        constants.insert(inner_op.clone());
                    }
                }
                if constants.len() == 0 {
                    // skip this
                    untouched.push(op);
                    continue;
                }

                if constants.len() > 1 {
                    // contradiction -- (is-eq k1 k2 ...) where each ki is unique is never true
                    return Ok(vec![Box::new(SymOp::Constant(Value::Bool(false)))]);
                }

                let Some(inner_const) = last_constant else {
                    return Err(Error::Bug("unreachable -- last_constant is None".into()));
                };

                for inner_op in inner.iter() {
                    if *inner_op != inner_const {
                        let l = expanded_eq.len();
                        expanded_eq.push((inner_op.clone(), inner_const.clone(), op_i));

                        let term_s = inner_op.to_string();
                        if let Some(pos) = term_eqs.get_mut(&term_s) {
                            pos.push(l);
                        }
                        else {
                            term_eqs.insert(inner_op.to_string(), vec![l]);
                        }
                    }
                }
            }
            else if let Self::Not(eq) = &*op {
                if let Self::Equals(inner) = &**eq {
                    // find all constants (even if there's more than one).
                    let mut constants = HashSet::new();
                    let mut last_constant = None;
                    for inner_op in inner.iter() {
                        if let SymOp::Constant(..) = **inner_op {
                            last_constant = Some(inner_op);
                            constants.insert(inner_op);
                        }
                    }
                    if constants.len() == 0 {
                        // skip this
                        untouched.push(op);
                        continue;
                    }

                    if constants.len() > 1 {
                        // (not (is-eq k1 k2)) when k1 != k2 is a tautology, so skip this op
                        untouched.push(op);
                        continue;
                    }

                    let Some(inner_const) = last_constant else {
                        return Err(Error::Bug("unreachable -- last_constant is None".into()));
                    };

                    for inner_op in inner.iter() {
                        if inner_op != inner_const {
                            let l = expanded_neq.len();
                            expanded_neq.push((inner_op.clone(), inner_const.clone(), op_i));
                            
                            let term_s = inner_op.to_string();
                            if let Some(pos) = term_neqs.get_mut(&term_s) {
                                pos.push(l);
                            }
                            else {
                                term_neqs.insert(inner_op.to_string(), vec![l]);
                            }
                        }
                    }
                }
                else {
                    untouched.push(op);
                }
            }
            else {
                untouched.push(op);
            }
        }
        trace!("and_eqs_redundant: expanded_eq = {:?}", &expanded_eq);
        trace!("and_eqs_redundant: expanded_neq = {:?}", &expanded_neq);

        trace!("and_eqs_redundant: term_eqs = {:?}", &term_eqs);
        trace!("and_eqs_redundant: term_neqs = {:?}", &term_neqs);

        // for each (is-eq x k1), identify and drop each corresponding (not (is-eq x k2)) 
        // if k1 != k2.  If k1 == k2, then there is a contradiction and this should just return
        // False.  While we're at it, if we found (is-eq x k1) and (is-eq x k2) where k1 != k2,
        // then also return False.
        let mut redundant_neqs = HashSet::new();
        for (term_s, eqs) in term_eqs.into_iter() {
            // consolidate constants
            let mut constants = HashSet::new();
            let mut last_constant = None;
            for eq in eqs.iter() {
                let constant = expanded_eq[*eq].1.clone();
                last_constant = Some(constant.clone());
                constants.insert(constant);
            }
            if constants.len() > 1 {
                // this term is equal to two or more different constants
                return Ok(vec![Box::new(Self::Constant(Value::Bool(false)))]);
            }
            if constants.len() == 0 {
                return Err(Error::Bug("unreachable: no constants".into()));
            }
            let Some(k) = last_constant.take() else {
                return Err(Error::Bug("unreachable: no last-constant".into()));
            };
            let Some(neqs) = term_neqs.get(&term_s) else {
                continue;
            };

            for neq in neqs.iter() {
                let neq_const = expanded_neq[*neq].1.clone();
                if neq_const == k {
                    // have (is-eq x k1) and (not (is-eq x k1))
                    return Ok(vec![Box::new(Self::Constant(Value::Bool(false)))]);
                }

                // this not-equals is redundant
                trace!("and_eqs_redundant: redundant term {neq} in {}", &combined_terms[expanded_neq[*neq].2]);
                redundant_neqs.insert(*neq);
            }
        }

        // consolidate eqs
        let mut consolidated_eq : HashMap<usize, Vec<Box<SymOp>>> = HashMap::new();
        for (eq_op, eq_const, op_i) in expanded_eq.into_iter() {
            if let Some(ops) = consolidated_eq.get_mut(&op_i) {
                ops.push(eq_op);
            }
            else {
                let ops = vec![eq_op, eq_const];
                consolidated_eq.insert(op_i, ops);
            }
        }

        // consolidate neqs
        let mut consolidated_neq : HashMap<usize, Vec<Box<SymOp>>> = HashMap::new();
        for (neq_i, (neq_op, neq_const, op_i)) in expanded_neq.into_iter().enumerate() {
            if let Some(ops) = consolidated_neq.get_mut(&op_i) {
                ops.push(neq_op);
            }
            else if !redundant_neqs.contains(&neq_i) {
                let ops = vec![neq_op, neq_const];
                consolidated_neq.insert(op_i, ops);
            }
        }

        // reconstitute
        for (_, eq_ops) in consolidated_eq.into_iter() {
            untouched.push(Box::new(Self::Equals(eq_ops)));
        }
        for (_, neq_ops) in consolidated_neq.into_iter() {
            untouched.push(Box::new(Self::Not(Box::new(Self::Equals(neq_ops)))));
        }

        Ok(untouched)
    }

    /// Find the minimum value in a list of values of the same type (Int or UInt).
    fn find_min_value(values: &[Value]) -> Option<&Value> {
        let first = values.get(0)?;
        let rest = values.get(1..)?;
        let mut minimum = first;
        for v in rest.iter() {
            match (minimum, v) {
                (Value::UInt(x), Value::UInt(y)) => {
                    if y < x {
                        minimum = v;
                    }
                },
                (Value::Int(x), Value::Int(y)) => {
                    if y < x {
                        minimum = v;
                    }
                },
                (_, _) => {
                    panic!("Incomparable value types {minimum} and {v}");
                }
            }
        }
        Some(minimum)
    }

    /// Find the maximum value in a list of values of the same type (Int or UInt).
    fn find_max_value(values: &[Value]) -> Option<&Value> {
        let first = values.get(0)?;
        let rest = values.get(1..)?;
        let mut maximum = first;
        for v in rest.iter() {
            match (maximum, v) {
                (Value::UInt(x), Value::UInt(y)) => {
                    if y > x {
                        maximum = v;
                    }
                },
                (Value::Int(x), Value::Int(y)) => {
                    if y > x {
                        maximum = v;
                    }
                },
                (_, _) => {
                    panic!("Incomparable value types {maximum} and {v}");
                }
            }
        }
        Some(maximum)
    }

    /// Compare two Values and report if one is less than or equal to the other
    fn value_leq(v1: &Value, v2: &Value) -> Option<bool> {
        match (v1, v2) {
            (Value::UInt(x), Value::UInt(y)) => {
                Some(x <= y)
            }
            (Value::Int(x), Value::Int(y)) => {
                Some(x <= y)
            }
            (_, _) => {
                None
            }
        }
    }
    
    /// Compare two Values and report if one is less than the other
    fn value_lesser(v1: &Value, v2: &Value) -> Option<bool> {
        Self::value_leq(v1, v2).map(|b| b && v1 != v2)
    }
    
    /// Compare two Values and report if one is greater than or equal to the other
    fn value_geq(v1: &Value, v2: &Value) -> Option<bool> {
        match (v1, v2) {
            (Value::UInt(x), Value::UInt(y)) => {
                Some(x >= y)
            }
            (Value::Int(x), Value::Int(y)) => {
                Some(x >= y)
            }
            (_, _) => {
                None
            }
        }
    }

    /// Compare two Values and report if one is greater than the other
    fn value_greater(v1: &Value, v2: &Value) -> Option<bool> {
        Self::value_geq(v1, v2).map(|b| b && v1 != v2)
    }
    
    /// Compare two Values and report if one is greater than the other, plus 1 (i.e. v1 > v2 + 1)
    fn value_greater_plus_1(v1: &Value, v2: &Value) -> Option<bool> {
        match (v1, v2) {
            (Value::UInt(x), Value::UInt(y)) => {
                Some(x > &y.checked_add(1)?)
            }
            (Value::Int(x), Value::Int(y)) => {
                Some(x > &y.checked_add(1)?)
            }
            (_, _) => {
                None
            }
        }
    }

    /// Compute Value - 1, if possible
    fn value_minus_1(v: &Value) -> Option<Value> {
        match v {
            Value::UInt(x) => x.checked_sub(1).map(|v| Value::UInt(v)),
            Value::Int(x) => x.checked_sub(1).map(|v| Value::Int(v)),
            _ => None
        }
    }
    
    /// Compute Value + 1, if possible
    fn value_plus_1(v: &Value) -> Option<Value> {
        match v {
            Value::UInt(x) => x.checked_add(1).map(|v| Value::UInt(v)),
            Value::Int(x) => x.checked_add(1).map(|v| Value::Int(v)),
            _ => None
        }
    }

    /// Reduce inequalities between symbols and constants
    fn and_inequality_constant_simplify(ops: Vec<Box<SymOp>>) -> Result<SymOp, Error> {
        #[derive(Debug, Copy, Clone)]
        enum Cmp {
            Lt,
            Leq,
            Eqs,
            Neq,
            Geq,
            Gt
        }

        #[derive(Debug)]
        struct ValueCmp {
            op: SymOp,
            greater: Option<Value>,
            geq: Option<Value>,
            eq: Option<Value>,
            neq: HashSet<Value>,
            leq: Option<Value>,
            lesser: Option<Value>,
            possible: bool
        }

        impl ValueCmp {
            fn new(op: SymOp) -> Self {
                Self {
                    op: op,
                    greater: None,
                    geq: None,
                    eq: None,
                    neq: HashSet::new(),
                    leq: None,
                    lesser: None,
                    possible: true
                }
            }

            fn set_greater(&mut self, val: Value) {
                if let Some(prev) = self.greater.take() {
                    if SymOp::value_greater(&val, &prev).expect("unreachable -- value_greater failed") {
                        self.greater = Some(val)
                    }
                    else {
                        self.greater = Some(prev)
                    }
                }
                else {
                    self.greater = Some(val)
                }
            }
            
            fn set_geq(&mut self, val: Value) {
                if let Some(prev) = self.geq.take() {
                    if SymOp::value_geq(&val, &prev).expect("unreachable -- value_geq failed") {
                        self.geq = Some(val)
                    }
                    else {
                        self.geq = Some(prev)
                    }
                }
                else {
                    self.geq = Some(val)
                }
            }
            
            fn set_lesser(&mut self, val: Value) {
                if let Some(prev) = self.lesser.take() {
                    if SymOp::value_lesser(&val, &prev).expect("unreachable -- value_lesser failed") {
                        self.lesser = Some(val)
                    }
                    else {
                        self.lesser = Some(prev)
                    }
                }
                else {
                    self.lesser = Some(val)
                }
            }
            
            fn set_leq(&mut self, val: Value) {
                if let Some(prev) = self.leq.take() {
                    if SymOp::value_leq(&val, &prev).expect("unreachable -- value_leq failed") {
                        self.leq = Some(val)
                    }
                    else {
                        self.leq = Some(prev)
                    }
                }
                else {
                    self.leq = Some(val)
                }
            }
            
            fn set_eq(&mut self, val: Value) {
                if let Some(prev) = self.eq.as_ref() {
                    self.possible = self.possible && prev == &val;
                }
                else {
                    self.eq = Some(val)
                }
            }

            fn set_neq(&mut self, val: Value) {
                self.neq.insert(val);
            }

            fn neq_rewrite(&mut self) {
                loop {
                    let mut changed = false;
                    let mut neq_remove = HashSet::new();
                    let mut neqs = std::mem::replace(&mut self.neq, HashSet::new());
                    for neq in neqs.iter() {
                        // (and (x <= k) (not (is-eq x k))) implies x < k
                        if let Some(k) = self.leq.as_ref() && k == neq {
                            trace!("(and (x <= k) (not (is-eq x k))) implies x < k");
                            self.set_lesser(k.clone());
                            self.leq = None;
                            changed = true;
                        }
                        // (and (x >= k) (not (is-eq x k))) implies x > k
                        if let Some(k) = self.geq.as_ref() && k == neq {
                            trace!("(and (x >= k) (not (is-eq x k))) implies x > k");
                            self.set_greater(k.clone());
                            self.geq = None;
                            changed = true;
                        }
                        // (and (x < k) (not (is-eq x (- k 1)))) implies x < k - 1
                        if let Some(k1) = self.lesser.as_ref() && let Some(k2) = SymOp::value_minus_1(k1) && k2 == *neq {
                            trace!("(and (x < k) (not (is-eq x (- k 1)))) implies x < k - 1");
                            self.set_lesser(k2);
                            neq_remove.insert(neq.clone());
                            changed = true;
                        }
                        // (and (x > k) (not (is-eq x (+ k 1))) implies x > k + 1
                        if let Some(k1) = self.greater.as_ref() && let Some(k2) = SymOp::value_plus_1(k1) && k2 == *neq {
                            trace!("(and (x > k) (not (is-eq x (+ k 1))) implies x > k + 1");
                            self.set_greater(k2);
                            neq_remove.insert(neq.clone());
                            changed = true;
                        }
                        // (and (x < k) (not (is-eq x k))) reduces to just (x < k)
                        if let Some(k1) = self.lesser.as_ref() && k1 == neq {
                            trace!("(and (x < k) (not (is-eq x k))) implies just x < k");
                            neq_remove.insert(neq.clone());
                            changed = true;
                        }
                        // (and (x > k) (not (is-eq x k))) reduces to just (x > k)
                        if let Some(k1) = self.greater.as_ref() && k1 == neq {
                            trace!("(and (x > k) (not (is-eq x k))) implies just x > k");
                            neq_remove.insert(neq.clone());
                            changed = true;
                        }
                        // (and (x < k1) (not (is-eq x k2))) and k2 > k1 implies just x < k1
                        if let Some(k1) = self.lesser.as_ref() && SymOp::value_greater(neq, k1) == Some(true) {
                            trace!("(and (x < k1) (not (is-eq x k2))) and k2 > k1 implies just x < k1");
                            neq_remove.insert(neq.clone());
                            changed = true;
                        }
                        // (and (x <= k1) (not (is-eq x k2))) and k2 > k1 implies just x <= k1
                        if let Some(k1) = self.leq.as_ref() && SymOp::value_greater(neq, k1) == Some(true) {
                            trace!("(and (x <= k1) (not (is-eq x k2))) and k2 > k1 implies just x <= k1");
                            neq_remove.insert(neq.clone());
                            changed = true;
                        }
                        // (and (x > k1) (not (is-eq x k2))) and k2 < k1 implies just x < k1
                        if let Some(k1) = self.greater.as_ref() && SymOp::value_lesser(neq, k1) == Some(true) {
                            trace!("(and (x > k1) (not (is-eq x k2))) and k2 < k1 implies just x > k1");
                            neq_remove.insert(neq.clone());
                            changed = true;
                        }
                        // (and (x >= k1) (not (is-eq x k2))) and k2 < k1 implies just x <= k1
                        if let Some(k1) = self.geq.as_ref() && SymOp::value_lesser(neq, k1) == Some(true) {
                            trace!("(and (x >= k1) (not (is-eq x k2))) and k2 < k1 implies just x >= k1");
                            neq_remove.insert(neq.clone());
                            changed = true;
                        }
                    }
                    for neq in neq_remove.into_iter() {
                        neqs.remove(&neq);
                    }
                    let _ = std::mem::replace(&mut self.neq, neqs);

                    if !changed {
                        break;
                    }
                }
            }
            
            fn eq_rewrite(&mut self) {
                // (and (<= x k1) (is-eq x k2) (>= k1 k2)) implies (is-eq x k2)
                if let Some(k1) = self.leq.as_ref() && let Some(k2) = self.eq.as_ref() && SymOp::value_geq(k1, k2).expect("unreachable -- eq_rewrite value_geq failed") {
                    trace!("(and (<= x k1) (is-eq x k2) (<= k1 k2)) implies (is-eq x k2)");
                    self.leq = None;
                }
                // (and (>= x k1) (is-eq x k2) (<= k1 k2)) implies (is-eq x k2)
                if let Some(k1) = self.geq.as_ref() && let Some(k2) = self.eq.as_ref() && SymOp::value_leq(k1, k2).expect("unreachable -- eq_rewrite value_leq failed") {
                    trace!("(and (<= x k1) (is-eq x k2) (>= k1 k2)) implies (is-eq x k2)");
                    self.geq = None;
                }
                // (and (< x k1) (is-eq x k2) (k1 > k2)) implies (is-eq x k2)
                if let Some(k1) = self.lesser.as_ref() && let Some(k2) = self.eq.as_ref() && SymOp::value_greater(k1, k2).expect("unreachable -- eq_rewrite value_greater failed") {
                    trace!("(and (< x k1) (is-eq x k2) (k1 > k2)) implies (is-eq x k2)");
                    self.lesser = None;
                }
                // (and (> x k1) (is-eq x k2) (k1 < k2)) implies (is-eq x k2)
                if let Some(k1) = self.greater.as_ref() && let Some(k2) = self.eq.as_ref() && SymOp::value_lesser(k1, k2).expect("unreachable -- eq_rewrite value_lesser failed") {
                    trace!("(and (> x k1) (is-eq x k2) (k1 < k2)) implies (is-eq x k2)");
                    self.greater = None;
                }
            }

            fn ineq_rewrite(&mut self) {
                // (and (< x k1) (<= x k2) (k1 < k2)) implies (< x k1)
                if let Some(k1) = self.lesser.as_ref() && let Some(k2) = self.leq.as_ref() && SymOp::value_lesser(k1, k2).expect("unreachable -- ineq_rewrite value_lesser failed") {
                    trace!("(and (< x k1) (<= x k2) (k1 < k2)) implies (< x k1)");
                    self.leq = None;
                }
                // (and (<= x k1) (< x k2) (k1 < k2)) implies (<= x k1)
                if let Some(k1) = self.leq.as_ref() && let Some(k2) = self.lesser.as_ref() && SymOp::value_lesser(k1, k2).expect("unreachable -- ineq_rewrite value_lesser(2) failed") {
                    trace!("(and (<= x k1) (< x k2) (k1 < k2)) implies (<= x k1)");
                    self.lesser = None;
                }
                // (and (> x k1) (>= x k2) (k1 > k2)) implies (> x k1)
                if let Some(k1) = self.greater.as_ref() && let Some(k2) = self.geq.as_ref() && SymOp::value_greater(k1, k2).expect("unreachable -- ineq_rewrite value-greater failed") {
                    trace!("(and (> x k1) (>= x k2) (k1 > k2)) implies (> x k1)");
                    self.geq = None;
                }
                // (and (>= x k1) (> x k2) (k1 > k2)) implies (>= x k1)
                if let Some(k1) = self.geq.as_ref() && let Some(k2) = self.greater.as_ref() && SymOp::value_greater(k1, k2).expect("unreachable -- ineq_rewrite value-greater(2) failed") {
                    trace!("(and (>= x k1) (> x k2) (k1 > k2)) implies (>= x k1)");
                    self.greater = None;
                }
            }

            fn check_possible(&mut self) {
                // uint: (x < k) implies k > u0
                if let Some(k) = self.lesser.as_ref() && let Value::UInt(v) = k {
                    trace!("uint: (x < k) implies k > u0");
                    self.possible = self.possible && *v > u128::MIN;
                }
                // uint: (x > k) implies k < u128::MAX
                if let Some(k) = self.greater.as_ref() && let Value::UInt(v) = k {
                    trace!("uint: (x > k) implies k < u128::MAX");
                    self.possible = self.possible && *v < u128::MAX;
                }
                // int: (x < k) implies k > i128::MIN
                if let Some(k) = self.lesser.as_ref() && let Value::Int(v) = k {
                    trace!("int: (x < k) implies k > i128::MIN");
                    self.possible = self.possible && *v > i128::MIN;
                }
                // int: (x > k) implies k < i128::MAX
                if let Some(k) = self.greater.as_ref() && let Value::Int(v) = k {
                    trace!("int: (x > k) implies k < i128::MAX");
                    self.possible = self.possible && *v < i128::MAX;
                }
                // (and (< x k1) (> x k2)) implies k1 > k2 + 1
                if let Some(k1) = self.lesser.as_ref() && let Some(k2) = self.greater.as_ref() {
                    trace!("(and (< x k1) (> x k2)) implies k1 > k2 + 1");
                    self.possible = self.possible && SymOp::value_greater_plus_1(k1, k2).expect("unreachable -- check_possible value_greater_plus_1 failed");
                }
                // (and (x < k1) (>= x k2) implies k1 > k2
                if let Some(k1) = self.lesser.as_ref() && let Some(k2) = self.geq.as_ref() {
                    trace!("(and (x < k1) (>= x k2) implies k1 > k2");
                    self.possible = self.possible && SymOp::value_greater(k1, k2).expect("unreachable -- check_possible value_greater failed");
                }
                // (and (x <= k1) (> x k2) implies k1 > k2
                if let Some(k1) = self.leq.as_ref() && let Some(k2) = self.greater.as_ref() {
                    trace!("(and (x <= k1) (> x k2) implies k1 > k2");
                    self.possible = self.possible && SymOp::value_greater(k1, k2).expect("unreachable -- check_possible value_greater(2) failed");
                }
                // (and (x <= k1) (>= x k2) implies k1 >= k2
                if let Some(k1) = self.leq.as_ref() && let Some(k2) = self.geq.as_ref() {
                    trace!("(and (x <= k1) (>= x k2) implies k1 >= k2");
                    self.possible = self.possible && SymOp::value_geq(k1, k2).expect("unreachable -- check_possible value_geq failed");
                }
                // (and (< x k1) (is-eq x k2)) implies k1 > k2
                if let Some(k1) = self.lesser.as_ref() && let Some(k2) = self.eq.as_ref() {
                    trace!("(and (< x k1) (is-eq x k2)) implies k1 > k2");
                    self.possible = self.possible && SymOp::value_greater(k1, k2).expect("unreachable -- check_possible value_greater(3) failed");
                }
                // (and (<= x k1) (is-eq x k2)) implies k1 >= k2
                if let Some(k1) = self.leq.as_ref() && let Some(k2) = self.eq.as_ref() {
                    trace!("(and (<= x k1) (is-eq x k2)) implies k1 >= k2");
                    self.possible = self.possible && SymOp::value_geq(k1, k2).expect("unreachable -- check_possible value_geq(2) failed");
                }
                // (and (> x k1) (is-eq x k2)) implies k1 < k2
                if let Some(k1) = self.greater.as_ref() && let Some(k2) = self.eq.as_ref() {
                    trace!("(and (> x k1) (is-eq x k2)) implies k1 < k2");
                    self.possible = self.possible && SymOp::value_lesser(k1, k2).expect("unreachable -- check_possible value_lesser failed");
                }
                // (and (>= x k1) (is-eq x k2)) implies k1 <= k2
                if let Some(k1) = self.geq.as_ref() && let Some(k2) = self.eq.as_ref() {
                    trace!("(and (>= x k1) (is-eq x k2)) implies k1 <= k2");
                    self.possible = self.possible && SymOp::value_leq(k1, k2).expect("unreachable -- check_possible value_leq failed");
                }
                // (and (is-eq x k) (not (is-eq x k))) is impossible
                if let Some(k) = self.eq.as_ref() && self.neq.contains(k) {
                    trace!("(and (is-eq x k) (not (is-eq x k))) is impossible");
                    self.possible = false;
                }
                // (and (is-eq x k1) (x < k2)) implies k1 < k2
                if let Some(k1) = self.eq.as_ref() && let Some(k2) = self.lesser.as_ref() {
                    trace!("(and (is-eq x k1) (x < k2)) implies k1 < k2");
                    self.possible = self.possible && SymOp::value_lesser(k1, k2).expect("unreachable -- check_possible value_lesser(2) failed");
                }
                // (and (is-eq x k1) (x > k2)) implies k1 > k2
                if let Some(k1) = self.eq.as_ref() && let Some(k2) = self.greater.as_ref() {
                    trace!("(and (is-eq x k1) (x > k2)) implies k1 > k2");
                    self.possible = self.possible && SymOp::value_greater(k1, k2).expect("unreachable -- check_possible value_greater(4) failed");
                }
                // (and (is-eq x k1) (<= x k2)) implies k1 <= k2
                if let Some(k1) = self.eq.as_ref() && let Some(k2) = self.leq.as_ref() {
                    trace!("(and (is-eq x k1) (<= x k2)) implies k1 <= k2");
                    self.possible = self.possible && SymOp::value_leq(k1, k2).expect("unreachable -- check_possibe value_leq(2) failed");
                }
                // (and (is-eq x k1) (>= x k2)) implies k1 >= k2
                if let Some(k1) = self.eq.as_ref() && let Some(k2) = self.geq.as_ref() {
                    trace!("(and (is-eq x k1) (>= x k2)) implies k1 >= k2");
                    self.possible = self.possible && SymOp::value_geq(k1, k2).expect("unreachable -- check_possible value_geq(3) failed");
                }
                // (and (is-eq x k1) (> x k1)) is false
                if let Some(k1) = self.eq.as_ref() && let Some(k2) = self.greater.as_ref() && k1 == k2 {
                    trace!("(and (is-eq x k1) (> x k1)) is false");
                    self.possible = false;
                }
                // (and (is-eq x k1) (< x k1)) is false
                if let Some(k1) = self.eq.as_ref() && let Some(k2) = self.lesser.as_ref() && k1 == k2 {
                    trace!("(and (is-eq x k1) (< x k1)) is false");
                    self.possible = false;
                }
                // (and (> x k1) (< x k1)) is false
                if let Some(k1) = self.greater.as_ref() && let Some(k2) = self.lesser.as_ref() && k1 == k2 {
                    trace!("(and (> x k1) (< x k1)) is false");
                    self.possible = false;
                }
            }

            fn simplify(&mut self) {
                self.neq_rewrite();
                self.eq_rewrite();
                self.ineq_rewrite();
                self.check_possible();
            }

            fn add_cmp(&mut self, op: Box<SymOp>, cmp: Cmp) {
                if let SymOp::Constant(v) = *op {
                    match cmp {
                        Cmp::Lt => self.set_lesser(v),
                        Cmp::Leq => self.set_leq(v),
                        Cmp::Eqs => self.set_eq(v),
                        Cmp::Neq => self.set_neq(v),
                        Cmp::Geq => self.set_geq(v),
                        Cmp::Gt => self.set_greater(v),
                    }
                }
            }

            fn into_symops(mut self) -> Vec<Box<SymOp>> {
                let mut ret = vec![];
                if let Some(k) = self.lesser.take() {
                    ret.push(Box::new(SymOp::Less(Box::new(self.op.clone()), Box::new(SymOp::Constant(k)))));
                }
                if let Some(k) = self.leq.take() {
                    ret.push(Box::new(SymOp::Leq(Box::new(self.op.clone()), Box::new(SymOp::Constant(k)))));
                }
                if let Some(k) = self.geq.take() {
                    ret.push(Box::new(SymOp::Geq(Box::new(self.op.clone()), Box::new(SymOp::Constant(k)))));
                }
                if let Some(k) = self.greater.take() {
                    ret.push(Box::new(SymOp::Greater(Box::new(self.op.clone()), Box::new(SymOp::Constant(k)))));
                }
                if let Some(k) = self.eq.take() {
                    ret.push(Box::new(SymOp::Equals(vec![Box::new(self.op.clone()), Box::new(SymOp::Constant(k))])));
                }
                for neq in self.neq.into_iter() {
                    ret.push(Box::new(SymOp::Not(Box::new(SymOp::Equals(vec![Box::new(self.op.clone()), Box::new(SymOp::Constant(neq))])))));
                }
                ret
            }
        }
        
        let mut consolidated_ops : Vec<Box<SymOp>> = vec![];
        let mut cmps : HashMap<String, ValueCmp> = HashMap::new();

        let mut add_cmp = |op1: Box<SymOp>, op2: Box<SymOp>, cmp: Cmp| {
            let op1_s = op1.to_string();
            if let Some(set) = cmps.get_mut(&op1_s) {
                set.add_cmp(op2, cmp);
            }
            else {
                let mut set = ValueCmp::new((*op1).clone());
                set.add_cmp(op2, cmp);
                cmps.insert(op1_s, set);
            }
        };

        for op in ops.into_iter() {
            match *op {
                Self::Greater(op1, op2) => {
                    if op2.is_constant() {
                        add_cmp(op1, op2, Cmp::Gt);
                    }
                    else if op1.is_constant() {
                        add_cmp(op2, op1, Cmp::Lt);
                    }
                    else {
                        consolidated_ops.push(Box::new(Self::Greater(op1, op2)));
                        continue;
                    }
                }
                Self::Geq(op1, op2) => {
                    if op2.is_constant() {
                        add_cmp(op1, op2, Cmp::Geq);
                    }
                    else if op1.is_constant() {
                        add_cmp(op2, op1, Cmp::Leq);
                    }
                    else {
                        consolidated_ops.push(Box::new(Self::Geq(op1, op2)));
                        continue;
                    }
                }
                Self::Leq(op1, op2) => {
                    if op2.is_constant() {
                        add_cmp(op1, op2, Cmp::Leq);
                    }
                    else if op1.is_constant() {
                        add_cmp(op2, op1, Cmp::Geq);
                    }
                    else {
                        consolidated_ops.push(Box::new(Self::Leq(op1, op2)));
                        continue;
                    }
                }
                Self::Less(op1, op2) => {
                    if op2.is_constant() {
                        add_cmp(op1, op2, Cmp::Lt);
                    }
                    else if op1.is_constant() {
                        add_cmp(op2, op1, Cmp::Gt);
                    }
                    else {
                        consolidated_ops.push(Box::new(Self::Less(op1, op2)));
                        continue;
                    }
                }
                Self::Equals(ops) => {
                    // find the one constant
                    // if this is reduced, then there will be at most one constant in ops
                    let Some(const_op_i) = ops.iter().position(|op| op.is_constant()) else {
                        consolidated_ops.push(Box::new(Self::Equals(ops)));
                        continue;
                    };
                    for (i, op) in ops.iter().enumerate() {
                        if i == const_op_i {
                            continue;
                        }

                        add_cmp(op.clone(), ops[const_op_i].clone(), Cmp::Eqs);
                    }
                }
                Self::Not(inner_eq) => {
                    if let Self::Equals(mut inner_ops) = *inner_eq {
                        if inner_ops.len() == 2 {
                            // (ops.len() should already be 2, since this is simplified)
                            // if this is reduced, then there will be at most one constant in ops
                            if inner_ops.iter().position(|op| op.is_constant()).is_none() {
                                consolidated_ops.push(Box::new(Self::Not(Box::new(Self::Equals(inner_ops)))));
                                continue;
                            };
                            let op2 = inner_ops.pop().expect("unreachable -- inner_ops.len() == 2 but pop failed");
                            let op1 = inner_ops.pop().expect("unreachable -- inner_ops.len() == 1 but pop failed");
                            if op1.is_constant() && op2.is_constant() {
                                return Err(Error::Bug(format!("(not (is-eq {op1} {op2})) is not simplified")));
                            }
                            else if op2.is_constant() {
                                add_cmp(op1, op2, Cmp::Neq);
                            }
                            else {
                                add_cmp(op2, op1, Cmp::Neq);
                            }
                        }
                        else {
                            consolidated_ops.push(Box::new(Self::Not(Box::new(Self::Equals(inner_ops)))));
                        }
                    }
                    else {
                        consolidated_ops.push(Box::new(Self::Not(inner_eq)));
                    }
                }
                x => {
                    consolidated_ops.push(Box::new(x));
                }
            }
        }

        for (_op_s, set) in cmps.iter_mut() {
            set.simplify();
            trace!("and_inequality_constant_simplify: op = {_op_s}, set = {set:?}");
            if !set.possible {
                return Ok(SymOp::False());
            }
        }

        for (_op_s, set) in cmps.into_iter() {
            let ops = set.into_symops();
            consolidated_ops.extend(ops.into_iter());
        }
        Ok(SymOp::And(consolidated_ops))
    }


    /// Identify symbolic contradictions for inequality
    fn and_inequality_symbolic_contradictions(ops: Vec<Box<SymOp>>) -> Result<Vec<Box<SymOp>>, Error> {
        // try to put all inequality symbols in partial order.
        // If that cannot be done due to a cycle, then this is a contradiction
        let mut order : HashMap<String, HashSet<SymOp>> = HashMap::new();
        for op in ops.iter() {
            match &**op {
                Self::Less(op1, op2) => {
                    let op1_s = op1.to_string();
                    if let Some(successors) = order.get_mut(&op1_s) {
                        successors.insert((**op2).clone());
                    }
                    else {
                        let mut successors = HashSet::new();
                        successors.insert((**op2).clone());
                        order.insert(op1_s, successors);
                    };
                }
                Self::Greater(op1, op2) => {
                    let op2_s = op2.to_string();
                    if let Some(successors) = order.get_mut(&op2_s) {
                        successors.insert((**op1).clone());
                    }
                    else {
                        let mut successors = HashSet::new();
                        successors.insert((**op1).clone());
                        order.insert(op2_s, successors);
                    };
                }
                _x => {
                    continue;
                }
            }
        }
        for (key, successors) in order.iter() {
            for s in successors.iter() {
                 if s.to_string() == *key {
                     trace!("Term {key} is succeeded by itself");
                     return Ok(vec![Box::new(SymOp::False())]);
                 }
            }
        }

        trace!("and_inequality_symbolic_contradictions: order = {order:?}");

        // contract -- convert order to the transitive closure, and in doing so, reduce this
        // and-inequality to False if any term is found to be its own successor
        loop {
            let keys : Vec<_> = order.keys().into_iter().map(|k| k.to_string()).collect();
            let mut contractions = 0;
            for key in keys.into_iter() {
                let mut closure = HashSet::new();
                let Some(successors) = order.remove(&key) else {
                    continue;
                };

                let mut successor_queue : VecDeque<_> = successors.into_iter().collect();
                while let Some(front) = successor_queue.pop_front() {
                    let front_s = front.to_string();
                    if front_s == key {
                        trace!("Term {front_s} visited twice in closure computed for {key}");
                        return Ok(vec![Box::new(SymOp::False())]);
                    }
                    if closure.contains(&front) {
                        trace!("Term {front_s} visited twice in closure computed for {key}");
                        return Ok(vec![Box::new(SymOp::False())]);
                    }
                    closure.insert(front.clone());

                    let Some(front_successors) = order.remove(&front_s) else {
                        continue;
                    };
                    contractions += front_successors.len();
                    successor_queue.extend(front_successors.into_iter());
                }
                order.insert(key, closure);
                trace!("and_inequality_symbolic_contradictions: contractions = {contractions}, order = {order:?}");
            }
            if contractions == 0 {
                break;
            }
        }

        // no contradiction found
        Ok(ops)
    }


    /// Identify conflicting cons tests and eliminate contradictions
    /// i.e. is-some/is-none, is-ok/is-err
    fn and_cons_contradiction(ops: Vec<Box<SymOp>>) -> Result<SymOp, Error> {
        #[derive(Debug, Clone)]
        enum Cons {
            IsSome,
            IsNone,
            IsOkay,
            IsErr,
            IsUnwrapPanic,
            IsUnwrapErrPanic,
        }

        #[derive(Debug, Clone)]
        struct ValueCons {
            op: SymOp,
            is_okay: bool,
            is_err: bool,
            is_some: bool,
            is_none: bool,
            is_unwrap_panic: bool,
            is_unwrap_err_panic: bool,
            original: bool,
        }

        impl ValueCons {
            fn new(op: SymOp) -> Self {
                Self {
                    op: op,
                    is_okay: false,
                    is_err: false,
                    is_some: false,
                    is_none: false,
                    is_unwrap_panic: false,
                    is_unwrap_err_panic: false,
                    original: true,
                }
            }

            fn fold(&self, other: &ValueCons) -> Self {
                Self {
                    op: self.op.clone(),
                    is_okay: self.is_okay || other.is_okay,
                    is_err: self.is_err || other.is_err,
                    is_some: self.is_some || other.is_some,
                    is_none: self.is_none || other.is_none,
                    is_unwrap_panic: self.is_unwrap_panic || other.is_unwrap_panic,
                    is_unwrap_err_panic: self.is_unwrap_err_panic || other.is_unwrap_err_panic,
                    original: false
                }
            }

            fn check_possible(&self) -> bool {
                if self.is_okay && self.is_err {
                    trace!("cons {} is both (ok ..) and (err ..)", &self.op);
                    return false;
                }
                if self.is_some && self.is_none {
                    trace!("cons {} is both (some ..) and none", &self.op);
                    return false;
                }
                true
            }

            fn into_symop(self) -> Box<SymOp> {
                if self.is_okay {
                    return Box::new(SymOp::IsOkay(Box::new(self.op)));
                }
                if self.is_err {
                    return Box::new(SymOp::IsErr(Box::new(self.op)));
                }
                if self.is_some {
                    return Box::new(SymOp::IsSome(Box::new(self.op)));
                }
                if self.is_none {
                    return Box::new(SymOp::IsNone(Box::new(self.op)));
                }
                if self.is_unwrap_panic {
                    return Box::new(SymOp::UnwrapPanic(Box::new(self.op)));
                }
                if self.is_unwrap_err_panic {
                    return Box::new(SymOp::UnwrapErrPanic(Box::new(self.op)));
                }
                return Box::new(self.op)
            }

            fn add_cons(&mut self, cons: Cons, original: bool) {
                self.original = original;
                match cons {
                    Cons::IsOkay => {
                        self.is_okay = true;
                    }
                    Cons::IsErr => {
                        self.is_err = true;
                    }
                    Cons::IsSome => {
                        self.is_some = true;
                    }
                    Cons::IsNone => {
                        self.is_none = true;
                    }
                    Cons::IsUnwrapPanic => {
                        self.is_unwrap_panic = true;
                    }
                    Cons::IsUnwrapErrPanic => {
                        self.is_unwrap_err_panic = true;
                    }
                }
            }
        }
        
        let mut consolidated_ops : Vec<Box<SymOp>> = vec![];
        let mut cons : HashMap<String, Vec<ValueCons>> = HashMap::new();

        let mut add_cons = |op: Box<SymOp>, c: Cons, original: bool| {
            let op_s = op.to_string();
            let mut set = ValueCons::new((*op).clone());
            set.add_cons(c, original);
            if let Some(sets) = cons.get_mut(&op_s) {
                sets.push(set);
            }
            else {
                cons.insert(op_s, vec![set]);
            }
        };

        for op in ops.into_iter() {
            match *op {
                Self::IsOkay(op) => {
                    add_cons(op, Cons::IsOkay, true);
                }
                Self::IsErr(op) => {
                    add_cons(op, Cons::IsErr, true);
                }
                Self::IsSome(op) => {
                    if let SymOp::TupleGet(_name, inner) = &*op && inner.maybe_produces_optional_tuple() {
                        // (is-some (get X (optional Y))) implies (is-some Y)
                        add_cons(inner.clone(), Cons::IsSome, false);
                    }
                    add_cons(op, Cons::IsSome, true);
                }
                Self::IsNone(op) => {
                    if let SymOp::TupleGet(_name, inner) = &*op && inner.maybe_produces_optional_tuple() {
                        // (is-none (get X (optional Y))) implies (is-none Y)
                        add_cons(inner.clone(), Cons::IsNone, false);
                    }
                    add_cons(op, Cons::IsNone, true);
                }
                Self::UnwrapPanic(op) => {
                    add_cons(op.clone(), Cons::IsUnwrapPanic, true);

                    // we don't know which fact is true, but we know that
                    // it's either one or the other.  The type checker will have
                    // already ensured that the rest of the terms here are all
                    // exclusively results or optionals, so any type incompatibility
                    // is due to these synthetic conses.
                    add_cons(op.clone(), Cons::IsSome, false);
                    add_cons(op, Cons::IsOkay, false);
                }
                Self::UnwrapErrPanic(op) => {
                    add_cons(op.clone(), Cons::IsUnwrapErrPanic, true);
                    add_cons(op, Cons::IsErr, false);
                }
                x => {
                    consolidated_ops.push(Box::new(x));
                }
            }
        };

        for (_op_s, sets) in cons.iter() {
            let Some(first) = sets.first() else {
                continue;
            };
            let mut folded = (*first).clone();
            let Some(rest) = sets.get(1..) else {
                trace!("Consider cons {:?}", &first);
                if !first.check_possible() {
                    return Ok(SymOp::False());
                }
                continue;
            };
            for set in rest.iter() {
                trace!("Consider cons {:?}", &set);
                folded = folded.fold(set);
            }
            if !folded.check_possible() {
                return Ok(SymOp::False());
            }
        }

        for (_op_s, sets) in cons.into_iter() {
            for set in sets.into_iter() {
                if !set.original {
                    continue;
                }
                let op = set.into_symop();
                consolidated_ops.push(op);
            }
        }
        Ok(SymOp::And(consolidated_ops))
    }

    /// apply and-contradiction
    /// X && !X == False
    fn contradiction_and(ops: Vec<Box<SymOp>>) -> Result<SymOp, Error> {
        let mut terms = HashSet::new();
        let mut not_terms = HashSet::new();
        for term in ops.iter() {
            match &**term {
                Self::Not(x) => {
                    not_terms.insert(x.to_string());
                }
                x => {
                    terms.insert(x.to_string());
                }
            }
        }
        if terms.intersection(&not_terms).next().is_some() {
            return Ok(Self::False());
        }
        Ok(Self::And(ops))
    }

    /// apply consensus
    /// (X && Y) || (!X && Z) || (Y && Z) == (X && Y) || (!X && Z)
    fn consensus_or(ops: Vec<Box<SymOp>>) -> Result<SymOp, Error> {
        let (and_terms, _) : (Vec<Box<SymOp>>, Vec<Box<SymOp>>) = ops.clone().into_iter().partition(|op| if let Self::And(..) = &**op { true } else { false });

        let num_and_terms = and_terms.len();
        let mut and_positive = vec![HashMap::new(); num_and_terms];
        let mut and_negative = vec![HashMap::new(); num_and_terms];

        for (i, and_term) in and_terms.clone().into_iter().enumerate() {
            let Self::And(terms) = *and_term else {
                return Err(Error::Bug("unreachable".into()));
            };
            for term in terms.into_iter() {
                if let Self::Not(nterm) = *term {
                    and_negative[i].insert(nterm.to_string(), nterm);
                }
                else {
                    and_positive[i].insert(term.to_string(), term);
                }
            }
        }

        let and_positive_sets : Vec<HashSet<String>> = and_positive.iter().map(|terms| terms.keys().map(|term_s| term_s.to_string()).collect::<HashSet<_>>()).collect();
        let and_negative_sets : Vec<HashSet<String>> = and_negative.iter().map(|terms| terms.keys().map(|term_s| term_s.to_string()).collect::<HashSet<_>>()).collect();

        trace!("consensus_or: and_positive_sets = {and_positive_sets:?}");
        trace!("consensus_or: and_negative_sets = {and_negative_sets:?}");

        // find terms X where both X and !X are present in different conjunctions
        let mut complements = vec![];
        for i in 0..num_and_terms {
            for j in 0..num_and_terms {
                if i == j {
                    continue;
                }
                for term_s in and_positive_sets[i].intersection(&and_negative_sets[j]) {
                    let neg_term = and_negative[j].get(term_s).expect("unreachable");
                    let neg_term_s = SymOp::Not(neg_term.clone()).to_string();
                    complements.push((term_s.clone(), neg_term_s, i, j));
                }
            }
        }

        // find the Y and Z terms
        let mut consensus_terms = HashSet::new();
        for (term_s, not_term_s, i, j) in complements.iter() {
            let SymOp::And(pos) = &*and_terms[*i] else { unreachable!() };
            let SymOp::And(neg) = &*and_terms[*j] else { unreachable!() };
            let mut yz_terms = HashMap::new();
            for v in pos.iter() {
                let t = v.to_string();
                if *term_s == t || *not_term_s == t {
                    continue;
                }
                yz_terms.insert(t.clone(), v.clone());
            }
            for v in neg.iter() {
                let t = v.to_string();
                if *term_s == t || *not_term_s == t {
                    continue;
                }
                yz_terms.insert(t.clone(), v.clone());
            }
            let yz_term = SymOp::And(yz_terms.into_iter().map(|(_, v)| v).collect());
            consensus_terms.insert(yz_term.to_string());
        }

        trace!("consensus_or: consensus_terms = {consensus_terms:?}");

        let final_terms : Vec<_> = ops
            .into_iter()
            .filter(|op| !consensus_terms.contains(&op.to_string()))
            .collect();

        assert!(final_terms.len() > 1);
        Ok(Self::Or(final_terms))
    }

    /// apply and-absorption
    /// X && (X || Y) ==> X
    fn absorption_and(ops: Vec<Box<SymOp>>) -> Result<SymOp, Error> {
        let mut x_terms = HashSet::new();
        for op in ops.clone().into_iter() {
            x_terms.insert(op);
        }

        let mut retain_ops = vec![];

        // look for X || Y
        for op in ops.into_iter() {
            if let SymOp::Or(inner) = *op {
                let inner_set : HashSet<_> = inner.into_iter().collect();
                let mut absorb = false;
                for x_term in x_terms.iter() {
                    if inner_set.contains(x_term) {
                        // this is X || Y, so it can be absorbed
                        absorb = true;
                        break;
                    }
                }
                if absorb {
                    continue;
                }
                retain_ops.push(Box::new(SymOp::Or(inner_set.into_iter().collect())));
            }
            else {
                retain_ops.push(op);
            }
        }

        if retain_ops.len() == 1 {
            return Ok(*retain_ops.pop().expect("unreachable"));
        }

        Ok(SymOp::And(retain_ops))
    }

    /// distribute and across or.
    /// (a || b) && c ==> (a && c) || (b && c)
    ///
    /// (a || b) && (c || d) ==> (a && (c || d)) || (b && (c || d))
    ///                      ==> ((a && c) || (a && d)) || ((b && c) || (b && d))
    ///                      ==> (a && c) || (a && d) || (b && c) || (b && d)
    ///
    /// etc.
    fn distribute_and(mut ops: Vec<Box<SymOp>>) -> Result<SymOp, Error> {
        if ops.len() < 2 {
            return Err(Error::Bug(format!("(and ..) with fewer than two terms: {:?}", &ops)));
        }
        let t2 = *ops.pop().expect("unreachable");
        let t1 = if ops.len() == 1 {
            *ops.pop().expect("unreachable")
        }
        else {
            Self::distribute_and(ops)?
        };
        let op = match (t1, t2) {
            (Self::Or(t1_ops), x) => SymOp::Or(t1_ops.into_iter().map(|op| Box::new(SymOp::And(vec![op, Box::new(x.clone())]))).collect()),
            (x, Self::Or(t2_ops)) => SymOp::Or(t2_ops.into_iter().map(|op| Box::new(SymOp::And(vec![op, Box::new(x.clone())]))).collect()),
            (x, y) => SymOp::And(vec![Box::new(x), Box::new(y)])
        };

        // lift out any nested-ANDs coming from distribution
        if let Self::And(mut consolidated_ops) = op {
            let new_consolidated_ops = loop {
                let mut new_consolidated_ops = vec![];
                let mut lifted = false;
                for op in consolidated_ops.into_iter() {
                    if let Self::And(inner_ops) = *op {
                        for inner_op in inner_ops.into_iter() {
                            new_consolidated_ops.push(inner_op);
                            lifted = true;
                        }
                    }
                    else {
                        new_consolidated_ops.push(op);
                    }
                }
                if !lifted {
                    break new_consolidated_ops;
                }
                consolidated_ops = new_consolidated_ops;
            };
            Ok(Self::And(new_consolidated_ops))
        }
        else {
            Ok(op)
        }
    }

    /// Fold and propagate constants in an And(..)
    fn simplify_and(ops: Vec<Box<SymOp>>) -> Result<SymOp, Error> {
        trace!("simplify_and: ops = {ops:?}");
        let mut consolidated_ops = vec![];
        for op in ops.into_iter() {
            if let Self::And(inner_ops) = *op {
                for inner_op in inner_ops.into_iter() {
                    let inner_op = inner_op.simplify()?;
                    consolidated_ops.push(Box::new(inner_op));
                }
            }
            else {
                consolidated_ops.push(Box::new(op.simplify()?));
            }
        }
        trace!("simplify_and: consolidated_ops = {}", consolidated_ops.iter().map(|op| op.to_string()).collect::<Vec<_>>().join(", "));
      
        let consolidated_and = Self::distribute_and(consolidated_ops)?;
        let SymOp::And(consolidated_ops) = consolidated_and else {
            return Ok(consolidated_and);
        };
        
        trace!("simplify_and: distribute_and: consolidated_ops = {}", consolidated_ops.iter().map(|op| op.to_string()).collect::<Vec<_>>().join(", "));
            
        // find contradictions with inequalities
        let consolidated_ops = match Self::and_inequality_constant_simplify(consolidated_ops)? {
            Self::And(ops) => ops,
            x => {
                return Ok(x);
            }
        };
        
        trace!("simplify_and: and_inequality_constant_simplify: consolidated_ops = {}", consolidated_ops.iter().map(|op| op.to_string()).collect::<Vec<_>>().join(", "));
        
        // remove (and (x > y) (x < y)) contradictions
        let mut consolidated_ops = Self::and_inequality_symbolic_contradictions(consolidated_ops)?;
        if consolidated_ops.len() == 1 {
            return Ok(*consolidated_ops.pop().expect("unreachable"));
        }
        
        trace!("simplify_and: and_inequality_symbolic_contradictions: consolidated_ops = {}", consolidated_ops.iter().map(|op| op.to_string()).collect::<Vec<_>>().join(", "));

        // flatten (is-eq) terms which have overlapping inner terms
        let consolidated_ops = Self::and_flatten_equals(consolidated_ops)?;
        
        trace!("simplify_and: and_flatten_equals: consolidated_ops = {}", consolidated_ops.iter().map(|op| op.to_string()).collect::<Vec<_>>().join(", "));
        
        // eliminate and-eq contradictions 
        let consolidated_ops = Self::and_equals_contradiction(consolidated_ops)?;
        
        trace!("simplify_and: and_equals_contradiction: consolidated_ops = {}", consolidated_ops.iter().map(|op| op.to_string()).collect::<Vec<_>>().join(", "));
        
        // remove (and (is-eq x k1) (not (is-eq x k2))) redundancies (where k1 != k2)
        let consolidated_ops = Self::and_equals_redundant(consolidated_ops)?;
        
        trace!("simplify_and: and_equals_redundant: consolidated_ops = {}", consolidated_ops.iter().map(|op| op.to_string()).collect::<Vec<_>>().join(", "));

        // eliminate and-cons contradictions 
        let consolidated_ops = match Self::and_cons_contradiction(consolidated_ops)? {
            Self::And(ops) => ops,
            x => {
                return Ok(x);
            }
        };
        
        trace!("simplify_and: and_cons_contradiction: consolidated_ops = {}", consolidated_ops.iter().map(|op| op.to_string()).collect::<Vec<_>>().join(", "));

        // and contradiction
        let consolidated_ops = match Self::contradiction_and(consolidated_ops)? {
            Self::And(ops) => ops,
            x => {
                return Ok(x);
            }
        };

        trace!("simplify_and: contradiction_and: consolidated_ops = {}", consolidated_ops.iter().map(|op| op.to_string()).collect::<Vec<_>>().join(", "));
        
        // and absorption
        let consolidated_ops = match Self::absorption_and(consolidated_ops)? {
            Self::And(ops) => ops,
            x => {
                return Ok(x);
            }
        };

        trace!("simplify_and: aborption_and: consolidated_ops = {}", consolidated_ops.iter().map(|op| op.to_string()).collect::<Vec<_>>().join(", "));

        // remove pure duplicates and simplfiy
        let simplified = Self::dedup_readonly_booleans(consolidated_ops)?;
        
        trace!("simplify_and: dedup_readonly_booleans: simplified = {simplified:?}");

        // constant elimination
        let simplified = Self::simplify_assoc_variadic(
            "and",
            simplified,
            |op| *op == Self::True(),
            |op| if let Self::And(inner) = op { Some(inner) } else { None },
            |new_ops| Self::And(new_ops)
        )?;
        let SymOp::And(simplified) = simplified else {
            return Ok(simplified);
        };
        
        trace!("simplify_and: simplify_assoc_variadic: simplified = {simplified:?}");

        // domination: False && X == False
        for op in simplified.iter() {
            if let Self::Constant(Value::Bool(false)) = &**op {
                return Ok(SymOp::Constant(Value::Bool(false)));
            }
        }

        // identity: True && X == X
        let mut simplified : Vec<_> = simplified.into_iter().filter(|s| if let Self::Constant(Value::Bool(true)) = **s { false } else { true }).collect();
        
        trace!("simplify_and: domination: simplified = {simplified:?}");

        // if they were all true, then simplified would be empty
        if simplified.len() == 0 {
            simplified.push(Box::new(Self::Constant(Value::Bool(true))));
        }
        else if simplified.len() == 1 {
            // lift out
            trace!("simplify_and: simplified = {simplified:?}");
            let Some(inner) = simplified.pop() else { return Err(Error::Bug("unreachable -- simplify_and simplified.len() == 1 but pop failed".into())); };
            return Ok(*inner);
        }

        trace!("simplify_and: simplified = {simplified:?}");
        Ok(Self::And(simplified))
    }

    /// apply or-absorption
    /// X || (X && Y) ==> X
    fn absorption_or(ops: Vec<Box<SymOp>>) -> Result<SymOp, Error> {
        let mut x_terms = HashSet::new();
        for op in ops.clone().into_iter() {
            x_terms.insert(op);
        }

        let mut retain_ops = vec![];

        // look for X && Y
        for op in ops.into_iter() {
            if let SymOp::And(inner) = *op {
                let inner_set : HashSet<_> = inner.into_iter().collect();
                let mut absorb = false;
                for x_term in x_terms.iter() {
                    if inner_set.contains(x_term) {
                        // this is X && Y, so it can be absorbed
                        absorb = true;
                        break;
                    }
                }
                if absorb {
                    continue;
                }
                retain_ops.push(Box::new(SymOp::And(inner_set.into_iter().collect())));
            }
            else {
                retain_ops.push(op);
            }
        }

        if retain_ops.len() == 1 {
            return Ok(*retain_ops.pop().expect("unreachable"));
        }

        Ok(SymOp::Or(retain_ops))
    }
    
    /// fold and propagate constants for an Or(..)
    fn simplify_or(ops: Vec<Box<SymOp>>) -> Result<SymOp, Error> {
        trace!("simplify_or: ops = {}", ops.iter().map(|o| o.to_string()).collect::<Vec<_>>().join(", "));
        let mut consolidated_ops = vec![];
        for op in ops.into_iter() {
            if let Self::Or(inner_ops) = *op {
                for inner_op in inner_ops.into_iter() {
                    let inner_op = inner_op.simplify()?;
                    consolidated_ops.push(Box::new(inner_op));
                }
            }
            else {
                consolidated_ops.push(Box::new(op.simplify()?));
            }
        }
        
        trace!("simplify_or: consolidated_ops = {}", consolidated_ops.iter().map(|o| o.to_string()).collect::<Vec<_>>().join(", "));
        
        // remove readonly duplicates and simplify
        // (i.e. if we have X || X, then replace with X)
        let consolidated_ops = Self::dedup_readonly_booleans(consolidated_ops)?;
        
        trace!("simplify_or: dedup_readonly_booleans: consolidated_ops = {}", consolidated_ops.iter().map(|o| o.to_string()).collect::<Vec<_>>().join(", "));

        // constant elimination
        let consolidated_ops = Self::simplify_assoc_variadic(
            "or",
            consolidated_ops,
            |op| *op == Self::False(),
            |op| if let Self::Or(inner) = op { Some(inner) } else { None },
            |new_ops| Self::Or(new_ops)
        )?;
        let Self::Or(consolidated_ops) = consolidated_ops else {
            return Ok(consolidated_ops);
        };

        // domination: True || X == True
        for op in consolidated_ops.iter() {
            if let Self::Constant(Value::Bool(true)) = &**op {
                return Ok(Self::Constant(Value::Bool(true)));
            }
        }
        // identity: False || X == X
        let mut consolidated_ops : Vec<_> = consolidated_ops.into_iter().filter(|s| if let Self::Constant(Value::Bool(false)) = **s { false } else { true }).collect();
       
        if vec![Box::new(SymOp::Constant(Value::Bool(false)))] == Self::and_equals_contradiction(consolidated_ops.clone())? {
            // (is-eq x y) and (not (is-eq x y)) detected, which for (or ..) is a tautology
            return Ok(SymOp::Constant(Value::Bool(true)));
        }
        
        // if they were all false, then consolidated_ops would be empty
        if consolidated_ops.len() == 0 {
            return Ok(Self::Constant(Value::Bool(false)));
        }
        else if consolidated_ops.len() == 1 {
            // lift out
            let Some(inner) = consolidated_ops.pop() else { return Err(Error::Bug("unreachable -- simplify_or consolidated_ops.len() == 1 but pop failed".into())); };
            return Ok(*inner);
        }
        
        trace!("simplify_or: and_equals_contradiction: consolidated_ops = {}", consolidated_ops.iter().map(|o| o.to_string()).collect::<Vec<_>>().join(", "));
        
        if Self::Constant(Value::Bool(false)) == Self::and_cons_contradiction(consolidated_ops.clone())? {
            // cons contradiction detected, which for (or ..) is a tautology
            return Ok(SymOp::Constant(Value::Bool(true)));
        }
        
        trace!("simplify_or: and_cons_contradiction: consolidated_ops = {}", consolidated_ops.iter().map(|o| o.to_string()).collect::<Vec<_>>().join(", "));

        // absorption
        // X || (X && Y) ==> X
        let absorbed_or = Self::absorption_or(consolidated_ops)?;
        let SymOp::Or(consolidated_ops) = absorbed_or else {
            return Ok(absorbed_or);
        };
        
        trace!("simplify_or: absorption_or: consolidated_ops = {}", consolidated_ops.iter().map(|o| o.to_string()).collect::<Vec<_>>().join(", "));

        // consensus
        let consensus_or = Self::consensus_or(consolidated_ops)?;
        let SymOp::Or(mut consolidated_ops) = consensus_or else {
            return Ok(consensus_or);
        };
        
        trace!("simplify_or: consensus_or: consolidated_ops = {}", consolidated_ops.iter().map(|o| o.to_string()).collect::<Vec<_>>().join(", "));

        // if they were all false, then consolidated_ops would be empty
        if consolidated_ops.len() == 0 {
            return Ok(Self::Constant(Value::Bool(false)));
        }
        else if consolidated_ops.len() == 1 {
            // lift out
            let Some(inner) = consolidated_ops.pop() else { return Err(Error::Bug("unreachable -- simplify_or consolidated_ops.len() == 1 but pop failed".into())); };
            return Ok(*inner);
        }
        Ok(Self::Or(consolidated_ops))
    }

    /// fold and propagate constants for a Not(..)
    fn simplify_not(op: Box<SymOp>) -> Result<SymOp, Error> {
        match *op {
            Self::Constant(x) => {
                let v = Self::context_free_clarity_eval_mainnet(vec![
                    SymbolicExpression::atom("not".try_into()?),
                    SymbolicExpression::literal_value(x),
                ])?
                .ok_or_else(|| Error::Bug("Clarity VM evaluated to None".into()))?;
                Ok(Self::Constant(v))
            },
            // (not (not x)) == x
            Self::Not(x) => Ok(*x),
            // (not (> x y)) == (<= x y)
            Self::Greater(x, y) => Ok(Self::Leq(x, y)),
            // (not (>= x y)) == (< x y)
            Self::Geq(x, y) => Ok(Self::Less(x, y)),
            // (not (< x y)) == (>= x y)
            Self::Less(x, y) => Ok(Self::Geq(x, y)),
            // (not (<= x y)) == (> x y)
            Self::Leq(x, y) => Ok(Self::Greater(x, y)),
            // DeMorgan's Laws
            // (not (and x0 x1 x2 ..)) == (or (not x0) (not x1) (not x2) ...)
            Self::And(ops) => Ok(Self::Or(ops.into_iter().map(|op| Box::new(Self::Not(op))).collect())),
            // (not (or x0 x1 x2 ...)) == (and (not x0) (not x1) (not x2) ...)
            Self::Or(ops) => Ok(Self::And(ops.into_iter().map(|op| Box::new(Self::Not(op))).collect())),
            // (not (is-eq x0 x1 x2 ...)) == (or (not (is-eq x0 x1)) (not (is-eq x1 x2)) ...)
            Self::Equals(ops) => {
                if ops.len() <= 2 {
                    Ok(Self::Not(Box::new(Self::Equals(ops))))
                }
                else {
                    let mut ret = vec![];
                    for i in 0..(ops.len()-1) {
                        let op1 = ops[i].clone();
                        let op2 = ops[i+1].clone();
                        ret.push(Box::new(Self::Not(Box::new(Self::Equals(vec![Box::new(*op1), Box::new(*op2)])))));
                    }
                    Ok(Self::Or(ret))
                }
            }
            // (not (is-some x)) == (is-none x)
            Self::IsSome(op) => Ok(Self::IsNone(op)),
            // (not (is-none x)) == (is-some x)
            Self::IsNone(op) => Ok(Self::IsSome(op)),
            x => Ok(Self::Not(Box::new(x)))
        }
    }
    
    /// Deduplicate pure and read-only boolean formulae
    /// (i.e. ones that don't do mutable I/O)
    fn dedup_readonly_booleans(ops: Vec<Box<SymOp>>) -> Result<Vec<Box<SymOp>>, Error> {
        // remove pure duplicates and simplfiy
        let mut pure_distinct = HashSet::new();
        let mut simplified = vec![];
        for op in ops.into_iter() {
            if op.is_read_only() {
                if !pure_distinct.contains(&op) {
                    pure_distinct.insert(op.clone());
                    simplified.push(op);
                }
            }
            else {
                simplified.push(op);
            }
        }
        Ok(simplified)
    }
        
    fn decompose_adds_subs(op: SymOp) -> Result<(Vec<Box<SymOp>>, Vec<Box<SymOp>>), Error> {
        match op {
            Self::Add(ops) => {
                Ok((ops, vec![]))
            }
            Self::Subtract(ops) => {
                let Some(first) = ops.first().cloned() else {
                    return Err(Error::Bug("Empty subtract".to_string()));
                };
                if let Some(rest) = ops.get(1..) {
                    Ok((vec![first], rest.to_vec()))
                }
                else {
                    // this is negation
                    Ok((vec![], vec![first]))
                }
            }
            x => Ok((vec![Box::new(x)], vec![]))
        }
    }

    /// Gather terms across a comparator operation
    /// Given (a1 + b1 + c1 + ...) - (x1 + y1 + z1 + ...) CMP_OP (a2 + b2 + c2 + ...) - (x2 + y2 + z2 + ..),
    /// Reduce to (a1 + b1 + c1 + ...) + (x2 + y2 + z2 + ...) CMP_OP (a2 + b2 + c2 + ...) + (x1 + y1 + z1 + ...).
    /// In other words, eliminate subtraction on both sides, and set the left-hand side to 0
    fn gather_comparator_terms(left_op: Box<SymOp>, right_op: Box<SymOp>) -> Result<(Box<SymOp>, Box<SymOp>), Error> {
        let unsigned = [&left_op, &right_op].iter().find(|op| op.is_unsigned().is_some()).map(|op| op.is_unsigned().expect("unreachable")).unwrap_or(false);
        let zero = if unsigned {
            Self::Constant(Value::UInt(0))
        }
        else {
            Self::Constant(Value::Int(0))
        };
        let mut lhs = zero.clone();
        let rhs = Self::Subtract(vec![right_op.clone(), left_op.clone()]).simplify()?;

        // add subtracted terms back to lhs
        let (mut adds, subs) = Self::decompose_adds_subs(rhs)?;
        for sub in subs.into_iter() {
            lhs = lhs.add(*sub);
        }

        let rhs = if adds.len() == 0 {
            zero
        }
        else if adds.len() == 1 {
            *adds.pop().expect("unreachable")
        }
        else {
            Self::Add(adds)
        };

        Ok((Box::new(lhs.simplify()?), Box::new(rhs.simplify()?)))
    }

    /// Gather terms across an equality operation
    fn gather_eq_terms(op_sets: Vec<Box<SymOp>>) -> Result<Vec<Box<SymOp>>, Error> {
        if op_sets.len() < 2 {
            return Err(Error::Bug("Equality check between fewer than 2 terms".into()));
        }
      
        let is_unsigned = |ops: &[Vec<Box<SymOp>>]| -> bool {
            let mut is_unsigned = None;
            for op_set in ops.iter() {
                if is_unsigned.is_some() {
                    break;
                }
                for op in op_set.iter() {
                    if op.is_unsigned().is_some() {
                        is_unsigned = op.is_unsigned();
                        break;
                    }
                }
            }
            is_unsigned.unwrap_or(false)
        };

        let make_zero = |ops: &[Vec<Box<SymOp>>]| -> SymOp {
            if is_unsigned(ops) {
                Self::Constant(Value::UInt(0))
            }
            else {
                Self::Constant(Value::Int(0))
            }
        };
      
        let make_add = |mut adds: Vec<Box<SymOp>>, ops: &[Vec<Box<SymOp>>]| -> SymOp {
            if adds.len() > 1 {
                Self::Add(adds)
            }
            else if adds.len() == 1 {
                *adds.pop().expect("unreachable")
            }
            else {
                make_zero(ops)
            }
        };

        let common_terms = |left: &HashMap<String, (Box<SymOp>, u128)>, right: &HashMap<String, (Box<SymOp>, u128)>| -> HashMap<String, (Box<SymOp>, u128)> {
            let mut common = HashMap::new();
            for (l_term, (l_op, l_count)) in left.iter() {
                let Some((_, r_count)) = right.get(l_term) else {
                    continue;
                };
                common.insert(l_term.clone(), (l_op.clone(), (*l_count).min(*r_count)));
            }
            common
        };

        for (i, op) in op_sets.iter().enumerate() {
            trace!("gather_eq_terms: op {i} = {op}");
        }

        // consolidate subtractions
        let mut all_adds = vec![];
        let mut all_subs = vec![];
        let num_terms = op_sets.len();
        for (i, op) in op_sets.iter().enumerate() {
            let (add, sub) = Self::decompose_adds_subs(*op.clone())?;

            trace!("gather_eq_terms: op {i} adds = {add:?}");
            trace!("gather_eq_terms: op {i} subs = {sub:?}");

            all_adds.push(add);
            all_subs.push(sub);
        }

        // add each set's subtracted terms to all _other_ sets' added terms
        for i in 0..num_terms {
            for j in 0..num_terms {
                if i == j {
                    continue;
                }
                all_adds[i].extend(all_subs[j].clone().into_iter());
            }
        }

        let unsigned = is_unsigned(&all_adds);

        let mut add_term_counts = vec![];
        for i in 0..num_terms {
            let add_term = make_add(all_adds[i].clone(), &all_adds);

            trace!("gather_eq_terms: gathered term {i} = {add_term}");
        
            let (adds, subs) = Self::decompose_adds_subs(add_term.clone())?;
            assert_eq!(subs.len(), 0, "Subtraction in term {}: {}", i, add_term);

            let (add_term_count, _) = Self::make_add_sub_term_counts(adds, subs)?;
            add_term_counts.push(add_term_count);
        }

        assert!(add_term_counts.len() >= 2, "BUG: did not account for all add terms");

        // remove terms common to all sets
        let mut common = common_terms(&add_term_counts[0], &add_term_counts[1]);
        for i in 2..add_term_counts.len() {
            let new_common = common_terms(&add_term_counts[i-1], &add_term_counts[i]);
            let mut remove = HashSet::new();
            for (term_s, (_, count)) in common.iter_mut() {
                if let Some((_, new_count)) = new_common.get(term_s) {
                    *count = (*new_count).min(*count);
                }
                else {
                    remove.insert(term_s.clone());
                }
            }
            for term_s in remove.into_iter() {
                common.remove(&term_s);
            }
        }

        trace!("gather_eq_terms: {} term(s) common to all terms", common.len());
        for (_, (op, count)) in common.iter() {
            trace!("gather_eq_terms: comon term: count {count} of {op}");
        }

        if common.len() == 0 {
            // nothing in common, so we can stop
            return Ok(op_sets);
        }

        let mut sub_ops = vec![];
        for (_, (op, count)) in common.into_iter() {
            let term = if count > 1 {
                let count_term = if unsigned {
                    Box::new(Self::Constant(Value::UInt(count as u128)))
                }
                else {
                    Box::new(Self::Constant(Value::Int(count as i128)))
                };
                Self::Multiply(vec![count_term, op])
            }
            else {
                *op
            };
            sub_ops.push(Box::new(term));
        }

        let mut new_ops = vec![];
        for i in 0..num_terms {
            let adds_uniq = Box::new(Self::Subtract(vec![Box::new(make_add(all_adds[i].clone(), &all_adds)), Box::new(make_add(sub_ops.clone(), &all_adds))]).simplify()?);
            new_ops.push(adds_uniq);
        }
        Ok(new_ops)
    }

    // fold and propagate constants for an Equals(..)
    fn simplify_equals(ops: Vec<Box<SymOp>>) -> Result<SymOp, Error> {
        let mut consolidated_ops = vec![];
        for op in ops.into_iter() {
            let op = Box::new(op.simplify()?);
            consolidated_ops.push(op);
        }

        // remove pure duplicates and simplify
        let simplified = Self::dedup_readonly_booleans(consolidated_ops)?;

        // if dedup'ing left us with only one entry, then this is True
        if simplified.len() == 1 {
            // lift out
            return Ok(Self::True());
        }

        // if we have multiple constants that are distinct, then this is False
        let consts : HashSet<_> = simplified.iter().filter_map(|op| if op.is_constant() { Some(op.clone()) } else { None }).collect();
        if consts.len() > 1 {
            return Ok(Self::False());
        }

        trace!("simplify_equals: simplified = {}", simplified.iter().map(|op| op.to_string()).collect::<Vec<_>>().join(", "));

        let simplified = Self::gather_eq_terms(simplified)?;
        
        trace!("simplify_equals: gather_eq_terms = {}", simplified.iter().map(|op| op.to_string()).collect::<Vec<_>>().join(", "));
        
        Ok(Self::Equals(simplified))
    }
    
    /// Evaluate a list of symbolic expressions without concern to any surrounding context (e.g.
    /// no access to the DB or globals, and without concern to the calling contract or whether or
    /// not we're on mainnet)
    fn context_free_clarity_eval_mainnet(inner_syms: Vec<SymbolicExpression>) -> Result<Option<Value>, Error> {
        let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::transient(), "contract".try_into()?);
        let syms = vec![SymbolicExpression::list(inner_syms)];

        let mut backing_store = BackingStore::new();
        let mut contract_context = ContractContext::new(contract_id, DEFAULT_CLARITY_VERSION);

        let conn = backing_store.as_clarity_db();
        let mut global_context = GlobalContext::new(
            true,
            CHAIN_ID_MAINNET,
            conn,
            LimitedCostTracker::new_free(),
            DEFAULT_STACKS_EPOCH,
        );

        global_context
            .execute(|g| {
                let res = eval_all(&syms, &mut contract_context, g, None);
                res
            })
            .map_err(|e| match e {
                VmExecutionError::Runtime(RuntimeError::Arithmetic(s), _) => Error::Arithmetic(format!("Clarity VM arithmetic error: '{s}' on evaluating {:?}", &syms)),
                VmExecutionError::Runtime(RuntimeError::ArithmeticOverflow, _) => Error::Arithmetic(format!("Clarity VM arithmetic error: overflow on evaluating {:?}", &syms)),
                VmExecutionError::Runtime(RuntimeError::ArithmeticUnderflow, _) => Error::Arithmetic(format!("Clarity VM arithmetic error: underflow on evaluating {:?}", &syms)),
                e => Error::from(ClarityEvalError::from(e)),
            })
    }

    /// Simplify a native function with arity 1.
    /// Only allowed for context-free native functions
    fn simplify_native_1arg<F>(func_name: &str, op: Box<SymOp>, cons: F) -> Result<SymOp, Error>
    where
        F: FnOnce(Box<SymOp>) -> SymOp
    {
        match op.simplify()? {
            Self::Constant(v) => {
                let v = Self::context_free_clarity_eval_mainnet(vec![
                    SymbolicExpression::atom(func_name.try_into()?),
                    SymbolicExpression::literal_value(v)
                ])?
                .ok_or_else(|| Error::Bug("Clarity VM evaluated to None".into()))?;
                Ok(Self::Constant(v))
            }
            x => Ok(cons(Box::new(x)))
        }
    }
    
    /// Simplify a native function with arity 2
    /// Only allowed for context-free native functions
    fn simplify_native_2args<F>(func_name: &str, op1: Box<SymOp>, op2: Box<SymOp>, cons: F) -> Result<SymOp, Error>
    where
        F: FnOnce(Box<SymOp>, Box<SymOp>) -> SymOp
    {
        match (op1.simplify()?, op2.simplify()?) {
            (Self::Constant(v1), Self::Constant(v2)) => {
                let v = Self::context_free_clarity_eval_mainnet(vec![
                    SymbolicExpression::atom(func_name.try_into()?),
                    SymbolicExpression::literal_value(v1),
                    SymbolicExpression::literal_value(v2)
                ])?
                .ok_or_else(|| Error::Bug("Clarity VM evaluated to None".into()))?;
                Ok(Self::Constant(v))
            }
            (x, y) => Ok(cons(Box::new(x), Box::new(y)))
        }
    }
    
    /// Simplify a native function with arity 3
    /// Only allowed for context-free native functions
    fn simplify_native_3args<F>(func_name: &str, op1: Box<SymOp>, op2: Box<SymOp>, op3: Box<SymOp>, cons: F) -> Result<SymOp, Error>
    where
        F: FnOnce(Box<SymOp>, Box<SymOp>, Box<SymOp>) -> SymOp
    {
        match (op1.simplify()?, op2.simplify()?, op3.simplify()?) {
            (Self::Constant(v1), Self::Constant(v2), Self::Constant(v3)) => {
                let v = Self::context_free_clarity_eval_mainnet(vec![
                    SymbolicExpression::atom(func_name.try_into()?),
                    SymbolicExpression::literal_value(v1),
                    SymbolicExpression::literal_value(v2),
                    SymbolicExpression::literal_value(v3)
                ])?
                .ok_or_else(|| Error::Bug("Clarity VM evaluated to None".into()))?;
                Ok(Self::Constant(v))
            }
            (x, y, z) => Ok(cons(Box::new(x), Box::new(y), Box::new(z)))
        }
    }
    
    /// Simplify a native function with arity 5
    /// Only allowed for context-free native functions
    fn simplify_native_5args<F>(func_name: &str, op1: Box<SymOp>, op2: Box<SymOp>, op3: Box<SymOp>, op4: Box<SymOp>, op5: Box<SymOp>, cons: F) -> Result<SymOp, Error>
    where
        F: FnOnce(Box<SymOp>, Box<SymOp>, Box<SymOp>, Box<SymOp>, Box<SymOp>) -> SymOp
    {
        match (op1.simplify()?, op2.simplify()?, op3.simplify()?, op4.simplify()?, op5.simplify()?) {
            (Self::Constant(v1), Self::Constant(v2), Self::Constant(v3), Self::Constant(v4), Self::Constant(v5)) => {
                let v = Self::context_free_clarity_eval_mainnet(vec![
                    SymbolicExpression::atom(func_name.try_into()?),
                    SymbolicExpression::literal_value(v1),
                    SymbolicExpression::literal_value(v2),
                    SymbolicExpression::literal_value(v3),
                    SymbolicExpression::literal_value(v4),
                    SymbolicExpression::literal_value(v5),
                ])?
                .ok_or_else(|| Error::Bug("Clarity VM evaluated to None".into()))?;
                Ok(Self::Constant(v))
            }
            (x, y, z, w, v) => Ok(cons(Box::new(x), Box::new(y), Box::new(z), Box::new(w), Box::new(v)))
        }
    }

    /// Simplify a tuple get, besides a get from an option
    fn inner_simplify_tuple_get(name: ClarityName, op: SymOp) -> Result<Option<SymOp>, Error> {
        trace!("simplify (get {name} {op})");
        match op {
            Self::Constant(Value::Tuple(data)) => {
                trace!("op is a constant tuple");
                let v = Self::context_free_clarity_eval_mainnet(vec![
                    SymbolicExpression::atom("get".try_into()?),
                    SymbolicExpression::atom(name.clone()),
                    SymbolicExpression::literal_value(Value::Tuple(data))
                ])?
                .ok_or_else(|| Error::Bug("Clarity VM evaluated to None".into()))?;
                Ok(Some(Self::Constant(v)))
            }
            Self::Constant(Value::Optional(optdata)) => {
                if let Some(value) = optdata.data && let Value::Tuple(data) = &*value {
                    trace!("op is a constant optional tuple");
                    let v = Self::context_free_clarity_eval_mainnet(vec![
                        SymbolicExpression::atom("get".try_into()?),
                        SymbolicExpression::atom(name.clone()),
                        SymbolicExpression::literal_value(Value::Tuple(data.clone()))
                    ])?
                    .ok_or_else(|| Error::Bug("Clarity VM evaluated to None".into()))?;
                    Ok(Some(Self::Constant(v).some()))
                }
                else {
                    Ok(None)
                }
            }
            Self::TupleCons(fields) => {
                // lift out of fields
                trace!("op is a tuple constructor");
                let Some((_name, sym)) = fields.iter().find(|(fname, _fop)| *fname == name) else {
                    return Err(Error::Bug(format!("No such tuple key {name} in {fields:?}")));
                };
                Ok(Some(*sym.clone()))
            }
            Self::TupleMerge(base, merged) => {
                // lift out of merged, then base
                trace!("op is a tuple-merge");
                if let Some(sym) = Self::inner_simplify_tuple_get(name.clone(), *merged)? {
                    return Ok(Some(sym));
                };
                if let Some(sym) = Self::inner_simplify_tuple_get(name.clone(), *base)? {
                    return Ok(Some(sym));
                };
                Ok(None)
            }
            Self::ConsSome(some_inner_op) => {
                // N.B. this cannot recurse forever since the typechecker already made sure
                // that some_inner_op has type tuple
                trace!("op is a some-constructor");
                Ok(Self::inner_simplify_tuple_get(name.clone(), *some_inner_op)?
                    .map(|new_inner_op| Self::ConsSome(Box::new(new_inner_op))))
            }
            Self::LoadedDataVariable(var_name, inner_op) => match *inner_op {
                Self::Constant(Value::Tuple(data)) => {
                    trace!("op is a loaded data-var tuple constant");
                    let v = Self::context_free_clarity_eval_mainnet(vec![
                        SymbolicExpression::atom("get".try_into()?),
                        SymbolicExpression::atom(name.clone()),
                        SymbolicExpression::literal_value(Value::Tuple(data))
                    ])?
                    .ok_or_else(|| Error::Bug("Clarity VM evaluated to None".into()))?;
                    Ok(Some(Self::Constant(v)))
                }
                Self::TupleCons(fields) => {
                    trace!("op is a loaded data-var tuple constructor");
                    // lift out of fields
                    let Some((_name, sym)) = fields.iter().find(|(fname, _fop)| *fname == name) else {
                        return Err(Error::Bug(format!("No such tuple key {name} in {fields:?}")));
                    };
                    Ok(Some(*sym.clone()))
                }
                Self::ConsSome(some_inner_op) => {
                    trace!("op is a loaded data-var optional tuple");
                    // N.B. this cannot recurse forever since the typechecker already made sure
                    // that some_inner_op has type tuple
                    Ok(Some(Self::inner_simplify_tuple_get(name.clone(), *some_inner_op.clone())?
                       .unwrap_or(Self::LoadedDataVariable(var_name, Box::new(Self::ConsSome(some_inner_op))))))
                }
                x => Ok(Some(Self::LoadedDataVariable(var_name, Box::new(x))))
            }
            Self::LoadedMapEntry(map_name, map_key, Some(inner_op)) => match *inner_op {
                Self::Constant(Value::Tuple(data)) => {
                    trace!("op is a loaded map entry tuple constant");
                    let v = Self::context_free_clarity_eval_mainnet(vec![
                        SymbolicExpression::atom("get".try_into()?),
                        SymbolicExpression::atom(name.clone()),
                        SymbolicExpression::literal_value(Value::Tuple(data))
                    ])?
                    .ok_or_else(|| Error::Bug("Clarity VM evaluated to None".into()))?;
                    Ok(Some(Self::Constant(v).some()))
                }
                Self::TupleCons(fields) => {
                    // lift out of fields
                    trace!("op is a loaded map entry tuple constructor");
                    let Some((_name, sym)) = fields.iter().find(|(fname, _fop)| *fname == name) else {
                        return Err(Error::Bug(format!("No such tuple key {name} in {fields:?}")));
                    };
                    Ok(Some((*sym.clone()).some()))
                },
                x => Ok(Some(Self::LoadedMapEntry(map_name, map_key, Some(Box::new(x)))))
            }
            _ => Ok(None)
        }
    }

    fn simplify_tuple_get(name: ClarityName, op: SymOp) -> Result<SymOp, Error> {
        match op {
            Self::Constant(..)
            | Self::TupleCons(..)
            | Self::TupleMerge(..)
            | Self::ConsSome(..)
            | Self::LoadedDataVariable(..)
            | Self::LoadedMapEntry(..) => {
                Self::inner_simplify_tuple_get(name.clone(), op.clone())
                    .map(|op_opt| op_opt.unwrap_or(Self::TupleGet(name, Box::new(op))))
            },
            x => Ok(Self::TupleGet(name, Box::new(x)))
        }
    }

    /// Convert a type signature back into a symbolic expression
    fn type_signature_to_symbolic_expression(ts: TypeSignature) -> SymbolicExpression {
        match ts {
            TypeSignature::NoType => unreachable!(),
            TypeSignature::IntType => SymbolicExpression::atom("int".try_into().expect("infallible")),
            TypeSignature::UIntType => SymbolicExpression::atom("uint".try_into().expect("infallible")),
            TypeSignature::BoolType => SymbolicExpression::atom("bool".try_into().expect("infallible")),
            TypeSignature::SequenceType(SequenceSubtype::BufferType(buflen)) => {
                SymbolicExpression::list(vec![
                    SymbolicExpression::atom("buff".try_into().expect("infallible")),
                    SymbolicExpression::literal_value(Value::Int(u32::from(buflen) as i128))
                ])
            },
            TypeSignature::SequenceType(SequenceSubtype::ListType(listdata)) => {
                let (inner_ts, max_len) = listdata.destruct();
                SymbolicExpression::list(vec![
                    SymbolicExpression::atom("list".try_into().expect("infallible")),
                    Self::type_signature_to_symbolic_expression(inner_ts),
                    SymbolicExpression::literal_value(Value::Int(max_len as i128))
                ])
            }
            TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(len))) => {
                SymbolicExpression::list(vec![
                    SymbolicExpression::atom("string-ascii".try_into().expect("infallible")),
                    SymbolicExpression::literal_value(Value::Int(u32::from(len) as i128))
                ])
            },
            TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(len))) => {
                SymbolicExpression::list(vec![
                    SymbolicExpression::atom("string-ascii".try_into().expect("infallible")),
                    SymbolicExpression::literal_value(Value::Int(u32::from(len) as i128))
                ])
            },
            TypeSignature::PrincipalType => SymbolicExpression::atom("principal".try_into().expect("infallible")),
            TypeSignature::TupleType(tuple_ts) => {
                SymbolicExpression::list(vec![
                    SymbolicExpression::atom("tuple".try_into().expect("infallible")),
                    SymbolicExpression::list(
                        tuple_ts
                            .get_type_map()
                            .iter()
                            .map(|(name, inner_ts)| {
                                SymbolicExpression::list(vec![
                                    SymbolicExpression::atom(name.clone()),
                                    Self::type_signature_to_symbolic_expression(inner_ts.clone())
                                ])
                            })
                            .collect()
                    )
                ])
            },
            TypeSignature::OptionalType(inner_ts) => {
                SymbolicExpression::list(vec![
                    SymbolicExpression::atom("optional".try_into().expect("infallible")),
                    Self::type_signature_to_symbolic_expression(*inner_ts)
                ])
            },
            TypeSignature::ResponseType(inner_ok_err_ts) => {
                let (ok_ts, err_ts) = *inner_ok_err_ts;
                SymbolicExpression::list(vec![
                    SymbolicExpression::atom("response".try_into().expect("infallible")),
                    Self::type_signature_to_symbolic_expression(ok_ts),
                    Self::type_signature_to_symbolic_expression(err_ts)
                ])
            },
            TypeSignature::CallableType(CallableSubtype::Principal(contract_id)) => {
                // this shouldn't be possible
                SymbolicExpression::atom(format!("<{contract_id}>").as_str().try_into().expect("infallible"))
            },
            TypeSignature::CallableType(CallableSubtype::Trait(trait_id)) => {
                // this shouldn't be possible
                SymbolicExpression::atom(format!("<{}>", &trait_id.contract_identifier).as_str().try_into().expect("infallible"))
            },
            TypeSignature::ListUnionType(callables) => {
                // this shouldn't be possible
                SymbolicExpression::list(callables
                    .into_iter()
                    .map(|callable| match callable {
                        CallableSubtype::Principal(contract_id) => SymbolicExpression::atom(format!("<{contract_id}>").as_str().try_into().expect("infallible")),
                        CallableSubtype::Trait(trait_id) => SymbolicExpression::atom(format!("{}", &trait_id.contract_identifier).as_str().try_into().expect("infallible")),
                    })
                    .collect()
                )
            },
            TypeSignature::TraitReferenceType(trait_id) => {
                // OBSOLETE
                SymbolicExpression::atom(format!("{}", &trait_id.contract_identifier).as_str().try_into().expect("infallible"))
            }
        }
    }

    /// Apply tactics to simplify a symbolic operation
    fn inner_simplify(symop: SymOp) -> Result<SymOp, Error> {
        trace!("Simplify {:?}", &symop);
        match symop {
            Self::Constant(v) => Ok(Self::Constant(v)),
            Self::Variable(v) => Ok(Self::Variable(v)),
            Self::LoadedDataVariable(name, op) => {
                let simplified = op.clone().simplify()?;
                if let Self::Constant(v) = simplified {
                    Ok(Self::Constant(v))
                }
                else if let Self::Variable(v) = simplified {
                    Ok(Self::LoadedDataVariable(name, Box::new(Self::Variable(v))))
                }
                else {
                    Ok(simplified)
                }
            },
            Self::Add(ops) => {
                let flattened_adds = Self::flatten_additions(ops)?;
                let SymOp::Add(ops) = flattened_adds else {
                    return Ok(flattened_adds);
                };
                let ops = Self::simplify_assoc_variadic(
                    "+",
                    ops,
                    |op| *op == Self::Constant(Value::Int(0)) || *op == Self::Constant(Value::UInt(0)),
                    |op| if let Self::Add(inner) = op { Some(inner) } else { None },
                    |new_ops| Self::Add(new_ops)
                )?;
                
                Ok(ops)
            },
            Self::Subtract(ops) => {
                Self::simplify_subtraction(ops)
            }
            Self::Multiply(ops) => {
                let ops = Self::simplify_assoc_variadic(
                    "*",
                    ops,
                    |op| *op == Self::Constant(Value::Int(1)) || *op == Self::Constant(Value::UInt(1)),
                    |op| if let Self::Multiply(inner) = op { Some(inner) } else { None },
                    |new_ops| Self::Multiply(new_ops)
                )?;
                
                // if we have a multiply by zero, then this is all zero
                if let Self::Multiply(ops) = &ops {
                    if ops.iter().find(|op| ***op == Self::Constant(Value::Int(0))).is_some() {
                        return Ok(Self::Constant(Value::Int(0)));
                    }
                    if ops.iter().find(|op| ***op == Self::Constant(Value::UInt(0))).is_some() {
                        return Ok(Self::Constant(Value::UInt(0)));
                    }
                }

                let op = if let Self::Multiply(inner_ops) = ops {
                    // if we're multiplying two or more of Add(..) or Subtract(..), then compute the
                    // symbolic product and combine terms.
                    Self::flatten_multiply(inner_ops)?
                }
                else {
                    ops
                };

                let op = if let Self::Multiply(inner_ops) = op {
                    // combine like terms into powers.
                    // Also, combine terms and their powers: (* x (pow x y)) == (pow x (+ y 1))
                    let mut like_terms : HashMap<SymOp, SymOp> = HashMap::new();
                    for inner_op in inner_ops.into_iter() {
                        if let Self::Power(base, exp) = *inner_op {
                            if let Some(cnt_term) = like_terms.get_mut(&*base) {
                                *cnt_term = cnt_term.clone().add(*exp);
                            }
                            else {
                                like_terms.insert(*base, *exp);
                            }
                        }
                        else {
                            if let Some(cnt_term) = like_terms.get_mut(&*inner_op) {
                                *cnt_term = cnt_term.clone().add(SymOp::Constant(Value::UInt(1)));
                            }
                            else {
                                like_terms.insert(*inner_op, SymOp::Constant(Value::UInt(1)));
                            }
                        }
                    }
                    let mut pows = vec![];
                    for (term, cnt_term) in like_terms.into_iter() {
                        pows.push(match cnt_term.simplify()? {
                            Self::Constant(Value::UInt(e)) => {
                                // (pow x u1) == x
                                if e == 1 {
                                    Box::new(term)
                                }
                                else {
                                    Box::new(Self::Power(Box::new(term), Box::new(SymOp::Constant(Value::UInt(e)))))
                                }
                            }
                            x => {
                                Box::new(Self::Power(Box::new(term), Box::new(x)))
                            }
                        });
                    }
                    if pows.len() == 1 {
                        *pows.pop().expect("unreachable")
                    }
                    else {
                        Self::Multiply(pows)
                    }
                }
                else {
                    op
                };

                let op = if let Self::Multiply(inner_ops) = op {
                    // if we're multiplying two or more Power(..) items with the same base, then
                    // combine the exponents symbolically
                    let (powers, mut others) : (Vec<Box<SymOp>>, Vec<Box<SymOp>>) = inner_ops.into_iter().partition(|mul| if let Self::Power(..) = &**mul { true } else { false });
                    let mut power_table : HashMap<SymOp, SymOp> = HashMap::new();
                    for power in powers.into_iter() {
                        let Self::Power(base, exp) = *power else { unreachable!() };
                        if let Some(exps) = power_table.get_mut(&*base) {
                            *exps = exps.clone().add(*exp);
                        }
                        else {
                            power_table.insert(*base, *exp);
                        }
                    }

                    let powers : Vec<Box<SymOp>> = power_table.into_iter().map(|(base, exps)| Box::new(Self::Power(Box::new(base), Box::new(exps)))).collect();
                    others.extend(powers.into_iter());
                    Self::Multiply(others)
                }
                else {
                    op
                };
                Ok(op)
            }
            Self::Divide(ops) => {
                Self::simplify_divide(ops)
            }
            Self::ToInt(op) => {
                Self::simplify_native_1arg("to-int", op, |x| Self::ToInt(x))
            }
            Self::ToUInt(op) => {
                Self::simplify_native_1arg("to-uint", op, |x| Self::ToUInt(x))
            }
            Self::Modulo(op1, op2) => {
                Self::simplify_modulus(op1, op2)
            }
            Self::Power(base_op, exp_op) => {
                let op = Self::simplify_native_2args("pow", base_op, exp_op, |x, y| Self::Power(x, y))?;
                if let Self::Power(base, exp) = op {
                    match (*base, *exp) {
                        (Self::Constant(Value::UInt(2)), Self::Log2(x)) => {
                            // (pow u2 (log2 x)) == x
                            Ok(*x)
                        },
                        (Self::Constant(Value::Int(2)), Self::Log2(x)) => {
                            // (pow 2 (log2 x)) == x
                            Ok(*x)
                        },
                        (Self::Power(x, y), z) => {
                            // (pow (pow x y) z) == (pow x (* y z))
                            Ok(Self::Power(x, Box::new(Self::Multiply(vec![y, Box::new(z)]))))
                        }
                        (x, Self::Constant(Value::UInt(1))) => {
                            // (pow x u1) == x
                            Ok(x)
                        }
                        (x, y) => {
                            Ok(Self::Power(Box::new(x), Box::new(y)))
                        }
                    }
                }
                else {
                    Ok(op)
                }
            }
            Self::Sqrti(op) => {
                // TODO: (sqrti (* x x)) == x
                // TODO: (sqrti (* x x y)) == (* x (sqrti y))
                // TODO: (sqrti (pow y (* u2 x))) == (pow y x)
                let op = Self::simplify_native_1arg("sqrti", op, |x| Self::Sqrti(x))?;
                Ok(op)
            }
            Self::Log2(op) => {
                // TODO: (log2 (pow u2 x)) == x
                Self::simplify_native_1arg("log2", op, |x| Self::Log2(x))
            }
            Self::And(ops) => {
                Self::simplify_and(ops)
            },
            Self::Or(ops) => {
                Self::simplify_or(ops)
            },
            Self::Not(op) => {
                Self::simplify_not(op)
            },
            Self::Greater(x, y) => {
                Ok(Self::Less(y, x))
            }
            Self::Geq(x, y) => {
                Ok(Self::Leq(y, x))
            },
            Self::Equals(ops) => {
                Self::simplify_equals(ops)
            }
            Self::Leq(x, y) => {
                Ok(Self::Or(vec![Box::new(Self::Equals(vec![x.clone(), y.clone()])), Box::new(Self::Less(x, y))]))
            },
            Self::Less(x, y) => {
                let op = Self::simplify_native_2args("<", x, y, |x, y| Self::Less(x, y))?;
                if let Self::Less(x, y) = op {
                    // trivial case: x < u0 never
                    if let Self::Constant(Value::UInt(0)) = *y {
                        return Ok(Self::False())
                    }
                    let (new_x, new_y) = Self::gather_comparator_terms(x, y)?;
                    Ok(Self::Less(new_x, new_y))
                }
                else {
                    Ok(op)
                }
            }
            Self::Append(list_op, val_op) => {
                match (list_op.simplify()?, val_op.simplify()?) {
                    (Self::ListCons(mut syms), y) => {
                        // (append (list a b c) y) becomes (list a b c y) even if a, b, c, and/or y
                        // are symbols
                        syms.push(Box::new(y));
                        Ok(Self::ListCons(syms))
                    }
                    (Self::Constant(v1), Self::Constant(v2)) => {
                        // can eval directly
                        let v = Self::context_free_clarity_eval_mainnet(vec![
                            SymbolicExpression::atom("append".try_into()?),
                            SymbolicExpression::literal_value(v1),
                            SymbolicExpression::literal_value(v2)
                        ])?
                        .ok_or_else(|| Error::Bug("Clarity VM evaluated to None".into()))?;
                        Ok(Self::Constant(v))
                    }
                    (Self::Constant(Value::Sequence(SequenceData::List(mut data))), y) => {
                        // can promote a constant list to (list c1 c2 c3 .. y)
                        let mut syms : Vec<_> = data.take_items().into_iter().map(|v| Box::new(Self::Constant(v))).collect();
                        syms.push(Box::new(y));
                        Ok(Self::ListCons(syms))
                    }
                    (x, y) => {
                        Ok(Self::Append(Box::new(x), Box::new(y)))
                    }
                }
            },
            Self::Concat(ops) => {
                let mut simplified_ops : Vec<Box<SymOp>> = vec![];
                for op in ops.into_iter() {
                    simplified_ops.push(Box::new(op.simplify()?));
                }
                let mut flattened_ops : Vec<Box<SymOp>> = vec![];
                for op in simplified_ops.into_iter() {
                    if let Self::Concat(inner) = *op {
                        flattened_ops.extend(inner.into_iter());
                    }
                    else {
                        flattened_ops.push(op);
                    }
                }
                let mut folded_ops : Vec<Box<SymOp>> = vec![];
                let mut cur_constant = None;
                for op in flattened_ops.into_iter() {
                    if let Self::Constant(c) = *op {
                        if let Some(cur_c) = cur_constant.take() {
                            let v = Self::context_free_clarity_eval_mainnet(vec![
                                SymbolicExpression::atom("concat".try_into()?),
                                SymbolicExpression::literal_value(cur_c),
                                SymbolicExpression::literal_value(c),
                            ])?
                            .ok_or_else(|| Error::Bug("Clarity VM evaluated to None".into()))?;
                            cur_constant = Some(v);
                        }
                        else {
                            cur_constant = Some(c);
                        }
                    }
                    else {
                        if let Some(cur_constant) = cur_constant.take() {
                            folded_ops.push(Box::new(Self::Constant(cur_constant)));
                        }
                        folded_ops.push(op);
                    }
                }
                if let Some(cur_constant) = cur_constant.take() {
                    if folded_ops.len() == 0 {
                        return Ok(Self::Constant(cur_constant));
                    }

                    folded_ops.push(Box::new(Self::Constant(cur_constant)));
                }

                assert!(folded_ops.len() > 1, "Too few folded ops");
                Ok(Self::Concat(folded_ops))
            },
            Self::AsMaxLen(op1, op2) => {
                Self::simplify_native_2args("as-max-len?", op1, op2, |x, y| Self::AsMaxLen(x, y))
            },
            Self::Len(op) => {
                match op.simplify()? {
                    Self::ListCons(y) => {
                        // (len (list x y z)) can still be evaluated, even if x, y, and/or z are
                        // symbols
                        return Ok(SymOp::Constant(Value::UInt(u128::try_from(y.len()).map_err(|_| Error::Bug("Could not convert usize to u128".into()))?)));
                    }
                    Self::Constant(v) => {
                        let v = Self::context_free_clarity_eval_mainnet(vec![
                            SymbolicExpression::atom("len".try_into()?),
                            SymbolicExpression::literal_value(v)
                        ])?
                        .ok_or_else(|| Error::Bug("Clarity VM evaluated to None".into()))?;
                        Ok(Self::Constant(v))
                    }
                    z => {
                        Ok(Self::Len(Box::new(z)))
                    }
                }
            },
            Self::ElementAt(op1, op2) => {
                match (op1.simplify()?, op2.simplify()?) {
                    (Self::ListCons(x), Self::Constant(v)) => {
                        // (element-at (list x y z) v) can still be evalauted, as long as v is a
                        // constant
                        let index = match v {
                            Value::UInt(a) => usize::try_from(a).map_err(|_| Error::Bug("index cannot fit into usize".into()))?,
                            Value::Int(b) => usize::try_from(b).map_err(|_| Error::Bug("index cannot fit into usize".into()))?,
                            c => {
                                return Err(Error::Bug(format!("Invalid element-at index {c}")));
                            }
                        };

                        Ok(x.get(index).map(|sym| Self::ConsSome(sym.clone())).unwrap_or(Self::none()))
                    },
                    (Self::Constant(v1), Self::Constant(v2)) => {
                        let v = Self::context_free_clarity_eval_mainnet(vec![
                            SymbolicExpression::atom("element-at?".try_into()?),
                            SymbolicExpression::literal_value(v1),
                            SymbolicExpression::literal_value(v2)
                        ])?
                        .ok_or_else(|| Error::Bug("Clarity VM evaluated to None".into()))?;
                        Ok(Self::Constant(v))
                    }
                    (x, y) => {
                        Ok(Self::ElementAt(Box::new(x), Box::new(y)))
                    }
                }
            },
            Self::IndexOf(op1, op2) => {
                Self::simplify_native_2args("index-of?", op1, op2, |x, y| Self::IndexOf(x, y))
            },
            Self::BuffToIntLe(op) => {
                Self::simplify_native_1arg("buff-to-int-le", op, |x| Self::BuffToIntLe(x))
            },
            Self::BuffToUIntLe(op) => {
                Self::simplify_native_1arg("buff-to-uint-le", op, |x| Self::BuffToUIntLe(x))
            },
            Self::BuffToIntBe(op) => {
                Self::simplify_native_1arg("buff-to-int-be", op, |x| Self::BuffToIntBe(x))
            },
            Self::BuffToUIntBe(op) => {
                Self::simplify_native_1arg("buff-to-uint-be", op, |x| Self::BuffToUIntBe(x))
            },
            Self::IsStandard(op) => {
                Self::simplify_native_1arg("is-standard", op, |x| Self::IsStandard(x))
            },
            Self::PrincipalDestruct(op) => {
                // can't simplify context-free -- outcome depends on whether or not we're in
                // mainnet or testnet
                Ok(Self::PrincipalDestruct(Box::new(op.simplify()?)))
            },
            Self::PrincipalConstruct(op1, op2, op3_opt) => {
                // can't simplify context-free -- outcome depends on whether or not we're in
                // mainnet or testnet
                let op3_opt = if let Some(op3) = op3_opt {
                    Some(Box::new(op3.simplify()?))
                }
                else {
                    None
                };
                Ok(Self::PrincipalConstruct(Box::new(op1.simplify()?), Box::new(op2.simplify()?), op3_opt))
            },
            Self::StringToInt(op) => {
                Self::simplify_native_1arg("string-to-int?", op, |x| Self::StringToInt(x))
            },
            Self::StringToUInt(op) => {
                Self::simplify_native_1arg("string-to-uint?", op, |x| Self::StringToUInt(x))
            }
            Self::IntToAscii(op) => {
                Self::simplify_native_1arg("int-to-ascii", op, |x| Self::IntToAscii(x))
            }
            Self::IntToUtf8(op) => {
                Self::simplify_native_1arg("int-to-utf8", op, |x| Self::IntToUtf8(x))
            }
            Self::ListCons(ops) => {
                let mut simplified_ops = vec![];
                for op in ops.into_iter() {
                    simplified_ops.push(Box::new(op.simplify()?));
                }

                // if they're all constants, then convert to constant
                let all_consts = simplified_ops.iter().find(|op| if let Self::Constant(..) = &***op { false } else { true }).is_none();
                if all_consts {
                    let values : Vec<Value> = simplified_ops
                        .into_iter()
                        .map(|x| { let Self::Constant(v) = *x else { unreachable!() }; v })
                        .collect();

                    return Ok(Self::Constant(Value::cons_list(values, &DEFAULT_STACKS_EPOCH)?));
                }

                // if it's empty, replace with a constant
                if simplified_ops.len() == 0 {
                    return Ok(Self::Constant(Value::cons_list(vec![], &DEFAULT_STACKS_EPOCH)?));
                }

                Ok(Self::ListCons(simplified_ops))
            },
            Self::FetchVar(name) => Ok(Self::FetchVar(name)),
            Self::SetVar(name, op) => Ok(Self::SetVar(name, Box::new(op.simplify()?))),
            Self::FetchEntry(name, op) => Ok(Self::FetchEntry(name, Box::new(op.simplify()?))),
            Self::LoadedMapEntry(name, key_op, value_op_opt) => {
                if let Some(value_op) = value_op_opt {
                    let simplified = value_op.simplify()?;
                    Ok(simplified.some())
                }
                else {
                    Ok(Self::LoadedMapEntry(name, Box::new(key_op.simplify()?), None))
                }
            }
            Self::SetEntry(name, op1, op2) => Ok(Self::SetEntry(name, Box::new(op1.simplify()?), Box::new(op2.simplify()?))),
            Self::InsertEntry(name, op1, op2) => Ok(Self::InsertEntry(name, Box::new(op1.simplify()?), Box::new(op2.simplify()?))),
            Self::DeleteEntry(name, op) => Ok(Self::DeleteEntry(name, Box::new(op.simplify()?))),
            Self::TupleCons(fields) => {
                let mut simplified = vec![];
                for (fname, fop) in fields.into_iter() {
                    simplified.push((fname, Box::new(fop.simplify()?)));
                }

                // if they're all constants, then construct the tuple directly
                let have_syms = simplified.iter().find(|(_name, fop)| if let Self::Constant(..) = &**fop { false } else { true }).is_some();
                if !have_syms {
                    let value_list = simplified
                        .into_iter()
                        .map(|(name, fop)| {
                            let Self::Constant(v) = *fop else { unreachable!() };
                            (name, v)
                        })
                        .collect();

                    let tup = Value::Tuple(TupleData::from_data(value_list)?);
                    return Ok(Self::Constant(tup));
                }
                Ok(Self::TupleCons(simplified))
            },
            Self::TupleGet(name, op) => {
                Self::simplify_tuple_get(name, op.simplify()?)
            }
            Self::TupleMerge(op1, op2) => {
                match (op1.simplify()?, op2.simplify()?) {
                    (Self::Constant(Value::Tuple(dest_data)), Self::Constant(Value::Tuple(src_data))) => {
                        let v = Self::context_free_clarity_eval_mainnet(vec![
                            SymbolicExpression::atom("merge".try_into()?),
                            SymbolicExpression::literal_value(Value::Tuple(dest_data)),
                            SymbolicExpression::literal_value(Value::Tuple(src_data))
                        ])?
                        .ok_or_else(|| Error::Bug("Clarity VM evaluated to None".into()))?;
                        Ok(Self::Constant(v))
                    }
                    (Self::Constant(Value::Tuple(dest_data)), Self::TupleCons(src_syms)) => {
                        // (merge constant-tuple symbolic-tuplecons) produces a symbolic-tuplecons
                        let mut merged : BTreeMap<_, _> = dest_data.data_map.into_iter().map(|(name, val)| (name, Box::new(SymOp::Constant(val)))).collect();
                        for (name, symop) in src_syms.into_iter() {
                            merged.insert(name, symop);
                        }
                        Ok(Self::TupleCons(merged.into_iter().collect()))
                    },
                    (Self::TupleCons(dest_syms), Self::Constant(Value::Tuple(src_data))) => {
                        let mut merged : BTreeMap<_, _> = dest_syms.into_iter().collect();
                        for (name, val) in src_data.data_map.into_iter() {
                            merged.insert(name, Box::new(SymOp::Constant(val)));
                        }
                        Ok(Self::TupleCons(merged.into_iter().collect()))
                    }
                    (Self::TupleCons(dest_syms), Self::TupleCons(src_syms)) => {
                        let mut merged : BTreeMap<_, _> = dest_syms.into_iter().collect();
                        for (name, symop) in src_syms.into_iter() {
                            merged.insert(name, symop);
                        }
                        Ok(Self::TupleCons(merged.into_iter().collect()))
                    },
                    (x, y) => Ok(Self::TupleMerge(Box::new(x), Box::new(y)))
                }
            }
            Self::Hash160(op) => {
                Self::simplify_native_1arg("hash160", op, |x| Self::Hash160(x))
            }
            Self::Sha256(op) => {
                Self::simplify_native_1arg("sha256", op, |x| Self::Sha256(x))
            }
            Self::Sha512(op) => {
                Self::simplify_native_1arg("sha512", op, |x| Self::Sha512(x))
            }
            Self::Sha512Trunc256(op) => {
                Self::simplify_native_1arg("sha512/256", op, |x| Self::Sha512Trunc256(x))
            }
            Self::Keccak256(op) => {
                Self::simplify_native_1arg("keccak256", op, |x| Self::Keccak256(x))
            }
            Self::Secp256k1Recover(op1, op2) => {
                Self::simplify_native_2args("secp256k1-recover?", op1, op2, |x, y| Self::Secp256k1Recover(x, y))
            }
            Self::Secp256k1Verify(op1, op2, op3) => {
                Self::simplify_native_3args("secp256k1-verify", op1, op2, op3, |x, y, z| Self::Secp256k1Verify(x, y, z))
            }
            Self::ContractOf(op1) => {
                Self::simplify_native_1arg("contract-of", op1, |x| Self::ContractOf(x))
            }
            Self::PrincipalOf(op1) => {
                Self::simplify_native_1arg("principal-of", op1, |x| Self::PrincipalOf(x))
            }
            Self::GetBurnBlockInfo(prop, op) => Ok(Self::GetBurnBlockInfo(prop, Box::new(op.simplify()?))),
            Self::IsOkay(op) => {
                match op.simplify()? {
                    Self::ConsError(_inner) => {
                        // this can wholesale be converted to False
                        Ok(Self::False())
                    }
                    Self::ConsOkay(_inner) => {
                        // this can wholesale be converted to True
                        Ok(Self::True())
                    }
                    op => {
                        Self::simplify_native_1arg("is-ok", Box::new(op), |x| Self::IsOkay(x))
                    }
                }
            }
            Self::IsErr(op) => {
                match op.simplify()? {
                    Self::ConsError(_inner) => {
                        // this can wholesale be converted to True
                        Ok(Self::True())
                    }
                    Self::ConsOkay(_inner) => {
                        // this can wholesale be converted to False
                        Ok(Self::False())
                    }
                    op => {
                        Self::simplify_native_1arg("is-err", Box::new(op), |x| Self::IsErr(x))
                    }
                }
            }
            Self::IsSome(op) => {
                match op.simplify()? {
                    x if x == Self::none() => {
                        // this can wholesale be converted to False
                        Ok(Self::False())
                    },
                    Self::ConsSome(_inner) => {
                        // this can wholesale be converted to True
                        Ok(Self::True())
                    }
                    op => {
                        Self::simplify_native_1arg("is-some", Box::new(op), |x| Self::IsSome(x))
                    }
                }
            }
            Self::IsNone(op) => {
                match op.simplify()? {
                    Self::ConsSome(..) => {
                        // this can wholesale be converted to False
                        Ok(Self::False())
                    }
                    op => {
                        Self::simplify_native_1arg("is-none", Box::new(op), |x| Self::IsNone(x))
                    }
                }
            }
            Self::UnwrapPanic(op) => {
                match op.simplify()? {
                    Self::ConsOkay(inner) => {
                        Ok(*inner)
                    }
                    Self::ConsSome(inner) => {
                        Ok(*inner)
                    }
                    Self::ConsError(..) => {
                        Ok(Self::Panic)
                    }
                    x if x == Self::none() => {
                        Ok(Self::Panic)
                    }
                    op => {
                        match Self::simplify_native_1arg("unwrap-panic", Box::new(op), |x| Self::UnwrapPanic(x)) {
                            Err(Error::VM(VmExecutionError::Runtime(RuntimeError::UnwrapFailure, _))) => {
                                Ok(Self::Panic)
                            }
                            Err(Error::Eval(ClarityEvalError::Vm(VmExecutionError::Runtime(RuntimeError::UnwrapFailure, _)))) => {
                                Ok(Self::Panic)
                            }
                            x => Ok(x?)
                        }
                    }
                }
            }
            Self::UnwrapErrPanic(op) => {
                match op.simplify()? {
                    Self::ConsOkay(..) => {
                        Ok(Self::Panic)
                    }
                    Self::ConsError(inner) => {
                        Ok(*inner)
                    }
                    op => {
                        match Self::simplify_native_1arg("unwrap-err-panic", Box::new(op), |x| Self::UnwrapErrPanic(x)) {
                            Err(Error::VM(VmExecutionError::Runtime(RuntimeError::UnwrapFailure, _))) => {
                                Ok(Self::Panic)
                            }
                            Err(Error::Eval(ClarityEvalError::Vm(VmExecutionError::Runtime(RuntimeError::UnwrapFailure, _)))) => {
                                Ok(Self::Panic)
                            }
                            x => Ok(x?)
                        }
                    }
                }
            }
            Self::ConsError(op) => {
                Self::simplify_native_1arg("err", op, |x| Self::ConsError(x))
            }
            Self::ConsOkay(op) => {
                Self::simplify_native_1arg("ok", op, |x| Self::ConsOkay(x))
            }
            Self::ConsSome(op) => {
                Self::simplify_native_1arg("some", op, |x| Self::ConsSome(x))
            }
            Self::GetTokenBalance(name, op) => Ok(Self::GetTokenBalance(name, Box::new(op.simplify()?))),
            Self::GetNftOwner(name, op) => Ok(Self::GetNftOwner(name, Box::new(op.simplify()?))),
            Self::TransferToken(name, op1, op2, op3) => Ok(Self::TransferToken(name, Box::new(op1.simplify()?), Box::new(op2.simplify()?), Box::new(op3.simplify()?))),
            Self::TransferNft(name, op1, op2, op3) => Ok(Self::TransferNft(name, Box::new(op1.simplify()?), Box::new(op2.simplify()?), Box::new(op3.simplify()?))),
            Self::MintToken(name, op1, op2) => Ok(Self::MintToken(name, Box::new(op1.simplify()?), Box::new(op2.simplify()?))),
            Self::MintNft(name, op1, op2) => Ok(Self::MintNft(name, Box::new(op1.simplify()?), Box::new(op2.simplify()?))),
            Self::GetTokenSupply(name) => Ok(Self::GetTokenSupply(name)),
            Self::BurnToken(name, op) => Ok(Self::BurnToken(name, Box::new(op.simplify()?))),
            Self::BurnNft(name, op1, op2) => Ok(Self::BurnNft(name, Box::new(op1.simplify()?), Box::new(op2.simplify()?))),
            Self::GetStxBalance(op) => Ok(Self::GetStxBalance(Box::new(op.simplify()?))),
            Self::StxTransfer(op1, op2, op3) => Ok(Self::StxTransfer(Box::new(op1.simplify()?), Box::new(op2.simplify()?), Box::new(op3.simplify()?))),
            Self::StxTransferMemo(op1, op2, op3, op4) => Ok(Self::StxTransferMemo(Box::new(op1.simplify()?), Box::new(op2.simplify()?), Box::new(op3.simplify()?), Box::new(op4.simplify()?))),
            Self::StxBurn(op1) => Ok(Self::StxBurn(Box::new(op1.simplify()?))),
            Self::StxGetAccount(op1) => Ok(Self::StxGetAccount(Box::new(op1.simplify()?))),
            Self::BitwiseAnd(ops) => {
                Self::simplify_assoc_variadic(
                    "bit-and",
                    ops,
                    |op| *op == Self::Constant(Value::Int(i128::MIN)) || *op == Self::Constant(Value::UInt(u128::MAX)),
                    |op| if let Self::BitwiseAnd(inner) = op { Some(inner) } else { None },
                    |new_ops| Self::BitwiseAnd(new_ops)
                )
            }
            Self::BitwiseOr(ops) => {
                Self::simplify_assoc_variadic(
                    "bit-or",
                    ops,
                    |op| *op == Self::Constant(Value::Int(0)) || *op == Self::Constant(Value::UInt(0)),
                    |op| if let Self::BitwiseOr(inner) = op { Some(inner) } else { None },
                    |new_ops| Self::BitwiseOr(new_ops)
                )
            }
            Self::BitwiseXor(ops) => {
                Self::simplify_assoc_variadic(
                    "bit-xor",
                    ops,
                    |op| *op == Self::Constant(Value::Int(0)) || *op == Self::Constant(Value::UInt(0)),
                    |op| if let Self::BitwiseXor(inner) = op { Some(inner) } else { None },
                    |new_ops| Self::BitwiseXor(new_ops)
                )
            }
            Self::BitwiseNot(op) => {
                Self::simplify_native_1arg("bit-not", op, |x| Self::BitwiseNot(x))
            }
            Self::BitwiseLShift(op1, op2) => {
                Self::simplify_native_2args("bit-shift-left", op1, op2, |x, y| Self::BitwiseLShift(x, y))
            }
            Self::BitwiseRShift(op1, op2) => {
                Self::simplify_native_2args("bit-shift-right", op1, op2, |x, y| Self::BitwiseRShift(x, y))
            }
            Self::Slice(op1, op2, op3) => {
                Self::simplify_native_3args("slice?", op1, op2, op3, |x, y, z| Self::Slice(x, y, z))
            }
            Self::ToConsensusBuff(op) => {
                Self::simplify_native_1arg("to-consensus-buff?", op, |x| Self::ToConsensusBuff(x))
            }
            Self::FromConsensusBuff(ts, op) => {
                match op.simplify()? {
                    Self::Constant(v) => {
                        let v = Self::context_free_clarity_eval_mainnet(vec![
                            SymbolicExpression::atom("from-consensus-buff?".try_into()?),
                            Self::type_signature_to_symbolic_expression(ts),
                            SymbolicExpression::literal_value(v)
                        ])?
                        .ok_or_else(|| Error::Bug("Clarity VM evaluated to None".into()))?;
                        Ok(Self::Constant(v))
                    }
                    x => Ok(Self::FromConsensusBuff(ts, Box::new(x)))
                }
            }
            Self::ReplaceAt(op1, op2, op3) => {
                Self::simplify_native_3args("replace-at?", op1, op2, op3, |x, y, z| Self::ReplaceAt(x, y, z))
            }
            Self::GetStacksBlockInfo(name, op) => Ok(Self::GetStacksBlockInfo(name, Box::new(op.simplify()?))),
            Self::GetTenureInfo(name, op) => Ok(Self::GetTenureInfo(name, Box::new(op.simplify()?))),
            Self::ContractHash(op) => Ok(Self::ContractHash(Box::new(op.simplify()?))),
            Self::ToAscii(op) => {
                Self::simplify_native_1arg("to-ascii?", op, |x| Self::ToAscii(x))
            }
            Self::RestrictAssets(op1, op2, op3) => Ok(Self::RestrictAssets(Box::new(op1.simplify()?), Box::new(op2.simplify()?), Box::new(op3.simplify()?))),
            Self::AsContractSafe(op1, op2) => Ok(Self::AsContractSafe(Box::new(op1.simplify()?), Box::new(op2.simplify()?))),
            Self::AllowanceWithStx(op) => Ok(Self::AllowanceWithStx(Box::new(op.simplify()?))),
            Self::AllowanceWithFt(op1, name, op2) => Ok(Self::AllowanceWithFt(Box::new(op1.simplify()?), name, Box::new(op2.simplify()?))),
            Self::AllowanceWithNft(op1, name, op2) => Ok(Self::AllowanceWithNft(Box::new(op1.simplify()?), name, Box::new(op2.simplify()?))),
            Self::AllowanceWithStacking(op) => Ok(Self::AllowanceWithStacking(Box::new(op.simplify()?))),
            Self::AllowanceAll => Ok(Self::AllowanceAll),
            Self::Secp256r1Verify(op1, op2, op3) => {
                Self::simplify_native_3args("secp256r1-verify?", op1, op2, op3, |x, y, z| Self::Secp256r1Verify(x, y, z))
            }
            Self::VerifyMerkleProof(op1, op2, op3, op4, op5) => {
                Self::simplify_native_5args("verify-merkle-proof", op1, op2, op3, op4, op5, |x, y, z, w, v| Self::VerifyMerkleProof(x, y, z, w, v))
            }
            Self::GetBitcoinTxOutput(op1, op2) => Self::simplify_native_2args("get-bitcoin-tx-output?", op1, op2, |x, y| Self::GetBitcoinTxOutput(x, y)),
            Self::Panic => Ok(Self::Panic),
            Self::FunctionCall(name, args) => {
                let mut simplified_args = vec![];
                for arg in args.into_iter() {
                    let arg = arg.simplify()?;
                    simplified_args.push(Box::new(arg));
                }
                Ok(Self::FunctionCall(name, simplified_args))
            }
        }
    }

    /// Apply tactics to simplify this operation
    pub fn simplify(self) -> Result<Self, Error> {
        let mut cur = self;
        if is_simplified(&cur) {
            return Ok(cur);
        }

        let old = cur.clone();
        loop {
            trace!("simplify: {cur}");
            let new = Self::inner_simplify(cur.clone())?;
            if new == cur {
                break;
            }
            cur = new;
        }

        set_simplified(cur.clone());
        trace!("simplified({}): {old} ==> {cur}", old == cur);
        Ok(cur)
    }

    fn bind_symbol_in_list(ops: Vec<Box<SymOp>>, sym_id: SymId, symop: SymOp) -> Vec<Box<SymOp>> {
        let mut new = vec![];
        for op in ops.into_iter() {
            let new_op = op.bind_symbol(sym_id.clone(), symop.clone());
            new.push(new_op);
        }
        new
    }

    /// Bind a formula to a symbol in this symop
    pub fn bind_symbol(self, sym_id: SymId, symop: SymOp) -> Box<SymOp> {
        trace!("Bind symbol '{sym_id}' to {symop} in {self}");
        let op = match self {
            Self::Constant(v) => Self::Constant(v),
            Self::Variable(v) => {
                if v.id() != sym_id.as_str() {
                    Self::Variable(v)
                }
                else {
                    symop
                }
            }
            Self::LoadedDataVariable(name, op) => Self::LoadedDataVariable(name, op.bind_symbol(sym_id, symop)),
            Self::Add(ops) => Self::Add(Self::bind_symbol_in_list(ops, sym_id, symop)),
            Self::Subtract(ops) => Self::Subtract(Self::bind_symbol_in_list(ops, sym_id, symop)),
            Self::Multiply(ops) => Self::Multiply(Self::bind_symbol_in_list(ops, sym_id, symop)),
            Self::Divide(ops) => Self::Divide(Self::bind_symbol_in_list(ops, sym_id, symop)),
            Self::ToInt(op) => Self::ToInt(op.bind_symbol(sym_id, symop)),
            Self::ToUInt(op) => Self::ToUInt(op.bind_symbol(sym_id, symop)),
            Self::Modulo(op1, op2) => Self::Modulo(op1.bind_symbol(sym_id.clone(), symop.clone()), op2.bind_symbol(sym_id.clone(), symop.clone())),
            Self::Power(base_op, exp_op) => Self::Power(base_op.bind_symbol(sym_id.clone(), symop.clone()), exp_op.bind_symbol(sym_id.clone(), symop.clone())),
            Self::Sqrti(op) => Self::Sqrti(op.bind_symbol(sym_id, symop)),
            Self::Log2(op) => Self::Log2(op.bind_symbol(sym_id, symop)),
            Self::And(ops) => Self::And(Self::bind_symbol_in_list(ops, sym_id, symop)),
            Self::Or(ops) => Self::Or(Self::bind_symbol_in_list(ops, sym_id, symop)),
            Self::Not(op) => Self::Not(op.bind_symbol(sym_id, symop)),
            Self::Greater(x, y) => Self::Greater(x.bind_symbol(sym_id.clone(), symop.clone()), y.bind_symbol(sym_id.clone(), symop.clone())),
            Self::Geq(x, y) => Self::Geq(x.bind_symbol(sym_id.clone(), symop.clone()), y.bind_symbol(sym_id.clone(), symop.clone())),
            Self::Equals(ops) => Self::Equals(Self::bind_symbol_in_list(ops, sym_id, symop)),
            Self::Leq(x, y) => Self::Leq(x.bind_symbol(sym_id.clone(), symop.clone()), y.bind_symbol(sym_id.clone(), symop.clone())),
            Self::Less(x, y) => Self::Less(x.bind_symbol(sym_id.clone(), symop.clone()), y.bind_symbol(sym_id.clone(), symop.clone())),
            Self::Append(list_op, val_op) => Self::Append(list_op.bind_symbol(sym_id.clone(), symop.clone()), val_op.bind_symbol(sym_id.clone(), symop.clone())),
            Self::Concat(ops) => Self::Concat(Self::bind_symbol_in_list(ops, sym_id, symop)),
            Self::AsMaxLen(op1, op2) => Self::AsMaxLen(op1.bind_symbol(sym_id.clone(), symop.clone()), op2.bind_symbol(sym_id.clone(), symop.clone())),
            Self::Len(op) => Self::Len(op.bind_symbol(sym_id, symop)),
            Self::ElementAt(op1, op2) => Self::ElementAt(op1.bind_symbol(sym_id.clone(), symop.clone()), op2.bind_symbol(sym_id.clone(), symop.clone())),
            Self::IndexOf(op1, op2) => Self::IndexOf(op1.bind_symbol(sym_id.clone(), symop.clone()), op2.bind_symbol(sym_id.clone(), symop.clone())),
            Self::BuffToIntLe(op) => Self::BuffToIntLe(op.bind_symbol(sym_id, symop)),
            Self::BuffToUIntLe(op) => Self::BuffToUIntLe(op.bind_symbol(sym_id, symop)),
            Self::BuffToIntBe(op) => Self::BuffToIntBe(op.bind_symbol(sym_id, symop)),
            Self::BuffToUIntBe(op) => Self::BuffToUIntBe(op.bind_symbol(sym_id, symop)),
            Self::IsStandard(op) => Self::IsStandard(op.bind_symbol(sym_id, symop)),
            Self::PrincipalDestruct(op) => Self::PrincipalDestruct(op.bind_symbol(sym_id, symop)),
            Self::PrincipalConstruct(op1, op2, op3_opt) => {
                let new_op3_opt = if let Some(op3) = op3_opt {
                    Some(op3.bind_symbol(sym_id.clone(), symop.clone()))
                }
                else {
                    None
                };
                Self::PrincipalConstruct(op1.bind_symbol(sym_id.clone(), symop.clone()), op2.bind_symbol(sym_id.clone(), symop.clone()), new_op3_opt)
            },
            Self::StringToInt(op) => Self::StringToInt(op.bind_symbol(sym_id, symop)),
            Self::StringToUInt(op) => Self::StringToUInt(op.bind_symbol(sym_id, symop)),
            Self::IntToAscii(op) => Self::IntToAscii(op.bind_symbol(sym_id, symop)),
            Self::IntToUtf8(op) => Self::IntToUtf8(op.bind_symbol(sym_id, symop)),
            Self::ListCons(ops) => Self::ListCons(Self::bind_symbol_in_list(ops, sym_id, symop)),
            Self::FetchVar(name) => Self::FetchVar(name),
            Self::SetVar(name, op) => Self::SetVar(name, op.bind_symbol(sym_id, symop)),
            Self::FetchEntry(name, op) => Self::FetchEntry(name, op.bind_symbol(sym_id, symop)),
            Self::LoadedMapEntry(name, key_op, value_op_opt) => {
                let new_value_op_opt = if let Some(op) = value_op_opt {
                    Some(op.bind_symbol(sym_id.clone(), symop.clone()))
                }
                else {
                    None
                };
                Self::LoadedMapEntry(name, key_op.bind_symbol(sym_id, symop), new_value_op_opt)
            }
            Self::SetEntry(name, op1, op2) => Self::SetEntry(name, op1.bind_symbol(sym_id.clone(), symop.clone()), op2.bind_symbol(sym_id.clone(), symop.clone())),
            Self::InsertEntry(name, op1, op2) => Self::InsertEntry(name, op1.bind_symbol(sym_id.clone(), symop.clone()), op2.bind_symbol(sym_id.clone(), symop.clone())),
            Self::DeleteEntry(name, op) => Self::DeleteEntry(name, op.bind_symbol(sym_id, symop)),
            Self::TupleCons(fields) => {
                let mut new_fields = vec![];
                for (key, value) in fields.into_iter() {
                    let new_value = value.bind_symbol(sym_id.clone(), symop.clone());
                    new_fields.push((key, new_value));
                }
                Self::TupleCons(new_fields)
            }
            Self::TupleGet(name, op) => Self::TupleGet(name, op.bind_symbol(sym_id, symop)),
            Self::TupleMerge(op1, op2) => Self::TupleMerge(op1.bind_symbol(sym_id.clone(), symop.clone()), op2.bind_symbol(sym_id.clone(), symop.clone())),
            Self::Hash160(op) => Self::Hash160(op.bind_symbol(sym_id, symop)),
            Self::Sha256(op) => Self::Sha256(op.bind_symbol(sym_id, symop)),
            Self::Sha512(op) => Self::Sha512(op.bind_symbol(sym_id, symop)),
            Self::Sha512Trunc256(op) => Self::Sha512Trunc256(op.bind_symbol(sym_id, symop)),
            Self::Keccak256(op) => Self::Keccak256(op.bind_symbol(sym_id, symop)),
            Self::Secp256k1Recover(op1, op2) => Self::Secp256k1Recover(op1.bind_symbol(sym_id.clone(), symop.clone()), op2.bind_symbol(sym_id.clone(), symop.clone())),
            Self::Secp256k1Verify(op1, op2, op3) => Self::Secp256k1Verify(op1.bind_symbol(sym_id.clone(), symop.clone()), op2.bind_symbol(sym_id.clone(), symop.clone()), op3.bind_symbol(sym_id.clone(), symop.clone())),
            Self::ContractOf(op1) => Self::ContractOf(op1.bind_symbol(sym_id, symop)),
            Self::PrincipalOf(op1) => Self::PrincipalOf(op1.bind_symbol(sym_id, symop)),
            Self::GetBurnBlockInfo(prop, op) => Self::GetBurnBlockInfo(prop, op.bind_symbol(sym_id, symop)),
            Self::IsOkay(op) => Self::IsOkay(op.bind_symbol(sym_id, symop)),
            Self::IsErr(op) => Self::IsErr(op.bind_symbol(sym_id, symop)),
            Self::IsSome(op) => Self::IsSome(op.bind_symbol(sym_id, symop)),
            Self::IsNone(op) => Self::IsNone(op.bind_symbol(sym_id, symop)),
            Self::UnwrapPanic(op) => Self::UnwrapPanic(op.bind_symbol(sym_id, symop)),
            Self::UnwrapErrPanic(op) => Self::UnwrapErrPanic(op.bind_symbol(sym_id, symop)),
            Self::ConsError(op) => Self::ConsError(op.bind_symbol(sym_id, symop)),
            Self::ConsOkay(op) => Self::ConsOkay(op.bind_symbol(sym_id, symop)),
            Self::ConsSome(op) => Self::ConsSome(op.bind_symbol(sym_id, symop)),
            Self::GetTokenBalance(name, op) => Self::GetTokenBalance(name, op.bind_symbol(sym_id, symop)),
            Self::GetNftOwner(name, op) => Self::GetNftOwner(name, op.bind_symbol(sym_id, symop)),
            Self::TransferToken(name, op1, op2, op3) => Self::TransferToken(name, op1.bind_symbol(sym_id.clone(), symop.clone()), op2.bind_symbol(sym_id.clone(), symop.clone()), op3.bind_symbol(sym_id.clone(), symop.clone())),
            Self::TransferNft(name, op1, op2, op3) => Self::TransferNft(name, op1.bind_symbol(sym_id.clone(), symop.clone()), op2.bind_symbol(sym_id.clone(), symop.clone()), op3.bind_symbol(sym_id.clone(), symop.clone())),
            Self::MintToken(name, op1, op2) => Self::MintToken(name, op1.bind_symbol(sym_id.clone(), symop.clone()), op2.bind_symbol(sym_id.clone(), symop.clone())),
            Self::MintNft(name, op1, op2) => Self::MintNft(name, op1.bind_symbol(sym_id.clone(), symop.clone()), op2.bind_symbol(sym_id.clone(), symop.clone())),
            Self::GetTokenSupply(name) => Self::GetTokenSupply(name),
            Self::BurnToken(name, op) => Self::BurnToken(name, op.bind_symbol(sym_id, symop)),
            Self::BurnNft(name, op1, op2) => Self::BurnNft(name, op1.bind_symbol(sym_id.clone(), symop.clone()), op2.bind_symbol(sym_id.clone(), symop.clone())),
            Self::GetStxBalance(op) => Self::GetStxBalance(op.bind_symbol(sym_id, symop)),
            Self::StxTransfer(op1, op2, op3) => Self::StxTransfer(op1.bind_symbol(sym_id.clone(), symop.clone()), op2.bind_symbol(sym_id.clone(), symop.clone()), op3.bind_symbol(sym_id.clone(), symop.clone())),
            Self::StxTransferMemo(op1, op2, op3, op4) => Self::StxTransferMemo(op1.bind_symbol(sym_id.clone(), symop.clone()), op2.bind_symbol(sym_id.clone(), symop.clone()), op3.bind_symbol(sym_id.clone(), symop.clone()), op4.bind_symbol(sym_id.clone(), symop.clone())),
            Self::StxBurn(op1) => Self::StxBurn(op1.bind_symbol(sym_id, symop)),
            Self::StxGetAccount(op1) => Self::StxGetAccount(op1.bind_symbol(sym_id, symop)),
            Self::BitwiseAnd(ops) => Self::BitwiseAnd(Self::bind_symbol_in_list(ops, sym_id, symop)),
            Self::BitwiseOr(ops) => Self::BitwiseOr(Self::bind_symbol_in_list(ops, sym_id, symop)),
            Self::BitwiseXor(ops) => Self::BitwiseXor(Self::bind_symbol_in_list(ops, sym_id, symop)),
            Self::BitwiseNot(op) => Self::BitwiseNot(op.bind_symbol(sym_id, symop)),
            Self::BitwiseLShift(op1, op2) => Self::BitwiseLShift(op1.bind_symbol(sym_id.clone(), symop.clone()), op2.bind_symbol(sym_id.clone(), symop.clone())),
            Self::BitwiseRShift(op1, op2) => Self::BitwiseRShift(op1.bind_symbol(sym_id.clone(), symop.clone()), op2.bind_symbol(sym_id.clone(), symop.clone())),
            Self::Slice(op1, op2, op3) => Self::Slice(op1.bind_symbol(sym_id.clone(), symop.clone()), op2.bind_symbol(sym_id.clone(), symop.clone()), op3.bind_symbol(sym_id.clone(), symop.clone())),
            Self::ToConsensusBuff(op) => Self::ToConsensusBuff(op.bind_symbol(sym_id, symop)),
            Self::FromConsensusBuff(ts, op) => Self::FromConsensusBuff(ts, op.bind_symbol(sym_id, symop)),
            Self::ReplaceAt(op1, op2, op3) => Self::ReplaceAt(op1.bind_symbol(sym_id.clone(), symop.clone()), op2.bind_symbol(sym_id.clone(), symop.clone()), op3.bind_symbol(sym_id.clone(), symop.clone())),
            Self::GetStacksBlockInfo(name, op) => Self::GetStacksBlockInfo(name, op.bind_symbol(sym_id, symop)),
            Self::GetTenureInfo(name, op) => Self::GetTenureInfo(name, op.bind_symbol(sym_id, symop)),
            Self::ContractHash(op) => Self::ContractHash(op.bind_symbol(sym_id, symop)),
            Self::ToAscii(op) => Self::ToAscii(op.bind_symbol(sym_id, symop)),
            Self::RestrictAssets(op1, op2, op3) => Self::RestrictAssets(op1.bind_symbol(sym_id.clone(), symop.clone()), op2.bind_symbol(sym_id.clone(), symop.clone()), op3.bind_symbol(sym_id.clone(), symop.clone())),
            Self::AsContractSafe(op1, op2) => Self::AsContractSafe(op1.bind_symbol(sym_id.clone(), symop.clone()), op2.bind_symbol(sym_id.clone(), symop.clone())),
            Self::AllowanceWithStx(op) => Self::AllowanceWithStx(op.bind_symbol(sym_id, symop)),
            Self::AllowanceWithFt(op1, name, op2) => Self::AllowanceWithFt(op1.bind_symbol(sym_id.clone(), symop.clone()), name, op2.bind_symbol(sym_id.clone(), symop.clone())),
            Self::AllowanceWithNft(op1, name, op2) => Self::AllowanceWithNft(op1.bind_symbol(sym_id.clone(), symop.clone()), name, op2.bind_symbol(sym_id.clone(), symop.clone())),
            Self::AllowanceWithStacking(op) => Self::AllowanceWithStacking(op.bind_symbol(sym_id, symop)),
            Self::AllowanceAll => Self::AllowanceAll,
            Self::Secp256r1Verify(op1, op2, op3) => Self::Secp256r1Verify(op1.bind_symbol(sym_id.clone(), symop.clone()), op2.bind_symbol(sym_id.clone(), symop.clone()), op3.bind_symbol(sym_id.clone(), symop.clone())),
            Self::VerifyMerkleProof(op1, op2, op3, op4, op5) => Self::VerifyMerkleProof(
                op1.bind_symbol(sym_id.clone(), symop.clone()),
                op2.bind_symbol(sym_id.clone(), symop.clone()),
                op3.bind_symbol(sym_id.clone(), symop.clone()),
                op4.bind_symbol(sym_id.clone(), symop.clone()),
                op5.bind_symbol(sym_id.clone(), symop.clone()),
            ),
            Self::GetBitcoinTxOutput(op1, op2) => Self::GetBitcoinTxOutput(
                op1.bind_symbol(sym_id.clone(), symop.clone()),
                op2.bind_symbol(sym_id.clone(), symop.clone()),
            ),
            Self::Panic => Self::Panic,
            Self::FunctionCall(name, args) => {
                let mut new_args = vec![];
                for arg in args.into_iter() {
                    let new_arg = arg.bind_symbol(sym_id.clone(), symop.clone());
                    new_args.push(new_arg);
                }
                Self::FunctionCall(name, new_args)
            }
        };
        Box::new(op)
    }
}

/// Predicates over operations over symbols.
/// not all relations are well-defined here; we rely on the Clarity type-checker for this.
#[derive(Debug, Clone, Hash, Eq)]
pub enum Predicate {
    True,
    False,
    Identity(SymOp),
    And(Vec<Box<Predicate>>),
    Or(Vec<Box<Predicate>>),
    Not(Box<Predicate>),
    Equals(Vec<SymOp>),
    Geq(SymOp, SymOp),
    Leq(SymOp, SymOp),
    Less(SymOp, SymOp),
    Greater(SymOp, SymOp),
    IsSome(SymOp),
    IsNone(SymOp),
    IsOkay(SymOp),
    IsErr(SymOp),
}

impl PartialEq for Predicate {
    fn eq(&self, other: &Self) -> bool {
        let self_as_symop = self.clone().as_symop();
        let other_as_symop = other.clone().as_symop();
        self_as_symop.eq(&other_as_symop)
    }
}

impl Predicate {
    fn inner_format_prefix(func: &str, list: &[Box<Predicate>], sorted: bool, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let mut pred_strs : Vec<_> = list
            .iter()
            .map(|pred| format!("{}", pred))
            .collect();

        if sorted {
            pred_strs.sort();
        }

        let pred_str = pred_strs.join(" ");

        write!(f, "({func} {pred_str})")
    }

    fn format_prefix(func: &str, list: &[Box<Predicate>], f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        Self::inner_format_prefix(func, list, false, f)
    }

    fn format_prefix_sorted(func: &str, list: &[Box<Predicate>], f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        Self::inner_format_prefix(func, list, true, f)
    }
    
    pub fn to_pretty_string(&self, depth: usize) -> String {
        self.clone().as_symop().to_pretty_string(depth)
    }
}


impl fmt::Display for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::True => write!(f, "true"),
            Self::False => write!(f, "false"),
            Self::Identity(symop) => write!(f, "{}", symop),
            Self::And(preds) => Self::format_prefix_sorted("and", preds, f),
            Self::Or(preds) => Self::format_prefix_sorted("or", preds, f),
            Self::Not(pred) => write!(f, "(not {pred})"),
            Self::Equals(symops) => {
                let mut opstrs : Vec<_> = symops
                    .iter()
                    .map(|s| format!("{}", s))
                    .collect();

                opstrs.sort();
                let opstr = opstrs.join(" ");
                write!(f, "(is-eq {})", opstr)
            }
            Self::Geq(symop1, symop2) => write!(f, "(>= {symop1} {symop2})"),
            Self::Leq(symop1, symop2) => write!(f, "(<= {symop1} {symop2})"),
            Self::Less(symop1, symop2) => write!(f, "(< {symop1} {symop2})"),
            Self::Greater(symop1, symop2) => write!(f, "(> {symop1} {symop2})"),
            Self::IsSome(symop) => write!(f, "(is-some {symop})"),
            Self::IsNone(symop) => write!(f, "(is-none {symop})"),
            Self::IsOkay(symop) => write!(f, "(is-ok {symop})"),
            Self::IsErr(symop) => write!(f, "(is-err {symop})"),
        }
    }
}

impl Predicate {
    fn merge_and1(mut ps1: Vec<Box<Predicate>>, p: Box<Predicate>) -> Predicate {
        if ps1.iter().find(|x| ***x == *p).is_none() {
            // check for obvious contradictions
            let contra = p.clone().not();
            if ps1.iter().find(|x| ***x == contra).is_some() {
                return Self::False;
            }
            ps1.push(p);
        }
        Self::And(ps1)
    }

    fn merge_and(p1: Predicate, p2: Predicate) -> Self {
        match (p1, p2) {
            (Self::True, p2) => p2,
            (p1, Self::True) => p1,
            (Self::False, _p2) => Self::False,
            (_p1, Self::False) => Self::False,
            (Self::And(mut ps1), Self::And(ps2)) => {
                for p in ps2 {
                    ps1 = match Self::merge_and1(ps1, p) {
                        Self::And(ps) => ps,
                        x => {
                            return x;
                        }
                    };
                }
                Self::And(ps1)
            },
            (Self::And(ps), x) => {
                Self::merge_and1(ps, Box::new(x))
            },
            (x, Self::And(ps)) => {
                Self::merge_and1(ps, Box::new(x))
            },
            (x, y) => {
                let ps = if x == y {
                    return x;
                }
                else if x.clone().not() == y || y.clone().not() == x {
                    return Self::False;
                }
                else {
                    vec![Box::new(x), Box::new(y)]
                };
                Self::And(ps)
            }
        }
    }

    pub fn and(self, p: Predicate) -> Self {
        Self::merge_and(self, p)
    }
    
    fn merge_or1(mut ps1: Vec<Box<Predicate>>, p: Box<Predicate>) -> Predicate {
        if ps1.iter().find(|x| ***x == *p).is_none() {
            // check for obvious contradictions
            let contra = p.clone().not();
            if ps1.iter().find(|x| ***x == contra).is_some() {
                return Self::True;
            }
            ps1.push(p);
        }
        Self::Or(ps1)
    }

    fn merge_or(p1: Predicate, p2: Predicate) -> Self {
        match (p1, p2) {
            (Self::True, _p2) => Self::True,
            (_p1, Self::True) => Self::True,
            (Self::False, p2) => p2,
            (p1, Self::False) => p1,
            (Self::Or(mut ps1), Self::Or(ps2)) => {
                for p in ps2 {
                    ps1 = match Self::merge_or1(ps1, p) {
                        Self::Or(ps) => ps,
                        x => {
                            return x;
                        }
                    };
                }
                Self::Or(ps1)
            },
            (Self::Or(ps), x) => {
                Self::merge_or1(ps, Box::new(x))
            },
            (x, Self::Or(ps)) => {
                Self::merge_or1(ps, Box::new(x))
            },
            (x, y) => {
                let ps = if x == y {
                    return x;
                }
                else if x.clone().not() == y || y.clone().not() == x {
                    return Self::True;
                }
                else {
                    vec![Box::new(x), Box::new(y)]
                };
                Self::Or(ps)
            }
        }
    }

    pub fn or(self, p: Predicate) -> Self {
        Self::merge_or(self, p)
    }

    pub fn not(self) -> Self {
        match self {
            Self::True => Self::False,
            Self::False => Self::True,
            Self::Not(x) => *x,
            x => Self::Not(Box::new(x))
        }
    }
    
    pub fn as_symop(self) -> SymOp {
        match self {
            Self::True => SymOp::True(),
            Self::False => SymOp::False(),
            Self::Identity(op) => op,
            Self::And(preds) => SymOp::And(preds.into_iter().map(|p| Box::new(p.as_symop())).collect()),
            Self::Or(preds) => SymOp::Or(preds.into_iter().map(|p| Box::new(p.as_symop())).collect()),
            Self::Not(p) => SymOp::Not(Box::new(p.as_symop())),
            Self::Equals(ops) => SymOp::Equals(ops.into_iter().map(|p| Box::new(p)).collect()),
            Self::Geq(op1, op2) => SymOp::Geq(Box::new(op1), Box::new(op2)),
            Self::Leq(op1, op2) => SymOp::Leq(Box::new(op1), Box::new(op2)),
            Self::Less(op1, op2) => SymOp::Less(Box::new(op1), Box::new(op2)),
            Self::Greater(op1, op2) => SymOp::Greater(Box::new(op1), Box::new(op2)),
            Self::IsSome(op) => SymOp::IsSome(Box::new(op)),
            Self::IsNone(op) => SymOp::IsNone(Box::new(op)),
            Self::IsOkay(op) => SymOp::IsOkay(Box::new(op)),
            Self::IsErr(op) => SymOp::IsErr(Box::new(op)),
        }
    }

    /// Try to evaluate the predicate.
    /// Only works if each contained SymOp is a Constant
    fn try_evaluate(p: Predicate) -> Result<Predicate, Error> {
        match p {
            Self::True => Ok(Self::True),
            Self::False => Ok(Self::False),
            Self::Identity(mut x) => {
                loop {
                    let new_x = x.clone().simplify()?;
                    if new_x == x {
                        return Ok(Self::Identity(new_x));
                    }
                    x = new_x;
                }
            },
            x => x.as_symop().simplify()?.try_as_predicate()
        }
    }

    /// Apply tactics to simplify the predicate to a tautology or contradiction
    pub fn simplify(self) -> Result<Self, Error> {
        let mut cur = self;
        loop {
            let ret = Self::try_evaluate(cur.clone())?;
            if ret == cur {
                return Ok(ret);
            }
            cur = ret;
        }
    }
}

/// A trace of a sequence of continuations
#[derive(Clone, Debug)]
pub struct TraceItem {
    pub depth: usize,
    pub identifier: String,
    pub contract_id: QualifiedContractIdentifier,
    pub start_line: u32,
    pub function: String,
    pub cont_id: u64,
    pub bound_formulae: HashMap<SymId, SymOp>,
    pub dropped_formulae: Vec<SymId>,
    pub predicate: Predicate
}

impl fmt::Display for TraceItem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let bound_formulae_parts : Vec<_> = self.bound_formulae
            .iter()
            .map(|(sym_id, symop)| format!("({sym_id} {symop})"))
            .collect();

        let bound_formulae_str = bound_formulae_parts.join(" ");

        let unbound_formulae_parts : Vec<_> = self.dropped_formulae
            .iter()
            .map(|sym_id| format!("{sym_id}"))
            .collect();

        let unbound_formulae_str = if unbound_formulae_parts.len() > 0 {
            format!("unbound: {}", unbound_formulae_parts.join(" "))
        }
        else {
            "".to_string()
        };
        write!(f, "{}: {} {}.{}:{} ({}) {} {}", self.depth, self.cont_id, &self.contract_id, &self.function, self.start_line, &self.identifier, &bound_formulae_str, &unbound_formulae_str)
    }
}

pub struct Trace(Vec<TraceItem>);

impl fmt::Display for Trace {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        for t in self.0.iter() {
            writeln!(f, "{}", t)?;
        }
        Ok(())
    }
}

static CONT_ID_CTR : AtomicU64 = AtomicU64::new(1);
fn next_cont_id() -> u64 {
    let next_id = CONT_ID_CTR.fetch_add(1, Ordering::SeqCst);
    next_id
}

static LAST_CONT_ID_CTR : AtomicU64 = AtomicU64::new(0);
fn set_last_cont_id(id: u64) {
    LAST_CONT_ID_CTR.store(id, Ordering::SeqCst);
}

fn last_cont_id() -> u64 {
    let id = LAST_CONT_ID_CTR.load(Ordering::SeqCst);
    id
}

static SIMPLIFIED : LazyLock<Mutex<HashSet<SymOp>>> = LazyLock::new(|| Mutex::new(HashSet::new()));
fn is_simplified(op: &SymOp) -> bool {
    SIMPLIFIED.lock().expect("infallible").contains(op)
}

fn set_simplified(op: SymOp) {
    SIMPLIFIED.lock().expect("infallible").insert(op);
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct VarAccess {
    pub name: FullName,
    pub line: u32
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MapAccess {
    pub name: FullName,
    pub key: SymOp,
    pub line: u32
}

#[derive(Clone, Debug, PartialEq)]
pub struct ContinuationAccessSnapshot {
    map_accesses: HashSet<MapAccess>,
    var_accesses: HashSet<VarAccess>,
    parent: Option<Rc<Continuation>>,
    caller: Option<Rc<Continuation>>,
    panicked: bool
}

/// A symbolic continuation
#[derive(Clone, Debug, PartialEq)]
pub struct Continuation {
    /// internal identifier to ensure uniqueness
    pub id: u64,
    /// Path to the item in the contract being evaluated
    function_path: Option<String>,
    /// line in the source code
    current_line: Option<u32>,
    /// currently-explored function
    current_function: Option<String>,
    /// Bindings between symbols and their evaluated formulae
    bound_formulae: HashMap<SymId, SymOp>,
    /// Bindings dropped in this continuation
    dropped_formulae: Vec<SymId>,
    /// The symbolic condition under which this continuation is reachable
    pub predicate: Predicate,
    /// The computed symbolic expression of this continuation
    pub final_formula: SymOp,
    /// The tx-sender variable, if different from the parent continuation
    tx_sender: Option<SymOp>,
    /// The contract-caller variable, if different from the parent continuation
    contract_caller: Option<SymOp>,
    /// The tx-sponsor variable
    tx_sponsor: Option<SymOp>,
    /// The current contract, if different from the parent continuation.
    /// Unlike tx-sender, contract-caller, and tx-sponsor?, current-contract is always bound
    current_contract: Option<PrincipalData>,
    /// Parent continuation (None means this is the "root" continuation)
    parent: Option<Rc<Continuation>>,
    /// Parent caller continuation (none means this is the "root" continuation).
    /// This is the continuation of the ongoing function being evaluated.
    /// Used for handling early-return.
    caller: Option<Rc<Continuation>>,
    /// data-var formulae prior to evaluation
    pub pre_var_state: HashMap<FullName, SymOp>,
    /// data-var formulae after evaluation
    pub var_state: HashMap<FullName, SymOp>,
    /// map data that was read (but not written), and thus serves as input
    pub pre_map_state: HashMap<FullName, HashSet<SymOp>>,
    /// current view of each map
    pub map_state: HashMap<FullName, HashMap<SymOp, SymOp>>,
    pub map_tombstones: HashMap<FullName, HashSet<SymOp>>,
    /// map accesses (but not values)
    pub map_accesses: HashSet<MapAccess>,
    /// var accesses (but not values)
    pub var_accesses: HashSet<VarAccess>,
    /// map state that could be accessed (i.e. is reachable by) a function that was not explored in
    /// this continuation's evaluation
    pub reachable_map_reads: HashSet<FullName>,
    /// map state that could be written by a function that was not explored in
    /// this continuation's evaluation
    pub reachable_map_writes: HashSet<FullName>,
    /// var state that could be accessed (i.e. is reachable by) a function that was not explored in
    /// this continuation's evaluation
    pub reachable_var_reads: HashSet<FullName>,
    /// var state that could be written (i.e. is reachable by) a function that was not explored in
    /// this continuation's evaluation
    pub reachable_var_writes: HashSet<FullName>,
    /// whether or not this continuation panicked
    pub panicking: bool,
    /// whether or not this continuation represents an early return
    pub early_return: bool,
}

impl fmt::Display for Continuation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        writeln!(f, "ID:               {}", &self.id)?;
        writeln!(f, "Path:             {}", &self.function_path.as_ref().unwrap_or(&"".to_string()))?;
        writeln!(f, "Panicked:         {}", &self.panicking)?;
        writeln!(f, "Early return:     {}", &self.early_return)?;
        writeln!(f, "Caller:           {}", &self.get_caller_name())?;
        writeln!(f, "tx-sender:        {}", &self.get_tx_sender())?;
        writeln!(f, "contract-caller:  {}", &self.get_contract_caller())?;
        writeln!(f, "current-contract: {}", &self.get_current_contract())?;
        writeln!(f, "Formula:          {}", &self.final_formula)?;
        write!(f, "Predicate: \n{}", &self.predicate.clone().as_symop().to_pretty_string(1))?;

        let mut syms : Vec<_> = self.bound_formulae.keys().collect();

        if syms.len() > 0 {
            writeln!(f, "Bound formulae:")?;
            syms.sort();
            for sym in syms.iter() {
                let formula = self.bound_formulae.get(sym).expect("infallible");
                writeln!(f, "   {} = {}", sym, formula)?;
            }
        }

        writeln!(f, "Input vars explored:")?;
        if self.pre_var_state.len() > 0 {
            let mut keys : Vec<_> = self.pre_var_state.keys().collect();
            keys.sort();
            for key in keys {
                let var_val = self.pre_var_state.get(&key).expect("unreachable");
                writeln!(f, "   (define-data-var {key} {var_val})")?;
            }
        }
        else {
            writeln!(f, "   (empty)")?;
        }

        writeln!(f, "Output vars computed:")?;
        if self.var_state.len() > 0 {
            let mut keys : Vec<_> = self.var_state.keys().collect();
            keys.sort();
            for key in keys {
                let var_val = self.var_state.get(&key).expect("unreachable");
                writeln!(f, "   (var-set {key} {var_val})")?;
            }
        }
        else {
            writeln!(f, "   (empty)")?;
        }
        
        writeln!(f, "Input map entries explored:")?;
        if self.pre_map_state.len() > 0 {
            for (map, data) in self.pre_map_state.iter() {
                if data.len() > 0 {
                    writeln!(f, "   map: {map}")?;
                    for key in data.iter() {
                        if is_debug() {
                            writeln!(f, "      key (not simplified): {key}")?;
                        }
                        let key = key.clone().simplify().map(|k| k.to_string()).unwrap_or("ERROR: failed to simplify".to_string());
                        writeln!(f, "      key:   {key}")?;
                    }
                }
                else {
                    writeln!(f, "      (empty)")?;
                }
            }
        }
        else {
            writeln!(f, "   (empty)")?;
        }

        writeln!(f, "Output map entries computed:")?;
        if self.map_state.len() > 0 {
            for (map, data) in self.map_state.iter() {
                if data.len() > 0 {
                    let mut num_present = 0;
                    writeln!(f, "   map: {map}")?;
                    for (key, value) in data.iter() {
                        if let Some(deleted_map_info) = self.map_tombstones.get(map) && deleted_map_info.contains(key) {
                            continue;
                        }

                        if is_debug() {
                            writeln!(f, "        key (not simplified): {key}")?;
                            writeln!(f, "      value (not simplified): {value}")?;
                        }
                        let key = key.clone().simplify().map(|k| k.to_string()).unwrap_or("ERROR: failed to simplify".to_string());
                        let value = value.clone().simplify().map(|v| v.to_string()).unwrap_or("ERROR: failed to simplify".to_string());
                        writeln!(f, "      key:   {key}")?;
                        writeln!(f, "      value: {value}")?;
                        num_present += 1;
                    }
                    if num_present == 0 {
                        writeln!(f,  "      (all deleted)")?;
                    }
                }
                else {
                    writeln!(f, "   (empty)")?;
                }
            }
        }
        else {
            writeln!(f, "   (empty)")?;
        }
        writeln!(f, "Deleted map entries computed:")?;
        if self.map_tombstones.len() > 0 {
            for (map, data) in self.map_tombstones.iter() {
                if data.len() > 0 {
                    writeln!(f, "   map: {map}")?;
                    for key in data.iter() {
                        if is_debug() {
                            writeln!(f, "        key (not simplified): {key}")?;
                        }
                        let key = key.clone().simplify().map(|k| k.to_string()).unwrap_or("ERROR: failed to simplify".to_string());
                        writeln!(f, "      key:   {key}")?;
                    }
                }
                else {
                    writeln!(f, "      (empty)")?;
                }
            }
        }
        else {
            writeln!(f, "   (empty)")?;
        }

        writeln!(f, "Possibly-read data vars:\n   {}",
            if self.reachable_var_reads.len() > 0 {
                let as_strs: Vec<_> = self.reachable_var_reads.iter().map(|n| n.to_string()).collect();
                as_strs.join(", ")
            }
            else {
                "(none)".to_string()
            })?;
        
        writeln!(f, "Possibly-written data vars:\n   {}",
            if self.reachable_var_writes.len() > 0 {
                let as_strs: Vec<_> = self.reachable_var_writes.iter().map(|n| n.to_string()).collect();
                as_strs.join(", ")
            }
            else {
                "(none)".to_string()
            })?;
        
        writeln!(f, "Possibly-read maps:\n   {}",
            if self.reachable_map_reads.len() > 0 {
                let as_strs: Vec<_> = self.reachable_map_reads.iter().map(|n| n.to_string()).collect();
                as_strs.join(", ")
            }
            else {
                "(none)".to_string()
            })?;
        
        writeln!(f, "Possibly-written maps:\n   {}",
            if self.reachable_map_writes.len() > 0 {
                let as_strs: Vec<_> = self.reachable_map_writes.iter().map(|n| n.to_string()).collect();
                as_strs.join(", ")
            }
            else {
                "(none)".to_string()
            })?;
        Ok(())
    }
}

pub trait GetContractSymOps {
    fn get_tx_sender_symop(&self) -> SymOp;
    fn get_tx_sponsor_symop(&self) -> SymOp;
    fn get_contract_caller_symop(&self) -> SymOp;
    fn get_current_contract_symop(&self) -> SymOp;
}

impl GetContractSymOps for Continuation {
    fn get_tx_sender_symop(&self) -> SymOp {
        self.get_tx_sender()
    }

    fn get_tx_sponsor_symop(&self) -> SymOp {
        self.get_tx_sponsor()
    }

    fn get_contract_caller_symop(&self) -> SymOp {
        self.get_contract_caller()
    }

    fn get_current_contract_symop(&self) -> SymOp {
        SymOp::Constant(Value::Principal(self.get_current_contract()))
    }
}

impl Continuation {
    pub fn root(symbex: &Symbex, current_contract: PrincipalData) -> Self {
        let mut cont = Self {
            id: next_cont_id(),
            function_path: None,
            current_line: None,
            current_function: None,
            bound_formulae: HashMap::new(),
            dropped_formulae: vec![],
            predicate: Predicate::True,
            final_formula: SymOp::True(), 
            tx_sender: Some(SymOp::Variable(Sym::Principal("tx-sender".into()))),
            contract_caller: Some(SymOp::Variable(Sym::Principal("contract-caller".into()))),
            tx_sponsor: Some(SymOp::Variable(Sym::Optional("tx-sponsor?".into(), TypeSignature::PrincipalType))),
            current_contract: Some(current_contract),
            parent: None,
            caller: None,
            pre_var_state: HashMap::new(),
            var_state: HashMap::new(),
            pre_map_state: HashMap::new(),
            map_state: HashMap::new(),
            map_tombstones: HashMap::new(),
            map_accesses: HashSet::new(),
            var_accesses: HashSet::new(),
            reachable_map_reads: HashSet::new(),
            reachable_map_writes: HashSet::new(),
            reachable_var_reads: HashSet::new(),
            reachable_var_writes: HashSet::new(),
            panicking: false,
            early_return: false,
        };
        if symbex.tx_sender.is_some() {
            cont.tx_sender = symbex.tx_sender.clone();
        }
        if symbex.contract_caller.is_some() {
            cont.contract_caller = symbex.contract_caller.clone();
        }
        if symbex.tx_sponsor.is_some() {
            cont.tx_sponsor = symbex.tx_sponsor.clone();
        }
        debug!("Root continuation {}", cont.id);
        cont
    }

    pub fn from_parent(parent: Rc<Continuation>, function_path: String, start_line: u32) -> Self {
        assert!(!parent.panicking, "BUG: tried to continue from a panic! Faulty continuation:\n{parent}");
        let parent_id = parent.id;
        let cont = Self {
            id: next_cont_id(),
            function_path: Some(function_path),
            current_line: Some(start_line),
            current_function: parent.current_function.clone(),
            bound_formulae: HashMap::new(),
            dropped_formulae: vec![],
            final_formula: parent.final_formula.clone(),
            predicate: parent.predicate.clone(),
            tx_sender: None,
            contract_caller: None,
            tx_sponsor: None,
            current_contract: None,
            parent: Some(parent.clone()),
            caller: parent.caller.clone(),
            pre_var_state: parent.pre_var_state.clone(),
            var_state: parent.var_state.clone(),
            pre_map_state: parent.pre_map_state.clone(),
            map_state: parent.map_state.clone(),
            map_tombstones: parent.map_tombstones.clone(),
            map_accesses: HashSet::new(),
            var_accesses: HashSet::new(),
            reachable_map_reads: parent.reachable_map_reads.clone(),
            reachable_map_writes: parent.reachable_map_writes.clone(),
            reachable_var_reads: parent.reachable_var_reads.clone(),
            reachable_var_writes: parent.reachable_var_writes.clone(),
            panicking: false,
            early_return: false,
        };
        trace!("Created continuation {} ({}) from parent {}: pred={}", cont.id, cont.function_path.as_ref().map(|s| s.as_str()).unwrap_or("unreachable"), parent_id, &cont.predicate);
        cont
    }
    
    pub fn from_caller(parent: Rc<Continuation>, function_path: String, current_function: String, start_line: u32) -> Self {
        assert!(!parent.panicking, "BUG: tried to continue from a panic");
        let parent_copy = parent.clone();
        let parent_id = parent.id;
        let mut cont = Self::from_parent(parent, function_path, start_line);
        cont.caller = Some(parent_copy);
        cont.current_function = Some(current_function);
        debug!("Created continuation {} ({}) from caller {}", cont.id, cont.function_path.as_ref().map(|s| s.as_str()).unwrap_or("unreachable"), parent_id);
        cont
    }

    pub fn from_callee(parent: Rc<Continuation>, function_path: String, start_line: u32) -> Self {
        // NOTE: parent may be early-return, since we will want to unbind variables on return
        // either way
        assert!(!parent.panicking, "BUG: tried to continue from a panic");
        let parent_id = parent.id;
        let parent_caller_caller = if let Some(parent_caller) = (*parent).caller.as_ref() {
            parent_caller.caller.clone()
        }
        else {
            None
        };

        let early_return = parent.early_return;
        let mut cont = Self::from_parent(parent.clone(), function_path, start_line);
        cont.early_return = early_return;
        cont.bound_formulae = parent_caller_caller.as_ref().map(|parent_caller| parent_caller.bound_formulae.clone()).unwrap_or(HashMap::new());
        cont.caller = parent_caller_caller;
        cont.current_function = if let Some(c) = cont.caller.as_ref() {
            c.current_function.clone()
        }
        else {
            None
        };

        debug!("Created continuation {} ({}) from callee {}", cont.id, cont.function_path.as_ref().map(|s| s.as_str()).unwrap_or("unreachable"), parent_id);
        cont
    }

    /// Clear all side-effects
    fn clear_side_effects(&mut self) {
        self.var_state.clear();
        self.map_state.clear();
        self.map_tombstones.clear();
    }

    /// Bind this continuation's global constants to symbols
    fn bind_globals(&self, symop: SymOp) -> SymOp {
        *symop
            .bind_symbol("tx-sender".into(), self.get_tx_sender())
            .bind_symbol("contract-caller".into(), self.get_contract_caller())
            .bind_symbol("tx-sponsor?".into(), self.get_tx_sponsor())
    }

    /// Given a pre-evaluated "free" continuation representing a function (i.e. where all input and output
    /// variables are free), and given a parent continuation which "calls" this function (i.e.
    /// it binds all of the input symbols), compute a new continuation from the free continuation
    /// by binding all of the parent's symbols into its formulae, maps, data-vars, and predicates.
    /// It's as if the parent has called the function represented by the free continuation, but
    /// skipping the needless work of re-evaluating every possible continuation of the function.
    pub fn from_evaluated(free: &Continuation, function_path: String, parent: Rc<Continuation>) -> Result<Self, Error> {
        assert!(!parent.panicking, "BUG: tried to continue from a panic");

        assert_eq!(free.bound_formulae.len(), 0);
        let mut bound_formulae = free.bound_formulae.clone();
        bound_formulae.extend(parent.bound_formulae.clone().into_iter());

        let mut free_predicate = free.predicate.clone().as_symop();
        for (sym_id, symop) in bound_formulae.iter() {
            trace!("Bind predicate symbol {sym_id} = {symop}");
            free_predicate = *free_predicate.bind_symbol(sym_id.clone(), symop.clone());
        }
        free_predicate = parent.bind_globals(free_predicate);
        let predicate = free_predicate.and(parent.predicate.clone().as_symop()).try_as_predicate()?.simplify()?;

        let mut final_formula = free.final_formula.clone();
        for (sym_id, symop) in bound_formulae.iter() {
            trace!("Bind final formula symbol {sym_id} = {symop}");
            final_formula = *final_formula.bind_symbol(sym_id.clone(), symop.clone());
        }
        final_formula = parent.bind_globals(final_formula);
       
        let mut pre_var_state = parent.pre_var_state.clone();
        for (name, val) in free.pre_var_state.iter() {
            if parent.pre_var_state.contains_key(name) {
                // skip pre-set vars in the parent
                continue;
            }
            if parent.var_state.contains_key(name) {
                // skip already-set vars in the parent -- they're not new inputs
                continue;
            }
            let mut new_val = val.clone().simplify()?;
            for (sym_id, symop) in bound_formulae.iter() {
                let symop = symop.clone().simplify()?;
                trace!("Bind pre-var (var-set {name}) symbol {sym_id} = {symop}");
                new_val = new_val.bind_symbol(sym_id.clone(), symop).simplify()?;
            }
            pre_var_state.insert(name.clone(), new_val);
        }
        
        let mut var_state = parent.var_state.clone();
        for (name, val) in free.var_state.iter() {
            let mut new_val = val.clone().simplify()?;
            for (sym_id, symop) in bound_formulae.iter() {
                let symop = symop.clone().simplify()?;
                trace!("Bind var (var-set {name}) symbol {sym_id} = {symop}");
                new_val = new_val.bind_symbol(sym_id.clone(), symop).simplify()?;
            }
            var_state.insert(name.clone(), new_val);
        }
        
        let mut pre_map_state = parent.pre_map_state.clone();
        for (map_name, map_info) in free.pre_map_state.iter() {
            for key_sym in map_info.iter() {
                let mut new_key_sym = key_sym.clone();
                for (sym_id, symop) in bound_formulae.iter() {
                    let symop = symop.clone().simplify()?;
                    trace!("Bind (pre-map-write {map_name} {key_sym}) symbol {sym_id} = {symop}");
                    new_key_sym = new_key_sym.bind_symbol(sym_id.clone(), symop.clone()).simplify()?;
                }
                new_key_sym = parent.bind_globals(new_key_sym);
                if let Some(new_map_info) = pre_map_state.get_mut(map_name) {
                    new_map_info.insert(new_key_sym);
                }
                else {
                    let mut new_map_state = HashSet::new();
                    new_map_state.insert(new_key_sym);
                    pre_map_state.insert(map_name.clone(), new_map_state);
                }
            }
        }

        let mut map_state = parent.map_state.clone();
        for (map_name, map_info) in free.map_state.iter() {
            for (key_sym, val_sym) in map_info.iter() {
                let mut new_key_sym = key_sym.clone();
                let mut new_val_sym = val_sym.clone();
                for (sym_id, symop) in bound_formulae.iter() {
                    let symop = symop.clone().simplify()?;
                    trace!("Bind (map-write {map_name} {key_sym}) symbol {sym_id} = {symop}");
                    new_key_sym = new_key_sym.bind_symbol(sym_id.clone(), symop.clone()).simplify()?;
                    new_val_sym = new_val_sym.bind_symbol(sym_id.clone(), symop.clone()).simplify()?;
                }
                new_key_sym = parent.bind_globals(new_key_sym);
                new_val_sym = parent.bind_globals(new_val_sym);
                if let Some(new_map_info) = map_state.get_mut(map_name) {
                    new_map_info.insert(new_key_sym, new_val_sym);
                }
                else {
                    let mut new_map_state = HashMap::new();
                    new_map_state.insert(new_key_sym, new_val_sym);
                    map_state.insert(map_name.clone(), new_map_state);
                }
            }
        }
        
        let mut map_tombstones = parent.map_tombstones.clone();
        for (map_name, map_info) in free.map_tombstones.iter() {
            for key_sym in map_info.iter() {
                let mut new_key_sym = key_sym.clone();
                for (sym_id, symop) in bound_formulae.iter() {
                    let symop = symop.clone().simplify()?;
                    trace!("Bind (map-delete {map_name} {key_sym}) symbol {sym_id} = {symop}");
                    new_key_sym = new_key_sym.bind_symbol(sym_id.clone(), symop.clone()).simplify()?;
                }
                new_key_sym = parent.bind_globals(new_key_sym);
                if let Some(new_map_info) = map_tombstones.get_mut(map_name) {
                    new_map_info.insert(new_key_sym);
                }
                else {
                    let mut new_map_tombstones = HashSet::new();
                    new_map_tombstones.insert(new_key_sym);
                    map_tombstones.insert(map_name.clone(), new_map_tombstones);
                }
            }
        }

        let mut reachable_map_reads = HashSet::new();
        reachable_map_reads.extend(free.reachable_map_reads.clone().into_iter());
        reachable_map_reads.extend(parent.reachable_map_reads.clone().into_iter());
        
        let mut reachable_map_writes = HashSet::new();
        reachable_map_writes.extend(free.reachable_map_writes.clone().into_iter());
        reachable_map_writes.extend(parent.reachable_map_writes.clone().into_iter());

        let mut reachable_var_reads = HashSet::new();
        reachable_var_reads.extend(free.reachable_var_reads.clone().into_iter());
        reachable_var_reads.extend(parent.reachable_var_reads.clone().into_iter());
        
        let mut reachable_var_writes = HashSet::new();
        reachable_var_writes.extend(free.reachable_var_writes.clone().into_iter());
        reachable_var_writes.extend(parent.reachable_var_writes.clone().into_iter());

        let mut map_accesses = parent.map_accesses.clone();
        map_accesses.extend(free.map_accesses.clone().into_iter());
        
        let mut var_accesses = parent.var_accesses.clone();
        var_accesses.extend(free.var_accesses.clone().into_iter());

        let cont = Self {
            id: next_cont_id(),
            function_path: Some(function_path),
            current_line: free.current_line.clone(),
            current_function: parent.current_function.clone(),
            bound_formulae: HashMap::new(),
            dropped_formulae: vec![],
            predicate,
            final_formula,
            tx_sender: parent.tx_sender.clone(),
            contract_caller: parent.contract_caller.clone(),
            tx_sponsor: parent.tx_sponsor.clone(),
            current_contract: parent.current_contract.clone(),
            parent: Some(parent.clone()),
            caller: Some(parent.clone()),
            pre_var_state,
            var_state,
            pre_map_state,
            map_state,
            map_tombstones,
            map_accesses,
            var_accesses,
            reachable_map_reads,
            reachable_map_writes,
            reachable_var_reads,
            reachable_var_writes,
            panicking: false,
            early_return: free.early_return || parent.early_return,
        };

        debug!("Created continuation {} ({}) from pre-evaluated continuation {} and parent {}", cont.id, cont.function_path.as_ref().map(|s| s.as_str()).unwrap_or("unreachable"), free.id, parent.id);
        debug!("Parent continuation\n{}", parent);
        debug!("Free continuation\n{}", free);
        debug!("Evaluated continuation\n{}", &cont);
        Ok(cont)
    }

    pub fn with_bound_formulae(mut self, bound_formulae: HashMap<SymId, SymOp>) -> Self {
        self.bound_formulae = bound_formulae;
        self
    }

    /// Find the formula for the given symbol
    pub fn lookup_formula(&self, id: &SymId) -> Option<&SymOp> {
        let mut cursor = self;
        loop {
            if let Some(op) = cursor.bound_formulae.get(id) {
                return Some(op);
            }
            if let Some(parent) = cursor.parent.as_ref() {
                cursor = parent;
            }
            else {
                return None;
            }
        }
    }

    /// Get the compressed view of all bound formulae
    pub fn get_bound_formulae(&self) -> HashMap<SymId, SymOp> {
        let mut cursor = self;
        let mut queue = VecDeque::new();
        queue.push_back(cursor);
        while let Some(parent) = cursor.parent.as_ref() {
            queue.push_back(parent);
            cursor = parent;
        }
        
        let mut ret = HashMap::new();
        for ancestor in queue.into_iter() {
            for dropped in ancestor.dropped_formulae.iter() {
                ret.remove(dropped);
            }
            for (sym_id, sym_val) in ancestor.bound_formulae.iter() {
                ret.insert(sym_id.clone(), sym_val.clone());
            }
        }
        ret
    }

    /// Find the data var formula with the given data var name
    fn lookup_data_var(&mut self, name: &ClarityName) -> Option<&SymOp> {
        // no need to claim that this is "possibly" reached
        let var_full_name = FullName(self.get_current_contract_id(), name.clone());
        self.reachable_var_reads.remove(&var_full_name);
        self.inner_lookup_data_var(&var_full_name)
    }
    
    /// Find the data var formula with the given data var name, as part of checking a clairvoyance
    /// proof
    fn lookup_data_var_for_proof(&self, name: &ClarityName) -> Option<&SymOp> {
        // no need to claim that this is "possibly" reached
        let var_full_name = FullName(self.get_current_contract_id(), name.clone());
        self.inner_lookup_data_var(&var_full_name)
    }

    fn inner_lookup_data_var(&self, name: &FullName) -> Option<&SymOp> {
        if let Some(val) = self.var_state.get(name) {
            Some(val)
        }
        else if let Some(val) = self.pre_var_state.get(name) {
            Some(val)
        }
        else {
            None
        }
    }

    /// record that a map access happend
    pub fn read_data_var(&mut self, name: ClarityName, line: u32) {
        let name = FullName(self.get_current_contract_id(), name);
        self.var_accesses.insert(VarAccess {
            name,
            line
        });
    }

    /// Find the map entry formula with the given map name and key
    /// key_op must be simplified
    pub fn lookup_map_entry(&mut self, name: &ClarityName, key_op: &SymOp) -> Option<&SymOp> {
        let name = FullName(self.get_current_contract_id(), name.clone());

        // no need to claim that this is "possibly" reached
        self.reachable_map_reads.remove(&name);
        if self.is_map_deleted(&name, key_op) {
            return None;
        }

        let map_index = self.map_state.get(&name)?;
        map_index.get(key_op)
    }
    
    /// Find the map entry formula with the given map name and key
    /// key_op must be simplified.
    /// used for checking proofs
    pub fn lookup_map_entry_for_proof(&self, name: &ClarityName, key_op: &SymOp) -> Option<&SymOp> {
        let name = FullName(self.get_current_contract_id(), name.clone());

        // no need to claim that this is "possibly" reached
        if self.is_map_deleted(&name, key_op) {
            return None;
        }

        let map_index = self.map_state.get(&name)?;
        map_index.get(key_op)
    }
    
    /// See if this key was recently deleted
    /// key_op must be simplified
    pub fn is_map_deleted(&self, name: &FullName, key_op: &SymOp) -> bool {
        if let Some(tombstone_idx) = self.map_tombstones.get(name) && tombstone_idx.get(key_op).is_some() {
            return true;
        }
        false
    }

    /// Find tx-sender
    pub fn get_tx_sender(&self) -> SymOp {
        let mut cursor = self;
        loop {
            if let Some(p) = cursor.tx_sender.as_ref() {
                return p.clone();
            }
            if let Some(parent) = cursor.parent.as_ref() {
                cursor = parent;
            }
            else {
                unreachable!("root continuation always constructed with tx-sender");
            }
        }
    }

    /// Find contract-caller
    pub fn get_contract_caller(&self) -> SymOp {
        let mut cursor = self;
        loop {
            if let Some(p) = cursor.contract_caller.as_ref() {
                return p.clone();
            }
            if let Some(parent) = cursor.parent.as_ref() {
                cursor = parent;
            }
            else {
                unreachable!("root continuation always constructed with contract-caller");
            }
        }
    }
    
    /// Find current-contract
    pub fn get_current_contract(&self) -> PrincipalData {
        let mut cursor = self;
        loop {
            if let Some(p) = cursor.current_contract.as_ref() {
                return p.clone();
            }
            if let Some(parent) = cursor.parent.as_ref() {
                cursor = parent;
            }
            else {
                unreachable!("root continuation always constructed with current-contract");
            }
        }
    }
   
    /// Get current-contract, but as a QualifiedContractIdentifier
    pub fn get_current_contract_id(&self) -> QualifiedContractIdentifier {
        let p = self.get_current_contract();
        let PrincipalData::Contract(qid) = p else {
            unreachable!("current-contract is not a contract principal");
        };
        qid
    }

    /// Find tx-sponsor
    pub fn get_tx_sponsor(&self) -> SymOp {
        let mut cursor = self;
        loop {
            if let Some(p) = cursor.contract_caller.as_ref() {
                return p.clone();
            }
            if let Some(parent) = cursor.parent.as_ref() {
                cursor = parent;
            }
            else {
                unreachable!("root continuation always constructed with tx-sponsor");
            }
        }
    }

    /// Set a constant value via (define-constant ..)
    pub fn bind_constant(&mut self, name: &ClarityName, value: &Value) {
        let symid : SymId = name.into();
        self.bound_formulae.insert(symid, SymOp::Constant(value.clone()));
    }

    /// Bind a name to a symbol
    pub fn bind_sym(&mut self, name: &ClarityName, sym: Sym) {
        let symid : SymId = name.into();
        self.bound_formulae.insert(symid, SymOp::Variable(sym));
    }
    
    /// Bind a name to a formula over symbols
    pub fn bind_symop(&mut self, name: &ClarityName, symop: SymOp) {
        if symop == SymOp::Panic {
            warn!("Continuation {}: bound {} to a panicking symop", self.id, name);
            self.panicking = true;
        }
        let symid : SymId = name.into();
        self.bound_formulae.insert(symid, symop);
    }

    /// Unbind a bound formula
    pub fn unbind(&mut self, name: &ClarityName) {
        let symid : SymId = name.into();
        self.dropped_formulae.push(symid);
    }
    
    /// Set an initial data var formula
    pub fn set_pre_data_var(&mut self, name: &ClarityName, symop: SymOp) {
        let fqname = FullName(self.get_current_contract_id(), name.clone());
        self.pre_var_state.insert(fqname.clone(), SymOp::LoadedDataVariable(fqname, Box::new(symop)));
    }

    /// Set a data-var formula consequent to a (var-set ..)
    /// symop should be simplified
    pub fn set_data_var(&mut self, name: &ClarityName, symop: SymOp) {
        let fqname = FullName(self.get_current_contract_id(), name.clone());
        self.var_state.insert(fqname.clone(), symop); // SymOp::LoadedDataVariable(fqname, Box::new(symop)));

        // no need to claim that this is "possibly" reached
        self.reachable_var_writes.remove(&fqname);
    }

    /// Record that a map entry was accessed, and possibly had the given value at the time
    pub fn read_map_entry(&mut self, name: ClarityName, key_symop: SymOp, val_symop: Option<SymOp>, line: u32) {
        let name = FullName(self.get_current_contract_id(), name.clone());
        if val_symop.is_none() && !self.is_map_deleted(&name, &key_symop) {
            // this is the first time this was accessed, so it's input
            if let Some(recs) = self.pre_map_state.get_mut(&name) {
                recs.insert(key_symop.clone());
            }
            else {
                let mut recs = HashSet::new();
                recs.insert(key_symop.clone());
                self.pre_map_state.insert(name.clone(), recs);
            }
        }
        self.map_accesses.insert(MapAccess {
            name,
            key: key_symop,
            line
        });
    }

    /// Set a map entry consequent to a (map-set ..)
    /// key_symop must be simplified.
    pub fn set_map_entry(&mut self, name: &ClarityName, key_symop: SymOp, val_symop: SymOp) {
        let name = FullName(self.get_current_contract_id(), name.clone());
        if let Some(idx) = self.map_tombstones.get_mut(&name) {
            idx.remove(&key_symop);
        }
        if let Some(map) = self.map_state.get_mut(&name) {
            map.insert(key_symop, val_symop);
        }
        else {
            let mut map = HashMap::new();
            map.insert(key_symop, val_symop);
            self.map_state.insert(name.clone(), map);
        }
        // no need to claim that this is "possibly" reached
        self.reachable_map_writes.remove(&name);
    }
    
    /// Delete a map entry
    pub fn delete_map_entry(&mut self, name: &ClarityName, key_symop: &SymOp) -> bool {
        let name = FullName(self.get_current_contract_id(), name.clone());
        let present = if let Some(map) = self.map_state.get_mut(&name) {
            let present = map.contains_key(&key_symop);
            map.remove(key_symop);
            present
        }
        else {
            false
        };
        let empty = self.map_state.get(&name).map(|map| map.is_empty()).unwrap_or(false);
        if empty {
            self.map_state.remove(&name);
        }

        if let Some(idx) = self.map_tombstones.get_mut(&name) {
            idx.insert(key_symop.clone());
        }
        else {
            let mut idx = HashSet::new();
            idx.insert(key_symop.clone());
            self.map_tombstones.insert(name.clone(), idx);
        }
        // no need to claim that this is "possibly" reached
        self.reachable_map_writes.remove(&name);
        present
    }

    /// Compute a trace of how this continuation arrived to where it did
    pub fn trace(&self) -> Trace {
        let mut cursor_stack = vec![];
        let mut trace_items = vec![];
            
        let mut self_trace = TraceItem {
            depth: 0,
            identifier: self.function_path.clone().unwrap_or("".to_string()),
            contract_id: self.get_current_contract_id(),
            start_line: self.current_line.clone().unwrap_or(0),
            function: self.current_function.clone().unwrap_or("".to_string()),
            cont_id: self.id,
            bound_formulae: self.bound_formulae.clone(),
            dropped_formulae: self.dropped_formulae.clone(),
            predicate: self.predicate.clone(),
        };

        let Some(parent) = &self.parent else {
            return Trace(vec![self_trace]);
        };

        cursor_stack.push(parent);

        let mut end = false;

        while let Some(cursor) = cursor_stack.last() {
            if !end {
                if let Some(parent) = cursor.parent.as_ref() {
                    cursor_stack.push(&parent);
                    continue;
                }
            }

            end = true;
            let cursor = cursor_stack.pop().expect("infallible");
            let depth = cursor_stack.len();

            let trace_item = TraceItem {
                depth,
                identifier: cursor.function_path.clone().unwrap_or("".to_string()),
                contract_id: cursor.get_current_contract_id(),
                start_line: cursor.current_line.clone().unwrap_or(0),
                function: cursor.current_function.clone().unwrap_or("".to_string()),
                cont_id: cursor.id,
                bound_formulae: cursor.bound_formulae.clone(),
                dropped_formulae: cursor.dropped_formulae.clone(),
                predicate: cursor.predicate.clone(),
            };
            trace_items.push(trace_item);
        }

        let depth = trace_items.len();
        trace_items.iter_mut().for_each(|t| t.depth = depth - t.depth);
        self_trace.depth = depth + 1;
        trace_items.push(self_trace);
        trace_items.reverse();
        Trace(trace_items)
    }

    /// Compress a chain of continuations' states into a single, final state
    fn snapshot_access_state(&self, ancestor_id: Option<u64>) -> ContinuationAccessSnapshot {
        // compute state for the rolled-up continuation
        let mut cursor_stack = vec![];
        cursor_stack.push(self);
        
        let mut final_map_accesses = vec![];
        let mut final_var_accesses = vec![];
        
        let mut parent = None;
        let mut caller = None;
        let mut end = false;
        let mut panicking = self.panicking;

        while let Some(cursor) = cursor_stack.last() {
            if !end {
                if let Some(parent) = cursor.parent.as_ref() {
                    let stop = if let Some(ancestor_id) = ancestor_id.as_ref() {
                        parent.id == *ancestor_id
                    }
                    else {
                        false
                    };
                    if !stop {
                        cursor_stack.push(parent);
                        continue;
                    }
                }
            }
            let cursor = cursor_stack.pop().expect("infallible");
            trace!("Compressing state from continuation {}", cursor.id);
            if !end {
                parent = cursor.parent.clone();
                caller = cursor.caller.clone();
                trace!("New parent of compressed continuation snapshot of {} will be {}", self.id, parent.as_ref().map(|p| format!("{}", p.id)).unwrap_or("(none)".to_string()));
                trace!("New caller of compressed continuation snapshot of {} will be {}", self.id, caller.as_ref().map(|c| format!("{}", c.id)).unwrap_or("(none)".to_string()));
                if let Some(ancestor_id) = ancestor_id {
                    assert_eq!(parent.as_ref().map(|p| p.id), Some(ancestor_id));
                }
                end = true;
            }
            final_var_accesses.extend(cursor.var_accesses.clone().into_iter());
            final_map_accesses.extend(cursor.map_accesses.clone().into_iter());
            panicking = panicking || cursor.panicking;
        }

        ContinuationAccessSnapshot {
            map_accesses: final_map_accesses.into_iter().collect(),
            var_accesses: final_var_accesses.into_iter().collect(),
            parent,
            caller,
            panicked: panicking
        }
    }


    /// Roll up this continuation with its ancestors, back to a certain ancestor ID (inclusive)
    pub fn rollup_to(self, ancestor_id: Option<u64>) -> Self {
        let tx_sender = self.get_tx_sender();
        let contract_caller = self.get_contract_caller();
        let current_contract = self.get_current_contract();

        let early_return = self.early_return || self.halted();

        if early_return {
            trace!("Rolling up an early-return continuation {}", self.id);
        }
        
        // check that ancestor_id is actually an ancestor.
        let mut is_ancestor = ancestor_id.is_none();
        let mut cursor = &self;
        while !is_ancestor {
            if let Some(parent) = cursor.parent.as_ref() {
                if let Some(ancestor_id) = ancestor_id {
                    if ancestor_id == parent.id {
                        is_ancestor = true;
                    }
                }
                cursor = parent;
                continue;
            }
            break;
        }

        assert!(is_ancestor, "Continuation {} does not descend from {:?}", self.id, &ancestor_id);

        trace!("Roll back continunation {} to its ancestor {:?}", self.id, &ancestor_id);

        // compute state for the rolled-up continuation
        let snapshot = self.snapshot_access_state(ancestor_id);
        let final_map_accesses = snapshot.map_accesses;
        let final_var_accesses = snapshot.var_accesses;
        let parent = snapshot.parent;
        let caller = snapshot.caller;
        let panicking = snapshot.panicked;

        let old_cont_str = self.to_string();
        let old_trace = self.trace();

        let merged = Self {
            id: next_cont_id(),
            bound_formulae: self.bound_formulae.clone(),
            var_state: self.var_state.clone(),
            pre_var_state: self.pre_var_state.clone(),
            pre_map_state: self.pre_map_state.clone(),
            map_state: self.map_state.clone(),
            map_tombstones: self.map_tombstones.clone(),
            var_accesses: final_var_accesses,
            map_accesses: final_map_accesses,
            reachable_map_reads: self.reachable_map_reads.clone(),
            reachable_map_writes: self.reachable_map_writes.clone(),
            reachable_var_reads: self.reachable_var_reads.clone(),
            reachable_var_writes: self.reachable_var_writes.clone(),
            tx_sender: Some(tx_sender),
            contract_caller: Some(contract_caller),
            current_contract: Some(current_contract),
            panicking,
            early_return,
            parent,
            caller,
            dropped_formulae: self.dropped_formulae.clone(),
            ..self
        };
        let bound_formulae_parts : Vec<_> = self.bound_formulae
            .iter()
            .map(|(sym_id, symop)| format!("({sym_id} {symop})"))
            .collect();

        let bound_formulae_str = bound_formulae_parts.join(" ");
        
        let unbound_formulae_parts : Vec<_> = self.dropped_formulae
            .iter()
            .map(|sym_id| format!("{sym_id}"))
            .collect();

        let unbound_formulae_str = if unbound_formulae_parts.len() > 0 {
            format!("unbound: {}", unbound_formulae_parts.join(" "))
        }
        else {
            "".to_string()
        };
        debug!("Roll up continuation {} to ancestor {:?} to create continuation {} {} {}", self.id, ancestor_id, merged.id, &bound_formulae_str, &unbound_formulae_str);
        trace!("Continuation name: {}", merged.get_function_path());
        trace!("Continuation:\n{}", &merged);
        trace!("Trace:\n{}", &merged.trace());
        trace!("Old continuation:\n{old_cont_str}");
        trace!("Old trace:\n{old_trace}");
        merged
    }
    
    // Roll up all the way back to the root
    pub fn rollup(self) -> Self {
        let root = self.rollup_to(None);
        assert!(root.parent.is_none());
        assert!(root.caller.is_none());
        root
    }

    /// Has this continuation halted execution?
    pub fn halted(&self) -> bool {
        if self.panicking {
            return true;
        }
        if self.early_return {
            return true;
        }
        false
    }

    /// Is the given continuation an ancestor of this continuation?
    pub fn descends_from(&self, ancestor: &Continuation) -> bool {
        if ancestor.id == self.id {
            return true;
        }
        let mut cursor = self.parent.as_ref();
        while let Some(anc) = cursor.take() {
            // if anc.borrow() == ancestor {
            if (*anc).id == ancestor.id {
                return true;
            }
            cursor = anc.parent.as_ref();
        }
        return false;
    }

    /// Determine whether or not a given function in the callgraph may read state that has been
    /// written in this continuation (i.e. if not, then perhaps we don't need to evaluate this
    /// function).
    pub fn is_causally_independent(&self, func_name: &FullName, callgraph: &Callgraph) -> Result<bool, Error> {
        let reachable_map_accesses : HashSet<_> = callgraph.reachable_map_accesses_from(func_name)?
            .into_iter()
            .collect();
        
        let reachable_var_accesses : HashSet<_> = callgraph.reachable_var_accesses_from(func_name)?
            .into_iter()
            .collect();

        let rolled_up = self.clone().rollup();
        for accessed in reachable_map_accesses.into_iter() {
            if rolled_up.map_state.contains_key(&accessed) {
                // this function may access a map written in this continuation
                debug!("Function {func_name} reads state from map {accessed}, which was written to by continuation {}", self.id);
                return Ok(false);
            }
            if rolled_up.reachable_map_writes.contains(&accessed) {
                // this function may access a map that might have been written before
                debug!("Function {func_name} reads state from map {accessed}, which may be written to by continuation {}", self.id);
                return Ok(false);
            }
        }
        for accessed in reachable_var_accesses.into_iter() {
            if rolled_up.var_state.contains_key(&accessed) {
                // this function may access a var written in this continuation
                debug!("Function {func_name} reads state from data-var {accessed}, which was written to by continuation {}", self.id);
                return Ok(false);
            }
            if rolled_up.reachable_var_writes.contains(&accessed) {
                // this function may access a var that might have been written before
                debug!("Function {func_name} reads state from data-var {accessed}, which may be written to by continuation {}", self.id);
                return Ok(false);
            }
        }
        
        // this function cannot access any state written so far
        Ok(true)
    }

    /// Determine whether or not a given function's reads are independent of this continuation.
    /// That is, the values it reads from vars or maps have not previously been written by this
    /// continuation.
    pub fn is_read_independent(&self, evaled_cont: &Continuation) -> Result<bool, Error> {
        let mut evaled_map_reads : HashMap<FullName, HashSet<SymOp>> = HashMap::new();

        for map_access in evaled_cont.map_accesses.iter() {
            let map_name = &map_access.name;
            let key_sym = map_access.key.clone().simplify()?;
            if let Some(keys) = evaled_map_reads.get_mut(map_name) {
                keys.insert(key_sym);
            }
            else {
                let mut set = HashSet::new();
                set.insert(key_sym);
                evaled_map_reads.insert(map_name.clone(), set);
            }
        }

        for (map_name, writes) in self.map_state.iter() {
            for (key_sym, _) in writes.iter() {
                let key_sym = key_sym.clone().simplify()?;
                if let Some(set) = evaled_map_reads.get(map_name) {
                    if set.contains(&key_sym) {
                        // this cont wrote a map entry that evaled_cont reads
                        debug!("Evaled continuation {} reads map {map_name} key {key_sym}, which continuation {} wrote", evaled_cont.id, self.id);
                        return Ok(false);
                    }
                }
            }
        }
        
        for var_access in evaled_cont.var_accesses.iter() {
            let var_name = &var_access.name;
            if self.inner_lookup_data_var(var_name).is_some() {
                // this cont write a var that evaled_cont reads
                debug!("Evaled continuation {} reads var {var_name}, which continuation {} wrote", evaled_cont.id, self.id);
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Determine whether or not this continuation has written any data
    pub fn is_read_only_so_far(&self) -> bool {
        if !self.map_state.is_empty() {
            return false;
        }
        if !self.map_tombstones.is_empty() {
            return false;
        }
        if !self.var_state.is_empty() {
            return false;
        } 

        true
    }

    /// Given a function and a callgraph, add to this continuation the set of map and var accesses
    /// that may be reached from it
    pub fn add_reachable_storage_accesses(&mut self, func_name: &FullName, callgraph: &Callgraph) -> Result<(), Error> {
        let reachable_map_accesses : HashSet<_> = callgraph.reachable_map_accesses_from(func_name)?
            .into_iter()
            .collect();
        
        let reachable_map_mutations : HashSet<_> = callgraph.reachable_map_mutations_from(func_name)?
            .into_iter()
            .collect();
        
        let reachable_var_accesses : HashSet<_> = callgraph.reachable_var_accesses_from(func_name)?
            .into_iter()
            .collect();
        
        let reachable_var_mutations : HashSet<_> = callgraph.reachable_var_mutations_from(func_name)?
            .into_iter()
            .collect();

        self.reachable_map_reads.extend(reachable_map_accesses.into_iter());
        self.reachable_map_writes.extend(reachable_map_mutations.into_iter());
        self.reachable_var_reads.extend(reachable_var_accesses.into_iter());
        self.reachable_var_writes.extend(reachable_var_mutations.into_iter());
        Ok(())
    }

    /// Get the function path for this continuation
    pub fn get_function_path(&self) -> String {
        self.function_path.as_ref().unwrap_or(&"".to_string()).to_string()
    }

    /// Get the name of the caller of this continuation
    pub fn get_caller_name(&self) -> String {
        self.caller.as_ref().map(|c| c.get_function_path()).unwrap_or("(toplevel)".to_string())
    }

    /// Determine if it is possible to combine two continuations. That is:
    /// * they have the same caller
    /// * they have the same storage reads and writes so far
    /// * they have the same formula
    /// * they have the same early_return and panicked values
    pub fn can_combine_with<F>(&self, other: &Continuation, cmp_final_formula: F) -> bool
    where
        F: Fn(&SymOp, &SymOp) -> bool
    {
        let self_early_return = self.early_return || self.halted();
        let other_early_return = other.early_return || other.halted();

        if self.caller != other.caller
            || self.map_state != other.map_state
            || self.map_tombstones != other.map_tombstones
            || !cmp_final_formula(&self.final_formula, &other.final_formula)
            || self.bound_formulae != other.bound_formulae
            || self.panicking != other.panicking
            || self_early_return != other_early_return
        {
            return false;
        }

        let self_state = self.snapshot_access_state(None);
        let self_panicked = self_state.panicked;

        let other_state = self.snapshot_access_state(None);
        let other_panicked = other_state.panicked;

        if self.var_state != other.var_state
            || self_panicked != other_panicked
        {
            return false;
        }

        true
    }
    
    /// Combine two continuations.
    /// The resulting predicate will be the OR-ing of the two predicates.
    /// The resuting map and var accesses will be combined, as will their input states.
    pub fn combine<F>(self, others: Vec<Continuation>, merge_final_formulae: F) -> Result<Continuation, Error>
    where
        F: Fn(Vec<SymOp>) -> SymOp
    {
        let self_snapshot = self.snapshot_access_state(None);
        let self_map_access = self_snapshot.map_accesses;
        let self_var_access = self_snapshot.var_accesses;
        let self_panicked = self_snapshot.panicked;
        let self_function_path = self.get_function_path();
        let self_early_return = self.early_return || self.halted();

        let mut final_var_accesses = self_var_access.clone();
        let mut final_map_accesses = self_map_access.clone();

        let mut final_reachable_map_reads = self.reachable_map_reads.clone();
        let mut final_reachable_map_writes = self.reachable_map_writes.clone();
        let mut final_reachable_var_reads = self.reachable_var_reads.clone();
        let mut final_reachable_var_writes = self.reachable_var_writes.clone();

        let mut paths = vec![self_function_path.clone()];
        let mut preds = vec![Box::new(self.predicate.clone())];
        let mut ids = vec![self.id];

        let mut final_formulae = vec![self.final_formula.clone()];
        let mut pre_map_state = self.pre_map_state.clone();
        let mut pre_var_state = self.pre_var_state.clone();
        
        for other in others.into_iter() {
            // assert baseline combination conditions
            assert!(self.can_combine_with(&other, |_f1: &SymOp, _f2: &SymOp| true), "Cannot combine continuations {} and {}", self.id, other.id);

            let other_snapshot = other.snapshot_access_state(None);
            let other_map_access = other_snapshot.map_accesses;
            let other_var_access = other_snapshot.var_accesses;
            let other_function_path = other.get_function_path();

            final_var_accesses.extend(other_var_access.into_iter());
            final_map_accesses.extend(other_map_access.into_iter());

            final_reachable_map_reads.extend(other.reachable_map_reads.into_iter());
            final_reachable_map_writes.extend(other.reachable_map_writes.into_iter());
            final_reachable_var_reads.extend(other.reachable_var_reads.into_iter());
            final_reachable_var_writes.extend(other.reachable_var_writes.into_iter());
            
            let other_old_pred = other.predicate.clone();

            paths.push(other_function_path);
            preds.push(Box::new(other_old_pred));
            ids.push(other.id);
            final_formulae.push(other.final_formula);
            pre_map_state.extend(other.pre_map_state.into_iter());
            pre_var_state.extend(other.pre_var_state.into_iter());
        }

        let mut min_cutoff = 0;
        for function_path in paths.iter() {
            let mut cutoff = 0;
            for (i, (cs, co)) in self_function_path.chars().zip(function_path.chars()).enumerate() {
                if cs != co {
                    break;
                }
                cutoff = i;
            }

            min_cutoff = cutoff.min(min_cutoff);
        }

        let mut self_prefix = "".to_string();
        for (i, c) in self_function_path.chars().enumerate() {
            if i < min_cutoff {
                self_prefix.push(c);
            }
        }

        let mut suffixes = vec![];
        for (function_path, id) in paths.iter().zip(ids.iter()) {
            let mut other_suffix = "".to_string();
            for (i, c) in function_path.char_indices() {
                if i < min_cutoff {
                    continue;
                }
                other_suffix.push(c);
            }
            suffixes.push(format!("{id}-{other_suffix}"));
        }

        let function_path = format!("{self_prefix}.COMBINE({})", suffixes.join(", "));
        let predicate_combined = Predicate::Or(preds.clone());

        let combined = Self {
            id: next_cont_id(),
            predicate: predicate_combined.simplify()?,
            function_path: Some(function_path),
            bound_formulae: self.bound_formulae.clone(),
            pre_var_state,
            var_state: self.var_state.clone(),
            pre_map_state,
            map_state: self.map_state.clone(),
            map_tombstones: self.map_tombstones.clone(),
            var_accesses: final_var_accesses,
            map_accesses: final_map_accesses,
            reachable_map_reads: final_reachable_map_reads,
            reachable_map_writes: final_reachable_map_writes,
            reachable_var_reads: final_reachable_var_reads,
            reachable_var_writes: final_reachable_var_writes,
            tx_sender: self.tx_sender,
            contract_caller: self.contract_caller,
            current_contract: self.current_contract,
            panicking: self_panicked,
            early_return: self_early_return,
            parent: self.parent,
            caller: self.caller,
            dropped_formulae: self.dropped_formulae.clone(),
            final_formula: merge_final_formulae(final_formulae),
            ..self
        };

        debug!("Combined continuations {} to produce {}: Joined predicates\n{}", ids.into_iter().map(|i| i.to_string()).collect::<Vec<_>>().join(","), combined.id, preds.into_iter().map(|p| p.to_string()).collect::<Vec<_>>().join("\n"));
        Ok(combined)
    }
}

#[derive(Debug, Clone, PartialEq, Hash)]
pub struct CallgraphFunction {
    pub fq_name: FullName,
    pub start_line: u32
}

impl fmt::Display for CallgraphFunction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}:{}", &self.fq_name, self.start_line)
    }
}

impl CallgraphFunction {
    pub fn new(fq_name: FullName, start_line: u32) -> Self {
        Self {
            fq_name,
            start_line
        }
    }

    pub fn call_name(&self) -> &FullName {
        &self.fq_name
    }

    pub fn line(&self) -> u32 {
        self.start_line
    }
}

/// Call graph entries
#[derive(Debug, Clone, PartialEq)]
pub struct CallgraphNode {
    /// list of functions called
    pub callable: Vec<CallgraphFunction>,
    /// list of vars that this function may read from
    pub var_reads: HashSet<FullName>,
    /// list of maps that this function may read from
    pub map_reads: HashSet<FullName>,
    /// list of vars that this function may write to
    pub var_writes: HashSet<FullName>,
    /// list of maps that this function may write to
    pub map_writes: HashSet<FullName>,
    /// whether or not this function is pure -- as in, it does not do I/O, nor do any of its
    /// reachable functions.
    pub is_pure: bool,
}

impl fmt::Display for CallgraphNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let mut callables : Vec<_> = self.callable.iter().map(|c| format!("{}:{}", c.fq_name.name(), c.line())).collect();
        let mut var_reads : Vec<_> = self.var_reads.iter().map(|c| c.to_string()).collect();
        let mut map_reads : Vec<_> = self.map_reads.iter().map(|c| c.to_string()).collect();
        let mut var_writes : Vec<_> = self.var_writes.iter().map(|c| c.to_string()).collect();
        let mut map_writes : Vec<_> = self.map_writes.iter().map(|c| c.to_string()).collect();

        callables.sort();
        var_reads.sort();
        var_writes.sort();
        map_reads.sort();
        map_writes.sort();

        writeln!(f, "pure?:      {}", self.is_pure)?;
        writeln!(f, "functions:  {}", if callables.len() > 0 { callables.join(", ") } else { "(empty)".to_string() })?;
        writeln!(f, "map-reads:  {}", if map_reads.len() > 0 { map_reads.join(", ") } else { "(empty)".to_string() })?;
        writeln!(f, "map-writes: {}", if map_writes.len() > 0 { map_writes.join(", ") } else { "(empty)".to_string() })?;
        writeln!(f, "var-reads:  {}", if var_reads.len() > 0 { var_reads.join(", ") } else { "(empty)".to_string() })?;
        writeln!(f, "var-writes: {}", if var_writes.len() > 0 { var_writes.join(", ") } else { "(empty)".to_string() })?;
        Ok(())
    }
}

impl CallgraphNode {
    pub fn new() -> Self {
        Self {
            callable: vec![],
            var_reads: HashSet::new(),
            map_reads: HashSet::new(),
            var_writes: HashSet::new(),
            map_writes: HashSet::new(),
            is_pure: false,
        }
    }
    
    pub fn add_readable_var(&mut self, var_name: FullName) {
        self.var_reads.insert(var_name);
    }

    pub fn add_readable_map(&mut self, map_name: FullName) {
        self.map_reads.insert(map_name);
    }

    pub fn add_writable_var(&mut self, var_name: FullName) {
        self.var_writes.insert(var_name);
    }

    pub fn add_writable_map(&mut self, map_name: FullName) {
        self.map_writes.insert(map_name);
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Callgraph {
    /// Map data vars, data maps, and functions to their respective callgraph nodes
    reachable: HashMap<FullName, CallgraphNode>,
    /// Trait concretizations -- bind function name and variable name to contract ID
    trait_concretizations: HashMap<FullName, HashMap<ClarityName, QualifiedContractIdentifier>>,
    default_trait_concretizations: HashMap<TraitIdentifier, QualifiedContractIdentifier>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct CallgraphView<'a> {
    callgraph: &'a Callgraph,
    cursor: FullName
}

impl<'a> fmt::Display for CallgraphView<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let mut queue = vec![];
        queue.push((0, &self.cursor));
        while let Some((depth, name)) = queue.pop() {
            let mut indent = "".to_string();
            for _ in 0..depth {
                indent.push_str("   ");
            }
            let Some(node) = self.callgraph.reachable.get(name) else {
                panic!("BUG: callgraph view has no entry for {name}");
            };

            writeln!(f, "{indent}{} ({depth}):", name.name())?;
            let inner = node.to_string();
            let inner_parts = inner.split("\n");
            for part in inner_parts {
                writeln!(f, "   {indent}{part}")?;
            }
            for callable in node.callable.iter().rev() {
                // NOTE: need the rev() since we build the callgraph depth-first
                queue.push((depth + 1, callable.call_name()));
            }
        }
        Ok(())
    }
}

impl Callgraph {
    pub fn from_contracts(
        contracts: &HashMap<QualifiedContractIdentifier, SymContract>,
        target_contract: &QualifiedContractIdentifier,
        concretized_traits: HashMap<FullName, HashMap<ClarityName, QualifiedContractIdentifier>>,
        default_traits: HashMap<TraitIdentifier, QualifiedContractIdentifier>
    ) -> Result<Callgraph, Error> {
        let mut callgraph = Self::empty();
        callgraph.trait_concretizations = concretized_traits;
        callgraph.default_trait_concretizations = default_traits;
        callgraph.load_defs(contracts, target_contract)?;
        Ok(callgraph)
    }
    
    fn empty() -> Self {
        Self {
            reachable: HashMap::new(),
            trait_concretizations: HashMap::new(),
            default_trait_concretizations: HashMap::new(),
        }
    }

    fn walk_functions<F>(exprs: &[SymbolicExpression], mut walk: F) -> Result<(), Error>
    where
        F: FnMut(&ClarityName, Vec<(ClarityName, TypeSignature)>, &[SymbolicExpression]) -> Result<(), Error>
    {
        for body in exprs.iter() {
            if let SymbolicExpressionType::List(lv) = &body.expr
                && let Some(first) = lv.first()
                && let Some(function_base_name) = first.match_atom()
                && (function_base_name.as_str() == "define-public"
                    || function_base_name.as_str() == "define-private"
                    || function_base_name.as_str() == "define-read-only")
            {
                let Some(name_and_args_expr) = lv.get(1) else {
                    return Err(Error::Bug(format!("No function definition for {body}")));
                };
                let Some(name_and_args) = name_and_args_expr.match_list() else {
                    return Err(Error::Bug(format!("Function name and arguments is not a list in {body}")));
                };
                let Some(def_name_atom) = name_and_args.get(0) else {
                    return Err(Error::Bug(format!("No function definition for {name_and_args:?}")));
                };
                let Some(def_name) = def_name_atom.match_atom() else {
                    return Err(Error::Bug(format!("Function definition name is not an atom: {def_name_atom}")));
                };
                let typed_args = if let Some(func_args) = name_and_args.get(1..) {
                    let typed_args = parse_name_type_pairs::<_, VmExecutionError>(DEFAULT_STACKS_EPOCH, func_args, SyntaxBindingErrorType::Eval, &mut ())?;
                    typed_args
                }
                else {
                    vec![]
                };
                let Some(func_body) = lv.get(2..) else {
                    return Err(Error::Bug(format!("No function body for {def_name}")));
                };

                walk(def_name, typed_args, func_body)?;
            }
        }
        Ok(())
    }

    fn load_defs(&mut self, contracts: &HashMap<QualifiedContractIdentifier, SymContract>, target_contract: &QualifiedContractIdentifier) -> Result<(), Error> {
        let Some(sym_contract) = contracts.get(target_contract) else {
            return Err(Error::NotFound(format!("Missing contract {target_contract}")));
        };
        
        let mut frontier : HashMap<FullName, (Vec<(ClarityName, TypeSignature)>, Vec<SymbolicExpression>)> = HashMap::new();
        let mut reachable : HashMap<FullName, CallgraphNode> = HashMap::new();

        Self::walk_functions(&sym_contract.symbols, |def_name, func_args, func_body| {
            let node = CallgraphNode::new();
            let fq_name = FullName(target_contract.clone(), def_name.clone());
            reachable.insert(fq_name.clone(), node);

            trace!("top-level function: {fq_name}: {func_args:?}");
            frontier.insert(fq_name, (func_args, func_body.to_vec()));
            Ok(())
        })?;

        reachable.retain(|fq_name, _| !self.reachable.contains_key(fq_name));
        if reachable.is_empty() {
            return Ok(());
        }

        frontier.retain(|fq_name, _| !self.reachable.contains_key(fq_name));
        if frontier.is_empty() {
            return Ok(())
        }

        self.reachable.extend(reachable.into_iter());

        for (name, (func_args, func_body)) in frontier.into_iter() {
            self.build(contracts, target_contract, &name, &func_args, &func_body)?;
        }
        let mut is_pure = HashMap::new();
        for name in self.reachable.keys() {
            let is_pure_func = self.check_pure(name)?;
            is_pure.insert(name.clone(), is_pure_func);
        }

        for (name, is_pure) in is_pure.into_iter() {
            let Some(node) = self.reachable.get_mut(&name) else {
                return Err(Error::Bug(format!("unreachable -- no reachable node for {name}")));
            };
            trace!("Function {name} is {}", if is_pure { "pure" } else { "not pure" });
            node.is_pure = is_pure;
        }

        Ok(())
    }

    fn build(
        &mut self,
        contracts:
        &HashMap<QualifiedContractIdentifier, SymContract>,
        target_contract: &QualifiedContractIdentifier,
        func_name: &FullName,
        func_args: &[(ClarityName, TypeSignature)],
        body_list: &[SymbolicExpression]
    ) -> Result<(), Error> {
        for body in body_list.iter() {
            trace!("build: {func_name}: visit {}", &body.expr);
            let Some(lv) = body.match_list() else {
                continue;
            };
            let Some(first) = lv.first() else {
                // this can happen with `as-contract?`, for example
                continue;
            };
            if let Some(function_base_name) = first.match_atom() {
                match function_base_name.as_str() {
                    "contract-call?" => {
                        let target_contract_id = if let Some(Value::Principal(PrincipalData::Contract(target_contract_id))) = lv.get(1).ok_or_else(|| Error::NotFound("No contract ID".into()))?.match_literal_value() {
                            // direct contract call
                            target_contract_id.clone()
                        }
                        else if let Some(trait_name) = lv.get(1).ok_or_else(|| Error::NotFound("No contract ID".into()))?.match_atom() {
                            // call to a trait reference.
                            // look it up
                            if let Some(func_traits) = self.trait_concretizations.get(func_name) {
                                // user already bound this particular symbol to a trait
                                // implementation
                                let Some(target_contract_id) = func_traits.get(trait_name) else {
                                    return Err(Error::NotFound(format!("Trait '{trait_name}' in function {func_name} is not concretized")));
                                };
                                target_contract_id.clone()
                            }
                            else {
                                // see if this trait reference is a function argument
                                let trait_ref = func_args.iter()
                                    .find(|(arg_name, _arg_type)| arg_name == trait_name)
                                    .map(|(arg_name, arg_type)| {
                                        let TypeSignature::CallableType(CallableSubtype::Trait(trait_ref)) = arg_type else {
                                            return Err(Error::Bug(format!("argument {arg_name} of {func_name} is not a trait reference")))
                                        };
                                        Ok(trait_ref.clone())
                                    })
                                    .ok_or_else(|| Error::NotFound(format!("Function {func_name} calls an unconcretized trait implementation `{trait_name}`")))??;

                                // find the default concretization 
                                let Some(target_contract_id) = self.default_trait_concretizations.get(&trait_ref) else {
                                    return Err(Error::NotFound(format!("No concretization for '{trait_name}' in {func_name}")));
                                };
                                target_contract_id.clone()
                            }
                        }
                        else {
                            return Err(Error::NotFound(format!("contract ID is not a literal value or an atom: {:?}", &lv.get(1))));
                        };

                        let Some(target_func_name) = lv.get(2).ok_or_else(|| Error::NotFound("No function name".into()))?.match_atom() else {
                            return Err(Error::NotFound(format!("contract-call function name not found: {:?}", &lv.get(2))));
                        };

                        self.load_defs(contracts, &target_contract_id)?;

                        let fq_name = FullName(target_contract_id.clone(), target_func_name.clone());
                        let Some(node) = self.reachable.get_mut(&func_name) else {
                            return Err(Error::Bug(format!("Unexplored function {function_base_name}")));
                        };

                        trace!("function {func_name} calls {fq_name}");
                        node.callable.push(CallgraphFunction::new(fq_name, body.span.start_line));
                    },
                    "map-insert"
                    | "map-set"
                    | "map-delete" => {
                        let Some(node) = self.reachable.get_mut(func_name) else {
                            return Err(Error::Bug(format!("bare map mutation {function_base_name} from {func_name}")));
                        };
                        let Some(map_name_atom) = lv.get(1) else {
                            return Err(Error::Bug(format!("map mutation {function_base_name} has no map name")));
                        };
                        let Some(map_name) = map_name_atom.match_atom() else {
                            return Err(Error::Bug(format!("map name in {function_base_name} is not an atom")));
                        };
                        
                        trace!("function {} mutates map {}", &func_name, map_name);
                        
                        let map_full_name = FullName(target_contract.clone(), map_name.clone());
                        node.add_writable_map(map_full_name.clone());
                    },
                    "map-get?" => {
                        let Some(node) = self.reachable.get_mut(func_name) else {
                            return Err(Error::Bug(format!("bare map access {function_base_name} from {func_name}")));
                        };
                        let Some(map_name_atom) = lv.get(1) else {
                            return Err(Error::Bug(format!("map access {function_base_name} has no map name")));
                        };
                        let Some(map_name) = map_name_atom.match_atom() else {
                            return Err(Error::Bug(format!("map name in {function_base_name} is not an atom")));
                        };
                        
                        trace!("function {} accesses map {}", &func_name, map_name);
                        
                        let map_full_name = FullName(target_contract.clone(), map_name.clone());
                        node.add_readable_map(map_full_name.clone());
                    }
                    "fold"
                    | "filter"
                    | "map" => {
                        let Some(node) = self.reachable.get_mut(func_name) else {
                            return Err(Error::Bug(format!("bare higher-order function {function_base_name} from {func_name}")));
                        };
                        let Some(called_func_name) = lv.get(1).ok_or_else(|| Error::Bug(format!("{function_base_name} missing function")))?.match_atom() else {
                            return Err(Error::Bug(format!("{function_base_name} missing function (not atom)")));
                        };
                        let fq_name = FullName(func_name.contract_id().clone(), called_func_name.clone());
                        trace!("function {func_name} calls {fq_name}");
                        node.callable.push(CallgraphFunction::new(fq_name, body.span.start_line));
                    }
                    "var-set" => {
                        let Some(node) = self.reachable.get_mut(func_name) else {
                            return Err(Error::Bug(format!("bare var-set from {func_name}")));
                        };
                        let Some(var_name_atom) = lv.get(1) else {
                            return Err(Error::Bug(format!("var-set has no var name")));
                        };
                        let Some(var_name) = var_name_atom.match_atom() else {
                            return Err(Error::Bug(format!("var name not an atom")));
                        };
                        
                        trace!("function {} mutates var {}", &func_name, var_name);
                        
                        let var_full_name = FullName(target_contract.clone(), var_name.clone());
                        node.add_writable_var(var_full_name);
                    },
                    "var-get" => {
                        let Some(node) = self.reachable.get_mut(func_name) else {
                            return Err(Error::Bug(format!("bare var-get from {func_name}")));
                        };
                        let Some(var_name_atom) = lv.get(1) else {
                            return Err(Error::Bug(format!("var-get has no var name")));
                        };
                        let Some(var_name) = var_name_atom.match_atom() else {
                            return Err(Error::Bug(format!("var name not an atom")));
                        };
                        
                        trace!("function {} accesses var {}", &func_name, var_name);

                        let var_full_name = FullName(target_contract.clone(), var_name.clone());
                        node.add_readable_var(var_full_name);
                    },
                    _ => {
                        let Some(sym_contract) = contracts.get(target_contract) else {
                            return Err(Error::NotFound(format!("No such contract {target_contract}")));
                        };

                        if sym_contract.contract_context.functions.get(function_base_name).is_some() {
                            let fq_name = FullName(func_name.contract_id().clone(), function_base_name.clone());
                            let Some(node) = self.reachable.get_mut(&func_name) else {
                                return Err(Error::Bug(format!("Unexplored function {function_base_name}")));
                            };
                            trace!("function {func_name} calls {fq_name}");
                            node.callable.push(CallgraphFunction::new(fq_name, body.span.start_line));
                        }
                        for ili in lv.iter() {
                            self.build(contracts, target_contract, func_name, func_args, &[ili.clone()])?;
                        }
                    }
                }
            }
            else {
                for ili in lv.iter() {
                    self.build(contracts, target_contract, func_name, func_args, &[ili.clone()])?;
                }
            }
        }
        Ok(())
    }

    /// Compute the set of reachable functions from a given function.
    /// Returns None if the function is not known.
    /// Functions are returned in post-order traversal -- the "furthest away" functions are first
    pub fn reachable_from(&self, func_name: &FullName) -> Result<Vec<FullName>, Error> {
        let mut reachable = vec![];
        let mut reachable_set = HashSet::new();
        let mut frontier = VecDeque::new();
        if !self.reachable.contains_key(func_name) {
            return Err(Error::NotFound(format!("{func_name}")));
        };

        frontier.push_back(func_name.clone());
        while let Some(func_name) = frontier.pop_front() {
            let Some(node) = self.reachable.get(&func_name) else {
                return Err(Error::Bug(format!("Unknown function {func_name}")));
            };

            for c in node.callable.iter() {
                if reachable_set.contains(c.call_name()) {
                    continue;
                }
                frontier.push_back(c.call_name().clone());
            }
            if !reachable_set.contains(&func_name) {
                reachable.push(func_name.clone());
            }
            reachable_set.insert(func_name.clone());
        }
        reachable.reverse();
        let _ = reachable.pop();
        Ok(reachable)
    }

    /// Get a callgraph node
    pub fn get_node(&self, func_name: &FullName) -> Option<&CallgraphNode> {
        self.reachable.get(func_name)
    }

    /// Get all functions defined in a given contract
    pub fn get_contract_functions(&self, contract_id: &QualifiedContractIdentifier) -> Vec<FullName> {
        self.reachable
            .keys()
            .filter_map(|k| if k.contract_id() == contract_id {
                Some(k.clone())
            }
            else {
                None
            })
            .collect()
    }
    
    /// Determine what map accesses a function could potentially cause
    pub fn reachable_map_accesses_from(&self, func_name: &FullName) -> Result<Vec<FullName>, Error> {
        let mut reachable_funcs = self.reachable_from(func_name)?;
        reachable_funcs.push(func_name.clone());
        let mut reachable_maps = HashSet::new();
        for reachable_func in reachable_funcs.iter() {
            let Some(node) = self.reachable.get(reachable_func) else {
                return Err(Error::Bug(format!("unreachable reachable function {reachable_func}")));
            };
            for map in node.map_reads.iter() {
                reachable_maps.insert(map.clone());
            }
        }
        Ok(reachable_maps.into_iter().collect())
    }

    /// Determine what map mutations a function could potentially cause
    pub fn reachable_map_mutations_from(&self, func_name: &FullName) -> Result<Vec<FullName>, Error> {
        let mut reachable_funcs = self.reachable_from(func_name)?;
        reachable_funcs.push(func_name.clone());
        let mut reachable_maps = HashSet::new();
        for reachable_func in reachable_funcs.iter() {
            let Some(node) = self.reachable.get(reachable_func) else {
                return Err(Error::Bug(format!("unreachable reachable function {reachable_func}")));
            };
            for map in node.map_writes.iter() {
                reachable_maps.insert(map.clone());
            }
        }
        Ok(reachable_maps.into_iter().collect())
    }
    
    /// Determine what var accesses a function could potentially cause
    pub fn reachable_var_accesses_from(&self, func_name: &FullName) -> Result<Vec<FullName>, Error> {
        let mut reachable_funcs = self.reachable_from(func_name)?;
        reachable_funcs.push(func_name.clone());
        let mut reachable_vars = HashSet::new();
        for reachable_func in reachable_funcs.iter() {
            let Some(node) = self.reachable.get(reachable_func) else {
                return Err(Error::Bug(format!("unreachable reachable function {reachable_func}")));
            };
            for var in node.var_reads.iter() {
                reachable_vars.insert(var.clone());
            }
        }
        Ok(reachable_vars.into_iter().collect())
    }
    
    /// Determine what var mutations a function could potentially cause
    pub fn reachable_var_mutations_from(&self, func_name: &FullName) -> Result<Vec<FullName>, Error> {
        let mut reachable_funcs = self.reachable_from(func_name)?;
        reachable_funcs.push(func_name.clone());
        let mut reachable_vars = HashSet::new();
        for reachable_func in reachable_funcs.iter() {
            let Some(node) = self.reachable.get(reachable_func) else {
                return Err(Error::Bug(format!("unreachable reachable function {reachable_func}")));
            };
            for var in node.var_writes.iter() {
                reachable_vars.insert(var.clone());
            }
        }
        Ok(reachable_vars.into_iter().collect())
    }

    /// Is a given function read-only? As in, it can _never_ mutate state?
    fn check_pure(&self, func_name: &FullName) -> Result<bool, Error> {
        Ok(self.reachable_map_accesses_from(func_name)?.len() == 0
           && self.reachable_map_mutations_from(func_name)?.len() == 0
           && self.reachable_var_accesses_from(func_name)?.len() == 0
           && self.reachable_var_mutations_from(func_name)?.len() == 0)
    }

    /// Report whether or not a given function is pure
    pub fn is_pure(&self, func_name: &FullName) -> Result<bool, Error> {
        let node = self.get_node(func_name).ok_or_else(|| Error::NotFound(format!("{func_name}")))?;
        Ok(node.is_pure)
    }

    pub fn view<'a>(&'a self, func_name: &FullName) -> Option<CallgraphView<'a>> {
        if self.reachable.get(func_name).is_none() {
            return None;
        }

        Some(CallgraphView {
            callgraph: self,
            cursor: func_name.clone()
        })
    }
}

/// Symbolic contract state
#[derive(Debug)]
pub struct SymContract {
    id: QualifiedContractIdentifier,
    typemap: TypeMap,
    symbols: Vec<SymbolicExpression>,
    contract_context: ContractContext,
    function_symexps: HashMap<ClarityName, SymbolicExpression>,
}

impl SymContract {
    fn extract_function_symexps(exprs: &[SymbolicExpression]) -> HashMap<ClarityName, SymbolicExpression> {
        let mut ret = HashMap::new();
        for expr in exprs {
            let Some(lv) = expr.match_list() else {
                continue;
            };
            if lv.len() < 2 {
                continue;
            }
            let Some(func_def_expr) = lv.get(0) else {
                continue;
            };
            let Some(func_body) = lv.get(1) else {
                continue;
            };
            let Some(func_def) = func_def_expr.match_atom() else {
                continue;
            };
            if func_def.as_str() != "define-public"
                && func_def.as_str() != "define-private"
                && func_def.as_str() != "define-read-only"
            {
                continue;
            }
            let Some(func_name_and_args) = func_body.match_list() else {
                continue;
            };
            let Some(func_name_expr) = func_name_and_args.get(0) else {
                continue;
            };
            let Some(func_name) = func_name_expr.match_atom() else {
                continue;
            };
            ret.insert(func_name.clone(), expr.clone());
        }
        ret
    }

    pub fn new(id: QualifiedContractIdentifier, typemap: TypeMap, symbols: Vec<SymbolicExpression>, contract_context: ContractContext) -> Self {
        let function_symexps = Self::extract_function_symexps(&symbols);
        Self {
            id,
            typemap,
            symbols,
            contract_context,
            function_symexps
        }
    }

    pub fn get_function_symexp(&self, name: &ClarityName) -> Option<&SymbolicExpression> {
        self.function_symexps.get(name)
    }
}

/// Symbolic execution engine configuration
#[derive(Debug, Clone)]
pub struct SymbexConfig {
    drop_early_returns: HashSet<FullName>,
    skip_function_calls: HashSet<FullName>,
    skip_contract_calls: HashSet<FullName>,
    skip_pure_calls: bool,
    skip_causally_independent_calls: bool,
    combine_continuations: bool,
    check_proofs: bool
}

impl SymbexConfig {
    pub fn new(symbex: &Symbex) -> Self {
        Self {
            drop_early_returns: symbex.drop_early_returns.clone(),
            skip_function_calls: symbex.skip_function_calls.clone(),
            skip_contract_calls: symbex.skip_contract_calls.clone(),
            skip_pure_calls: symbex.skip_pure_calls,
            skip_causally_independent_calls: symbex.skip_causally_independent_calls,
            combine_continuations: symbex.combine_continuations,
            check_proofs: symbex.check_proofs,
        }
    }

    pub fn empty() -> Self {
        Self {
            drop_early_returns: HashSet::new(),
            skip_function_calls: HashSet::new(),
            skip_contract_calls: HashSet::new(),
            skip_pure_calls: true,
            skip_causally_independent_calls: true,
            combine_continuations: true,
            check_proofs: true
        }
    }
}

/// Symbolic execution engine
#[derive(Debug)]
pub struct Symbex {
    /// in-RAM contract store
    datastore: BackingStore,
    /// contracts loaded, and their typemaps, symbols, and contexts
    contracts: HashMap<QualifiedContractIdentifier, SymContract>,
    /// table of reachable functions, maps, and vars
    pub callgraph: Option<Callgraph>,
    /// first tx-sender
    tx_sender: Option<SymOp>,
    /// first tx-sponsor
    tx_sponsor: Option<SymOp>,
    /// first contract-caller (when evaluating a specific function)
    contract_caller: Option<SymOp>,
    /// contract to be analyzed
    pub target_contract: QualifiedContractIdentifier,
    /// trait concretizations on a per-function, per-variable basis
    trait_concretizations: HashMap<FullName, HashMap<ClarityName, QualifiedContractIdentifier>>,
    default_trait_concretizations: HashMap<TraitIdentifier, QualifiedContractIdentifier>,
    /// option to skip evaluating all function calls
    explore_function_calls: bool,
    /// option to skip evaluating specific function calls
    skip_function_calls: HashSet<FullName>,
    /// option to skip evaluating specific contract-calls
    skip_contract_calls: HashSet<FullName>,
    /// option to skip function calls that do not do I/O and instead treat them as symbols
    skip_pure_calls: bool,
    /// option to skip function calls that do I/O that is causally independent of the
    /// currently-evaluating continuation
    skip_causally_independent_calls: bool,
    /// drop early-return continuations from the given functions
    drop_early_returns: HashSet<FullName>,
    /// cache of evaluated function calls, with all function arguments unbound.
    /// Maps the SymbolicExpression ID to the set of halting continuations
    evaluated_functions: HashMap<FullName, Vec<Continuation>>,
    /// combine continuations that have the same halting states and final formulae
    combine_continuations: bool,
    /// whether or not to abort on proof failure
    check_proofs: bool,
}

pub fn print_continuation(cont: &Continuation) {
    eprintln!("{cont}");
    let trace = cont.trace();
    eprintln!("Symbolic stack trace:\n{trace}");

    let halt = format!("{}", Halt::from(cont.clone()));
    let mut halt_strs = halt.split("\n");
    let mut halt_with_comments = vec![];
    while let Some(halt_str) = halt_strs.next() {
        halt_with_comments.push(format!(";;     {halt_str}"));
    }
    let halts = halt_with_comments.join("\n");
    eprintln!("Halt description:\n{halts}\n");
}


impl Symbex {
    /// Get a ref to a contract's typemap.
    pub fn typemap(&self, contract_id: &QualifiedContractIdentifier) -> Result<&TypeMap, Error> {
        self.contracts.get(contract_id).map(|sc| &sc.typemap).ok_or_else(|| Error::NotFound(format!("No such contract {contract_id}")))
    }

    /// Get a ref to a contract's context
    pub fn contract_context(&self, contract_id: &QualifiedContractIdentifier) -> Result<&ContractContext, Error> {
        self.contracts.get(contract_id).map(|sc| &sc.contract_context).ok_or_else(|| Error::NotFound(format!("No such contract {contract_id}")))
    }

    /// Get a ref to a contract's symbols
    pub fn symbols(&self, contract_id: &QualifiedContractIdentifier) -> Result<&[SymbolicExpression], Error> {
        self.contracts.get(contract_id).map(|sc| sc.symbols.as_slice()).ok_or_else(|| Error::NotFound(format!("No such contract {contract_id}")))
    }

    /// Get a ref to the callgraph
    pub fn callgraph(&self) -> &Callgraph {
        self.callgraph.as_ref().expect("FATAL: did not instantiate Symbex")
    }

    /// Get the symbolic expression of a function definition
    pub fn get_function_symexp(&self, fq_name: &FullName) -> Option<&SymbolicExpression> {
        let sym_contract = self.contracts.get(fq_name.contract_id())?;
        sym_contract.get_function_symexp(fq_name.name())
    }

    fn sequence_maxlen(ts: &TypeSignature) -> Result<usize, Error> {
        // type signature must be a sequence
        match ts {
            TypeSignature::SequenceType(SequenceSubtype::BufferType(buff_len)) => usize::try_from(u32::from(buff_len)).map_err(|_| Error::Bug("Coult not convert u32 to usize".into())),
            TypeSignature::SequenceType(SequenceSubtype::ListType(list_type_data)) => usize::try_from(list_type_data.get_max_len()).map_err(|_| Error::Bug("Could not convert u32 to usize".into())),
            TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(str_len))) => usize::try_from(u32::from(str_len)).map_err(|_| Error::Bug("Could not convert u32 to usize".into())),
            TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(str_len))) => usize::try_from(u32::from(str_len)).map_err(|_| Error::Bug("Could not convert u32 to usize".into())),
            _ => {
                return Err(Error::Bug("mapped sequence does not have a sequence type".into()));
            }
        }
    }

    /// simplify each continuation's predicate and formula.
    /// * eliminate unreachable continuations.
    /// * if we have a chain of linear continuations, then compress them.
    /// * if multiple continuations have the same halting state, combine them (unless told not to)
    fn reduce_continuations(&self, config: &SymbexConfig, conts: Vec<Continuation>) -> Vec<Continuation> {
        let mut filtered_conts : Vec<_> = conts
           .into_iter()
           .map(|mut c| {
               let p = c.predicate.clone();
               match p.simplify() {
                   Ok(p) => {
                       trace!("Continuation {} simplified predicate = {p}, old predicate = {}", c.id, &c.predicate);
                       c.predicate = p.clone();
                   }
                   Err(e) => {
                       panic!("failed to simplify predicate: {e:?}");
                   }
               }
               let f = c.final_formula.clone();
               match f.simplify() {
                   Ok(f) => {
                       trace!("Continuation {} simplified final formula = {f}, old final formula = {}", c.id, &c.final_formula);
                       c.final_formula = f.clone();
                   }
                   Err(e) => {
                       panic!("failed to simplify final formula: {e:?}");
                   }
               }
               c
           })
           .filter(|c| {
               if SymOp::Panic == c.final_formula {
                   debug!("Continuation {} ({}) always panics", c.id, c.get_function_path());
                   trace!("Continuation always panics:\n{c}");
               }

               if c.predicate != Predicate::False {
                   trace!("Retain continuation {}", c.id);
                   true
               }
               else {
                   debug!("Continuation {} ({}) is unreachable", c.id, c.get_function_path());
                   trace!("Continuation is unreachable:\n{c}");
                   false
               }
           })
           .collect();

        // assert that there are no dups
        let mut ids = HashSet::new();
        for cont in filtered_conts.iter() {
            if ids.contains(&cont.id) {
                panic!("Duplicate continuation: {}\n{}", &cont.id, &cont);
            }
            ids.insert(cont.id);
        }

        // assert that if the predicates match, then the rest of the continuation must match
        let mut by_pred : HashMap<Predicate, &Continuation> = HashMap::new();
        for cont in filtered_conts.iter() {
            if let Some(c) = by_pred.get(&cont.predicate) {
                // this has to be the same continuation, insofar as it must have the same final
                // formula, same effects, and same caller
                if c.final_formula != cont.final_formula
                    || c.pre_map_state != cont.pre_map_state
                    || c.map_state != cont.map_state
                    || c.map_tombstones != cont.map_tombstones
                    || c.pre_var_state != cont.pre_var_state
                    || c.var_state != cont.var_state
                    || c.caller != cont.caller {
                    error!("Two different continuations detected with the same halting state");
                    error!("First offending continuation:\n{c}");
                    error!("Second offending continuation:\n{cont}");
                    panic!();
                }
            }
            else {
                by_pred.insert(cont.predicate.clone(), cont);
            }
        }

        // remove linear chains of continuations by rolling them up.
        // map continuation ID to the number of children it has
        let mut considered = HashSet::new();
        loop {
            let mut children_counts = HashMap::new();
            let mut new_conts = vec![];
            let mut merge_count = 0;
            for cont in filtered_conts.iter() {
                let Some(parent) = cont.parent.as_ref() else {
                    continue;
                };
                let parent_id = parent.id;
                if considered.contains(&parent_id) {
                    continue;
                }
                if let Some(cnt) = children_counts.get_mut(&parent_id) {
                    *cnt += 1;
                }
                else {
                    children_counts.insert(parent_id, 1);
                }
            }
            for cont in filtered_conts.into_iter() {
                let Some(parent) = cont.parent.as_ref() else {
                    new_conts.push(cont);
                    continue;
                };
                let parent_id = parent.id;
                if considered.contains(&parent_id) {
                    new_conts.push(cont);
                    continue;
                }
                let children_count = *children_counts.get(&parent_id).expect(&format!("Unreachable -- no child count for parent cont {}", parent_id));
                if children_count > 1 {
                    considered.insert(parent_id);
                    new_conts.push(cont);
                    continue;
                }

                // have exactly one child. Merge them.
                let merged = cont.rollup_to(Some(parent_id));
                considered.insert(parent_id);
                new_conts.push(merged);

                merge_count += 1;
            }
            filtered_conts = new_conts;
            if merge_count == 0 {
                break;
            }
        }

        if config.combine_continuations {
            // try to combine continuations
            let cmp_final_formulae = |f1: &SymOp, f2: &SymOp| {
                f1 == f2
            };

            let merge_final_formulae = |mut formulae: Vec<SymOp>| {
                formulae.pop().expect("unreachable")
            };

            let mut combineable : HashMap<_, Vec<_>> = HashMap::new();
            let mut droppable = HashSet::new();
            for (i, cont_i) in filtered_conts.iter().enumerate() {
                if i + 1 >= filtered_conts.len() {
                    break;
                }

                for (j, cont_j) in filtered_conts[(i+1)..].iter().enumerate() {
                    if cont_i.can_combine_with(cont_j, cmp_final_formulae) {
                        debug!("continuation {} ({}) can combine with continuation {} ({})", cont_i.get_function_path(), cont_i.id, cont_j.get_function_path(), cont_j.id);
                        if let Some(combined) = combineable.get_mut(&i) {
                            combined.push(i + 1 + j);
                        }
                        else {
                            combineable.insert(i, vec![i + 1 + j]);
                        }

                        droppable.insert(i + 1 + j);
                    }
                }
            }

            let mut combined = vec![];
            for (i, cont) in filtered_conts.iter().enumerate() {
                let Some(js) = combineable.get(&i) else {
                    if !droppable.contains(&i) {
                        combined.push(cont.clone());
                    }
                    continue;
                };
                if droppable.contains(&i) {
                    continue;
                }

                let combineable : Vec<_> = filtered_conts.iter().enumerate().filter_map(|(idx, c)| if js.contains(&idx) { Some(c.clone()) } else { None }).collect();

                let c = filtered_conts[i].clone().combine(combineable, merge_final_formulae).expect("BUG: failed to combine continuation");
                combined.push(c);
            }

            return combined;
        }
        else {
            return filtered_conts;
        }
    }
    
    /// Apply all (@clairvoyance ..) commands for a symbolic expression and its computed
    /// continuations
    fn run_post_commands(&mut self, config: &SymbexConfig, body: &SymbolicExpression, mut original_cont: Continuation, continuations: &mut Vec<Continuation>) -> Result<(), Error> {
        if !config.check_proofs {
            return Ok(());
        }

        let mut command_context = CommandContext::new();
        let commands = command_context.eval(body)?;
        if commands.len() > 0 {
            debug!("Commands on {body}:");
            for cmd in commands.iter() {
                debug!("\n{cmd}");
            }
            debug!("End of commands");
        }
        else {
            return Ok(());
        }
       
        let mut halts = vec![];
        for command in commands.into_iter() {
            match command {
                Command::Halt(halt) => {
                    halts.push(halt);
                }
                Command::DropEarlyReturns => {
                    continuations.retain(|cont| !cont.early_return);
                }
                Command::SetResult(res) => {
                    for cont in continuations.iter_mut() {
                        cont.final_formula = res.clone();
                    }
                    original_cont.final_formula = res;
                }
                Command::Invariant(inv) => {
                    let mut failed = vec![];
                    for cont in continuations.iter() {
                        // see if this continuation's predicate implies the invariant
                        let bound_formulae = cont.get_bound_formulae();
                        let mut rewritten_inv = inv.clone();
                        for (sym_id, symop) in bound_formulae.into_iter() {
                            rewritten_inv = *rewritten_inv.bind_symbol(sym_id, symop);
                        }

                        // merge predicate with statements about maps and vars
                        let mut var_stmts = vec![];
                        let mut map_stmts = vec![];
                        for (var_name, var_val) in cont.var_state.iter() {
                            var_stmts.push(SymOp::Equals(vec![Box::new(SymOp::FetchVar(var_name.clone())), Box::new(var_val.clone())]));
                        }
                        for (map_name, map_state) in cont.map_state.iter() {
                            for (key_op, val_op) in map_state.iter() {
                                map_stmts.push(SymOp::Equals(vec![Box::new(SymOp::FetchEntry(map_name.clone(), Box::new(key_op.clone()))), Box::new(SymOp::ConsSome(Box::new(val_op.clone())))]));
                            }
                        }
                        for (map_name, tombstones) in cont.map_tombstones.iter() {
                            for key_op in tombstones.iter() {
                                map_stmts.push(SymOp::IsNone(Box::new(SymOp::FetchEntry(map_name.clone(), Box::new(key_op.clone())))));
                            }
                        }
                       
                        let mut full_predicate = cont.predicate.clone().as_symop();
                        for map_stmt in map_stmts.into_iter() {
                            full_predicate = full_predicate.and(map_stmt);
                        }
                        for var_stmt in var_stmts.into_iter() {
                            full_predicate = full_predicate.and(var_stmt);
                        }

                        trace!("Constructed full predicate:\n{}", &full_predicate);

                        full_predicate = full_predicate.simplify()?;

                        debug!("Full predicate:\n{}", &full_predicate);
                        debug!("Invariant:\n{}", &rewritten_inv);

                        let implies = SymOp::Or(vec![
                            Box::new(SymOp::Not(Box::new(full_predicate))),
                            Box::new(rewritten_inv)
                        ])
                        .simplify()?
                        .try_as_predicate()?;

                        debug!("Implication:\n{}", &implies.clone().as_symop());

                        if implies != Predicate::True {
                            failed.push(cont.clone());
                        }
                    }
                    if failed.len() > 0 {
                        return Err(Error::InvariantFailure(body.clone(), inv, failed));
                    }
                }
                Command::PrintProducedContinuations => {
                    eprintln!("=========== Begin produced continuations for {body}");
                    for (i, cont) in continuations.iter().enumerate() {
                        if i > 0 {
                            eprintln!("--------------------------------------------------------------");
                        }
                        print_continuation(cont);
                    }
                    eprintln!("=========== End of produced continuations for {body}");
                }
                _ => {
                    continue;
                }
            }
        }

        if halts.len() == 0 {
            // no proofs to check
            return Ok(());
        }

        let failures = ProofFailures::from_continuations_and_halts(continuations.to_vec(), halts)?;
        if !failures.is_empty() {
            debug!("Errors were encountered while checking invariants for {}", body);
            return Err(Error::ProofFailure(failures));
        }
        else {
            debug!("Proof checks passed on {body}");
        }

        Ok(())
    }
    
    fn make_config(&self, parent_config: &SymbexConfig) -> SymbexConfig {
        let mut new_config = SymbexConfig::new(self);
        new_config.drop_early_returns.extend(parent_config.drop_early_returns.clone().into_iter());
        new_config.skip_function_calls.extend(parent_config.skip_function_calls.clone().into_iter());
        new_config.skip_contract_calls.extend(parent_config.skip_contract_calls.clone().into_iter());
        new_config.skip_pure_calls = parent_config.skip_pure_calls;
        new_config.skip_causally_independent_calls = parent_config.skip_causally_independent_calls;
        new_config.combine_continuations = parent_config.combine_continuations;
        new_config.check_proofs = parent_config.check_proofs;
        new_config
    }

    fn get_contract_call_contract(&self, continuation: &Continuation, lv: &[SymbolicExpression]) -> Result<QualifiedContractIdentifier, Error> {
        let contract_principal = if let Some(Value::Principal(PrincipalData::Contract(contract_principal))) = lv.get(1).ok_or_else(|| Error::NotFound("No contract ID".into()))?.match_literal_value() {
            // direct contract call
            contract_principal.clone()
        }
        else if let Some(trait_name) = lv.get(1).ok_or_else(|| Error::NotFound("No contract ID".into()))?.match_atom() {
            // call to a trait reference.
            // look it up
            let cur_contract = continuation.get_current_contract_id();
            let fq_name = if let Some(cur_func) = continuation.current_function.as_ref() {
                FullName(cur_contract.clone(), cur_func.as_str().try_into()?)
            }
            else {
                FullName::root(cur_contract.clone())
            };

            let target_contract_id = if let Some(func_traits) = self.trait_concretizations.get(&fq_name) {
                let Some(target_contract_id) = func_traits.get(trait_name) else {
                    return Err(Error::NotFound(format!("Trait '{trait_name}' in function {fq_name} is not concretized")));
                };
                target_contract_id.clone()
            }
            else {
                return Err(Error::NotFound(format!("Function {fq_name} has no concretized traits")));
            };

            target_contract_id
        }
        else {
            return Err(Error::NotFound(format!("contract-call contract is not a literal value or an atom: {:?}", &lv.get(1))));
        };
        Ok(contract_principal)
    }
    
    /// Apply all (@clairvoyance ..) directives for a symbolic expression on this symbolic
    /// executor instance which apply prior to computing its continuations.
    fn run_pre_commands(&mut self, parent_config: &SymbexConfig, continuation: &Continuation, body: &SymbolicExpression) -> Result<SymbexConfig, Error> {
        let mut command_context = CommandContext::new();
        let commands = command_context.eval(body)?;
        if commands.len() > 0 {
            debug!("Commands on {body}:");
            for cmd in commands.iter() {
                debug!("\n{cmd}");
            }
            debug!("End of commands");
        }
        else {
            return Ok(parent_config.clone());
        }

        let mut config = self.make_config(parent_config);
       
        for command in commands.into_iter() {
            match command {
                Command::SkipFunctionCall(name_opt) => {
                    let name = if let Some(name) = name_opt {
                        name
                    }
                    else {
                        let Some(lv) = body.match_list() else {
                            return Err(Error::new_program_error(format!("`skip-function-call` without a name only applies to function call sites (in {body})")));
                        };
                        if lv.len() == 0 {
                            return Err(Error::new_program_error(format!("`skip-function-call` without a name only applies to function call sites (in {body})")));
                        }
                        let Some(name) = lv[0].match_atom() else {
                            return Err(Error::new_program_error(format!("`skip-function-call` without a name only applies to function call sites (in {body})")));
                        };
                        name.clone()
                    };
                    let fq_name = FullName(continuation.get_current_contract_id(), name.clone());
                    config.skip_function_calls.insert(fq_name);
                }
                Command::SkipContractCall(name_opt) => {
                    let fq_name = if let Some(fq_name) = name_opt {
                        fq_name
                    }
                    else {
                        let Some(lv) = body.match_list() else {
                            return Err(Error::new_program_error(format!("`skip-contract-call` without a name only applies to contract-call sites (in {body})")));
                        };
                        if lv.len() <= 2 {
                            return Err(Error::new_program_error(format!("`skip-contract-call` without a name only applies to contract-call sites (in {body})")));
                        }
                        let contract_principal = self.get_contract_call_contract(continuation, lv)?;
                        let Some(name) = lv[2].match_atom() else {
                            return Err(Error::new_program_error(format!("`skip-contract-call` without a name only applies to function call sites (in {body})")));
                        };
                        let fq_name = FullName(contract_principal, name.clone());
                        fq_name
                    };
                    config.skip_contract_calls.insert(fq_name);
                }
                Command::ExploreAll => {
                    config.combine_continuations = false;
                    config.skip_pure_calls = false;
                    config.skip_causally_independent_calls = false;
                }
                Command::PrintLn(expr) => {
                    let bound_formulae = continuation.get_bound_formulae();
                    let mut rewritten_expr = expr.clone();
                    for (sym_id, symop) in bound_formulae.into_iter() {
                        rewritten_expr = *rewritten_expr.bind_symbol(sym_id, symop);
                    }
                    let v = rewritten_expr.simplify()?;
                    eprintln!("{v}");
                }
                Command::PrintContinuation => {
                    print_continuation(&continuation);
                }
                Command::StopExploring => {
                    eprintln!("Stopping symbolic execution on explicit directive");
                    return Err(Error::Stopped);
                }
                Command::Pause(expr) => {
                    eprintln!("Symbolic execution paused at line {}", expr.span.start_line);
                    eprintln!("Current symbolic expression: {expr}");
                    eprintln!();
                    eprintln!("Press Return to continue");
                    let mut s = String::new();
                    let _ = match io::stdin().read_line(&mut s) {
                        Ok(_x) => _x,
                        Err(e) => match e.kind() {
                            io::ErrorKind::UnexpectedEof => {
                                continue;
                            }
                            _ => {
                                return Err(Error::Failed(format!("I/O error: {e:?}")));
                            }
                        }
                    };
                }
                _ => {
                    continue;
                }
            }
        }

        Ok(config)
    }
    
    fn eval_variadic_native<I, F>(&mut self, config: &SymbexConfig, continuation: Continuation, function_name: &str, args: &[SymbolicExpression], initial: I, fold: F) -> Result<Vec<Continuation>, Error> 
    where
        I: Fn(SymOp) -> SymOp,
        F: Fn(SymOp, SymOp) -> SymOp
    {
        let mut left_conts_opt : Option<Vec<Continuation>> = None;

        let continuation_rc = Rc::new(continuation);
        for symexp in args.iter() {
            if let Some(left_conts) = left_conts_opt.take() {
                let mut right_conts = vec![];
                for left_cont in left_conts.into_iter() {
                    if left_cont.halted() {
                        right_conts.push(left_cont);
                        continue;
                    }
                    let left_cont_formula = left_cont.final_formula.clone();
                    let left_cont_predicate = left_cont.predicate.clone();
                    let mut conts = self.eval(&config, Continuation::from_parent(Rc::new(left_cont), function_name.to_string(), symexp.span.start_line), symexp)?;
                    for cont in conts.iter_mut() {
                        if cont.halted() {
                            continue;
                        }

                        let final_formula = fold(left_cont_formula.clone(), cont.final_formula.clone());
                        let predicate = left_cont_predicate.clone().and(cont.predicate.clone());
                        cont.predicate = predicate.simplify()?;
                        cont.final_formula = final_formula.simplify()?;
                    }
                    right_conts.extend(conts.into_iter());
                }
                left_conts_opt = Some(self.reduce_continuations(config, right_conts));
            }
            else {
                let mut conts = self.eval(config, Continuation::from_parent(continuation_rc.clone(), function_name.to_string(), symexp.span.start_line), symexp)?;
                for cont in conts.iter_mut() {
                    if cont.halted() {
                        continue;
                    }
                    cont.final_formula = initial(cont.final_formula.clone()).simplify()?;
                }
                left_conts_opt = Some(self.reduce_continuations(config, conts));
            }
        }
        let Some(conts) = left_conts_opt.take() else {
            return Err(Error::Bug(format!("No continuations produced from {args:?}")));
        };
        Ok(self.reduce_continuations(config, conts))
    }

    /// eval_variadic_native, but where the initial constructor is an identity
    fn eval_foldable_native<F>(&mut self, config: &SymbexConfig, continuation: Continuation, function_name: &str, args: &[SymbolicExpression], fold: F) -> Result<Vec<Continuation>, Error> 
    where
        F: Fn(SymOp, SymOp) -> SymOp
    {
        self.eval_variadic_native(config, continuation, function_name, args, |initial| initial, fold)
    }

    fn eval_native_1arg<C>(&mut self, config: &SymbexConfig, continuation: Continuation, function_name: &str, arg: SymbolicExpression, cons: C) -> Result<Vec<Continuation>, Error>
    where
        C: Fn(SymOp) -> SymOp
    {
        self.eval_variadic_native(config, continuation, function_name, &[arg], cons, |_, _| unreachable!())
    }
    
    fn eval_native_2args<C>(&mut self, config: &SymbexConfig, continuation: Continuation, function_name: &str, arg1: SymbolicExpression, arg2: SymbolicExpression, cons: C) -> Result<Vec<Continuation>, Error>
    where
        C: Fn(SymOp, SymOp) -> SymOp
    {
        self.eval_variadic_native(config, continuation, function_name, &[arg1, arg2], |initial| initial, cons)
    }
    
    fn eval_native_n_args<C>(&mut self, config: &SymbexConfig, continuation: Continuation, function_name: &str, args: &[SymbolicExpression], cons: C) -> Result<Vec<Continuation>, Error>
    where
        C: Fn(Vec<SymOp>) -> SymOp
    {
        let mut ret = vec![];
        let mut conts = vec![(vec![], continuation)];
        for arg in args {
            let mut next_conts = vec![];
            for (arg_formulae, cont) in conts.into_iter() {
                if cont.halted() {
                    ret.push(cont);
                    continue;
                }

                let parent_rc = Rc::new(cont);
                let new_conts = self.eval(config, Continuation::from_parent(parent_rc, function_name.to_string(), arg.span.start_line), arg)?;

                for new_cont in new_conts.into_iter() {
                    if new_cont.halted() {
                        ret.push(new_cont);
                        continue;
                    }
                    if new_cont.predicate.clone().simplify()? == Predicate::False {
                        ret.push(new_cont);
                        continue;
                    }

                    let mut new_args = arg_formulae.clone();
                    new_args.push(new_cont.final_formula.clone().simplify()?);

                    next_conts.push((new_args, new_cont));
                }
            }
            conts = next_conts;
        }
        
        // construct final formulae and predicates
        let mut ret = vec![];
        for (formulae, mut cont) in conts.into_iter() {
            if cont.halted() {
                ret.push(cont);
                continue;
            }
            if cont.predicate.clone().simplify()? == Predicate::False {
                ret.push(cont);
                continue;
            }

            cont.final_formula = cons(formulae);
            ret.push(cont);
        }
        
        Ok(ret)
    }

    fn eval_native_3args<C>(&mut self, config: &SymbexConfig, continuation: Continuation, function_name: &str, arg1: SymbolicExpression, arg2: SymbolicExpression, arg3: SymbolicExpression, cons: C) -> Result<Vec<Continuation>, Error>
    where
        C: Fn(SymOp, SymOp, SymOp) -> SymOp
    {
        self.eval_native_n_args(config, continuation, function_name, &[arg1, arg2, arg3], |mut args| {
            let arg2 = args.pop().expect("infallible");
            let arg1 = args.pop().expect("infallible");
            let arg0 = args.pop().expect("infallible");
            cons(arg0, arg1, arg2)
        })
    }

    /// Try to evaluate a causally-independent function.
    /// Used both for direct function-calls, and for higher-order function calls.
    /// In the first case, `arg_symbols_opt` should be Some(..), so the code here can bind all
    /// arguments to symbols in `binding_cont`.
    /// In the latter case, `arg_symbols_opt` should be None, and the caller should have already
    /// bound all arguments to symbols prior to calling.
    fn try_eval_causally_independent_contract_function(&mut self, config: &SymbexConfig, function_base_name: &ClarityName, binding_cont: Continuation, arg_symbols_opt: Option<&[SymbolicExpression]>, start_line: u32) -> Result<Result<Vec<Continuation>, Continuation>, Error> {
        let cur_contract = binding_cont.get_current_contract_id();
        let parent_func = binding_cont.function_path.clone().unwrap_or("".to_string());
        let function_name = format!("{parent_func}/{}", &function_base_name);
        let fq_name = FullName(cur_contract.clone(), function_base_name.clone());

        // can we skip this, or shorten our consideration?
        let is_pure = self.callgraph().is_pure(&fq_name)?;
        let is_root = binding_cont.caller.is_none();

        let is_causally_independent = binding_cont.is_causally_independent(&fq_name, &self.callgraph())?;
        if !self.explore_function_calls
            || config.skip_function_calls.contains(&fq_name)
            || (!is_root && is_pure && config.skip_pure_calls)
            || (!is_root && is_causally_independent && config.skip_causally_independent_calls)
        {
            if !is_root && is_pure && config.skip_pure_calls {
                debug!("Will not evaluate function {fq_name} from continuation {}, since it is pure", binding_cont.id);
            }
            if !is_root && is_causally_independent && config.skip_causally_independent_calls {
                debug!("Will not evaluate function {fq_name} from continuation {}, since it is causally independent", binding_cont.id);
            }

            // skip this; treat this function call as a symbol
            let skip_conts = if let Some(arg_symbols) = arg_symbols_opt {
                let parent_rc = Rc::new(binding_cont);
                let skip_cont = Continuation::from_parent(parent_rc, format!("{function_name}.skipped"), start_line);

                let mut skip_conts = vec![vec![(skip_cont, vec![])]];

                // evaluate each argument 
                for (i, arg) in arg_symbols.get(1..).unwrap_or(&[]).iter().enumerate() {
                    let mut next_skip_conts = vec![];
                    for skip_cont_set in skip_conts.into_iter() {
                        let mut next_skip_cont_set = vec![];
                        for (skip_cont, args_so_far) in skip_cont_set.into_iter() {
                            if skip_cont.halted() {
                                let mut args = args_so_far.clone();
                                args.push(Box::new(skip_cont.final_formula.clone()));
                                next_skip_cont_set.push(vec![(skip_cont, args)]);
                                continue;
                            }
                            let next_conts = self.eval(config, Continuation::from_parent(Rc::new(skip_cont), format!("{function_name}.skipped/arg[{i}]"), arg.span.start_line), arg)?;
                            let next_conts_and_args : Vec<_> = next_conts
                                .into_iter()
                                .map(|cont| {
                                    let mut args = args_so_far.clone();
                                    args.push(Box::new(cont.final_formula.clone()));
                                    (cont, args)
                                })
                                .collect();

                            next_skip_cont_set.push(next_conts_and_args);
                        }
                        next_skip_conts.extend(next_skip_cont_set.into_iter());
                    }
                    skip_conts = next_skip_conts;
                }
                skip_conts
            }
            else {
                // synthesize arg symops
                let Some(func) = self.contract_context(&cur_contract)?.functions.get(function_base_name) else {
                    return Err(Error::Bug(format!("Missing function {function_base_name} in {cur_contract}")));
                };
                let mut arg_symops = vec![];
                for (arg_name, arg_type) in func.arguments.iter().zip(func.arg_types.iter()) {
                    let sym = Sym::from_name_and_type_signature(arg_name, arg_type);
                    arg_symops.push(Box::new(SymOp::Variable(sym)));
                }

                vec![vec![(binding_cont, arg_symops)]]
            };

            // final continuation treats the function as a symbol
            let mut final_conts = vec![];
            for skip_cont_set in skip_conts.into_iter() {
                for (skip_cont, args) in skip_cont_set.into_iter() {
                    if skip_cont.halted() {
                        final_conts.push(skip_cont);
                        continue;
                    }
                    let mut final_cont = Continuation::from_parent(Rc::new(skip_cont), format!("{function_name}.skipped/return"), start_line);
                    final_cont.add_reachable_storage_accesses(&fq_name, &self.callgraph())?;
                    final_cont.final_formula = SymOp::FunctionCall(fq_name.clone(), args);
                    final_conts.push(final_cont);
                }
            }
            return Ok(Ok(self.reduce_continuations(config, final_conts)));
        }
        else {
            return Ok(Err(binding_cont))
        }
    }

    /// Evaluate a pre-computed continuation.
    /// * `function_base_name` is the unqualified name of the function to evaluate in the current
    /// contract
    /// * `binding_cont` is the continuation in which the function's argument names will be bound to
    /// SymOps
    /// * `arg_symbols_opt` is the optional list of function argument symbolic expressions.  If this
    /// is None, then the argument names for this function must already be bound in `binding_cont`
    /// (or this call will error out)
    /// * `start_line` is the line number of the callsite.
    fn eval_precomputed_contract_function(&mut self, config: &SymbexConfig, function_base_name: &ClarityName, binding_cont: Continuation, arg_symbols_opt: Option<&[SymbolicExpression]>, start_line: u32) -> Result<Vec<Continuation>, Error> {
        let cur_contract = binding_cont.get_current_contract_id();
        let parent_func = binding_cont.function_path.clone().unwrap_or("".to_string());
        let function_name = format!("{parent_func}/{}", &function_base_name);
        let fq_name = FullName(cur_contract.clone(), function_base_name.clone());
        
        let Some(func) = self.contract_context(&cur_contract)?.functions.get(function_base_name).cloned() else {
            return Err(Error::NotFound(format!("No such function {function_base_name} in {cur_contract}")));
        };

        // going to evaluate a pre-evaluated function.
        // bind each bound formula in this continuation to the simplified
        // final formula and simplified final predicate.
        let is_root = binding_cont.caller.is_none();
        let mut evaled_conts = vec![vec![(binding_cont, vec![])]];
        let mut final_conts = vec![];

        if let Some(arg_symbols) = arg_symbols_opt.as_ref() {
            for (i, arg) in arg_symbols.get(1..).unwrap_or(&[]).iter().enumerate() {
                let mut next_evaled_conts = vec![];
                for evaled_cont_set in evaled_conts.into_iter() {
                    let mut next_evaled_cont_set = vec![];
                    for (evaled_cont, args_so_far) in evaled_cont_set.into_iter() {
                        if evaled_cont.halted() {
                            final_conts.push(evaled_cont);
                            continue;
                        }
                        let next_conts = self.eval(config, Continuation::from_parent(Rc::new(evaled_cont), format!("{function_name}.evaled/arg[{i}]"), arg.span.start_line), arg)?;
                        let next_conts_and_args : Vec<_> = next_conts
                            .into_iter()
                            .map(|cont| {
                                let mut args = args_so_far.clone();
                                args.push(Box::new(cont.final_formula.clone()));
                                (cont, args)
                            })
                            .collect();

                        next_evaled_cont_set.push(next_conts_and_args);
                    }
                    next_evaled_conts.extend(next_evaled_cont_set.into_iter());
                }
                evaled_conts = next_evaled_conts;
            }
        }

        for evaled_cont_set in evaled_conts.into_iter() {
            for (evaled_cont, args) in evaled_cont_set.into_iter() {
                if evaled_cont.halted() {
                    final_conts.push(evaled_cont);
                    continue;
                }
                let binding_cont = if arg_symbols_opt.is_some() {
                    // need to bind
                    if args.len() != func.arguments.len() {
                        return Err(Error::Bug(format!("Computed arguments ({}) does not match function type signature ({}) for {fq_name}", args.len(), func.arguments.len())));
                    }

                    let mut binding_cont = Continuation::from_parent(Rc::new(evaled_cont), format!("{function_name}.evaled/bind"), start_line);
                    // NOTE: no need to unbind these symbols later, since the
                    // continuation produced by Continuation::from_evaluated()
                    // will not have any bound formulae (its final formula,
                    // predicate, and state will instead have their free
                    // variables bound to symops in the binding continuation)
                    for (arg_name, arg_symop) in func.arguments.iter().zip(args.iter()) {
                        binding_cont.bind_symop(arg_name, (*arg_symop.clone()).simplify()?);
                    }
                    binding_cont
                }
                else {
                    // already bound; evaled_conts contains only the given binding continuation
                    evaled_cont
                };

                let binding_cont_id = binding_cont.id;
                let binding_cont_rc = Rc::new(binding_cont);
                let mut pushed = 0;
                let Some(precomputed_conts) = self.evaluated_functions.get(&fq_name) else {
                    return Err(Error::Bug(format!("No precomputed continuations for {fq_name}")));
                };
                for cont in precomputed_conts.iter() {
                    let eval_cont = Continuation::from_evaluated(cont, format!("{function_name}.evaled"), binding_cont_rc.clone())?;
                    if eval_cont.panicking {
                        debug!("Continuation {} (id {}) panics", eval_cont.get_function_path(), eval_cont.id);
                        final_conts.push(eval_cont);
                        continue;
                    }
                    if eval_cont.predicate == Predicate::False {
                        debug!("Continuation {} (id {}) is unreachable", eval_cont.get_function_path(), eval_cont.id);
                        continue;
                    }

                    if !eval_cont.early_return && !is_root && config.skip_causally_independent_calls && binding_cont_rc.is_read_independent(&eval_cont)? && cont.is_read_only_so_far() {
                        debug!("Will not evaluate function {fq_name} in continuation {} from free continuation {}, since it is causally read-independent of binding continuation {}", eval_cont.id, cont.id, binding_cont_rc.id);
                        continue;
                    }

                    if config.drop_early_returns.contains(&fq_name) && eval_cont.early_return {
                        debug!("Will not evaluate early-return continuation {} (free continuation {}) of {fq_name}", eval_cont.id, cont.id);
                        continue;
                    }

                    let return_cont = Continuation::from_callee(Rc::new(eval_cont), format!("{function_name}.evaled/return"), func.body.span.start_line);
                    final_conts.push(return_cont);
                    pushed += 1;
                }
                if pushed == 0 {
                    // all continuations are read-independent of the
                    // binding continuation, so we can skip
                    debug!("All continuations of {fq_name} are read-independent of continuation {}", binding_cont_id);
                    let mut final_cont = Continuation::from_parent(binding_cont_rc, format!("{function_name}.eval-skipped/return"), start_line);
                    final_cont.add_reachable_storage_accesses(&fq_name, &self.callgraph())?;
                    final_cont.final_formula = SymOp::FunctionCall(fq_name.clone(), args);
                    final_conts.push(final_cont);
                }
            }
        }
        Ok(self.reduce_continuations(config, final_conts))
    }
    
    /// Call a function within a contract
    fn eval_contract_function(&mut self, config: &SymbexConfig, continuation: Continuation, function_base_name: &ClarityName, lv: &[SymbolicExpression], start_line: u32) -> Result<Result<Vec<Continuation>, Continuation>, Error> {
        let cur_contract = continuation.get_current_contract_id();
        let fq_name = FullName(cur_contract.clone(), function_base_name.clone());

        if self.contract_context(&cur_contract)?.functions.get(function_base_name).is_some() {
            let continuation = match self.try_eval_causally_independent_contract_function(config, function_base_name, continuation, Some(lv), start_line) {
                Ok(Ok(conts)) => {
                    return Ok(Ok(conts));
                }
                Ok(Err(cont)) => cont,
                Err(e) => {
                    return Err(e);
                }
            };

            if self.evaluated_functions.get(&fq_name).is_some() {
                let evaled_conts = self.eval_precomputed_contract_function(config, function_base_name, continuation, Some(lv), start_line)?;
                Ok(Ok(evaled_conts))
            }
            else {
                return self.apply_user_function(config, continuation, function_base_name, lv.get(1..).unwrap_or(&[]))
                    .map(|conts| Ok(conts));
            }
        }
        else {
            if function_base_name.len() > 20 {
                debug!("Not a contract function: {fq_name}");
            }
            return Ok(Err(continuation));
        }
    }

    /// Call a user function in the contract as part of a map, filter, or fold
    fn eval_shortcircuit_higher_order_contract_function(&mut self, config: &SymbexConfig, function_base_name: &ClarityName, binding_cont: Continuation, start_line: u32) -> Result<Result<Vec<Continuation>, Continuation>, Error> {
        let cur_contract = binding_cont.get_current_contract_id();
        let fq_name = FullName(cur_contract.clone(), function_base_name.clone());

        let continuation = match self.try_eval_causally_independent_contract_function(config, function_base_name, binding_cont, None, start_line) {
            Ok(Ok(conts)) => {
                return Ok(Ok(conts));
            }
            Ok(Err(cont)) => cont,
            Err(e) => {
                return Err(e);
            }
        };

        if self.evaluated_functions.get(&fq_name).is_some() {
            let evaled_conts = self.eval_precomputed_contract_function(config, function_base_name, continuation, None, start_line)?;
            return Ok(Ok(evaled_conts));
        }
        else {
            return Ok(Err(continuation));
        }
    }

    /// Given an atom, try to evaluate it to a built-in symbol
    pub fn try_atom_as_symbol<C: GetContractSymOps>(cont: &C, cn: &ClarityName) -> Result<Option<SymOp>, Error> {
        let sym_opt = match cn.as_str() {
            "true" => Some(SymOp::Constant(Value::Bool(true))),
            "false" => Some(SymOp::Constant(Value::Bool(false))),
            "none" => Some(SymOp::none()),
            "tx-sender" => Some(cont.get_tx_sender_symop()),
            "contract-caller" => Some(cont.get_contract_caller_symop()),
            "block-height" => {
                return Err(Error::Bug("`block-height` is not supported anymore".into()));
            },
            "burn-block-height" => Some(SymOp::Variable(Sym::UInt("burn-block-height".into()))),
            "stx-liquid-supply" => Some(SymOp::Variable(Sym::UInt("stx-liquid-supply".into()))),
            "is-in-regtest" => Some(SymOp::Variable(Sym::Bool("is-in-regtest".into()))),
            "tx-sponsor?" => Some(cont.get_tx_sponsor_symop()),
            "is-in-mainnet" => Some(SymOp::Variable(Sym::Bool("is-in-mainnet".into()))),
            "chain-id" => Some(SymOp::Variable(Sym::UInt("chain-id".into()))),
            "stacks-block-height" => Some(SymOp::Variable(Sym::UInt("stacks-block-height".into()))),
            "tenure-height" => Some(SymOp::Variable(Sym::UInt("tenure-height".into()))),
            "stacks-block-time" => Some(SymOp::Variable(Sym::UInt("stacks-block-time".into()))),
            "current-contract" => Some(cont.get_current_contract_symop()),
            _ => None
        };
        Ok(sym_opt)
    }

    pub fn eval(&mut self, parent_config: &SymbexConfig, mut continuation: Continuation, body: &SymbolicExpression) -> Result<Vec<Continuation>, Error> {
        if continuation.halted() {
            return Ok(vec![continuation]);
        }
        let original_continuation = continuation.clone();
        let config = self.run_pre_commands(parent_config, &continuation, body)?;

        trace!("Simplify continuation {} predicate {}", continuation.id, &continuation.predicate);
        let pred = continuation.predicate.clone().simplify()?;
        if pred == Predicate::False {
            // this is unreachable anyway
            return Ok(vec![]);
        }
        debug!("Evaluating continuation {}\ncurrent contract: {}\n   function name: {}\n            body: {}\n       predicate: {}\n", continuation.id, &continuation.get_current_contract_id(), continuation.get_function_path(), &body.expr, &pred);
        if continuation.id <= last_cont_id() {
            return Err(Error::Bug(format!("Tried to evaluate a continuation twice: {} (at {})", continuation.id, last_cont_id())));
        }
        set_last_cont_id(continuation.id);
        let cur_contract = continuation.get_current_contract_id();
        let cont_id = continuation.id;
        let cont_path = continuation.get_function_path();

        let continuations = match &body.expr {
            SymbolicExpressionType::LiteralValue(v) => {
                let parent_func = continuation.function_path.clone().unwrap_or("".to_string());
                let function_name = format!("{parent_func}/{}", &v);
                continuation.function_path = Some(function_name);
                continuation.final_formula = SymOp::Constant(v.clone());
                vec![continuation]
            }
            SymbolicExpressionType::List(lv) => {
                if let Some(first) = lv.first() && let Some(function_base_name) = first.match_atom() {
                    let conts_res = self.eval_contract_function(&config, continuation, function_base_name, lv, body.span.start_line)?;
                    let conts = match conts_res {
                        Ok(conts) => conts,
                        Err(mut continuation) => {
                            // native function application
                            let parent_func = continuation.function_path.clone().unwrap_or("".to_string());
                            let function_name = format!("{parent_func}/{}", &function_base_name);
                            match function_base_name.as_str() {
                                "+" => {
                                    self.eval_foldable_native(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1..).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?,
                                        |left, right| left.add(right)
                                    )?
                                }
                                "-" => {
                                    self.eval_foldable_native(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1..).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?,
                                        |left, right| left.subtract(right)
                                    )?
                                }
                                "*" => {
                                    self.eval_foldable_native(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1..).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?,
                                        |left, right| left.multiply(right)
                                    )?
                                }
                                "/" => {
                                    self.eval_foldable_native(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1..).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?,
                                        |left, right| left.divide(right)
                                    )?
                                }
                                "to-int" => {
                                    self.eval_native_1arg(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::ToInt(Box::new(initial))
                                    )?
                                }
                                "to-uint" => {
                                    self.eval_native_1arg(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::ToUInt(Box::new(initial))
                                    )?
                                }
                                "mod" => {
                                    self.eval_native_2args(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing argument 1 to {function_name}")))?.clone(),
                                        lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.clone(),
                                        |left, right| SymOp::Modulo(Box::new(left), Box::new(right))
                                    )?
                                }
                                "pow" => {
                                    self.eval_native_2args(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing argument 1 to {function_name}")))?.clone(),
                                        lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.clone(),
                                        |left, right| SymOp::Power(Box::new(left), Box::new(right))
                                    )?
                                }
                                "sqrti" => {
                                    self.eval_native_1arg(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::Sqrti(Box::new(initial))
                                    )?
                                }
                                "log2" => {
                                    self.eval_native_1arg(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::Log2(Box::new(initial))
                                    )?
                                }
                                "and" => {
                                    self.eval_foldable_native(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1..).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?,
                                        |left, right| left.and(right)
                                    )?
                                }
                                "or" => {
                                    self.eval_foldable_native(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1..).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?,
                                        |left, right| left.or(right)
                                    )?
                                }
                                "not" => {
                                    self.eval_native_1arg(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::Not(Box::new(initial))
                                    )?
                                }
                                ">" => {
                                    self.eval_native_2args(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing argument 1 to {function_name}")))?.clone(),
                                        lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.clone(),
                                        |left, right| SymOp::Greater(Box::new(left), Box::new(right))
                                    )?
                                }
                                ">=" => {
                                    self.eval_native_2args(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing argument 1 to {function_name}")))?.clone(),
                                        lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.clone(),
                                        |left, right| SymOp::Geq(Box::new(left), Box::new(right))
                                    )?
                                }
                                "is-eq" => {
                                    self.eval_variadic_native(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1..).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?,
                                        |initial| initial,
                                        |left, right| left.equals(right)
                                    )?
                                }
                                "<=" => {
                                    self.eval_native_2args(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing argument 1 to {function_name}")))?.clone(),
                                        lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.clone(),
                                        |left, right| SymOp::Leq(Box::new(left), Box::new(right))
                                    )?
                                }
                                "<" => {
                                    self.eval_native_2args(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing argument 1 to {function_name}")))?.clone(),
                                        lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.clone(),
                                        |left, right| SymOp::Less(Box::new(left), Box::new(right))
                                    )?
                                }
                                "append" => {
                                    self.eval_native_2args(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing argument 1 to {function_name}")))?.clone(),
                                        lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.clone(),
                                        |left, right| SymOp::Append(Box::new(left), Box::new(right))
                                    )?
                                }
                                "concat" => {
                                    self.eval_foldable_native(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1..).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?,
                                        |left, right| left.concat(right)
                                    )?
                                }
                                "as-max-len?" => {
                                    // treat `(as-max-len? x y)` where `(len x)` is z like
                                    // `(if (> (len x) y) none (some x))`
                                    // where we modify `(some x)` to have len y instead of z.
                                    //
                                    // HOWEVER, we must take care in how we evaluate this!  In
                                    // particular, we cannot eval `x` twice -- it only gets eval'ed
                                    // once.

                                    let Some(list_sym) = lv.get(1).cloned() else {
                                        return Err(Error::Bug(format!("Missing argument 1 to {function_name}")));
                                    };
                                    let Some(new_len_sym) = lv.get(2).cloned() else {
                                        return Err(Error::Bug(format!("Missing argument 2 of {function_name}")));
                                    };

                                    // NOTE: `new_len_sym` is always a UInt constant
                                    let mut len_cont = self.eval(&config, Continuation::from_parent(Rc::new(continuation), format!("{function_name}.max-len"), new_len_sym.span.start_line), &new_len_sym)?; 
                                    if len_cont.len() != 1 {
                                        return Err(Error::Bug(format!("as-max-len? length evaluation had {} continuation(s); expected 1. Symexp was {}", len_cont.len(), &new_len_sym)));
                                    }
                                    let Some(len_cont) = len_cont.pop() else {
                                        return Err(Error::Bug("unreachable -- len_cont.len() == 1 but pop failed".into()));
                                    };

                                    let SymOp::Constant(Value::UInt(x)) = len_cont.final_formula else {
                                        return Err(Error::Bug("as-max-len? length evalauation was not a uint constant".into()));
                                    };

                                    // now we can evaluate the list
                                    let list_conts = self.eval(&config, Continuation::from_parent(Rc::new(len_cont), format!("{function_name}.list"), list_sym.span.start_line), &list_sym)?;

                                    // if y is greater than or equal to the maximum length of x,
                                    // then this will always succeed
                                    let sz = if let Some(ts) = self.typemap(&cur_contract)?.get_type_expected(&list_sym) {
                                        Self::sequence_maxlen(ts)?
                                    }
                                    else {
                                        return Err(Error::Bug(format!("No type information for sequence {list_sym:?}")));
                                    };
                                    let sz = u128::try_from(sz).map_err(|_| Error::Bug("Maximum sequence size does not fit into u128".into()))?;

                                    let mut new_conts = vec![];
                                    for list_cont in list_conts.into_iter() {
                                        if list_cont.halted() {
                                            new_conts.push(list_cont);
                                            continue;
                                        }

                                        let parent_final_formula = list_cont.final_formula.clone();
                                        let parent_predicate = list_cont.predicate.clone();
                                        let parent_rc = Rc::new(list_cont);

                                        // case 1: the sequence's length is less than or equal to the
                                        // given length
                                        let mut some_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}.case-some-seq"), body.span.start_line);
                                        some_cont.final_formula = SymOp::ConsSome(Box::new(parent_final_formula.clone()));
                                        some_cont.predicate = parent_predicate.clone().and(Predicate::Leq(SymOp::Len(Box::new(parent_final_formula.clone())), SymOp::Constant(Value::UInt(x))));

                                        new_conts.push(some_cont);

                                        // case 2: the sequence's length is greater than the given
                                        // length. Only need this if the sequence's maximum length
                                        // is greater than the new_len
                                        if sz < x {
                                            // we're growing this list size
                                            continue;
                                        }

                                        let mut none_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}.case-none-seq"), body.span.start_line);
                                        none_cont.final_formula = SymOp::none();
                                        none_cont.predicate = parent_predicate.and(Predicate::Greater(SymOp::Len(Box::new(parent_final_formula)), SymOp::Constant(Value::UInt(x))));

                                        new_conts.push(none_cont);
                                    }

                                    new_conts
                                }
                                "len" => {
                                    self.eval_native_1arg(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::Len(Box::new(initial))
                                    )?
                                },
                                "element-at?" | "element-at" => {
                                    self.eval_native_2args(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing argument 1 to {function_name}")))?.clone(),
                                        lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.clone(),
                                        |left, right| SymOp::ElementAt(Box::new(left), Box::new(right))
                                    )?
                                }
                                "index-of" | "index-of?" => {
                                    self.eval_native_2args(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing argument 1 to {function_name}")))?.clone(),
                                        lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.clone(),
                                        |left, right| SymOp::IndexOf(Box::new(left), Box::new(right))
                                    )?
                                }
                                "buff-to-int-le" => {
                                    self.eval_native_1arg(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::BuffToIntLe(Box::new(initial))
                                    )?
                                }
                                "buff-to-uint-le" => {
                                    self.eval_native_1arg(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::BuffToUIntLe(Box::new(initial))
                                    )?
                                }
                                "buff-to-int-be" => {
                                    self.eval_native_1arg(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::BuffToIntBe(Box::new(initial))
                                    )?
                                }
                                "buff-to-uint-be" => {
                                    self.eval_native_1arg(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::BuffToUIntBe(Box::new(initial))
                                    )?
                                }
                                "is-standard" => {
                                    self.eval_native_1arg(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::IsStandard(Box::new(initial))
                                    )?
                                }
                                "principal-destruct?" => {
                                    self.eval_native_1arg(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::PrincipalDestruct(Box::new(initial))
                                    )?
                                }
                                "principal-construct?" => {
                                    if lv.len() == 3 {
                                        self.eval_native_2args(
                                            &config,
                                            continuation,
                                            function_name.as_str(),
                                            lv.get(1).ok_or_else(|| Error::Bug(format!("Missing argument 1 to {function_name}")))?.clone(),
                                            lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.clone(),
                                            |op1, op2| SymOp::PrincipalConstruct(Box::new(op1), Box::new(op2), None)
                                        )?
                                    }
                                    else if lv.len() == 4 {
                                        self.eval_native_3args(
                                            &config,
                                            continuation,
                                            function_name.as_str(),
                                            lv.get(1).ok_or_else(|| Error::Bug(format!("Missing argument 1 to {function_name}")))?.clone(),
                                            lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.clone(),
                                            lv.get(3).ok_or_else(|| Error::Bug(format!("Missing argument 3 to {function_name}")))?.clone(),
                                            |op1, op2, op3| SymOp::PrincipalConstruct(Box::new(op1), Box::new(op2), Some(Box::new(op3)))
                                        )?
                                    }
                                    else {
                                        return Err(Error::Bug(format!("Wrong number of arguments for {function_name}")));
                                    }
                                }
                                "string-to-int?" => {
                                    self.eval_native_1arg(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::StringToInt(Box::new(initial))
                                    )?
                                }
                                "string-to-uint?" => {
                                    self.eval_native_1arg(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::StringToUInt(Box::new(initial))
                                    )?
                                }
                                "int-to-ascii" => {
                                    self.eval_native_1arg(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::IntToAscii(Box::new(initial))
                                    )?
                                }
                                "int-to-utf8" => {
                                    self.eval_native_1arg(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::IntToUtf8(Box::new(initial))
                                    )?
                                }
                                "list" => {
                                    let list_syms = lv.get(1..).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?;
                                    if list_syms.len() == 0 {
                                        let mut cont = Continuation::from_parent(Rc::new(continuation), function_name.to_string(), body.span.start_line);
                                        cont.final_formula = SymOp::ListCons(vec![]);
                                        vec![cont]
                                    }
                                    else {
                                        let conts = self.eval_variadic_native(
                                            &config,
                                            continuation,
                                            function_name.as_str(),
                                            list_syms,
                                            |initial| SymOp::ListCons(vec![Box::new(initial)]),
                                            |left, right| left.list_cons(right)
                                        )?;
                                        conts
                                    }
                                }
                                "var-get" => {
                                    let var_name_expr = lv.get(1).ok_or_else(|| Error::Bug("Missing variable name".into()))?;
                                    let Some(var_name) = var_name_expr.match_atom() else {
                                        return Err(Error::Bug(format!("Variable name '{:?}' is not an atom", &var_name_expr)));
                                    };

                                    let Some(formula) = continuation.lookup_data_var(var_name) else {
                                        error!("Faulty continuation looking for '{}'", &var_name);
                                        return Err(Error::Bug(format!("Unbound formula '{}'", &var_name)));
                                    };

                                    let formula = formula.clone();

                                    let var_full_name = FullName(continuation.get_current_contract_id(), var_name.clone());

                                    continuation.read_data_var(var_name.clone(), body.span.start_line);
                                    continuation.final_formula = SymOp::LoadedDataVariable(var_full_name, Box::new(formula.clone()));
                                    vec![continuation]
                                },
                                "var-set" => {
                                    let var_name_expr = lv.get(1).ok_or_else(|| Error::Bug("Missing variable name".into()))?;
                                    let var_val_expr = lv.get(2).ok_or_else(|| Error::Bug("Missing variable value".into()))?;

                                    let Some(var_name) = var_name_expr.match_atom() else {
                                        return Err(Error::Bug(format!("Variable name '{:?}' is not an atom", &var_name_expr)));
                                    };

                                    let mut conts = self.eval(&config, Continuation::from_parent(Rc::new(continuation), format!("{function_name}.var-value"), var_val_expr.span.start_line), var_val_expr)?;
                                    for cont in conts.iter_mut() {
                                        if cont.halted() {
                                            continue;
                                        }
                                        cont.set_data_var(var_name, cont.final_formula.clone().simplify()?);

                                        // (var-set ..) always evals to True
                                        cont.final_formula = SymOp::True();

                                        trace!("var-set cont:\n{}", &cont);
                                    }
                                    conts
                                },
                                "map-get?" => {
                                    let Some(map_name) = lv.get(1).ok_or_else(|| Error::Bug("Missing map name".into()))?.match_atom() else {
                                        return Err(Error::Bug("Map name is not an atom".into()));
                                    };
                                    let key_symexp = lv.get(2).ok_or_else(|| Error::Bug("Missing key expr".into()))?;

                                    let mut key_conts = self.eval(&config, Continuation::from_parent(Rc::new(continuation), format!("{function_name}.{map_name}"), key_symexp.span.start_line), key_symexp)?;

                                    for cont in key_conts.iter_mut() {
                                        if cont.halted() {
                                            continue;
                                        }

                                        let key_formula = cont.final_formula.clone().simplify()?;

                                        // If a map entry was not set in the computation of this
                                        // continuation, we cannot treat it as definitely present.
                                        // We capture this with 
                                        // `LoadedMapEntry(map_name, key_formula, None)`.
                                        //
                                        // If the continuation already set a value for the given
                                        // `key_formula`, however, we will return it with
                                        // `LoadedMapEntry(map_name, key_formula, Some(value_formula))`
                                        let value = match cont.lookup_map_entry(map_name, &key_formula) {
                                            Some(value_op) => Some(Box::new(value_op.clone())),
                                            None => None
                                        };

                                        let full_map_name = FullName(cont.get_current_contract_id(), map_name.clone());
                                        if value.is_none() {
                                            if cont.is_map_deleted(&full_map_name, &key_formula) {
                                                // this value was definitely deleted
                                                cont.final_formula = SymOp::Constant(Value::none());
                                            }
                                            else {
                                                cont.read_map_entry(map_name.clone(), key_formula.clone(), None, body.span.start_line); 
                                                cont.final_formula = SymOp::LoadedMapEntry(full_map_name.clone(), Box::new(key_formula), None);
                                            }
                                        }
                                        else {
                                            cont.final_formula = SymOp::LoadedMapEntry(full_map_name.clone(), Box::new(key_formula), value);
                                        }
                                    }

                                    key_conts
                                }
                                "map-set" => {
                                    let Some(map_name) = lv.get(1).ok_or_else(|| Error::Bug("Missing map name".into()))?.match_atom() else {
                                        return Err(Error::Bug("Map name is not an atom".into()));
                                    };
                                    let key_symexp = lv.get(2).ok_or_else(|| Error::Bug("Missing key expr".into()))?;
                                    let val_symexp = lv.get(3).ok_or_else(|| Error::Bug("Missing value expr".into()))?;
                                   
                                    let key_conts = self.eval(&config, Continuation::from_parent(Rc::new(continuation), format!("{function_name}.key"), key_symexp.span.start_line), key_symexp)?;

                                    let mut final_conts = vec![];
                                    let mut val_cont_sets = vec![];
                                    for cont in key_conts.into_iter() {
                                        if cont.halted() {
                                            final_conts.push(cont);
                                            continue;
                                        }

                                        let key_formula = cont.final_formula.clone().simplify()?;
                                        let parent_rc = Continuation::from_parent(Rc::new(cont), format!("{function_name}.value"), val_symexp.span.start_line);
                                        let val_conts = self.eval(&config, parent_rc, val_symexp)?;
                                        val_cont_sets.push((key_formula, val_conts));
                                    }

                                    for (key_formula, val_cont_set) in val_cont_sets.into_iter() {
                                        for mut val_cont in val_cont_set.into_iter() {
                                            if val_cont.halted() {
                                                final_conts.push(val_cont);
                                                continue;
                                            }

                                            val_cont.set_map_entry(map_name, key_formula.clone(), val_cont.final_formula.clone().simplify()?);

                                            // (map-set ..) always evals to True
                                            val_cont.final_formula = SymOp::True();
                                            final_conts.push(val_cont);
                                        }
                                    }
                                    final_conts
                                }
                                "map-insert" => {
                                    let Some(map_name) = lv.get(1).ok_or_else(|| Error::Bug("Missing map name".into()))?.match_atom() else {
                                        return Err(Error::Bug("Map name is not an atom".into()));
                                    };
                                    let key_symexp = lv.get(2).ok_or_else(|| Error::Bug("Missing key expr".into()))?;
                                    let val_symexp = lv.get(3).ok_or_else(|| Error::Bug("Missing value expr".into()))?;
                                   
                                    let key_conts = self.eval(&config, Continuation::from_parent(Rc::new(continuation), format!("{function_name}.key"), key_symexp.span.start_line), key_symexp)?;

                                    let mut final_conts = vec![];
                                    let mut val_cont_sets = vec![];
                                    for cont in key_conts.into_iter() {
                                        if cont.halted() {
                                            final_conts.push(cont);
                                            continue;
                                        }

                                        let key_formula = cont.final_formula.clone().simplify()?;
                                        let parent_rc = Continuation::from_parent(Rc::new(cont), format!("{function_name}.value"), val_symexp.span.start_line);
                                        let val_conts = self.eval(&config, parent_rc, val_symexp)?;
                                        val_cont_sets.push((key_formula, val_conts));
                                    }

                                    for (key_formula, val_cont_set) in val_cont_sets.into_iter() {
                                        for mut val_cont in val_cont_set.into_iter() {
                                            if val_cont.halted() {
                                                final_conts.push(val_cont);
                                                continue;
                                            }

                                            if val_cont.lookup_map_entry(map_name, &key_formula).is_some() {
                                                // this will definitely fail
                                                val_cont.final_formula = SymOp::False();
                                                final_conts.push(val_cont);
                                                continue;
                                            }

                                            // this may or may not produce a map entry, so account for both
                                            let parent_formula = val_cont.final_formula.clone().simplify()?;
                                            let parent_pred = val_cont.predicate.clone().simplify()?;
                                            let parent = Rc::new(val_cont);

                                            let full_map_name = FullName(parent.get_current_contract_id(), map_name.clone());
                                            let entry = SymOp::LoadedMapEntry(full_map_name, Box::new(key_formula.clone()), None);

                                            let mut cont_present = Continuation::from_parent(parent.clone(), format!("{function_name}.present"), body.span.start_line);
                                            cont_present.predicate = parent_pred.clone()
                                                .and(SymOp::IsSome(Box::new(entry.clone())).try_as_predicate()?);

                                            cont_present.final_formula = SymOp::False();

                                            let mut cont_absent = Continuation::from_parent(parent.clone(), format!("{function_name}.absent"), body.span.start_line);
                                            cont_absent.predicate = parent_pred.clone()
                                                .and(SymOp::IsNone(Box::new(entry.clone())).try_as_predicate()?);

                                            cont_absent.final_formula = SymOp::True();

                                            cont_absent.set_map_entry(map_name, key_formula.clone(), parent_formula);

                                            final_conts.push(cont_present);
                                            final_conts.push(cont_absent);
                                        }
                                    }
                                    final_conts
                                }
                                "map-delete" => {
                                    let Some(map_name) = lv.get(1).ok_or_else(|| Error::Bug("Missing map name".into()))?.match_atom() else {
                                        return Err(Error::Bug("Map name is not an atom".into()));
                                    };
                                    let key_symexp = lv.get(2).ok_or_else(|| Error::Bug("Missing key expr".into()))?;

                                    let key_conts = self.eval(&config, Continuation::from_parent(Rc::new(continuation), format!("{function_name}"), key_symexp.span.start_line), key_symexp)?;

                                    let mut final_conts = vec![];
                                    for mut cont in key_conts.into_iter() {
                                        if cont.halted() {
                                            final_conts.push(cont);
                                            continue;
                                        }

                                        let key_formula = cont.final_formula.clone().simplify()?;
                                        let res = cont.delete_map_entry(map_name, &key_formula);
                                        if res {
                                            // this was definitely present, so only one
                                            // continuation is necessary
                                            let mut cont_present = Continuation::from_parent(Rc::new(cont), format!("{function_name}.present"), body.span.start_line);
                                            cont_present.final_formula = SymOp::True();
                                            final_conts.push(cont_present);
                                            continue;
                                        }

                                        // this may be true or false, so account for both
                                        let parent_pred = cont.predicate.clone().simplify()?;
                                        let parent = Rc::new(cont);

                                        let full_map_name = FullName(parent.get_current_contract_id(), map_name.clone());
                                        let entry = SymOp::LoadedMapEntry(full_map_name, Box::new(key_formula.clone().simplify()?), None);

                                        let mut cont_present = Continuation::from_parent(parent.clone(), format!("{function_name}.present"), body.span.start_line);
                                        cont_present.predicate = parent_pred.clone()
                                            .and(SymOp::IsSome(Box::new(entry.clone())).try_as_predicate()?);

                                        cont_present.final_formula = SymOp::True();

                                        let mut cont_absent = Continuation::from_parent(parent.clone(), format!("{function_name}.absent"), body.span.start_line);
                                        cont_absent.predicate = parent_pred.clone()
                                            .and(SymOp::IsNone(Box::new(entry.clone())).try_as_predicate()?);

                                        cont_absent.final_formula = SymOp::False();

                                        final_conts.push(cont_present);
                                        final_conts.push(cont_absent);
                                    }
                                    final_conts
                                }
                                "tuple" => {
                                    let mut conts = vec![(vec![], continuation)];
                                    for i in 1..lv.len() {
                                        let Some(key_value_list) = lv.get(i).ok_or_else(|| Error::Bug("unreachable -- lv is empty in tuple cons".into()))?.match_list() else {
                                            return Err(Error::Bug(format!("tuple item {i} is not a list")));
                                        };
                                        let Some(key_name) = key_value_list.get(0).ok_or_else(|| Error::Bug(format!("No tuple item name in tuple item {i}")))?.match_atom() else {
                                            return Err(Error::Bug(format!("tuple item {i} did not have an atom as its first item")));
                                        };

                                        let value_exp = key_value_list.get(1).ok_or_else(|| Error::Bug(format!("No tuple item value in tuple item {i}")))?;

                                        let mut new_conts = vec![];
                                        for (prev_key_values, cont) in conts.into_iter() {
                                            if cont.halted() {
                                                new_conts.push((prev_key_values, cont));
                                                continue;
                                            }
                                            let parent_rc = Rc::new(cont);
                                            let next = self.eval(&config, Continuation::from_parent(parent_rc, format!("{function_name}.tuple-item-{i}"), value_exp.span.start_line), value_exp)?;

                                            for next_cont in next.into_iter() {
                                                let mut key_values = prev_key_values.clone();
                                                key_values.push((key_name.clone(), Box::new(next_cont.final_formula.clone())));
                                                new_conts.push((key_values, next_cont));
                                            }
                                        }

                                        conts = new_conts;
                                    }

                                    let mut ret = vec![];
                                    for (key_values, mut cont) in conts.into_iter() {
                                        if cont.halted() {
                                            ret.push(cont);
                                            continue;
                                        }

                                        let tuple_formula = SymOp::TupleCons(key_values);
                                        cont.final_formula = tuple_formula;
                                        ret.push(cont);
                                    }
                                    ret
                                }
                                "get" => {
                                   let Some(name) = lv.get(1).ok_or_else(|| Error::Bug("Missing field name".into()))?.match_atom() else {
                                       return Err(Error::Bug(format!("Tuple name is not an atom in {body:?}")));
                                   };
                                   let sym = lv.get(2).ok_or_else(|| Error::Bug("Missing tuple symbolic expression".into()))?;

                                   let mut conts = self.eval(&config, Continuation::from_parent(Rc::new(continuation), format!("{function_name}.tuple-get"), sym.span.start_line), sym)?;
                                   for cont in conts.iter_mut() {
                                       if cont.halted() {
                                           continue;
                                       }

                                       let f = cont.final_formula.clone();
                                       cont.final_formula = SymOp::TupleGet(name.clone(), Box::new(f));
                                   }
                                   conts
                                }
                                "merge" => {
                                   let dest_tuple = lv.get(1).ok_or_else(|| Error::Bug("Missing destination tuple".into()))?;
                                   let src_tuple = lv.get(2).ok_or_else(|| Error::Bug("Missing source tuple".into()))?;

                                   let dest_conts = self.eval(&config, Continuation::from_parent(Rc::new(continuation), format!("{function_name}.tuple-merge-dest"), dest_tuple.span.start_line), dest_tuple)?;
                                   let mut src_conts = vec![];
                                   for dest_cont in dest_conts.into_iter() {
                                       if dest_cont.halted() {
                                           src_conts.push(dest_cont);
                                           continue;
                                       }

                                       let dest_formula = dest_cont.final_formula.clone();
                                       let dest_pred = dest_cont.predicate.clone();

                                       let mut next_conts = self.eval(&config, Continuation::from_parent(Rc::new(dest_cont), format!("{function_name}.tuple-merge-src"), src_tuple.span.start_line), src_tuple)?;

                                       for next_cont in next_conts.iter_mut() {
                                           if next_cont.halted() {
                                               continue;
                                           }

                                           let f = next_cont.final_formula.clone();
                                           let p = dest_pred.clone().and(next_cont.predicate.clone());
                                           next_cont.final_formula = SymOp::TupleMerge(Box::new(dest_formula.clone()), Box::new(f));
                                           next_cont.predicate = p;
                                       }

                                       src_conts.extend(next_conts.into_iter());
                                   }

                                   src_conts
                                }
                                "hash160" => {
                                    self.eval_native_1arg(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::Hash160(Box::new(initial))
                                    )?
                                }
                                "sha256" => {
                                    self.eval_native_1arg(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::Sha256(Box::new(initial))
                                    )?
                                }
                                "sha512" => {
                                    self.eval_native_1arg(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::Sha512(Box::new(initial))
                                    )?
                                }
                                "sha512/256" => {
                                    self.eval_native_1arg(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::Sha512Trunc256(Box::new(initial))
                                    )?
                                }
                                "keccak256" => {
                                    self.eval_native_1arg(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::Keccak256(Box::new(initial))
                                    )?
                                }
                                "secp256k1-recover?" => {
                                    self.eval_native_2args(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing argument 1 to {function_name}")))?.clone(),
                                        lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.clone(),
                                        |op1, op2| SymOp::Secp256k1Recover(Box::new(op1), Box::new(op2))
                                    )?
                                }
                                "secp256k1-verify" => {
                                    self.eval_native_3args(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing argument 1 to {function_name}")))?.clone(),
                                        lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.clone(),
                                        lv.get(3).ok_or_else(|| Error::Bug(format!("Missing argument 3 to {function_name}")))?.clone(),
                                        |op1, op2, op3| SymOp::Secp256k1Verify(Box::new(op1), Box::new(op2), Box::new(op3))
                                    )?
                                }
                                "contract-of" => {
                                    self.eval_native_1arg(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::ContractOf(Box::new(initial))
                                    )?
                                }
                                "principal-of" => {
                                    todo!();
                                }
                                "get-burn-block-info?" => {
                                    let Some(prop_sym) = lv.get(1) else {
                                        return Err(Error::Bug(format!("Missing argument 1 to {function_name}")));
                                    };
                                    let Some(prop_name) = prop_sym.match_atom() else {
                                        return Err(Error::Bug(format!("Argument 1 to {function_name} is not an atom")));
                                    };
                                    let Some(query_sym) = lv.get(2) else {
                                        return Err(Error::Bug(format!("Missing argument 1 to {function_name}")));
                                    };

                                    let query_cont = Continuation::from_parent(Rc::new(continuation), format!("{function_name}.query-value"),prop_sym.span.start_line);

                                    let mut conts = self.eval(&config, query_cont, query_sym)?;
                                    for cont in conts.iter_mut() {
                                        if cont.halted() {
                                            continue;
                                        }

                                        match prop_name.as_str() {
                                            "header-hash" => {
                                                cont.final_formula = SymOp::Variable(Sym::Optional("TODO-get-burn-block-info-header-hash".into(), TypeSignature::SequenceType(SequenceSubtype::BufferType(32u32.try_into().expect("infallible")))));
                                            }
                                            "pox-addrs" => {
                                                let addr_type = TupleTypeSignature::try_from(vec![
                                                    (
                                                        ClarityName::try_from("hashbytes").expect("infallible"),
                                                        TypeSignature::SequenceType(SequenceSubtype::BufferType(20u32.try_into().expect("infallible")))
                                                    ),
                                                    (
                                                        ClarityName::try_from("version").expect("infallible"),
                                                        TypeSignature::SequenceType(SequenceSubtype::BufferType(1u32.try_into().expect("infallible")))
                                                    )
                                                ])
                                                .expect("infallible");

                                                let addr_list_type = TypeSignature::SequenceType(SequenceSubtype::ListType(ListTypeData::new_list(addr_type.into(), 2).expect("infallible")));
                                                let pox_addr_type = TupleTypeSignature::try_from(vec![
                                                    (
                                                        ClarityName::try_from("addrs").expect("infallible"),
                                                        addr_list_type
                                                    ),
                                                    (
                                                        ClarityName::try_from("payout").expect("infallible"),
                                                        TypeSignature::UIntType
                                                    )
                                                ])
                                                .expect("infallible");
                                                
                                                cont.final_formula = SymOp::Variable(Sym::Optional("TODO-get-burn-block-info-pox-addr".into(), pox_addr_type.into()));
                                            },
                                            _ => {
                                                return Err(Error::Bug(format!("Unrecognized property `{prop_name}` in `get-burn-block-info?`")));
                                            }
                                        }
                                    }
                                    conts
                                }
                                "is-ok" => {
                                    self.eval_native_1arg(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::IsOkay(Box::new(initial))
                                    )?
                                }
                                "is-err" => {
                                    self.eval_native_1arg(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::IsErr(Box::new(initial))
                                    )?
                                }
                                "is-some" => {
                                    self.eval_native_1arg(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::IsSome(Box::new(initial))
                                    )?
                                }
                                "is-none" => {
                                    self.eval_native_1arg(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::IsNone(Box::new(initial))
                                    )?
                                }
                                "unwrap-panic" => {
                                    // evaluate `(unwrap-panic x)`, where `x` evaluates to either `(optional v)` or `(response v w)`
                                    //
                                    // NOTE: The Clarity VM will evaluate both x and y, in that
                                    // order

                                    let Some(cond_sym) = lv.get(1).cloned() else {
                                        return Err(Error::Bug(format!("Missing argument 1 to {function_name}")));
                                    };

                                    let mut new_conts = vec![];

                                    // evaluate `x`
                                    let cond_conts = self.eval(&config, Continuation::from_parent(Rc::new(continuation), format!("{function_name}.cond"), cond_sym.span.start_line), &cond_sym)?;

                                    for cond_cont in cond_conts.into_iter() {
                                        if cond_cont.halted() {
                                            new_conts.push(cond_cont);
                                            continue;
                                        }

                                        let cond_formula = cond_cont.final_formula.clone();
                                        let cond_predicate = cond_cont.predicate.clone();
                                        let parent_rc = Rc::new(cond_cont);

                                        // case 1: `(is-ok x)` is true or `(is-some x)` is true
                                        let mut ok_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}.unwrap-success"), cond_sym.span.start_line);
                                        ok_cont.predicate = match self.typemap(&cur_contract)?.get_type_expected(&cond_sym) {
                                            Some(TypeSignature::OptionalType(..)) => {
                                                cond_predicate.clone().and(Predicate::IsSome(cond_formula.clone()))
                                            }
                                            Some(TypeSignature::ResponseType(..)) => {
                                                cond_predicate.clone().and(Predicate::IsOkay(cond_formula.clone()))
                                            },
                                            Some(x) => {
                                                return Err(Error::Bug(format!("Did not get (optional ..) or (response ..) type (got {x:?}) for symbol {cond_sym}")));
                                            }
                                            None => {
                                                return Err(Error::Bug(format!("Did not get any type information for symbol {cond_sym}")));
                                            }
                                        };
                                        ok_cont.final_formula = SymOp::UnwrapPanic(Box::new(cond_formula.clone()));

                                        // case 2: (is-ok x) (or (is-some x)) is false. This
                                        // panics
                                        let mut panic_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}.unwrap-failure"), cond_sym.span.start_line);
                                        panic_cont.predicate = match self.typemap(&cur_contract)?.get_type_expected(&cond_sym) {
                                            Some(TypeSignature::OptionalType(..)) => {
                                                cond_predicate.and(Predicate::IsNone(cond_formula.clone()))
                                            }
                                            Some(TypeSignature::ResponseType(..)) => {
                                                cond_predicate.and(Predicate::IsErr(cond_formula.clone()))
                                            }
                                            Some(x) => {
                                                return Err(Error::Bug(format!("Did not get (optional ..) or (response ..) type (got {x:?}) for symbol {cond_sym}")));
                                            }
                                            None => {
                                                return Err(Error::Bug(format!("Did not get any type information for symbol {cond_sym}")));
                                            }
                                        };

                                        panic_cont.panicking = true;
                                        panic_cont.final_formula = SymOp::Panic;

                                        new_conts.push(ok_cont);
                                        new_conts.push(panic_cont);
                                    }

                                    new_conts
                                }
                                "unwrap-err-panic" => {
                                    // evaluate `(unwrap-err-panic x)`, where `x` evaluates to `(response v w)`
                                    //
                                    // NOTE: The Clarity VM will evaluate both x and y, in that
                                    // order
                                    
                                    let Some(cond_sym) = lv.get(1).cloned() else {
                                        return Err(Error::Bug(format!("Missing argument 1 to {function_name}")));
                                    };

                                    let mut new_conts = vec![];

                                    // evaluate `x`
                                    let cond_conts = self.eval(&config, Continuation::from_parent(Rc::new(continuation), format!("{function_name}.cond"), cond_sym.span.start_line), &cond_sym)?;

                                    for cond_cont in cond_conts.into_iter() {
                                        if cond_cont.halted() {
                                            new_conts.push(cond_cont);
                                            continue;
                                        }

                                        let cond_predicate = cond_cont.predicate.clone();
                                        let cond_formula = cond_cont.final_formula.clone();

                                        let parent_rc = Rc::new(cond_cont);

                                        // case 1: `(is-err x)` is true
                                        let mut is_err_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}.unwrap-err-success"), cond_sym.span.start_line);
                                        is_err_cont.predicate = cond_predicate.clone().and(Predicate::IsErr(cond_formula.clone()));
                                        is_err_cont.final_formula = SymOp::UnwrapErrPanic(Box::new(cond_formula.clone()));

                                        // case 2: (is-ok x) is true This
                                        // panics
                                        let mut panic_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}.unwrap-err-failure"), cond_sym.span.start_line);
                                        panic_cont.predicate = cond_predicate.and(Predicate::IsOkay(cond_formula.clone()));
                                        panic_cont.panicking = true;
                                        panic_cont.final_formula = SymOp::Panic;

                                        new_conts.push(is_err_cont);
                                        new_conts.push(panic_cont);
                                    }

                                    new_conts
                                }
                                "err" => {
                                    self.eval_native_1arg(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::ConsError(Box::new(initial))
                                    )?
                                }
                                "ok" => {
                                    self.eval_native_1arg(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::ConsOkay(Box::new(initial))
                                    )?
                                }
                                "some" => {
                                    self.eval_native_1arg(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::ConsSome(Box::new(initial))
                                    )?
                                }
                                "ft-get-balance" => {
                                    todo!();
                                }
                                "nft-get-owner?" => {
                                    todo!();
                                }
                                "ft-transfer?" => {
                                    todo!();
                                }
                                "nft-transfer?" => {
                                    todo!();
                                }
                                "ft-mint?" => {
                                    todo!();
                                }
                                "nft-mint?" => {
                                    todo!();
                                }
                                "ft-get-supply" => {
                                    todo!();
                                }
                                "ft-burn?" => {
                                    todo!();
                                }
                                "nft-burn?" => {
                                    todo!();
                                }
                                "stx-get-balance" => {
                                    let Some(addr_sym) = lv.get(1) else {
                                        return Err(Error::Bug(format!("Missing argument 1 to {function_name}")));
                                    };
                                    let addr_cont = Continuation::from_parent(Rc::new(continuation), format!("{function_name}.address-eval"), addr_sym.span.start_line);

                                    let mut conts = self.eval(&config, addr_cont, addr_sym)?;
                                    for cont in conts.iter_mut() {
                                        if cont.halted() {
                                            continue;
                                        }

                                        // TODO: look up balances
                                        cont.final_formula = SymOp::Variable(Sym::UInt("TODO-stx-get-balance".into()));
                                    }
                                    conts
                                }
                                "stx-transfer?" => {
                                    todo!();
                                }
                                "stx-transfer-memo?" => {
                                    todo!();
                                }
                                "stx-burn?" => {
                                    todo!();
                                }
                                "stx-account" => {
                                    todo!();
                                }
                                "bit-and" => {
                                    self.eval_foldable_native(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1..).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?,
                                        |left, right| left.bitwise_and(right)
                                    )?
                                }
                                "bit-or" => {
                                    self.eval_foldable_native(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1..).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?,
                                        |left, right| left.bitwise_or(right)
                                    )?
                                }
                                "xor" => {
                                    self.eval_native_2args(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing argument 1 to {function_name}")))?.clone(),
                                        lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.clone(),
                                        |left, right| SymOp::BitwiseXor(vec![Box::new(left), Box::new(right)])
                                    )?
                                }
                                "bit-xor" => {
                                    self.eval_foldable_native(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1..).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?,
                                        |left, right| left.bitwise_xor(right)
                                    )?
                                }
                                "bit-not" => {
                                    self.eval_native_1arg(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::BitwiseNot(Box::new(initial))
                                    )?
                                }
                                "bit-shift-left" => {
                                    self.eval_native_2args(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing argument 1 to {function_name}")))?.clone(),
                                        lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.clone(),
                                        |left, right| SymOp::BitwiseLShift(Box::new(left), Box::new(right))
                                    )?
                                }
                                "bit-shift-right" => {
                                    self.eval_native_2args(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing argument 1 to {function_name}")))?.clone(),
                                        lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.clone(),
                                        |left, right| SymOp::BitwiseRShift(Box::new(left), Box::new(right))
                                    )?
                                }
                                "slice" | "slice?" => {
                                    self.eval_native_3args(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing argument 1 to {function_name}")))?.clone(),
                                        lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.clone(),
                                        lv.get(3).ok_or_else(|| Error::Bug(format!("Missing argument 3 to {function_name}")))?.clone(),
                                        |op1, op2, op3| SymOp::Slice(Box::new(op1), Box::new(op2), Box::new(op3))
                                    )?
                                }
                                "to-consensus-buff?" => {
                                    let Some(exp_sym) = lv.get(1) else {
                                        return Err(Error::Bug(format!("Missing argument 1 to {function_name}")));
                                    };

                                    let expr_cont = Continuation::from_parent(Rc::new(continuation), format!("{function_name}.expr-eval"), exp_sym.span.start_line);
                                    let conts = self.eval(&config, expr_cont, exp_sym)?;
                                    let mut ret = vec![];
                                    for cont in conts.into_iter() {
                                        if cont.halted() {
                                            ret.push(cont);
                                            continue;
                                        }

                                        let pred = cont.predicate.clone();
                                        let formula = SymOp::ToConsensusBuff(Box::new(cont.final_formula.clone()));

                                        let cont_rc = Rc::new(cont);

                                        // successfully serialized
                                        let mut success = Continuation::from_parent(cont_rc.clone(), format!("{function_name}.expr-serialized"), exp_sym.span.start_line);
                                        success.predicate = pred.clone().and(Predicate::IsSome(formula.clone()));
                                        success.final_formula = formula.clone();

                                        // failed to serialize
                                        let mut failure = Continuation::from_parent(cont_rc.clone(), format!("{function_name}.expr-too-big"), exp_sym.span.end_line);
                                        failure.predicate = pred.clone().and(Predicate::IsNone(formula.clone()));
                                        failure.final_formula = SymOp::none();

                                        ret.push(success);
                                        ret.push(failure);
                                    }

                                    ret
                                }
                                "from-consensus-buff?" => {
                                    let Some(ts_sym) = lv.get(1) else {
                                        return Err(Error::Bug(format!("Missing argument 1 to {function_name}")));
                                    };
                                    let ts = TypeSignature::parse_type_repr(DEFAULT_STACKS_EPOCH, ts_sym, &mut ())?;
                                    let Some(buf_sym) = lv.get(2) else {
                                        return Err(Error::Bug(format!("Missing argument 2 to {function_name}")));
                                    };
                                    
                                    let buff_cont = Continuation::from_parent(Rc::new(continuation), format!("{function_name}.buff-eval"), buf_sym.span.start_line);
                                    let conts = self.eval(&config, buff_cont, buf_sym)?;
                                    let mut ret = vec![];
                                    for cont in conts.into_iter() {
                                        if cont.halted() {
                                            ret.push(cont);
                                            continue;
                                        }
                                        
                                        let pred = cont.predicate.clone();
                                        let formula = SymOp::FromConsensusBuff(ts.clone(), Box::new(cont.final_formula.clone()));

                                        let cont_rc = Rc::new(cont);

                                        // successfully deserialized
                                        let mut success = Continuation::from_parent(cont_rc.clone(), format!("{function_name}.buff-deserialized"), buf_sym.span.start_line);
                                        success.predicate = pred.clone().and(Predicate::IsSome(formula.clone()));
                                        success.final_formula = formula.clone();

                                        // failed to deserialize
                                        let mut failure = Continuation::from_parent(cont_rc.clone(), format!("{function_name}.buff-deserialize-failed"), buf_sym.span.end_line);
                                        failure.predicate = pred.clone().and(Predicate::IsNone(formula.clone()));
                                        failure.final_formula = SymOp::none();

                                        ret.push(success);
                                        ret.push(failure);
                                    }
                                    ret
                                }
                                "replace-at?" => {
                                    todo!()
                                }
                                "get-stacks-block-info?" => {
                                    todo!()
                                }
                                "get-tenure-info?" => {
                                    todo!()
                                }
                                "contract-hash?" => {
                                    todo!()
                                }
                                "to-ascii?" => {
                                    todo!()
                                }
                                "restrict-assets?" => {
                                    todo!()
                                }
                                "as-contract?" => {
                                    todo!()
                                }
                                "secp256r1-verify?" => {
                                    todo!()
                                }
                                "verify-merkle-proof" => {
                                    let args = lv.get(1..).ok_or_else(|| Error::Bug(format!("Missing arguments for {function_name}")))?;
                                    if args.len() != 5 {
                                        return Err(Error::Bug(format!("Expected 5 arguments to {function_name}")));
                                    }

                                    self.eval_native_n_args(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1..).ok_or_else(|| Error::Bug(format!("Missing arguments for {function_name}")))?,
                                        |mut ops| {
                                            let arg4 = Box::new(ops.pop().expect("infallible"));
                                            let arg3 = Box::new(ops.pop().expect("infallible"));
                                            let arg2 = Box::new(ops.pop().expect("infallible"));
                                            let arg1 = Box::new(ops.pop().expect("infallible"));
                                            let arg0 = Box::new(ops.pop().expect("infallible"));
                                            SymOp::VerifyMerkleProof(arg0, arg1, arg2, arg3, arg4)
                                        }
                                    )?
                                }
                                "get-bitcoin-tx-output?" => {
                                    self.eval_native_2args(
                                        &config,
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing argument 1 to {function_name}")))?.clone(),
                                        lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.clone(),
                                        |op1, op2| SymOp::GetBitcoinTxOutput(Box::new(op1), Box::new(op2))
                                    )?
                                }
                                "default-to" => {
                                    // treat `(default-to x y)` as 
                                    // `(if (is-none y) x (unwrap-panic y))`
                                    //
                                    // HOWEVER, we must take care to only eval `x` once, and do so
                                    // before `y`.
                                    //
                                    // NOTE: the Clarity VM will evaluate x and then y, regardless
                                    // of whether or not y is none.

                                    let Some(default_sym) = lv.get(1).cloned() else {
                                        return Err(Error::Bug(format!("Missing argument 1 to {function_name}")));
                                    };

                                    let Some(opt_sym) = lv.get(2).cloned() else {
                                        return Err(Error::Bug(format!("Missing argument 2 to {function_name}")));
                                    };

                                    let mut new_conts = vec![];

                                    // evaluate `x`
                                    let default_conts = self.eval(&config, Continuation::from_parent(Rc::new(continuation), format!("{function_name}.default"), default_sym.span.start_line), &default_sym)?;
                                    for default_cont in default_conts.into_iter() {
                                        if default_cont.halted() {
                                            new_conts.push(default_cont);
                                            continue;
                                        }

                                        let default_final_formula = default_cont.final_formula.clone();
                                        let parent_rc = Rc::new(default_cont);

                                        // evaluate `y` for this `x`'s continuation
                                        let opt_conts = self.eval(&config, Continuation::from_parent(parent_rc, format!("{function_name}.optional"), opt_sym.span.start_line), &opt_sym)?;
                                        for opt_cont in opt_conts.into_iter() {
                                            if opt_cont.halted() {
                                                new_conts.push(opt_cont);
                                                continue;
                                            }
                                            let parent_predicate = opt_cont.predicate.clone();
                                            let final_formula = opt_cont.final_formula.clone();
                                            let parent_rc = Rc::new(opt_cont);

                                            // case 1: this is (some ..)
                                            let mut some_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}.optional/is-some"), opt_sym.span.start_line);
                                            some_cont.predicate = parent_predicate.clone().and(Predicate::IsSome(final_formula.clone()));
                                            some_cont.final_formula = SymOp::UnwrapPanic(Box::new(final_formula.clone()));

                                            // case 2: this is none
                                            let mut none_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}.is_none"), opt_sym.span.start_line);
                                            none_cont.predicate = parent_predicate.clone().and(Predicate::IsNone(final_formula.clone()));
                                            none_cont.final_formula = default_final_formula.clone();

                                            new_conts.push(some_cont);
                                            new_conts.push(none_cont);
                                        }
                                    }

                                    new_conts
                                }
                                "asserts!" => {
                                    // evaluate `(asserts! x y)`, where `x` evaluates to a bool and `y` evaluates to `(err z)`.
                                    //
                                    // NOTE: the Clarity VM does _not_ evaluate `y` unless `x` is
                                    // false.

                                    let Some(cond_sym) = lv.get(1).cloned() else {
                                        return Err(Error::Bug(format!("Missing argument 1 to {function_name}")));
                                    };
                                    let Some(err_sym) = lv.get(2).cloned() else {
                                        return Err(Error::Bug(format!("Missing argument 2 to {function_name}")));
                                    };

                                    let mut new_conts = vec![];

                                    // evaluate `x`
                                    let cond_conts = self.eval(&config, Continuation::from_parent(Rc::new(continuation), format!("{function_name}.cond-eval"), cond_sym.span.start_line), &cond_sym)?;
                                    for cond_cont in cond_conts.into_iter() {
                                        if cond_cont.halted() {
                                            new_conts.push(cond_cont);
                                            continue;
                                        }

                                        let cond_pred = cond_cont.predicate.clone();
                                        let cond_formula = cond_cont.final_formula.clone();
                                        let cont_rc = Rc::new(cond_cont);

                                        // case 1: `x` is true.
                                        // `(asserts! ..)` then evaluates to true, and `x` joins
                                        // the predicate.
                                        let mut cont_true = Continuation::from_parent(cont_rc.clone(), format!("{function_name}.is-true"), cond_sym.span.start_line);
                                        cont_true.predicate = cond_pred.clone().and(cond_formula.clone().try_as_predicate()?).simplify()?;
                                        cont_true.final_formula = SymOp::True();

                                        if cont_true.predicate != Predicate::False {
                                            new_conts.push(cont_true);
                                        }

                                        let mut cond_false = Continuation::from_parent(cont_rc, format!("{function_name}.is-false"), err_sym.span.start_line);
                                        cond_false.predicate = cond_pred.clone().and(cond_formula.clone().try_as_predicate()?.not().simplify()?).simplify()?;
                                        if cond_false.predicate == Predicate::False {
                                            continue;
                                        }

                                        // case 2: `x` is false.
                                        // evaluate `y`, and set all of its continuations as
                                        // early-return.
                                        let err_conts = self.eval(&config, cond_false, &err_sym)?;
                                        for mut err_cont in err_conts.into_iter() {
                                            if err_cont.halted() {
                                                new_conts.push(err_cont);
                                                continue;
                                            }

                                            trace!("Continuation {} is early-return", err_cont.id);
                                            err_cont.early_return = true;
                                            new_conts.push(err_cont);
                                        }
                                    }

                                    new_conts
                                }
                                "unwrap!" => {
                                    // evaluate `(unwrap! x y)`, where `x` evaluates to either `(optional v)` or `(response v w)`
                                    // and `y` evaluates to `(err z)`
                                    //
                                    // NOTE: The Clarity VM will evaluate both x and y, in that
                                    // order

                                    let Some(cond_sym) = lv.get(1).cloned() else {
                                        return Err(Error::Bug(format!("Missing argument 1 to {function_name}")));
                                    };
                                    let Some(err_sym) = lv.get(2).cloned() else {
                                        return Err(Error::Bug(format!("Missing argument 2 to {function_name}")));
                                    };

                                    let mut new_conts = vec![];

                                    // evaluate `x`
                                    let cond_conts = self.eval(&config, Continuation::from_parent(Rc::new(continuation), format!("{function_name}.cond-eval"), cond_sym.span.start_line), &cond_sym)?;

                                    // evaluate `y` from each `x`
                                    for cond_cont in cond_conts.into_iter() {
                                        if cond_cont.halted() {
                                            new_conts.push(cond_cont);
                                            continue;
                                        }

                                        let cond_formula = cond_cont.final_formula.clone();

                                        let parent_rc = Rc::new(cond_cont);
                                        let err_conts = self.eval(&config, Continuation::from_parent(parent_rc, format!("{function_name}.err-eval"), err_sym.span.start_line), &err_sym)?;

                                        for parent_cont in err_conts.into_iter() {
                                            if parent_cont.halted() {
                                                new_conts.push(parent_cont);
                                                continue;
                                            }

                                            let cond_predicate = parent_cont.predicate.clone();
                                            let parent_rc = Rc::new(parent_cont);

                                            // case 1: `(is-ok x)` is true or `(is-some x)` is true
                                            let mut ok_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}.cond-true"), cond_sym.span.start_line);
                                            ok_cont.predicate = match self.typemap(&cur_contract)?.get_type_expected(&cond_sym) {
                                                Some(TypeSignature::OptionalType(..)) => {
                                                    cond_predicate.clone().and(Predicate::IsSome(cond_formula.clone()))
                                                }
                                                Some(TypeSignature::ResponseType(..)) => {
                                                    cond_predicate.clone().and(Predicate::IsOkay(cond_formula.clone()))
                                                },
                                                Some(x) => {
                                                    return Err(Error::Bug(format!("Did not get (optional ..) or (response ..) type (got {x:?}) for symbol {cond_sym}")));
                                                }
                                                None => {
                                                    return Err(Error::Bug(format!("Did not get any type information for symbol {cond_sym}")));
                                                }
                                            };

                                            ok_cont.final_formula = SymOp::UnwrapPanic(Box::new(cond_formula.clone()));

                                            let mut err_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}.cond-false"), err_sym.span.start_line);
                                            // case 2: (is-ok x) (or (is-some x)) is false
                                            err_cont.predicate = match self.typemap(&cur_contract)?.get_type_expected(&cond_sym) {
                                                Some(TypeSignature::OptionalType(..)) => {
                                                    cond_predicate.and(Predicate::IsNone(cond_formula.clone()))
                                                }
                                                Some(TypeSignature::ResponseType(..)) => {
                                                    cond_predicate.and(Predicate::IsErr(cond_formula.clone()))
                                                }
                                                Some(x) => {
                                                    return Err(Error::Bug(format!("Did not get (optional ..) or (response ..) type (got {x:?}) for symbol {cond_sym}")));
                                                }
                                                None => {
                                                    return Err(Error::Bug(format!("Did not get any type information for symbol {cond_sym}")));
                                                }
                                            };

                                            trace!("Continuation {} is early-return", err_cont.id);
                                            err_cont.early_return = true;

                                            new_conts.push(ok_cont);
                                            new_conts.push(err_cont);
                                        }
                                    }

                                    new_conts
                                }
                                "unwrap-err!" => {
                                    // evaluate `(unwrap-err! x y)`, where `x` evaluates to `(response v w)`
                                    // and `y` evaluates to `(err z)`
                                    //
                                    // NOTE: The Clarity VM will evaluate both x and y, in that
                                    // order

                                    let Some(cond_sym) = lv.get(1).cloned() else {
                                        return Err(Error::Bug(format!("Missing argument 1 to {function_name}")));
                                    };
                                    let Some(err_sym) = lv.get(2).cloned() else {
                                        return Err(Error::Bug(format!("Missing argument 2 to {function_name}")));
                                    };

                                    let mut new_conts = vec![];

                                    // evaluate `x`
                                    let cond_conts = self.eval(&config, Continuation::from_parent(Rc::new(continuation), format!("{function_name}.cond-eval"), cond_sym.span.start_line), &cond_sym)?;

                                    // evaluate `y` from each `x`
                                    for cond_cont in cond_conts.into_iter() {
                                        if cond_cont.halted() {
                                            new_conts.push(cond_cont);
                                            continue;
                                        }
                                        let cond_formula = cond_cont.final_formula.clone();

                                        let parent_rc = Rc::new(cond_cont);
                                        let err_conts = self.eval(&config, Continuation::from_parent(parent_rc, format!("{function_name}.err-eval"), err_sym.span.start_line), &err_sym)?;

                                        for parent_cont in err_conts.into_iter() {
                                            if parent_cont.halted() {
                                                new_conts.push(parent_cont);
                                                continue;
                                            }

                                            let cond_predicate = parent_cont.predicate.clone();
                                            let parent_rc = Rc::new(parent_cont);

                                            // case 1: `(is-err x)` is true
                                            let mut is_err_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}.is-err"), cond_sym.span.start_line);
                                            is_err_cont.predicate = cond_predicate.clone().and(Predicate::IsErr(cond_formula.clone()));
                                            is_err_cont.final_formula = SymOp::UnwrapErrPanic(Box::new(cond_formula.clone()));

                                            // case 2: `(is-err x)` is false
                                            let mut err_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}.is-ok"), err_sym.span.start_line);
                                            err_cont.predicate = cond_predicate.and(Predicate::IsOkay(cond_formula.clone()));
                                            
                                            trace!("Continuation {} is early-return", err_cont.id);
                                            err_cont.early_return = true;

                                            new_conts.push(is_err_cont);
                                            new_conts.push(err_cont);
                                        }
                                    }

                                    new_conts
                                }
                                "match" => {
                                    // evaluate `(match x (ok y) z (err v) w)`, or
                                    // evaluate `(match x (some y) z w)`
                                    if lv.len() == 6 {
                                        // evaluate `(match x (ok y) z (err v) w)`, or
                                        let Some(cond_sym) = lv.get(1).cloned() else {
                                            return Err(Error::Bug(format!("Missing argument 1 to {function_name}")));
                                        };
                                        
                                        let Some(ok_sym_name) = lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.match_atom() else {
                                            return Err(Error::Bug(format!("Argument 2 is not an atom in {function_name}")));
                                        };

                                        let Some(cond_ok_sym) = lv.get(3).cloned() else {
                                            return Err(Error::Bug(format!("Missing argument 3 to {function_name}")));
                                        };
                                        
                                        let Some(err_sym_name) = lv.get(4).ok_or_else(|| Error::Bug(format!("Missing argument 4 to {function_name}")))?.match_atom() else {
                                            return Err(Error::Bug(format!("Argument 4 is not an atom in {function_name}")));
                                        };
                                        
                                        let Some(cond_err_sym) = lv.get(5).cloned() else {
                                            return Err(Error::Bug(format!("Missing argument 5 to {function_name}")));
                                        };

                                        let mut new_conts = vec![];

                                        let cond_conts = self.eval(&config, Continuation::from_parent(Rc::new(continuation), format!("{function_name}.cond-eval"), cond_sym.span.start_line), &cond_sym)?;
                                        for cond_cont in cond_conts.into_iter() {
                                            if cond_cont.halted() {
                                                new_conts.push(cond_cont);
                                                continue;
                                            }
                                            let parent_pred = cond_cont.predicate.clone();
                                            let cond_formula = cond_cont.final_formula.clone();
                                            let parent_rc = Rc::new(cond_cont);

                                            // case 1: (ok y)
                                            let mut ok_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}.ok-case"), cond_ok_sym.span.start_line);

                                            ok_cont.predicate = parent_pred.clone().and(Predicate::IsOkay(cond_formula.clone()));
                                            ok_cont.bind_symop(&ok_sym_name.clone(), SymOp::UnwrapPanic(Box::new(cond_formula.clone())).simplify()?);

                                            let mut ok_conts = self.eval(&config, ok_cont, &cond_ok_sym)?;
                                            for ok_cont in ok_conts.iter_mut() {
                                                ok_cont.unbind(ok_sym_name);
                                            }
                                            new_conts.extend(ok_conts.into_iter());

                                            // case 2: (err y)
                                            let mut err_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}.err-eval"), cond_err_sym.span.start_line);

                                            err_cont.predicate = parent_pred.clone().and(Predicate::IsErr(cond_formula.clone()));
                                            err_cont.bind_symop(&err_sym_name.clone(), SymOp::UnwrapErrPanic(Box::new(cond_formula.clone())).simplify()?);

                                            let mut err_conts = self.eval(&config, err_cont, &cond_err_sym)?;
                                            for err_cont in err_conts.iter_mut() {
                                                err_cont.unbind(err_sym_name);
                                            }
                                            new_conts.extend(err_conts.into_iter());
                                        }

                                        new_conts
                                    }
                                    else if lv.len() == 5 {
                                        // evaluate `(match x (some y) z w)`
                                        let Some(cond_sym) = lv.get(1).cloned() else {
                                            return Err(Error::Bug(format!("Missing argument 1 to {function_name}")));
                                        };
                                        
                                        let Some(some_sym_name) = lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.match_atom() else {
                                            return Err(Error::Bug(format!("Argument 2 is not an atom in {function_name}")));
                                        };

                                        let Some(cond_some_sym) = lv.get(3).cloned() else {
                                            return Err(Error::Bug(format!("Missing argument 3 to {function_name}")));
                                        };

                                        let Some(cond_none_sym) = lv.get(4).cloned() else {
                                            return Err(Error::Bug(format!("Missing argument 4 to {function_name}")));
                                        };

                                        let mut new_conts = vec![];

                                        let cond_conts = self.eval(&config, Continuation::from_parent(Rc::new(continuation), format!("{function_name}.cond"), cond_sym.span.start_line), &cond_sym)?;
                                        for cond_cont in cond_conts.into_iter() {
                                            if cond_cont.halted() {
                                                new_conts.push(cond_cont);
                                                continue;
                                            }

                                            let parent_pred = cond_cont.predicate.clone();
                                            let cond_formula = cond_cont.final_formula.clone();
                                            let parent_rc = Rc::new(cond_cont);

                                            // case 1: (some y)
                                            let mut some_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}.is-some"), cond_some_sym.span.start_line);

                                            some_cont.predicate = parent_pred.clone().and(Predicate::IsSome(cond_formula.clone()));
                                            some_cont.bind_symop(&some_sym_name.clone(), SymOp::UnwrapPanic(Box::new(cond_formula.clone())).simplify()?);

                                            let mut some_conts = self.eval(&config, some_cont, &cond_some_sym)?;
                                            for some_cont in some_conts.iter_mut() {
                                                some_cont.unbind(some_sym_name);
                                            }
                                            new_conts.extend(some_conts.into_iter());

                                            // case 2: none
                                            let mut none_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}.is-none"), cond_none_sym.span.start_line);

                                            none_cont.predicate = parent_pred.clone().and(Predicate::IsNone(cond_formula.clone()));

                                            let none_conts = self.eval(&config, none_cont, &cond_none_sym)?;
                                            new_conts.extend(none_conts.into_iter());
                                        }

                                        new_conts
                                    }
                                    else {
                                        return Err(Error::Bug(format!("Wrong number of arguments to `match` in {:?}", &body)));
                                    }
                                }
                                "try!" => {
                                    // evaluate `(optional x)` or `(response y z)`
                                    let Some(exp_sym) = lv.get(1).cloned() else {
                                        return Err(Error::Bug(format!("Missing argument 1 to {function_name}")));
                                    };

                                    let parent_rc = Rc::new(continuation);

                                    let mut new_conts = vec![];
                                    let cond_conts = self.eval(&config, Continuation::from_parent(parent_rc, format!("{function_name}.inner"), exp_sym.span.start_line), &exp_sym)?;
                                    for cond_cont in cond_conts.into_iter() {
                                        if cond_cont.halted() {
                                            new_conts.push(cond_cont);
                                            continue;
                                        }

                                        let cond_formula = cond_cont.final_formula.clone();
                                        let cond_predicate = cond_cont.predicate.clone();

                                        let parent_rc = Rc::new(cond_cont);

                                        // case 1: `(is-ok x)` is true or `(is-some x)` is true
                                        let mut ok_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}.success"), exp_sym.span.start_line);

                                        ok_cont.predicate = match self.typemap(&cur_contract)?.get_type_expected(&exp_sym) {
                                            Some(TypeSignature::OptionalType(..)) => {
                                                cond_predicate.clone().and(Predicate::IsSome(cond_formula.clone()))
                                            }
                                            Some(TypeSignature::ResponseType(..)) => {
                                                cond_predicate.clone().and(Predicate::IsOkay(cond_formula.clone()))
                                            },
                                            Some(x) => {
                                                return Err(Error::Bug(format!("Did not get (optional ..) or (response ..) type (got {x:?}) for symbol {exp_sym}")));
                                            }
                                            None => {
                                                return Err(Error::Bug(format!("Did not get any type information for symbol {exp_sym}")));
                                            }
                                        };
                                        ok_cont.final_formula = SymOp::UnwrapPanic(Box::new(cond_formula.clone()));

                                        // case 2: (is-ok x) or (is-some x) is false
                                        let mut fail_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}.failure"), exp_sym.span.start_line);
                                        let (fail_formula, fail_predicate) = match self.typemap(&cur_contract)?.get_type_expected(&exp_sym) {
                                            Some(TypeSignature::OptionalType(..)) => {
                                                (
                                                    SymOp::none(),
                                                    cond_predicate.and(Predicate::IsNone(cond_formula.clone()))
                                                )
                                            }
                                            Some(TypeSignature::ResponseType(..)) => {
                                                (
                                                    // SymOp::UnwrapErrPanic(Box::new(cond_formula.clone())),
                                                    cond_formula.clone(),
                                                    cond_predicate.and(Predicate::IsErr(cond_formula.clone()))
                                                )
                                            }
                                            Some(x) => {
                                                return Err(Error::Bug(format!("Did not get (optional ..) or (response ..) type (got {x:?}) for symbol {exp_sym}")));
                                            }
                                            None => {
                                                return Err(Error::Bug(format!("Did not get any type information for symbol {exp_sym}")));
                                            }
                                        };
                                            
                                        trace!("Continuation {} is early-return", fail_cont.id);
                                        fail_cont.early_return = true;
                                        fail_cont.final_formula = fail_formula;
                                        fail_cont.predicate = fail_predicate;

                                        new_conts.push(ok_cont);
                                        new_conts.push(fail_cont);
                                    }

                                    new_conts
                                }
                                "filter" => {
                                    let Some(func_name) = lv.get(1).ok_or_else(|| Error::Bug("Missing function".into()))?.match_atom() else {
                                        return Err(Error::Bug("map function is not an atom".into()));
                                    };
                                    let sequence = lv.get(2).ok_or_else(|| Error::Bug("Missing sequence".into()))?;
                                    let Some(seq_ts) = self.typemap(&cur_contract)?.get_type_expected(sequence).cloned() else {
                                        return Err(Error::Bug(format!("No type information for sequence {sequence:?}")));
                                    };

                                    let seq_maxlen = Self::sequence_maxlen(&seq_ts)?;

                                    let mut final_conts = vec![];
                                    let mut ret = vec![];

                                    let conts = self.eval(&config, Continuation::from_parent(Rc::new(continuation), format!("{function_name}.sequence"), sequence.span.start_line), &sequence)?;

                                    // for each sequence continuation, apply the given
                                    // function on each item in the sequence.
                                    //
                                    // We don't know how many items are in the sequence, so we need
                                    // to generate a continuation for each possible length.
                                    for cont in conts.into_iter() {
                                        if cont.halted() {
                                            ret.push(cont);
                                            continue;
                                        }

                                        let seq_formula = cont.final_formula.clone();

                                        // create zero-length continuations, but keep the
                                        // predicates separate for now.
                                        let mut zero_length_conts = vec![];
                                        let len_eq_zero = SymOp::Equals(vec![Box::new(SymOp::Constant(Value::UInt(0))), Box::new(SymOp::Len(Box::new(seq_formula.clone())))]).try_as_predicate()?;

                                        // make a continuation that descends from the sequence
                                        // continuation and has a final formula with an empty
                                        // sequence.
                                        let parent_line = cont.current_line.clone().expect("unreachable -- parent continuation of a sequence continuation should be a `filter` and thus have a symbolic expression");
                                        let mut empty_cont = Continuation::from_parent(Rc::new(cont), format!("{function_name}/{func_name}.empty"), parent_line);

                                        // filter produces a sequence with the same type as the
                                        // input sequence.
                                        let final_formula = match seq_ts {
                                            TypeSignature::SequenceType(SequenceSubtype::BufferType(..)) => SymOp::Constant(Value::buff_from(vec![])?),
                                            TypeSignature::SequenceType(SequenceSubtype::ListType(..)) => SymOp::Constant(Value::cons_list(vec![], &DEFAULT_STACKS_EPOCH)?),
                                            TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(..))) => SymOp::Constant(Value::string_ascii_from_bytes(vec![])?),
                                            TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(..))) => SymOp::Constant(Value::string_utf8_from_bytes(vec![])?),
                                            _ => {
                                                return Err(Error::Bug("mapped sequence does not have a sequence type".into()));
                                            }
                                        };

                                        empty_cont.final_formula = final_formula.clone();
                                        zero_length_conts.push((len_eq_zero, final_formula, empty_cont.clone()));

                                        final_conts.push(zero_length_conts.clone());

                                        let mut cont_sets = vec![zero_length_conts];

                                        // for a sequence of length 1 or more, we call the function
                                        // on the ith sequence item
                                        for seq_i in 1..=seq_maxlen {
                                            let seq_i = u128::try_from(seq_i).map_err(|_| Error::Bug("Cannot convert usize to u128".into()))?;
                                            let len_eq_i = SymOp::Equals(vec![Box::new(SymOp::Constant(Value::UInt(seq_i))), Box::new(SymOp::Len(Box::new(seq_formula.clone())))]).try_as_predicate()?;
                                           
                                            // group continuations of executing up to the ith
                                            // element by parent in order to preserve logical
                                            // dependency.
                                            let mut next_conts = vec![];
                                            for cont_set in cont_sets.into_iter() {
                                                for (_pred, seq_cons, cont) in cont_set.into_iter() {
                                                    if cont.halted() {
                                                        ret.push(cont);
                                                        continue;
                                                    }
                                                    if let Some(func) = self.contract_context(&cur_contract)?.functions.get(func_name).cloned() {
                                                        // user-defined function
                                                        if func.arguments.len() != 1 {
                                                            return Err(Error::Bug(format!("Function `{func_name}` takes {} arguments but expected 1 argument", func.arguments.len())));
                                                        }
                                                        let mut binding_cont = Continuation::from_parent(Rc::new(cont), format!("{function_name}/{func_name}.seq-{seq_i}.binding"), func.body.span.start_line);                                                        
                                                        binding_cont.bind_symop(&func.arguments[0], SymOp::UnwrapPanic(Box::new(SymOp::ElementAt(Box::new(seq_formula.clone()), Box::new(SymOp::Constant(Value::UInt(seq_i - 1)))))).simplify()?);

                                                        let mut return_conts = vec![];
                                                        let body_conts = match self.eval_shortcircuit_higher_order_contract_function(&config, func_name, binding_cont, func.body.span.start_line)? {
                                                            Ok(conts) => conts,
                                                            Err(binding_cont) => {
                                                                // have to directly evaluate
                                                                let callee_cont = Continuation::from_caller(Rc::new(binding_cont), format!("{function_name}/{func_name}.seq-{seq_i}.body"), func_name.to_string(), func.body.span.start_line);
                                                                let body_conts = self.eval(&config, callee_cont, &func.body)?;
                                                                body_conts
                                                            }
                                                        };

                                                        for cont in body_conts.into_iter() {
                                                            if cont.panicking {
                                                                ret.push(cont);
                                                                continue;
                                                            }
                                                            if cont.early_return {
                                                                // should not be possible since the
                                                                // function returns a bool
                                                                return Err(Error::Bug("filter function had an early-return".into()));
                                                            }

                                                            // there are two continuations: either
                                                            // the function evaluated to true, or
                                                            // false.  In the first case, the final
                                                            // formula is the previous
                                                            // continuation's list cons plus this
                                                            // sequence item.  In the second case,
                                                            // it's the previous continuation's
                                                            // list cons with no new items.
                                                            // Both continuations entail the
                                                            // `len_eq_i` predicate.
                                                            let func_result = cont.final_formula.clone();
                                                            let seq_item = SymOp::UnwrapPanic(Box::new(SymOp::ElementAt(Box::new(seq_formula.clone()), Box::new(SymOp::Constant(Value::UInt(seq_i - 1))))));
                                                            let parent_rc = Rc::new(cont);

                                                            let true_seq_cons = match seq_ts {
                                                                TypeSignature::SequenceType(SequenceSubtype::BufferType(..)) => {
                                                                    seq_cons.clone().concat(seq_item)
                                                                },
                                                                TypeSignature::SequenceType(SequenceSubtype::ListType(..)) => {
                                                                    seq_cons.clone().list_cons(seq_item)
                                                                },
                                                                TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(..))) => {
                                                                    seq_cons.clone().concat(seq_item)
                                                                },
                                                                TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(..))) =>  {
                                                                    seq_cons.clone().concat(seq_item)
                                                                },
                                                                _ => {
                                                                    return Err(Error::Bug("filtered sequence does not have a sequence type".into()));
                                                                }
                                                            };

                                                            let mut true_cont = Continuation::from_callee(parent_rc.clone(), format!("{function_name}/{func_name}.seq-{seq_i}.true"), func.body.span.start_line);
                                                            true_cont.predicate = true_cont.predicate.and(func_result.clone().try_as_predicate()?);
                                                            true_cont.final_formula = true_seq_cons.clone();

                                                            let mut false_cont = Continuation::from_callee(parent_rc, format!("{function_name}/{func_name}.seq-{seq_i}.false"), func.body.span.start_line);
                                                            false_cont.predicate = false_cont.predicate.and(func_result.clone().try_as_predicate()?.not());
                                                            false_cont.final_formula = seq_cons.clone();

                                                            true_cont.unbind(&func.arguments[0]);
                                                            false_cont.unbind(&func.arguments[0]);
                                                            
                                                            return_conts.push((len_eq_i.clone(), true_seq_cons, true_cont));
                                                            return_conts.push((len_eq_i.clone(), seq_cons.clone(), false_cont));
                                                        }
                                                        next_conts.push(return_conts);
                                                    }
                                                    else {
                                                        // native function
                                                        todo!("Native functions not supported yet for fold");
                                                    }
                                                }
                                            }
                                            cont_sets = next_conts;
                                            final_conts.extend(cont_sets.clone().into_iter());
                                        }
                                    }
                                    for cont_set in final_conts.into_iter() {
                                        for (pred, _formula, mut cont) in cont_set.into_iter() {
                                            cont.predicate = cont.predicate.clone().and(pred);
                                            ret.push(cont);
                                        }
                                    }
                                    ret
                                },
                                "define-constant"
                                | "define-private"
                                | "define-read-only"
                                | "define-public"
                                | "define-trait"
                                | "impl-trait"
                                | "use-trait"
                                | "define-map"
                                | "define-data-var" => {
                                    // already handled
                                    vec![continuation]
                                }
                                "if" => {
                                    self.eval_if(
                                        &config,
                                        continuation,
                                        lv.get(1).ok_or_else(|| Error::Bug("Missing if-predicate".into()))?.clone(),
                                        lv.get(2).ok_or_else(|| Error::Bug("Missing if-true branch".into()))?.clone(),
                                        lv.get(3).ok_or_else(|| Error::Bug("Missing if-else branch".into()))?.clone(),
                                    )?
                                }
                                "let" => {
                                    self.let_bind(&config, continuation, lv.get(1..).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?)?
                                },
                                "map" => {
                                    // When evaluating `(map func sequence-1 sequence-2 ... sequence-n)`,
                                    // the Clarity VM first evaluates `sequence-1`, then `sequence-2`, 
                                    // up to `sequence-n`.  It then internally zips `sequence-1`,
                                    // `sequence-2`, up to `sequence-n`, and applies `func` on each
                                    // zipped item.  `map` stops at the end of the shortest given
                                    // sequence.

                                    let Some(func_name) = lv.get(1).ok_or_else(|| Error::Bug("Missing function".into()))?.match_atom() else {
                                        return Err(Error::Bug("map function is not an atom".into()));
                                    };
                                    let sequences = lv.get(2..).ok_or_else(|| Error::Bug("Missing sequences".into()))?;

                                    if sequences.len() == 0 {
                                        return Err(Error::Bug("No sequences given".into()));
                                    }

                                    let mut seq_len = usize::MAX;
                                    for s in sequences {
                                        let sz = if let Some(ts) = self.typemap(&cur_contract)?.get_type_expected(s) {
                                            Self::sequence_maxlen(ts)?
                                        }
                                        else {
                                            return Err(Error::Bug(format!("No type information for sequence {s:?}")));
                                        };
                                        seq_len = seq_len.min(sz);
                                    }

                                    // evaluate each sequence, but preserve the final formulas for
                                    // each one (i.e. by way of preserving their continuations)
                                    let mut last_conts = vec![continuation];
                                    let mut sequence_conts = vec![];
                                    for (i, seq) in sequences.iter().enumerate() {
                                        let mut next_conts = vec![];
                                        for last_cont in last_conts.into_iter() {
                                            if last_cont.halted() {
                                                next_conts.push(last_cont);
                                                continue;
                                            }

                                            let conts = self.eval(&config, Continuation::from_parent(Rc::new(last_cont), format!("{function_name}.seq-{i}"), seq.span.start_line), seq)?;
                                            next_conts.extend(conts.into_iter());
                                        }
                                        sequence_conts.push(next_conts.clone());
                                        last_conts = next_conts;
                                    }

                                    // accumulate evaluation of `func` up to i.
                                    // Bind a particular set of function arguments to the last
                                    // continuation evaluated on them.
                                    let mut list_cons_items : HashMap<(u128, Vec<usize>), Vec<Continuation>> = HashMap::new();
                                    let mut list_cons_preds : HashMap<(u128, Vec<usize>), Predicate> = HashMap::new();
                                   
                                    // make a continuation to cons a list of all lengths up to
                                    // `seq_len`.  The predicate asserts that each list is long
                                    // enough.
                                    for seq_i in 0..=seq_len {
                                        let seq_i = u128::try_from(seq_i).map_err(|_| Error::Bug("Cannot convert usize to u128".into()))?;

                                        // compute the predicate for computing `func` over these
                                        // sequences for up to `i` elements.  Do so for each
                                        // combination of formulae for each sequence.   Each unique
                                        // combination represents a set of disjoint continuations,
                                        // and will be used to key them in `list_cons_items`.
                                        let mut form_idx : Vec<usize> = vec![0; sequence_conts.len()];
                                        assert_eq!(form_idx.len(), sequences.len());
                                        assert_eq!(form_idx.len(), sequence_conts.len());
                                        
                                        let last_form = form_idx.len() - 1;
                                        while form_idx[last_form] < sequence_conts[last_form].len() {
                                            // i must be equal to the length of the
                                            // smallest sequence.  That is, i is less than or
                                            // equal to the length of all sequences, and i is
                                            // equal to the length of at least one sequence.
                                            let seq_i_matches_shortest_seq_predicate = if sequence_conts.len() == 1 {
                                                // `(is-eq seq_i (len seq))`
                                                SymOp::Equals(vec![Box::new(SymOp::Constant(Value::UInt(seq_i))), Box::new(SymOp::Len(Box::new(sequence_conts[0][form_idx[0]].final_formula.clone())))])
                                            }
                                            else {
                                                if seq_i == 0 {
                                                    // optimization -- only check if at least one
                                                    // sequence is zero, since all of their lengths
                                                    // are at least zero
                                                    let mut zero_checks = vec![];
                                                    for (s1, f1) in form_idx.iter().enumerate() {
                                                        // the ith sequence is the smallest sequence
                                                        let zero_check = SymOp::Equals(vec![Box::new(SymOp::Constant(Value::UInt(seq_i))), Box::new(SymOp::Len(Box::new(sequence_conts[s1][*f1].final_formula.clone())))]);
                                                        zero_checks.push(Box::new(zero_check));
                                                    }
                                                    SymOp::Or(zero_checks)
                                                }
                                                else {
                                                    // at least one sequence is exactly this length.
                                                    // It's an OR of the following for each `seq-X`
                                                    // ```
                                                    // (and
                                                    //    (is-eq seq_i (len seq-a))
                                                    //    (<= seq_i (len seq-b))
                                                    //    (<= seq_i (len seq-c))
                                                    //    ...
                                                    //    (<= seq_i (len seq-n)))
                                                    // ```
                                                    let mut small_checks = vec![];
                                                    for (s1, f1) in form_idx.iter().enumerate() {
                                                        // the ith sequence is the smallest sequence
                                                        let len_eq_check = SymOp::Equals(vec![Box::new(SymOp::Constant(Value::UInt(seq_i))), Box::new(SymOp::Len(Box::new(sequence_conts[s1][*f1].final_formula.clone())))]);

                                                        let mut smallest_len_checks = vec![Box::new(len_eq_check)];
                                                        for (s2, f2) in form_idx.iter().enumerate() {
                                                            // all other sequences are at least as long
                                                            if s1 == s2 {
                                                                continue;
                                                            }
                                                            let small_check = SymOp::Leq(Box::new(SymOp::Constant(Value::UInt(seq_i))), Box::new(SymOp::Len(Box::new(sequence_conts[s2][*f2].final_formula.clone()))));
                                                            smallest_len_checks.push(Box::new(small_check));
                                                        }

                                                        small_checks.push(Box::new(SymOp::And(smallest_len_checks)));
                                                    }
                                                    SymOp::Or(small_checks)
                                                }
                                            };

                                            // the combined predicate.
                                            // Keep predicates out of continuations for now, since
                                            // if we add them, it may cause some predicates to be
                                            // evaluated as unreachable prematurely.
                                            let predicate = seq_i_matches_shortest_seq_predicate.try_as_predicate()?;
                                            list_cons_preds.insert((seq_i, form_idx.clone()), predicate);

                                            // the final formula:
                                            // ```
                                            // (list
                                            //    (func
                                            //       (unwrap-panic (element-at seq-1 u0))
                                            //       (unwrap-panic (element-at seq-2 u0))
                                            //       ...
                                            //       (unwrap-panic (element-at seq-n u0)))
                                            //
                                            //    (func
                                            //       (unwrap-panic (element-at seq-1 u1))
                                            //       (unwrap-panic (element-at seq-2 u1))
                                            //       ...
                                            //       (unwrap-panic (element-at seq-n u1)))
                                            //
                                            //    ...
                                            //    (func
                                            //       (unwrap-panic (element-at seq-1 k))
                                            //       (unwrap-panic (element-at seq-2 k))
                                            //       ...
                                            //       (unwrap-panic (element-at seq-n k)))
                                            // ```
                                            //
                                            // We already have list items up to i-1, so just
                                            // compute those for i.
                                            if seq_i == 0 {
                                                // no need to evaluate any function, since it will
                                                // never be called.  The final formula will be an
                                                // empty list with the type given by the function
                                                // body.
                                                let final_formula = SymOp::ListCons(vec![]);
                                                let mut empty_conts = vec![];
                                                for cont in last_conts.iter() {
                                                    if cont.halted() {
                                                        empty_conts.push(cont.clone());
                                                        continue;
                                                    }

                                                    let parent_start_line = cont.current_line.clone().expect("unreachable -- parent continuation of a sequence continuation should be a `map` and thus have a symbolic expression");
                                                    let mut empty_cont = Continuation::from_parent(Rc::new(cont.clone()), format!("{function_name}/{func_name}.seq-{seq_i}.empty"), parent_start_line);
                                                    empty_cont.final_formula = final_formula.clone();
                                                    empty_conts.push(empty_cont);
                                                }
                                                list_cons_items.insert((seq_i, form_idx.clone()), empty_conts);
                                            }
                                            else {
                                                let mut elems_i = vec![];
                                                for (s, f) in form_idx.iter().enumerate() {
                                                    let elem = SymOp::UnwrapPanic(Box::new(SymOp::ElementAt(Box::new(sequence_conts[s][*f].final_formula.clone()), Box::new(SymOp::Constant(Value::UInt(seq_i - 1))))));
                                                    elems_i.push(elem);
                                                }
                                            
                                                // evaluate `func` from each continuation, using this
                                                // particular set of elements as function arguments.
                                                if let Some(func) = self.contract_context(&cur_contract)?.functions.get(func_name).cloned() {
                                                    // user-defined function
                                                    if func.arguments.len() != elems_i.len() {
                                                        return Err(Error::Bug(format!("Function takes {} arguments but computed {} arguments", func.arguments.len(), elems_i.len())));
                                                    }

                                                    let mut called_conts = vec![];
                                                    let (caller_conts, list_conses) = {
                                                        let Some(conts) = list_cons_items.get(&((seq_i - 1), form_idx.clone())).cloned() else {
                                                            return Err(Error::Bug(format!("Missing continuations entry for ({}, {:?})", seq_i, &form_idx.clone())));
                                                        };
                                                        (conts.clone(), conts.iter().map(|c| c.final_formula.clone()).collect::<Vec<_>>())
                                                    };

                                                    assert_eq!(caller_conts.len(), list_conses.len());

                                                    for (caller_cont, list_cons) in caller_conts.into_iter().zip(list_conses.into_iter()) {
                                                        if caller_cont.halted() {
                                                            called_conts.push(caller_cont);
                                                            continue;
                                                        }

                                                        // this continuation must descend from the
                                                        // continuations which produced all of these
                                                        // function arguments
                                                        let mut descends = true;
                                                        for (s, f) in form_idx.iter().enumerate() {
                                                            if !caller_cont.descends_from(&sequence_conts[s][*f]) {
                                                                descends = false;
                                                                break;
                                                            }
                                                        }
                                                        if !descends {
                                                            continue;
                                                        }
                                                        // this continuation descends from this
                                                        // particular set of function arguments, so we
                                                        // can evaluate the function on them.
                                                        let mut binding_cont = Continuation::from_parent(Rc::new(caller_cont), format!("{function_name}/{func_name}.seq-{seq_i}.binding"), func.body.span.start_line);

                                                        let mut bound = vec![];
                                                        for (arg_name, elem_i) in func.arguments.iter().zip(elems_i.iter()) {
                                                            binding_cont.bind_symop(arg_name, elem_i.clone().simplify()?);
                                                            bound.push(arg_name.clone());
                                                        }

                                                        let conts = match self.eval_shortcircuit_higher_order_contract_function(&config, func_name, binding_cont, func.body.span.start_line)? {
                                                            Ok(conts) => {
                                                                conts
                                                                    .into_iter()
                                                                    .map(|mut c| {
                                                                        if c.panicking {
                                                                            return c;
                                                                        }
                                                                        let return_formula = c.final_formula.clone();

                                                                        // return value is a list-cons of all
                                                                        // values up to seq_i
                                                                        c.final_formula = if let SymOp::ListCons(mut items) = list_cons.clone() {
                                                                            items.push(Box::new(return_formula.clone()));
                                                                            SymOp::ListCons(items)
                                                                        }
                                                                        else {
                                                                            unreachable!()
                                                                        };
                                                                        for unbind in bound.iter() {
                                                                            c.unbind(unbind);
                                                                        }
                                                                        c
                                                                    })
                                                                    .collect()
                                                            },
                                                            Err(binding_cont) => {
                                                                // have to directly evaluate
                                                                let callee_cont = Continuation::from_caller(Rc::new(binding_cont), format!("{function_name}/{func_name}.seq-{seq_i}.body"), func_name.to_string(), func.body.span.start_line);
                                                                let body_conts : Vec<_> = self.eval(&config, callee_cont, &func.body)?
                                                                    .into_iter()
                                                                    .map(|cont| {
                                                                        if cont.panicking {
                                                                            return cont;
                                                                        }
                                                                        let mut return_cont = Continuation::from_callee(Rc::new(cont), format!("{function_name}/{func_name}.seq-{seq_i}.return"), func.body.span.start_line);
                                                                        let return_formula = return_cont.final_formula.clone();

                                                                        // return value is a list-cons of all
                                                                        // values up to seq_i
                                                                        return_cont.final_formula = if let SymOp::ListCons(mut items) = list_cons.clone() {
                                                                            items.push(Box::new(return_formula));
                                                                            SymOp::ListCons(items)
                                                                        }
                                                                        else {
                                                                            unreachable!()
                                                                        };
                                                                        
                                                                        for unbind in bound.iter() {
                                                                            return_cont.unbind(unbind);
                                                                        }
                                                                        return_cont
                                                                    })
                                                                    .collect();

                                                                body_conts
                                                            }
                                                        };

                                                        /*
                                                        let callee_cont = Continuation::from_caller(Rc::new(binding_cont), format!("{function_name}/{func_name}.seq-{seq_i}.body"), func_name.to_string(), func.body.span.start_line);
                                                        let conts = self.eval(&config, callee_cont, &func.body)?;
                                                        let conts : Vec<_> = conts
                                                            .into_iter()
                                                            .map(|cont| {
                                                                if cont.panicking {
                                                                    return cont;
                                                                }
                                                                let mut return_cont = Continuation::from_callee(Rc::new(cont), format!("{function_name}/{func_name}.seq-{seq_i}.return"), func.body.span.start_line);
                                                                let return_formula = return_cont.final_formula.clone();

                                                                // return value is a list-cons of all
                                                                // values up to seq_i
                                                                return_cont.final_formula = if let SymOp::ListCons(mut items) = list_cons.clone() {
                                                                    items.push(Box::new(return_formula));
                                                                    SymOp::ListCons(items)
                                                                }
                                                                else {
                                                                    unreachable!()
                                                                };
                                                                for unbind in bound.iter() {
                                                                    return_cont.unbind(unbind);
                                                                }
                                                                return_cont
                                                            })
                                                            .collect();
                                                        */

                                                        called_conts.extend(conts.into_iter());
                                                    }

                                                    // remember the continuations for this particular
                                                    // set of arguments
                                                    list_cons_items.insert((seq_i, form_idx.clone()), called_conts);
                                                }
                                                else {
                                                    // native function
                                                    todo!("Not a user function: {func_name}");
                                                }
                                            }

                                            // "increment"
                                            let mut carry = 0;
                                            for i in 0..form_idx.len() {
                                                if carry > 0 {
                                                    form_idx[i] += carry;
                                                }
                                                form_idx[i] += 1;
                                                if form_idx[i] >= sequence_conts[i].len() {
                                                    carry = sequence_conts[i].len() - form_idx[i];
                                                    form_idx[i] = form_idx[i] % sequence_conts[i].len();
                                                    if i == last_form {
                                                        // we've overflowed
                                                        form_idx[last_form] = usize::MAX;
                                                    }
                                                }
                                                else {
                                                    break;
                                                }
                                            }
                                        }
                                    }

                                    // accumulate all list_cons continuations and their associated
                                    // predicates
                                    let ret : Vec<_> = list_cons_items
                                        .into_iter()
                                        .map(|(key, mut conts)| {
                                            let pred = list_cons_preds.get(&key).expect(&format!("unreachable -- list_cont_preds lacks {key:?}"));
                                            for cont in conts.iter_mut() {
                                                cont.predicate = cont.predicate.clone().and(pred.clone());
                                            }
                                            conts
                                        })
                                        .flatten()
                                        .collect();

                                    ret
                                },
                                "fold" => {
                                    let Some(func_name) = lv.get(1).ok_or_else(|| Error::Bug("Missing function".into()))?.match_atom() else {
                                        return Err(Error::Bug("map function is not an atom".into()));
                                    };
                                    let sequence = lv.get(2).ok_or_else(|| Error::Bug("Missing sequence".into()))?;
                                    let initial_value = lv.get(3).ok_or_else(|| Error::Bug("Missing initial value".into()))?;
                                    
                                    let seq_maxlen = if let Some(ts) = self.typemap(&cur_contract)?.get_type_expected(sequence) {
                                        Self::sequence_maxlen(ts)?
                                    }
                                    else {
                                        return Err(Error::Bug(format!("No type information for sequence {sequence:?}")));
                                    };

                                    let mut ret = vec![];
                                    let conts = self.eval(&config, Continuation::from_parent(Rc::new(continuation), format!("{function_name}.sequence"), sequence.span.start_line), &sequence)?;

                                    let mut initial_conts = vec![];
                                    for cont in conts.into_iter() {
                                        if cont.halted() {
                                            ret.push(cont);
                                            continue;
                                        }
                                        let seq_formula = cont.final_formula.clone().simplify()?;
                                        let initial_value_conts = self.eval(&config, Continuation::from_parent(Rc::new(cont), format!("{function_name}.initial"), initial_value.span.start_line), &initial_value)?;
                                        initial_conts.push((seq_formula, initial_value_conts));
                                    }

                                    // for each set of initial value continuations (i.e. which
                                    // descend from the same sequence continuation), apply the given
                                    // function on each item in the sequence.
                                    //
                                    // We don't know how many items are in the sequence, so we need
                                    // to generate a continuation for each possible length.
                                    for (seq_formula, conts) in initial_conts.into_iter() {
                                        let mut final_conts = vec![];

                                        // for a zero-length list, just evaluate the initial value
                                        let mut zero_length_conts = vec![];
                                        for cont in conts.iter() {
                                            if cont.halted() {
                                                // should be unreachable since we filtered out
                                                // halted continuations above
                                                continue;
                                            }
                                            let len_eq_zero = SymOp::Equals(vec![Box::new(SymOp::Constant(Value::UInt(0))), Box::new(SymOp::Len(Box::new(seq_formula.clone())))]).try_as_predicate()?.simplify()?;
                                            zero_length_conts.push((len_eq_zero, cont.clone()));
                                        }

                                        final_conts.push(zero_length_conts.clone());

                                        let mut cont_sets = vec![zero_length_conts];

                                        // for a sequence of length 1 or more, we call the function
                                        // on initial value (and its successive values).
                                        for seq_i in 1..=seq_maxlen {
                                            let seq_i = u128::try_from(seq_i).map_err(|_| Error::Bug("Cannot convert usize to u128".into()))?;
                                            let len_eq_i = SymOp::Equals(vec![Box::new(SymOp::Constant(Value::UInt(seq_i))), Box::new(SymOp::Len(Box::new(seq_formula.clone())))]).try_as_predicate()?.simplify()?;
                                            
                                            let mut next_conts = vec![];
                                            let cont_set_set_len = cont_sets.len();
                                            for (cont_set_i, cont_set) in cont_sets.into_iter().enumerate() {
                                                let cont_set_len = cont_set.len();
                                                for (cont_i, (_pred, cont)) in cont_set.into_iter().enumerate() {
                                                    if cont.halted() {
                                                        continue;
                                                    }
                                                    if let Some(func) = self.contract_context(&cur_contract)?.functions.get(func_name).cloned() {
                                                        // user-defined function
                                                        if func.arguments.len() != 2 {
                                                            return Err(Error::Bug(format!("Function `{func_name}` takes {} arguments but expected 2 arguments", func.arguments.len())));
                                                        }
                                                        let value_formula = cont.final_formula.clone();
                                                        let mut binding_cont = Continuation::from_parent(Rc::new(cont), format!("{function_name}/{func_name}.seq-({seq_i}-of-{seq_maxlen})-cont-({cont_i}-of-{cont_set_len})-contset-({cont_set_i}-of-{cont_set_set_len}).binding"), func.body.span.start_line); 
                                                        binding_cont.bind_symop(&func.arguments[0], SymOp::UnwrapPanic(Box::new(SymOp::ElementAt(Box::new(seq_formula.clone()), Box::new(SymOp::Constant(Value::UInt(seq_i - 1)))))).simplify()?);
                                                        binding_cont.bind_symop(&func.arguments[1], value_formula.simplify()?);
                                                        let bound = vec![func.arguments[0].clone(), func.arguments[1].clone()];
                                                        let body_conts = match self.eval_shortcircuit_higher_order_contract_function(&config, func_name, binding_cont, func.body.span.start_line)? {
                                                            Ok(conts) => {
                                                                conts
                                                                    .into_iter()
                                                                    .map(|mut c| {
                                                                        if c.panicking {
                                                                            return (len_eq_i.clone(), c);
                                                                        }
                                                                        for unbind in bound.iter() {
                                                                            c.unbind(unbind);
                                                                        }
                                                                        (len_eq_i.clone(), c)
                                                                    })
                                                                    .collect()
                                                            },
                                                            Err(binding_cont) => {
                                                                // have to directly evaluate
                                                                let callee_cont = Continuation::from_caller(Rc::new(binding_cont), format!("{function_name}/{func_name}.seq-({seq_i}-of-{seq_maxlen})-cont-({cont_i}-of-{cont_set_len})-contset-({cont_set_i}-of-{cont_set_set_len}).body"), func_name.to_string(), func.body.span.start_line);
                                                                let body_conts : Vec<_> = self.eval(&config, callee_cont, &func.body)?
                                                                    .into_iter()
                                                                    .map(|cont| {
                                                                        if cont.panicking {
                                                                            return (len_eq_i.clone(), cont);
                                                                        }
                                                                        let mut return_cont = Continuation::from_callee(Rc::new(cont), format!("{function_name}/{func_name}.seq-({seq_i}-of-{seq_maxlen})-cont-({cont_i}-of-{cont_set_len})-contset-({cont_set_i}-of-{cont_set_set_len}).return"), func.body.span.start_line);
                                                                        
                                                                        for unbind in bound.iter() {
                                                                            return_cont.unbind(unbind);
                                                                        }
                                                                        (len_eq_i.clone(), return_cont)
                                                                    })
                                                                    .collect();

                                                                body_conts
                                                            }
                                                        };

                                                        next_conts.push(body_conts);
                                                    }
                                                    else {
                                                        // native function
                                                        todo!("Native functions not supported yet for fold");
                                                    }
                                                }
                                            }
                                            cont_sets = next_conts;
                                            final_conts.extend(cont_sets.clone().into_iter());
                                        }

                                        for cont_set in final_conts.into_iter() {
                                            for (pred, mut cont) in cont_set.into_iter() {
                                                cont.predicate = cont.predicate.clone().and(pred).simplify()?;
                                                if cont.predicate == Predicate::False {
                                                    continue;
                                                }
                                                ret.push(cont);
                                            }
                                        }
                                    }

                                    self.reduce_continuations(&config, ret)
                                },
                                "begin" => {
                                    let mut ret = vec![];
                                    let mut conts = vec![vec![continuation]];
                                    for (i, symexp) in lv.get(1..).ok_or_else(|| Error::Bug(format!("Missing symbolic expressions for ({function_base_name} ..)")))?.iter().enumerate() {
                                        let mut new_conts = vec![];
                                        for cont_set in conts.into_iter() {
                                            for cont in cont_set.into_iter() {
                                                if cont.halted() {
                                                    ret.push(cont);
                                                    continue;
                                                }
                                                if cont.predicate.clone().simplify()? == Predicate::False {
                                                    continue;
                                                }

                                                let next_conts = self.eval(&config, Continuation::from_parent(Rc::new(cont), format!("{function_name}.expr[{i}]"), symexp.span.start_line), symexp)?;
                                                new_conts.push(self.reduce_continuations(&config, next_conts));
                                            }
                                        }
                                        conts = new_conts;
                                    }
                                    for cont_set in conts.into_iter() {
                                        ret.extend(cont_set.into_iter());
                                    }
                                    ret
                                }
                                "print" => {
                                    let expr = lv.get(1).ok_or_else(|| Error::Bug("Missing argument to `print`".into()))?;
                                    let conts = self.eval(&config, Continuation::from_parent(Rc::new(continuation), function_name.to_string(), expr.span.start_line), expr)?;
                                    conts
                                }
                                "contract-call?" => {
                                    let contract_principal = self.get_contract_call_contract(&continuation, lv)?;
                                    let Some(target_func_name) = lv.get(2).ok_or_else(|| Error::Bug("No function name".into()))?.match_atom() else {
                                        return Err(Error::Bug(format!("contract-call function name not found: {:?}", &lv.get(2))));
                                    };
                                    let target_func_fullname = FullName(contract_principal.clone(), target_func_name.clone());
                                     
                                    let target_func_name_and_args = lv.get(2..).ok_or_else(|| Error::Bug("No function args".into()))?;

                                    if config.skip_contract_calls.contains(&target_func_fullname) {
                                        debug!("Skipping contract-call to {}", &target_func_fullname);
                                        unimplemented!();
                                    }

                                    let mut cc_cont = Continuation::from_parent(Rc::new(continuation), function_name.clone(), body.span.start_line);

                                    let old_contract_caller = cc_cont.get_contract_caller();
                                    let old_current_contract = cc_cont.get_current_contract();

                                    cc_cont.contract_caller = Some(SymOp::Constant(Value::Principal(cc_cont.get_current_contract())));
                                    cc_cont.current_contract = Some(PrincipalData::Contract(contract_principal.clone()));

                                    let mut conts = match self.eval_contract_function(&config, cc_cont, target_func_name, target_func_name_and_args, body.span.start_line)? {
                                        Ok(conts) => conts,
                                        Err(_) => {
                                            return Err(Error::Bug(format!("contract-call? to unknown user-defined function {target_func_name} in {contract_principal}")));
                                        }
                                    };

                                    for cont in conts.iter_mut() {
                                        cont.contract_caller = Some(old_contract_caller.clone());
                                        cont.current_contract = Some(old_current_contract.clone());
                                    }
                                    conts
                                }
                                "as-contract" => {
                                    return Err(Error::Bug("`as-contract` is deprecated and not supported by this tool".into()));
                                }
                                x => {
                                    todo!("native not implemented: {x}")
                                }
                            }
                        }
                    };
                    conts
                }
                else {
                    unreachable!()
                }
            }
            SymbolicExpressionType::AtomValue(_v) => {
                // bound arguments to a contract-call?, it seems
                unreachable!()
            },
            SymbolicExpressionType::Atom(cn) => {
                let parent_func = continuation.function_path.clone().unwrap_or("".to_string());
                let function_name = format!("{parent_func}/{}", &cn.as_str());
                let mut cont = Continuation::from_parent(Rc::new(continuation), function_name, body.span.start_line);
                if let Some(new_final_formula) = Self::try_atom_as_symbol(&cont, &cn)? {
                    cont.final_formula = new_final_formula;
                }
                else {
                    let symid : SymId = cn.as_str().into();
                    let Some(formula) = cont.lookup_formula(&symid) else {
                        error!("Faulty cont looking for '{}'", &symid);
                        error!("{}", &cont);
                        error!("Trace:\n{}", cont.trace());
                        return Err(Error::Bug(format!("Unbound formula '{}'", &cn)));
                    };
                    cont.final_formula = formula.clone();
                }
                vec![cont]
            },
            SymbolicExpressionType::Field(_ti) => {
                unreachable!()
            }
            SymbolicExpressionType::TraitReference(_cn, _td) => {
                unreachable!()
            }
        };
        debug!("Reduce continuations after {body} (parent cont was {cont_id} path {cont_path})"); 
        let mut continuations = self.reduce_continuations(&config, continuations);

        for continuation in continuations.iter() {
            trace!("eval continuation {}: {} pred={}, formula={}", continuation.id, &continuation.function_path.clone().unwrap_or("".to_string()), &continuation.predicate.clone().simplify().unwrap(), &continuation.final_formula.clone().simplify().unwrap());
        }

        self.run_post_commands(&config, body, original_continuation, &mut continuations)?;
        Ok(continuations)
    }

    fn apply_user_function(&mut self, config: &SymbexConfig, continuation: Continuation, function_name: &ClarityName, function_arg_values: &[SymbolicExpression]) -> Result<Vec<Continuation>, Error> {
        let cur_contract = continuation.get_current_contract_id();
        let fq_name = FullName(cur_contract.clone(), function_name.clone());

        let Some(func) = self.contract_context(&continuation.get_current_contract_id())?.functions.get(function_name).cloned() else {
            return Err(Error::NotFound(format!("No such function '{function_name}' in {} (id {})", &continuation.get_current_contract_id(), continuation.id)));
        };
        if function_arg_values.len() != func.arguments.len() {
            return Err(Error::Bug("Function argument values != function arguments or function_arguments != function argument types".into()));
        }

        let parent_function_name = continuation.function_path.clone().unwrap_or("".to_string());
        let fq_function = format!("{}.{}", &parent_function_name, function_name);

        // build up (final-continuation, list-of-argument-symops)
        let mut conts = vec![(continuation, vec![])];
        for (i, symexp) in function_arg_values.iter().enumerate() {
            let mut new_conts = vec![];
            for (cont, mut symops) in conts.into_iter() {
                let arg_conts = self.eval(config, Continuation::from_parent(Rc::new(cont), format!("{}.arg[{}]={}", &fq_function, i, &func.arguments[i]), symexp.span.start_line), symexp)?;
                for arg_cont in arg_conts.into_iter() {
                    if arg_cont.halted() {
                        new_conts.push((arg_cont, vec![]));
                        continue;
                    }
                    symops.push(arg_cont.final_formula.clone());
                    new_conts.push((arg_cont, symops.clone()));
                }
            }
            conts = new_conts;
        }

        let mut called_conts = vec![];
        for (caller_cont, symops) in conts.into_iter() {
            if caller_cont.halted() {
                called_conts.push(caller_cont);
                continue;
            }
            if symops.len() != function_arg_values.len() {
                return Err(Error::Bug("Function argument values != symops values".into()));
            }

            let mut binding_cont = Continuation::from_parent(Rc::new(caller_cont), format!("{}.binding", &fq_function), func.body.span.start_line);
            let mut bound = vec![];
            for (arg_name, symop) in func.arguments.iter().zip(symops.iter()) {
                binding_cont.bind_symop(arg_name, symop.clone().simplify()?);
                bound.push(arg_name.clone());
            }

            let callee_cont = Continuation::from_caller(Rc::new(binding_cont), format!("{}.body", &fq_function), function_name.to_string(), func.body.span.start_line);
            let conts = self.eval(config, callee_cont, &func.body)?;

            let conts : Vec<_> = conts
                .into_iter()
                .filter(|cont| {
                    if config.drop_early_returns.contains(&fq_name) && cont.early_return {
                        debug!("Will not evaluate early-return continuation {} of {fq_name}", cont.id);
                        false
                    }
                    else {
                        true
                    }
                })
                .map(|cont| {
                    if cont.panicking {
                        return cont;
                    }
                    let mut return_cont = Continuation::from_callee(Rc::new(cont), format!("{}.return", fq_function), func.body.span.start_line);
                    for unbind in bound.iter() {
                        return_cont.unbind(unbind);
                    }
                    return_cont
                })
                .collect();

            called_conts.extend(conts.into_iter());
        }
        Ok(self.reduce_continuations(&config, called_conts))
    }

    fn eval_if(&mut self, config: &SymbexConfig, continuation: Continuation, predicate_symexp: SymbolicExpression, if_true_symexp: SymbolicExpression, if_false_symexp: SymbolicExpression) -> Result<Vec<Continuation>, Error> {
        let parent_func = continuation.function_path.clone().unwrap_or("".to_string());
        let continuation_rc = Rc::new(continuation);
        let predicate_conts = self.eval(&config, Continuation::from_parent(continuation_rc.clone(), format!("{}/if", &parent_func), predicate_symexp.span.start_line), &predicate_symexp)?;
        let mut branch_conts = vec![];
        for predicate_cont in predicate_conts.into_iter() {
            if predicate_cont.halted() {
                branch_conts.push(predicate_cont);
                continue;
            }
            let predicate = predicate_cont.final_formula.try_as_predicate()?;
            let predicate_rc = Rc::new(predicate_cont);
            let if_true_conts = if predicate != Predicate::False {
                let mut true_continuation = Continuation::from_parent(predicate_rc.clone(), format!("{}.true", &parent_func), if_true_symexp.span.start_line);
                true_continuation.predicate = true_continuation.predicate.clone().and(predicate.clone());

                let if_true_conts = self.eval(config, true_continuation, &if_true_symexp)?;
                if_true_conts
            }
            else {
                vec![]
            };

            let if_false_conts = if predicate != Predicate::True {
                let mut false_continuation = Continuation::from_parent(predicate_rc.clone(), format!("{}.false", parent_func), if_false_symexp.span.start_line);
                false_continuation.predicate = false_continuation.predicate.clone().and(predicate.clone().not());

                let if_false_conts = self.eval(config, false_continuation, &if_false_symexp)?;
                if_false_conts
            }
            else {
                vec![]
            };

            branch_conts.extend(if_true_conts.into_iter());
            branch_conts.extend(if_false_conts.into_iter());
        }
        Ok(branch_conts)
    }

    fn let_bind(&mut self, config: &SymbexConfig, continuation: Continuation, let_bindings: &[SymbolicExpression]) -> Result<Vec<Continuation>, Error> {
        if let_bindings.len() < 2 {
            return Err(Error::Bug(format!("Let-binding has wrong length {}", let_bindings.len())));
        };

        let Some(body_exprs) = let_bindings.get(1..) else {
            return Err(Error::Bug("Empty let-binding".into()));
        };

        let Some(bindings_symexp) = let_bindings.get(0) else {
            return Err(Error::Bug(format!("Let-binding with no bindings: {let_bindings:?}")));
        };

        let Some(bindings) = bindings_symexp.match_list() else {
            return Err(Error::Bug(format!("Let-binding bindings is not a list: {bindings_symexp:?}")));
        };

        let mut bind_names_and_bodies = vec![];
        for binding in bindings.iter() {
            // each binding must be a (list 2 _), and the first item is the bound name
            let SymbolicExpressionType::List(lv) = &binding.expr else {
                return Err(Error::Bug(format!("Let-binding is not a list: {binding:?}")));
            };

            let Some(binding_name_symexp) = lv.get(0) else {
                return Err(Error::Bug(format!("Let-binding does not have a name: {binding:?}")));
            };

            let Some(binding_body_symexp) = lv.get(1) else {
                return Err(Error::Bug(format!("Let-binding does not have a body: {binding:?}")));
            };

            let Some(binding_name) = binding_name_symexp.match_atom() else {
                return Err(Error::Bug(format!("Let-binding name is not an atom: {binding_name_symexp:?}")));
            };

            bind_names_and_bodies.push((binding_name, binding_body_symexp));
        }

        let parent_func = continuation.function_path.clone().unwrap_or("".to_string());
        let function_name = format!("{parent_func}/let");

        let mut conts = vec![(continuation, vec![])];
        for (i, (bind_name, body_symexp)) in bind_names_and_bodies.iter().enumerate() {
            let mut new_conts = vec![];
            for (cont, bound_syms) in conts.into_iter() {
                if cont.halted() {
                    new_conts.push((cont, bound_syms));
                    continue;
                }
                if cont.predicate.clone().simplify()? == Predicate::False {
                    new_conts.push((cont, bound_syms));
                    continue;
                }

                let bind_conts = self.eval(config, Continuation::from_parent(Rc::new(cont), format!("{function_name}.bind[{i}].{bind_name}"), (*body_symexp).span.start_line), body_symexp)?;
                for mut bind_cont in bind_conts.into_iter() {
                    if bind_cont.halted() {
                        new_conts.push((bind_cont, bound_syms.clone()));
                        continue;
                    }
                    if bind_cont.predicate.clone().simplify()? == Predicate::False {
                        new_conts.push((bind_cont, bound_syms.clone()));
                        continue;
                    }

                    // the computed binding can be used by a subsequent binding formula
                    bind_cont.bind_symop(bind_name, bind_cont.final_formula.clone().simplify()?);
                    let mut new_bound_syms = bound_syms.clone();
                    new_bound_syms.push(bind_name);
                    new_conts.push((bind_cont, new_bound_syms));
                }
            }
            conts = new_conts;
        }

        let mut bound_conts = vec![];
        for (bind_cont, bound_syms) in conts.into_iter() {
            if bind_cont.halted() {
                bound_conts.push(bind_cont);
                continue;
            }

            let mut body_conts = vec![vec![bind_cont]];
            for (i, body) in body_exprs.iter().enumerate() {
                let mut next_body_conts = vec![];
                for body_cont_set in body_conts.into_iter() {
                    for body_cont in body_cont_set.into_iter() {
                        if body_cont.halted() {
                            bound_conts.push(body_cont);
                            continue;
                        }
                        if body_cont.predicate.clone().simplify()? == Predicate::False {
                            bound_conts.push(body_cont);
                            continue;
                        }
                        let next_body_cont = Continuation::from_parent(Rc::new(body_cont), format!("{function_name}.expr[{i}]"), body.span.start_line);
                        let conts = self.eval(config, next_body_cont, body)?;
                        next_body_conts.push(self.reduce_continuations(&config, conts));
                    }
                }
                body_conts = next_body_conts;
            }

            for body_set in body_conts.into_iter() {
                bound_conts.extend(body_set.into_iter());
            }
            for bound_cont in bound_conts.iter_mut() {
                for bound_sym in bound_syms.iter() {
                    bound_cont.unbind(bound_sym);
                }
            }
        }
        Ok(self.reduce_continuations(&config, bound_conts))
    }
    
    /// Apply all (@clairvoyance ..) directives for a symbolic expression on this symbolic
    /// executor instance which apply prior any evaluation
    pub fn from_contract_comments(code: &str, mut search_paths: Vec<String>) -> Result<Symbex, Error> {
        // first, parse and analyze this contract in a throw-away datastore
        let default_contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "clairvoyance".try_into().unwrap());
        let ast = ast::parse_ast(&default_contract_id, &code)?;

        // walk through top-level comments
        let mut command_context = CommandContext::new();

        let mut trait_concretizations = vec![];
        let mut default_traits = vec![];
        let mut deps = vec![];
        let mut contract_id = None;
        let mut contract_sponsor = None;
        
        let function_symexps = SymContract::extract_function_symexps(&ast.expressions);
        search_paths.push("".to_string());

        // commands in all top-level expressions
        for toplevel_body in ast.expressions.iter() {
            let commands = command_context.eval(toplevel_body)?;
            if commands.len() > 0 {
                debug!("Commands on top-level {toplevel_body}:");
                for cmd in commands.iter() {
                    debug!("\n{cmd}");
                }
                debug!("End of commands");
            }
            else {
                continue;
            }

            for command in commands.into_iter() {
                match command {
                    Command::Dependency(contract_id, path, sponsor_opt) => {
                        let mut found = false;
                        for search_path in search_paths.iter() {
                            let path = if let Some('/') = path.chars().next() {
                                path.clone()
                            }
                            else {
                                format!("{search_path}/{path}")
                            };

                            if let Err(_e) = fs::metadata(&path) {
                                continue;
                            }
                            let Ok(data) = fs::read(&path) else {
                                continue;
                            };

                            let Ok(code) = str::from_utf8(&data) else {
                                continue;
                            };

                            found = true;
                            deps.push((contract_id.clone(), code.to_string(), sponsor_opt));
                            break;
                        }
                        if !found {
                            return Err(Error::new_program_error(format!("Unable to read `{path}`. Search path was `{}`", search_paths.to_vec().join(":"))));
                        }
                    }
                    Command::DefaultTraitImpl(trait_id, contract_id) => {
                        default_traits.push((trait_id, contract_id));
                    }
                    Command::ContractSponsor(sponsor) => {
                        if contract_sponsor.is_some() {
                            return Err(Error::new_program_error(format!("`(contract-sponsor ..)` directive used more than once")));
                        }
                        contract_sponsor = Some(sponsor)
                    }
                    Command::ContractId(deployed_id) => {
                        if contract_id.is_some() {
                            return Err(Error::new_program_error(format!("`(contract-id ..)` directive used more than once")));
                        }
                        contract_id = Some(deployed_id);
                    }
                    _ => {
                        continue;
                    }
                }
            }
        }

        let contract_id = contract_id.unwrap_or(default_contract_id);

        // commands in function-level comments
        // (i.e. trait concretizations)
        for (name, body) in function_symexps.iter() {
            let commands = command_context.eval(body)?;
            if commands.len() > 0 {
                debug!("Commands on function {body}:");
                for cmd in commands.iter() {
                    debug!("\n{cmd}");
                }
                debug!("End of commands");
            }
            else {
                continue;
            }

            for command in commands.into_iter() {
                match command {
                    Command::ConcretizeTrait(trait_var_name, impl_contract_id) => {
                        let fq_func_name = FullName(contract_id.clone(), name.clone());
                        trait_concretizations.push((fq_func_name, trait_var_name.clone(), impl_contract_id.clone()));
                    },
                    _ => {
                        continue;
                    }
                }
            }
        }

        let this_idx = deps.len();
        deps.push((contract_id, code.to_string(), contract_sponsor.clone()));
        let mut symbex = Symbex::from_contracts(deps, this_idx)?
            .with_tx_sponsor(contract_sponsor);

        for (fq_name, arg_name, contract_id) in trait_concretizations.into_iter() {
            symbex = symbex.concretize_trait(fq_name, arg_name, contract_id);
        }
        for (trait_id, contract_id) in default_traits.into_iter() {
            symbex = symbex.default_trait(trait_id, contract_id);
        }

        Ok(symbex)
    }

    pub fn from_contract(contract_id: QualifiedContractIdentifier, code: &str) -> Result<Self, Error> {
        Self::from_contract_ex(contract_id, code, None)
    }

    pub fn from_contract_sponsored(contract_id: QualifiedContractIdentifier, code: &str, contract_sponsor: StandardPrincipalData) -> Result<Self, Error> {
        Self::from_contract_ex(contract_id, code, Some(contract_sponsor))
    }
    
    pub fn from_contract_ex(contract_id: QualifiedContractIdentifier, code: &str, contract_sponsor: Option<StandardPrincipalData>) -> Result<Self, Error> {
        Self::from_contracts(vec![(contract_id, code.to_string(), contract_sponsor)], 0)
    }

    pub fn from_contracts(contracts: Vec<(QualifiedContractIdentifier, String, Option<StandardPrincipalData>)>, target_contract_idx: usize) -> Result<Self, Error> {
        let mut datastore = BackingStore::new();
        let mut contract_state = HashMap::new();
        let target_contract = contracts.get(target_contract_idx).map(|(contract_id, _, _)| contract_id.clone()).ok_or_else(|| Error::NotFound("bad target contract index".into()))?;

        for (contract_id, code, contract_sponsor) in contracts.into_iter() {
            debug!("Instantiate contract {}", &contract_id);
            let ast = ast::parse_ast(&contract_id, &code)?;
            let mut analysis = ast::make_contract_analysis_from_ast(&mut datastore, &contract_id, &ast)?;
            let contract_context = ast::make_contract_context_from_ast(
                &mut datastore,
                &contract_id,
                &code,
                &ast,
                contract_sponsor.clone().map(|s| PrincipalData::Standard(s))
            )?;
         
            let Some(typemap) = analysis.type_map.take() else {
                return Err(Error::Bug("No typemap computed".into()));
            };
            let sym_contract = SymContract::new(contract_id.clone(), typemap, ast.expressions, contract_context);
            contract_state.insert(contract_id, sym_contract);
        }

        let symbex = Symbex {
            datastore,
            callgraph: None,
            contracts: contract_state,
            target_contract,
            tx_sender: None,
            contract_caller: None,
            tx_sponsor: None,
            trait_concretizations: HashMap::new(),
            default_trait_concretizations: HashMap::new(),
            explore_function_calls: true,
            skip_function_calls: HashSet::new(),
            skip_contract_calls: HashSet::new(),
            skip_pure_calls: true,
            skip_causally_independent_calls: true,
            drop_early_returns: HashSet::new(),
            evaluated_functions: HashMap::new(),
            combine_continuations: true,
            check_proofs: true,
        };
        Ok(symbex)
    }

    pub fn with_tx_sender(mut self, tx_sender: Option<StandardPrincipalData>) -> Self {
        self.tx_sender = tx_sender.map(|tx_sender| SymOp::Constant(Value::Principal(PrincipalData::Standard(tx_sender))));
        trace!("tx-sender is {:?}", &self.tx_sender);
        self
    }

    pub fn with_tx_sponsor(mut self, tx_sponsor: Option<StandardPrincipalData>) -> Self {
        self.tx_sponsor = tx_sponsor.map(|tx_sponsor| SymOp::Constant(Value::some(Value::Principal(PrincipalData::Standard(tx_sponsor))).expect("infallible")));
        trace!("tx-sponsor? is {:?}", &self.tx_sponsor);
        self
    }

    pub fn with_contract_caller(mut self, contract_caller: Option<PrincipalData>) -> Self {
        self.contract_caller = contract_caller.map(|contract_caller| SymOp::Constant(Value::Principal(contract_caller)));
        trace!("contract-caller is {:?}", &self.contract_caller);
        self
    }

    pub fn with_function_call_exploration(mut self, explore: bool) -> Self {
        self.explore_function_calls = explore;
        trace!("explore_function_calls = {}", self.explore_function_calls);
        self
    }

    pub fn with_skipped_function_call(mut self, func_name: FullName) -> Self {
        trace!("skip_function_call {func_name}");
        self.skip_function_calls.insert(func_name);
        self
    }
    
    pub fn with_skipped_contract_call(mut self, func_name: FullName) -> Self {
        trace!("skip_contract_call {func_name}");
        self.skip_contract_calls.insert(func_name);
        self
    }

    pub fn skip_pure(mut self, val: bool) -> Self {
        self.skip_pure_calls = val;
        trace!("skip_pure_calls = {}", self.skip_pure_calls);
        self
    }

    pub fn skip_causally_independent(mut self, val: bool) -> Self {
        self.skip_causally_independent_calls = val;
        trace!("skip_causally_independent_calls = {}", self.skip_causally_independent_calls);
        self
    }

    pub fn drop_early_return(mut self, function_name: FullName) -> Self {
        debug!("Drop early-returns from {}", &function_name);
        self.drop_early_returns.insert(function_name);
        self
    }
   
    pub fn combine_continuations(mut self, combine: bool) -> Self {
        self.combine_continuations = combine;
        self
    }

    pub fn concretize_trait(mut self, function_name: FullName, var_name: ClarityName, concrete_contract_id: QualifiedContractIdentifier) -> Self {
        if let Some(concretizations) = self.trait_concretizations.get_mut(&function_name) {
            concretizations.insert(var_name, concrete_contract_id);
        }
        else {
            let mut concretizations = HashMap::new();
            concretizations.insert(var_name, concrete_contract_id);
            self.trait_concretizations.insert(function_name, concretizations);
        }
        self
    }

    pub fn default_trait(mut self, trait_id: TraitIdentifier, concrete_contract_id: QualifiedContractIdentifier) -> Self {
        self.default_trait_concretizations.insert(trait_id, concrete_contract_id);
        self
    }

    pub fn check_proofs(mut self, check: bool) -> Self {
        self.check_proofs = check;
        self
    }

    pub fn init(mut self) -> Result<Self, Error> {
        self.do_init()?;
        Ok(self)
    }

    fn do_init(&mut self) -> Result<(), Error> {
        if self.callgraph.is_none() {
            let callgraph = Callgraph::from_contracts(&self.contracts, &self.target_contract, self.trait_concretizations.clone(), self.default_trait_concretizations.clone())?;
            self.callgraph = Some(callgraph);
        }
        Ok(())
    }
   
    pub fn eval_all(&mut self) -> Result<Vec<Continuation>, Error> {
        self.do_init()?;
        let config = SymbexConfig::new(self);

        let current_contract = PrincipalData::Contract(self.contract_context(&self.target_contract)?.contract_identifier.clone());

        let mut root_continuation = Continuation::root(self, current_contract);
        
        for (const_name, const_value) in self.contract_context(&self.target_contract)?.variables.iter() {
            root_continuation.bind_constant(const_name, const_value);
        }

        for (var_name, var_metadata) in self.contract_context(&self.target_contract)?.meta_data_var.iter() {
            root_continuation.set_pre_data_var(var_name, SymOp::Variable(Sym::from_name_and_type_signature(var_name, &var_metadata.value_type)));
        }

        let contract_funcs = self.callgraph().get_contract_functions(&self.contract_context(&self.target_contract)?.contract_identifier);
        for contract_func in contract_funcs.into_iter() {
            if self.evaluated_functions.contains_key(&contract_func) {
                continue;
            }

            debug!("Evaluating function '{contract_func}'");
            let conts : Vec<_> = self.eval_user_function(contract_func.name().as_str())?
                .into_iter()
                .map(|cont| cont.rollup())
                .collect();

            for cont in conts.iter() {
                debug!("Computed continuation for function '{contract_func}'\n{cont}");
                debug!("Trace:\n{}", cont.clone().trace());
            }
            self.evaluated_functions.insert(contract_func, conts);
        }

        debug!("Evaluating top-level symbols");

        let mut conts = vec![root_continuation];
        let syms = self.symbols(&self.target_contract)?.to_vec();
        for sym in syms.iter() {
            let mut next = vec![];
            for cont in conts.into_iter() {
                let cont_rc = Rc::new(cont);
                let next_conts = self.eval(&config, Continuation::from_parent(cont_rc.clone(), "".to_string(), sym.span.start_line), sym)?;
                assert!(next_conts.len() > 0, "No continuation produced from {cont_rc:?}");
                next.extend(next_conts.into_iter());
            }
            conts = next;
        }

        Ok(self.reduce_continuations(&config, conts))
    }
  
    /// Symbolically evaluate a user function.
    /// Each argument will be bound to a SymOp::Variable of the appropriate type.
    /// `function_name` may be a FullName
    pub fn eval_user_function(&mut self, function_name: &str) -> Result<Vec<Continuation>, Error> {
        self.do_init()?;
        let config = SymbexConfig::new(self);

        let fq_name = if let Ok(fq_name) = FullName::try_from(function_name) {
            fq_name
        }
        else {
            if self.contract_context(&self.target_contract)?.functions.get(function_name).is_none() {
                return Err(Error::NotFound(format!("No such function '{function_name}' in target contract {}", &self.target_contract)));
            };

            let fq_name = FullName(
                self.contract_context(&self.target_contract)?.contract_identifier.clone(),
                ClarityName::try_from(function_name).map_err(|_| Error::Bug("Invalid function name".into()))?
            );
            fq_name
        };

        let reachable_funcs = self.callgraph().reachable_from(&fq_name)?;
        for reachable_func in reachable_funcs.into_iter() {
            if self.evaluated_functions.contains_key(&reachable_func) {
                continue;
            }
            
            debug!("Evaluating reachable function '{reachable_func}' in {}", &self.target_contract);
            let conts : Vec<_> = self.inner_eval_user_function(&config, &reachable_func)?
                .into_iter()
                .filter(|c| !c.panicking)
                .map(|c| c.rollup())
                .collect();

            for cont in conts.iter() {
                debug!("Computed continuation for function '{reachable_func}'\n{cont}");
                debug!("Trace:\n{}", cont.clone().trace());
            }

            self.evaluated_functions.insert(reachable_func, conts);
        }

        debug!("Evaluating function '{fq_name}'");
        self.inner_eval_user_function(&config, &fq_name)
    }

    fn inner_eval_user_function(&mut self, config: &SymbexConfig, fq_function_name: &FullName) -> Result<Vec<Continuation>, Error> {
        let contract_id = fq_function_name.contract_id();
        let function_name = fq_function_name.name().as_str();

        let Some(func) = self.contract_context(contract_id)?.functions.get(function_name).cloned() else {
            return Err(Error::NotFound(format!("No such function '{function_name}'")));
        };
        if func.arguments.len() != func.arg_types.len() {
            return Err(Error::Bug("Function argument names length != function argument types length".into()));
        }
        let fq_name = FullName(self.contract_context(&contract_id)?.contract_identifier.clone(), ClarityName::try_from(function_name).map_err(|_| Error::Bug("Invalid function name".into()))?);
        let func_def = self.get_function_symexp(&fq_name).ok_or_else(|| Error::Bug(format!("No such function {fq_name}")))?.clone();

        // set up root context
        let current_contract = PrincipalData::Contract(contract_id.clone());
        let mut root_continuation = Continuation::root(self, current_contract);
        
        for (const_name, const_value) in self.contract_context(contract_id)?.variables.iter() {
            root_continuation.bind_constant(const_name, const_value);
        }

        for (var_name, var_metadata) in self.contract_context(contract_id)?.meta_data_var.iter() {
            root_continuation.set_pre_data_var(var_name, SymOp::Variable(Sym::from_name_and_type_signature(var_name, &var_metadata.value_type)));
        }

        // create symbolic function bindings
        let mut binding_cont = Continuation::from_parent(Rc::new(root_continuation), format!("{}.binding", &function_name), func.body.span.start_line);

        binding_cont.add_reachable_storage_accesses(&fq_name, &self.callgraph())?;
        let mut bound = vec![];
        for (arg_name, arg_type) in func.arguments.iter().zip(func.arg_types.iter()) {
            let sym = Sym::from_name_and_type_signature(arg_name, arg_type);
            binding_cont.bind_symop(arg_name, SymOp::Variable(sym));
            bound.push(arg_name.clone());
        }

        // run that function!
        let callee_cont = Continuation::from_caller(Rc::new(binding_cont), format!("{}.body", &function_name), function_name.to_string(), func.body.span.start_line);
        let original_cont = callee_cont.clone();

        // HACK: the function definition (not body) contains the pre-evaluation commands, so
        // synthesize the SymbexConfig from it and pass it into Self::eval() for this function.
        let func_config = self.run_pre_commands(config, &callee_cont, &func_def)?;
        let conts = self.eval(&func_config, callee_cont, &func.body)?;

        let mut conts : Vec<_> = conts
            .into_iter()
            .filter(|cont| {
                if self.drop_early_returns.contains(&fq_name) && cont.early_return {
                    debug!("Will not evaluate early-return continuation {} of {fq_name}", cont.id);
                    false
                }
                else {
                    true
                }
            })
            .map(|cont| {
                if cont.panicking {
                    return cont;
                }
                let mut return_cont = Continuation::from_callee(Rc::new(cont), format!("{}.return", function_name), func.body.span.start_line);
                for unbind in bound.iter() {
                    return_cont.unbind(unbind);
                }
                return_cont
            })
            .collect();

        // each early-return continuation loses its mutable state
        for cont in conts.iter_mut() {
            if cont.early_return {
                debug!("Final continuation {} ({}) is an early-return continuation, and has no side-effects", cont.get_function_path(), cont.id);
                cont.clear_side_effects();
            }
            if cont.panicking {
                debug!("Final continuation {} ({}) is a panicking continuation, and has no side-effects", cont.get_function_path(), cont.id);
                cont.clear_side_effects();
            }
        }

        let mut conts = self.reduce_continuations(&config, conts);
        self.run_post_commands(&config, &func_def, original_cont, &mut conts)?;
        Ok(conts)
    }
}

