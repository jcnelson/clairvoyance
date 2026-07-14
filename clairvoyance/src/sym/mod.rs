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

use std::fmt;
use std::rc::Rc;
use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::collections::BTreeMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::collections::BTreeSet;
use std::borrow::Borrow;
use std::hash::{Hash, Hasher};

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
use clarity::vm::analysis::type_checker::contexts::TypeMap;

use clarity_types::types::SequencedValue;
use clarity_types::types::signatures::{SequenceSubtype, TupleTypeSignature, CallableSubtype, StringSubtype};
use clarity_types::types::TraitIdentifier;
use clarity_types::types::TupleData;
use clarity_types::types::ListTypeData;
use clarity::vm::types::{
    ASCIIData, BuffData, CharType, SequenceData, UTF8Data,
};
use clarity_types::types::ListData;

use stacks_common::consts::CHAIN_ID_MAINNET;
use crate::core::BackingStore;
use crate::core::Error;
use crate::core::ast;
use crate::core::{DEFAULT_STACKS_EPOCH, DEFAULT_CLARITY_VERSION};

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

/// computations over symbols.
/// not all relations are well-defined here; we rely on the Clarity type-checker for this.
#[derive(Debug, Clone, Eq)]
pub enum SymOp {
    Constant(Value),
    Variable(Sym),
    LoadedDataVariable(ClarityName, Box<SymOp>),
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
    Concat(Box<SymOp>, Box<SymOp>),
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
    FetchVar(ClarityName),
    SetVar(ClarityName, Box<SymOp>),
    FetchEntry(ClarityName, Box<SymOp>),
    LoadedMapEntry(ClarityName, Box<SymOp>, Option<Box<SymOp>>),
    SetEntry(ClarityName, Box<SymOp>, Box<SymOp>),
    InsertEntry(ClarityName, Box<SymOp>, Box<SymOp>),
    DeleteEntry(ClarityName, Box<SymOp>),
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
    GetTokenBalance(ClarityName, Box<SymOp>),
    GetNftOwner(ClarityName, Box<SymOp>),
    TransferToken(ClarityName, Box<SymOp>, Box<SymOp>, Box<SymOp>),
    TransferNft(ClarityName, Box<SymOp>, Box<SymOp>, Box<SymOp>),
    MintToken(ClarityName, Box<SymOp>, Box<SymOp>),
    MintNft(ClarityName, Box<SymOp>, Box<SymOp>),
    GetTokenSupply(ClarityName),
    BurnToken(ClarityName, Box<SymOp>),
    BurnNft(ClarityName, Box<SymOp>, Box<SymOp>),
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
    // INTERNAL -- symbolic execution detected an unconditional panic
    Panic,
    // INTERNAL -- a "stub" function call that will not be explored.
    FunctionCall(ClarityName, Vec<Box<SymOp>>)
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
            (Self::Concat(s11, s12), Self::Concat(s21, s22)) => s11 == s21 && s12 == s22,
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
            (Self::Panic, Self::Panic) => true,
            (Self::FunctionCall(n1, args1), Self::FunctionCall(n2, args2)) => n1 == n2 && args1 == args2,
            (_, _) => false
        }
    }
}

impl SymOp {
    fn inner_format_prefix(func: &str, list: &[Box<SymOp>], sort: bool, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let mut symop_strs : Vec<_> = list
            .iter()
            .map(|symop| format!("{}", symop))
            .collect();

        if sort {
            symop_strs.sort();
        }
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
                match &**symop {
                    Self::Constant(c) => write!(f, "(loaded-var-const {} {})", name, c),
                    | Self::Variable(v) => write!(f, "(loaded-var {} {})", name, v.type_str()),
                    x => write!(f, "(loaded-var-sym {} {})", name, x)
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
            Self::Concat(op1, op2) => write!(f, "(concat {op1} {op2})"),
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
                if let Some(value_op) = value_op_opt.as_ref() {
                    match &**value_op {
                        Self::Constant(c) => write!(f, "(map-entry-const {} {} {})", name, key_op, c),
                        | Self::Variable(v) => write!(f, "(map-entry {} {} {} {})", name, key_op, Self::Variable(v.clone()), v.type_str()),
                        x => write!(f, "(map-entry-sym {} {} {})", name, key_op, x),
                    }
                }
                else {
                    write!(f, "(map-entry {} {})", name, key_op)
                }
            }
            Self::SetEntry(name, op1, op2) => write!(f, "(map-set {name} {op1} {op2})"),
            Self::InsertEntry(name, op1, op2) => write!(f, "(map-insert {name} {op1} {op2})"),
            Self::DeleteEntry(name, op1) => write!(f, "(map-delete {name} {op1})"),
            Self::TupleCons(fields) => {
                let frags : Vec<_> = fields.iter().map(|(name, op)| format!("{name}: {op}")).collect();
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
            Self::Secp256k1Recover(op1, op2) => write!(f, "(secp256-recover? {op1} {op2})"),
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
                let non_ident = non_identities.pop().expect("unreachable");
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
    /// (u8), and its count (u128).
    fn make_term_count_table(terms: Vec<Box<SymOp>>) -> Result<HashMap<String, (Box<SymOp>, i8, u128)>, Error> {
        let mut table = HashMap::new();
        for term in terms.into_iter() {
            // skip trivial zero's
            if SymOp::Constant(Value::UInt(0)) == *term {
                continue;
            }
            if SymOp::Constant(Value::Int(0)) == *term {
                continue;
            }

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
                    let inner_term = terms.pop().ok_or_else(|| Error::Bug("unreachable".into()))?;
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
        for (term, diff) in diff.into_iter() {
            let del = if let Some((_, add_count)) = term_table.get_mut(&term) {
                if diff == *add_count {
                    true
                }
                else {
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
    }

    /// Combine terms in the form of (a + b + c + ...) - (x + y + z + ...)
    /// `adds` are terms that are to be added together (i.e. a, b, c. ..)
    /// `subs` are terms that are to be summed, and then subtracted from `adds` (i.e. x, y, z, ...)
    fn combine_terms(adds: Vec<Box<SymOp>>, subs: Vec<Box<SymOp>>) -> Result<SymOp, Error> {
        let add_signed_table = Self::make_term_count_table(adds)?;
        let sub_signed_table = Self::make_term_count_table(subs)?;

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

        let mut add_diff = HashMap::new();
        let mut sub_diff = HashMap::new();
        for (add_term, (_, add_count)) in add_table.iter() {
            if let Some((_, sub_count)) = sub_table.get(add_term) {
                if add_count > sub_count {
                    sub_diff.insert(add_term.clone(), *add_count - *sub_count);
                }
                else if add_count == sub_count {
                    add_diff.insert(add_term.clone(), *add_count);
                    sub_diff.insert(add_term.clone(), *sub_count);
                }
                else {
                    add_diff.insert(add_term.clone(), *sub_count - *add_count);
                }
            }
        }

        Self::remove_terms(&mut add_table, add_diff);
        Self::remove_terms(&mut sub_table, sub_diff);

        let mut adds = vec![];
        let mut subs = vec![];

        if add_table.len() == 0 {
            // all subtractions
            for (_, (op, count)) in sub_table.into_iter() {
                let count = u128::try_from(count).map_err(|_| Error::Bug("Could not cast usize to u128".into()))?;
                if subs.len() == 0 {
                    // first item is negative, so negate
                    if count > 1 {
                        let inner_mult = SymOp::Multiply(vec![
                            Box::new(SymOp::Constant(Value::UInt(count))),
                            op.clone()
                        ]);
                        subs.push(Box::new(SymOp::Subtract(vec![Box::new(inner_mult)])));
                    }
                    else {
                        subs.push(Box::new(SymOp::Subtract(vec![op.clone()])))
                    }
                }
                else {
                    if count > 1 {
                        let count = u128::try_from(count).map_err(|_| Error::Bug("Could not cast usize to u128".into()))?;
                        subs.push(Box::new(SymOp::Multiply(vec![Box::new(SymOp::Constant(Value::UInt(count))), op.clone()])));
                    }
                    else {
                        subs.push(op.clone());
                    }
                }
            }
        }
        else {
            for (_, (op, count)) in add_table.into_iter() {
                let count = u128::try_from(count).map_err(|_| Error::Bug("Could not cast usize to u128".into()))?;
                if count > 1 {
                    adds.push(Box::new(SymOp::Multiply(vec![Box::new(SymOp::Constant(Value::UInt(count))), op.clone()])));
                }
                else {
                    adds.push(op.clone());
                }
            }
            for (_, (op, count)) in sub_table.into_iter() {
                let count = u128::try_from(count).map_err(|_| Error::Bug("Could not cast usize to u128".into()))?;
                if count > 1 {
                    let count = u128::try_from(count).map_err(|_| Error::Bug("Could not cast usize to u128".into()))?;
                    subs.push(Box::new(SymOp::Multiply(vec![Box::new(SymOp::Constant(Value::UInt(count))), op.clone()])));
                }
                else {
                    subs.push(op.clone());
                }
            }
        }

        debug!("combine_terms: adds = {:?}", &adds);
        debug!("combine_terms: subs = {:?}", &subs);

        if subs.len() == 0 {
            if adds.len() > 1 {
                Ok(SymOp::Add(adds))
            }
            else {
                Ok(*adds.pop().ok_or_else(|| Error::Bug("unreachable".into()))?)
            }
        }
        else {
            if adds.len() == 1 {
                let Some(add) = adds.pop() else {
                    return Err(Error::Bug("unreachable".into()));
                };
                if subs.len() == 1 {
                    let Some(sub) = subs.pop() else {
                        return Err(Error::Bug("unreachable".into()));
                    };
                    Ok(SymOp::Subtract(vec![add, sub]))
                }
                else {
                    Ok(SymOp::Subtract(vec![add, Box::new(SymOp::Add(subs))]))
                }
            }
            else {
                if subs.len() == 1 {
                    let Some(sub) = subs.pop() else {
                        return Err(Error::Bug("unreachable".into()));
                    };
                    Ok(SymOp::Subtract(vec![Box::new(SymOp::Add(adds)), sub]))
                }
                else {
                    Ok(SymOp::Subtract(vec![Box::new(SymOp::Add(adds)), Box::new(SymOp::Add(subs))]))
                }
            }
        }
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
        //
        let mut adds = vec![];
        let mut subs = vec![];
        
        debug!("flatten_subs original ops: {:?}", &ops);
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
                        adds.push(first);
                        if rest.len() > 0 {
                            subs.extend(rest.to_vec().into_iter());
                        }
                    }
                    else {
                        subs.push(first);
                        if rest.len() > 0 {
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
        debug!("flatten_subs adds = {:?}", &adds);
        debug!("flatten_subs subs = {:?}", &subs);
       
        let combined = Self::combine_terms(adds, subs)?;
        debug!("combine_subs: combined = {:?}", &combined);

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
        debug!("flatten_adds original ops: {:?}", &ops);
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
                        adds.push(Box::new(Self::Subtract(inner)));
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

        debug!("flatten_adds adds = {:?}", &adds);
        debug!("flatten_adds subs = {:?}", &subs);

        let combined = Self::combine_terms(adds, subs)?;
        debug!("combine_subs: combined = {:?}", &combined);

        Ok(combined)
    }

    /// fold constants in subtraction and combine terms
    fn simplify_subtraction(ops: Vec<Box<SymOp>>) -> Result<SymOp, Error> {
        let sub = Self::Subtract(ops.clone());  // for debugging
        let flattened_op = Self::flatten_subtractions(ops)?;

        debug!("{} becomes {}", &sub, &flattened_op);
        let Self::Subtract(mut ops) = flattened_op else {
            return Ok(flattened_op);
        };

        if ops.len() == 1 {
            let Some(op) = ops.pop() else { unreachable!() };
            return Ok(*op)
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
        
        debug!("flatten_multiply: adds = {}", &adds.iter().map(|o| o.to_string()).collect::<Vec<_>>().join(", "));
        debug!("flatten_multiply: subs = {}", &subs.iter().map(|o| o.to_string()).collect::<Vec<_>>().join(", "));

        let mut accum_opt : Option<Box<SymOp>> = None;
        for op in adds.into_iter().chain(subs.into_iter()) {
            if let Some(accum) = accum_opt.take() {
                debug!("flatten_multiply: accum = {}", &accum);

                let mut prod_adds = vec![];
                let mut prod_subs = vec![];
                let accum_signs = Self::get_op_signs(*accum);
                let op_signs = Self::get_op_signs(*op);

                for (accum_sign, accum_op) in accum_signs.into_iter() {
                    for (op_sign, op) in op_signs.clone().into_iter() {
                        let sign = accum_sign * op_sign;
                        let p = Self::Multiply(vec![accum_op.clone(), op]);

                        debug!("flatten_multiply: prod = {}", &p);

                        if sign > 0 {
                            prod_adds.push(Box::new(p));
                        }
                        else {
                            prod_subs.push(Box::new(p));
                        }
                    }
                }
        
                debug!("flatten_multiply: prod_adds = {}", &prod_adds.iter().map(|o| o.to_string()).collect::<Vec<_>>().join(", "));
                debug!("flatten_multiply: prod_subs = {}", &prod_subs.iter().map(|o| o.to_string()).collect::<Vec<_>>().join(", "));

                let prod = if prod_subs.len() > 0 && prod_adds.len() > 0 {
                    Self::Subtract(vec![Box::new(SymOp::Add(prod_adds)), Box::new(SymOp::Add(prod_subs))])
                }
                else if prod_subs.len() > 0 && prod_adds.len() == 0 {
                    // negate the first term, and subtract the rest
                    let first = prod_subs.pop().ok_or_else(|| Error::Bug("Unreachable".into()))?;
                    let rest = prod_subs.get(1..).ok_or_else(|| Error::Bug("Unreachable".into()))?;
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

                debug!("flatten_multiply: prod = {}", &prod);
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
            return Err(Error::Bug("unreachable".into()));
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
                if let Some(Self::Constant(Value::UInt(f))) = consts.pop().map(|c| *c) {
                    if f % c == 0 {
                        // factor it out
                        syms.push(Box::new(Self::Constant(Value::UInt(f / c))));
                        return Ok(Self::Multiply(syms));
                    }
                    else if f != 0 && c % f == 0 {
                        // factor it out
                        let syms = if syms.len() == 1 {
                            let Some(sym) = syms.pop() else { return Err(Error::Bug("unreachable: unsigned product / constant: syms has length 1".into())); };
                            sym
                        }
                        else {
                            Box::new(Self::Multiply(syms))
                        };
                        return Ok(Self::Divide(vec![syms, Box::new(Self::Constant(Value::UInt(c / f)))]));
                    }
                }
                // no factoring
                Ok(Self::Divide(vec![Box::new(Self::Multiply(numer_ops_no_factoring)), Box::new(Self::Constant(Value::UInt(c)))]))
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
                if let Some(Self::Constant(Value::Int(f))) = consts.pop().map(|c| *c) {
                    if f % c == 0 {
                        // factor it out
                        syms.push(Box::new(Self::Constant(Value::Int(f / c))));
                        return Ok(Self::Multiply(syms));
                    }
                    else if f != 0 && c % f == 0 {
                        // factor it out
                        let syms = if syms.len() == 1 {
                            let Some(sym) = syms.pop() else { return Err(Error::Bug("unreachable: signed product / constant: syms has length 1".into())); };
                            sym
                        }
                        else {
                            Box::new(Self::Multiply(syms))
                        };
                        return Ok(Self::Divide(vec![syms, Box::new(Self::Constant(Value::Int(c / f)))]));
                    }
                }
                // no factoring
                Ok(Self::Divide(vec![Box::new(Self::Multiply(numer_ops_no_factoring)), Box::new(Self::Constant(Value::Int(c)))]))
            },
            (Self::Constant(Value::UInt(f)), Self::Multiply(denom_ops)) => {
                let denom_ops_no_factoring = denom_ops.clone();
                let (mut consts, mut syms) : (Vec<Box<SymOp>>, Vec<Box<SymOp>>) = denom_ops.into_iter().partition(|n| if let Self::Constant(..) = &**n { true } else { false });
                if consts.len() > 1 {
                    return Err(Error::Bug(format!("Got multiple constants from simplified Multiply(..): {consts:?}")));
                }
                if let Some(Self::Constant(Value::UInt(c))) = consts.pop().map(|c| *c) {
                    if c == 0 {
                        return Err(Error::Arithmetic(format!("{f} / {c}")));
                    }
                    if f % c == 0 {
                        // factor it out
                        let syms = if syms.len() == 1 {
                            let Some(sym) = syms.pop() else { return Err(Error::Bug("unreachable: unsigned constant / product: syms has length 1".into())); };
                            sym
                        }
                        else {
                            Box::new(Self::Multiply(syms))
                        };
                        return Ok(Self::Divide(vec![Box::new(Self::Constant(Value::UInt(f / c))), syms]));
                    }
                    else if f != 0 && c % f == 0 {
                        // factor it out
                        syms.push(Box::new(Self::Constant(Value::UInt(c / f))));
                        return Ok(Self::Divide(vec![Box::new(Self::Constant(Value::UInt(1))), Box::new(Self::Multiply(syms))]));
                    }
                }
                Ok(Self::Divide(vec![Box::new(Self::Constant(Value::UInt(f))), Box::new(Self::Multiply(denom_ops_no_factoring))]))
            }
            (Self::Constant(Value::Int(f)), Self::Multiply(denom_ops)) => {
                let denom_ops_no_factoring = denom_ops.clone();
                let (mut consts, mut syms) : (Vec<Box<SymOp>>, Vec<Box<SymOp>>) = denom_ops.into_iter().partition(|n| if let Self::Constant(..) = &**n { true } else { false });
                if consts.len() > 1 {
                    return Err(Error::Bug(format!("Got multiple constants from simplified Multiply(..): {consts:?}")));
                }
                if let Some(Self::Constant(Value::Int(c))) = consts.pop().map(|c| *c) {
                    if c == 0 {
                        return Err(Error::Arithmetic(format!("{f} / {c}")));
                    }
                    if f % c == 0 {
                        // factor it out
                        let syms = if syms.len() == 1 {
                            let Some(sym) = syms.pop() else { return Err(Error::Bug("unreachable : signed constant / product: syms has length 1".into())); };
                            sym
                        }
                        else {
                            Box::new(Self::Multiply(syms))
                        };
                        return Ok(Self::Divide(vec![Box::new(Self::Constant(Value::Int(f / c))), syms]));
                    }
                    else if c % f == 0 {
                        // factor it out
                        syms.push(Box::new(Self::Constant(Value::Int(c / f))));
                        return Ok(Self::Divide(vec![Box::new(Self::Constant(Value::Int(1))), Box::new(Self::Multiply(syms))]));
                    }
                }
                Ok(Self::Divide(vec![Box::new(Self::Constant(Value::Int(f))), Box::new(Self::Multiply(denom_ops_no_factoring))]))
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

    /// When processing Self::And(..), combine all inner Self::Equals(..) and
    /// Self::Not(Self::Equals(..)) statements that share at
    /// least one non-constant term.  This will let us find a contradiction if we ever claim that the
    /// same term is equal to two or more different constants.
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
                let (op_idx, term_idx) = op_idx_list.pop().ok_or_else(|| Error::Bug("unreachable".into()))?;
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
                debug!("{} combined_eqs = {:?}", &_term_s, &combined_eqs);
            }
            else {
                // this term appears in more than one (is-eq ..), so put all of the other terms in
                // each of its (is-eq ..) list into the same combined (is-eq ..) list, along with
                // this one.
                debug!("{} appears in terms {:?}", &_term_s, &op_idx_list);
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

                    debug!("{} combined_eqs = {:?}", &_term_s, &combined_eqs);
                }
            }
        }

        debug!("combined_eqs = {:?}", &combined_eqs);
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
        debug!("flatten_equals: before:        {:?}", &before_s);
        debug!("flatten_equals: combined_eqs:  {:?}", &after_s);
        
        combined_terms.extend(combined_eqs.into_iter());
       
        debug!("flatten_equals: combined_terms:  {:?}", &combined_terms);
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

        debug!("and_eq_contradiction: not_terms = {:?}", &not_terms);

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
                                debug!("and_eq_contradiction: contradiction detected");
                                debug!("and_eq_contradiction: {i}: {}", combined_terms[i]);
                                for neg_op_idx in neg_set.clone().iter() {
                                    debug!("and_eq_contradiction: {neg_op_idx}: {}", combined_terms[*neg_op_idx]);
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

        debug!("and_eqs_redundant: combined_terms = {:?}", &combined_terms);

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
                    return Err(Error::Bug("unreachable".into()));
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
                        return Err(Error::Bug("unreachable".into()));
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
        debug!("and_eqs_redundant: expanded_eq = {:?}", &expanded_eq);
        debug!("and_eqs_redundant: expanded_neq = {:?}", &expanded_neq);

        debug!("and_eqs_redundant: term_eqs = {:?}", &term_eqs);
        debug!("and_eqs_redundant: term_neqs = {:?}", &term_neqs);

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
                debug!("and_eqs_redundant: redundant term {neq} in {}", &combined_terms[expanded_neq[*neq].2]);
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
                    if SymOp::value_greater(&val, &prev).expect("unreachable") {
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
                    if SymOp::value_geq(&val, &prev).expect("unreachable") {
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
                    if SymOp::value_lesser(&val, &prev).expect("unreachable") {
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
                    if SymOp::value_leq(&val, &prev).expect("unreachable") {
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
                            debug!("(and (x <= k) (not (is-eq x k))) implies x < k");
                            self.set_lesser(k.clone());
                            self.leq = None;
                            changed = true;
                        }
                        // (and (x >= k) (not (is-eq x k))) implies x > k
                        if let Some(k) = self.geq.as_ref() && k == neq {
                            debug!("(and (x >= k) (not (is-eq x k))) implies x > k");
                            self.set_greater(k.clone());
                            self.geq = None;
                            changed = true;
                        }
                        // (and (x < k) (not (is-eq x (- k 1)))) implies x < k - 1
                        if let Some(k1) = self.lesser.as_ref() && let Some(k2) = SymOp::value_minus_1(k1) {
                            debug!("(and (x < k) (not (is-eq x (- k 1)))) implies x < k - 1");
                            self.set_lesser(k2);
                            neq_remove.insert(neq.clone());
                            changed = true;
                        }
                        // (and (x > k) (not (is-eq x (+ k 1))) implies x > k + 1
                        if let Some(k1) = self.greater.as_ref() && let Some(k2) = SymOp::value_plus_1(k1) {
                            debug!("(and (x > k) (not (is-eq x (+ k 1))) implies x > k + 1");
                            self.set_greater(k2);
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
                if let Some(k1) = self.leq.as_ref() && let Some(k2) = self.eq.as_ref() && SymOp::value_geq(k1, k2).expect("unreachable") {
                    debug!("(and (<= x k1) (is-eq x k2) (<= k1 k2)) implies (is-eq x k2)");
                    self.leq = None;
                }
                // (and (>= x k1) (is-eq x k2) (<= k1 k2)) implies (is-eq x k2)
                if let Some(k1) = self.geq.as_ref() && let Some(k2) = self.eq.as_ref() && SymOp::value_leq(k1, k2).expect("unreachable") {
                    debug!("(and (<= x k1) (is-eq x k2) (>= k1 k2)) implies (is-eq x k2)");
                    self.geq = None;
                }
                // (and (< x k1) (is-eq x k2) (k1 > k2)) implies (is-eq x k2)
                if let Some(k1) = self.lesser.as_ref() && let Some(k2) = self.eq.as_ref() && SymOp::value_greater(k1, k2).expect("unreachable") {
                    debug!("(and (< x k1) (is-eq x k2) (k1 > k2)) implies (is-eq x k2)");
                    self.lesser = None;
                }
                // (and (> x k1) (is-eq x k2) (k1 < k2)) implies (is-eq x k2)
                if let Some(k1) = self.greater.as_ref() && let Some(k2) = self.eq.as_ref() && SymOp::value_lesser(k1, k2).expect("unreachable") {
                    debug!("(and (> x k1) (is-eq x k2) (k1 < k2)) implies (is-eq x k2)");
                    self.greater = None;
                }
            }

            fn ineq_rewrite(&mut self) {
                // (and (< x k1) (<= x k2) (k1 < k2)) implies (< x k1)
                if let Some(k1) = self.lesser.as_ref() && let Some(k2) = self.leq.as_ref() && SymOp::value_lesser(k1, k2).expect("unreachable") {
                    debug!("(and (< x k1) (<= x k2) (k1 < k2)) implies (< x k1)");
                    self.leq = None;
                }
                // (and (<= x k1) (< x k2) (k1 < k2)) implies (<= x k1)
                if let Some(k1) = self.leq.as_ref() && let Some(k2) = self.lesser.as_ref() && SymOp::value_lesser(k1, k2).expect("unreachable") {
                    debug!("(and (<= x k1) (< x k2) (k1 < k2)) implies (<= x k1)");
                    self.lesser = None;
                }
                // (and (> x k1) (>= x k2) (k1 > k2)) implies (> x k1)
                if let Some(k1) = self.greater.as_ref() && let Some(k2) = self.geq.as_ref() && SymOp::value_greater(k1, k2).expect("unreachable") {
                    debug!("(and (> x k1) (>= x k2) (k1 > k2)) implies (> x k1)");
                    self.geq = None;
                }
                // (and (>= x k1) (> x k2) (k1 > k2)) implies (>= x k1)
                if let Some(k1) = self.geq.as_ref() && let Some(k2) = self.greater.as_ref() && SymOp::value_greater(k1, k2).expect("unreachable") {
                    debug!("(and (>= x k1) (> x k2) (k1 > k2)) implies (>= x k1)");
                    self.greater = None;
                }
            }

            fn check_possible(&mut self) {
                // uint: (x < k) implies k > u0
                if let Some(k) = self.lesser.as_ref() && let Value::UInt(v) = k {
                    debug!("uint: (x < k) implies k > u0");
                    self.possible = self.possible && *v > u128::MIN;
                }
                // uint: (x > k) implies k < u128::MAX
                if let Some(k) = self.greater.as_ref() && let Value::UInt(v) = k {
                    debug!("uint: (x > k) implies k < u128::MAX");
                    self.possible = self.possible && *v < u128::MAX;
                }
                // int: (x < k) implies k > i128::MIN
                if let Some(k) = self.lesser.as_ref() && let Value::Int(v) = k {
                    debug!("int: (x < k) implies k > i128::MIN");
                    self.possible = self.possible && *v > i128::MIN;
                }
                // int: (x > k) implies k < i128::MAX
                if let Some(k) = self.greater.as_ref() && let Value::Int(v) = k {
                    debug!("int: (x > k) implies k < i128::MAX");
                    self.possible = self.possible && *v < i128::MAX;
                }
                // (and (< x k1) (> x k2)) implies k1 > k2 + 1
                if let Some(k1) = self.lesser.as_ref() && let Some(k2) = self.greater.as_ref() {
                    debug!("(and (< x k1) (> x k2)) implies k1 > k2 + 1");
                    self.possible = self.possible && SymOp::value_greater_plus_1(k1, k2).expect("unreachable");
                }
                // (and (x < k1) (>= x k2) implies k1 > k2
                if let Some(k1) = self.lesser.as_ref() && let Some(k2) = self.geq.as_ref() {
                    debug!("(and (x < k1) (>= x k2) implies k1 > k2");
                    self.possible = self.possible && SymOp::value_greater(k1, k2).expect("unreachable");
                }
                // (and (x <= k1) (> x k2) implies k1 > k2
                if let Some(k1) = self.leq.as_ref() && let Some(k2) = self.greater.as_ref() {
                    debug!("(and (x <= k1) (> x k2) implies k1 > k2");
                    self.possible = self.possible && SymOp::value_greater(k1, k2).expect("unreachable");
                }
                // (and (x <= k1) (>= x k2) implies k1 >= k2
                if let Some(k1) = self.leq.as_ref() && let Some(k2) = self.geq.as_ref() {
                    debug!("(and (x <= k1) (>= x k2) implies k1 >= k2");
                    self.possible = self.possible && SymOp::value_geq(k1, k2).expect("unreachable");
                }
                // (and (< x k1) (is-eq x k2)) implies k1 > k2
                if let Some(k1) = self.lesser.as_ref() && let Some(k2) = self.eq.as_ref() {
                    debug!("(and (< x k1) (is-eq x k2)) implies k1 > k2");
                    self.possible = self.possible && SymOp::value_greater(k1, k2).expect("unreachable");
                }
                // (and (<= x k1) (is-eq x k2)) implies k1 >= k2
                if let Some(k1) = self.leq.as_ref() && let Some(k2) = self.eq.as_ref() {
                    debug!("(and (<= x k1) (is-eq x k2)) implies k1 >= k2");
                    self.possible = self.possible && SymOp::value_geq(k1, k2).expect("unreachable");
                }
                // (and (> x k1) (is-eq x k2)) implies k1 < k2
                if let Some(k1) = self.greater.as_ref() && let Some(k2) = self.eq.as_ref() {
                    debug!("(and (> x k1) (is-eq x k2)) implies k1 < k2");
                    self.possible = self.possible && SymOp::value_lesser(k1, k2).expect("unreachable");
                }
                // (and (>= x k1) (is-eq x k2)) implies k1 <= k2
                if let Some(k1) = self.geq.as_ref() && let Some(k2) = self.eq.as_ref() {
                    debug!("(and (>= x k1) (is-eq x k2)) implies k1 <= k2");
                    self.possible = self.possible && SymOp::value_leq(k1, k2).expect("unreachable");
                }
                // (and (is-eq x k) (not (is-eq x k))) is impossible
                if let Some(k) = self.eq.as_ref() && self.neq.contains(k) {
                    debug!("(and (is-eq x k) (not (is-eq x k))) is impossible");
                    self.possible = false;
                }
                // (and (is-eq x k1) (x < k2)) implies k1 < k2
                if let Some(k1) = self.eq.as_ref() && let Some(k2) = self.lesser.as_ref() {
                    debug!("(and (is-eq x k1) (x < k2)) implies k1 < k2");
                    self.possible = self.possible && SymOp::value_lesser(k1, k2).expect("unreachable");
                }
                // (and (is-eq x k1) (x > k2)) implies k1 > k2
                if let Some(k1) = self.eq.as_ref() && let Some(k2) = self.greater.as_ref() {
                    debug!("(and (is-eq x k1) (x > k2)) implies k1 > k2");
                    self.possible = self.possible && SymOp::value_greater(k1, k2).expect("unreachable");
                }
                // (and (is-eq x k1) (<= x k2)) implies k1 <= k2
                if let Some(k1) = self.eq.as_ref() && let Some(k2) = self.leq.as_ref() {
                    debug!("(and (is-eq x k1) (<= x k2)) implies k1 <= k2");
                    self.possible = self.possible && SymOp::value_leq(k1, k2).expect("unreachable");
                }
                // (and (is-eq x k1) (>= x k2)) implies k1 >= k2
                if let Some(k1) = self.eq.as_ref() && let Some(k2) = self.geq.as_ref() {
                    debug!("(and (is-eq x k1) (>= x k2)) implies k1 >= k2");
                    self.possible = self.possible && SymOp::value_geq(k1, k2).expect("unreachable");
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
                    else {
                        consolidated_ops.push(Box::new(Self::Greater(op1, op2)));
                        continue;
                    }
                }
                Self::Geq(op1, op2) => {
                    if op2.is_constant() {
                        add_cmp(op1, op2, Cmp::Geq);
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
                    else {
                        consolidated_ops.push(Box::new(Self::Leq(op1, op2)));
                        continue;
                    }
                }
                Self::Less(op1, op2) => {
                    if op2.is_constant() {
                        add_cmp(op1, op2, Cmp::Lt);
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
                            let op2 = inner_ops.pop().expect("unreachable");
                            let op1 = inner_ops.pop().expect("unreachable");
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

    /// Identify conflicting cons tests and eliminate contradictions
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
                    debug!("cons {} is both (ok ..) and (err ..)", &self.op);
                    return false;
                }
                if self.is_some && self.is_none {
                    debug!("cons {} is both (some ..) and none", &self.op);
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
                debug!("Consider cons {:?}", &first);
                if !first.check_possible() {
                    return Ok(SymOp::False());
                }
                continue;
            };
            for set in rest.iter() {
                debug!("Consider cons {:?}", &set);
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


    /// Fold and propagate constants in an And(..)
    fn simplify_and(ops: Vec<Box<SymOp>>) -> Result<SymOp, Error> {
        debug!("simplify_and: ops = {ops:?}");
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
        debug!("simplify_and: consolidated_ops = {consolidated_ops:?}");
        
        // find contradictions with inequalities
        let consolidated_ops = match Self::and_inequality_constant_simplify(consolidated_ops)? {
            Self::And(ops) => ops,
            x => {
                return Ok(x);
            }
        };
        
        debug!("simplify_and: consolidated_ops = {consolidated_ops:?}");

        // flatten (is-eq) terms which have overlapping inner terms
        let consolidated_ops = Self::and_flatten_equals(consolidated_ops)?;
        
        debug!("simplify_and: consolidated_ops = {consolidated_ops:?}");
        
        // eliminate and-eq contradictions 
        let consolidated_ops = Self::and_equals_contradiction(consolidated_ops)?;
        
        debug!("simplify_and: consolidated_ops = {consolidated_ops:?}");
        
        // remove (and (is-eq x k1) (not (is-eq x k2))) redundancies (where k1 != k2)
        let consolidated_ops = Self::and_equals_redundant(consolidated_ops)?;
        
        debug!("simplify_and: consolidated_ops = {consolidated_ops:?}");
        
        // eliminate and-cons contradictions 
        let consolidated_ops = match Self::and_cons_contradiction(consolidated_ops)? {
            Self::And(ops) => ops,
            x => {
                return Ok(x);
            }
        };
        
        debug!("simplify_and: consolidated_ops = {consolidated_ops:?}");

        // remove pure duplicates and simplfiy
        let simplified = Self::dedup_pure_booleans(consolidated_ops)?;
        
        debug!("simplify_and: simplified = {simplified:?}");

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
        
        debug!("simplify_and: simplified = {simplified:?}");

        // domination: False && X == False
        for op in simplified.iter() {
            if let Self::Constant(Value::Bool(false)) = &**op {
                return Ok(SymOp::Constant(Value::Bool(false)));
            }
        }

        // identity: True && X == X
        let mut simplified : Vec<_> = simplified.into_iter().filter(|s| if let Self::Constant(Value::Bool(true)) = **s { false } else { true }).collect();
        
        debug!("simplify_and: simplified = {simplified:?}");

        // if they were all true, then simplified would be empty
        if simplified.len() == 0 {
            simplified.push(Box::new(Self::Constant(Value::Bool(true))));
        }
        else if simplified.len() == 1 {
            // lift out
            debug!("simplify_and: simplified = {simplified:?}");
            let Some(inner) = simplified.pop() else { return Err(Error::Bug("unreachable".into())); };
            return Ok(*inner);
        }

        debug!("simplify_and: simplified = {simplified:?}");
        Ok(Self::And(simplified))
    }

    /// fold and propagate constants for an Or(..)
    fn simplify_or(ops: Vec<Box<SymOp>>) -> Result<SymOp, Error> {
        let mut consolidated_ops = vec![];
        for op in ops.into_iter() {
            if let Self::Or(inner_ops) = *op {
                for inner_op in inner_ops.into_iter() {
                    let inner_op = inner_op.simplify()?;
                    consolidated_ops.push(Box::new(inner_op));
                }
            }
            else {
                consolidated_ops.push(op);
            }
        }
        
        // remove pure duplicates and simplify
        let simplified = Self::dedup_pure_booleans(consolidated_ops)?;

        // constant elimination
        let simplified = Self::simplify_assoc_variadic(
            "or",
            simplified,
            |op| *op == Self::False(),
            |op| if let Self::Or(inner) = op { Some(inner) } else { None },
            |new_ops| Self::Or(new_ops)
        )?;
        let Self::Or(simplified) = simplified else {
            return Ok(simplified);
        };

        // domination: True || X == True
        for op in simplified.iter() {
            if let Self::Constant(Value::Bool(true)) = &**op {
                return Ok(Self::Constant(Value::Bool(true)));
            }
        }
        // identity: False || X == X
        let mut simplified : Vec<_> = simplified.into_iter().filter(|s| if let Self::Constant(Value::Bool(false)) = **s { false } else { true }).collect();

        // if they were all false, then simplified would be empty
        if simplified.len() == 0 {
            simplified.push(Box::new(Self::Constant(Value::Bool(false))));
        }
        else if simplified.len() == 1 {
            // lift out
            let Some(inner) = simplified.pop() else { return Err(Error::Bug("unreachable".into())); };
            return Ok(*inner);
        }
        Ok(Self::Or(simplified))
    }

    /// fold and propagate constants for a Not(..)
    fn simplify_not(op: Box<SymOp>) -> Result<SymOp, Error> {
        match op.simplify()? {
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
    
    /// Deduplicate pure boolean formulae
    /// (i.e. ones that don't do I/O)
    fn dedup_pure_booleans(ops: Vec<Box<SymOp>>) -> Result<Vec<Box<SymOp>>, Error> {
        // remove pure duplicates and simplfiy
        let mut pure_distinct = HashSet::new();
        let mut simplified = vec![];
        for op in ops.into_iter() {
            if op.is_pure() {
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

    // fold and propagate constants for an Equals(..)
    fn simplify_equals(ops: Vec<Box<SymOp>>) -> Result<SymOp, Error> {
        let mut consolidated_ops = vec![];
        for op in ops.into_iter() {
            let op = Box::new(op.simplify()?);
            consolidated_ops.push(op);
        }

        // remove pure duplicates and simplify
        let simplified = Self::dedup_pure_booleans(consolidated_ops)?;

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

    /// Simplify a tuple get, besides a get from an option
    fn inner_simplify_tuple_get(name: ClarityName, op: SymOp) -> Result<Option<SymOp>, Error> {
        debug!("simplify (get {name} {op})");
        match op {
            Self::Constant(Value::Tuple(data)) => {
                debug!("op is a constant tuple");
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
                    debug!("op is a constant optional tuple");
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
                debug!("op is a tuple constructor");
                let Some((_name, sym)) = fields.iter().find(|(fname, _fop)| *fname == name) else {
                    return Err(Error::Bug(format!("No such tuple key {name} in {fields:?}")));
                };
                Ok(Some(*sym.clone()))
            }
            Self::ConsSome(some_inner_op) => {
                // N.B. this cannot recurse forever since the typechecker already made sure
                // that some_inner_op has type tuple
                debug!("op is a some-constructor");
                Ok(Self::inner_simplify_tuple_get(name.clone(), *some_inner_op)?
                    .map(|new_inner_op| Self::ConsSome(Box::new(new_inner_op))))
            }
            Self::LoadedDataVariable(var_name, inner_op) => match *inner_op {
                Self::Constant(Value::Tuple(data)) => {
                    debug!("op is a loaded data-var tuple constant");
                    let v = Self::context_free_clarity_eval_mainnet(vec![
                        SymbolicExpression::atom("get".try_into()?),
                        SymbolicExpression::atom(name.clone()),
                        SymbolicExpression::literal_value(Value::Tuple(data))
                    ])?
                    .ok_or_else(|| Error::Bug("Clarity VM evaluated to None".into()))?;
                    Ok(Some(Self::Constant(v)))
                }
                Self::TupleCons(fields) => {
                    debug!("op is a loaded data-var tuple constructor");
                    // lift out of fields
                    let Some((_name, sym)) = fields.iter().find(|(fname, _fop)| *fname == name) else {
                        return Err(Error::Bug(format!("No such tuple key {name} in {fields:?}")));
                    };
                    Ok(Some(*sym.clone()))
                }
                Self::ConsSome(some_inner_op) => {
                    debug!("op is a loaded data-var optional tuple");
                    // N.B. this cannot recurse forever since the typechecker already made sure
                    // that some_inner_op has type tuple
                    Ok(Some(Self::inner_simplify_tuple_get(name.clone(), *some_inner_op.clone())?
                       .unwrap_or(Self::LoadedDataVariable(var_name, Box::new(Self::ConsSome(some_inner_op))))))
                }
                x => Ok(Some(Self::LoadedDataVariable(var_name, Box::new(x))))
            }
            Self::LoadedMapEntry(map_name, map_key, Some(inner_op)) => match *inner_op {
                Self::Constant(Value::Tuple(data)) => {
                    debug!("op is a loaded map entry tuple constant");
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
                    debug!("op is a loaded map entry tuple constructor");
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
        debug!("Simplify {:?}", &symop);
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

                let ops = if let Self::Multiply(inner_ops) = ops {
                    // if we're multiplying two or more of Add(..) or Subtract(..), then compute the
                    // symbolic product and combine terms.
                    Self::flatten_multiply(inner_ops)?
                }
                else {
                    ops
                };

                Ok(ops)
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
                // TODO: (pow (pow x y) z) == (pow x (* y z))
                // TODO: (* (pow x y) (pow x z)) == (pow x (+ y z))
                // TODO: (pow u2 (log2 x)) == x
                Self::simplify_native_2args("pow", base_op, exp_op, |x, y| Self::Power(x, y))
            }
            Self::Sqrti(op) => {
                // TODO: (sqrti (* x x)) == x
                // TODO: (sqrti (* x x y)) == (* x (sqrti y))
                Self::simplify_native_1arg("sqrti", op, |x| Self::Sqrti(x))
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
                let op = Self::simplify_native_2args(">", x, y, |x, y| Self::Greater(x, y))?;
                if let Self::Greater(x, y) = op {
                    // put constants on the right hand side
                    if x.is_constant() && !y.is_constant() {
                        Ok(Self::Less(y, x))
                    }
                    // trivial case: 0 > y never
                    else if let Self::Constant(Value::UInt(0)) = *x {
                        Ok(Self::False())
                    }
                    else {
                        Ok(Self::Greater(x, y))
                    }
                }
                else {
                    Ok(op)
                }
            }
            Self::Geq(x, y) => {
                let op = Self::simplify_native_2args(">=", x, y, |x, y| Self::Geq(x, y))?;
                if let Self::Geq(x, y) = op {
                    // put constants on the right hand side
                    if x.is_constant() && !y.is_constant() {
                        Ok(Self::Leq(y, x))
                    }
                    // trivial case: x >= u0 always
                    else if let Self::Constant(Value::UInt(0)) = *y {
                        Ok(Self::True())
                    }
                    else {
                        Ok(Self::Geq(x, y))
                    }
                }
                else {
                    Ok(op)
                }
            },
            Self::Equals(ops) => {
                Self::simplify_equals(ops)
            }
            Self::Leq(x, y) => {
                let op = Self::simplify_native_2args("<=", x, y, |x, y| Self::Leq(x, y))?;
                if let Self::Leq(x, y) = op {
                    // put constants on the right hand side
                    if x.is_constant() && !y.is_constant() {
                        Ok(Self::Geq(y, x))
                    }
                    // trivial case: u0 <= y always
                    else if let Self::Constant(Value::UInt(0)) = *x {
                        Ok(Self::True())
                    }
                    else {
                        Ok(Self::Leq(x, y))
                    }
                }
                else {
                    Ok(op)
                }
            },
            Self::Less(x, y) => {
                let op = Self::simplify_native_2args("<", x, y, |x, y| Self::Less(x, y))?;
                if let Self::Less(x, y) = op {
                    // put constants on the right hand side
                    if x.is_constant() && !y.is_constant() {
                        Ok(Self::Greater(y, x))
                    }
                    // trivial case: x < u0 never
                    else if let Self::Constant(Value::UInt(0)) = *y {
                        Ok(Self::False())
                    }
                    else {
                        Ok(Self::Less(x, y))
                    }
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
            Self::Concat(op1, op2) => {
                // TODO: can symbolically concatenate
                Self::simplify_native_2args("concat", op1, op2, |x, y| Self::Concat(x, y))
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
                Self::simplify_native_3args("secp256r1-verify", op1, op2, op3, |x, y, z| Self::Secp256r1Verify(x, y, z))
            }
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
        loop {
            let new = Self::inner_simplify(cur.clone())?;
            if new == cur {
                return Ok(new);
            }
            cur = new;
        }
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
        debug!("Bind symbol '{sym_id}' to {symop} in {self}");
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
            Self::Concat(op1, op2) => Self::Concat(op1.bind_symbol(sym_id.clone(), symop.clone()), op2.bind_symbol(sym_id.clone(), symop.clone())),
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
    
    fn as_symop(self) -> SymOp {
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


// NOTE: insert is a special case, since it is implicitly the following:
// ```
// (if (is-none (map-get MAP_ID KEY)) (map-set MAP_ID KEY VALUE) false)
// ```
#[derive(Debug, Clone, PartialEq)]
pub enum MapOp {
    Get(ClarityName, SymOp),
    Set(ClarityName, SymOp, SymOp),
    Insert(ClarityName, SymOp, SymOp),
    Delete(ClarityName, SymOp),
}

#[derive(Debug, Clone, PartialEq)]
pub enum VarOp {
    Get(ClarityName),
    Set(ClarityName, SymOp)
}

impl VarOp {
    pub fn simplify(self) -> Result<VarOp, Error> {
        match self {
            Self::Get(name) => Ok(Self::Get(name)),
            Self::Set(name, op) => Ok(Self::Set(name, op.simplify()?))
        }
    }

    pub fn var_name(&self) -> &ClarityName {
        match self {
            Self::Get(name) => name,
            Self::Set(name, ..) => name
        }
    }
}

impl MapOp {
    pub fn simplify(self) -> Result<MapOp, Error> {
        match self {
            Self::Get(name, op) => Ok(Self::Get(name, op.simplify()?)),
            Self::Set(name, op, val) => Ok(Self::Set(name, op.simplify()?, val.simplify()?)),
            Self::Insert(name, op, val) => Ok(Self::Insert(name, op.simplify()?, val.simplify()?)),
            Self::Delete(name, op) => Ok(Self::Delete(name, op.simplify()?)),
        }
    }
}

impl fmt::Display for VarOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::Get(name) => write!(f, "(var-get {})", name),
            Self::Set(name, symop) => write!(f, "(var-set {} {})", name, symop),
        }
    }
}

impl fmt::Display for MapOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::Get(name, key_symop) => write!(f, "(map-get? {} {})", name, key_symop),
            Self::Set(name, key_symop, value_symop) => write!(f, "(map-set {} {} {})", name, key_symop, value_symop),
            Self::Insert(name, key_symop, value_symop) => write!(f, "(map-insert {} {} {})", name, key_symop, value_symop),
            Self::Delete(name, key_symop) => write!(f, "(map-delete {} {})", name, key_symop)
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
        write!(f, "{}: {} {}::{}:{} {} {}", self.depth, self.cont_id, &self.contract_id, &self.identifier, self.start_line, &bound_formulae_str, &unbound_formulae_str)
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

#[derive(Clone, Debug, PartialEq)]
pub struct VarAccess {
    pub name: ClarityName,
    pub value: SymOp,
    pub line: u32
}

#[derive(Clone, Debug, PartialEq)]
pub struct MapAccess {
    pub name: ClarityName,
    pub key: SymOp,
    pub value: Option<SymOp>,
    pub line: u32
}

/// A symbolic continuation
#[derive(Clone, Debug, PartialEq)]
pub struct Continuation {
    /// internal identifier to ensure uniqueness
    id: u64,
    /// Current "function" (really, it identifies what code is being evaluated)
    current_function: Option<String>,
    /// line in the source code
    current_line: Option<u32>,
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
    pre_vars: Vec<VarOp>,
    /// data-var formulae after evaluation
    pub post_vars: Vec<VarOp>,
    /// map data that was read (but not written), and thus serves as input
    /// TODO: do a copy-on-write version of this, like we do for data vars
    pub pre_map_state: HashMap<ClarityName, HashSet<SymOp>>,
    /// current view of each map
    /// TODO: do a copy-on-write version of this, like we do for data vars
    pub map_state: HashMap<ClarityName, HashMap<SymOp, SymOp>>,
    pub map_tombstones: HashMap<ClarityName, HashSet<SymOp>>,
    /// map accesses, and what they returned
    pub map_accesses: Vec<MapAccess>,
    /// var accesses, and what they returned
    pub var_accesses: Vec<VarAccess>,
    /// map state that could be accessed (i.e. is reachable by) a function that was not explored in
    /// this continuation's evaluation
    /// TODO: do a copy-on-write version of this, like we do for data vars
    pub reachable_map_reads: HashSet<ClarityName>,
    /// map state that could be written by a function that was not explored in
    /// this continuation's evaluation
    /// TODO: do a copy-on-write version of this, like we do for data vars
    pub reachable_map_writes: HashSet<ClarityName>,
    /// var state that could be accessed (i.e. is reachable by) a function that was not explored in
    /// this continuation's evaluation
    /// TODO: do a copy-on-write version of this, like we do for data vars
    pub reachable_var_reads: HashSet<ClarityName>,
    /// var state that could be written (i.e. is reachable by) a function that was not explored in
    /// this continuation's evaluation
    /// TODO: do a copy-on-write version of this, like we do for data vars
    pub reachable_var_writes: HashSet<ClarityName>,
    /// events generated 
    events: Vec<SymOp>,
    /// whether or not this continuation panicked
    pub panicking: bool,
    /// whether or not this continuation represents an early return
    pub early_return: bool,
}

impl fmt::Display for Continuation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        writeln!(f, "ID:               {}", &self.id)?;
        writeln!(f, "Path:             {}", &self.current_function.as_ref().unwrap_or(&"".to_string()))?;
        writeln!(f, "Panicked:         {}", &self.panicking)?;
        writeln!(f, "Early return:     {}", &self.early_return)?;
        writeln!(f, "tx-sender:        {}", &self.get_tx_sender())?;
        writeln!(f, "contract-caller:  {}", &self.get_contract_caller())?;
        writeln!(f, "current-contract: {}", &self.get_current_contract())?;
        writeln!(f, "Predicate:        {}", &self.predicate)?;
        writeln!(f, "Formula:          {}", &self.final_formula)?;
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
        if self.pre_vars.len() > 0 {
            for varop in self.pre_vars.iter() {
                writeln!(f, "   {}", varop)?;
            }
        }
        else {
            writeln!(f, "   (empty)")?;
        }

        writeln!(f, "Output vars computed:")?;
        if self.post_vars.len() > 0 {
            let mut seen_vars : HashSet<&ClarityName> = HashSet::new();
            for varop in self.post_vars.iter().rev() {
                if let VarOp::Set(name, ..) = varop {
                    if seen_vars.contains(name) {
                        continue;
                    }
                    seen_vars.insert(name);
                }
                if is_debug() {
                    writeln!(f, "   Not simplified: {}", varop)?;
                }
                writeln!(f, "   {}", match varop.clone().simplify() {
                    Ok(vop) => format!("{}", &vop),
                    Err(e) => format!("ERROR: failed to simplify: {:?}", &e)
                })?;
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
                let as_strs: Vec<_> = self.reachable_var_reads.iter().map(|n| n.as_str().to_string()).collect();
                as_strs.join(", ")
            }
            else {
                "(none)".to_string()
            })?;
        
        writeln!(f, "Possibly-written data vars:\n   {}",
            if self.reachable_var_writes.len() > 0 {
                let as_strs: Vec<_> = self.reachable_var_writes.iter().map(|n| n.as_str().to_string()).collect();
                as_strs.join(", ")
            }
            else {
                "(none)".to_string()
            })?;
        
        writeln!(f, "Possibly-read maps:\n   {}",
            if self.reachable_map_reads.len() > 0 {
                let as_strs: Vec<_> = self.reachable_map_reads.iter().map(|n| n.as_str().to_string()).collect();
                as_strs.join(", ")
            }
            else {
                "(none)".to_string()
            })?;
        
        writeln!(f, "Possibly-written maps:\n   {}",
            if self.reachable_map_writes.len() > 0 {
                let as_strs: Vec<_> = self.reachable_map_writes.iter().map(|n| n.as_str().to_string()).collect();
                as_strs.join(", ")
            }
            else {
                "(none)".to_string()
            })?;
        Ok(())
    }
}

impl Continuation {
    pub fn root(symbex: &Symbex, current_contract: PrincipalData) -> Self {
        let mut cont = Self {
            id: next_cont_id(),
            current_function: None,
            current_line: None,
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
            pre_vars: vec![],
            post_vars: vec![],
            pre_map_state: HashMap::new(),
            map_state: HashMap::new(),
            map_tombstones: HashMap::new(),
            map_accesses: vec![],
            var_accesses: vec![],
            reachable_map_reads: HashSet::new(),
            reachable_map_writes: HashSet::new(),
            reachable_var_reads: HashSet::new(),
            reachable_var_writes: HashSet::new(),
            events: vec![],
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
        info!("Root continuation {}", cont.id);
        cont
    }

    pub fn from_parent(parent: Rc<Continuation>, function_name: String, start_line: u32) -> Self {
        Self::inner_from_parent(parent, function_name, start_line, false)
    }

    fn inner_from_parent(parent: Rc<Continuation>, function_name: String, start_line: u32, from_early_return: bool) -> Self {
        assert!(!parent.panicking, "BUG: tried to continue from a panic");
        if !from_early_return {
            assert!(!parent.early_return);
        }
        let parent_id = parent.id;
        let cont = Self {
            id: next_cont_id(),
            current_function: Some(function_name),
            current_line: Some(start_line),
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
            pre_vars: vec![],
            pre_map_state: parent.pre_map_state.clone(),
            map_state: parent.map_state.clone(),
            map_tombstones: HashMap::new(),
            map_accesses: vec![],
            var_accesses: vec![],
            reachable_map_reads: parent.reachable_map_reads.clone(),
            reachable_map_writes: parent.reachable_map_writes.clone(),
            reachable_var_reads: parent.reachable_var_reads.clone(),
            reachable_var_writes: parent.reachable_var_writes.clone(),
            post_vars: vec![],
            events: vec![],
            panicking: false,
            early_return: false,
        };
        debug!("Created continuation {} ({}) from parent {}: pred={}", cont.id, cont.current_function.as_ref().map(|s| s.as_str()).unwrap_or("unreachable"), parent_id, &cont.predicate);
        cont
    }
    
    pub fn from_caller(parent: Rc<Continuation>, function_name: String, start_line: u32) -> Self {
        assert!(!parent.panicking, "BUG: tried to continue from a panic");
        let parent_copy = parent.clone();
        let parent_id = parent.id;
        let mut cont = Self::from_parent(parent, function_name, start_line);
        cont.caller = Some(parent_copy);
        debug!("Created continuation {} ({}) from caller {}", cont.id, cont.current_function.as_ref().map(|s| s.as_str()).unwrap_or("unreachable"), parent_id);
        cont
    }

    pub fn from_callee(parent: Rc<Continuation>, function_name: String, start_line: u32) -> Self {
        assert!(!parent.panicking, "BUG: tried to continue from a panic");
        let parent_id = parent.id;
        let parent_caller_caller = if let Some(parent_caller) = (*parent).caller.as_ref() {
            parent_caller.caller.clone()
        }
        else {
            None
        };

        let early_return = parent.early_return;
        let mut cont = Self::inner_from_parent(parent.clone(), function_name, start_line, true);
        cont.early_return = early_return;
        cont.bound_formulae = parent_caller_caller.as_ref().map(|parent_caller| parent_caller.bound_formulae.clone()).unwrap_or(HashMap::new());
        cont.caller = parent_caller_caller;

        debug!("Created continuation {} ({}) from callee {}", cont.id, cont.current_function.as_ref().map(|s| s.as_str()).unwrap_or("unreachable"), parent_id);
        cont
    }

    /// Given a pre-evaluated "free" continuation representing a function (i.e. where all input and output
    /// variables are free), and given a parent continuation which "calls" this function (i.e.
    /// it binds all of the input symbols), compute a new continuation from the free continuation
    /// by binding all of the parent's symbols into its formulae, maps, data-vars, and predicates.
    /// It's as if the parent has called the function represented by the free continuation, but
    /// skipping the needless work of re-evaluating every possible continuation of the function.
    pub fn from_evaluated(free: &Continuation, function_name: String, parent: Rc<Continuation>) -> Result<Self, Error> {
        assert!(!parent.panicking, "BUG: tried to continue from a panic");
        assert!(!free.panicking, "BUG: tried to build from a panicked free continuation");

        let mut bound_formulae = free.bound_formulae.clone();
        bound_formulae.extend(parent.bound_formulae.clone().into_iter());

        let mut predicate = free.predicate.clone().as_symop().and(parent.predicate.clone().as_symop());
        for (sym_id, symop) in bound_formulae.iter() {
            predicate = *predicate.bind_symbol(sym_id.clone(), symop.clone());
        }
        let predicate = predicate.try_as_predicate()?;

        let mut final_formula = free.final_formula.clone();
        for (sym_id, symop) in bound_formulae.iter() {
            final_formula = *final_formula.bind_symbol(sym_id.clone(), symop.clone());
        }
        
        let mut post_vars = vec![];
        for op in free.post_vars.iter() {
            let new_op = match op {
                VarOp::Get(n) => VarOp::Get(n.clone()),
                VarOp::Set(n, op) => {
                    let mut new_op = op.clone();
                    for (sym_id, symop) in bound_formulae.iter() {
                        let symop = symop.clone().simplify()?;
                        new_op = new_op.bind_symbol(sym_id.clone(), symop).simplify()?;
                    }
                    VarOp::Set(n.clone(), new_op)
                }
            };
            post_vars.push(new_op);
        }
        
        let mut pre_map_state = parent.pre_map_state.clone();
        for (map_name, map_info) in free.pre_map_state.iter() {
            for key_sym in map_info.iter() {
                let mut new_key_sym = key_sym.clone();
                for (sym_id, symop) in bound_formulae.iter() {
                    let symop = symop.clone().simplify()?;
                    new_key_sym = new_key_sym.bind_symbol(sym_id.clone(), symop.clone()).simplify()?;
                }
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
                    new_key_sym = new_key_sym.bind_symbol(sym_id.clone(), symop.clone()).simplify()?;
                    new_val_sym = new_val_sym.bind_symbol(sym_id.clone(), symop.clone()).simplify()?;
                }
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
                    new_key_sym = new_key_sym.bind_symbol(sym_id.clone(), symop.clone()).simplify()?;
                }
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
            current_function: Some(function_name),
            current_line: free.current_line.clone(),
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
            pre_vars: parent.pre_vars.clone(),
            post_vars,
            pre_map_state,
            map_state,
            map_tombstones,
            map_accesses,
            var_accesses,
            reachable_map_reads,
            reachable_map_writes,
            reachable_var_reads,
            reachable_var_writes,
            events: parent.events.clone(),
            panicking: false,
            early_return: free.early_return || parent.early_return,
        };

        info!("Created continuation {} ({}) from pre-evaluated continuation {} and parent {}", cont.id, cont.current_function.as_ref().map(|s| s.as_str()).unwrap_or("unreachable"), free.id, parent.id);
        info!("Parent continuation\n{}", parent);
        info!("Free continuation\n{}", free);
        info!("Evaluated continuation\n{}", &cont);
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

    /// Find the data var formula with the given data var name
    fn lookup_data_var(&self, name: &ClarityName) -> Option<&SymOp> {
        let mut cursor = self;
        loop {
            for var_val in cursor.post_vars.iter().rev() {
                if let VarOp::Set(var_id, val) = var_val {
                    if name == var_id {
                        if let SymOp::LoadedDataVariable(_name, inner_formula) = val {
                            return Some(inner_formula);
                        }
                    }
                }
            }
            for var_val in cursor.pre_vars.iter().rev() {
                if let VarOp::Set(var_id, val) = var_val {
                    if name == var_id {
                        if let SymOp::LoadedDataVariable(_name, inner_formula) = val {
                            return Some(inner_formula);
                        }
                    }
                }
            }
            if let Some(parent) = cursor.parent.as_ref() {
                cursor = parent;
            }
            else {
                return None;
            }
        }
    }

    /// record that a map access happend
    pub fn read_data_var(&mut self, name: ClarityName, val: SymOp, line: u32) {
        self.var_accesses.push(VarAccess {
            name,
            value: val,
            line
        })
    }

    /// Find the map entry formula with the given map name and key
    /// key_op must be simplified
    pub fn lookup_map_entry(&self, name: &ClarityName, key_op: &SymOp) -> Option<&SymOp> {
        if self.is_map_deleted(name, key_op) {
            return None;
        }

        let map_index = self.map_state.get(name)?;
        map_index.get(key_op)
    }
    
    /// See if this key was recently deleted
    /// key_op must be simplified
    pub fn is_map_deleted(&self, name: &ClarityName, key_op: &SymOp) -> bool {
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
        self.pre_vars.push(VarOp::Set(name.clone(), SymOp::LoadedDataVariable(name.clone(), Box::new(symop))));
    }

    /// Set a data-var formula consequent to a (var-set ..)
    /// symop should be simplified
    pub fn set_post_data_var(&mut self, name: &ClarityName, symop: SymOp) {
        self.post_vars.push(VarOp::Set(name.clone(), SymOp::LoadedDataVariable(name.clone(), Box::new(symop))));
    }

    /// Record that a map entry was accessed, and possibly had the given value at the time
    pub fn read_map_entry(&mut self, name: ClarityName, key_symop: SymOp, val_symop: Option<SymOp>, line: u32) {
        if val_symop.is_none() {
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
        self.map_accesses.push(MapAccess {
            name,
            key: key_symop,
            value: val_symop,
            line
        });
    }

    /// Set a map entry consequent to a (map-set ..)
    /// key_symop must be simplified.
    pub fn set_map_entry(&mut self, name: &ClarityName, key_symop: SymOp, val_symop: SymOp) {
        if let Some(idx) = self.map_tombstones.get_mut(name) {
            idx.remove(&key_symop);
        }
        if let Some(map) = self.map_state.get_mut(name) {
            map.insert(key_symop, val_symop);
        }
        else {
            let mut map = HashMap::new();
            map.insert(key_symop, val_symop);
            self.map_state.insert(name.clone(), map);
        }
    }
    
    /// Delete a map entry
    pub fn delete_map_entry(&mut self, name: &ClarityName, key_symop: &SymOp) -> bool {
        let present = if let Some(map) = self.map_state.get_mut(name) {
            let present = map.contains_key(&key_symop);
            map.remove(key_symop);
            present
        }
        else {
            false
        };
        if let Some(idx) = self.map_tombstones.get_mut(name) {
            idx.insert(key_symop.clone());
        }
        else {
            let mut idx = HashSet::new();
            idx.insert(key_symop.clone());
            self.map_tombstones.insert(name.clone(), idx);
        }
        present
    }

    /// Compute a trace of how this continuation arrived to where it did
    pub fn trace(&self) -> Trace {
        let mut cursor_stack = vec![];
        let mut trace_items = vec![];
            
        let mut self_trace = TraceItem {
            depth: 0,
            identifier: self.current_function.clone().unwrap_or("".to_string()),
            contract_id: self.get_current_contract_id(),
            start_line: self.current_line.clone().unwrap_or(0),
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
                identifier: cursor.current_function.clone().unwrap_or("".to_string()),
                contract_id: cursor.get_current_contract_id(),
                start_line: cursor.current_line.clone().unwrap_or(0),
                cont_id: cursor.id,
                bound_formulae: cursor.bound_formulae.clone(),
                dropped_formulae: cursor.dropped_formulae.clone(),
                predicate: cursor.predicate.clone(),
            };
            trace_items.push(trace_item);
        }

        let depth = trace_items.len();
        trace_items.iter_mut().for_each(|t| t.depth = depth - t.depth);
        self_trace.depth = depth;
        trace_items.push(self_trace);
        trace_items.reverse();
        Trace(trace_items)
    }

    /// Roll up this continuation with its ancestors, back to a certain ancestor ID (inclusive)
    pub fn rollup_to(self, ancestor_id: Option<u64>) -> Self {
        let mut pre_vars = vec![];
        let mut final_vars = vec![];
        let mut final_map_accesses = vec![];
        let mut final_var_accesses = vec![];
        let mut events = vec![];
        let tx_sender = self.get_tx_sender();
        let contract_caller = self.get_contract_caller();
        let current_contract = self.get_current_contract();

        let mut cursor_stack = vec![];
        cursor_stack.push(&self);

        let mut end = false;
        let mut panicking = self.panicking;
        let early_return = self.early_return || self.halted();
        let mut parent = None;
        let mut caller = None;

        if early_return {
            debug!("Rolling up an early-return continuation {}", self.id);
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

        debug!("Roll back continunation {} to its ancestor {:?}", self.id, &ancestor_id);

        // compute state for the rolled-up continuation
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
            debug!("Rolling back from continuation {}", cursor.id);
            if !end {
                parent = cursor.parent.clone();
                caller = cursor.caller.clone();
                debug!("New parent of rolled-up continuation {} will be {}", self.id, parent.as_ref().map(|p| format!("{}", p.id)).unwrap_or("(none)".to_string()));
                debug!("New caller of rolled-up continuation {} will be {}", self.id, caller.as_ref().map(|c| format!("{}", c.id)).unwrap_or("(none)".to_string()));
                if let Some(ancestor_id) = ancestor_id {
                    assert_eq!(parent.as_ref().map(|p| p.id), Some(ancestor_id));
                }
                end = true;
            }
            if cursor.post_vars.len() > 0 {
                for pv in cursor.post_vars.iter().rev() {
                    debug!("post-var in {}: {pv}", cursor.id);
                }
            }
            pre_vars.extend(cursor.pre_vars.clone().into_iter());
            final_vars.extend(cursor.post_vars.clone().into_iter());
            final_var_accesses.extend(cursor.var_accesses.clone().into_iter());
            final_map_accesses.extend(cursor.map_accesses.clone().into_iter());
            events.extend(cursor.events.clone().into_iter());
            panicking = panicking || cursor.panicking;
        }

        let mut seen_vars : HashSet<ClarityName> = HashSet::new();
        let mut post_vars = vec![];
        for varop in final_vars.into_iter().rev() {
            if let VarOp::Set(name, ..) = &varop {
                if seen_vars.contains(name) {
                    continue;
                }
                seen_vars.insert(name.clone());
            }
            post_vars.push(varop);
        }

        let old_cont_str = self.to_string();
        let old_trace = self.trace();
        
        let merged = Self {
            id: next_cont_id(),
            bound_formulae: self.bound_formulae.clone(),
            post_vars: post_vars,
            pre_vars: pre_vars,
            pre_map_state: self.pre_map_state.clone(),
            map_state: self.map_state.clone(),
            map_tombstones: self.map_tombstones.clone(),
            var_accesses: final_var_accesses,
            map_accesses: final_map_accesses,
            reachable_map_reads: self.reachable_map_reads.clone(),
            reachable_map_writes: self.reachable_map_writes.clone(),
            reachable_var_reads: self.reachable_var_reads.clone(),
            reachable_var_writes: self.reachable_var_writes.clone(),
            events,
            tx_sender: Some(tx_sender),
            contract_caller: Some(contract_caller),
            current_contract: Some(current_contract),
            panicking: panicking,
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
        debug!("Continuation name: {}", merged.current_function.as_ref().map(|s| s.as_str()).unwrap_or(""));
        debug!("Continuation:\n{}", &merged);
        debug!("Trace:\n{}", &merged.trace());
        debug!("Old continuation:\n{old_cont_str}");
        debug!("Old trace:\n{old_trace}");
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
    /// * Has it panicked?
    /// * Is it marked as an early-return continuation, and its calling continuation matches its
    /// the calling continuation of its parent?
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
    pub fn is_causally_independent(&self, func_name: &CallableName, callgraph: &Callgraph) -> Result<bool, Error> {
        let reachable_map_accesses : HashSet<_> = callgraph.reachable_map_accesses_from(func_name)?
            .into_iter()
            .collect();
        
        let reachable_var_accesses : HashSet<_> = callgraph.reachable_var_accesses_from(func_name)?
            .into_iter()
            .collect();

        let mut all_accesses = HashSet::new();
        all_accesses.extend(reachable_map_accesses.into_iter());
        all_accesses.extend(reachable_var_accesses.into_iter());

        let rolled_up = self.clone().rollup();
        for accessed in all_accesses.into_iter() {
            if rolled_up.map_state.contains_key(&accessed) {
                // this function may access a map written in this continuation
                info!("Function {func_name} reads state from map {accessed}, which was written to by continuation {}", self.id);
                return Ok(false);
            }
            if rolled_up.post_vars.iter().find(|v| if let VarOp::Set(varname, ..) = v && varname == &accessed { true } else { false }).is_some() {
                // this function may access a var written in this continuation
                info!("Function {func_name} reads state from data-var {accessed}, which was written to by continuation {}", self.id);
                return Ok(false);
            }
            if rolled_up.reachable_var_writes.contains(&accessed) {
                // this function may access a var that might have been written before
                info!("Function {func_name} reads state from data-var {accessed}, which may be written to by continuation {}", self.id);
                return Ok(false);
            }
            if rolled_up.reachable_map_writes.contains(&accessed) {
                // this function may access a map that might have been written before
                info!("Function {func_name} reads state from map {accessed}, which may be written to by continuation {}", self.id);
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
        let mut evaled_map_reads : HashMap<ClarityName, HashSet<SymOp>> = HashMap::new();

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
                        info!("Evaled continuation {} reads map {map_name} key {key_sym}, which continuation {} wrote", evaled_cont.id, self.id);
                        return Ok(false);
                    }
                }
            }
        }
        
        for var_access in evaled_cont.var_accesses.iter() {
            let var_name = &var_access.name;
            if self.lookup_data_var(var_name).is_some() {
                // this cont write a var that evaled_cont reads
                info!("Evaled continuation {} reads var {var_name}, which continuation {} wrote", evaled_cont.id, self.id);
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
        
        // check this and ancestral var writes
        let mut cursor = self;
        loop {
            for var_val in cursor.post_vars.iter().rev() {
                if let VarOp::Set(..) = var_val {
                    return false;
                }
            }
            if let Some(parent) = cursor.parent.as_ref() {
                cursor = parent;
            }
            else {
                break;
            }
        }

        true
    }

    /// Given a function and a callgraph, add to this continuation the set of map and var accesses
    /// that may be reached from it
    pub fn add_reachable_storage_accesses(&mut self, func_name: &CallableName, callgraph: &Callgraph) -> Result<(), Error> {
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
}


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CallableName(pub QualifiedContractIdentifier, pub ClarityName);

impl fmt::Display for CallableName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}.{}", &self.0, &self.1)
    }
}

impl CallableName {
    pub fn name(&self) -> &ClarityName {
        &self.1
    }

    pub fn contract_id(&self) -> &QualifiedContractIdentifier {
        &self.0
    }
}

#[derive(Debug, Clone, PartialEq, Hash)]
pub struct CallgraphFunction {
    pub fq_name: CallableName,
    pub start_line: u32
}

impl fmt::Display for CallgraphFunction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}:{}", &self.fq_name, self.start_line)
    }
}

impl CallgraphFunction {
    pub fn new(fq_name: CallableName, start_line: u32) -> Self {
        Self {
            fq_name,
            start_line
        }
    }

    pub fn call_name(&self) -> &CallableName {
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
    pub var_reads: HashSet<ClarityName>,
    /// list of maps that this function may read from
    pub map_reads: HashSet<ClarityName>,
    /// list of vars that this function may write to
    pub var_writes: HashSet<ClarityName>,
    /// list of maps that this function may write to
    pub map_writes: HashSet<ClarityName>,
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
    
    pub fn add_readable_var(&mut self, var_name: ClarityName) {
        self.var_reads.insert(var_name);
    }

    pub fn add_readable_map(&mut self, map_name: ClarityName) {
        self.map_reads.insert(map_name);
    }

    pub fn add_writable_var(&mut self, var_name: ClarityName) {
        self.var_writes.insert(var_name);
    }

    pub fn add_writable_map(&mut self, map_name: ClarityName) {
        self.map_writes.insert(map_name);
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Callgraph {
    reachable: HashMap<CallableName, CallgraphNode>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct CallgraphView<'a> {
    callgraph: &'a Callgraph,
    cursor: CallableName
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

            writeln!(f, "{indent}{}:", name.name())?;
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
    pub fn from_exprs(contract_context: &ContractContext, exprs: &[SymbolicExpression]) -> Result<Callgraph, Error> {
        let mut callgraph = Self::empty();
        callgraph.load_defs(contract_context, exprs)?;
        Ok(callgraph)
    }

    fn empty() -> Self {
        Self {
            reachable: HashMap::new()
        }
    }

    fn load_defs(&mut self, contract_context: &ContractContext, bodies: &[SymbolicExpression]) -> Result<(), Error> {
        let mut frontier : HashMap<CallableName, &[SymbolicExpression]> = HashMap::new();
        for body in bodies.iter() {
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
                let Some(def_name_atom) = name_and_args.first() else {
                    return Err(Error::Bug(format!("No function definition for {name_and_args:?}")));
                };
                let Some(def_name) = def_name_atom.match_atom() else {
                    return Err(Error::Bug(format!("Function definition name is not an atom: {def_name_atom}")));
                };
                let Some(func_body) = lv.get(2..) else {
                    return Err(Error::Bug(format!("No function body for {def_name}")));
                };

                let node = CallgraphNode::new();
                let fq_name = CallableName(contract_context.contract_identifier.clone(), def_name.clone());
                self.reachable.insert(fq_name.clone(), node);

                debug!("top-level function {}", &fq_name);
                frontier.insert(fq_name, func_body);
            }
        }

        for (name, func_body) in frontier.into_iter() {
            self.build(contract_context, &name, func_body)?;
        }
        let mut is_pure = HashMap::new();
        for name in self.reachable.keys() {
            let is_pure_func = self.check_pure(name)?;
            is_pure.insert(name.clone(), is_pure_func);
        }

        for (name, is_pure) in is_pure.into_iter() {
            let Some(node) = self.reachable.get_mut(&name) else {
                return Err(Error::Bug("unreachable".into()));
            };
            debug!("Function {name} is {}", if is_pure { "pure" } else { "not pure" });
            node.is_pure = is_pure;
        }

        Ok(())
    }

    fn build(&mut self, contract_context: &ContractContext, func_name: &CallableName, body_list: &[SymbolicExpression]) -> Result<(), Error> {
        for body in body_list.iter() {
            debug!("build: {func_name}: visit {}", &body.expr);
            let Some(lv) = body.match_list() else {
                continue;
            };
            let Some(first) = lv.first() else {
                return Err(Error::Bug(format!("empty list in {func_name}")));
            };
            if let Some(function_base_name) = first.match_atom() {
                match function_base_name.as_str() {
                    "contract-call?" => {
                        todo!()
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
                        
                        debug!("function {} mutates map {}", &func_name, map_name);
                        node.add_writable_map(map_name.clone());
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
                        
                        debug!("function {} accesses map {}", &func_name, map_name);
                        node.add_readable_map(map_name.clone());
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
                        let fq_name = CallableName(func_name.contract_id().clone(), called_func_name.clone());
                        debug!("function {func_name} calls {fq_name}");
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
                        
                        debug!("function {} mutates var {}", &func_name, var_name);
                        node.add_writable_var(var_name.clone());
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
                        
                        debug!("function {} accesses var {}", &func_name, var_name);
                        node.add_readable_var(var_name.clone());
                    },
                    _ => {
                        if contract_context.functions.get(function_base_name).is_some() {
                            let fq_name = CallableName(func_name.contract_id().clone(), function_base_name.clone());
                            let Some(node) = self.reachable.get_mut(&func_name) else {
                                return Err(Error::Bug(format!("Unexplored function {function_base_name}")));
                            };
                            debug!("function {func_name} calls {fq_name}");
                            node.callable.push(CallgraphFunction::new(fq_name, body.span.start_line));
                        }
                        for ili in lv.iter() {
                            self.build(contract_context, func_name, &[ili.clone()])?;
                        }
                    }
                }
            }
            else {
                for ili in lv.iter() {
                    self.build(contract_context, func_name, &[ili.clone()])?;
                }
            }
        }
        Ok(())
    }

    /// Compute the set of reachable functions from a given function.
    /// Returns None if the function is not known
    pub fn reachable_from(&self, func_name: &CallableName) -> Result<Vec<CallableName>, Error> {
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
    pub fn get_node(&self, func_name: &CallableName) -> Option<&CallgraphNode> {
        self.reachable.get(func_name)
    }

    /// Get all functions defined in a given contract
    pub fn get_contract_functions(&self, contract_id: &QualifiedContractIdentifier) -> Vec<CallableName> {
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
    pub fn reachable_map_accesses_from(&self, func_name: &CallableName) -> Result<Vec<ClarityName>, Error> {
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
    pub fn reachable_map_mutations_from(&self, func_name: &CallableName) -> Result<Vec<ClarityName>, Error> {
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
    pub fn reachable_var_accesses_from(&self, func_name: &CallableName) -> Result<Vec<ClarityName>, Error> {
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
    pub fn reachable_var_mutations_from(&self, func_name: &CallableName) -> Result<Vec<ClarityName>, Error> {
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
    fn check_pure(&self, func_name: &CallableName) -> Result<bool, Error> {
        Ok(self.reachable_map_accesses_from(func_name)?.len() == 0
           && self.reachable_map_mutations_from(func_name)?.len() == 0
           && self.reachable_var_accesses_from(func_name)?.len() == 0
           && self.reachable_var_mutations_from(func_name)?.len() == 0)
    }

    /// Report whether or not a given function is pure
    pub fn is_pure(&self, func_name: &CallableName) -> Result<bool, Error> {
        let node = self.get_node(func_name).ok_or_else(|| Error::NotFound(format!("{func_name}")))?;
        Ok(node.is_pure)
    }

    pub fn view<'a>(&'a self, func_name: &CallableName) -> Option<CallgraphView<'a>> {
        if self.reachable.get(func_name).is_none() {
            return None;
        }

        Some(CallgraphView {
            callgraph: self,
            cursor: func_name.clone()
        })
    }
}

/// Symbolic execution engine
#[derive(Debug)]
pub struct Symbex {
    datastore: BackingStore,
    contract_context: ContractContext,
    symbols: Vec<SymbolicExpression>,
    typemap: TypeMap,
    tx_sender: Option<SymOp>,
    tx_sponsor: Option<SymOp>,
    contract_caller: Option<SymOp>,
    pub callgraph: Callgraph,
    /// option to skip evaluating all function calls
    explore_function_calls: bool,
    /// option to skip evaluating specific function calls
    skip_function_calls: HashSet<ClarityName>,
    /// option to skip function calls that do not do I/O and instead treat them as symbols
    skip_pure_calls: bool,
    /// option to skip function calls that do I/O that is causally independent of the
    /// currently-evaluating continuation
    skip_causally_independent_calls: bool,
    /// cache of evaluated function calls, with all function arguments unbound.
    /// Maps the SymbolicExpression ID to the set of halting continuations
    evaluated_functions: HashMap<CallableName, Vec<Continuation>>
}

impl Symbex {
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

    // simplify each continuation's predicate and formula.
    // eliminate unreachable continuations.
    // if we have a chain of linear continuations, then compress them.
    fn reduce_continuations(conts: Vec<Continuation>) -> Vec<Continuation> {
        let mut filtered_conts : Vec<_> = conts
           .into_iter()
           .map(|mut c| {
               let p = c.predicate.clone();
               match p.simplify() {
                   Ok(p) => {
                       debug!("Continuation {} simplified predicate = {p}, old predicate = {}", c.id, &c.predicate);
                       c.predicate = p.clone();
                   }
                   Err(e) => {
                       panic!("failed to simplify predicate: {e:?}");
                   }
               }
               let f = c.final_formula.clone();
               match f.simplify() {
                   Ok(f) => {
                       debug!("Continuation {} simplified final formula = {f}, old final formula = {}", c.id, &c.final_formula);
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
                   debug!("Continuation always panics:\n{c}");
               }

               if c.predicate != Predicate::False {
                   debug!("Retain continuation {}", c.id);
                   true
               }
               else {
                   debug!("Continuation is unreachable:\n{c}");
                   false
               }
           })
           .collect();

        // assert that there are no dups
        let mut ids = HashSet::new();
        for cont in filtered_conts.iter() {
            if ids.contains(&cont.id) {
                panic!("Duplicate continuation: {}", &cont.id);
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
                    || c.map_state != cont.map_state
                    || c.map_tombstones != cont.map_tombstones
                    || c.post_vars != cont.post_vars
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
                let children_count = *children_counts.get(&parent_id).expect("Unreachable");
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

        filtered_conts
    }

    fn eval_variadic_native<I, F>(&self, continuation: Continuation, function_name: &str, args: &[SymbolicExpression], initial: I, fold: F) -> Result<Vec<Continuation>, Error> 
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
                    let mut conts = self.eval(Continuation::from_parent(Rc::new(left_cont), function_name.to_string(), symexp.span.start_line), symexp)?;
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
                left_conts_opt = Some(Self::reduce_continuations(right_conts));
            }
            else {
                let mut conts = self.eval(Continuation::from_parent(continuation_rc.clone(), function_name.to_string(), symexp.span.start_line), symexp)?;
                for cont in conts.iter_mut() {
                    if cont.halted() {
                        continue;
                    }
                    cont.final_formula = initial(cont.final_formula.clone()).simplify()?;
                }
                left_conts_opt = Some(Self::reduce_continuations(conts));
            }
        }
        let Some(conts) = left_conts_opt.take() else {
            return Err(Error::Bug(format!("No continuations produced from {args:?}")));
        };
        Ok(Self::reduce_continuations(conts))
    }

    /// eval_variadic_native, but where the initial constructor is an identity
    fn eval_foldable_native<F>(&self, continuation: Continuation, function_name: &str, args: &[SymbolicExpression], fold: F) -> Result<Vec<Continuation>, Error> 
    where
        F: Fn(SymOp, SymOp) -> SymOp
    {
        self.eval_variadic_native(continuation, function_name, args, |initial| initial, fold)
    }

    fn eval_native_1arg<C>(&self, continuation: Continuation, function_name: &str, arg: SymbolicExpression, cons: C) -> Result<Vec<Continuation>, Error>
    where
        C: Fn(SymOp) -> SymOp
    {
        self.eval_variadic_native(continuation, function_name, &[arg], cons, |_, _| unreachable!())
    }
    
    fn eval_native_2args<C>(&self, continuation: Continuation, function_name: &str, arg1: SymbolicExpression, arg2: SymbolicExpression, cons: C) -> Result<Vec<Continuation>, Error>
    where
        C: Fn(SymOp, SymOp) -> SymOp
    {
        self.eval_variadic_native(continuation, function_name, &[arg1, arg2], |initial| initial, cons)
    }
    
    fn eval_native_3args<C>(&self, continuation: Continuation, function_name: &str, arg1: SymbolicExpression, arg2: SymbolicExpression, arg3: SymbolicExpression, cons: C) -> Result<Vec<Continuation>, Error>
    where
        C: Fn(SymOp, SymOp, SymOp) -> SymOp
    {
        let parent_func = continuation.current_function.clone().unwrap_or("".to_string());
        let parent_rc = Rc::new(continuation);
        let function_name = format!("{parent_func}/{function_name}");

        // first arg
        let conts_1 = self.eval(Continuation::from_parent(parent_rc, function_name.to_string(), arg1.span.start_line), &arg1)?;
        
        // second arg
        let mut conts_2 = vec![];
        for cont in conts_1.into_iter() {
            if cont.halted() {
                conts_2.push(((cont.final_formula.clone(), cont.predicate.clone()), cont));
                continue;
            }
            let form1 = cont.final_formula.clone();
            let pred1 = cont.predicate.clone();
            let cont_rc = Rc::new(cont);

            let next = self.eval(Continuation::from_parent(cont_rc, function_name.to_string(), arg2.span.start_line), &arg2)?;
            conts_2.extend(next.into_iter().map(|c| ((form1.clone(), pred1.clone()), c)));
        }

        // third arg
        let mut conts_3 = vec![];
        for ((form1, pred1), mut cont) in conts_2.into_iter() {
            if cont.halted() {
                conts_3.push((cont.final_formula.clone(), (cont.final_formula.clone(), cont.predicate.clone()), cont));
                continue;
            }
            let form2 = cont.final_formula.clone();
            let pred2 = cont.predicate.clone();

            cont.predicate = pred1.and(pred2.clone());
            let cont_rc = Rc::new(cont);

            let next = self.eval(Continuation::from_parent(cont_rc, function_name.to_string(), arg3.span.start_line), &arg3)?;
            conts_3.extend(next.into_iter().map(|c| (form1.clone(), (form2.clone(), pred2.clone()), c)));
        }

        // construct final formulae and predicates
        let mut ret = vec![];
        for (form1, (form2, pred2), mut cont3) in conts_3.into_iter() {
            if cont3.halted() {
                ret.push(cont3);
                continue;
            }
            let pred3 = cont3.predicate.clone();
            let final_formula = cons(form1, form2, cont3.final_formula.clone());
            let predicate = pred2.and(pred3);

            cont3.final_formula = final_formula;
            cont3.predicate = predicate;

            ret.push(cont3);
        }
        
        Ok(ret)
    }

    pub fn eval(&self, mut continuation: Continuation, body: &SymbolicExpression) -> Result<Vec<Continuation>, Error> {
        if continuation.halted() {
            return Ok(vec![continuation]);
        }
        debug!("Simplify continuation {} predicate {}", continuation.id, &continuation.predicate);
        let pred = continuation.predicate.clone().simplify()?;
        if pred == Predicate::False {
            // this is unreachable anyway
            return Ok(vec![]);
        }
        info!("Evaluating continuation {}\n   function name: {}\n            body: {}\n       predicate: {}\n", continuation.id, &continuation.current_function.as_ref().map(|s| s.as_str()).unwrap_or(""), &body.expr, &pred);
        if continuation.id <= last_cont_id() {
            return Err(Error::Bug(format!("Tried to evaluate a continuation twice: {}", continuation.id)));
        }
        set_last_cont_id(continuation.id);

        let continuations = match &body.expr {
            SymbolicExpressionType::LiteralValue(v) => {
                let parent_func = continuation.current_function.clone().unwrap_or("".to_string());
                let function_name = format!("{parent_func}.{}", &v);
                continuation.current_function = Some(function_name);
                continuation.final_formula = SymOp::Constant(v.clone());
                vec![continuation]
            }
            SymbolicExpressionType::List(lv) => {
                if let Some(first) = lv.first() {
                    if let Some(function_base_name) = first.match_atom() {
                        let parent_func = continuation.current_function.clone().unwrap_or("".to_string());
                        let function_name = format!("{parent_func}.{}", &function_base_name);
                        let fq_name = CallableName(continuation.get_current_contract_id(), function_base_name.clone());
                        if let Some(func) = self.contract_context.functions.get(function_base_name) {
                            // can we skip this, or shorten our consideration?
                            let is_pure = self.callgraph.is_pure(&fq_name)?;
                            let is_causally_independent = continuation.is_causally_independent(&fq_name, &self.callgraph)?;
                            if !self.explore_function_calls
                                || self.skip_function_calls.contains(function_base_name)
                                || (is_pure && self.skip_pure_calls)
                                || (is_causally_independent && self.skip_causally_independent_calls)
                            {
                                if is_pure && self.skip_pure_calls {
                                    info!("Will not evaluate function {fq_name} from continuation {}, since it is pure", continuation.id);
                                }
                                if is_causally_independent && self.skip_causally_independent_calls {
                                    info!("Will not evaluate function {fq_name} from continuation {}, since it is causally independent", continuation.id);
                                }

                                // skip this; treat this function call as a symbol
                                let parent_rc = Rc::new(continuation);
                                let skip_cont = Continuation::from_parent(parent_rc, format!("{function_name}/skipped"), body.span.start_line);
                                let mut skip_conts = vec![vec![(skip_cont, vec![])]];
                                for (i, arg) in lv.get(1..).unwrap_or(&[]).iter().enumerate() {
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
                                            let next_conts = self.eval(Continuation::from_parent(Rc::new(skip_cont), format!("{function_name}/skipped/arg[{i}]"), arg.span.start_line), arg)?;
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
                                let mut final_conts = vec![];
                                for skip_cont_set in skip_conts.into_iter() {
                                    for (skip_cont, args) in skip_cont_set.into_iter() {
                                        let mut final_cont = Continuation::from_parent(Rc::new(skip_cont), format!("{function_name}/skipped/return"), body.span.start_line);
                                        final_cont.add_reachable_storage_accesses(&fq_name, &self.callgraph)?;
                                        final_cont.final_formula = SymOp::FunctionCall(function_base_name.clone(), args);
                                        final_conts.push(final_cont);
                                    }
                                }
                                return Ok(Self::reduce_continuations(final_conts));
                            }
                            else if let Some(conts) = self.evaluated_functions.get(&fq_name) {
                                // going to evaluate a pre-evaluated function.
                                // bind each bound formula in this continuation to the simplified
                                // final formula and simplified final predicate.
                                let mut evaled_conts = vec![vec![(continuation, vec![])]];
                                let mut final_conts = vec![];
                                for (i, arg) in lv.get(1..).unwrap_or(&[]).iter().enumerate() {
                                    let mut next_evaled_conts = vec![];
                                    for evaled_cont_set in evaled_conts.into_iter() {
                                        let mut next_evaled_cont_set = vec![];
                                        for (evaled_cont, args_so_far) in evaled_cont_set.into_iter() {
                                            if evaled_cont.halted() {
                                                final_conts.push(evaled_cont);
                                                continue;
                                            }
                                            let next_conts = self.eval(Continuation::from_parent(Rc::new(evaled_cont), format!("{function_name}/evaled/arg[{i}]"), arg.span.start_line), arg)?;
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
                                for evaled_cont_set in evaled_conts.into_iter() {
                                    for (evaled_cont, args) in evaled_cont_set.into_iter() {
                                        if evaled_cont.halted() {
                                            final_conts.push(evaled_cont);
                                            continue;
                                        }
                                        if args.len() != func.arguments.len() {
                                            return Err(Error::Bug(format!("Computed arguments ({}) does not match function type signature ({})", args.len(), func.arguments.len())));
                                        }

                                        let mut binding_cont = Continuation::from_parent(Rc::new(evaled_cont), format!("{function_name}/evaled/bind"), body.span.start_line);
                                        // NOTE: no need to unbind these symbols later, since the
                                        // continuation produced by Continuation::from_evaluated()
                                        // will not have any bound formulae (its final formula,
                                        // predicate, and state will instead have their free
                                        // variables bound to symops in the binding continuation)
                                        for (arg_name, arg_symop) in func.arguments.iter().zip(args.iter()) {
                                            binding_cont.bind_symop(arg_name, (*arg_symop.clone()).simplify()?);
                                        }

                                        let binding_cont_id = binding_cont.id;
                                        let binding_cont_rc = Rc::new(binding_cont);
                                        let mut pushed = 0;
                                        for cont in conts.iter() {
                                            let eval_cont = Continuation::from_evaluated(cont, format!("{function_name}/evaled"), binding_cont_rc.clone())?;
                                            if self.skip_causally_independent_calls && binding_cont_rc.is_read_independent(&eval_cont)? && cont.is_read_only_so_far() {
                                                info!("Will not evaluate function {fq_name} continuation {}, since it is causally read-independent of continuation {}", cont.id, binding_cont_rc.id);
                                                continue;
                                            }

                                            let return_cont = Continuation::from_callee(Rc::new(eval_cont), format!("{function_name}/evaled/return"), func.body.span.start_line);
                                            final_conts.push(return_cont);
                                            pushed += 1;
                                        }
                                        if pushed == 0 {
                                            // all continuations are read-independent of the
                                            // binding continuation, so we can skip
                                            info!("All continuations of {fq_name} are read-independent of continuation {}", binding_cont_id);
                                            let mut final_cont = Continuation::from_parent(binding_cont_rc, format!("{function_name}/eval-skipped/return"), body.span.start_line);
                                            final_cont.add_reachable_storage_accesses(&fq_name, &self.callgraph)?;
                                            final_cont.final_formula = SymOp::FunctionCall(function_base_name.clone(), args);
                                            final_conts.push(final_cont);
                                        }
                                    }
                                }

                                return Ok(Self::reduce_continuations(final_conts));
                            }
                            else {
                                self.apply_user_function(continuation, function_base_name, lv.get(1..).unwrap_or(&[]))?
                            }
                        }
                        else {
                            // native function application
                            match function_base_name.as_str() {
                                "+" => {
                                    self.eval_foldable_native(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1..).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?,
                                        |left, right| left.add(right)
                                    )?
                                }
                                "-" => {
                                    self.eval_foldable_native(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1..).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?,
                                        |left, right| left.subtract(right)
                                    )?
                                }
                                "*" => {
                                    self.eval_foldable_native(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1..).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?,
                                        |left, right| left.multiply(right)
                                    )?
                                }
                                "/" => {
                                    self.eval_foldable_native(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1..).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?,
                                        |left, right| left.divide(right)
                                    )?
                                }
                                ">=" => {
                                    self.eval_native_2args(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing argument 1 to {function_name}")))?.clone(),
                                        lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.clone(),
                                        |left, right| SymOp::Geq(Box::new(left), Box::new(right))
                                    )?
                                }
                                "<=" => {
                                    self.eval_native_2args(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing argument 1 to {function_name}")))?.clone(),
                                        lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.clone(),
                                        |left, right| SymOp::Leq(Box::new(left), Box::new(right))
                                    )?
                                }
                                "<" => {
                                    self.eval_native_2args(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing argument 1 to {function_name}")))?.clone(),
                                        lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.clone(),
                                        |left, right| SymOp::Less(Box::new(left), Box::new(right))
                                    )?
                                }
                                ">" => {
                                    self.eval_native_2args(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing argument 1 to {function_name}")))?.clone(),
                                        lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.clone(),
                                        |left, right| SymOp::Greater(Box::new(left), Box::new(right))
                                    )?
                                }
                                "to-int" => {
                                    self.eval_native_1arg(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::ToInt(Box::new(initial))
                                    )?
                                }
                                "to-uint" => {
                                    self.eval_native_1arg(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::ToUInt(Box::new(initial))
                                    )?
                                }
                                "mod" => {
                                    self.eval_native_2args(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing argument 1 to {function_name}")))?.clone(),
                                        lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.clone(),
                                        |left, right| SymOp::Modulo(Box::new(left), Box::new(right))
                                    )?
                                }
                                "pow" => {
                                    self.eval_native_2args(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing argument 1 to {function_name}")))?.clone(),
                                        lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.clone(),
                                        |left, right| SymOp::Power(Box::new(left), Box::new(right))
                                    )?
                                }
                                "sqrti" => {
                                    self.eval_native_1arg(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::Sqrti(Box::new(initial))
                                    )?
                                }
                                "log2" => {
                                    self.eval_native_1arg(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::Log2(Box::new(initial))
                                    )?
                                }
                                "bit-xor" => {
                                    self.eval_foldable_native(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1..).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?,
                                        |left, right| left.bitwise_xor(right)
                                    )?
                                }
                                "and" => {
                                    self.eval_foldable_native(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1..).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?,
                                        |left, right| left.and(right)
                                    )?
                                }
                                "or" => {
                                    self.eval_foldable_native(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1..).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?,
                                        |left, right| left.or(right)
                                    )?
                                }
                                "not" => {
                                    self.eval_native_1arg(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::Not(Box::new(initial))
                                    )?
                                }
                                "is-eq" => {
                                    self.eval_variadic_native(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1..).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?,
                                        |initial| initial,
                                        |left, right| left.equals(right)
                                    )?
                                }
                                "if" => {
                                    self.eval_if(
                                        continuation,
                                        lv.get(1).ok_or_else(|| Error::Bug("Missing if-predicate".into()))?.clone(),
                                        lv.get(2).ok_or_else(|| Error::Bug("Missing if-true branch".into()))?.clone(),
                                        lv.get(3).ok_or_else(|| Error::Bug("Missing if-else branch".into()))?.clone(),
                                    )?
                                }
                                "let" => {
                                    self.let_bind(continuation, lv.get(1..).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?)?
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
                                        let sz = if let Some(ts) = self.typemap.get_type_expected(s) {
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

                                            let conts = self.eval(Continuation::from_parent(Rc::new(last_cont), format!("{function_name}/map/seq-{i}"), seq.span.start_line), seq)?;
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
                                                    let mut empty_cont = Continuation::from_parent(Rc::new(cont.clone()), format!("{function_name}/{func_name}/seq-{seq_i}/empty-case"), parent_start_line);
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
                                                if let Some(func) = self.contract_context.functions.get(func_name) {
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
                                                        let mut binding_cont = Continuation::from_parent(Rc::new(caller_cont), format!("{function_name}/{func_name}/seq-{seq_i}/binding"), func.body.span.start_line);

                                                        let mut bound = vec![];
                                                        for (arg_name, elem_i) in func.arguments.iter().zip(elems_i.iter()) {
                                                            binding_cont.bind_symop(arg_name, elem_i.clone().simplify()?);
                                                            bound.push(arg_name.clone());
                                                        }

                                                        let callee_cont = Continuation::from_caller(Rc::new(binding_cont), format!("{function_name}/{func_name}/seq-{seq_i}/body"), func.body.span.start_line);
                                                        let conts = self.eval(callee_cont, &func.body)?;

                                                        let conts : Vec<_> = conts
                                                            .into_iter()
                                                            .map(|cont| {
                                                                if cont.panicking {
                                                                    return cont;
                                                                }
                                                                let mut return_cont = Continuation::from_callee(Rc::new(cont), format!("{function_name}/{func_name}/seq-{seq_i}/return"), func.body.span.start_line);
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
                                            let pred = list_cons_preds.get(&key).expect("unreachable");
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
                                    
                                    let seq_maxlen = if let Some(ts) = self.typemap.get_type_expected(sequence) {
                                        Self::sequence_maxlen(ts)?
                                    }
                                    else {
                                        return Err(Error::Bug(format!("No type information for sequence {sequence:?}")));
                                    };

                                    let mut ret = vec![];
                                    let conts = self.eval(Continuation::from_parent(Rc::new(continuation), format!("{function_name}/sequence"), sequence.span.start_line), &sequence)?;

                                    let mut initial_conts = vec![];
                                    for cont in conts.into_iter() {
                                        if cont.halted() {
                                            ret.push(cont);
                                            continue;
                                        }
                                        let seq_formula = cont.final_formula.clone().simplify()?;
                                        let initial_value_conts = self.eval(Continuation::from_parent(Rc::new(cont), format!("{function_name}/initial_value"), initial_value.span.start_line), &initial_value)?;
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
                                                        ret.push(cont);
                                                        continue;
                                                    }
                                                    if let Some(func) = self.contract_context.functions.get(func_name) {
                                                        // user-defined function
                                                        if func.arguments.len() != 2 {
                                                            return Err(Error::Bug(format!("Function `{func_name}` takes {} arguments but expected 2 arguments", func.arguments.len())));
                                                        }
                                                        let value_formula = cont.final_formula.clone();
                                                        let mut binding_cont = Continuation::from_parent(Rc::new(cont), format!("{function_name}/{func_name}/seq-{seq_i}-of-({cont_i}-of-{cont_set_len})-of-({cont_set_i}-of-{cont_set_set_len})/binding"), func.body.span.start_line);
                                                        
                                                        binding_cont.bind_symop(&func.arguments[0], SymOp::UnwrapPanic(Box::new(SymOp::ElementAt(Box::new(seq_formula.clone()), Box::new(SymOp::Constant(Value::UInt(seq_i - 1)))))).simplify()?);
                                                        binding_cont.bind_symop(&func.arguments[1], value_formula.simplify()?);
                                                        let bound = vec![func.arguments[0].clone(), func.arguments[1].clone()];

                                                        let callee_cont = Continuation::from_caller(Rc::new(binding_cont), format!("{function_name}/{func_name}/seq-{seq_i}-of-({cont_i}-of-{cont_set_len})-of-({cont_set_i}-of-{cont_set_set_len})/body"), func.body.span.start_line);
                                                        let body_conts : Vec<_> = self.eval(callee_cont, &func.body)?
                                                            .into_iter()
                                                            .map(|cont| {
                                                                if cont.panicking {
                                                                    return (len_eq_i.clone(), cont);
                                                                }
                                                                let mut return_cont = Continuation::from_callee(Rc::new(cont), format!("{function_name}/{func_name}/seq-{seq_i}-of-({cont_i}-of-{cont_set_len})-of-({cont_set_i}-of-{cont_set_set_len})/return"), func.body.span.start_line);
                                                                
                                                                for unbind in bound.iter() {
                                                                    return_cont.unbind(unbind);
                                                                }
                                                                (len_eq_i.clone(), return_cont)
                                                            })
                                                            .collect();

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
                                                ret.push(cont);
                                            }
                                        }
                                    }

                                    ret
                                },
                                "append" => {
                                    self.eval_native_2args(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing argument 1 to {function_name}")))?.clone(),
                                        lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.clone(),
                                        |left, right| SymOp::Append(Box::new(left), Box::new(right))
                                    )?
                                }
                                "concat" => {
                                    self.eval_native_2args(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing argument 1 to {function_name}")))?.clone(),
                                        lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.clone(),
                                        |left, right| SymOp::Concat(Box::new(left), Box::new(right))
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
                                    let mut len_cont = self.eval(Continuation::from_parent(Rc::new(continuation), format!("{function_name}/max-len"), new_len_sym.span.start_line), &new_len_sym)?; 
                                    if len_cont.len() != 1 {
                                        return Err(Error::Bug(format!("as-max-len? length evaluation had {} continuation(s); expected 1. Symexp was {}", len_cont.len(), &new_len_sym)));
                                    }
                                    let Some(len_cont) = len_cont.pop() else {
                                        return Err(Error::Bug("unreachable".into()));
                                    };

                                    let SymOp::Constant(Value::UInt(x)) = len_cont.final_formula else {
                                        return Err(Error::Bug("as-max-len? length evalauation was not a uint constant".into()));
                                    };

                                    // now we can evaluate the list
                                    let list_conts = self.eval(Continuation::from_parent(Rc::new(len_cont), format!("{function_name}/list"), list_sym.span.start_line), &list_sym)?;

                                    // if y is greater than or equal to the maximum length of x,
                                    // then this will always succeed
                                    let sz = if let Some(ts) = self.typemap.get_type_expected(&list_sym) {
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
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::Len(Box::new(initial))
                                    )?
                                },
                                "element-at?" | "element-at" => {
                                    self.eval_native_2args(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing argument 1 to {function_name}")))?.clone(),
                                        lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.clone(),
                                        |left, right| SymOp::ElementAt(Box::new(left), Box::new(right))
                                    )?
                                }
                                "index-of" | "index-of?" => {
                                    self.eval_native_2args(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing argument 1 to {function_name}")))?.clone(),
                                        lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.clone(),
                                        |left, right| SymOp::IndexOf(Box::new(left), Box::new(right))
                                    )?
                                }
                                "buff-to-int-le" => {
                                    self.eval_native_1arg(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::BuffToIntLe(Box::new(initial))
                                    )?
                                }
                                "buff-to-uint-le" => {
                                    self.eval_native_1arg(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::BuffToUIntLe(Box::new(initial))
                                    )?
                                }
                                "buff-to-int-be" => {
                                    self.eval_native_1arg(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::BuffToIntBe(Box::new(initial))
                                    )?
                                }
                                "buff-to-uint-be" => {
                                    self.eval_native_1arg(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::BuffToUIntBe(Box::new(initial))
                                    )?
                                }
                                "is-standard" => {
                                    self.eval_native_1arg(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::IsStandard(Box::new(initial))
                                    )?
                                }
                                "principal-destruct?" => {
                                    self.eval_native_1arg(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::PrincipalDestruct(Box::new(initial))
                                    )?
                                }
                                "principal-construct?" => {
                                    if lv.len() == 3 {
                                        self.eval_native_2args(
                                            continuation,
                                            function_name.as_str(),
                                            lv.get(1).ok_or_else(|| Error::Bug(format!("Missing argument 1 to {function_name}")))?.clone(),
                                            lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.clone(),
                                            |op1, op2| SymOp::PrincipalConstruct(Box::new(op1), Box::new(op2), None)
                                        )?
                                    }
                                    else if lv.len() == 4 {
                                        self.eval_native_3args(
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
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::StringToInt(Box::new(initial))
                                    )?
                                }
                                "string-to-uint?" => {
                                    self.eval_native_1arg(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::StringToUInt(Box::new(initial))
                                    )?
                                }
                                "int-to-ascii" => {
                                    self.eval_native_1arg(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::IntToAscii(Box::new(initial))
                                    )?
                                }
                                "int-to-utf8" => {
                                    self.eval_native_1arg(
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

                                    continuation.read_data_var(var_name.clone(), formula.clone(), body.span.start_line);
                                    continuation.final_formula = SymOp::LoadedDataVariable(var_name.clone(), Box::new(formula.clone()));
                                    vec![continuation]
                                },
                                "var-set" => {
                                    let var_name_expr = lv.get(1).ok_or_else(|| Error::Bug("Missing variable name".into()))?;
                                    let var_val_expr = lv.get(2).ok_or_else(|| Error::Bug("Missing variable value".into()))?;

                                    let Some(var_name) = var_name_expr.match_atom() else {
                                        return Err(Error::Bug(format!("Variable name '{:?}' is not an atom", &var_name_expr)));
                                    };

                                    let mut conts = self.eval(Continuation::from_parent(Rc::new(continuation), format!("{function_name}/var-valure"), var_val_expr.span.start_line), var_val_expr)?;
                                    for cont in conts.iter_mut() {
                                        if cont.halted() {
                                            continue;
                                        }
                                        cont.set_post_data_var(var_name, cont.final_formula.clone().simplify()?);

                                        // (var-set ..) always evals to True
                                        cont.final_formula = SymOp::True();

                                        debug!("var-set cont:\n{}", &cont);
                                    }
                                    conts
                                },
                                "map-get?" => {
                                    let Some(map_name) = lv.get(1).ok_or_else(|| Error::Bug("Missing map name".into()))?.match_atom() else {
                                        return Err(Error::Bug("Map name is not an atom".into()));
                                    };
                                    let key_symexp = lv.get(2).ok_or_else(|| Error::Bug("Missing key expr".into()))?;

                                    let mut key_conts = self.eval(Continuation::from_parent(Rc::new(continuation), format!("{function_name}.{map_name}"), key_symexp.span.start_line), key_symexp)?;

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
                                        if value.is_none() {
                                            if cont.is_map_deleted(map_name, &key_formula) {
                                                // this value was definitely deleted
                                                cont.final_formula = SymOp::Constant(Value::none());
                                            }
                                            else {
                                                cont.read_map_entry(map_name.clone(), key_formula.clone(), value.clone().map(|op| *op), body.span.start_line); 
                                                cont.final_formula = SymOp::LoadedMapEntry(map_name.clone(), Box::new(key_formula), value);
                                            }
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
                                   
                                    let key_conts = self.eval(Continuation::from_parent(Rc::new(continuation), format!("{function_name}/key"), key_symexp.span.start_line), key_symexp)?;

                                    let mut final_conts = vec![];
                                    let mut val_cont_sets = vec![];
                                    for cont in key_conts.into_iter() {
                                        if cont.halted() {
                                            final_conts.push(cont);
                                            continue;
                                        }

                                        let key_formula = cont.final_formula.clone().simplify()?;
                                        let parent_rc = Continuation::from_parent(Rc::new(cont), format!("{function_name}/value"), val_symexp.span.start_line);
                                        let val_conts = self.eval(parent_rc, val_symexp)?;
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
                                   
                                    let key_conts = self.eval(Continuation::from_parent(Rc::new(continuation), format!("{function_name}/key"), key_symexp.span.start_line), key_symexp)?;

                                    let mut final_conts = vec![];
                                    let mut val_cont_sets = vec![];
                                    for cont in key_conts.into_iter() {
                                        if cont.halted() {
                                            final_conts.push(cont);
                                            continue;
                                        }

                                        let key_formula = cont.final_formula.clone().simplify()?;
                                        let parent_rc = Continuation::from_parent(Rc::new(cont), format!("{function_name}/value"), val_symexp.span.start_line);
                                        let val_conts = self.eval(parent_rc, val_symexp)?;
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

                                            let entry = SymOp::LoadedMapEntry(map_name.clone(), Box::new(key_formula.clone()), None);

                                            let mut cont_present = Continuation::from_parent(parent.clone(), format!("{function_name}/present"), body.span.start_line);
                                            cont_present.predicate = parent_pred.clone()
                                                .and(SymOp::IsSome(Box::new(entry.clone())).try_as_predicate()?);

                                            cont_present.final_formula = SymOp::False();

                                            let mut cont_absent = Continuation::from_parent(parent.clone(), format!("{function_name}/absent"), body.span.start_line);
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

                                    let key_conts = self.eval(Continuation::from_parent(Rc::new(continuation), format!("{function_name}"), key_symexp.span.start_line), key_symexp)?;

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
                                            cont.final_formula = SymOp::True();
                                            final_conts.push(cont);
                                            continue;
                                        }

                                        // this may be true or false, so account for both
                                        let parent_pred = cont.predicate.clone().simplify()?;
                                        let parent = Rc::new(cont);

                                        let entry = SymOp::LoadedMapEntry(map_name.clone(), Box::new(key_formula.clone().simplify()?), None);

                                        let mut cont_present = Continuation::from_parent(parent.clone(), format!("{function_name}/present"), body.span.start_line);
                                        cont_present.predicate = parent_pred.clone()
                                            .and(SymOp::IsSome(Box::new(entry.clone())).try_as_predicate()?);

                                        cont_present.final_formula = SymOp::True();

                                        let mut cont_absent = Continuation::from_parent(parent.clone(), format!("{function_name}/absent"), body.span.start_line);
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
                                        let Some(key_value_list) = lv.get(i).ok_or_else(|| Error::Bug("unreachable".into()))?.match_list() else {
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
                                            let next = self.eval(Continuation::from_parent(parent_rc, format!("{function_name}/tuple-item-{i}"), value_exp.span.start_line), value_exp)?;

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

                                   let mut conts = self.eval(Continuation::from_parent(Rc::new(continuation), format!("{function_name}/tuple-get"), sym.span.start_line), sym)?;
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

                                   let dest_conts = self.eval(Continuation::from_parent(Rc::new(continuation), format!("{function_name}/tuple-merge-dest"), dest_tuple.span.start_line), dest_tuple)?;
                                   let mut src_conts = vec![];
                                   for dest_cont in dest_conts.into_iter() {
                                       if dest_cont.halted() {
                                           src_conts.push(dest_cont);
                                           continue;
                                       }

                                       let dest_formula = dest_cont.final_formula.clone();
                                       let dest_pred = dest_cont.predicate.clone();

                                       let mut next_conts = self.eval(Continuation::from_parent(Rc::new(dest_cont), format!("{function_name}/tuple-merge-src"), src_tuple.span.start_line), src_tuple)?;

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
                                "begin" => {
                                    let mut ret = vec![];
                                    let mut conts = vec![vec![continuation]];
                                    for (i, symexp) in lv.get(1..).ok_or_else(|| Error::Bug("Missing symbolic expressions for (begin ..)".into()))?.iter().enumerate() {
                                        let mut new_conts = vec![];
                                        for cont_set in conts.into_iter() {
                                            for cont in cont_set.into_iter() {
                                                if cont.halted() {
                                                    ret.push(cont);
                                                    continue;
                                                }
                                                let next_conts = self.eval(Continuation::from_parent(Rc::new(cont), format!("{function_name}/expr[{i}]"), symexp.span.start_line), symexp)?;
                                                new_conts.push(next_conts);
                                            }
                                        }
                                        conts = new_conts;
                                    }
                                    for cont_set in conts.into_iter() {
                                        ret.extend(cont_set.into_iter());
                                    }
                                    ret
                                }
                                "hash160" => {
                                    self.eval_native_1arg(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::Hash160(Box::new(initial))
                                    )?
                                }
                                "sha256" => {
                                    self.eval_native_1arg(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::Sha256(Box::new(initial))
                                    )?
                                }
                                "sha512" => {
                                    self.eval_native_1arg(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::Sha512(Box::new(initial))
                                    )?
                                }
                                "sha512/256" => {
                                    self.eval_native_1arg(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::Sha512Trunc256(Box::new(initial))
                                    )?
                                }
                                "keccak256" => {
                                    self.eval_native_1arg(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::Keccak256(Box::new(initial))
                                    )?
                                }
                                "secp256k1-recover?" => {
                                    self.eval_native_2args(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing argument 1 to {function_name}")))?.clone(),
                                        lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.clone(),
                                        |op1, op2| SymOp::Secp256k1Recover(Box::new(op1), Box::new(op2))
                                    )?
                                }
                                "secp256k1-verify" => {
                                    self.eval_native_3args(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing argument 1 to {function_name}")))?.clone(),
                                        lv.get(2).ok_or_else(|| Error::Bug(format!("Missing argument 2 to {function_name}")))?.clone(),
                                        lv.get(3).ok_or_else(|| Error::Bug(format!("Missing argument 3 to {function_name}")))?.clone(),
                                        |op1, op2, op3| SymOp::Secp256k1Verify(Box::new(op1), Box::new(op2), Box::new(op3))
                                    )?
                                }
                                "print" => {
                                    todo!()
                                }
                                "contract-call?" => {
                                    todo!()
                                }
                                "as-contract" => {
                                    return Err(Error::Bug("`as-contract` is deprecated and not supported by this tool".into()));
                                }
                                "contract-of" => {
                                    self.eval_native_1arg(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::ContractOf(Box::new(initial))
                                    )?
                                }
                                "get-burn-block-info?" => {
                                    todo!()
                                }
                                "err" => {
                                    self.eval_native_1arg(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::ConsError(Box::new(initial))
                                    )?
                                }
                                "ok" => {
                                    self.eval_native_1arg(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::ConsOkay(Box::new(initial))
                                    )?
                                }
                                "some" => {
                                    self.eval_native_1arg(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::ConsSome(Box::new(initial))
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
                                    let default_conts = self.eval(Continuation::from_parent(Rc::new(continuation), format!("{function_name}/default"), default_sym.span.start_line), &default_sym)?;
                                    for default_cont in default_conts.into_iter() {
                                        if default_cont.halted() {
                                            new_conts.push(default_cont);
                                            continue;
                                        }

                                        let default_final_formula = default_cont.final_formula.clone();
                                        let parent_rc = Rc::new(default_cont);

                                        // evaluate `y` for this `x`'s continuation
                                        let opt_conts = self.eval(Continuation::from_parent(parent_rc, format!("{function_name}/optional"), opt_sym.span.start_line), &opt_sym)?;
                                        for opt_cont in opt_conts.into_iter() {
                                            if opt_cont.halted() {
                                                new_conts.push(opt_cont);
                                                continue;
                                            }
                                            let parent_predicate = opt_cont.predicate.clone();
                                            let final_formula = opt_cont.final_formula.clone();
                                            let parent_rc = Rc::new(opt_cont);

                                            // case 1: this is (some ..)
                                            let mut some_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}/optional/is-some"), opt_sym.span.start_line);
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
                                    let cond_conts = self.eval(Continuation::from_parent(Rc::new(continuation), format!("{function_name}/cond-eval"), cond_sym.span.start_line), &cond_sym)?;
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
                                        let mut cont_true = Continuation::from_parent(cont_rc.clone(), format!("{function_name}/assert-is-true"), cond_sym.span.start_line);
                                        cont_true.predicate = cond_pred.clone().and(cond_formula.clone().try_as_predicate()?).simplify()?;
                                        cont_true.final_formula = SymOp::True();

                                        if cont_true.predicate != Predicate::False {
                                            new_conts.push(cont_true);
                                        }

                                        let mut cond_false = Continuation::from_parent(cont_rc, format!("{function_name}/assert-is-false"), err_sym.span.start_line);
                                        cond_false.predicate = cond_pred.clone().and(cond_formula.clone().try_as_predicate()?.not().simplify()?).simplify()?;
                                        if cond_false.predicate == Predicate::False {
                                            continue;
                                        }

                                        // case 2: `x` is false.
                                        // evaluate `y`, and set all of its continuations as
                                        // early-return.
                                        let err_conts = self.eval(cond_false, &err_sym)?;
                                        for mut err_cont in err_conts.into_iter() {
                                            if err_cont.halted() {
                                                new_conts.push(err_cont);
                                                continue;
                                            }

                                            debug!("Continuation {} is early-return", err_cont.id);
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
                                    let cond_conts = self.eval(Continuation::from_parent(Rc::new(continuation), format!("{function_name}/cond-eval"), cond_sym.span.start_line), &cond_sym)?;

                                    // evaluate `y` from each `x`
                                    for cond_cont in cond_conts.into_iter() {
                                        if cond_cont.halted() {
                                            new_conts.push(cond_cont);
                                            continue;
                                        }

                                        let cond_formula = cond_cont.final_formula.clone();

                                        let parent_rc = Rc::new(cond_cont);
                                        let err_conts = self.eval(Continuation::from_parent(parent_rc, format!("{function_name}/err-eval"), err_sym.span.start_line), &err_sym)?;

                                        for parent_cont in err_conts.into_iter() {
                                            if parent_cont.halted() {
                                                new_conts.push(parent_cont);
                                                continue;
                                            }

                                            let cond_predicate = parent_cont.predicate.clone();
                                            let parent_rc = Rc::new(parent_cont);

                                            // case 1: `(is-ok x)` is true or `(is-some x)` is true
                                            let mut ok_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}/cond-true"), cond_sym.span.start_line);
                                            ok_cont.predicate = match self.typemap.get_type_expected(&cond_sym) {
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

                                            let mut err_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}/cond-false"), err_sym.span.start_line);
                                            // case 2: (is-ok x) (or (is-some x)) is false
                                            err_cont.predicate = match self.typemap.get_type_expected(&cond_sym) {
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

                                            debug!("Continuation {} is early-return", err_cont.id);
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
                                    let cond_conts = self.eval(Continuation::from_parent(Rc::new(continuation), format!("{function_name}/cond-eval"), cond_sym.span.start_line), &cond_sym)?;

                                    // evaluate `y` from each `x`
                                    for cond_cont in cond_conts.into_iter() {
                                        if cond_cont.halted() {
                                            new_conts.push(cond_cont);
                                            continue;
                                        }
                                        let cond_formula = cond_cont.final_formula.clone();

                                        let parent_rc = Rc::new(cond_cont);
                                        let err_conts = self.eval(Continuation::from_parent(parent_rc, format!("{function_name}.err-eval"), err_sym.span.start_line), &err_sym)?;

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
                                            
                                            debug!("Continuation {} is early-return", err_cont.id);
                                            err_cont.early_return = true;

                                            new_conts.push(is_err_cont);
                                            new_conts.push(err_cont);
                                        }
                                    }

                                    new_conts
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
                                    let cond_conts = self.eval(Continuation::from_parent(Rc::new(continuation), format!("{function_name}/cond"), cond_sym.span.start_line), &cond_sym)?;

                                    for cond_cont in cond_conts.into_iter() {
                                        if cond_cont.halted() {
                                            new_conts.push(cond_cont);
                                            continue;
                                        }

                                        let cond_formula = cond_cont.final_formula.clone();
                                        let cond_predicate = cond_cont.predicate.clone();
                                        let parent_rc = Rc::new(cond_cont);

                                        // case 1: `(is-ok x)` is true or `(is-some x)` is true
                                        let mut ok_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}/unwrap-success"), cond_sym.span.start_line);
                                        ok_cont.predicate = match self.typemap.get_type_expected(&cond_sym) {
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
                                        let mut panic_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}/unwrap-failure"), cond_sym.span.start_line);
                                        panic_cont.predicate = match self.typemap.get_type_expected(&cond_sym) {
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
                                    let cond_conts = self.eval(Continuation::from_parent(Rc::new(continuation), format!("{function_name}/cond"), cond_sym.span.start_line), &cond_sym)?;

                                    for cond_cont in cond_conts.into_iter() {
                                        if cond_cont.halted() {
                                            new_conts.push(cond_cont);
                                            continue;
                                        }

                                        let cond_predicate = cond_cont.predicate.clone();
                                        let cond_formula = cond_cont.final_formula.clone();

                                        let parent_rc = Rc::new(cond_cont);

                                        // case 1: `(is-err x)` is true
                                        let mut is_err_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}/unwrap-err-success"), cond_sym.span.start_line);
                                        is_err_cont.predicate = cond_predicate.clone().and(Predicate::IsErr(cond_formula.clone()));
                                        is_err_cont.final_formula = SymOp::UnwrapErrPanic(Box::new(cond_formula.clone()));

                                        // case 2: (is-ok x) is true This
                                        // panics
                                        let mut panic_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}/unwrap-err-failure"), cond_sym.span.start_line);
                                        panic_cont.predicate = cond_predicate.and(Predicate::IsOkay(cond_formula.clone()));
                                        panic_cont.panicking = true;
                                        panic_cont.final_formula = SymOp::Panic;

                                        new_conts.push(is_err_cont);
                                        new_conts.push(panic_cont);
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

                                        let cond_conts = self.eval(Continuation::from_parent(Rc::new(continuation), format!("{function_name}/cond-eval"), cond_sym.span.start_line), &cond_sym)?;
                                        for cond_cont in cond_conts.into_iter() {
                                            if cond_cont.halted() {
                                                new_conts.push(cond_cont);
                                                continue;
                                            }
                                            let parent_pred = cond_cont.predicate.clone();
                                            let cond_formula = cond_cont.final_formula.clone();
                                            let parent_rc = Rc::new(cond_cont);

                                            // case 1: (ok y)
                                            let mut ok_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}/ok-case"), cond_ok_sym.span.start_line);

                                            ok_cont.predicate = parent_pred.clone().and(Predicate::IsOkay(cond_formula.clone()));
                                            ok_cont.bind_symop(&ok_sym_name.clone(), SymOp::UnwrapPanic(Box::new(cond_formula.clone())).simplify()?);

                                            let mut ok_conts = self.eval(ok_cont, &cond_ok_sym)?;
                                            for ok_cont in ok_conts.iter_mut() {
                                                ok_cont.unbind(ok_sym_name);
                                            }
                                            new_conts.extend(ok_conts.into_iter());

                                            // case 2: (err y)
                                            let mut err_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}/err-eval"), cond_err_sym.span.start_line);

                                            err_cont.predicate = parent_pred.clone().and(Predicate::IsErr(cond_formula.clone()));
                                            err_cont.bind_symop(&err_sym_name.clone(), SymOp::UnwrapErrPanic(Box::new(cond_formula.clone())).simplify()?);

                                            let mut err_conts = self.eval(err_cont, &cond_err_sym)?;
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

                                        let cond_conts = self.eval(Continuation::from_parent(Rc::new(continuation), format!("{function_name}/cond"), cond_sym.span.start_line), &cond_sym)?;
                                        for cond_cont in cond_conts.into_iter() {
                                            if cond_cont.halted() {
                                                new_conts.push(cond_cont);
                                                continue;
                                            }

                                            let parent_pred = cond_cont.predicate.clone();
                                            let cond_formula = cond_cont.final_formula.clone();
                                            let parent_rc = Rc::new(cond_cont);

                                            // case 1: (some y)
                                            let mut some_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}/some-case"), cond_some_sym.span.start_line);

                                            some_cont.predicate = parent_pred.clone().and(Predicate::IsSome(cond_formula.clone()));
                                            some_cont.bind_symop(&some_sym_name.clone(), SymOp::UnwrapPanic(Box::new(cond_formula.clone())).simplify()?);

                                            let mut some_conts = self.eval(some_cont, &cond_some_sym)?;
                                            for some_cont in some_conts.iter_mut() {
                                                some_cont.unbind(some_sym_name);
                                            }
                                            new_conts.extend(some_conts.into_iter());

                                            // case 2: none
                                            let mut none_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}/none-case"), cond_none_sym.span.start_line);

                                            none_cont.predicate = parent_pred.clone().and(Predicate::IsNone(cond_formula.clone()));

                                            let none_conts = self.eval(none_cont, &cond_none_sym)?;
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
                                    let cond_conts = self.eval(Continuation::from_parent(parent_rc, format!("{function_name}/inner"), exp_sym.span.start_line), &exp_sym)?;
                                    for cond_cont in cond_conts.into_iter() {
                                        if cond_cont.halted() {
                                            new_conts.push(cond_cont);
                                            continue;
                                        }

                                        let cond_formula = cond_cont.final_formula.clone();
                                        let cond_predicate = cond_cont.predicate.clone();

                                        let parent_rc = Rc::new(cond_cont);

                                        // case 1: `(is-ok x)` is true or `(is-some x)` is true
                                        let mut ok_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}/try-success"), exp_sym.span.start_line);

                                        ok_cont.predicate = match self.typemap.get_type_expected(&exp_sym) {
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

                                        // case 2: (is-ok x) (or (is-some x)) is false
                                        let mut fail_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}/try-failure"), exp_sym.span.start_line);
                                        let (fail_formula, fail_predicate) = match self.typemap.get_type_expected(&exp_sym) {
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
                                            
                                        debug!("Continuation {} is early-return", fail_cont.id);
                                        fail_cont.early_return = true;
                                        fail_cont.final_formula = fail_formula;
                                        fail_cont.predicate = fail_predicate;

                                        new_conts.push(ok_cont);
                                        new_conts.push(fail_cont);
                                    }

                                    new_conts
                                }
                                "is-ok" => {
                                    self.eval_native_1arg(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::IsOkay(Box::new(initial))
                                    )?
                                }
                                "is-err" => {
                                    self.eval_native_1arg(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::IsErr(Box::new(initial))
                                    )?
                                }
                                "is-some" => {
                                    self.eval_native_1arg(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::IsSome(Box::new(initial))
                                    )?
                                }
                                "is-none" => {
                                    self.eval_native_1arg(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?.clone(),
                                        |initial| SymOp::IsNone(Box::new(initial))
                                    )?
                                }
                                "filter" => {
                                    let Some(func_name) = lv.get(1).ok_or_else(|| Error::Bug("Missing function".into()))?.match_atom() else {
                                        return Err(Error::Bug("map function is not an atom".into()));
                                    };
                                    let sequence = lv.get(2).ok_or_else(|| Error::Bug("Missing sequence".into()))?;
                                    let Some(seq_ts) = self.typemap.get_type_expected(sequence).cloned() else {
                                        return Err(Error::Bug(format!("No type information for sequence {sequence:?}")));
                                    };

                                    let seq_maxlen = Self::sequence_maxlen(&seq_ts)?;

                                    let mut final_conts = vec![];
                                    let mut ret = vec![];

                                    let conts = self.eval(Continuation::from_parent(Rc::new(continuation), format!("{function_name}/sequence"), sequence.span.start_line), &sequence)?;

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
                                        let mut empty_cont = Continuation::from_parent(Rc::new(cont), format!("{function_name}/{func_name}/empty-case"), parent_line);

                                        // filter produces a sequence with the same type as the
                                        // input sequence.
                                        let final_formula = match seq_ts {
                                            TypeSignature::SequenceType(SequenceSubtype::BufferType(..)) => SymOp::Constant(Value::buff_from(vec![])?),
                                            TypeSignature::SequenceType(SequenceSubtype::ListType(..)) => SymOp::ListCons(vec![]),
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
                                                    if let Some(func) = self.contract_context.functions.get(func_name) {
                                                        // user-defined function
                                                        if func.arguments.len() != 1 {
                                                            return Err(Error::Bug(format!("Function `{func_name}` takes {} arguments but expected 1 argument", func.arguments.len())));
                                                        }
                                                        let mut binding_cont = Continuation::from_parent(Rc::new(cont), format!("{function_name}/{func_name}/seq-{seq_i}/binding"), func.body.span.start_line);
                                                        
                                                        binding_cont.bind_symop(&func.arguments[0], SymOp::UnwrapPanic(Box::new(SymOp::ElementAt(Box::new(seq_formula.clone()), Box::new(SymOp::Constant(Value::UInt(seq_i - 1)))))).simplify()?);

                                                        let callee_cont = Continuation::from_caller(Rc::new(binding_cont), format!("{function_name}/{func_name}/seq-{seq_i}/body"), func.body.span.start_line);
                                                        let body_conts = self.eval(callee_cont, &func.body)?;

                                                        let mut return_conts = vec![];
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
                                                                    SymOp::Concat(Box::new(seq_cons.clone()), Box::new(seq_item))
                                                                },
                                                                TypeSignature::SequenceType(SequenceSubtype::ListType(..)) => {
                                                                    seq_cons.clone().list_cons(seq_item)
                                                                },
                                                                TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(..))) => {
                                                                    SymOp::Concat(Box::new(seq_cons.clone()), Box::new(seq_item))
                                                                },
                                                                TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(..))) =>  {
                                                                    SymOp::Concat(Box::new(seq_cons.clone()), Box::new(seq_item))
                                                                },
                                                                _ => {
                                                                    return Err(Error::Bug("filtered sequence does not have a sequence type".into()));
                                                                }
                                                            };

                                                            let mut true_cont = Continuation::from_callee(parent_rc.clone(), format!("{function_name}/{func_name}/seq-{seq_i}/return-true"), func.body.span.start_line);
                                                            true_cont.predicate = true_cont.predicate.and(func_result.clone().try_as_predicate()?);
                                                            true_cont.final_formula = true_seq_cons.clone();

                                                            let mut false_cont = Continuation::from_callee(parent_rc, format!("{function_name}/{func_name}/seq-{seq_i}/return-false"), func.body.span.start_line);
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
                                "to-consensus-buff?" => {
                                    let Some(exp_sym) = lv.get(1) else {
                                        return Err(Error::Bug(format!("Missing argument 1 to {function_name}")));
                                    };

                                    let expr_cont = Continuation::from_parent(Rc::new(continuation), format!("{function_name}/expr-eval"), exp_sym.span.start_line);
                                    let conts = self.eval(expr_cont, exp_sym)?;
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
                                        let mut success = Continuation::from_parent(cont_rc.clone(), format!("{function_name}/expr-serialized"), exp_sym.span.start_line);
                                        success.predicate = pred.clone().and(Predicate::IsSome(formula.clone()));
                                        success.final_formula = formula.clone();

                                        let mut failure = Continuation::from_parent(cont_rc.clone(), format!("{function_name}/expr-too-big"), exp_sym.span.end_line);
                                        failure.predicate = pred.clone().and(Predicate::IsNone(formula.clone()));
                                        failure.final_formula = SymOp::none();

                                        ret.push(success);
                                        ret.push(failure);
                                    }

                                    ret
                                }

                                "define-constant"
                                | "define-private"
                                | "define-read-only"
                                | "define-public"
                                | "define-map"
                                | "define-data-var" => {
                                    // already handled
                                    vec![continuation]
                                }
                                "stx-get-balance" => {
                                    let Some(addr_sym) = lv.get(1) else {
                                        return Err(Error::Bug(format!("Missing argument 1 to {function_name}")));
                                    };
                                    let addr_cont = Continuation::from_parent(Rc::new(continuation), format!("{function_name}/addr-eval"), addr_sym.span.start_line);

                                    let mut conts = self.eval(addr_cont, addr_sym)?;
                                    for cont in conts.iter_mut() {
                                        if cont.halted() {
                                            continue;
                                        }

                                        // TODO: look up balances
                                        cont.final_formula = SymOp::Variable(Sym::UInt("mock-stx-get-balance".into()));
                                    }
                                    conts
                                }
                                x => {
                                    todo!("native not implemented: {x}")
                                }
                            }
                        }
                    }
                    else {
                        unreachable!()
                    }
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
                let parent_func = continuation.current_function.clone().unwrap_or("".to_string());
                let function_name = format!("{parent_func}.{}", &cn.as_str());
                let mut cont = Continuation::from_parent(Rc::new(continuation), function_name, body.span.start_line);
                match cn.as_str() {
                    "true" => {
                        cont.final_formula = SymOp::Constant(Value::Bool(true));
                        vec![cont]
                    }
                    "false" => {
                        cont.final_formula = SymOp::Constant(Value::Bool(false));
                        vec![cont]
                    }
                    "none" => {
                        cont.final_formula = SymOp::none();
                        vec![cont]
                    },
                    "tx-sender" => {
                        cont.final_formula = cont.get_tx_sender();
                        vec![cont]
                    }
                    "contract-caller" => {
                        cont.final_formula = cont.get_contract_caller();
                        vec![cont]
                    }
                    "block-height" => {
                        return Err(Error::Bug("`block-height` is not supported anymore".into()));
                    },
                    "burn-block-height" => {
                        cont.final_formula = SymOp::Variable(Sym::UInt("burn-block-height".into()));
                        vec![cont]
                    }
                    "stx-liquid-supply" => {
                        cont.final_formula = SymOp::Variable(Sym::UInt("stx-liquid-supply".into()));
                        vec![cont]
                    }
                    "is-in-regtest" => {
                        cont.final_formula = SymOp::Variable(Sym::Bool("is-in-regtest".into()));
                        vec![cont]
                    }
                    "tx-sponsor?" => {
                        cont.final_formula = cont.get_tx_sponsor();
                        vec![cont]
                    }
                    "is-in-mainnet" => {
                        cont.final_formula = SymOp::Variable(Sym::Bool("is-in-mainnet".into()));
                        vec![cont]
                    }
                    "chain-id" => {
                        cont.final_formula = SymOp::Variable(Sym::UInt("chain-id".into()));
                        vec![cont]
                    }
                    "stacks-block-height" => {
                        cont.final_formula = SymOp::Variable(Sym::UInt("stacks-block-height".into()));
                        vec![cont]
                    }
                    "tenure-height" => {
                        cont.final_formula = SymOp::Variable(Sym::UInt("tenure-height".into()));
                        vec![cont]
                    }
                    "stacks-block-time" => {
                        cont.final_formula = SymOp::Variable(Sym::UInt("stacks-block-time".into()));
                        vec![cont]
                    }
                    "current-contract" => {
                        cont.final_formula = SymOp::Constant(Value::Principal(cont.get_current_contract()));
                        vec![cont]
                    }
                    x => {
                        let symid : SymId = x.into();
                        let Some(formula) = cont.lookup_formula(&symid) else {
                            error!("Faulty cont looking for '{}'", &symid);
                            error!("{}", &cont);
                            error!("Trace:\n{}", cont.trace());
                            return Err(Error::Bug(format!("Unbound formula '{}'", &x)));
                        };
                        cont.final_formula = formula.clone();
                        vec![cont]
                    }
                }
            },
            SymbolicExpressionType::Field(_ti) => {
                unreachable!()
            }
            SymbolicExpressionType::TraitReference(_cn, _td) => {
                unreachable!()
            }
        };
        let continuations = Self::reduce_continuations(continuations);

        for continuation in continuations.iter() {
            debug!("eval continuation {}: {} pred={}, formula={}", continuation.id, &continuation.current_function.clone().unwrap_or("".to_string()), &continuation.predicate.clone().simplify().unwrap(), &continuation.final_formula.clone().simplify().unwrap());
        }
        Ok(continuations)
    }

    fn apply_user_function(&self, continuation: Continuation, function_name: &ClarityName, function_arg_values: &[SymbolicExpression]) -> Result<Vec<Continuation>, Error> {
        let Some(func) = self.contract_context.functions.get(function_name) else {
            return Err(Error::NotFound(format!("No such function '{function_name}'")));
        };
        if function_arg_values.len() != func.arguments.len() {
            return Err(Error::Bug("Function argument values != function arguments or function_arguments != function argument types".into()));
        }

        let parent_function_name = continuation.current_function.clone().unwrap_or("".to_string());
        let fq_function = format!("{}.{}", &parent_function_name, function_name);

        // build up (final-continuation, list-of-argument-symops)
        let mut conts = vec![(continuation, vec![])];
        for (i, symexp) in function_arg_values.iter().enumerate() {
            let mut new_conts = vec![];
            for (cont, mut symops) in conts.into_iter() {
                let arg_conts = self.eval(Continuation::from_parent(Rc::new(cont), format!("{}/arg[{}]={}", &fq_function, i, &func.arguments[i]), symexp.span.start_line), symexp)?;
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

            let mut binding_cont = Continuation::from_parent(Rc::new(caller_cont), format!("{}/binding", &fq_function), func.body.span.start_line);
            let mut bound = vec![];
            for (arg_name, symop) in func.arguments.iter().zip(symops.iter()) {
                binding_cont.bind_symop(arg_name, symop.clone().simplify()?);
                bound.push(arg_name.clone());
            }

            let callee_cont = Continuation::from_caller(Rc::new(binding_cont), format!("{}/body", &fq_function), func.body.span.start_line);
            let conts = self.eval(callee_cont, &func.body)?;

            let conts : Vec<_> = conts
                .into_iter()
                .map(|cont| {
                    if cont.panicking {
                        return cont;
                    }
                    let mut return_cont = Continuation::from_callee(Rc::new(cont), format!("{}/return", fq_function), func.body.span.start_line);
                    for unbind in bound.iter() {
                        return_cont.unbind(unbind);
                    }
                    return_cont
                })
                .collect();

            called_conts.extend(conts.into_iter());
        }
        Ok(Self::reduce_continuations(called_conts))
    }

    fn eval_if(&self, continuation: Continuation, predicate_symexp: SymbolicExpression, if_true_symexp: SymbolicExpression, if_false_symexp: SymbolicExpression) -> Result<Vec<Continuation>, Error> {
        let parent_func = continuation.current_function.clone().unwrap_or("".to_string());
        let continuation_rc = Rc::new(continuation);
        let predicate_conts = self.eval(Continuation::from_parent(continuation_rc.clone(), format!("{}/if", &parent_func), predicate_symexp.span.start_line), &predicate_symexp)?;
        let mut branch_conts = vec![];
        for predicate_cont in predicate_conts.into_iter() {
            if predicate_cont.halted() {
                branch_conts.push(predicate_cont);
                continue;
            }
            let predicate = predicate_cont.final_formula.try_as_predicate()?;
            let predicate_rc = Rc::new(predicate_cont);
            let if_true_conts = if predicate != Predicate::False {
                let mut true_continuation = Continuation::from_parent(predicate_rc.clone(), format!("{}/if-true", &parent_func), if_true_symexp.span.start_line);
                true_continuation.predicate = true_continuation.predicate.clone().and(predicate.clone());

                let if_true_conts = self.eval(true_continuation, &if_true_symexp)?;
                if_true_conts
            }
            else {
                vec![]
            };

            let if_false_conts = if predicate != Predicate::True {
                let mut false_continuation = Continuation::from_parent(predicate_rc.clone(), format!("{}/if-false", parent_func), if_false_symexp.span.start_line);
                false_continuation.predicate = false_continuation.predicate.clone().and(predicate.clone().not());

                let if_false_conts = self.eval(false_continuation, &if_false_symexp)?;
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

    fn let_bind(&self, continuation: Continuation, let_bindings: &[SymbolicExpression]) -> Result<Vec<Continuation>, Error> {
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

        let parent_func = continuation.current_function.clone().unwrap_or("".to_string());
        let function_name = format!("{parent_func}.let");

        let mut conts = vec![(continuation, vec![])];
        for (i, (bind_name, body_symexp)) in bind_names_and_bodies.iter().enumerate() {
            let mut new_conts = vec![];
            for (cont, bound_syms) in conts.into_iter() {
                if cont.halted() {
                    new_conts.push((cont, bound_syms));
                    continue;
                }

                let bind_conts = self.eval(Continuation::from_parent(Rc::new(cont), format!("{function_name}/bind[{i}]/{bind_name}"), (*body_symexp).span.start_line), body_symexp)?;
                for mut bind_cont in bind_conts.into_iter() {
                    if bind_cont.halted() {
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
                        let next_body_cont = Continuation::from_parent(Rc::new(body_cont), format!("{function_name}/expr[{i}]"), body.span.start_line);
                        let conts = self.eval(next_body_cont, body)?;
                        next_body_conts.push(conts);
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
        Ok(Self::reduce_continuations(bound_conts))
    }
    
    pub fn from_contract(contract_id: QualifiedContractIdentifier, code: &str) -> Result<Self, Error> {
        Self::from_contract_ex(contract_id, code, None)
    }

    pub fn from_contract_sponsored(contract_id: QualifiedContractIdentifier, code: &str, contract_sponsor: StandardPrincipalData) -> Result<Self, Error> {
        Self::from_contract_ex(contract_id, code, Some(contract_sponsor))
    }
    
    pub fn from_contract_ex(contract_id: QualifiedContractIdentifier, code: &str, contract_sponsor: Option<StandardPrincipalData>) -> Result<Self, Error> {
        let mut datastore = BackingStore::new();
        let ast = ast::parse_ast(&contract_id, code)?;
        let mut analysis = ast::make_contract_analysis_from_ast(&mut datastore, &contract_id, &ast)?;
        let contract_context = ast::make_contract_context_from_ast(
            &mut datastore,
            &contract_id,
            code,
            &ast,
            contract_sponsor.clone().map(|s| PrincipalData::Standard(s))
        )?;
     
        let Some(typemap) = analysis.type_map.take() else {
            return Err(Error::Bug("No typemap computed".into()));
        };
        let callgraph = Callgraph::from_exprs(&contract_context, &ast.expressions)?;

        let symbex = Symbex {
            datastore,
            contract_context,
            symbols: ast.expressions,
            callgraph,
            typemap,
            tx_sender: None,
            contract_caller: None,
            tx_sponsor: None,
            explore_function_calls: true,
            skip_function_calls: HashSet::new(),
            skip_pure_calls: true,
            skip_causally_independent_calls: true,
            evaluated_functions: HashMap::new()
        };
        Ok(symbex)
    }

    pub fn with_tx_sender(mut self, tx_sender: Option<StandardPrincipalData>) -> Self {
        self.tx_sender = tx_sender.map(|tx_sender| SymOp::Constant(Value::Principal(PrincipalData::Standard(tx_sender))));
        debug!("tx-sender is {:?}", &self.tx_sender);
        self
    }

    pub fn with_tx_sponsor(mut self, tx_sponsor: Option<StandardPrincipalData>) -> Self {
        self.tx_sponsor = tx_sponsor.map(|tx_sponsor| SymOp::Constant(Value::some(Value::Principal(PrincipalData::Standard(tx_sponsor))).expect("infallible")));
        debug!("tx-sponsor? is {:?}", &self.tx_sponsor);
        self
    }

    pub fn with_contract_caller(mut self, contract_caller: Option<PrincipalData>) -> Self {
        self.contract_caller = contract_caller.map(|contract_caller| SymOp::Constant(Value::Principal(contract_caller)));
        debug!("contract-caller is {:?}", &self.contract_caller);
        self
    }

    pub fn with_function_call_exploration(mut self, explore: bool) -> Self {
        self.explore_function_calls = explore;
        debug!("explore_function_calls = {}", self.explore_function_calls);
        self
    }

    pub fn with_skipped_function_call(mut self, func_name: ClarityName) -> Self {
        debug!("skip_function_call {func_name}");
        self.skip_function_calls.insert(func_name);
        self
    }

    pub fn skip_pure(mut self, val: bool) -> Self {
        self.skip_pure_calls = val;
        debug!("skip_pure_calls = {}", self.skip_pure_calls);
        self
    }

    pub fn skip_causally_independent(mut self, val: bool) -> Self {
        self.skip_causally_independent_calls = val;
        debug!("skip_causally_independent_calls = {}", self.skip_causally_independent_calls);
        self
    }
    
    pub fn eval_all(&mut self) -> Result<Vec<Continuation>, Error> {
        let current_contract = PrincipalData::Contract(self.contract_context.contract_identifier.clone());

        let mut root_continuation = Continuation::root(self, current_contract);
        
        for (const_name, const_value) in self.contract_context.variables.iter() {
            root_continuation.bind_constant(const_name, const_value);
        }

        for (var_name, var_metadata) in self.contract_context.meta_data_var.iter() {
            root_continuation.set_pre_data_var(var_name, SymOp::Variable(Sym::from_name_and_type_signature(var_name, &var_metadata.value_type)));
        }

        let contract_funcs = self.callgraph.get_contract_functions(&self.contract_context.contract_identifier);
        for contract_func in contract_funcs.into_iter() {
            if self.evaluated_functions.contains_key(&contract_func) {
                continue;
            }

            info!("Evaluating function '{contract_func}'");
            // TODO: contract ID
            let conts : Vec<_> = self.eval_user_function(contract_func.name().as_str())?
                .into_iter()
                .map(|cont| cont.rollup())
                .collect();

            for cont in conts.iter() {
                info!("Computed continuation for function '{contract_func}'\n{cont}");
            }
            self.evaluated_functions.insert(contract_func, conts);
        }

        info!("Evaluating top-level symbols");

        let mut conts = vec![root_continuation];
        for sym in self.symbols.iter() {
            let mut next = vec![];
            for cont in conts.into_iter() {
                let cont_rc = Rc::new(cont);
                let next_conts = self.eval(Continuation::from_parent(cont_rc.clone(), "".to_string(), sym.span.start_line), sym)?;
                assert!(next_conts.len() > 0, "No continuation produced from {cont_rc:?}");
                next.extend(next_conts.into_iter());
            }
            conts = next;
        }

        Ok(Self::reduce_continuations(conts))
    }
  
    /// Symbolically evaluate a user function.
    /// Each argument will be bound to a SymOp::Variable of the appropriate type.
    /// TODO: contract ID
    pub fn eval_user_function(&mut self, function_name: &str) -> Result<Vec<Continuation>, Error> {
        if self.contract_context.functions.get(function_name).is_none() {
            return Err(Error::NotFound(format!("No such function '{function_name}'")));
        };

        let fq_name = CallableName(
            self.contract_context.contract_identifier.clone(),
            ClarityName::try_from(function_name).map_err(|_| Error::Bug("Invalid function name".into()))?
        );

        let reachable_funcs = self.callgraph.reachable_from(&fq_name)?;
        for reachable_func in reachable_funcs.into_iter() {
            if self.evaluated_functions.contains_key(&reachable_func) {
                continue;
            }
            
            info!("Evaluating reachable function '{reachable_func}'");
            // TODO: contract ID
            let conts : Vec<_> = self.inner_eval_user_function(reachable_func.name().as_str())?
                .into_iter()
                .filter(|c| !c.panicking)
                .map(|c| c.rollup())
                .collect();

            for cont in conts.iter() {
                info!("Computed continuation for function '{reachable_func}'\n{cont}");
            }

            self.evaluated_functions.insert(reachable_func, conts);
        }

        info!("Evaluating function '{function_name}'");
        self.inner_eval_user_function(function_name)
    }

    fn inner_eval_user_function(&mut self, function_name: &str) -> Result<Vec<Continuation>, Error> {
        if self.contract_context.functions.get(function_name).is_none() {
            return Err(Error::NotFound(format!("No such function '{function_name}'")));
        };
        let Some(func) = self.contract_context.functions.get(function_name) else {
            return Err(Error::NotFound(format!("No such function '{function_name}'")));
        };
        if func.arguments.len() != func.arg_types.len() {
            return Err(Error::Bug("Function argument names length != function argument types length".into()));
        }
        let fq_name = CallableName(self.contract_context.contract_identifier.clone(), ClarityName::try_from(function_name).map_err(|_| Error::Bug("Invalid function name".into()))?);

        // set up root context
        let current_contract = PrincipalData::Contract(self.contract_context.contract_identifier.clone());
        let mut root_continuation = Continuation::root(self, current_contract);
        
        for (const_name, const_value) in self.contract_context.variables.iter() {
            root_continuation.bind_constant(const_name, const_value);
        }

        for (var_name, var_metadata) in self.contract_context.meta_data_var.iter() {
            root_continuation.set_pre_data_var(var_name, SymOp::Variable(Sym::from_name_and_type_signature(var_name, &var_metadata.value_type)));
        }

        // create symbolic function bindings
        let mut binding_cont = Continuation::from_parent(Rc::new(root_continuation), format!("{}/binding", &function_name), func.body.span.start_line);

        binding_cont.add_reachable_storage_accesses(&fq_name, &self.callgraph)?;
        let mut bound = vec![];
        for (arg_name, arg_type) in func.arguments.iter().zip(func.arg_types.iter()) {
            let sym = Sym::from_name_and_type_signature(arg_name, arg_type);
            binding_cont.bind_symop(arg_name, SymOp::Variable(sym));
            bound.push(arg_name.clone());
        }

        // run that function!
        let callee_cont = Continuation::from_caller(Rc::new(binding_cont), format!("{}/body", &function_name), func.body.span.start_line);
        let conts = self.eval(callee_cont, &func.body)?;

        let conts : Vec<_> = conts
            .into_iter()
            .map(|cont| {
                if cont.panicking {
                    return cont;
                }
                let mut return_cont = Continuation::from_callee(Rc::new(cont), format!("{}/return", function_name), func.body.span.start_line);
                for unbind in bound.iter() {
                    return_cont.unbind(unbind);
                }
                return_cont
            })
            .collect();

        Ok(Self::reduce_continuations(conts))
    }

    pub fn callgraph(&self) -> &Callgraph {
        &self.callgraph
    }
}

