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
use std::collections::BTreeMap;
use std::sync::LazyLock; 
use std::collections::BTreeSet;
use std::borrow::Borrow;

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
use clarity::vm::types::{
    ASCIIData, BuffData, CharType, SequenceData, UTF8Data,
};

use stacks_common::consts::CHAIN_ID_MAINNET;

// use integer_sqrt::IntegerSquareRoot;

use crate::core::BackingStore;
use crate::core::Error;
use crate::core::ast;
use crate::core::{DEFAULT_STACKS_EPOCH, DEFAULT_CLARITY_VERSION};

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
}

impl fmt::Display for Sym {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::Int(s) => write!(f, "({} {})", s, TypeSignature::IntType),
            Self::UInt(s) => write!(f, "({} {})", s, TypeSignature::UIntType),
            Self::Bool(s) => write!(f, "({} {})", s, TypeSignature::BoolType),
            Self::Sequence(s, stype) => write!(f, "({} {})", s, TypeSignature::SequenceType(stype.clone())),
            Self::Principal(s) => write!(f, "({} {})", s, TypeSignature::PrincipalType),
            Self::Tuple(s, ttype) => write!(f, "({} {})", s, TypeSignature::TupleType(ttype.clone())),
            Self::Optional(s, otype) => write!(f, "({} {})", s, TypeSignature::OptionalType(Box::new(otype.clone()))),
            Self::Response(s, oktype, errtype) => write!(f, "({} {})", s, TypeSignature::ResponseType(Box::new((oktype.clone(), errtype.clone())))),
            Self::Callable(s, ctype) => write!(f, "({} {})", s, TypeSignature::CallableType(ctype.clone())),
            Self::ListUnion(s, utypes) => {
                let mut union_type_strs = vec![];
                for utype in utypes.iter() {
                    match utype {
                        CallableSubtype::Trait(trait_id) => {
                            union_type_strs.push(format!("({} <{}>)", s, trait_id));
                        }
                        CallableSubtype::Principal(contract_id) => {
                            union_type_strs.push(format!("({} (principal {}))", s, contract_id));
                        }
                    }
                }
                let union_type = union_type_strs.join(" ");
                write!(f, "({} (union {}))", s, union_type)
            },
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
#[derive(Debug, Clone, Eq, Hash)]
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
    Panic
}

/// Equality implementation that takes into account commutativity
impl PartialEq for SymOp {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Constant(v1), Self::Constant(v2)) => v1 == v2,
            (Self::Variable(s1), Self::Variable(s2)) => s1 == s2,
            (Self::LoadedDataVariable(n1, s1), Self::LoadedDataVariable(n2, s2)) => n1 == n2 && s1 == s2,
            (Self::Add(_s1), Self::Add(_s2)) => {
                let s1_set = self.hashcount().expect("infallible");
                let s2_set = other.hashcount().expect("infallible");

                s1_set == s2_set
            }
            (Self::Subtract(s1), Self::Subtract(s2)) => s1 == s2,
            (Self::Multiply(_s1), Self::Multiply(_s2)) => {
                let s1_set = self.hashcount().expect("infallible");
                let s2_set = other.hashcount().expect("infallible");

                s1_set == s2_set
            }
            (Self::Divide(s1), Self::Divide(s2)) => s1 == s2,
            (Self::And(_s1), Self::And(_s2)) => {
                let s1_set = self.hashcount().expect("infallible");
                let s2_set = other.hashcount().expect("infallible");

                s1_set == s2_set
            },
            (Self::Or(_s1), Self::Or(_s2)) => {
                let s1_set = self.hashcount().expect("infallible");
                let s2_set = other.hashcount().expect("infallible");

                s1_set == s2_set
            },
            (Self::Equals(_s1), Self::Equals(_s2)) => {
                let s1_set = self.hashcount().expect("infallible");
                let s2_set = other.hashcount().expect("infallible");

                s1_set == s2_set
            },
            (Self::BitwiseAnd(_s1), Self::BitwiseAnd(_s2)) => {
                let s1_set = self.hashcount().expect("infallible");
                let s2_set = other.hashcount().expect("infallible");

                s1_set == s2_set
            },
            (Self::BitwiseOr(_s1), Self::BitwiseOr(_s2)) => {
                let s1_set = self.hashcount().expect("infallible");
                let s2_set = other.hashcount().expect("infallible");

                s1_set == s2_set
            },
            (Self::BitwiseXor(_s1), Self::BitwiseXor(_s2)) => {
                let s1_set = self.hashcount().expect("infallible");
                let s2_set = other.hashcount().expect("infallible");

                s1_set == s2_set
            },
            (Self::BitwiseNot(_s1), Self::BitwiseNot(_s2)) => {
                let s1_set = self.hashcount().expect("infallible");
                let s2_set = other.hashcount().expect("infallible");

                s1_set == s2_set
            },
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
            (_, _) => false
        }
    }
}

impl SymOp {
    fn inner_hashcount(syms: &[Box<SymOp>]) -> HashMap<&Box<SymOp>, usize> {
        let mut ret = HashMap::new();
        for s in syms {
            if let Some(count) = ret.get_mut(s) {
                *count += 1;
            }
            else {
                ret.insert(s, 1);
            }
        }
        ret
    }

    /// Get a hash table of term counts.
    /// Used for comparing operations that are commutative
    fn hashcount(&self) -> Option<HashMap<&Box<SymOp>, usize>> {
        match self {
            Self::Add(s) => Some(Self::inner_hashcount(s)),
            Self::Multiply(s) => Some(Self::inner_hashcount(s)),
            Self::And(s) => Some(Self::inner_hashcount(s)),
            Self::Or(s) => Some(Self::inner_hashcount(s)),
            Self::Equals(s) => Some(Self::inner_hashcount(s)),
            Self::BitwiseAnd(s) => Some(Self::inner_hashcount(s)),
            Self::BitwiseOr(s) => Some(Self::inner_hashcount(s)),
            Self::BitwiseXor(s) => Some(Self::inner_hashcount(s)),

            Self::Constant(..)
            | Self::Variable(..)
            | Self::LoadedDataVariable(..)
            | Self::Subtract(..)
            | Self::Divide(..)
            | Self::ToInt(..)
            | Self::ToUInt(..)
            | Self::Modulo(..)
            | Self::Power(..)
            | Self::Sqrti(..)
            | Self::Log2(..)
            | Self::Greater(..)
            | Self::Geq(..)
            | Self::Leq(..)
            | Self::Less(..)
            | Self::Not(..)
            | Self::Append(..)
            | Self::Concat(..)
            | Self::AsMaxLen(..)
            | Self::Len(..)
            | Self::ElementAt(..)
            | Self::IndexOf(..)
            | Self::BuffToIntLe(..)
            | Self::BuffToUIntLe(..)
            | Self::BuffToIntBe(..)
            | Self::BuffToUIntBe(..)
            | Self::IsStandard(..)
            | Self::PrincipalDestruct(..)
            | Self::PrincipalConstruct(..)
            | Self::StringToInt(..)
            | Self::StringToUInt(..)
            | Self::IntToAscii(..)
            | Self::IntToUtf8(..)
            | Self::ListCons(..)
            | Self::FetchVar(..)
            | Self::SetVar(..)
            | Self::FetchEntry(..)
            | Self::SetEntry(..)
            | Self::InsertEntry(..)
            | Self::DeleteEntry(..)
            | Self::TupleCons(..)
            | Self::TupleGet(..)
            | Self::TupleMerge(..)
            | Self::Hash160(..)
            | Self::Sha256(..)
            | Self::Sha512(..)
            | Self::Sha512Trunc256(..)
            | Self::Keccak256(..)
            | Self::Secp256k1Recover(..)
            | Self::Secp256k1Verify(..)
            | Self::ContractOf(..)
            | Self::PrincipalOf(..)
            | Self::GetBurnBlockInfo(..)
            | Self::IsOkay(..)
            | Self::IsErr(..)
            | Self::IsSome(..)
            | Self::IsNone(..)
            | Self::UnwrapPanic(..)
            | Self::UnwrapErrPanic(..)
            | Self::ConsSome(..)
            | Self::ConsError(..)
            | Self::ConsOkay(..)
            | Self::GetTokenBalance(..)
            | Self::GetNftOwner(..)
            | Self::TransferToken(..)
            | Self::TransferNft(..)
            | Self::MintToken(..)
            | Self::MintNft(..)
            | Self::GetTokenSupply(..)
            | Self::BurnToken(..)
            | Self::BurnNft(..)
            | Self::GetStxBalance(..)
            | Self::StxTransfer(..)
            | Self::StxTransferMemo(..)
            | Self::StxBurn(..)
            | Self::StxGetAccount(..)
            | Self::BitwiseNot(..)
            | Self::BitwiseLShift(..)
            | Self::BitwiseRShift(..)
            | Self::Slice(..)
            | Self::ToConsensusBuff(..)
            | Self::FromConsensusBuff(..)
            | Self::ReplaceAt(..)
            | Self::GetStacksBlockInfo(..)
            | Self::GetTenureInfo(..)
            | Self::ContractHash(..)
            | Self::ToAscii(..)
            | Self::RestrictAssets(..)
            | Self::AsContractSafe(..)
            | Self::AllowanceWithStx(..)
            | Self::AllowanceWithFt(..)
            | Self::AllowanceWithNft(..)
            | Self::AllowanceWithStacking(..)
            | Self::AllowanceAll
            | Self::Secp256r1Verify(..)
            | Self::Panic
            => None
        }
    }

    fn format_prefix(func: &str, list: &[Box<SymOp>], f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let symop_strs : Vec<_> = list
            .iter()
            .map(|symop| format!("{}", symop))
            .collect();

        let symop_str = symop_strs.join(" ");

        write!(f, "({func} {symop_str})")
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

impl fmt::Display for SymOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::Constant(v) => write!(f, "{}", v),
            Self::Variable(s) => write!(f, "{}", s),
            Self::LoadedDataVariable(name, symop) => {
                match &**symop {
                    Self::Constant(..)
                    | Self::Variable(..) => write!(f, "(begin (print \"input: {}\") (var-get {}))", symop, name),
                    x => write!(f, "{}", x)
                }
            }
            Self::Add(symops) => Self::format_prefix("+", symops, f),
            Self::Subtract(symops) => Self::format_prefix("-", symops, f),
            Self::Multiply(symops) => Self::format_prefix("*", symops, f),
            Self::Divide(symops) => Self::format_prefix("/", symops, f),
            Self::Modulo(op1, op2) => write!(f, "(mod {op1} {op2})"),
            Self::Power(op1, op2) => write!(f, "(pow {op1} {op2})"),
            Self::Sqrti(op1) => write!(f, "(sqrti {op1})"),
            Self::Log2(op1) => write!(f, "(log2 {op1})"),
            Self::And(symops) => Self::format_prefix("and", symops, f),
            Self::Or(symops) => Self::format_prefix("or", symops, f),
            Self::Not(op1) => write!(f, "(not {op1})"),
            Self::Greater(op1, op2) => write!(f, "(> {op1} {op2})"),
            Self::Geq(op1, op2) => write!(f, "(>= {op1} {op2})"),
            Self::Equals(symops) => Self::format_prefix("is-eq", symops, f),
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
            Self::BitwiseAnd(symops) => Self::format_prefix("bit-and", symops, f),
            Self::BitwiseOr(symops) => Self::format_prefix("bit-or", symops, f),
            Self::BitwiseXor(symops) => Self::format_prefix("bit-xor", symops, f),
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
    fn simplify_assoc_variadic<D, C>(func_name: &str, ops: Vec<Box<SymOp>>, destruct: D, construct: C) -> Result<SymOp, Error>
    where
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

        let mut new_ops = vec![];
        let mut folded = None;
        for op in consolidated_ops {
            let op = op.clone().simplify()?;
            if let Self::Constant(v) = op {
                if let Some(Self::Constant(folded_value)) = folded {
                    let v = Self::context_free_clarity_eval_mainnet(vec![
                        SymbolicExpression::atom(func_name.into()),
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

    /// Combine constants in a Subtract(..)
    fn combine_sub_constants(ops: Vec<Box<SymOp>>) -> Result<Vec<Box<SymOp>>, Error> {
        let mut constants = vec![];
        let mut syms = vec![];
        for (i, op) in ops.into_iter().enumerate() {
            let op = (*op).simplify()?;
            if let Self::Constant(v) = op {
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
            // (- (u1 x u2)) becomes (- (-x) u1)
            // (- (u3 x u1)) becomes (- u2 x)
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
                        return Err(Error::Arithmetic(format!("Cannot compute {f} - {c}")));
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

    /// fold constants in subtraction
    fn fold_subtraction_constants(ops: Vec<Box<SymOp>>) -> Result<SymOp, Error> {
        let mut ops = Self::combine_sub_constants(ops)?;

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

    /// Fold and propagate constants in a Divide(..)
    fn fold_divide_constants(ops: Vec<Box<SymOp>>) -> Result<SymOp, Error> {
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
                    SymbolicExpression::atom("/".into()),
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
                            let Some(sym) = syms.pop() else { return Err(Error::Bug("unreachable".into())); };
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
                            let Some(sym) = syms.pop() else { return Err(Error::Bug("unreachable".into())); };
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
                            let Some(sym) = syms.pop() else { return Err(Error::Bug("unreachable".into())); };
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
                            let Some(sym) = syms.pop() else { return Err(Error::Bug("unreachable".into())); };
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
    
    /// Fold and propagate constants through modulus
    fn fold_modulus_constants(numer: Box<SymOp>, denom: Box<SymOp>) -> Result<SymOp, Error> {
        // don't do fraction reduction, but do remove constant multiplication if the
        // numerator is a multiple of the denominator
        match (numer.simplify()?, denom.simplify()?) {
            (Self::Constant(v1), Self::Constant(v2)) => {
                let v = Self::context_free_clarity_eval_mainnet(vec![
                    SymbolicExpression::atom("mod".into()),
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
            (x, y) => {
                Ok(Self::Modulo(Box::new(x), Box::new(y)))
            }
        }
    }

    /// Fold and propagate constants in an And(..)
    fn fold_and_constants(ops: Vec<Box<SymOp>>) -> Result<SymOp, Error> {
        let mut consolidated_ops = vec![];
        for op in ops.into_iter() {
            if let Self::And(inner_ops) = *op {
                for inner_op in inner_ops.into_iter() {
                    let inner_op = inner_op.simplify()?;
                    consolidated_ops.push(Box::new(inner_op));
                }
            }
            else {
                consolidated_ops.push(op);
            }
        }
        
        // remove pure duplicates and simplfiy
        let simplified = Self::dedup_pure_booleans(consolidated_ops)?;

        // constant elimination
        let simplified = Self::simplify_assoc_variadic(
            "and",
            simplified,
            |op| if let Self::And(inner) = op { Some(inner) } else { None },
            |new_ops| Self::And(new_ops)
        )?;
        let SymOp::And(simplified) = simplified else {
            return Ok(simplified);
        };

        // domination: False && X == False
        for op in simplified.iter() {
            if let Self::Constant(Value::Bool(false)) = &**op {
                return Ok(SymOp::Constant(Value::Bool(false)));
            }
        }

        // identity: True && X == X
        let mut simplified : Vec<_> = simplified.into_iter().filter(|s| if let Self::Constant(Value::Bool(true)) = **s { false } else { true }).collect();

        // if they were all true, then simplified would be empty
        if simplified.len() == 0 {
            simplified.push(Box::new(Self::Constant(Value::Bool(true))));
        }
        else if simplified.len() == 1 {
            // lift out
            let Some(inner) = simplified.pop() else { return Err(Error::Bug("unreachable".into())); };
            return Ok(*inner);
        }

        Ok(Self::And(simplified))
    }

    /// fold and propagate constants for an Or(..)
    fn fold_or_constants(ops: Vec<Box<SymOp>>) -> Result<SymOp, Error> {
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
    fn fold_not_constants(op: Box<SymOp>) -> Result<SymOp, Error> {
        match op.simplify()? {
            Self::Constant(x) => {
                let v = Self::context_free_clarity_eval_mainnet(vec![
                    SymbolicExpression::atom("not".into()),
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
            let op = op.simplify()?;
            if op.is_pure() {
                if !pure_distinct.contains(&op) {
                    pure_distinct.insert(op.clone());
                    simplified.push(Box::new(op));
                }
            }
            else {
                simplified.push(Box::new(op));
            }
        }
        Ok(simplified)
    }

    // fold and propagate constants for an Equals(..)
    fn fold_equals_constants(ops: Vec<Box<SymOp>>) -> Result<SymOp, Error> {
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
        let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::transient(), "contract".into());
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
                    SymbolicExpression::atom(func_name.into()),
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
                    SymbolicExpression::atom(func_name.into()),
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
                    SymbolicExpression::atom(func_name.into()),
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

    /// Convert a type signature back into a symbolic expression
    fn type_signature_to_symbolic_expression(ts: TypeSignature) -> SymbolicExpression {
        match ts {
            TypeSignature::NoType => unreachable!(),
            TypeSignature::IntType => SymbolicExpression::atom("int".into()),
            TypeSignature::UIntType => SymbolicExpression::atom("uint".into()),
            TypeSignature::BoolType => SymbolicExpression::atom("bool".into()),
            TypeSignature::SequenceType(SequenceSubtype::BufferType(buflen)) => {
                SymbolicExpression::list(vec![
                    SymbolicExpression::atom("buff".into()),
                    SymbolicExpression::literal_value(Value::Int(u32::from(buflen) as i128))
                ])
            },
            TypeSignature::SequenceType(SequenceSubtype::ListType(listdata)) => {
                let (inner_ts, max_len) = listdata.destruct();
                SymbolicExpression::list(vec![
                    SymbolicExpression::atom("list".into()),
                    Self::type_signature_to_symbolic_expression(inner_ts),
                    SymbolicExpression::literal_value(Value::Int(max_len as i128))
                ])
            }
            TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(len))) => {
                SymbolicExpression::list(vec![
                    SymbolicExpression::atom("string-ascii".into()),
                    SymbolicExpression::literal_value(Value::Int(u32::from(len) as i128))
                ])
            },
            TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(len))) => {
                SymbolicExpression::list(vec![
                    SymbolicExpression::atom("string-ascii".into()),
                    SymbolicExpression::literal_value(Value::Int(u32::from(len) as i128))
                ])
            },
            TypeSignature::PrincipalType => SymbolicExpression::atom("principal".into()),
            TypeSignature::TupleType(tuple_ts) => {
                SymbolicExpression::list(vec![
                    SymbolicExpression::atom("tuple".into()),
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
                    SymbolicExpression::atom("optional".into()),
                    Self::type_signature_to_symbolic_expression(*inner_ts)
                ])
            },
            TypeSignature::ResponseType(inner_ok_err_ts) => {
                let (ok_ts, err_ts) = *inner_ok_err_ts;
                SymbolicExpression::list(vec![
                    SymbolicExpression::atom("response".into()),
                    Self::type_signature_to_symbolic_expression(ok_ts),
                    Self::type_signature_to_symbolic_expression(err_ts)
                ])
            },
            TypeSignature::CallableType(CallableSubtype::Principal(contract_id)) => {
                // this shouldn't be possible
                SymbolicExpression::atom(format!("<{contract_id}>").as_str().into())
            },
            TypeSignature::CallableType(CallableSubtype::Trait(trait_id)) => {
                // this shouldn't be possible
                SymbolicExpression::atom(format!("<{}>", &trait_id.contract_identifier).as_str().into())
            },
            TypeSignature::ListUnionType(callables) => {
                // this shouldn't be possible
                SymbolicExpression::list(callables
                    .into_iter()
                    .map(|callable| match callable {
                        CallableSubtype::Principal(contract_id) => SymbolicExpression::atom(format!("<{contract_id}>").as_str().into()),
                        CallableSubtype::Trait(trait_id) => SymbolicExpression::atom(format!("{}", &trait_id.contract_identifier).as_str().into()),
                    })
                    .collect()
                )
            },
            TypeSignature::TraitReferenceType(trait_id) => {
                // OBSOLETE
                SymbolicExpression::atom(format!("{}", &trait_id.contract_identifier).as_str().into())
            }
        }
    }

    /// Fold and propagate all constants
    fn fold_constants(symop: SymOp) -> Result<SymOp, Error> {
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
                Self::simplify_assoc_variadic(
                    "+",
                    ops,
                    |op| if let Self::Add(inner) = op { Some(inner) } else { None },
                    |new_ops| Self::Add(new_ops)
                )
            },
            Self::Subtract(ops) => {
                Self::fold_subtraction_constants(ops)
            }
            Self::Multiply(ops) => {
                Self::simplify_assoc_variadic(
                    "*",
                    ops,
                    |op| if let Self::Multiply(inner) = op { Some(inner) } else { None },
                    |new_ops| Self::Multiply(new_ops)
                )
            }
            Self::Divide(ops) => {
                Self::fold_divide_constants(ops)
            }
            Self::ToInt(op) => {
                Self::simplify_native_1arg("to-int", op, |x| Self::ToInt(x))
            }
            Self::ToUInt(op) => {
                Self::simplify_native_1arg("to-uint", op, |x| Self::ToUInt(x))
            }
            Self::Modulo(op1, op2) => {
                Self::fold_modulus_constants(op1, op2)
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
                Self::fold_and_constants(ops)
            },
            Self::Or(ops) => {
                Self::fold_or_constants(ops)
            },
            Self::Not(op) => {
                Self::fold_not_constants(op)
            },
            Self::Greater(x, y) => {
                Self::simplify_native_2args(">", x, y, |x, y| Self::Greater(x, y))
            }
            Self::Geq(x, y) => {
                Self::simplify_native_2args(">=", x, y, |x, y| Self::Geq(x, y))
            },
            Self::Equals(ops) => {
                Self::fold_equals_constants(ops)
            }
            Self::Leq(x, y) => {
                Self::simplify_native_2args("<=", x, y, |x, y| Self::Leq(x, y))
            },
            Self::Less(x, y) => {
                Self::simplify_native_2args("<", x, y, |x, y| Self::Less(x, y))
            }
            Self::Append(list_op, val_op) => {
                Self::simplify_native_2args("append", list_op, val_op, |x, y| Self::Append(x, y))
            },
            Self::Concat(op1, op2) => {
                Self::simplify_native_2args("concat", op1, op2, |x, y| Self::Concat(x, y))
            },
            Self::AsMaxLen(op1, op2) => {
                Self::simplify_native_2args("as-max-len?", op1, op2, |x, y| Self::AsMaxLen(x, y))
            },
            Self::Len(op) => {
                Self::simplify_native_1arg("len", op, |x| Self::Len(x))
            },
            Self::ElementAt(op1, op2) => {
                Self::simplify_native_2args("element-at?", op1, op2, |x, y| Self::ElementAt(x, y))
            },
            Self::IndexOf(op1, op2) => {
                Self::simplify_native_2args("index-of", op1, op2, |x, y| Self::IndexOf(x, y))
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
                match op.simplify()? {
                    Self::Constant(Value::Tuple(data)) => {
                        let v = Self::context_free_clarity_eval_mainnet(vec![
                            SymbolicExpression::atom("get".into()),
                            SymbolicExpression::atom(name.clone()),
                            SymbolicExpression::literal_value(Value::Tuple(data))
                        ])?
                        .ok_or_else(|| Error::Bug("Clarity VM evaluated to None".into()))?;
                        Ok(Self::Constant(v))
                    }
                    Self::TupleCons(fields) => {
                        // lift out of fields
                        let Some((_name, sym)) = fields.iter().find(|(fname, _fop)| *fname == name) else {
                            return Err(Error::Bug(format!("No such tuple key {name} in {fields:?}")));
                        };
                        Ok(*sym.clone())
                    }
                    x => Ok(Self::TupleGet(name, Box::new(x)))
                }
            }
            Self::TupleMerge(op1, op2) => {
                match (op1.simplify()?, op2.simplify()?) {
                    (Self::Constant(Value::Tuple(dest_data)), Self::Constant(Value::Tuple(src_data))) => {
                        let v = Self::context_free_clarity_eval_mainnet(vec![
                            SymbolicExpression::atom("merge".into()),
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
                        match Self::simplify_native_1arg("unwrap-err-panic", Box::new(op), |x| Self::UnwrapPanic(x)) {
                            Err(Error::VM(VmExecutionError::Runtime(RuntimeError::UnwrapFailure, _))) => {
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
                    |op| if let Self::BitwiseAnd(inner) = op { Some(inner) } else { None },
                    |new_ops| Self::BitwiseAnd(new_ops)
                )
            }
            Self::BitwiseOr(ops) => {
                Self::simplify_assoc_variadic(
                    "bit-or",
                    ops,
                    |op| if let Self::BitwiseOr(inner) = op { Some(inner) } else { None },
                    |new_ops| Self::BitwiseOr(new_ops)
                )
            }
            Self::BitwiseXor(ops) => {
                Self::simplify_assoc_variadic(
                    "bit-xor",
                    ops,
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
                            SymbolicExpression::atom("from-consensus-buff?".into()),
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
            Self::Panic => Ok(Self::Panic)
        }
    }

    /// Apply tactics to simplify this operation
    pub fn simplify(self) -> Result<Self, Error> {
        let mut cur = self;
        loop {
            let new = Self::fold_constants(cur.clone())?;
            if new == cur {
                return Ok(new);
            }
            cur = new;
        }
    }
}

/// Predicates over operations over symbols.
/// not all relations are well-defined here; we rely on the Clarity type-checker for this.
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
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

impl Predicate {
    fn format_prefix(func: &str, list: &[Box<Predicate>], f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let pred_strs : Vec<_> = list
            .iter()
            .map(|pred| format!("{}", pred))
            .collect();

        let pred_str = pred_strs.join(" ");

        write!(f, "({func} {pred_str})")
    }
}


impl fmt::Display for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::True => write!(f, "true"),
            Self::False => write!(f, "false"),
            Self::Identity(symop) => write!(f, "{}", symop),
            Self::And(preds) => Self::format_prefix("and", preds, f),
            Self::Or(preds) => Self::format_prefix("or", preds, f),
            Self::Not(pred) => write!(f, "(not {pred})"),
            Self::Equals(symops) => {
                let opstrs : Vec<_> = symops
                    .iter()
                    .map(|s| format!("{}", s))
                    .collect();

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
}

impl MapOp {
    pub fn simplify(self) -> Result<MapOp, Error> {
        match self {
            Self::Get(name, op) => Ok(Self::Get(name, op.simplify()?)),
            Self::Set(name, op, val) => Ok(Self::Set(name, op.simplify()?, val.simplify()?)),
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
    pub symexp: SymbolicExpression
}

impl fmt::Display for TraceItem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} ({}): {}::{}:{}", self.depth, self.symexp.id, &self.contract_id, &self.identifier, self.symexp.span.start_line)
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

/// A symbolic continuation
#[derive(Clone, Debug)]
pub struct Continuation {
    /// Current "function" (really, it identifies what code is being evaluated)
    current_function: Option<String>,
    /// Current symbolic expression being evaluated
    current_symexp: Option<SymbolicExpression>,
    /// Bindings between symbols and their evaluated formulae
    bound_formulae: HashMap<SymId, SymOp>,
    /// The symbolic condition under which this continuation is reachable
    pub predicate: Predicate,
    /// The simplified predicate
    simplified_predicate: Option<Predicate>,
    /// The computed symbolic expression of this continuation
    pub final_formula: SymOp,
    /// The simplified final formula
    simplified_final_formula: Option<SymOp>,
    /// The tx-sender variable, if different from the parent continuation
    tx_sender: Option<PrincipalData>,
    /// The contract-caller variable, if different from the parent continuation
    contract_caller: Option<PrincipalData>,
    /// The tx-sponsor variable
    tx_sponsor: Option<PrincipalData>,
    /// The current contract, if different from the parent continuation
    current_contract: Option<PrincipalData>,
    /// Current Bitcoin block height
    burn_block_height: u64,
    /// Current Stacks block height
    stacks_block_height: u64,
    /// Parent continuation (None means this is the "root" continuation)
    parent: Option<Rc<Continuation>>,
    /// Parent caller continuation (none means this is the "root" continuation).
    /// This is the continuation of the ongoing function being evaluated.
    /// Used for handling early-return.
    caller: Option<Rc<Continuation>>,
    /// data-var formulae prior to evaluation
    pre_vars: Vec<VarOp>,
    /// map formulae prior to evaluation
    pre_maps: Vec<MapOp>,
    /// data-var formulae after evaluation
    pub post_maps: Vec<MapOp>,
    /// map formulae after evaluation
    pub post_vars: Vec<VarOp>,
    /// events generated 
    events: Vec<SymOp>,
    /// whether or not this continuation panicked
    pub panicking: bool,
    /// whether or not this continuation represents an early return
    pub early_return: bool
}

impl fmt::Display for Continuation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        writeln!(f, "Panicked:\n   {}", &self.panicking)?;
        writeln!(f, "Early return:\n   {}", &self.early_return)?;
        writeln!(f, "Predicate:\n   {}", &self.predicate)?;
        if let Some(simplified_predicate) = &self.simplified_predicate {
            writeln!(f, "Simplified predicate:\n   {}", simplified_predicate)?;
        }
        writeln!(f, "Formula:\n   {}", &self.final_formula)?;
        if let Some(simplified_formula) = &self.simplified_final_formula {
            writeln!(f, "Simplified formula:\n   {}", simplified_formula)?;
        }
        writeln!(f, "Bound formulae:")?;
        let mut syms : Vec<_> = self.bound_formulae.keys().collect();
        syms.sort();
        for sym in syms.iter() {
            let formula = self.bound_formulae.get(sym).expect("infallible");
            writeln!(f, "   {} = {}", sym, formula)?;
        }
        if syms.len() == 0 {
            writeln!(f, "   (empty)")?;
        }

        writeln!(f, "tx-sender:\n   {}", &self.get_tx_sender())?;
        writeln!(f, "contract-caller:\n   {}", &self.get_contract_caller())?;
        writeln!(f, "current-contract:\n   {}", &self.get_current_contract())?;
        writeln!(f, "pre-exec vars:")?;
        for varop in self.pre_vars.iter() {
            writeln!(f, "   {}", varop)?;
        }
        if self.pre_vars.len() == 0 {
            writeln!(f, "   (empty)")?;
        }
        writeln!(f, "pre-exec maps:")?;
        for mapop in self.pre_maps.iter() {
            writeln!(f, "   {}", mapop)?;
        }
        if self.post_maps.len() == 0 {
            writeln!(f, "   (empty)")?;
        }

        writeln!(f, "post-exec vars:")?;
        let mut seen_vars : HashSet<&ClarityName> = HashSet::new();
        for varop in self.post_vars.iter().rev() {
            if let VarOp::Set(name, ..) = varop {
                if seen_vars.contains(name) {
                    continue;
                }
                seen_vars.insert(name);
            }
            writeln!(f, "   {}", varop)?;
        }
        if self.post_vars.len() > 0 {
            writeln!(f, "post-exec vars, simplified:")?;
            seen_vars.clear();
            for varop in self.post_vars.iter().rev() {
                if let VarOp::Set(name, ..) = varop {
                    if seen_vars.contains(name) {
                        continue;
                    }
                    seen_vars.insert(name);
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

        writeln!(f, "post-exec maps:")?;
        for mapop in self.post_maps.iter() {
            writeln!(f, "   {}", mapop)?;
        }
        if self.post_maps.len() == 0 {
            writeln!(f, "   (empty)")?;
        }

        writeln!(f, "Symbolic expression:\n   {}", &self.current_symexp.as_ref().map(|s| format!("{}", &s)).unwrap_or("(none)".to_string()))?;
        writeln!(f, "Parent expression:\n   {}", &self.parent.as_ref().map(|p| (*p).current_symexp.as_ref().map(|s| format!("{}", &s)).unwrap_or("(none)".to_string())).unwrap_or("(no parent)".to_string()))?;
        writeln!(f, "Caller expression:\n   {}", &self.caller.as_ref().map(|p| (*p).current_symexp.as_ref().map(|s| format!("{}", &s)).unwrap_or("(none)".to_string())).unwrap_or("(no parent)".to_string()))?;
        Ok(())
    }
}

impl Continuation {
    pub fn root(tx_sender: PrincipalData, contract_caller: PrincipalData, current_contract: PrincipalData) -> Self {
        Self {
            current_function: None,
            current_symexp: None,
            bound_formulae: HashMap::new(),
            predicate: Predicate::True,
            simplified_predicate: None,
            final_formula: SymOp::True(), 
            simplified_final_formula: None,
            tx_sender: Some(tx_sender),
            contract_caller: Some(contract_caller),
            tx_sponsor: None,
            current_contract: Some(current_contract),
            burn_block_height: 0,
            stacks_block_height: 0,
            parent: None,
            caller: None,
            pre_maps: vec![],
            pre_vars: vec![],
            post_maps: vec![],
            post_vars: vec![],
            events: vec![],
            panicking: false,
            early_return: false,
        }
    }

    pub fn from_parent(parent: Rc<Continuation>, function_name: String, symexp: SymbolicExpression) -> Self {
        assert!(!parent.panicking, "BUG: tried to continue from a panic");
        Self {
            current_function: Some(function_name),
            current_symexp: Some(symexp),
            bound_formulae: HashMap::new(),
            predicate: parent.predicate.clone(),
            simplified_predicate: parent.simplified_predicate.clone(),
            final_formula: parent.final_formula.clone(),
            simplified_final_formula: parent.simplified_final_formula.clone(),
            tx_sender: None,
            contract_caller: None,
            tx_sponsor: None,
            current_contract: None,
            burn_block_height: parent.burn_block_height,
            stacks_block_height: parent.stacks_block_height,
            parent: Some(parent.clone()),
            caller: parent.caller.clone(),
            pre_maps: vec![],
            pre_vars: vec![],
            post_maps: vec![],
            post_vars: vec![],
            events: vec![],
            panicking: false,
            early_return: false,
        }
    }
    
    pub fn from_caller(parent: Rc<Continuation>, function_name: String, symexp: SymbolicExpression) -> Self {
        assert!(!parent.panicking, "BUG: tried to continue from a panic");
        let parent_copy = parent.clone();
        let mut cont = Self::from_parent(parent, function_name, symexp);
        cont.caller = Some(parent_copy);
        cont
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
    pub fn lookup_data_var(&self, name: &ClarityName) -> Option<&SymOp> {
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

    /// Find tx-sender
    pub fn get_tx_sender(&self) -> PrincipalData {
        let mut cursor = self;
        loop {
            if let Some(p) = cursor.tx_sender.as_ref() {
                return p.clone();
            }
            if let Some(parent) = cursor.parent.as_ref() {
                cursor = parent;
            }
            else {
                unreachable!("root continuation always constructed with tx-sender, contract-caller, current-contract");
            }
        }
    }

    /// Find contract-caller
    pub fn get_contract_caller(&self) -> PrincipalData {
        let mut cursor = self;
        loop {
            if let Some(p) = cursor.contract_caller.as_ref() {
                return p.clone();
            }
            if let Some(parent) = cursor.parent.as_ref() {
                cursor = parent;
            }
            else {
                unreachable!("root continuation always constructed with tx-sender, contract-caller, current-contract");
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
                unreachable!("root continuation always constructed with tx-sender, contract-caller, current-contract");
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
    pub fn get_tx_sponsor(&self) -> Option<PrincipalData> {
        let mut cursor = self;
        loop {
            if let Some(p) = cursor.contract_caller.as_ref() {
                return Some(p.clone());
            }
            if let Some(parent) = cursor.parent.as_ref() {
                cursor = parent;
            }
            else {
                return None;
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
        let symid : SymId = name.into();
        self.bound_formulae.insert(symid, symop);
    }
    
    /// Set an initial data var formula
    pub fn set_pre_data_var(&mut self, name: &ClarityName, symop: SymOp) {
        self.pre_vars.push(VarOp::Set(name.clone(), SymOp::LoadedDataVariable(name.clone(), Box::new(symop))));
    }

    /// Set a data-var formula consequent to a (var-set ..)
    pub fn set_post_data_var(&mut self, name: &ClarityName, symop: SymOp) {
        self.post_vars.push(VarOp::Set(name.clone(), SymOp::LoadedDataVariable(name.clone(), Box::new(symop))));
    }

    /// Compute a trace of how this continuation arrived to where it did
    pub fn trace(&self) -> Trace {
        let mut cursor_stack = vec![];
        let mut trace_items = vec![];

        let Some(parent) = &self.parent else {
            let trace_item = TraceItem {
                depth: 0,
                identifier: self.current_function.clone().unwrap_or("".to_string()),
                contract_id: self.get_current_contract_id(),
                symexp: self.current_symexp.clone().unwrap_or(SymbolicExpression::atom("root_context__".into()))
            };
            return Trace(vec![trace_item]);
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
                symexp: cursor.current_symexp.clone().unwrap_or(SymbolicExpression::atom("root_context__".into()))
            };
            trace_items.push(trace_item);
        }

        let depth = trace_items.len();
        trace_items.iter_mut().for_each(|t| t.depth = depth - t.depth);
        trace_items.reverse();
        Trace(trace_items)
    }

    /// Roll up this continuation with its ancestors
    pub fn rollup(self) -> Self {
        let mut pre_vars = vec![];
        let mut pre_maps = vec![];
        let mut final_vars = vec![];
        let mut final_maps = vec![];
        let mut events = vec![];
        let tx_sender = self.get_tx_sender();
        let contract_caller = self.get_contract_caller();
        let current_contract = self.get_current_contract();

        let mut cursor_stack = vec![];
        cursor_stack.push(&self);

        let mut end = false;

        while let Some(cursor) = cursor_stack.last() {
            if !end {
                if let Some(parent) = cursor.parent.as_ref() {
                    cursor_stack.push(parent);
                    continue;
                }
            }

            end = true;
            let cursor = cursor_stack.pop().expect("infallible");

            pre_vars.extend(cursor.pre_vars.clone().into_iter());
            pre_maps.extend(cursor.pre_maps.clone().into_iter());
            final_vars.extend(cursor.post_vars.clone().into_iter());
            final_maps.extend(cursor.post_maps.clone().into_iter());
            events.extend(cursor.events.clone().into_iter())
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

        Self {
            post_vars: post_vars,
            post_maps: final_maps,
            pre_vars: pre_vars,
            pre_maps: pre_maps,
            events,
            tx_sender: Some(tx_sender),
            contract_caller: Some(contract_caller),
            current_contract: Some(current_contract),
            parent: None,
            ..self
        }
    }

    pub fn halted(&self) -> bool {
        if self.panicking {
            return true;
        }
        if self.early_return {
            match (self.caller.as_ref(), self.parent.as_ref()) {
                (Some(caller_rc), Some(parent_rc)) => {
                    if let Some(parent_caller_rc) = (*parent_rc).parent.as_ref() {
                        return parent_caller_rc.current_symexp == (*caller_rc).current_symexp;
                    }
                    else {
                        return false;
                    }
                }
                (_, _) => {
                    return false;
                }
            }
        }
        false
    }
}

/// Symbolic execution engine
#[derive(Debug, PartialEq)]
pub struct Symbex {
    datastore: BackingStore,
    contract_context: ContractContext,
    symbols: Vec<SymbolicExpression>,
    typemap: TypeMap, 
}

impl Symbex {
    fn reduce_continuations(conts: Vec<Continuation>) -> Vec<Continuation> {
        let filtered_conts : Vec<_> = conts
           .into_iter()
           .map(|mut c| {
               let p = c.predicate.clone();
               match p.simplify() {
                   Ok(p) => {
                       c.simplified_predicate = Some(p)
                   }
                   Err(e) => {
                       panic!("failed to simplify predicate: {e:?}");
                       // c.panicking = true
                   }
               }
               let f = c.final_formula.clone();
               match f.simplify() {
                   Ok(f) => {
                       c.simplified_final_formula = Some(f)
                   }
                   Err(e) => {
                       panic!("failed to simplify final formula: {e:?}");
                       // c.panicking = true
                   }
               }
               c
           })
           .filter(|c| {
               if let Some(SymOp::Panic) = c.simplified_final_formula {
                   debug!("Continuation always panics:\n{c}");
                   return false;
               }

               if c.simplified_predicate != Some(Predicate::False) {
                   true
               }
               else {
                   debug!("Continuation is unreachable:\n{c}");
                   false
               }
           })
           .collect();

        filtered_conts
    }

    fn eval_variadic_native<I, F>(&self, continuation: Continuation, function_name: &str, args: &[SymbolicExpression], initial: I, fold: F) -> Result<Vec<Continuation>, Error> 
    where
        I: Fn(SymOp) -> SymOp,
        F: Fn(SymOp, SymOp) -> SymOp
    {
        let mut left_conts_opt : Option<Vec<Continuation>> = None;
        let parent_func = continuation.current_function.clone().unwrap_or("".to_string());
        let function_name = format!("{parent_func}/{function_name}");

        let continuation_rc = Rc::new(continuation);
        for symexp in args.iter() {
            if let Some(left_conts) = left_conts_opt.take() {
                let mut right_conts = vec![];
                for left_cont in left_conts.into_iter() {
                    if left_cont.panicking {
                        continue;
                    }
                    let left_cont_formula = left_cont.final_formula.clone();
                    let left_cont_predicate = left_cont.predicate.clone();
                    let mut conts = self.eval(Continuation::from_parent(Rc::new(left_cont), function_name.to_string(), symexp.clone()), symexp)?;
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
                let mut conts = self.eval(Continuation::from_parent(continuation_rc.clone(), function_name.to_string(), symexp.clone()), symexp)?;
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
        let conts_1 = self.eval(Continuation::from_parent(parent_rc, function_name.to_string(), arg1.clone()), &arg1)?;
        
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

            let next = self.eval(Continuation::from_parent(cont_rc, function_name.to_string(), arg2.clone()), &arg2)?;
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

            let next = self.eval(Continuation::from_parent(cont_rc, function_name.to_string(), arg3.clone()), &arg3)?;
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

    /// Destruct (ok x), (err y), or (some z) into x, y, or z
    fn destruct_cons(cons_term: &str, bind_exp: &SymbolicExpression) -> Result<ClarityName, Error> {
        let Some(bind) = bind_exp.match_list() else {
            return Err(Error::Bug(format!("Symbolic expression must be ({cons_term} x); got {:?}", &bind_exp.expr)));
        };
        if bind.len() != 2 {
            return Err(Error::Bug(format!("Symbolic expression does not have two items; expected ({cons_term} x), got {:?}", &bind_exp.expr)));
        };
        let Some(bind_term) = bind.get(0).ok_or_else(|| Error::Bug(format!("Argument 2 does not have two items; expected ({cons_term} x), got {:?}", &bind_exp.expr)))?.match_atom() else {
            return Err(Error::Bug(format!("First item of ({cons_term} x) is not the atom '{cons_term}'; got {:?}", &bind_exp.expr)));
        };
        if bind_term.as_str() != cons_term {
            return Err(Error::Bug(format!("First item of ({cons_term} x) is not the atom '{cons_term}'; got {:?}", &bind_exp.expr)));
        };
        let Some(sym_name) = bind.get(1).ok_or_else(|| Error::Bug(format!("Argument 2 does not have two items; expected ({cons_term} x), got {:?}", &bind_exp.expr)))?.match_atom() else {
            return Err(Error::Bug(format!("Second item of ({cons_term} x) is not the atom 'x'; got {:?}", &bind_exp.expr)));
        };
        Ok(sym_name.clone())
    }

    pub fn eval(&self, mut continuation: Continuation, body: &SymbolicExpression) -> Result<Vec<Continuation>, Error> {
        if continuation.halted() {
            return Ok(vec![continuation]);
        }
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
                    if let Some(function_name) = first.match_atom() {
                        if self.contract_context.functions.get(function_name).is_some() {
                            self.apply_user_function(continuation, function_name, lv.get(1..).unwrap_or(&[]))?
                        }
                        else {
                            // native function application
                            match function_name.as_str() {
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
                                    todo!()
                                },
                                "fold" => {
                                    todo!()
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
                                    let mut len_cont = self.eval(continuation, &new_len_sym)?; 
                                    if len_cont.len() != 1 {
                                        return Err(Error::Bug("as-max-len? length evaluation had more than one continuation".into()));
                                    }
                                    let Some(len_cont) = len_cont.pop() else {
                                        return Err(Error::Bug("as-max-len? length evaluation had more than one continuation".into()));
                                    };

                                    let SymOp::Constant(Value::UInt(x)) = len_cont.final_formula else {
                                        return Err(Error::Bug("as-max-len? length evalauation was not a uint constant".into()));
                                    };

                                    // now we can evaluate the list
                                    let list_conts = self.eval(Continuation::from_parent(Rc::new(len_cont), format!("{function_name}.list"), list_sym.clone()), &list_sym)?;
                                    
                                    let mut new_conts = vec![];
                                    for list_cont in list_conts.into_iter() {
                                        if list_cont.halted() {
                                            new_conts.push(list_cont);
                                            continue;
                                        }

                                        let parent_final_formula = list_cont.final_formula.clone();
                                        let parent_predicate = list_cont.predicate.clone();
                                        let parent_rc = Rc::new(list_cont);

                                        // case 1: the list's length is less than or equal to the
                                        // given length
                                        let mut some_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}.case-some-seq"), body.clone());
                                        some_cont.final_formula = SymOp::ConsSome(Box::new(parent_final_formula.clone()));
                                        some_cont.predicate = parent_predicate.clone().and(Predicate::Leq(SymOp::Len(Box::new(parent_final_formula.clone())), SymOp::Constant(Value::UInt(x))));

                                        // case 2: the list's length is greater than the given
                                        // length
                                        let mut none_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}.case-none-seq"), body.clone());
                                        none_cont.final_formula = SymOp::none();
                                        none_cont.predicate = parent_predicate.and(Predicate::Greater(SymOp::Len(Box::new(parent_final_formula)), SymOp::Constant(Value::UInt(x))));

                                        new_conts.push(some_cont);
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
                                    let conts = self.eval_variadic_native(
                                        continuation,
                                        function_name.as_str(),
                                        lv.get(1..).ok_or_else(|| Error::Bug(format!("Missing arguments to {function_name}")))?,
                                        |initial| SymOp::ListCons(vec![Box::new(initial)]),
                                        |left, right| left.list_cons(right)
                                    )?;
                                    info!("list conts: {:?}", &conts.iter().map(|c| &c.final_formula).collect::<Vec<_>>());
                                    conts
                                }
                                "var-get" => {
                                    let var_name_expr = lv.get(1).ok_or_else(|| Error::Bug("Missing variable name".into()))?;
                                    let Some(var_name) = var_name_expr.match_atom() else {
                                        return Err(Error::Bug(format!("Variable name '{:?}' is not an atom", &var_name_expr)));
                                    };

                                    let Some(formula) = continuation.lookup_data_var(var_name) else {
                                        error!("Faulty continuation looking for '{}': {:#?}", &var_name, &continuation);
                                        return Err(Error::Bug(format!("Unbound formula '{}'", &var_name)));
                                    };

                                    continuation.final_formula = SymOp::LoadedDataVariable(var_name.clone(), Box::new(formula.clone()));
                                    vec![continuation]
                                },
                                "var-set" => {
                                    let var_name_expr = lv.get(1).ok_or_else(|| Error::Bug("Missing variable name".into()))?;
                                    let var_val_expr = lv.get(2).ok_or_else(|| Error::Bug("Missing variable value".into()))?;

                                    let Some(var_name) = var_name_expr.match_atom() else {
                                        return Err(Error::Bug(format!("Variable name '{:?}' is not an atom", &var_name_expr)));
                                    };

                                    let parent_func = continuation.current_function.clone().unwrap_or("".to_string());
                                    let function_name = format!("{parent_func}.var-set");
                                    let mut conts = self.eval(Continuation::from_parent(Rc::new(continuation), function_name, var_val_expr.clone()), var_val_expr)?;
                                    for cont in conts.iter_mut() {
                                        if cont.halted() {
                                            continue;
                                        }
                                        cont.set_post_data_var(var_name, cont.final_formula.clone());

                                        // (var-set ..) always evals to True
                                        cont.final_formula = SymOp::True();
                                    }
                                    conts
                                },
                                "map-get?" => {
                                    todo!()
                                }
                                "map-set" => {
                                    todo!()
                                }
                                "map-insert" => {
                                    todo!()
                                }
                                "map-delete" => {
                                    todo!()
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
                                            let next = self.eval(Continuation::from_parent(parent_rc, format!("{function_name}/.tuple-item-{i}"), value_exp.clone()), value_exp)?;

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

                                   let mut conts = self.eval(Continuation::from_parent(Rc::new(continuation), format!("{function_name}/tuple-get"), sym.clone()), sym)?;
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

                                   let dest_conts = self.eval(Continuation::from_parent(Rc::new(continuation), format!("{function_name}/tuple-merge-dest"), dest_tuple.clone()), dest_tuple)?;
                                   let mut src_conts = vec![];
                                   for dest_cont in dest_conts.into_iter() {
                                       if dest_cont.halted() {
                                           src_conts.push(dest_cont);
                                           continue;
                                       }

                                       let dest_formula = dest_cont.final_formula.clone();
                                       let dest_pred = dest_cont.predicate.clone();

                                       let mut next_conts = self.eval(Continuation::from_parent(Rc::new(dest_cont), format!("{function_name}/tuple-merge-src"), src_tuple.clone()), src_tuple)?;

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
                                    let parent_func = continuation.current_function.clone().unwrap_or("".to_string());
                                    let function_name = format!("{parent_func}.begin");
                                    let mut conts = vec![continuation];
                                    for symexp in lv.get(1..).ok_or_else(|| Error::Bug("Missing symbolic expressions for (begin ..)".into()))?.iter() {
                                        let mut new_conts = vec![];
                                        for cont in conts.into_iter() {
                                            if cont.halted() {
                                                new_conts.push(cont);
                                                continue;
                                            }

                                            let next_conts = self.eval(Continuation::from_parent(Rc::new(cont), function_name.to_string(), symexp.clone()), symexp)?;
                                            new_conts.extend(next_conts.into_iter());
                                        }
                                        conts = new_conts;
                                    }
                                    conts
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
                                    // `(if (is-none y) x y)`
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
                                    let default_conts = self.eval(continuation, &default_sym)?;
                                    for default_cont in default_conts.into_iter() {
                                        if default_cont.halted() {
                                            new_conts.push(default_cont);
                                            continue;
                                        }

                                        let default_final_formula = default_cont.final_formula.clone();
                                        let parent_rc = Rc::new(default_cont);

                                        // evaluate `y` for this `x`'s continuation
                                        let opt_conts = self.eval(Continuation::from_parent(parent_rc, function_name.to_string(), opt_sym.clone()), &opt_sym)?;
                                        for opt_cont in opt_conts.into_iter() {
                                            if opt_cont.halted() {
                                                new_conts.push(opt_cont);
                                                continue;
                                            }
                                            let parent_predicate = opt_cont.predicate.clone();
                                            let final_formula = opt_cont.final_formula.clone();
                                            let parent_rc = Rc::new(opt_cont);

                                            // case 1: this is (some ..)
                                            let mut some_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}.is_some"), opt_sym.clone());
                                            some_cont.predicate = parent_predicate.clone().and(Predicate::IsSome(final_formula.clone()));
                                            some_cont.final_formula = final_formula.clone();

                                            // case 2: this is none
                                            let mut none_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}.is_none"), opt_sym.clone());
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
                                    let cond_conts = self.eval(continuation, &cond_sym)?;
                                    for cond_cont in cond_conts.into_iter() {
                                        if cond_cont.halted() {
                                            new_conts.push(cond_cont);
                                            continue;
                                        }

                                        let cond_formula = cond_cont.final_formula.clone();

                                        // case 1: `x` is true.
                                        // `(asserts! ..)` then evaluates to true, and `x` joins
                                        // the predicate.
                                        let mut cond_true = cond_cont.clone();
                                        let cond_true_pred = cond_true.predicate.clone();
                                        cond_true.predicate = cond_true_pred.clone().and(cond_formula.clone().try_as_predicate()?);
                                        cond_true.final_formula = SymOp::True();

                                        new_conts.push(cond_true);

                                        // case 2: `x` is false.
                                        // evaluate `y`, and set all of its continuations as
                                        // early-return.
                                        let err_conts = self.eval(cond_cont, &err_sym)?;
                                        for mut err_cont in err_conts.into_iter() {
                                            if err_cont.halted() {
                                                new_conts.push(err_cont);
                                                continue;
                                            }

                                            err_cont.predicate = cond_true_pred.clone().and(cond_formula.clone().try_as_predicate()?.not());
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
                                    let cond_conts = self.eval(continuation, &cond_sym)?;

                                    // evaluate `y` from each `x`
                                    for cond_cont in cond_conts.into_iter() {
                                        if cond_cont.halted() {
                                            new_conts.push(cond_cont);
                                            continue;
                                        }

                                        let cond_formula = cond_cont.final_formula.clone();

                                        let parent_rc = Rc::new(cond_cont);
                                        let err_conts = self.eval(Continuation::from_parent(parent_rc, format!("{function_name}.err-case"), err_sym.clone()), &err_sym)?;

                                        for mut err_cont in err_conts.into_iter() {
                                            if err_cont.halted() {
                                                new_conts.push(err_cont);
                                                continue;
                                            }

                                            // case 1: `(is-ok x)` is true or `(is-some x)` is true
                                            let mut ok_cont = err_cont.clone();
                                            let cond_predicate = err_cont.predicate.clone();
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
                                            ok_cont.final_formula = cond_formula.clone();

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
                                    let cond_conts = self.eval(continuation, &cond_sym)?;

                                    // evaluate `y` from each `x`
                                    for cond_cont in cond_conts.into_iter() {
                                        if cond_cont.halted() {
                                            new_conts.push(cond_cont);
                                            continue;
                                        }
                                        let cond_formula = cond_cont.final_formula.clone();

                                        let parent_rc = Rc::new(cond_cont);
                                        let err_conts = self.eval(Continuation::from_parent(parent_rc, format!("{function_name}.err-case"), err_sym.clone()), &err_sym)?;

                                        for mut err_cont in err_conts.into_iter() {
                                            if err_cont.halted() {
                                                new_conts.push(err_cont);
                                                continue;
                                            }

                                            // case 1: `(is-err x)` is true
                                            let mut is_err_cont = err_cont.clone();
                                            let cond_predicate = err_cont.predicate.clone();
                                            is_err_cont.predicate = cond_predicate.clone().and(Predicate::IsErr(cond_formula.clone()));
                                            is_err_cont.final_formula = cond_formula.clone();

                                            // case 2: `(is-err x)` is false
                                            err_cont.predicate = cond_predicate.and(Predicate::IsOkay(cond_formula.clone()));
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
                                    let cond_conts = self.eval(continuation, &cond_sym)?;

                                    for mut cond_cont in cond_conts.into_iter() {
                                        if cond_cont.halted() {
                                            new_conts.push(cond_cont);
                                            continue;
                                        }

                                        let cond_formula = cond_cont.final_formula.clone();

                                        // case 1: `(is-ok x)` is true or `(is-some x)` is true
                                        let mut ok_cont = cond_cont.clone();
                                        let cond_predicate = cond_cont.predicate.clone();
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
                                        ok_cont.final_formula = cond_formula.clone();

                                        // case 2: (is-ok x) (or (is-some x)) is false. This
                                        // panics
                                        cond_cont.predicate = match self.typemap.get_type_expected(&cond_sym) {
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

                                        cond_cont.panicking = true;

                                        new_conts.push(ok_cont);
                                        new_conts.push(cond_cont);
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
                                    let cond_conts = self.eval(continuation, &cond_sym)?;

                                    for mut cond_cont in cond_conts.into_iter() {
                                        if cond_cont.halted() {
                                            new_conts.push(cond_cont);
                                            continue;
                                        }

                                        let cond_formula = cond_cont.final_formula.clone();

                                        // case 1: `(is-err x)` is true
                                        let mut err_cont = cond_cont.clone();
                                        let cond_predicate = cond_cont.predicate.clone();
                                        err_cont.predicate = cond_predicate.clone().and(Predicate::IsErr(cond_formula.clone()));
                                        err_cont.final_formula = cond_formula.clone();

                                        // case 2: (is-ok x) is true This
                                        // panics
                                        cond_cont.predicate = cond_predicate.and(Predicate::IsOkay(cond_formula.clone()));
                                        cond_cont.panicking = true;

                                        new_conts.push(err_cont);
                                        new_conts.push(cond_cont);
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

                                        let cond_conts = self.eval(continuation, &cond_sym)?;
                                        for cond_cont in cond_conts.into_iter() {
                                            if cond_cont.halted() {
                                                new_conts.push(cond_cont);
                                                continue;
                                            }
                                            let parent_pred = cond_cont.predicate.clone();
                                            let cond_formula = cond_cont.final_formula.clone();
                                            let parent_rc = Rc::new(cond_cont);

                                            // case 1: (ok y)
                                            let mut ok_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}/ok-case"), cond_ok_sym.clone());

                                            ok_cont.predicate = parent_pred.clone().and(Predicate::IsOkay(cond_formula.clone()));
                                            ok_cont.bind_symop(&ok_sym_name.clone(), cond_formula.clone());

                                            let ok_conts = self.eval(ok_cont, &cond_ok_sym)?;
                                            new_conts.extend(ok_conts.into_iter());

                                            // case 2: (err y)
                                            let mut err_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}/err-case"), cond_err_sym.clone());

                                            err_cont.predicate = parent_pred.clone().and(Predicate::IsErr(cond_formula.clone()));
                                            err_cont.bind_symop(&err_sym_name.clone(), cond_formula.clone());

                                            let err_conts = self.eval(err_cont, &cond_err_sym)?;
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

                                        let cond_conts = self.eval(continuation, &cond_sym)?;
                                        for cond_cont in cond_conts.into_iter() {
                                            if cond_cont.halted() {
                                                new_conts.push(cond_cont);
                                                continue;
                                            }

                                            let parent_pred = cond_cont.predicate.clone();
                                            let cond_formula = cond_cont.final_formula.clone();
                                            let parent_rc = Rc::new(cond_cont);

                                            // case 1: (some y)
                                            let mut some_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}/some-case"), cond_some_sym.clone());

                                            some_cont.predicate = parent_pred.clone().and(Predicate::IsSome(cond_formula.clone()));
                                            some_cont.bind_symop(&some_sym_name.clone(), cond_formula.clone());

                                            let some_conts = self.eval(some_cont, &cond_some_sym)?;
                                            new_conts.extend(some_conts.into_iter());

                                            // case 2: none
                                            let mut none_cont = Continuation::from_parent(parent_rc.clone(), format!("{function_name}/none-case"), cond_none_sym.clone());

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
                                    let cond_conts = self.eval(Continuation::from_parent(parent_rc, format!("{function_name}/inner"), exp_sym.clone()), &exp_sym)?;
                                    for mut cond_cont in cond_conts.into_iter() {
                                        if cond_cont.halted() {
                                            new_conts.push(cond_cont);
                                            continue;
                                        }

                                        let cond_formula = cond_cont.final_formula.clone();

                                        // case 1: `(is-ok x)` is true or `(is-some x)` is true
                                        let mut ok_cont = cond_cont.clone();
                                        let cond_predicate = cond_cont.predicate.clone();
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
                                        ok_cont.final_formula = cond_formula.clone();

                                        // case 2: (is-ok x) (or (is-some x)) is false
                                        cond_cont.predicate = match self.typemap.get_type_expected(&exp_sym) {
                                            Some(TypeSignature::OptionalType(..)) => {
                                                cond_predicate.and(Predicate::IsNone(cond_formula.clone()))
                                            }
                                            Some(TypeSignature::ResponseType(..)) => {
                                                cond_predicate.and(Predicate::IsErr(cond_formula.clone()))
                                            }
                                            Some(x) => {
                                                return Err(Error::Bug(format!("Did not get (optional ..) or (response ..) type (got {x:?}) for symbol {exp_sym}")));
                                            }
                                            None => {
                                                return Err(Error::Bug(format!("Did not get any type information for symbol {exp_sym}")));
                                            }
                                        };
                                        cond_cont.early_return = true;

                                        new_conts.push(ok_cont);
                                        new_conts.push(cond_cont);
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
                                    todo!()
                                },

                                "define-constant"
                                | "define-private"
                                | "define-read-only"
                                | "define-public"
                                | "define-data-var" => {
                                    // already handled
                                    vec![continuation]
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
                continuation.current_function = Some(function_name);
                match cn.as_str() {
                    "true" => {
                        continuation.final_formula = SymOp::Constant(Value::Bool(true));
                        vec![continuation]
                    }
                    "false" => {
                        continuation.final_formula = SymOp::Constant(Value::Bool(false));
                        vec![continuation]
                    }
                    x => {
                        let symid : SymId = x.into();
                        let Some(formula) = continuation.lookup_formula(&symid) else {
                            error!("Faulty continuation looking for '{}': {:#?}", &symid, &continuation);
                            return Err(Error::Bug(format!("Unbound formula '{}'", &x)));
                        };
                        continuation.final_formula = formula.clone();
                        vec![continuation]
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
        Ok(Self::reduce_continuations(continuations))
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
                let arg_conts = self.eval(Continuation::from_parent(Rc::new(cont), format!("{}/arg[{}]={}", &fq_function, i, &func.arguments[i]), symexp.clone()), symexp)?;
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

            let mut binding_cont = Continuation::from_parent(Rc::new(caller_cont), format!("{}/binding", &fq_function), func.body.clone());
            for (arg_name, symop) in func.arguments.iter().zip(symops.iter()) {
                binding_cont.bind_symop(arg_name, symop.clone());
            }

            let callee_cont = Continuation::from_caller(Rc::new(binding_cont), format!("{}/body", &fq_function), func.body.clone());
            let conts = self.eval(callee_cont, &func.body)?;
            called_conts.extend(conts.into_iter());
        }
        Ok(Self::reduce_continuations(called_conts))
    }

    fn eval_if(&self, continuation: Continuation, predicate_symexp: SymbolicExpression, if_true_symexp: SymbolicExpression, if_false_symexp: SymbolicExpression) -> Result<Vec<Continuation>, Error> {
        let parent_func = continuation.current_function.clone().unwrap_or("".to_string());
        let continuation_rc = Rc::new(continuation);
        let predicate_conts = self.eval(Continuation::from_parent(continuation_rc.clone(), format!("{}/if", &parent_func), predicate_symexp.clone()), &predicate_symexp)?;
        let mut branch_conts = vec![];
        for predicate_cont in predicate_conts.into_iter() {
            if predicate_cont.halted() {
                branch_conts.push(predicate_cont);
                continue;
            }
            let predicate = predicate_cont.final_formula.try_as_predicate()?;

            let mut true_continuation = Continuation::from_parent(continuation_rc.clone(), format!("{}/case-true", &parent_func), if_true_symexp.clone());
            true_continuation.predicate = true_continuation.predicate.clone().and(predicate.clone());

            let if_true_conts = self.eval(true_continuation, &if_true_symexp)?;

            let mut false_continuation = Continuation::from_parent(continuation_rc.clone(), format!("{}/case-false", parent_func), if_false_symexp.clone());
            false_continuation.predicate = false_continuation.predicate.clone().and(predicate.clone().not());

            let if_false_conts = self.eval(false_continuation, &if_false_symexp)?;

            branch_conts.extend(if_true_conts.into_iter());
            branch_conts.extend(if_false_conts.into_iter());
        }
        Ok(branch_conts)
    }

    fn let_bind(&self, continuation: Continuation, let_bindings: &[SymbolicExpression]) -> Result<Vec<Continuation>, Error> {
        if let_bindings.len() != 2 {
            return Err(Error::Bug(format!("Let-binding has wrong length {}", let_bindings.len())));
        };

        let Some(body) = let_bindings.get(1) else {
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

        let function_name = continuation.current_function.clone().unwrap_or("".to_string());

        let mut conts = vec![continuation];
        for (i, (bind_name, body_symexp)) in bind_names_and_bodies.iter().enumerate() {
            let mut new_conts = vec![];
            for cont in conts.into_iter() {
                if cont.halted() {
                    new_conts.push(cont);
                    continue;
                }

                let bind_conts = self.eval(Continuation::from_parent(Rc::new(cont), format!("{}/let-bind[{}].{}", function_name.as_str(), i, bind_name), (*body_symexp).clone()), body_symexp)?;
                for mut bind_cont in bind_conts.into_iter() {
                    if bind_cont.halted() {
                        new_conts.push(bind_cont);
                        continue;
                    }

                    // the computed binding can be used by a subsequent binding formula
                    bind_cont.bind_symop(bind_name, bind_cont.final_formula.clone());
                    new_conts.push(bind_cont);
                }
            }
            conts = new_conts;
        }

        let mut bound_conts = vec![];
        for bind_cont in conts.into_iter() {
            if bind_cont.halted() {
                bound_conts.push(bind_cont);
                continue;
            }

            let bound_cont = Continuation::from_parent(Rc::new(bind_cont), format!("{}/let-body", function_name.as_str()), body.clone());
            let conts = self.eval(bound_cont, body)?;
            bound_conts.extend(conts.into_iter());
        }
        Ok(Self::reduce_continuations(bound_conts))
    }

    pub fn from_contract(contract_id: QualifiedContractIdentifier, code: &str, sponsor: Option<PrincipalData>) -> Result<Self, Error> {
        let mut datastore = BackingStore::new();
        let ast = ast::parse_ast(&contract_id, code)?;
        let mut analysis = ast::make_contract_analysis_from_ast(&mut datastore, &contract_id, &ast)?;
        let contract_context = ast::make_contract_context_from_ast(&mut datastore, &contract_id, code, &ast, sponsor.clone())?;
      
        let Some(typemap) = analysis.type_map.take() else {
            return Err(Error::Bug("No typemap computed".into()));
        };

        let symbex = Symbex {
            datastore,
            contract_context,
            symbols: ast.expressions,
            typemap
        };
        Ok(symbex)
    }

    pub fn eval_all(&mut self) -> Result<Vec<Continuation>, Error> {
        let tx_sender = PrincipalData::Standard(StandardPrincipalData::transient());
        let contract_caller = tx_sender.clone();
        let current_contract = PrincipalData::Contract(self.contract_context.contract_identifier.clone());

        let mut root_continuation = Continuation::root(tx_sender, contract_caller, current_contract);
        
        for (const_name, const_value) in self.contract_context.variables.iter() {
            root_continuation.bind_constant(const_name, const_value);
        }

        for (var_name, var_metadata) in self.contract_context.meta_data_var.iter() {
            root_continuation.set_pre_data_var(var_name, SymOp::Variable(Sym::from_name_and_type_signature(var_name, &var_metadata.value_type)));
        }

        let mut conts = vec![root_continuation];
        for sym in self.symbols.iter() {
            let mut next = vec![];
            for cont in conts.into_iter() {
                let cont_rc = Rc::new(cont);
                let next_conts = self.eval(Continuation::from_parent(cont_rc.clone(), "".to_string(), sym.clone()), sym)?;
                assert!(next_conts.len() > 0, "No continuation produced from {cont_rc:?}");
                next.extend(next_conts.into_iter());
            }
            conts = next;
        }

        Ok(Self::reduce_continuations(conts))
    }
}

