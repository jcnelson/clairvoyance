// Copyright (C) 2026 Trust Machines
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

use clarity_types::Value;
use clarity_types::ClarityName;
use clarity_types::types::TypeSignature;
use clarity_types::types::{PrincipalData, StandardPrincipalData};

/// Symbol ID
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct SymId(String);

/// Value symbols
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Sym {
    Literal(Value),
    Int(SymId),
    UInt(SymId),
    Bool(SymId),
    Sequence(SymId, TypeSignature),
    Principal(SymId),
    Tuple(SymId, TypeSignature),
    Optional(SymId, TypeSignature),
    Response(SymId, TypeSignature),
    CallableContract(SymId)
}

/// computations over symbols.
/// not all relations are well-defined here; we rely on the Clarity type-checker for this.
#[derive(Debug, PartialEq, Clone)]
pub enum SymOp {
    Identity(Sym),
    Add(Vec<Box<SymOp>>),
    Subtract(Vec<Box<SymOp>>),
    Multiply(Vec<Box<SymOp>>),
    Divide(Vec<Box<SymOp>>),
    ToInt(Box<SymOp>),
    ToUInt(Box<SymOp>),
    Modulo(Box<SymOp>),
    Power(Box<SymOp>),
    Sqrti(Box<SymOp>),
    Log2(Box<SymOp>),
    Append(Box<SymOp>, Box<SymOp>),
    Concat(Box<SymOp>, Box<SymOp>),
    Len(Box<SymOp>),
    ElementAt(Box<SymOp>),
    IndexOf(Box<SymOp>),
    BuffToIntLe(Box<SymOp>),
    BuffToUIntLe(Box<SymOp>),
    BuffToIntBe(Box<SymOp>),
    BuffToUintBe(Box<SymOp>),
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
    TupleCons(ClarityName, Vec<(ClarityName, Box<SymOp>)>),
    TupleGet(ClarityName, ClarityName),
    TupleMerge(ClarityName, Box<SymOp>),
    Hash160(Box<SymOp>),
    Sha256(Box<SymOp>),
    Sha512Trunc256(Box<SymOp>),
    Keccak256(Box<SymOp>),
    Secp256k1Recover(Box<SymOp>, Box<SymOp>),
    Secp256k1Verify(Box<SymOp>, Box<SymOp>, Box<SymOp>),
    ConsError(Box<SymOp>),
    ConsOkay(Box<SymOp>),
    ConsSome(Box<SymOp>),
    GetTokenBalance(ClarityName, Box<SymOp>),
    GetNftOwner(ClarityName),
    TransferToken(ClarityName, Box<SymOp>, Box<SymOp>, Box<SymOp>),
    TransferNft(ClarityName, Box<SymOp>, Box<SymOp>, Box<SymOp>),
    MintToken(ClarityName, Box<SymOp>, Box<SymOp>),
    MintNft(ClarityName, Box<SymOp>, Box<SymOp>),
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
    BitwiseNot(Vec<Box<SymOp>>),
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
    RestrictAssets(Box<SymOp>),
    AllowanceWithStx(Box<SymOp>),
    AllowanceWithFt(Box<SymOp>, ClarityName, Box<SymOp>),
    AllowanceWithNft(Box<SymOp>, ClarityName, Box<SymOp>),
    AllowanceWithStacking(Box<SymOp>),
    Secp256r1Verify(Box<SymOp>, Box<SymOp>, Box<SymOp>),
}

/// Predicates over symbols.
/// not all relations are well-defined here; we rely on the Clarity type-checker for this.
#[derive(Debug, PartialEq, Clone)]
pub enum Predicate {
    Identity,
    And(Vec<Box<Predicate>>),
    Or(Vec<Box<Predicate>>),
    Not(Box<Predicate>),
    Geq(SymOp, SymOp),
    Leq(SymOp, SymOp),
    Less(SymOp, SymOp),
    Greater(SymOp, SymOp),
    Equals(SymOp, SymOp), 
}

impl Predicate {
    pub fn and(self, p: Box<Predicate>) -> Self {
        match self {
            Self::And(mut ps) => {
                ps.push(p);
                Self::And(ps)
            },
            x => {
                let ps = vec![Box::new(x), p];
                Self::And(ps)
            }
        }
    }

    pub fn or(self, p: Box<Predicate>) -> Self {
        match self {
            Self::Or(mut ps) => {
                ps.push(p);
                Self::Or(ps)
            },
            x => {
                let ps = vec![Box::new(x), p];
                Self::Or(ps)
            }
        }
    }

    pub fn not(self) -> Self {
        Self::Not(Box::new(self))
    }
}

/// Bound variables whose values are read as part of execution
#[derive(Debug, PartialEq, Clone)]
pub struct Context {
    pub tx_sender: Sym,
    pub contract_caller: Sym,
    pub current_contract: Sym,
    pub burn_block_height: Sym,
    pub stacks_block_height: Sym,

    /* TODO: add them all */
}

impl Context {
    pub fn new() -> Self {
        Self {
            tx_sender: Sym::Literal(Value::Principal(PrincipalData::Standard(StandardPrincipalData::transient()))),
            contract_caller: Sym::Literal(Value::Principal(PrincipalData::Standard(StandardPrincipalData::transient()))),
            current_contract: Sym::Literal(Value::Principal(PrincipalData::Standard(StandardPrincipalData::transient()))),
            burn_block_height: Sym::Literal(Value::UInt(0)),
            stacks_block_height: Sym::Literal(Value::UInt(0)),
        }
    }
}

/// Symbolic execution engine
#[derive(Debug, PartialEq, Clone)]
pub struct Symbex {
    pub context: Context,
    pub predicates: Vec<Predicate>,
    active_predicate: usize,
}

impl Symbex {
    pub fn new() -> Self {
        Self {
            context: Context::new(),
            predicates: vec![Predicate::Identity],
            active_predicate: 0
        }
    }
}

