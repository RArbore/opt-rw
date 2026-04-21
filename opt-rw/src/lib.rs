use lalrpop_util::lalrpop_mod;

pub mod ast;
pub mod ssa;

lalrpop_mod!(pub grammar);
