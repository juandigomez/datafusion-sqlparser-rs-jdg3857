use log::debug;

use crate::dialect::{Dialect, Precedence};
use crate::keywords::Keyword;
use crate::parser::{Parser, ParserError};
use crate::tokenizer::Token;

/// A [`Dialect`] for the Cypher query language (used by Neo4j, etc.)
#[derive(Debug)]
pub struct CypherDialect {}

impl Dialect for CypherDialect {
    /// Cypher identifiers are generally unquoted unless using backticks:
    /// Example: MATCH (n:`Person`) RETURN n.name
    fn identifier_quote_style(&self, _identifier: &str) -> Option<char> {
        Some('`')
    }

    fn is_delimited_identifier_start(&self, ch: char) -> bool {
        ch == '`'
    }

    fn is_identifier_start(&self, ch: char) -> bool {
        ch.is_alphabetic() || ch == '_' || !ch.is_ascii()
    }

    fn is_identifier_part(&self, ch: char) -> bool {
        ch.is_alphanumeric() || ch == '_' || ch == '.' || !ch.is_ascii()
    }

    /// Cypher supports Unicode string literals
    fn supports_unicode_string_literal(&self) -> bool {
        true
    }

    /// Cypher uses operators like =, <>, <, >, <=, >=, +, -, *, /, =~
    fn is_custom_operator_part(&self, ch: char) -> bool {
        matches!(ch, '=' | '<' | '>' | '+' | '-' | '*' | '/' | '~' | '!')
    }

    /// Define basic precedence (Cypher is not fully operator-precedence based like SQL)
    fn get_next_precedence(&self, parser: &Parser) -> Option<Result<u8, ParserError>> {
        let token = parser.peek_token();
        debug!("get_next_precedence() {token:?}");

        match token.token {
            Token::Eq | Token::Neq | Token::Lt | Token::Gt | Token::LtEq | Token::GtEq => {
                Some(Ok(50)) // arbitrary, equality-like ops
            }
            Token::Plus | Token::Minus => Some(Ok(80)),
            Token::Mul | Token::Div => Some(Ok(90)),
            _ => None,
        }
    }

    fn prec_value(&self, prec: Precedence) -> u8 {
        match prec {
            Precedence::Eq => 50,
            Precedence::PlusMinus => 80,
            Precedence::MulDivModOp => 90,
            _ => 10,
        }
    }

    /// Cypher does not use GROUP BY or FILTER in standard form
    fn supports_group_by_expr(&self) -> bool {
        false
    }

    fn supports_filter_during_aggregation(&self) -> bool {
        false
    }

    /// Cypher does allow nested comments like /* ... */
    fn supports_nested_comments(&self) -> bool {
        true
    }

    fn supports_string_escape_constant(&self) -> bool {
        true
    }

    /// Cypher identifiers can include Unicode, e.g. `MATCH (π)`
    fn supports_numeric_literal_underscores(&self) -> bool {
        true
    }
}
