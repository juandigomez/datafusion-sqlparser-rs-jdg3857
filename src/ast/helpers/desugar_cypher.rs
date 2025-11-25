// Licensed to the Apache Software Foundation (ASF) under one
// or more contributor license agreements.  See the NOTICE file
// distributed with this work for additional information
// regarding copyright ownership.  The ASF licenses this file
// to you under the Apache License, Version 2.0 (the
// "License"); you may not use this file except in compliance
// with the License.  You may obtain a copy of the License at
//
//   http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing,
// software distributed under the License is distributed on an
// "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
// KIND, either express or implied.  See the License for the
// specific language governing permissions and limitations
// under the License.

//! Cypher query desugaring utilities
//! 
//! Functions to transform Cypher CREATE patterns into SQL INSERT statements

use crate::ast::*;
use crate::ast::helpers::attached_token::AttachedToken;
use crate::tokenizer::TokenWithSpan;
use crate::tokenizer::Whitespace;
use crate::parser::{ParserError};

pub struct Desugarer;

impl Desugarer {

    // Helper function to extract alias from TableFactor
    fn extract_alias(table: &TableFactor) -> Result<Ident, ParserError> {
        match table {
            TableFactor::Table { alias: Some(a), .. } => Ok(a.name.clone()),
            _ => Err(ParserError::ParserError("Table must have an alias".to_string())),
        }
    }

    // Helper function to create a table factor with common defaults
    fn create_table_factor(table_name: &str, alias: Option<Ident>) -> TableFactor {
        TableFactor::Table {
            name: ObjectName(vec![ObjectNamePart::Identifier(Ident::new(table_name))]),
            alias: alias.map(|name| TableAlias { name, columns: vec![] }),
            args: None,
            with_hints: vec![],
            version: None,
            with_ordinality: false,
            partitions: vec![],
            json_path: None,
            sample: None,
            index_hints: vec![],
        }
    }

    // Helper function to combine multiple expressions with AND operator
    fn combine_filters_with_and(filters: Vec<Expr>) -> Option<Expr> {
        if filters.is_empty() {
            return None;
        }
        
        let mut combined = filters[0].clone();
        for expr in filters.iter().skip(1) {
            combined = Expr::BinaryOp {
                left: Box::new(combined),
                op: BinaryOperator::And,
                right: Box::new(expr.clone()),
            };
        }
        Some(combined)
    }

    // Helper function to create edge table with automatic alias generation
    fn create_edge_table(relationship: &RelationshipPattern, edge_counter: &mut i32) -> TableFactor {
        let alias = if let Some(ref var) = relationship.details.variable {
            var.clone()
        } else {
            let alias = Ident::new(format!("e{}", edge_counter));
            *edge_counter += 1;
            alias
        };
        Self::create_table_factor("edges", Some(alias))
    }

    // Helper function to create join condition
    fn create_join_condition(left_table: Ident, left_col: &str, right_table: Ident, right_col: &str) -> Expr {
        Expr::BinaryOp {
            left: Box::new(Expr::CompoundIdentifier(vec![left_table, Ident::new(left_col)])),
            op: BinaryOperator::Eq,
            right: Box::new(Expr::CompoundIdentifier(vec![right_table, Ident::new(right_col)])),
        }
    }

    // Helper function to create a subquery that selects node ID from new_nodes CTE
    fn create_node_id_subquery(node: &NodePattern) -> Result<Expr, ParserError> {
        let filter = Self::desugar_properties_map(
            if let Some(Expr::Map(m)) = &node.properties { m.clone() } else {
                return Err(ParserError::ParserError("Node must have properties to match".to_string()));
            },
            &Ident::new("new_nodes")
        )?;

        Ok(Expr::Subquery(Box::new(Query {
            with: None,
            body: Box::new(SetExpr::Select(Box::new(Select {
                select_token: AttachedToken::empty(),
                distinct: None,
                top: None,
                top_before_distinct: false,
                projection: vec![SelectItem::UnnamedExpr(Expr::Identifier(Ident::new("Id")))],
                exclude: None,
                into: None,
                from: vec![TableWithJoins {
                    relation: Self::create_table_factor("new_nodes", None),
                    joins: vec![],
                }],
                lateral_views: vec![],
                prewhere: None,
                selection: filter,
                group_by: GroupByExpr::Expressions(vec![], vec![]),
                cluster_by: vec![],
                distribute_by: vec![],
                sort_by: vec![],
                having: None,
                named_window: vec![],
                window_before_qualify: false,
                qualify: None,
                value_table_mode: None,
                connect_by: None,
                flavor: SelectFlavor::Standard,
            }))),
            order_by: None,
            limit_clause: None,
            for_clause: None,
            settings: None,
            format_clause: None,
            pipe_operators: vec![],
            fetch: None,
            locks: vec![],
        })))
    }

    /// Desugar Cypher property map into JSON string format for INSERT statements
    fn properties_to_string(properties: Map) -> Result<String, ParserError>{
        let entries: Vec<String> = properties.entries.into_iter()
                            .map(|kv| {
                                // Format key as JSON string
                                let key_str = match *kv.key {
                                    Expr::Identifier(id) => format!("\"{}\"", id.value),
                                    _ => format!("\"{}\"", kv.key),
                                };
                                
                                // Format value as JSON
                                let value_str = match *kv.value {
                                    Expr::Value(val_with_span) => {
                                        match val_with_span.value {
                                            Value::SingleQuotedString(s) => format!("\"{}\"", s),
                                            Value::DoubleQuotedString(s) => format!("\"{}\"", s),
                                            Value::Number(n, _) => n.to_string(),
                                            Value::Boolean(b) => b.to_string().to_lowercase(),
                                            Value::Null => "null".to_string(),
                                            _ => format!("\"{}\"", val_with_span),
                                        }
                                    }
                                    _ => format!("\"{}\"", kv.value),
                                };
                                
                                format!("{}: {}", key_str, value_str)
                            })
                            .collect();
        Ok(format!("{{{}}}", entries.join(", ")))
    }

    /// Desugar Cypher property map into WHERE clause expression with table alias
    fn desugar_properties_map(properties: Map, table_alias: &Ident) -> Result<Option<Expr>, ParserError>{

        let mut entries: Vec<Expr> = Vec::new();
        for entry in &properties.entries {
            // Create json_extract(p.Properties, '$.name') expression
            let left_expr = Expr::Function(Function {
                name: ObjectName(vec![ObjectNamePart::Identifier(Ident::new("json_extract"))]),
                parameters: FunctionArguments::None,
                args: FunctionArguments::List(FunctionArgumentList {
                    duplicate_treatment: None,
                    args: vec![
                        FunctionArg::Unnamed(FunctionArgExpr::Expr(
                            Expr::CompoundIdentifier(vec![
                                table_alias.clone(),
                                Ident::new("Properties"),
                            ])
                        )),
                        FunctionArg::Unnamed(FunctionArgExpr::Expr(
                            Expr::Value(Value::SingleQuotedString(format!("$.{}", entry.key)).into())
                        )),
                    ],
                    clauses: vec![],
                }),
                filter: None,
                null_treatment: None,
                over: None,
                within_group: vec![],
                uses_odbc_syntax: false,
            });
            
            // Convert the value, handling double-quoted strings by converting to single-quoted
            let right_value = if let Expr::Value(v) = entry.value.as_ref() {
                match &v.value {
                    Value::DoubleQuotedString(s) => {
                        Box::new(Expr::Value(Value::SingleQuotedString(s.clone()).into()))
                    },
                    _ => entry.value.clone()
                }
            } else {
                entry.value.clone()
            };
            
            let value_expr = Expr::BinaryOp {
                left: Box::new(left_expr),
                op: BinaryOperator::Eq,
                right: right_value,
            };
            entries.push(value_expr);
        }
        
        // Combine all expressions with AND
        if entries.is_empty() {
            return Ok(None);
        }
        
        let mut combined = entries[0].clone();
        for expr in entries.iter().skip(1) {
            combined = Expr::BinaryOp {
                left: Box::new(combined),
                op: BinaryOperator::And,
                right: Box::new(expr.clone()),
            };
        }
        
        Ok(Some(combined))
    }

    fn desugar_filters(properties: Option<Expr>, initial: Option<&Ident>, table_alias: &Ident) -> Result<Option<Expr>, ParserError> {
        
        let label_expr = if let Some(label) = initial {
            Some(Expr::BinaryOp {
                left: Box::new(Expr::CompoundIdentifier(vec![
                    table_alias.clone(),
                    Ident::new("Label"),
                ])),
                op: BinaryOperator::Eq,
                right: Box::new(Expr::Value(Value::SingleQuotedString(label.to_string()).into())),
            })
        } else {
            None
        };

        if let Some(Expr::Map(map)) = properties {
            let properties_expr = Self::desugar_properties_map(map.clone(), table_alias)?;

            let combined_expr = match (label_expr, properties_expr) {
                (Some(label), Some(props)) => {
                    Some(Expr::BinaryOp {
                        left: Box::new(label),
                        op: BinaryOperator::And,
                        right: Box::new(props),
                    })
                }
                (Some(label), None) => Some(label),
                (None, Some(props)) => Some(props),
                (None, None) => None,
            };

            Ok(combined_expr)            
        } else {
            Ok(label_expr)
        }
    }

    fn desugar_node_filter(node: NodePattern, table_alias: &Ident) -> Result<Option<Expr>, ParserError> {

        let filter = Self::desugar_filters(node.properties.clone(), node.labels.first(), table_alias)?;
        Ok(filter)
    }

    fn desugar_relationship_filter(relationship: RelationshipPattern, table_alias: &Ident) -> Result<Option<Expr>, ParserError> {

        if relationship.details.length.is_some() {
            return Err(ParserError::ParserError("Relationship length is not supported for Desugaring".to_string()));
        }
        let filter = Self::desugar_filters(relationship.details.properties.clone(), relationship.details.types.first(), table_alias)?;
        Ok(filter)
    }

    fn desugar_where(where_clause: CypherWhereClause) -> Result<Expr, ParserError> {

        match where_clause.expr{
            Expr::BinaryOp {left, op, right } => {
                match op {
                    BinaryOperator::And | BinaryOperator::Or => {
                        let left_expr = Self::desugar_where(CypherWhereClause { expr: *left })?;
                        let right_expr = Self::desugar_where(CypherWhereClause { expr: *right })?;
                        return Ok(Expr::BinaryOp {
                            left: Box::new(left_expr),
                            op,
                            right: Box::new(right_expr),
                        });
                    },
                        _ => {},
                }
                match left.as_ref(){
                    Expr::CompoundIdentifier(idents) => {
                        if idents.len() !=2 {
                            return Err(ParserError::ParserError("WHERE clause identifier not valid".to_string()));
                        }
                        
                        // Create json_extract(p.Properties, '$.name') expression
                        let key_expr = Expr::Function(Function {
                            name: ObjectName(vec![ObjectNamePart::Identifier(Ident::new("json_extract"))]),
                            parameters: FunctionArguments::None,
                            args: FunctionArguments::List(FunctionArgumentList {
                                duplicate_treatment: None,
                                args: vec![
                                    FunctionArg::Unnamed(FunctionArgExpr::Expr(
                                        Expr::CompoundIdentifier(vec![
                                            idents[0].clone(),
                                            Ident::new("Properties"),
                                        ])
                                    )),
                                    FunctionArg::Unnamed(FunctionArgExpr::Expr(
                                        Expr::Value(Value::SingleQuotedString(format!("$.{}", idents[1])).into())
                                    )),
                                ],
                                clauses: vec![],
                            }),
                            filter: None,
                            null_treatment: None,
                            over: None,
                            within_group: vec![],
                            uses_odbc_syntax: false,
                        });
                        
                        Ok(Expr::BinaryOp {
                            left: Box::new(key_expr),
                            op,
                            right,
                        })
                    },
                    _ => Err(ParserError::ParserError("WHERE clause left expression must be a property access".to_string())),
                }
            },
            _ => Err(ParserError::ParserError("Only binary operations are supported in WHERE clause desugaring".to_string())),
        }
    }

    fn create_table_factor_from_node(node: NodePattern, node_counter: &mut i32) -> Result<TableFactor, ParserError> {
        let table_alias = if let Some(ref var) = node.variable {
            var.clone()
        } else {
            let alias = Ident::new(format!("n{}", node_counter));
            *node_counter += 1;
            alias
        };
        Ok(Self::create_table_factor("nodes", Some(table_alias)))
    }

    fn desugar_nodes_only_for_match(pattern: Pattern) -> Result<Select, ParserError> {
        let mut filters = Vec::new();
        let mut first_table: Option<TableWithJoins> = None;
        let mut node_counter = 1;

        // Process each node pattern to build FROM clause and WHERE filters
        for (idx, pattern_part) in pattern.parts.iter().enumerate() {
            match &pattern_part.anon_pattern_part {
                PatternElement::Simple(simple_element) => {
                    let table_factor = Self::create_table_factor_from_node(simple_element.node.clone(), &mut node_counter)?;
                    let table_alias = Self::extract_alias(&table_factor)?;

                    // Build FROM clause with explicit CROSS JOINs
                    if idx == 0 {
                        first_table = Some(TableWithJoins {
                            relation: table_factor,
                            joins: vec![],
                        });
                    } else if let Some(ref mut first) = first_table {
                        first.joins.push(Join {
                            relation: table_factor,
                            global: false,
                            join_operator: JoinOperator::CrossJoin(JoinConstraint::None),
                        });
                    }

                    if let Some(filter) = Self::desugar_node_filter(simple_element.node.clone(), &table_alias)? {
                        filters.push(filter);
                    }
                }
                _ => {
                    return Err(ParserError::ParserError(
                        "Only simple node patterns are supported in MATCH clause".to_string()
                    ));
                }
            }
        }

        let selection = Self::combine_filters_with_and(filters);

        // Build the SELECT statement
        let from_tables = if let Some(first) = first_table {
            vec![first]
        } else {
            vec![]
        };

        Ok(Select {
            select_token: AttachedToken::empty(),
            distinct: None,
            top: None,
            top_before_distinct: false,
            projection: vec![SelectItem::Wildcard(WildcardAdditionalOptions::default())],
            exclude: None,
            into: None,
            from: from_tables,
            lateral_views: vec![],
            prewhere: None,
            selection,
            group_by: GroupByExpr::Expressions(vec![], vec![]),
            cluster_by: vec![],
            distribute_by: vec![],
            sort_by: vec![],
            having: None,
            named_window: vec![],
            window_before_qualify: false,
            qualify: None,
            value_table_mode: None,
            connect_by: None,
            flavor: SelectFlavor::Standard,
        })        
    }

    fn desugar_pattern_for_match(pattern: Pattern) -> Result<Select, ParserError> {
        let mut first_table: Option<TableWithJoins> = None;
        let mut edge_filters = Vec::new();
        let mut node_filters = Vec::new();
        let mut node_counter = 1;
        let mut edge_counter = 1;

        // Process all pattern parts
        for pattern_part in &pattern.parts {
            let simple_element = match &pattern_part.anon_pattern_part {
                PatternElement::Simple(s) => s,
                PatternElement::Nested(_) => {
                    return Err(ParserError::ParserError(
                        "Nested pattern elements are not supported in MATCH clause".to_string()
                    ));
                }
            };

            // Start with the first node in the pattern
            let mut current_node = Self::create_table_factor_from_node(simple_element.node.clone(), &mut node_counter)?;
            let current_alias = Self::extract_alias(&current_node)?;
            let first_node_filter = Self::desugar_node_filter(simple_element.node.clone(), &current_alias)?;
            if let Some(combined_expr) = first_node_filter {
                node_filters.push(combined_expr);
            }

            // Process each relationship chain element
            for chain_elem in &simple_element.chain {
                let edge_table = Self::create_edge_table(&chain_elem.relationship, &mut edge_counter);
                let rel_alias = Self::extract_alias(&edge_table)?;
                
                if let Some(filter) = Self::desugar_relationship_filter(chain_elem.relationship.clone(), &rel_alias)? {
                    edge_filters.push(filter);
                }

                let target_node = Self::create_table_factor_from_node(chain_elem.node.clone(), &mut node_counter)?;
                let target_alias = Self::extract_alias(&target_node)?;
                if let Some(filter) = Self::desugar_node_filter(chain_elem.node.clone(), &target_alias)? {
                    node_filters.push(filter);
                }

                // Start with first edge table in FROM clause
                if first_table.is_none() {
                    first_table = Some(TableWithJoins {
                        relation: edge_table.clone(),
                        joins: vec![],
                    });
                    
                    // Join the source node
                    if let Some(ref mut first) = first_table {
                        let source_alias = Self::extract_alias(&current_node)?;
                        let source_join_condition = Self::create_join_condition(rel_alias.clone(), "SourceId", source_alias, "Id");
                        first.joins.push(Join {
                            relation: current_node.clone(),
                            global: false,
                            join_operator: JoinOperator::Join(JoinConstraint::On(source_join_condition)),
                        });
                    }
                } else {
                    // For subsequent edges in the chain, join the edge first
                    if let Some(ref mut first) = first_table {
                        let source_alias = Self::extract_alias(&current_node)?;
                        let edge_join_condition = Self::create_join_condition(rel_alias.clone(), "SourceId", source_alias, "Id");
                        first.joins.push(Join {
                            relation: edge_table.clone(),
                            global: false,
                            join_operator: JoinOperator::Join(JoinConstraint::On(edge_join_condition)),
                        });
                    }
                }

                // Join target node: r.TargetId = b.Id
                if let Some(ref mut first) = first_table {
                    let target_join_condition = Self::create_join_condition(rel_alias, "TargetId", target_alias, "Id");
                    first.joins.push(Join {
                        relation: target_node.clone(),
                        global: false,
                        join_operator: JoinOperator::Join(JoinConstraint::On(target_join_condition)),
                    });
                }

                // Update current node to be the target for the next iteration
                current_node = target_node;
            }
        }

        // Combine filters: edge filters first, then node filters
        edge_filters.extend(node_filters);
        let selection = Self::combine_filters_with_and(edge_filters);

        Ok(Select {
            select_token: AttachedToken::empty(),
            distinct: None,
            top: None,
            top_before_distinct: false,
            projection: vec![SelectItem::Wildcard(WildcardAdditionalOptions::default())],
            exclude: None,
            into: None,
            from: first_table.into_iter().collect(),
            lateral_views: vec![],
            prewhere: None,
            selection,
            group_by: GroupByExpr::Expressions(vec![], vec![]),
            cluster_by: vec![],
            distribute_by: vec![],
            sort_by: vec![],
            having: None,
            named_window: vec![],
            window_before_qualify: false,
            qualify: None,
            value_table_mode: None,
            connect_by: None,
            flavor: SelectFlavor::Standard,
        })
    }

    /// Desugar simple node-only CREATE patterns into INSERT INTO nodes statement.
    /// Handles patterns like: CREATE (a:Person {name: 'Alice'}), (b:Person {name: 'Bob'})
    fn desugar_nodes_only_for_create(create_clause: CypherCreateClause) -> Result<Statement, ParserError> {
        let mut columns = Vec::new();
        let mut values = Vec::new();

        for pattern_part in &create_clause.pattern.parts {
            match &pattern_part.anon_pattern_part {
                PatternElement::Simple(simple_element) => {
                    let mut node_values = Vec::new();
                    
                    if let Some(label) = simple_element.node.labels.first() {
                        let label_expr = Expr::Value(Value::SingleQuotedString(label.to_string()).into());
                        if !columns.contains(&Ident::new("Label")) {
                            columns.push(Ident::new("Label"));
                        }
                        node_values.push(label_expr);
                    }
                    
                    if let Some(Expr::Map(map)) = &simple_element.node.properties {
                        let properties_str = Self::properties_to_string(map.clone())?;
                        if !columns.contains(&Ident::new("Properties")) {
                            columns.push(Ident::new("Properties"));
                        }
                        node_values.push(Expr::Value(Value::SingleQuotedString(properties_str).into()));
                        values.push(node_values);
                    }
                }
                _ => {
                    return Err(ParserError::ParserError(
                        "Only simple node patterns are supported in CREATE clause for desugaring to INSERT statements.".to_string()
                    ));
                }
            }
        }

        let values_clause = Values {
            explicit_row: false,
            value_keyword: false,
            rows: values,
        };
        
        let source = Some(Box::new(Query {
            with: None,
            body: Box::new(SetExpr::Values(values_clause)),
            order_by: None,
            limit_clause: None,
            for_clause: None,
            settings: None,
            format_clause: None,
            pipe_operators: vec![],
            fetch: None,
            locks: vec![],
        }));

        let table_object = TableObject::TableName(ObjectName(
            vec![ObjectNamePart::Identifier(Ident::new("nodes"))]
        ));

        Ok(Statement::Insert(Insert {
            insert_token: AttachedToken::empty(),
            or: None,
            table: table_object,
            table_alias: None,
            ignore: false,
            into: true,
            overwrite: false,
            partitioned: None,
            columns,
            after_columns: vec![],
            source,
            assignments: vec![],
            has_table_keyword: false,
            on: None,
            returning: None,
            replace_into: false,
            priority: None,
            insert_alias: None,
            settings: None,
            format_clause: None,
        }))
    }

    /// Desugar relationship CREATE patterns into a statement that inserts both nodes and edges.
    /// Handles patterns like: CREATE (a:Person)-[:KNOWS]->(b:Person)
    /// 
    /// Generates: First INSERT nodes, then use compound statement to INSERT edges.
    /// Returns a compound statement with both INSERT operations.
    fn desugar_pattern_for_create(create_clause: CypherCreateClause) -> Result<Statement, ParserError> {
        // Collect all nodes and their properties
        let mut all_nodes: Vec<NodePattern> = Vec::new();
        let mut relationships: Vec<(RelationshipPattern, NodePattern, NodePattern)> = Vec::new();

        for pattern_part in &create_clause.pattern.parts {
            if let PatternElement::Simple(simple) = &pattern_part.anon_pattern_part {
                all_nodes.push(simple.node.clone());

                // Process relationship chains
                let mut previous_node = simple.node.clone();
                for chain_elem in &simple.chain {
                    relationships.push((
                        chain_elem.relationship.clone(),
                        previous_node.clone(),
                        chain_elem.node.clone(),
                    ));
                    all_nodes.push(chain_elem.node.clone());
                    previous_node = chain_elem.node.clone();
                }
            } else {
                return Err(ParserError::ParserError(
                    "Only simple node patterns are supported in CREATE clause for desugaring to INSERT statements.".to_string()
                ));
            }
        }

        if relationships.is_empty() {
            return Err(ParserError::ParserError(
                "No relationship found to desugar".to_string()
            ));
        }

        // Build single INSERT INTO nodes with all nodes as VALUES rows
        let mut node_values_rows = Vec::new();
        for node in &all_nodes {
            let mut row = Vec::new();
            
            // Add Label
            if let Some(label) = node.labels.first() {
                row.push(Expr::Value(Value::SingleQuotedString(label.to_string()).into()));
            } else {
                row.push(Expr::Value(Value::Null.into()));
            }
            
            // Add Properties
            if let Some(Expr::Map(map)) = &node.properties {
                let properties_str = Self::properties_to_string(map.clone())?;
                row.push(Expr::Value(Value::SingleQuotedString(properties_str).into()));
            } else {
                row.push(Expr::Value(Value::SingleQuotedString("{}".to_string()).into()));
            }
            
            node_values_rows.push(row);
        }

        let values_clause = Values {
            explicit_row: false,
            value_keyword: false,
            rows: node_values_rows,
        };

        let node_insert_query = Query {
            with: None,
            body: Box::new(SetExpr::Values(values_clause)),
            order_by: None,
            limit_clause: None,
            for_clause: None,
            settings: None,
            format_clause: None,
            pipe_operators: vec![],
            fetch: None,
            locks: vec![],
        };

        // Create the INSERT statement for nodes
        let node_insert = Insert {
            insert_token: AttachedToken::empty(),
            or: None,
            table: TableObject::TableName(ObjectName(vec![
                ObjectNamePart::Identifier(Ident::new("nodes"))
            ])),
            table_alias: None,
            ignore: false,
            into: true,
            overwrite: false,
            partitioned: None,
            columns: vec![Ident::new("Label"), Ident::new("Properties")],
            after_columns: vec![],
            source: Some(Box::new(node_insert_query)),
            assignments: vec![],
            has_table_keyword: false,
            on: None,
            returning: None,
            replace_into: false,
            priority: None,
            insert_alias: None,
            settings: None,
            format_clause: None,
        };

        // Create CTE that selects the newly inserted nodes by querying the last N rows
        let new_nodes_select = Select {
            select_token: AttachedToken::empty(),
            distinct: None,
            top: None,
            top_before_distinct: false,
            projection: vec![
                SelectItem::UnnamedExpr(Expr::Identifier(Ident::new("Id"))),
                SelectItem::UnnamedExpr(Expr::Identifier(Ident::new("Properties"))),
            ],
            exclude: None,
            into: None,
            from: vec![TableWithJoins {
                relation: Self::create_table_factor("nodes", None),
                joins: vec![],
            }],
            lateral_views: vec![],
            prewhere: None,
            selection: None,
            group_by: GroupByExpr::Expressions(vec![], vec![]),
            cluster_by: vec![],
            distribute_by: vec![],
            sort_by: vec![],
            having: None,
            named_window: vec![],
            window_before_qualify: false,
            qualify: None,
            value_table_mode: None,
            connect_by: None,
            flavor: SelectFlavor::Standard,
        };

        let cte = Cte {
            alias: TableAlias {
                name: Ident::new("new_nodes"),
                columns: vec![],
            },
            query: Box::new(Query {
                with: None,
                body: Box::new(SetExpr::Select(Box::new(new_nodes_select))),
                order_by: Some(OrderBy {
                    kind: OrderByKind::Expressions(vec![OrderByExpr {
                        expr: Expr::Identifier(Ident::new("Id")),
                        options: OrderByOptions {
                            asc: Some(false),
                            nulls_first: None,
                        },
                        with_fill: None,
                    }]),
                    interpolate: None,
                }),
                limit_clause: Some(LimitClause::LimitOffset {
                    limit: Some(Expr::Value(Value::Number(all_nodes.len().to_string(), false).into())),
                    limit_by: vec![],
                    offset: None,
                }),
                fetch: None,
                locks: vec![],
                for_clause: None,
                settings: None,
                format_clause: None,
                pipe_operators: vec![],
            }),
            from: None,
            materialized: None,
            closing_paren_token: AttachedToken(TokenWithSpan {
                token: Token::RParen,
                span: Span::empty(),
            }),
        };

        // Build SELECT statements for each relationship with subqueries to find node IDs
        let mut edge_selects = Vec::new();
        for (relationship, source_node, target_node) in &relationships {
            let rel_type = relationship.details.types.first()
                .map(|id| id.value.clone())
                .unwrap_or_default();

            let props_expr = match relationship.details.properties.clone() {
                Some(Expr::Map(map)) => {
                    let properties_str = Self::properties_to_string(map)?;
                    Expr::Value(Value::SingleQuotedString(properties_str).into())
                }
                _ => Expr::Value(Value::SingleQuotedString("{}".to_string()).into()),
            };

            // Create subqueries for source and target node IDs
            let source_subquery = Self::create_node_id_subquery(source_node)?;
            let target_subquery = Self::create_node_id_subquery(target_node)?;

            edge_selects.push(Select {
                select_token: AttachedToken::empty(),
                distinct: None,
                top: None,
                top_before_distinct: false,
                projection: vec![
                    SelectItem::UnnamedExpr(Expr::Value(Value::SingleQuotedString(rel_type).into())),
                    SelectItem::UnnamedExpr(source_subquery),
                    SelectItem::UnnamedExpr(target_subquery),
                    SelectItem::UnnamedExpr(props_expr),
                ],
                exclude: None,
                into: None,
                from: vec![],
                lateral_views: vec![],
                prewhere: None,
                selection: None,
                group_by: GroupByExpr::Expressions(vec![], vec![]),
                cluster_by: vec![],
                distribute_by: vec![],
                sort_by: vec![],
                having: None,
                named_window: vec![],
                window_before_qualify: false,
                qualify: None,
                value_table_mode: None,
                connect_by: None,
                flavor: SelectFlavor::Standard,
            });
        }

        // Combine edge SELECTs with UNION ALL if multiple relationships
        let edge_source = if edge_selects.len() == 1 {
            Box::new(Query {
                with: None,
                body: Box::new(SetExpr::Select(Box::new(edge_selects[0].clone()))),
                order_by: None,
                limit_clause: None,
                for_clause: None,
                settings: None,
                format_clause: None,
                pipe_operators: vec![],
                fetch: None,
                locks: vec![],
            })
        } else {
            let mut combined: SetExpr = SetExpr::Select(Box::new(edge_selects[0].clone()));
            for sel in edge_selects.iter().skip(1) {
                combined = SetExpr::SetOperation {
                    op: SetOperator::Union,
                    set_quantifier: SetQuantifier::All,
                    left: Box::new(combined),
                    right: Box::new(SetExpr::Select(Box::new(sel.clone()))),
                };
            }
            Box::new(Query {
                with: None,
                body: Box::new(combined),
                order_by: None,
                limit_clause: None,
                for_clause: None,
                settings: None,
                format_clause: None,
                pipe_operators: vec![],
                fetch: None,
                locks: vec![],
            })
        };

        // Build INSERT INTO edges
        let edge_insert = Insert {
            insert_token: AttachedToken::empty(),
            or: None,
            table: TableObject::TableName(ObjectName(vec![
                ObjectNamePart::Identifier(Ident::new("edges"))
            ])),
            table_alias: None,
            ignore: false,
            into: true,
            overwrite: false,
            partitioned: None,
            columns: vec![
                Ident::new("Label"),
                Ident::new("SourceId"),
                Ident::new("TargetId"),
                Ident::new("Properties"),
            ],
            after_columns: vec![],
            source: Some(edge_source),
            assignments: vec![],
            has_table_keyword: false,
            on: None,
            returning: None,
            replace_into: false,
            priority: None,
            insert_alias: None,
            settings: None,
            format_clause: None,
        };

        // Build the final query that includes both node INSERT and edge INSERT
        // This returns an IF statement with a BEGIN...END block containing both INSERT statements
        let edge_query = Query {
            with: Some(With {
                with_token: AttachedToken::empty(),
                recursive: false,
                cte_tables: vec![cte],
            }),
            body: Box::new(SetExpr::Insert(Statement::Insert(edge_insert))),
            order_by: None,
            limit_clause: None,
            for_clause: None,
            settings: None,
            format_clause: None,
            pipe_operators: vec![],
            fetch: None,
            locks: vec![],
        };

        // Return an IF statement with a Sequence containing both INSERT statements
        // This will output: INSERT INTO nodes ...; WITH ... INSERT INTO edges ...;
        Ok(Statement::If(IfStatement {
            if_block: ConditionalStatementBlock {
                start_token: AttachedToken(TokenWithSpan {
                    token: Token::Whitespace(Whitespace::Space),
                    span: Span::empty(),
                }),
                condition: None,
                then_token: None,
                conditional_statements: ConditionalStatements::Sequence {
                    statements: vec![
                        Statement::Insert(node_insert),
                        Statement::Query(Box::new(edge_query)),
                    ],
                },
            },
            elseif_blocks: vec![],
            else_block: None,
            end_token: None,
        }))
    }

    fn desugar_return(returning_clause: ReturningClause, mut select: Select) -> Result<Select, ParserError> {
        
        let mut projections = Vec::new();
        
        let distinct = if returning_clause.body.distinct {
            Some(Distinct::Distinct)
        } else {
            None
        };

        for item in returning_clause.body.projections {
            match item {
                ProjectionItem::Expr { expr, alias } => {
                    match expr {
                        // Handle property access: a.name -> json_extract(a.Properties, '$.name')
                        Expr::CompoundIdentifier(idents) if idents.len() == 2 => {
                            let key_expr = Expr::Function(Function {
                                name: ObjectName(vec![ObjectNamePart::Identifier(Ident::new("json_extract"))]),
                                parameters: FunctionArguments::None,
                                args: FunctionArguments::List(FunctionArgumentList {
                                    duplicate_treatment: None,
                                    args: vec![
                                        FunctionArg::Unnamed(FunctionArgExpr::Expr(
                                            Expr::CompoundIdentifier(vec![
                                                idents[0].clone(),
                                                Ident::new("Properties"),
                                            ])
                                        )),
                                        FunctionArg::Unnamed(FunctionArgExpr::Expr(
                                            Expr::Value(Value::SingleQuotedString(format!("$.{}", idents[1])).into())
                                        )),
                                    ],
                                    clauses: vec![],
                                }),
                                filter: None,
                                null_treatment: None,
                                over: None,
                                within_group: vec![],
                                uses_odbc_syntax: false,
                            });
                            
                            if let Some(a) = alias {
                                projections.push(SelectItem::ExprWithAlias {
                                    expr: key_expr,
                                    alias: a,
                                });
                            } else {
                                projections.push(SelectItem::UnnamedExpr(key_expr));
                            }
                        },
                        // Handle simple identifier: a -> a.* (select all columns from that table)
                        Expr::Identifier(ident) => {
                            projections.push(SelectItem::QualifiedWildcard(
                                SelectItemQualifiedWildcardKind::ObjectName(
                                    ObjectName(vec![ObjectNamePart::Identifier(ident)])
                                ),
                                WildcardAdditionalOptions::default(),
                            ));
                        },
                        _ => return Err(ParserError::ParserError(
                            "RETURN only supports identifiers (e.g., 'a') or property access expressions (e.g., 'a.name')".to_string()
                        )),
                    }
                },
                ProjectionItem::All => {
                    projections.push(SelectItem::Wildcard(WildcardAdditionalOptions::default()));
                }
            }
        }

        select.projection = projections;
        select.distinct = distinct;

        Ok(select)
    }

    fn desugar_reading_clause(reading_query: CypherReadingClause) -> Result<Select, ParserError> {
        match reading_query {
            CypherReadingClause::Match(match_clause) => {
                Ok(Self::desugar_match(match_clause)?)
            },
        }
    }

    // Desugar Cypher MATCH clause into SQL SELECT statement(s).
    fn desugar_match(match_clause: CypherMatchClause) -> Result<Select, ParserError> {

        if match_clause.optional {
            return Err(ParserError::ParserError(
                "Desugaring Cypher OPTIONAL MATCH clause is not supported.".to_string()
            ));
        }
        else
        {
            // Determine if pattern contains relationships or just nodes
            let has_relationships = match_clause.pattern.parts.iter()
                .any(|p| matches!(&p.anon_pattern_part, PatternElement::Simple(s) if !s.chain.is_empty()));
                
            let mut select =if has_relationships {
                Self::desugar_pattern_for_match(match_clause.pattern)?
            } else {
                Self::desugar_nodes_only_for_match(match_clause.pattern)?
            };
            
            // Add WHERE clause if present
            if let Some(where_clause) = match_clause.where_clause {
                let where_expr = Self::desugar_where(where_clause)?;
                select.selection = match select.selection {
                    Some(existing) => Some(Expr::BinaryOp {
                        left: Box::new(existing),
                        op: BinaryOperator::And,
                        right: Box::new(where_expr),
                    }),
                    None => Some(where_expr),
                };
            }

            Ok(select)
        }
    }

    /// Desugar Cypher CREATE clause into SQL INSERT statement(s).
    fn desugar_create(create_clause: CypherCreateClause) -> Result<Statement, ParserError> {
        
        // Determine if pattern contains relationships or just nodes
        let has_relationships = create_clause.pattern.parts.iter()
            .any(|p| matches!(&p.anon_pattern_part, PatternElement::Simple(s) if !s.chain.is_empty()));
        
        if has_relationships {
            Self::desugar_pattern_for_create(create_clause)
        } else {
            Self::desugar_nodes_only_for_create(create_clause)
        }
    }

    pub fn desugar_cypher_query(query: SinglePartQuery) -> Result<Statement, ParserError> {
        match query {
            SinglePartQuery::Reading(reading_query) => {
                let reading = Self::desugar_reading_clause(reading_query.reading_clause)?;
                let select = Self::desugar_return(reading_query.returning_clause, reading)?;

                Ok(Statement::Query(Box::new(Query {
                    with: None,
                    body: Box::new(SetExpr::Select(Box::new(select))),
                    order_by: None,
                    limit_clause: None,
                    for_clause: None,
                    settings: None,
                    format_clause: None,
                    pipe_operators: vec![],
                    fetch: None,
                    locks: vec![],
                })))
            },
            SinglePartQuery::Updating(updating_query) => {
                Self::desugar_create(updating_query.create_clause)
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::helpers::desugar_cypher::Desugarer;

    #[test]
    fn test_properties_to_string(){

        let properties = Map {
            entries: vec![
                MapEntry {
                    key: Box::new(Expr::Identifier(Ident::new("name"))),
                    value: Box::new(Expr::Value(Value::SingleQuotedString("Alice".to_string()).into())),
                },
                MapEntry {
                    key: Box::new(Expr::Identifier(Ident::new("age"))),
                    value: Box::new(Expr::Value(Value::Number("30".to_string(), false).into())),
                },
            ],
        };

        let dummy_alias = Ident::new("n");
        let desugared = Desugarer::desugar_properties_map(properties, &dummy_alias).unwrap();
        let expected = Some(Expr::BinaryOp {
            left: Box::new(Expr::BinaryOp {
                left: Box::new(Expr::Function(Function {
                    name: ObjectName(vec![ObjectNamePart::Identifier(Ident::new("json_extract"))]),
                    parameters: FunctionArguments::None,
                    args: FunctionArguments::List(FunctionArgumentList {
                        duplicate_treatment: None,
                        args: vec![
                            FunctionArg::Unnamed(FunctionArgExpr::Expr(
                                Expr::CompoundIdentifier(vec![Ident::new("n"), Ident::new("Properties")])
                            )),
                            FunctionArg::Unnamed(FunctionArgExpr::Expr(
                                Expr::Value(Value::SingleQuotedString("$.name".to_string()).into())
                            )),
                        ],
                        clauses: vec![],
                    }),
                    filter: None,
                    null_treatment: None,
                    over: None,
                    within_group: vec![],
                    uses_odbc_syntax: false,
                })),
                op: BinaryOperator::Eq,
                right: Box::new(Expr::Value(Value::SingleQuotedString("Alice".to_string()).into())),
            }),
            op: BinaryOperator::And,
            right: Box::new(Expr::BinaryOp {
                left: Box::new(Expr::Function(Function {
                    name: ObjectName(vec![ObjectNamePart::Identifier(Ident::new("json_extract"))]),
                    parameters: FunctionArguments::None,
                    args: FunctionArguments::List(FunctionArgumentList {
                        duplicate_treatment: None,
                        args: vec![
                            FunctionArg::Unnamed(FunctionArgExpr::Expr(
                                Expr::CompoundIdentifier(vec![Ident::new("n"), Ident::new("Properties")])
                            )),
                            FunctionArg::Unnamed(FunctionArgExpr::Expr(
                                Expr::Value(Value::SingleQuotedString("$.age".to_string()).into())
                            )),
                        ],
                        clauses: vec![],
                    }),
                    filter: None,
                    null_treatment: None,
                    over: None,
                    within_group: vec![],
                    uses_odbc_syntax: false,
                })),
                op: BinaryOperator::Eq,
                right: Box::new(Expr::Value(Value::Number("30".to_string(), false).into())),
            }),
        });
        assert_eq!(desugared, expected);
    }

    #[test]
    fn test_desugar_cypher_node_pattern()  {
        let node_pattern = NodePattern {
            variable: Some(Ident::new("n")),
            labels: vec![Ident::new("Person")],
            properties: Some(Expr::Map(Map {
                entries: vec![
                    MapEntry {
                        key: Box::new(Expr::Identifier(Ident::new("name"))),
                        value: Box::new(Expr::Value(Value::SingleQuotedString("Alice".to_string()).into())),
                    },
                ],
            })),
        };

        let alias = Ident::new("n");
        let desugared = Desugarer::desugar_node_filter(node_pattern, &alias).unwrap();
        let expected = Some(Expr::BinaryOp {
            left: Box::new(Expr::BinaryOp {
                left: Box::new(Expr::CompoundIdentifier(vec![Ident::new("n"), Ident::new("Label")])),
                op: BinaryOperator::Eq,
                right: Box::new(Expr::Value(Value::SingleQuotedString("Person".to_string()).into())),
            }),
            op: BinaryOperator::And,
            right: Box::new(Expr::BinaryOp {
                left: Box::new(Expr::Function(Function {
                    name: ObjectName(vec![ObjectNamePart::Identifier(Ident::new("json_extract"))]),
                    parameters: FunctionArguments::None,
                    args: FunctionArguments::List(FunctionArgumentList {
                        duplicate_treatment: None,
                        args: vec![
                            FunctionArg::Unnamed(FunctionArgExpr::Expr(
                                Expr::CompoundIdentifier(vec![Ident::new("n"), Ident::new("Properties")])
                            )),
                            FunctionArg::Unnamed(FunctionArgExpr::Expr(
                                Expr::Value(Value::SingleQuotedString("$.name".to_string()).into())
                            )),
                        ],
                        clauses: vec![],
                    }),
                    filter: None,
                    null_treatment: None,
                    over: None,
                    within_group: vec![],
                    uses_odbc_syntax: false,
                })),
                op: BinaryOperator::Eq,
                right: Box::new(Expr::Value(Value::SingleQuotedString("Alice".to_string()).into())),
            }),
        });
        assert_eq!(desugared, expected);
    }

    #[test]
    fn test_desugar_cypher_relationship_pattern(){
        let relationship_pattern = RelationshipPattern {
            details: RelationshipDetail {
                types: vec![Ident::new("KNOWS")],
                properties: Some(Expr::Map(Map {
                    entries: vec![
                        MapEntry {
                            key: Box::new(Expr::Identifier(Ident::new("since"))),
                            value: Box::new(Expr::Value(Value::Number("2020".to_string(), false).into())),
                        },
                    ],
                })),
                length: None,
                variable: None,
            },
            l_direction: Some(RelationshipDirection::Undirected),
            r_direction: Some(RelationshipDirection::Undirected),
        };

        let alias = Ident::new("r");
        let desugared = Desugarer::desugar_relationship_filter(relationship_pattern, &alias).unwrap();
        let expected = Some(Expr::BinaryOp {
            left: Box::new(Expr::BinaryOp {
                left: Box::new(Expr::CompoundIdentifier(vec![Ident::new("r"), Ident::new("Label")])),
                op: BinaryOperator::Eq,
                right: Box::new(Expr::Value(Value::SingleQuotedString("KNOWS".to_string()).into())),
            }),
            op: BinaryOperator::And,
            right: Box::new(Expr::BinaryOp {
                left: Box::new(Expr::Function(Function {
                    name: ObjectName(vec![ObjectNamePart::Identifier(Ident::new("json_extract"))]),
                    parameters: FunctionArguments::None,
                    args: FunctionArguments::List(FunctionArgumentList {
                        duplicate_treatment: None,
                        args: vec![
                            FunctionArg::Unnamed(FunctionArgExpr::Expr(
                                Expr::CompoundIdentifier(vec![Ident::new("r"), Ident::new("Properties")])
                            )),
                            FunctionArg::Unnamed(FunctionArgExpr::Expr(
                                Expr::Value(Value::SingleQuotedString("$.since".to_string()).into())
                            )),
                        ],
                        clauses: vec![],
                    }),
                    filter: None,
                    null_treatment: None,
                    over: None,
                    within_group: vec![],
                    uses_odbc_syntax: false,
                })),
                op: BinaryOperator::Eq,
                right: Box::new(Expr::Value(Value::Number("2020".to_string(), false).into())),
            }),
        });
        assert_eq!(desugared, expected);
    }

    #[test]
    fn test_desguar_cypher_match_nodes_only() {
        let pattern = Pattern {
            parts: vec![
                PatternPart {
                    variable: None,
                    anon_pattern_part: PatternElement::Simple(SimplePatternElement {
                        node: NodePattern {
                            variable: Some(Ident::new("a")),
                            labels: vec![Ident::new("Person")],
                            properties: Some(Expr::Map(Map {
                                entries: vec![
                                    MapEntry {
                                        key: Box::new(Expr::Identifier(Ident::new("name"))),
                                        value: Box::new(Expr::Value(Value::SingleQuotedString("Alice".to_string()).into())),
                                    },
                                ],
                            })),
                        },
                        chain: vec![],
                    }),
                },
                PatternPart {
                    variable: None,
                    anon_pattern_part: PatternElement::Simple(SimplePatternElement {
                        node: NodePattern {
                            variable: Some(Ident::new("b")),
                            labels: vec![Ident::new("Person")],
                            properties: Some(Expr::Map(Map {
                                entries: vec![
                                    MapEntry {
                                        key: Box::new(Expr::Identifier(Ident::new("name"))),
                                        value: Box::new(Expr::Value(Value::SingleQuotedString("Bob".to_string()).into())),
                                    },
                                ],
                            })),
                        },
                        chain: vec![],
                    }),
                },
            ],
        };

        let desugared = Desugarer::desugar_nodes_only_for_match(pattern).unwrap();
        let expected = Select {
            select_token: AttachedToken::empty(),
            distinct: None,
            top: None,
            top_before_distinct: false,
            projection: vec![SelectItem::Wildcard(WildcardAdditionalOptions::default())],
            exclude: None,
            into: None,
            from: vec![
                TableWithJoins {
                    relation: TableFactor::Table {
                        name: ObjectName(vec![ObjectNamePart::Identifier(Ident::new("nodes"))]),
                        alias: Some(TableAlias {
                            name: Ident::new("a"),
                            columns: vec![],
                        }),
                        args: None,
                        with_hints: vec![],
                        version: None,
                        with_ordinality: false,
                        partitions: vec![],
                        json_path: None,
                        sample: None,
                        index_hints: vec![],
                    },
                    joins: vec![
                        Join {
                            relation: TableFactor::Table {
                                name: ObjectName(vec![ObjectNamePart::Identifier(Ident::new("nodes"))]),
                                alias: Some(TableAlias {
                                    name: Ident::new("b"),
                                    columns: vec![],
                                }),
                                args: None,
                                with_hints: vec![],
                                version: None,
                                with_ordinality: false,
                                partitions: vec![],
                                json_path: None,
                                sample: None,
                                index_hints: vec![],
                            },
                            global: false,
                            join_operator: JoinOperator::CrossJoin(JoinConstraint::None),
                        }
                    ],
                }
            ],
            lateral_views: vec![],
            prewhere: None,
            selection: Some(Expr::BinaryOp {
                left: Box::new(Expr::BinaryOp {
                    left: Box::new(Expr::BinaryOp {
                        left: Box::new(Expr::CompoundIdentifier(vec![Ident::new("a"), Ident::new("Label")])),
                        op: BinaryOperator::Eq,
                        right: Box::new(Expr::Value(Value::SingleQuotedString("Person".to_string()).into())),
                    }),
                    op: BinaryOperator::And,
                    right: Box::new(Expr::BinaryOp {
                        left: Box::new(Expr::Function(Function {
                            name: ObjectName(vec![ObjectNamePart::Identifier(Ident::new("json_extract"))]),
                            parameters: FunctionArguments::None,
                            args: FunctionArguments::List(FunctionArgumentList {
                                duplicate_treatment: None,
                                args: vec![
                                    FunctionArg::Unnamed(FunctionArgExpr::Expr(
                                        Expr::CompoundIdentifier(vec![Ident::new("a"), Ident::new("Properties")])
                                    )),
                                    FunctionArg::Unnamed(FunctionArgExpr::Expr(
                                        Expr::Value(Value::SingleQuotedString("$.name".to_string()).into())
                                    )),
                                ],
                                clauses: vec![],
                            }),
                            filter: None,
                            null_treatment: None,
                            over: None,
                            within_group: vec![],
                            uses_odbc_syntax: false,
                        })),
                        op: BinaryOperator::Eq,
                        right: Box::new(Expr::Value(Value::SingleQuotedString("Alice".to_string()).into())),
                    }),
                }),
                op: BinaryOperator::And,
                right: Box::new(Expr::BinaryOp {
                    left: Box::new(Expr::BinaryOp {
                        left: Box::new(Expr::CompoundIdentifier(vec![Ident::new("b"), Ident::new("Label")])),
                        op: BinaryOperator::Eq,
                        right: Box::new(Expr::Value(Value::SingleQuotedString("Person".to_string()).into())),
                    }),
                    op: BinaryOperator::And,
                    right: Box::new(Expr::BinaryOp {
                        left: Box::new(Expr::Function(Function {
                            name: ObjectName(vec![ObjectNamePart::Identifier(Ident::new("json_extract"))]),
                            parameters: FunctionArguments::None,
                            args: FunctionArguments::List(FunctionArgumentList {
                                duplicate_treatment: None,
                                args: vec![
                                    FunctionArg::Unnamed(FunctionArgExpr::Expr(
                                        Expr::CompoundIdentifier(vec![Ident::new("b"), Ident::new("Properties")])
                                    )),
                                    FunctionArg::Unnamed(FunctionArgExpr::Expr(
                                        Expr::Value(Value::SingleQuotedString("$.name".to_string()).into())
                                    )),
                                ],
                                clauses: vec![],
                            }),
                            filter: None,
                            null_treatment: None,
                            over: None,
                            within_group: vec![],
                            uses_odbc_syntax: false,
                        })),
                        op: BinaryOperator::Eq,
                        right: Box::new(Expr::Value(Value::SingleQuotedString("Bob".to_string()).into())),
                    }),
                }),
            }),
            group_by: GroupByExpr::Expressions(vec![], vec![]),
            cluster_by: vec![],
            distribute_by: vec![],
            sort_by: vec![],
            having: None,
            named_window: vec![],
            window_before_qualify: false,
            qualify: None,
            value_table_mode: None,
            connect_by: None,
            flavor: SelectFlavor::Standard,
        };
        assert_eq!(desugared, expected);
    }

    #[test]
    fn test_desugar_cypher_single_where() {
        let where_clause = CypherWhereClause {
            expr: Expr::BinaryOp {
                left: Box::new(Expr::CompoundIdentifier(vec![Ident::new("n"), Ident::new("age")])),
                op: BinaryOperator::Gt,
                right: Box::new(Expr::Value(Value::Number("30".to_string(), false).into())),
            },
        };

        let desugared = Desugarer::desugar_where(where_clause).unwrap();
        let expected = Expr::BinaryOp {
            left: Box::new(
                Expr::Function(Function {
                    name: ObjectName(vec![ObjectNamePart::Identifier(Ident::new("json_extract"))]),
                    parameters: FunctionArguments::None,
                    args: FunctionArguments::List(FunctionArgumentList {
                        duplicate_treatment: None,
                        args: vec![
                            FunctionArg::Unnamed(FunctionArgExpr::Expr(
                                Expr::CompoundIdentifier(vec![Ident::new("n"), Ident::new("Properties")])
                            )),
                            FunctionArg::Unnamed(FunctionArgExpr::Expr(
                                Expr::Value(Value::SingleQuotedString("$.age".to_string()).into())
                            )),
                        ],
                        clauses: vec![],
                    }),
                    filter: None,
                    null_treatment: None,
                    over: None,
                    within_group: vec![],
                    uses_odbc_syntax: false,
                })
            ),
            op: BinaryOperator::Gt,
            right: Box::new(Expr::Value(Value::Number("30".to_string(), false).into())),
        };
        assert_eq!(desugared, expected);
    }

    #[test]
    fn test_desugar_cypher_and_where(){
        let where_clause = CypherWhereClause {
            expr: Expr::BinaryOp {
                left: Box::new(Expr::BinaryOp {
                    left: Box::new(Expr::CompoundIdentifier(vec![Ident::new("n"), Ident::new("age")])),
                    op: BinaryOperator::Gt,
                    right: Box::new(Expr::Value(Value::Number("30".to_string(), false).into())),
                }),
                op: BinaryOperator::And,
                right: Box::new(Expr::BinaryOp {
                    left: Box::new(Expr::CompoundIdentifier(vec![Ident::new("n"), Ident::new("city")])),
                    op: BinaryOperator::Eq,
                    right: Box::new(Expr::Value(Value::SingleQuotedString("London".to_string()).into())),
                }),
            },
        };

        let desugared = Desugarer::desugar_where(where_clause).unwrap();
        let expected = Expr::BinaryOp {
            left: Box::new(
                Expr::BinaryOp {
                    left: Box::new(
                        Expr::Function(Function {
                            name: ObjectName(vec![ObjectNamePart::Identifier(Ident::new("json_extract"))]),
                            parameters: FunctionArguments::None,
                            args: FunctionArguments::List(FunctionArgumentList {
                                duplicate_treatment: None,
                                args: vec![
                                    FunctionArg::Unnamed(FunctionArgExpr::Expr(
                                        Expr::CompoundIdentifier(vec![Ident::new("n"), Ident::new("Properties")])
                                    )),
                                    FunctionArg::Unnamed(FunctionArgExpr::Expr(
                                        Expr::Value(Value::SingleQuotedString("$.age".to_string()).into())
                                    )),
                                ],
                                clauses: vec![],
                            }),
                            filter: None,
                            null_treatment: None,
                            over: None,
                            within_group: vec![],
                            uses_odbc_syntax: false,
                        })
                    ),
                    op: BinaryOperator::Gt,
                    right: Box::new(Expr::Value(Value::Number("30".to_string(), false).into())),
                }),
            op: BinaryOperator::And,
            right: Box::new(
                Expr::BinaryOp {
                    left: Box::new(Expr::Function(Function {
                        name: ObjectName(vec![ObjectNamePart::Identifier(Ident::new("json_extract"))]),
                        parameters: FunctionArguments::None,
                        args: FunctionArguments::List(FunctionArgumentList {
                            duplicate_treatment: None,
                            args: vec![
                                FunctionArg::Unnamed(FunctionArgExpr::Expr(
                                    Expr::CompoundIdentifier(vec![Ident::new("n"), Ident::new("Properties")])
                                )),
                                FunctionArg::Unnamed(FunctionArgExpr::Expr(
                                    Expr::Value(Value::SingleQuotedString("$.city".to_string()).into())
                                )),
                            ],
                            clauses: vec![],
                        }),
                        filter: None,
                        null_treatment: None,
                        over: None,
                        within_group: vec![],
                        uses_odbc_syntax: false,
                    })),
                    op: BinaryOperator::Eq,
                    right: Box::new(Expr::Value(Value::SingleQuotedString("London".to_string()).into())),
                }),
        };
        assert_eq!(desugared, expected);
    }

    #[test]
    fn test_desugar_cypher_or_where(){
        let where_clause = CypherWhereClause {
            expr: Expr::BinaryOp {
                left: Box::new(Expr::BinaryOp {
                    left: Box::new(Expr::CompoundIdentifier(vec![Ident::new("n"), Ident::new("age")])),
                    op: BinaryOperator::Lt,
                    right: Box::new(Expr::Value(Value::Number("25".to_string(), false).into())),
                }),
                op: BinaryOperator::Or,
                right: Box::new(Expr::BinaryOp {
                    left: Box::new(Expr::CompoundIdentifier(vec![Ident::new("n"), Ident::new("city")])),
                    op: BinaryOperator::Eq,
                    right: Box::new(Expr::Value(Value::SingleQuotedString("New York".to_string()).into())),
                }),
            },
        };

        let desugared = Desugarer::desugar_where(where_clause).unwrap();
        let expected = Expr::BinaryOp {
            left: Box::new(
                Expr::BinaryOp {
                    left: Box::new(
                        Expr::Function(Function {
                            name: ObjectName(vec![ObjectNamePart::Identifier(Ident::new("json_extract"))]),
                            parameters: FunctionArguments::None,
                            args: FunctionArguments::List(FunctionArgumentList {
                                duplicate_treatment: None,
                                args: vec![
                                    FunctionArg::Unnamed(FunctionArgExpr::Expr(
                                        Expr::CompoundIdentifier(vec![Ident::new("n"), Ident::new("Properties")])
                                    )),
                                    FunctionArg::Unnamed(FunctionArgExpr::Expr(
                                        Expr::Value(Value::SingleQuotedString("$.age".to_string()).into())
                                    )),
                                ],
                                clauses: vec![],
                            }),
                            filter: None,
                            null_treatment: None,
                            over: None,
                            within_group: vec![],
                            uses_odbc_syntax: false,
                        })
                    ),
                    op: BinaryOperator::Lt,
                    right: Box::new(Expr::Value(Value::Number("25".to_string(), false).into())),
                }),
            op: BinaryOperator::Or,
            right: Box::new(
                Expr::BinaryOp {
                    left: Box::new(Expr::Function(Function {
                        name: ObjectName(vec![ObjectNamePart::Identifier(Ident::new("json_extract"))]),
                        parameters: FunctionArguments::None,
                        args: FunctionArguments::List(FunctionArgumentList {
                            duplicate_treatment: None,
                            args: vec![
                                FunctionArg::Unnamed(FunctionArgExpr::Expr(
                                    Expr::CompoundIdentifier(vec![Ident::new("n"), Ident::new("Properties")])
                                )),
                                FunctionArg::Unnamed(FunctionArgExpr::Expr(
                                    Expr::Value(Value::SingleQuotedString("$.city".to_string()).into())
                                )),
                            ],
                            clauses: vec![],
                        }),
                        filter: None,
                        null_treatment: None,
                        over: None,
                        within_group: vec![],
                        uses_odbc_syntax: false,
                    })),
                    op: BinaryOperator::Eq,
                    right: Box::new(Expr::Value(Value::SingleQuotedString("New York".to_string()).into())),
                }),
        };
        assert_eq!(desugared, expected);
    }

    #[test]
    fn test_cypher_return(){
        let returning_clause = ReturningClause {
            body: ProjectionBody {
                distinct: true,
                projections: vec![
                    ProjectionItem::Expr {
                        expr: Expr::CompoundIdentifier(vec![Ident::new("n"), Ident::new("name")]),
                        alias: Some(Ident::new("person_name")),
                    },
                    ProjectionItem::All,
                ],
            },
        };

        let select = Select {
            select_token: AttachedToken::empty(),
            distinct: None,
            top: None,
            top_before_distinct: false,
            projection: vec![],
            exclude: None,
            into: None,
            from: vec![],
            lateral_views: vec![],
            prewhere: None,
            selection: None,
            group_by: GroupByExpr::Expressions(vec![], vec![]),
            cluster_by: vec![],
            distribute_by: vec![],
            sort_by: vec![],
            having: None,
            named_window: vec![],
            window_before_qualify: false,
            qualify: None,
            value_table_mode: None,
            connect_by: None,
            flavor: SelectFlavor::Standard,
        };

        let desugared = Desugarer::desugar_return(returning_clause, select).unwrap();
        let expected = Select {
            select_token: AttachedToken::empty(),
            distinct: Some(Distinct::Distinct),
            top: None,
            top_before_distinct: false,
            projection: vec![
                SelectItem::ExprWithAlias {
                    expr: Expr::Function(Function {
                        name: ObjectName(vec![ObjectNamePart::Identifier(Ident::new("json_extract"))]),
                        parameters: FunctionArguments::None,
                        args: FunctionArguments::List(FunctionArgumentList {
                            duplicate_treatment: None,
                            args: vec![
                                FunctionArg::Unnamed(FunctionArgExpr::Expr(
                                    Expr::CompoundIdentifier(vec![Ident::new("n"), Ident::new("Properties")])
                                )),
                                FunctionArg::Unnamed(FunctionArgExpr::Expr(
                                    Expr::Value(Value::SingleQuotedString("$.name".to_string()).into())
                                )),
                            ],
                            clauses: vec![],
                        }),
                        filter: None,
                        null_treatment: None,
                        over: None,
                        within_group: vec![],
                        uses_odbc_syntax: false,
                    }),
                    alias: Ident::new("person_name"),
                },
                SelectItem::Wildcard(WildcardAdditionalOptions::default()),
            ],
            exclude: None,
            into: None,
            from: vec![],
            lateral_views: vec![],
            prewhere: None,
            selection: None,
            group_by: GroupByExpr::Expressions(vec![], vec![]),
            cluster_by: vec![],
            distribute_by: vec![],
            sort_by: vec![],
            having: None,
            named_window: vec![],
            window_before_qualify: false,
            qualify: None,
            value_table_mode: None,
            connect_by: None,
            flavor: SelectFlavor::Standard,
        };

        assert_eq!(desugared, expected);
    }
}