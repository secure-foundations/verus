use crate::util::from_raw_span;
use air::ast::Ident;
use air::ast::Span as ASpan;
use air::model::Model as AModel;
use rustc_span::source_map::SourceMap;
use rustc_span::Span;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt;
use std::sync::Arc;
use vir::ast::Datatypes;
use vir::def::{SnapPos, SpanKind};
use vir::model::Model as VModel;
use vir::model::ModelDefX as VModelDefX;

#[derive(Debug)]
/// Rust-level model of a concrete counterexample
pub struct Debugger {
    /// Handle to the AIR-level model; only for internal use, e.g., for `eval`
    // air_model: AModel,
    /// VIR-level model
    vir_model: VModel,
    /// Internal mapping from a line in the source file to a snapshot ID
    line_map: HashMap<usize, Ident>,
    // the current line number
    line: usize,
}

// TODO: set up trace-base testing for debugger (regression test & CI purporse)

// The list of debugger commands
//
// Supported now:
//   set-line `n`
//   eval `var`       where `var` is a parameter or a local variable
//   locals           display immutable variables within the query
//
// Plan to support:
//   eval `expr`      where `expr` is a Rust-level expression
//   assume `expr`    additional assume. This will invoke additional `(check-sat)`
//   input            display counter example inputs
//   output           display counter example output
impl Debugger {
    pub fn new(
        mut air_model: AModel,
        _assign_map: &HashMap<*const ASpan, HashSet<Arc<String>>>,
        snap_map: &Vec<(ASpan, SnapPos)>,
        source_map: &SourceMap,
        datatypes: Datatypes,
        context: &mut air::context::Context,
        local_decls: &Vec<vir::sst::LocalDecl>,
    ) -> Debugger {
        let mut line_map: HashMap<usize, Ident> = HashMap::new();

        // let mut line_to_assigned = HashMap<usize, HashSet<Arc<String>>>::new();

        // for (air_span, vars) in assign_map {
        //     let span: &Span = &from_raw_span(&(*(*air_span)).raw_span);
        //     let (span_start, span_end) =
        //         source_map.is_valid_span(*span).expect("internal error: invalid Span");

        //     println!("{:?} {:?}", span_end.line, vars);
        // }
        let mut default_line = 0;

        if snap_map.len() > 0 {
            let (air_span, snap_pos) = &snap_map[0];
            let span: &Span = &from_raw_span(&air_span.raw_span);
            let (start, end) =
                source_map.is_valid_span(*span).expect("internal error: invalid Span");

            let mut min_snap: Ident = snap_pos.snapshot_id.clone();

            let mut min_line = start.line;
            let mut max_line = end.line;

            for (air_span, snap_pos) in snap_map {
                let span: &Span = &from_raw_span(&air_span.raw_span);
                let (span_start, span_end) =
                    source_map.is_valid_span(*span).expect("internal error: invalid Span");

                let cur_snap = snap_pos.snapshot_id.clone();
                let (start, end) = match snap_pos.kind {
                    SpanKind::Start => (span_start.line, span_start.line + 1),
                    SpanKind::Full => (span_start.line, span_end.line + 1),
                    SpanKind::End => (span_end.line, span_end.line + 1),
                };
                // println!("Apply {} to lines {}..{}", cur_snap, start, end);

                // Snapshots might overlap. For example:
                // `i = i +1 ` (when i is mutable).
                // above line has two snapshot at the same time
                // In that case, we merge the snapshot for this line
                // policy:
                //       if two snapshot contain a same variable, prefer the bigger suffix number for that variable
                //       for variables that are only present in one snapshot, safely merge those variables
                // For example, `snap%PRE` and `0_entry` will be better if these are merged, since both are intended for the initial state
                for line in start..end {
                    let mut snap_to_insert = cur_snap.clone();
                    if line_map.contains_key(&line)
                        && *(line_map.get(&line).expect("debugger::new line_map 1")) != cur_snap
                    {
                        // snap_to_insert = choose_later_snapshot(
                        //     cur_snap.clone(),
                        //     line_map.get(&line).unwrap().clone(),
                        // );
                        let sid1 = cur_snap.clone();
                        let sid2 = line_map.get(&line).unwrap().clone();
                        let merged_sid = Arc::new(format!("line_merged_snapshot_{}", line));
                        air_model.produce_merged_snapshot(&sid1, &sid2, &merged_sid); // when a line has > 2 snapshots, sid1 or sid2 might be same with merged_sid, but it is intended to implicitly update the hashmap
                        snap_to_insert = merged_sid;
                    }
                    // hashmap insert implicitly update value when key already exists
                    line_map.insert(line, snap_to_insert);
                }

                if span_start.line < min_line {
                    min_line = span_start.line;
                    min_snap = cur_snap.clone();
                }
                max_line = std::cmp::max(max_line, span_end.line);
            }

            // Fill in any gaps
            let mut cur_snap = min_snap;
            for line in min_line..max_line {
                match line_map.get(&line) {
                    Some(snap) => {
                        // println!("{} to {:?}", line, snap);
                        cur_snap = snap.clone();
                    }
                    None => {
                        // println!("{} (missing) to {:?}", line, cur_snap);
                        let _ = line_map.insert(line, cur_snap.clone());
                    }
                }
            }
            default_line = min_line;
        }

        // Debugging sanity checks
        // for (air_span, snap_pos) in snap_map {
        //     let span: &Span = &from_raw_span(&air_span.raw_span);
        //     let (start, end) =
        //         source_map.is_valid_span(*span).expect("internal error: invalid Span");
        // println!("Span from {} to {} => {:?}", start.line, end.line, snap_pos);
        // }

        // println!("\nPrinting line_map:");
        // for id in &line_map {
        //     println!("{:?}", id);
        // }

        // println!("Building AIR-level Model...");
        // air_model.build(context); // finalize air_model
        let mut vir_model: VModel = VModel::new(air_model, datatypes.clone(), local_decls);
        println!("Building VIR-level Model...");
        vir_model.build(context); // finalize vir_model

        println!("Setting Debugger Line to {:?}", default_line);
        Debugger { vir_model, line_map, line: default_line }
    }

    fn set_line(&mut self, line: usize) -> bool {
        if let None = self.line_map.get(&line) {
            false
        } else {
            self.line = line;
            true
            // println!("line number set to {}", line);
        }
    }

    // // TODO: struct field access
    // // TODO: struct eval -> each struct field access
    // // TODO: function call of form foo(x)
    // fn rewrite_eval_expr(&self, expr: &sise::Node) -> Option<sise::Node> {
    //     match expr {
    //         Node::Atom(var) => {
    //             let name = self.translate_variable(&Arc::new(String::from(var)));
    //             match name {
    //                 Some(n) => Some(Node::Atom(n)),
    //                 None => panic!(
    //                     "TODO: This variable is not in air model. Should rewrite this using existing definition."
    //                 ),
    //             }
    //         }
    //         Node::List(app) => {
    //             if let Node::Atom(var) = &app[0] {
    //                 // TODO: should use suffix_global_id + path_to_air_ident?
    //                 let mut func_name = var.clone();
    //                 func_name.push('.');
    //                 func_name.push('?');
    //                 let mut items = vec![Node::Atom(func_name)];
    //                 for name in app.iter().skip(1) {
    //                     let name = self.rewrite_eval_expr(name)?;
    //                     items.push(name);
    //                 }
    //                 Some(Node::List(items))
    //             }
    //             // TODO!!
    //             else {
    //                 panic!("TODO: Debugger::rewrite_eval_expr, list case");
    //                 // println!("rewrite_eval_expr is about to return None");
    //                 // println!("{:?}", expr);
    //                 // None
    //             }
    //         }
    //     }
    // }

    fn eval_expr(&self, expr: Arc<String>, context: &mut air::context::Context) {
        // Case 1: variable
        // TODO: sometimes a variable is not declared in query variables (not by 'declare-const`, but by `let` inside query assertion)
        // Should get the definition from somewhere else.

        // assume Case1 for now
        let sid = self.line_map.get(&self.line).expect("sid from line number");
        let value = self.vir_model.eval_variable(&expr, sid, context);
        match value {
            Ok(def) => {
                VModelDefX::pretty_print(&def);
                return;
            }
            Err(err_info) => {
                println!("eval of variable: {} failed. {}", expr.to_string(), err_info);
                return;
            }
        };

        // Case 2: Expression
        // TODO: make a function to translate Rust Expr -> Air Expr directly

        // let expr_byte: &[u8] = expr_str.as_bytes();
        // let mut parser = sise::Parser::new(expr_byte);
        // let node = sise::read_into_tree(&mut parser).expect("debugger::eval_expr, parsing");
        // let expr = self.rewrite_eval_expr(&node).expect("debugger::eval_expr, rewriting");
        // let result = context.eval_expr(expr);
        // println!("{}{}\n", expr_str, result);
        panic!("TODO: evaluation of Rust expression")
    }

    pub fn start_shell(&mut self, context: &mut air::context::Context) {
        println!("Welcome to Verus debugger shell");
        loop {
            let mut input = String::new();
            std::io::stdin().read_line(&mut input).expect("Error: reading line at debugger shell");
            let mut input_copy = input.clone();
            let inputs: Vec<&str> = input.split_whitespace().collect();
            // println!("You typed: {:?}", inputs);
            if inputs[0] == "quit" {
                println!("exit debugger shell\n");
                break;
            } else if inputs[0] == "model" {
                println!("Dumping Z3 Model...");
                for def in &self.vir_model.air_model.model {
                    println!("{:?}\n", def);
                }
                continue;
            } else if inputs[0] == "set-line" {
                let line_num = inputs[1].parse::<usize>().expect("Err: invalid line num");
                if !self.set_line(line_num) {
                    println!("invalid line number {}, no snapshot found\n", line_num);
                }
                continue;
            } else if inputs[0] == "locals" {
                for (_, def) in &self.vir_model.model {
                    vir::model::ModelDefX::pretty_print(&*def);
                    println!("");
                }
                continue;
            } else if inputs[0] == "eval" {
                if inputs.len() == 2 {
                    let later = inputs[1].to_string();
                    self.eval_expr(Arc::new(later), context);
                    continue;
                } else {
                    let mut later = input_copy.split_off(4);
                    later.pop(); //remove newline
                    panic!("TODO eval of expression");
                    continue;
                }
            } else {
                println!("Unsupported: you typed: {:?}\n", inputs);
                continue;
            }
        }
    }
}

impl fmt::Display for Debugger {
    /// Dump the contents of the Rust model for debugging purposes
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\nDisplaying model with {} lines\n", self.line_map.len())?;
        let mut lines: Vec<_> = self.line_map.iter().collect();
        lines.sort_by_key(|t| t.0);
        for (line, snap_id) in lines {
            write!(f, "Line {}: {}\n", line, snap_id)?;
        }
        Ok(())
    }
}
