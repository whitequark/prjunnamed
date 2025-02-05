/// Decision tree lowering.
///
/// The `decision` pass implements decision tree lowering based on the well-known heuristic
/// algorithm developed for ML from the paper "Tree pattern matching for ML" by Marianne Baudinet
/// and David MacQueen (unpublished, 1986) the extended abstract of which is available from:
/// *  https://smlfamily.github.io/history/Baudinet-DM-tree-pat-match-12-85.pdf (scan)
/// *  https://www.classes.cs.uchicago.edu/archive/2011/spring/22620-1/papers/macqueen-baudinet85.pdf (OCR)
///
/// The algorithm is described in §4 "Decision trees and the dispatching problem". Only two
/// of the heuristics described apply here: the relevance heuristic and the branching factor
/// heuristic.
///
/// TODO: actually use the heuristic; right now the column matching on a net with the lowest numeric
/// value is chosen, which is a really awful "heuristic" that still produces mostly okay results
///
use std::fmt::Display;
use std::collections::{BTreeMap, BTreeSet, HashMap};

use prjunnamed_netlist::{CellRef, Cell, Const, Design, MatchCell, Net, Trit, Value};

/// Maps `pattern` (a constant where 0 and 1 match the respective states, and X matches any state)
/// to a set of `rules` (the nets that are asserted if the `pattern` matches the value being tested).
#[derive(Debug, Clone, PartialEq, Eq)]
struct MatchRow {
    pattern: Const,
    rules: BTreeSet<Net>,
}

/// Matches `value` against ordered `rows` of patterns and their corresponding rules, where the `rules`
/// for the first pattern that matches the value being tested are asserted, and all other `rules`
/// are deasserted.
#[derive(Debug, Clone, PartialEq, Eq)]
struct MatchMatrix {
    value: Value,
    rows: Vec<MatchRow>,
}

/// Describes the process of testing individual nets of a value (equivalently, eliminating columns
/// from a match matrix) until a specific row is reached.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Decision {
    Result { rules: BTreeSet<Net> },
    Branch { net: Net, if0: Box<Decision>, if1: Box<Decision> },
}

impl MatchRow {
    fn new(pattern: impl Into<Const>, rules: impl IntoIterator<Item = Net>) -> Self {
        Self { pattern: pattern.into(), rules: BTreeSet::from_iter(rules) }
    }

    fn empty(pattern_len: usize) -> Self {
        Self::new(Const::undef(pattern_len), [])
    }

    fn merge(mut self, other: &MatchRow) -> Self {
        self.pattern.extend(&other.pattern);
        self.rules.extend(other.rules.iter().cloned());
        self
    }
}

impl MatchMatrix {
    fn new(value: impl Into<Value>) -> Self {
        Self { value: value.into(), rows: Vec::new() }
    }

    fn add(&mut self, row: MatchRow) -> usize {
        assert_eq!(self.value.len(), row.pattern.len());
        self.rows.push(row);
        self.rows.len() - 1
    }

    fn merge(mut self, at: Net, other: &MatchMatrix) -> Self {
        self.value.extend(&other.value);
        for self_row in std::mem::take(&mut self.rows) {
            if self_row.rules.contains(&at) {
                for other_row in &other.rows {
                    self.add(self_row.clone().merge(&other_row));
                }
            }
            self.add(self_row.merge(&MatchRow::empty(other.value.len())));
        }
        self
    }

    fn iter_rules(&self) -> impl Iterator<Item = Net> {
        BTreeSet::from_iter(self.rows.iter().flat_map(|row| row.rules.iter()).cloned()).into_iter()
    }

    fn assume(mut self, target: Net, value: Trit) -> Self {
        self.value =
            Value::from_iter(self.value.into_iter().map(|net| if net == target { Net::from(value) } else { net }));
        self
    }

    fn slice(mut self, nets: &BTreeSet<Net>) -> Self {
        for row in &mut self.rows {
            row.rules = BTreeSet::from_iter(row.rules.intersection(nets).cloned());
        }
        self
    }

    fn normalize(mut self) -> Self {
        let mut remove_cols = BTreeSet::new();
        let mut remove_rows = BTreeSet::new();

        // Pick columns to remove where the matched value is constant or has repeated nets.
        let mut first_at = BTreeMap::new();
        for (index, net) in self.value.iter().enumerate() {
            if net.is_cell() && !first_at.contains_key(&net) {
                first_at.insert(net, index);
            } else {
                remove_cols.insert(index);
            }
        }

        // Pick rows to remove that:
        // * are redundant with the previous row, or
        // * contradict themselves or the constant nets in matched value.
        let mut prev_pattern = None;
        'outer: for (row_index, row) in self.rows.iter_mut().enumerate() {
            // Check if row will never match because of a previous row that:
            // * has the same pattern, or
            // * matches any value.
            if let Some(ref prev_pattern) = prev_pattern {
                if row.pattern == *prev_pattern || prev_pattern.is_undef() {
                    remove_rows.insert(row_index);
                    continue;
                }
            }
            prev_pattern = Some(row.pattern.clone());
            // Check if row is contradictory.
            for (net_index, net) in self.value.iter().enumerate() {
                let mask = row.pattern[net_index];
                // Row contradicts constant in matched value.
                match net.as_const() {
                    Some(trit) if trit != mask && mask != Trit::Undef => {
                        remove_rows.insert(row_index);
                        continue 'outer;
                    }
                    _ => (),
                }
                // Check if the net appears multiple times in the matched value.
                match first_at.get(&net) {
                    // It doesn't.
                    None => (),
                    // It does and this is the first occurrence. Leave it alone.
                    Some(&first_at_index) if first_at_index == net_index => (),
                    // It does and this is the second or later occurrence. Check if it is compatible with
                    // the first one. Also, if the first one was a don't-care, move this one into the position
                    // of the first one.
                    Some(&first_at_index) => {
                        let first_mask = &mut row.pattern[first_at_index];
                        if *first_mask != Trit::Undef && mask != Trit::Undef && *first_mask != mask {
                            remove_rows.insert(row_index);
                            continue 'outer;
                        }
                        if *first_mask == Trit::Undef {
                            *first_mask = mask;
                        }
                    }
                }
            }
        }

        // Pick columns to remove where all of the patterns match any value.
        let mut all_undef = vec![true; self.value.len()];
        for row in self.rows.iter() {
            for col_index in 0..self.value.len() {
                if row.pattern[col_index] != Trit::Undef {
                    all_undef[col_index] = false;
                }
            }
        }
        for (col_index, matches_any) in all_undef.into_iter().enumerate() {
            if matches_any {
                remove_cols.insert(col_index);
            }
        }

        // Execute column and row removal.
        fn remove_indices<'a, T>(
            iter: impl IntoIterator<Item = T> + 'a,
            remove_set: &'a BTreeSet<usize>,
        ) -> impl Iterator<Item = T> + 'a {
            iter.into_iter().enumerate().filter_map(|(index, elem)| (!remove_set.contains(&index)).then_some(elem))
        }

        self.value = Value::from_iter(remove_indices(self.value, &remove_cols));
        self.rows = Vec::from_iter(remove_indices(self.rows, &remove_rows));
        for row in &mut self.rows {
            row.pattern = Const::from_iter(remove_indices(row.pattern.iter(), &remove_cols));
        }
        self
    }

    fn dispatch(mut self) -> Box<Decision> {
        self = self.normalize();
        if self.value.is_empty() || self.rows.len() == 1 {
            Box::new(Decision::Result { rules: self.rows.into_iter().next().map(|r| r.rules).unwrap_or_default() })
        } else {
            // TODO: better decision procedure
            let test = self.value.iter().rev().next().unwrap();

            let if0 = self.clone().assume(test, Trit::Zero).dispatch();
            let if1 = self.clone().assume(test, Trit::One).dispatch();
            if if0 == if1 {
                // Skip the branch if the outputs of the decision function are the same. This can happen
                // e.g. in the following matrix:
                //   00 => x
                //   10 => x
                //   XX => y
                // regardless of the column selection order. Even if the column 1 is chosen (as it should be),
                // there are two rows but the `y` rule is still unreachable due to irrefutability.
                if0
            } else {
                Box::new(Decision::Branch { net: test, if0, if1 })
            }
        }
    }
}

impl Decision {
    fn emit(&self, design: &Design, cache: &mut HashMap<Cell, Net>) -> BTreeSet<Net> {
        fn subtree(
            design: &Design,
            decision: &Decision,
            all_rules: &mut BTreeSet<Net>,
            sop: &mut BTreeMap<Net, Vec<Net>>,
            nets: &mut Vec<Net>,
            bits: &mut Vec<Trit>,
            cache: &mut HashMap<Cell, Net>,
        ) {
            match decision {
                Decision::Result { rules } => {
                    let cond_cell = match &bits[..] {
                        [] => Cell::Buf(Trit::One.into()),
                        [Trit::One] => Cell::Buf(nets[0].into()),
                        [Trit::Zero] => Cell::Not(nets[0].into()),
                        _ => Cell::Eq(nets.clone().into(), Const::from(bits.clone()).into()),
                    };
                    let cond =
                        *cache.entry(cond_cell).or_insert_with_key(|cell| design.add_cell(cell.clone()).unwrap_net());
                    for &rule in rules {
                        all_rules.insert(rule);
                        sop.entry(rule).or_default().push(cond);
                    }
                }
                Decision::Branch { net, if0, if1 } => {
                    nets.push(*net);
                    bits.push(Trit::Zero);
                    subtree(design, if0, all_rules, sop, nets, bits, cache);
                    bits.pop();
                    bits.push(Trit::One);
                    subtree(design, if1, all_rules, sop, nets, bits, cache);
                    bits.pop();
                    nets.pop();
                }
            }
        }

        // Convert decision tree into sum-of-products representation, and emit products as `eq` cells.
        // Although they will be merged later, this function avoids emitting duplicate cells anyway.
        let mut all_rules = BTreeSet::new();
        let mut sop = BTreeMap::new();
        let (mut nets, mut bits) = (Vec::new(), Vec::new());
        subtree(design, self, &mut all_rules, &mut sop, &mut nets, &mut bits, cache);

        // Emit sums as `or` cell sequences, and replace the void nets introduced for rules with the sum nets.
        for (rule, products) in sop {
            let mut sum = None::<Net>;
            for product in products {
                if let Some(ref mut sum) = sum {
                    let sum_cell = Cell::Or((*sum).into(), product.into());
                    *sum = *cache.entry(sum_cell).or_insert_with_key(|cell| design.add_cell(cell.clone()).unwrap_net());
                } else {
                    sum = Some(product);
                }
            }
            design.replace_net(rule, sum.unwrap());
        }

        // Return the set of all encountered rules. The caller will need to replace void nets for rules
        // that never appear in the decision trees to keep the netlist well-formed.
        all_rules
    }
}

// Convert a tree of `match` cells into a matrix, disregarding the enable input.
// The output of the cell is replaced with a newly conjured void.
fn match_tree_into_matrix(
    design: &Design,
    subtrees: &BTreeMap<(CellRef, usize), CellRef>,
    cell_ref: CellRef,
    enable: Net,
) -> MatchMatrix {
    let Cell::Match(match_cell) = &*cell_ref.get() else { unreachable!() };
    let output = design.add_void(match_cell.output_len());
    if enable == Net::ONE {
        design.replace_value(cell_ref.output(), &output);
    } else {
        design.replace_value(cell_ref.output(), design.add_mux(enable, &output, Const::zero(output.len())));
    }

    // Create matrix for this cell.
    let mut matrix = MatchMatrix::new(&match_cell.value);
    for (output_net, alternates) in std::iter::zip(output.iter(), match_cell.patterns.iter()) {
        for pattern in alternates {
            matrix.add(MatchRow::new(pattern.clone(), [output_net]));
        }
        if alternates.is_empty() {
            design.replace_net(output_net, Net::ZERO);
        }
    }
    matrix.add(MatchRow::empty(match_cell.value.len()));

    // Create matrices for subtrees and merge them into the matrix for this cell.
    for (offset, output_net) in output.iter().enumerate() {
        if let Some(&sub_cell_ref) = subtrees.get(&(cell_ref, offset)) {
            let sub_matrix = match_tree_into_matrix(design, subtrees, sub_cell_ref, enable);
            matrix = matrix.merge(output_net, &sub_matrix);
        }
    }

    matrix
}

pub fn decision(design: &mut Design) {
    // Find trees of `match` cells connected by their enable inputs.
    let mut roots: BTreeSet<CellRef> = BTreeSet::new();
    let mut subtrees: BTreeMap<(CellRef, usize), BTreeSet<CellRef>> = BTreeMap::new();
    for cell_ref in design.iter_cells() {
        if let Cell::Match(MatchCell { enable, .. }) = &*cell_ref.get() {
            match design.find_cell(*enable) {
                Err(Trit::Undef) | Err(Trit::Zero) => {
                    // Never enabled.
                    cell_ref.replace(Cell::Buf(Const::zero(cell_ref.output_len()).into()));
                }
                Err(Trit::One) => {
                    // Always enabled; is a root of a match tree.
                    roots.insert(cell_ref);
                }
                Ok((enable_cell_ref, offset)) => {
                    // Conditionally enabled; may be a node in a match tree or a root, depending on
                    // what the enable signal is connected to.
                    if let Cell::Match(_) = &*cell_ref.get() {
                        // Node in a match tree.
                        subtrees.entry((enable_cell_ref, offset)).or_default().insert(cell_ref);
                    } else {
                        // Some other signal.
                        roots.insert(cell_ref);
                    }
                }
            }
        }
    }

    // Whenever multiple subtrees are connected to the same one-hot output, it is not possible
    // to merge them into the same matrix. Turn all of the subtrees into roots.
    let subtrees = BTreeMap::from_iter(subtrees.into_iter().filter_map(|(key, subtrees)| {
        if subtrees.len() == 1 {
            Some((key, subtrees.into_iter().next().unwrap()))
        } else {
            roots.extend(subtrees);
            None
        }
    }));

    // Combine each tree of `match` cells into a single match matrix.
    let mut root_matrices = Vec::new();
    for root_cell_ref in roots {
        let Cell::Match(MatchCell { enable, .. }) = &*root_cell_ref.get() else { unreachable!() };
        root_matrices.push(match_tree_into_matrix(design, &subtrees, root_cell_ref, *enable));
    }

    // Compute the decision tree(s) for each of the root matrices and translate them to logic gates.
    let mut cache = HashMap::new();
    for root_matrix in root_matrices {
        let all_outputs = BTreeSet::from_iter(root_matrix.iter_rules());
        if cfg!(feature = "trace") {
            eprintln!(">matrix (initial):\n{root_matrix}");
        }

        let root_matrix = root_matrix.normalize();
        if cfg!(feature = "trace") {
            eprintln!(">matrix (normalized):\n{root_matrix}");
        }

        let mut unused_outputs = all_outputs.clone();
        for net in all_outputs {
            let sliced_matrix = root_matrix.clone().slice(&BTreeSet::from_iter([net]));
            if cfg!(feature = "trace") {
                eprintln!(">matrix (sliced):\n{sliced_matrix}")
            }

            let decision_tree = sliced_matrix.dispatch();
            if cfg!(feature = "trace") {
                eprintln!(">decision tree:\n{decision_tree}")
            }

            let replaced = decision_tree.emit(design, &mut cache);
            unused_outputs = BTreeSet::from_iter(unused_outputs.difference(&replaced).cloned());
        }

        for net in unused_outputs {
            if cfg!(feature = "trace") {
                eprintln!(">unused rule: {net}")
            }
            design.replace_net(net, Net::ZERO);
        }
    }

    // Lower `assign` cells.
    for cell_ref in design.iter_cells() {
        if let Cell::Assign(assign_cell) = &*cell_ref.get() {
            let mut nets = Vec::from_iter(assign_cell.value.iter());
            let slice = assign_cell.offset..(assign_cell.offset + assign_cell.update.len());
            nets[slice.clone()].copy_from_slice(
                &design.add_mux(assign_cell.enable, &assign_cell.update, assign_cell.value.slice(slice))[..],
            );
            design.replace_value(cell_ref.output(), Value::from(nets));
        }
    }

    design.compact();
}

impl Display for MatchRow {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        for (index, trit) in self.pattern.iter().rev().enumerate() {
            if index != 0 && index % 4 == 0 {
                write!(f, "_")?;
            }
            write!(f, "{trit}")?;
        }
        write!(f, " =>")?;
        if self.rules.len() == 0 {
            return write!(f, " (empty)");
        }
        for rule in &self.rules {
            write!(f, " {rule}")?;
        }
        Ok(())
    }
}

impl Display for MatchMatrix {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}:\n", self.value)?;
        for row in &self.rows {
            write!(f, "  {row}\n")?;
        }
        Ok(())
    }
}

impl Decision {
    fn format(&self, f: &mut std::fmt::Formatter, level: usize) -> std::fmt::Result {
        let format_rules = |f: &mut std::fmt::Formatter, rules: &BTreeSet<Net>| {
            if rules.is_empty() {
                write!(f, " (empty)")
            } else {
                for rule in rules {
                    write!(f, " {rule}")?;
                }
                Ok(())
            }
        };

        let format_decision = |f: &mut std::fmt::Formatter, net: Net, value: usize, decision: &Decision| {
            if let Decision::Result { rules } = decision {
                if rules.is_empty() {
                    return Ok(());
                }
            }
            for _ in 0..level {
                write!(f, "  ")?;
            }
            match decision {
                Decision::Result { rules } => {
                    write!(f, "{net} = {value} =>")?;
                    format_rules(f, &rules)?;
                    write!(f, "\n")
                }
                Decision::Branch { .. } => {
                    write!(f, "{net} = {value} =>\n")?;
                    decision.format(f, level + 1)
                }
            }
        };

        match self {
            Decision::Result { rules } => {
                assert_eq!(level, 0);
                write!(f, "=>")?;
                format_rules(f, &rules)?;
                write!(f, "\n")?;
            }
            Decision::Branch { net, if0, if1 } => {
                format_decision(f, *net, 0, if0)?;
                format_decision(f, *net, 1, if1)?;
            }
        }
        Ok(())
    }
}

impl Display for Decision {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.format(f, 0)
    }
}

#[cfg(test)]
mod test {
    #![allow(non_snake_case)]

    use std::collections::{BTreeMap, BTreeSet};

    use prjunnamed_netlist::{Cell, Const, Design, MatchCell, Net, Trit, Value};

    use super::{Decision, MatchMatrix, MatchRow, match_tree_into_matrix};

    struct Helper(Design);

    impl Helper {
        fn new() -> Self {
            Self(Design::new())
        }

        fn pat(&self, pattern: &str) -> Const {
            Const::from_iter(pattern.chars().map(Trit::lit))
        }

        fn val(&self, width: usize) -> Value {
            self.0.add_void(width)
        }

        fn net(&self) -> Net {
            self.0.add_void(1).unwrap_net()
        }

        fn rs(&self, rule: Net) -> Box<Decision> {
            Box::new(Decision::Result { rules: BTreeSet::from_iter([rule]) })
        }

        fn br(&self, net: Net, if1: Box<Decision>, if0: Box<Decision>) -> Box<Decision> {
            Box::new(Decision::Branch { net, if0, if1 })
        }
    }

    #[test]
    fn test_merge_1() {
        let h = Helper::new();

        let v1 = h.val(2);
        let (n11, n12) = (h.net(), h.net());
        let v2 = h.val(3);
        let (n21, n22) = (h.net(), h.net());
        let mut m1 = MatchMatrix::new(&v1);
        m1.add(MatchRow::new(h.pat("01"), [n11]));
        m1.add(MatchRow::new(h.pat("10"), [n12]));

        let mut m2 = MatchMatrix::new(&v2);
        m2.add(MatchRow::new(h.pat("00X"), [n21]));
        m2.add(MatchRow::new(h.pat("X01"), [n22]));

        let ml1 = m1.clone().merge(n12, &m2);

        let mut mr1 = MatchMatrix::new(v1.concat(&v2));
        mr1.add(MatchRow::new(h.pat("01XXX"), [n11]));
        mr1.add(MatchRow::new(h.pat("1000X"), [n12, n21]));
        mr1.add(MatchRow::new(h.pat("10X01"), [n12, n22]));
        mr1.add(MatchRow::new(h.pat("10XXX"), [n12]));

        assert_eq!(ml1, mr1, "\n{ml1} != \n{mr1}");
    }

    #[test]
    fn test_merge_2() {
        let h = Helper::new();

        let v1 = h.val(2);
        let (n11, n12) = (h.net(), h.net());
        let v2 = h.val(3);
        let (n21, n22) = (h.net(), h.net());
        let mut m1 = MatchMatrix::new(&v1);
        m1.add(MatchRow::new(h.pat("01"), [n11]));
        m1.add(MatchRow::new(h.pat("10"), [n11]));
        m1.add(MatchRow::new(h.pat("XX"), [n12]));

        let mut m2 = MatchMatrix::new(&v2);
        m2.add(MatchRow::new(h.pat("00X"), [n21]));
        m2.add(MatchRow::new(h.pat("X01"), [n22]));

        let ml1 = m1.clone().merge(n11, &m2);

        let mut mr1 = MatchMatrix::new(v1.concat(&v2));
        mr1.add(MatchRow::new(h.pat("0100X"), [n11, n21]));
        mr1.add(MatchRow::new(h.pat("01X01"), [n11, n22]));
        mr1.add(MatchRow::new(h.pat("01XXX"), [n11]));
        mr1.add(MatchRow::new(h.pat("1000X"), [n11, n21]));
        mr1.add(MatchRow::new(h.pat("10X01"), [n11, n22]));
        mr1.add(MatchRow::new(h.pat("10XXX"), [n11]));
        mr1.add(MatchRow::new(h.pat("XXXXX"), [n12]));

        assert_eq!(ml1, mr1, "\n{ml1} != \n{mr1}");
    }

    #[test]
    fn test_slice() {
        let h = Helper::new();

        let v = h.val(2);
        let (n1, n2) = (h.net(), h.net());
        let mut m = MatchMatrix::new(&v);
        m.add(MatchRow::new(h.pat("01"), [n1]));
        m.add(MatchRow::new(h.pat("10"), [n1]));
        m.add(MatchRow::new(h.pat("XX"), [n2]));

        let mut mr1 = MatchMatrix::new(&v);
        mr1.add(MatchRow::new(h.pat("01"), [n1]));
        mr1.add(MatchRow::new(h.pat("10"), [n1]));
        mr1.add(MatchRow::new(h.pat("XX"), []));

        let mut mr2 = MatchMatrix::new(&v);
        mr2.add(MatchRow::new(h.pat("01"), []));
        mr2.add(MatchRow::new(h.pat("10"), []));
        mr2.add(MatchRow::new(h.pat("XX"), [n2]));

        assert_eq!(m.clone().slice(&BTreeSet::from_iter([n1])), mr1);
        assert_eq!(m.clone().slice(&BTreeSet::from_iter([n2])), mr2);
    }

    #[test]
    fn test_normalize_vertical() {
        let h = Helper::new();
        let n = h.net();

        let mut m00 = MatchMatrix::new(&Value::from(Const::lit("0")));
        m00.add(MatchRow::new(h.pat("0"), [n]));

        let mut m01 = MatchMatrix::new(&Value::from(Const::lit("0")));
        m01.add(MatchRow::new(h.pat("1"), [n]));

        let mut m0X = MatchMatrix::new(&Value::from(Const::lit("0")));
        m0X.add(MatchRow::new(h.pat("X"), [n]));

        let mut m10 = MatchMatrix::new(&Value::from(Const::lit("1")));
        m10.add(MatchRow::new(h.pat("0"), [n]));

        let mut m11 = MatchMatrix::new(&Value::from(Const::lit("1")));
        m11.add(MatchRow::new(h.pat("1"), [n]));

        let mut m1X = MatchMatrix::new(&Value::from(Const::lit("1")));
        m1X.add(MatchRow::new(h.pat("X"), [n]));

        let mut mX0 = MatchMatrix::new(&Value::from(Const::lit("X")));
        mX0.add(MatchRow::new(h.pat("0"), [n]));

        let mut mX1 = MatchMatrix::new(&Value::from(Const::lit("X")));
        mX1.add(MatchRow::new(h.pat("1"), [n]));

        let mut mXX = MatchMatrix::new(&Value::from(Const::lit("X")));
        mXX.add(MatchRow::new(h.pat("X"), [n]));

        for must_reject in [m01, m10, mX0, mX1] {
            let normalized = must_reject.clone().normalize();
            assert_eq!(normalized.rows.len(), 0, "before:\n{must_reject}\nafter:\n{normalized}");
        }
        for must_accept in [m00, m0X, m11, m1X, mXX] {
            let normalized = must_accept.clone().normalize();
            assert_eq!(normalized.rows.len(), 1, "before:\n{must_accept}\nafter:\n{normalized}");
            assert_eq!(normalized.rows[0].pattern.len(), 0, "before:\n{must_accept}\nafter:\n{normalized}");
        }
    }

    #[test]
    fn test_normalize_horizontal() {
        let h = Helper::new();
        let v = h.val(1);
        let n = h.net();

        let mut m1 = MatchMatrix::new(v.concat(&v));
        m1.add(MatchRow::new(h.pat("X0"), [n]));
        m1 = m1.normalize();
        assert_eq!(m1.rows[0].pattern, h.pat("0"));

        let mut m2 = MatchMatrix::new(v.concat(&v));
        m2.add(MatchRow::new(h.pat("0X"), [n]));
        m2 = m2.normalize();
        assert_eq!(m2.rows[0].pattern, h.pat("0"));

        let mut m3 = MatchMatrix::new(v.concat(&v));
        m3.add(MatchRow::new(h.pat("01"), [n]));
        m3 = m3.normalize();
        assert_eq!(m3.rows.len(), 0);
    }

    #[test]
    fn test_normalize_duplicate_row() {
        let h = Helper::new();
        let v = h.val(2);
        let (n1, n2) = (h.net(), h.net());

        let mut m = MatchMatrix::new(v);
        m.add(MatchRow::new(h.pat("01"), [n1]));
        m.add(MatchRow::new(h.pat("01"), [n2]));
        m = m.normalize();
        assert_eq!(m.rows.len(), 1);
        assert_eq!(m.rows[0].pattern, h.pat("01"));
        assert_eq!(m.rows[0].rules, BTreeSet::from_iter([n1]));
    }

    #[test]
    fn test_normalize_irrefitable() {
        let h = Helper::new();
        let v = h.val(2);
        let (n1, n2) = (h.net(), h.net());

        let mut m = MatchMatrix::new(v);
        m.add(MatchRow::new(h.pat("XX"), [n1]));
        m.add(MatchRow::new(h.pat("01"), [n2]));
        m = m.normalize();
        assert_eq!(m.rows.len(), 1);
        assert_eq!(m.rows[0].pattern, h.pat("XX"));
        assert_eq!(m.rows[0].rules, BTreeSet::from_iter([n1]));
    }

    #[test]
    fn test_normalize_unused_column() {
        let h = Helper::new();
        let v = h.val(2);
        let (n1, n2) = (h.net(), h.net());

        let mut m = MatchMatrix::new(&v);
        m.add(MatchRow::new(h.pat("0X"), [n1]));
        m.add(MatchRow::new(h.pat("1X"), [n2]));
        m = m.normalize();
        assert_eq!(m.value, v.slice(0..1));
        assert_eq!(m.rows.len(), 2);
        assert_eq!(m.rows[0], MatchRow::new(h.pat("0"), [n1]));
        assert_eq!(m.rows[1], MatchRow::new(h.pat("1"), [n2]));
    }

    macro_rules! assert_dispatch {
        ($m:expr, $d:expr) => {
            let dl = $m.clone().dispatch();
            let dr = $d;
            assert!(dl == dr, "\ndispatching {}\n{} != \n{}", $m, dl, dr);
        };
    }

    #[test]
    fn test_decide_0() {
        let h = Helper::new();

        let v = h.val(1);
        let n = h.net();
        let mut m = MatchMatrix::new(&v);
        m.add(MatchRow::new(h.pat("0"), [n]));

        let d = h.rs(n);

        assert_dispatch!(m, d);
    }

    #[test]
    fn test_decide_0_1() {
        let h = Helper::new();

        let v = h.val(1);
        let (n1, n2) = (h.net(), h.net());
        let mut m = MatchMatrix::new(&v);
        m.add(MatchRow::new(h.pat("0"), [n1]));
        m.add(MatchRow::new(h.pat("1"), [n2]));

        let d = h.br(v[0], h.rs(n2), h.rs(n1));

        assert_dispatch!(m, d);
    }

    #[test]
    fn test_decide_0_X() {
        let h = Helper::new();

        let v = h.val(1);
        let (n1, n2) = (h.net(), h.net());
        let mut m = MatchMatrix::new(&v);
        m.add(MatchRow::new(h.pat("0"), [n1]));
        m.add(MatchRow::new(h.pat("X"), [n2]));

        let d = h.br(v[0], h.rs(n2), h.rs(n1));

        assert_dispatch!(m, d);
    }

    #[test]
    fn test_decide_1_X() {
        let h = Helper::new();

        let v = h.val(1);
        let (n1, n2) = (h.net(), h.net());
        let mut m = MatchMatrix::new(&v);
        m.add(MatchRow::new(h.pat("1"), [n1]));
        m.add(MatchRow::new(h.pat("X"), [n2]));

        let d = h.br(v[0], h.rs(n1), h.rs(n2));

        assert_dispatch!(m, d);
    }

    #[test]
    fn test_decide_X_0_1() {
        let h = Helper::new();

        let v = h.val(1);
        let (n1, n2, n3) = (h.net(), h.net(), h.net());
        let mut m = MatchMatrix::new(&v);
        m.add(MatchRow::new(h.pat("X"), [n1]));
        m.add(MatchRow::new(h.pat("0"), [n2]));
        m.add(MatchRow::new(h.pat("1"), [n3]));

        let d = h.rs(n1);

        assert_dispatch!(m, d);
    }

    #[test]
    fn test_decide_0_1_X() {
        let h = Helper::new();

        let v = h.val(1);
        let (n1, n2, n3) = (h.net(), h.net(), h.net());
        let mut m = MatchMatrix::new(&v);
        m.add(MatchRow::new(h.pat("0"), [n1]));
        m.add(MatchRow::new(h.pat("1"), [n2]));
        m.add(MatchRow::new(h.pat("X"), [n3]));

        let d = h.br(v[0], h.rs(n2), h.rs(n1));

        assert_dispatch!(m, d);
    }

    #[test]
    fn test_decide_0X_1X_XX() {
        let h = Helper::new();

        let v = h.val(2);
        let (n1, n2, n3) = (h.net(), h.net(), h.net());
        let mut m = MatchMatrix::new(&v);
        m.add(MatchRow::new(h.pat("0X"), [n1]));
        m.add(MatchRow::new(h.pat("1X"), [n2]));
        m.add(MatchRow::new(h.pat("XX"), [n3]));

        let d = h.br(v[0], h.rs(n2), h.rs(n1));

        assert_dispatch!(m, d);
    }

    #[test]
    fn test_decide_0X_11_XX() {
        let h = Helper::new();

        let v = h.val(2);
        let (n1, n2, n3) = (h.net(), h.net(), h.net());
        let mut m = MatchMatrix::new(&v);
        m.add(MatchRow::new(h.pat("X0"), [n1]));
        m.add(MatchRow::new(h.pat("11"), [n2]));
        m.add(MatchRow::new(h.pat("XX"), [n3]));

        let d = h.br(v[1], h.br(v[0], h.rs(n2), h.rs(n3)), h.rs(n1));

        assert_dispatch!(m, d);
    }

    #[test]
    fn test_decide_00_10_XX() {
        let h = Helper::new();

        let v = h.val(2);
        let (n1, n2) = (h.net(), h.net());
        let mut m = MatchMatrix::new(&v);
        m.add(MatchRow::new(h.pat("00"), [n1]));
        m.add(MatchRow::new(h.pat("10"), [n1]));
        m.add(MatchRow::new(h.pat("XX"), [n2]));

        let d = h.br(v[1], h.rs(n2), h.rs(n1));

        assert_dispatch!(m, d);
    }

    #[test]
    fn test_match_cell_into_matrix_flat() {
        let mut design = Design::new();
        let a = design.add_input("a", 3);
        let y = design.add_match(MatchCell {
            value: a.clone(),
            enable: Net::ONE,
            patterns: vec![vec![Const::lit("000"), Const::lit("111")], vec![Const::lit("010")]],
        });
        let yy = design.add_buf(&y);
        design.add_output("y", &yy);
        design.apply();

        let m = match_tree_into_matrix(&design, &BTreeMap::new(), design.find_cell(y[0]).unwrap().0, Net::ONE);
        design.apply();

        let Cell::Buf(y) = &*design.find_cell(yy[0]).unwrap().0.get() else { unreachable!() };
        assert_eq!(m.value, a);
        assert_eq!(m.rows, vec![
            MatchRow::new(Const::lit("000"), [y[0]]),
            MatchRow::new(Const::lit("111"), [y[0]]),
            MatchRow::new(Const::lit("010"), [y[1]]),
            MatchRow::new(Const::lit("XXX"), []),
        ]);
    }

    #[test]
    fn test_match_cell_into_matrix_nested() {
        let mut design = Design::new();
        let a = design.add_input("a", 3);
        let b = design.add_input("b", 2);
        let ya = design.add_match(MatchCell {
            value: a.clone(),
            enable: Net::ONE,
            patterns: vec![vec![Const::lit("000"), Const::lit("111")], vec![Const::lit("010")]],
        });
        let yb = design.add_match(MatchCell {
            value: b.clone(),
            enable: ya[1],
            patterns: vec![vec![Const::lit("00")], vec![Const::lit("11")]],
        });
        let yya = design.add_buf(&ya);
        let yyb = design.add_buf(&yb);
        design.add_output("ya", &yya);
        design.add_output("yb", &yyb);
        design.apply();

        let mut subtrees = BTreeMap::new();
        subtrees.insert(design.find_cell(ya[1]).unwrap(), design.find_cell(yb[0]).unwrap().0);

        let ml = match_tree_into_matrix(&design, &subtrees, design.find_cell(ya[0]).unwrap().0, Net::ONE);
        design.apply();

        let Cell::Buf(ya) = &*design.find_cell(yya[0]).unwrap().0.get() else { unreachable!() };
        let Cell::Buf(yb) = &*design.find_cell(yyb[0]).unwrap().0.get() else { unreachable!() };
        let mut mr = MatchMatrix::new(a.concat(b));
        mr.add(MatchRow::new(Const::lit("XX000"), [ya[0]]));
        mr.add(MatchRow::new(Const::lit("XX111"), [ya[0]]));
        mr.add(MatchRow::new(Const::lit("00010"), [ya[1], yb[0]]));
        mr.add(MatchRow::new(Const::lit("11010"), [ya[1], yb[1]]));
        mr.add(MatchRow::new(Const::lit("XX010"), [ya[1]]));
        mr.add(MatchRow::new(Const::lit("XX010"), [ya[1]]));
        mr.add(MatchRow::new(Const::lit("XXXXX"), []));

        assert_eq!(ml, mr, "\n{ml} != \n{mr}");
    }
}
