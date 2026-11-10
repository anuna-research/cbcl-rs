//! Independent Lean checker receives authored contracts and values, never Rust verdicts.
use cbcl_core::{
    contracts::CheckError,
    numeric::{Decimal, Float},
    sexpr::{Atom, SExpr},
    shape::ShapeRule,
};
use cbcl_parser::dialect_parser::parse_dialect;
use serde_json::{json, Value};
use std::{
    io::{BufRead, BufReader, Write},
    process::{Child, ChildStdin, ChildStdout, Command, Stdio},
};

struct Oracle {
    child: Child,
    input: ChildStdin,
    output: BufReader<ChildStdout>,
    count: usize,
}
impl Oracle {
    fn new() -> Self {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../lean-cbcl/.lake/build/bin/cbcl-flat-contract-oracle");
        let mut child = Command::new(path)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .expect("build cbcl-flat-contract-oracle first");
        Self {
            input: child.stdin.take().unwrap(),
            output: BufReader::new(child.stdout.take().unwrap()),
            child,
            count: 0,
        }
    }
    fn ask(&mut self, request: &Value) -> Value {
        writeln!(self.input, "{request}").unwrap();
        self.input.flush().unwrap();
        let mut line = String::new();
        self.output.read_line(&mut line).unwrap();
        self.count += 1;
        serde_json::from_str(&line).expect("oracle returned JSON")
    }
    fn compare(&mut self, definitions: Value, contract: Value, value: Value, work: u64) {
        let request =
            json!({"definitions":definitions,"contract":contract,"value":value,"work":work});
        let actual = rust(&request);
        let reference = self.ask(&request);
        assert_eq!(reference, json!({"verdict":actual}), "request {request}");
    }
}
impl Drop for Oracle {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}
fn text(v: &Value) -> &str {
    v.as_str().unwrap()
}
fn sym(s: &str) -> SExpr {
    SExpr::Atom(Atom::Symbol(s.into()))
}
fn list(xs: Vec<SExpr>) -> SExpr {
    SExpr::List(xs)
}
fn atom(v: &Value) -> SExpr {
    let a = v.as_array().unwrap();
    SExpr::Atom(match text(&a[0]) {
        "integer" => Atom::Num(text(&a[1]).parse().unwrap()),
        "float" => Atom::Float(Float::new(f64::from_bits(text(&a[1]).parse().unwrap())).unwrap()),
        "decimal" => {
            let coefficient = text(&a[1]);
            let scale = a[2].as_u64().unwrap() as usize;
            let negative = coefficient.starts_with('-');
            let digits = coefficient.trim_start_matches('-');
            let padded = format!("{:0>width$}", digits, width = scale + 1);
            let value = if scale == 0 {
                padded
            } else {
                format!(
                    "{}.{}",
                    &padded[..padded.len() - scale],
                    &padded[padded.len() - scale..]
                )
            };
            Atom::Decimal(
                format!("{}{value}", if negative { "-" } else { "" })
                    .parse::<Decimal>()
                    .unwrap(),
            )
        }
        "string" => Atom::Str(text(&a[1]).into()),
        "symbol" => Atom::Symbol(text(&a[1]).into()),
        "keyword" => Atom::Keyword(text(&a[1]).into()),
        "bool" => Atom::Bool(a[1].as_bool().unwrap()),
        _ => panic!("invalid atom"),
    })
}
fn value(v: &Value) -> SExpr {
    let a = v.as_array().unwrap();
    if a[0] == "list" {
        list(a[1..].iter().map(value).collect())
    } else {
        atom(v)
    }
}
fn predicate(v: &Value) -> SExpr {
    let a = v.as_array().unwrap();
    let op = text(&a[0]);
    let mut xs = vec![sym(op)];
    if op == "length" {
        xs.extend(a[1..].iter().map(|b| {
            list(vec![
                sym(text(&b[0])),
                SExpr::Atom(Atom::Num(b[1].as_i64().unwrap())),
            ])
        }));
    } else if op == "matches" {
        xs.push(SExpr::Atom(Atom::Str(text(&a[1]).into())));
    } else {
        xs.push(atom(&a[1]));
    }
    list(xs)
}
fn expr(v: &Value) -> SExpr {
    let a = v.as_array().unwrap();
    match text(&a[0]) {
        "builtin" | "ref" => sym(text(&a[1])),
        "enum" => {
            let mut xs = vec![sym("one-of")];
            xs.extend(a[1..].iter().map(atom));
            list(xs)
        }
        "refine" => {
            let mut xs = vec![sym(text(&a[1]))];
            xs.extend(a[2..].iter().map(predicate));
            list(xs)
        }
        "all" | "any" => {
            let mut xs = vec![sym(if a[0] == "all" { "and" } else { "or" })];
            xs.extend(a[1..].iter().map(expr));
            list(xs)
        }
        _ => panic!("invalid expression"),
    }
}
fn rust(request: &Value) -> &'static str {
    let mut declarations = String::new();
    for d in request["definitions"].as_array().unwrap() {
        declarations.push_str(&format!(" (type {} {})", text(&d[0]), expr(&d[1])));
    }
    let source = format!("(define contracts (cbcl) @author (extend submit (to value) (tell to :value value)) (shape submit (require :value {})) {declarations})", expr(&request["contract"]));
    let d = match parse_dialect(&source.parse::<SExpr>().unwrap()) {
        Ok(d) => d,
        Err(_) => return "definition-error",
    };
    let ShapeRule::Require {
        type_constraint, ..
    } = &d.shapes[0].rules[0]
    else {
        panic!("required field")
    };
    match type_constraint
        .as_ref()
        .unwrap()
        .check(&value(&request["value"]), request["work"].as_u64().unwrap())
    {
        Ok(()) => "accepted",
        Err(CheckError::Violation(_)) => "violation",
        Err(CheckError::ResourceLimit) => "resource-limit",
        Err(CheckError::InvalidDefinition(_)) => "definition-error",
    }
}
fn int(n: i64) -> Value {
    json!(["integer", n.to_string()])
}
fn float(n: f64) -> Value {
    json!(["float", Float::new(n).unwrap().get().to_bits().to_string()])
}
fn decimal(n: i64, scale: u32) -> Value {
    json!(["decimal", n.to_string(), scale])
}

#[test]
#[ignore = "requires pinned Lean build: lake build cbcl-flat-contract-oracle"]
fn lean_flat_contract_differential() {
    let mut oracle = Oracle::new();
    let values = vec![
        int(i64::MIN),
        int(-1),
        int(0),
        int(1),
        int(i64::MAX),
        int(9_007_199_254_740_993),
        float(-f64::MAX),
        float(-0.0),
        float(f64::from_bits(1)),
        float(0.1),
        float(1.0),
        float(f64::MAX),
        decimal(0, 0),
        decimal(1, 0),
        decimal(1, 1),
        decimal(-1, 1),
        decimal(9007199254740993, 0),
        json!(["string", ""]),
        json!(["string", "😀"]),
        json!(["string", "é"]),
        json!(["string", "abc"]),
        json!(["string", "hlc-0000000000000000-00000000"]),
        json!(["symbol", "x"]),
        json!(["keyword", "AUD"]),
        json!(["bool", true]),
        json!(["list"]),
        json!(["list", ["list", ["integer", "1"]]]),
    ];
    let mut contracts = Vec::new();
    for name in [
        "integer",
        "float",
        "decimal",
        "number",
        "nonnegative",
        "string",
        "hlc",
        "symbol",
        "keyword",
        "bool",
        "list",
    ] {
        contracts.push(json!(["builtin", name]));
    }
    for kind in ["integer", "float", "decimal", "number"] {
        for op in [">", ">=", "<", "<="] {
            for bound in [
                int(0),
                int(9_007_199_254_740_992),
                decimal(1, 1),
                float(f64::from_bits(1)),
            ] {
                contracts.push(json!(["refine", kind, [op, bound]]));
            }
        }
    }
    for kind in ["string", "list"] {
        contracts.push(json!(["refine", kind, ["length", [">", 0], ["<=", 2]]]));
    }
    contracts.extend([
        json!(["enum", int(1)]),
        json!(["enum", float(1.0), decimal(1, 0)]),
        json!(["any", ["builtin", "integer"], ["builtin", "string"]]),
        json!([
            "all",
            ["builtin", "number"],
            ["refine", "number", [">", int(0)]]
        ]),
    ]);
    for c in &contracts {
        for v in &values {
            for work in [0, 1, 268_435_456, 1 << 35] {
                oracle.compare(json!([]), c.clone(), v.clone(), work);
            }
        }
    }
    let defs = json!([
        ["alias", ["ref", "later"]],
        ["later", ["refine", "number", [">", int(0)]]]
    ]);
    for definitions in [defs.clone(), json!([defs[1], defs[0]])] {
        for v in &values {
            oracle.compare(
                definitions.clone(),
                json!(["ref", "alias"]),
                v.clone(),
                1 << 35,
            );
        }
    }
    for definitions in [
        json!([["a", ["ref", "missing"]]]),
        json!([["a", ["ref", "a"]]]),
        json!([["a", ["ref", "b"]], ["b", ["ref", "a"]]]),
        json!([["a", ["builtin", "string"]], ["a", ["builtin", "string"]]]),
        json!([["integer", ["builtin", "string"]]]),
        json!([["and", ["builtin", "string"]]]),
        json!([["A", ["builtin", "string"]]]),
    ] {
        oracle.compare(
            definitions,
            json!(["builtin", "string"]),
            json!(["string", "x"]),
            1 << 35,
        );
    }
    for c in [
        json!(["ref", "missing"]),
        json!(["enum"]),
        json!(["enum", int(1), int(1)]),
        json!(["all"]),
        json!(["any", ["builtin", "string"]]),
        json!(["all", ["builtin", "string"], ["builtin", "integer"]]),
        json!(["refine", "number", [">", int(2)], ["<=", int(2)]]),
        json!(["refine", "string", ["length", ["<", 0]]]),
        json!(["refine", "bool", [">", int(0)]]),
        json!(["refine", "integer", ["length", [">", 0]]]),
        json!(["refine", "string", ["length"]]),
        json!(["refine", "integer"]),
    ] {
        oracle.compare(json!([]), c, int(1), 1 << 35);
    }
    for pattern in ["", ".", "[0-9]{4}", "INV-[0-9]+", "^x$"] {
        for text in [
            "", "😀", "\n", "\r", "1234", "١٢٣٤", "INV-123", "INV-", "^x$", "x",
        ] {
            for work in [0, 1 << 35] {
                oracle.compare(
                    json!([]),
                    json!(["refine", "string", ["matches", pattern]]),
                    json!(["string", text]),
                    work,
                );
            }
        }
    }
    for n in [65534, 65535, 65536] {
        oracle.compare(
            json!([]),
            json!(["builtin", "string"]),
            json!(["string", "a".repeat(n)]),
            1 << 35,
        );
    }
    for (contract, required) in [
        (json!(["refine", "number", [">=", int(0)]]), 268_435_457_u64),
        (json!(["enum", int(1)]), 65_537),
        (
            json!(["refine", "list", ["length", [">", 0], ["<=", 2]]]),
            196_609,
        ),
        (
            json!(["any", ["builtin", "integer"], ["builtin", "string"]]),
            3,
        ),
    ] {
        for work in [required - 1, required, required + 1] {
            oracle.compare(json!([]), contract.clone(), int(1), work);
        }
    }
    for depth in [31, 32, 33] {
        let mut v = int(1);
        for _ in 0..depth {
            v = json!(["list", v]);
        }
        oracle.compare(json!([]), json!(["builtin", "list"]), v, 1 << 35);
    }
    for digits in [4095, 4096, 4097] {
        oracle.compare(
            json!([]),
            json!(["builtin", "decimal"]),
            json!(["decimal", "1".repeat(digits), 0]),
            1 << 35,
        );
    }
    for depth in [31, 32, 33] {
        let defs: Vec<_> = (0..depth)
            .map(|n| {
                json!([
                    format!("a{n}"),
                    if n + 1 == depth {
                        json!(["builtin", "string"])
                    } else {
                        json!(["ref", format!("a{}", n + 1)])
                    }
                ])
            })
            .collect();
        oracle.compare(
            json!(defs),
            json!(["ref", "a0"]),
            json!(["string", "x"]),
            1 << 35,
        );
    }
    oracle.compare(
        json!([["loop", ["ref", "loop"]]]),
        json!(["any", ["builtin", "string"], ["ref", "loop"]]),
        json!(["string", "x"]),
        1 << 35,
    );
    oracle.compare(
        json!([["s", ["builtin", "string"]], ["i", ["builtin", "integer"]]]),
        json!(["all", ["ref", "s"], ["ref", "i"]]),
        int(1),
        1 << 35,
    );
    for digits in [4095, 4096, 4097] {
        for contract in [
            json!(["enum", ["decimal", "1".repeat(digits), 0]]),
            json!([
                "refine",
                "number",
                [">=", ["decimal", "1".repeat(digits), 0]]
            ]),
        ] {
            oracle.compare(json!([]), contract, int(0), 1 << 35);
        }
    }
    for depth in [29, 30, 31, 32] {
        let mut contract = json!(["refine", "number", [">=", int(0)]]);
        for _ in 0..depth {
            contract = json!(["any", contract, ["builtin", "string"]]);
        }
        oracle.compare(json!([]), contract, int(0), 1 << 35);
    }
    for work in [196_608, 196_609, 196_610] {
        oracle.compare(
            json!([]),
            json!(["refine", "list", ["length", [">", 0], ["<=", 2]]]),
            json!(["list", int(1)]),
            work,
        );
    }
    let diamond = json!([
        ["base", ["refine", "integer", [">=", int(0)]]],
        ["left", ["ref", "base"]],
        ["right", ["ref", "base"]],
        [
            "top",
            ["all", ["ref", "left"], ["ref", "right"], ["ref", "left"]]
        ]
    ]);
    for definitions in [
        diamond.clone(),
        json!([diamond[3], diamond[1], diamond[0], diamond[2]]),
    ] {
        for value in [int(-1), int(0), int(1)] {
            for work in [0, 1 << 35] {
                oracle.compare(
                    definitions.clone(),
                    json!(["ref", "top"]),
                    value.clone(),
                    work,
                );
            }
        }
    }
    for constructor in ["all", "any"] {
        for operands in [
            [
                json!(["builtin", "integer"]),
                json!(["refine", "number", [">=", int(0)]]),
            ],
            [
                json!(["refine", "number", [">=", int(0)]]),
                json!(["builtin", "integer"]),
            ],
        ] {
            for value in [int(-1), int(0), float(1.0)] {
                oracle.compare(
                    json!([]),
                    json!([constructor, operands[0], operands[1]]),
                    value,
                    1 << 35,
                );
            }
        }
    }
    let outside = oracle.ask(&json!({"definitions":[],"contract":["enum",["string","x".repeat(8192)]],"value":["string","x"],"work":1_u64<<35}));
    assert_eq!(
        outside,
        json!({"error":"unsupported oracle source-size profile"})
    );
    let unsupported = oracle.ask(&json!({"definitions":[],"contract":["refine","string",["matches","a*"]],"value":["string","a"],"work":1_u64<<35}));
    assert_eq!(
        unsupported,
        json!({"error":"unsupported oracle regex profile"})
    );
    eprintln!("{} independent Lean requests passed", oracle.count);
}
