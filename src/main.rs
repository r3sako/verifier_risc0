mod parser;
mod ir;
mod verifier;
mod verifier_int;

use parser::Parser;
use parser::ast::Item;
use ir::ComponentDB;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let cmd = args.get(1).map(|s| s.as_str()).unwrap_or("help");

    match cmd {
        "parse" => cmd_parse(args.get(2).map(|s| s.as_str()).unwrap_or("specs/u32.zir")),
        "list"  => cmd_list(args.get(2).map(|s| s.as_str()).unwrap_or("specs/u32.zir")),
        "ir"    => cmd_ir(
            args.get(2).map(|s| s.as_str()).unwrap_or("specs/u32.zir"),
            args.get(3).map(|s| s.as_str()).unwrap_or("AddU32"),
        ),
        "verify" => {
            let (file, instr, abs) = parse_verify_args(&args, "specs/u32.zir");
            cmd_verify(file, instr, false, abs);
        }
        "verify-int" => {
            let (file, instr, abs) = parse_verify_args(&args, "specs/mult.zir");
            cmd_verify(file, instr, true, abs);
        }
        _ => {
            println!("zkvm-verifier — автоматический верификатор инструкций RISC Zero\n");
            println!("Использование:");
            println!("  zkvm-verifier parse <file.zir>              — парсинг .zir файла");
            println!("  zkvm-verifier list <file.zir>               — список компонентов");
            println!("  zkvm-verifier ir <file.zir> <instruction>   — показать IR");
            println!("  zkvm-verifier verify <file.zir> <instr>     — верификация (BV<32>)");
            println!("  zkvm-verifier verify-int <file.zir> <instr> — верификация (Int/QF_NIA)");
            println!();
            println!("Опционально (только для verify-int):");
            println!("  --abstract=COMP1,COMP2  — заменить инлайн этих компонентов на UF-абстракцию.");
            println!("                            Подходит для модульной верификации композитов:");
            println!("                            компоненты, доказанные независимо, становятся");
            println!("                            uninterpreted functions — same args → same outputs.");
            println!();
            println!("Пример: verify-int specs/mult.zir MultiplyAccumulate --abstract=ExpandU32,SplitTotal");
        }
    }
}

/// Парсит args после команды `verify` / `verify-int`.
/// Поддерживает `--abstract=COMP1,COMP2,...` флаг и позиционные file/instr.
fn parse_verify_args<'a>(args: &'a [String], default_file: &'a str) -> (&'a str, &'a str, Vec<String>) {
    let mut abs: Vec<String> = Vec::new();
    let mut positional: Vec<&str> = Vec::new();
    for a in &args[2..] {
        if let Some(rest) = a.strip_prefix("--abstract=") {
            abs = rest.split(',').filter(|s| !s.is_empty()).map(String::from).collect();
        } else if !a.starts_with("--") {
            positional.push(a.as_str());
        }
    }
    let file = positional.first().copied().unwrap_or(default_file);
    let instr = positional.get(1).copied().unwrap_or("all");
    (file, instr, abs)
}

fn load(path: &str) -> Vec<Item> {
    let mut all: Vec<Item> = Vec::new();
    let mut loaded: std::collections::HashSet<String> = std::collections::HashSet::new();
    load_recursive(path, &mut all, &mut loaded);
    all
}

/// Загружает .zir-файл и рекурсивно его `import X;` зависимости из той же директории.
/// Если файл импорта не найден на диске — это внешний модуль (bits/lookups/...),
/// его символы обрабатываются как builtin'ы в IR-уровне, импорт молча пропускаем.
fn load_recursive(path: &str, all: &mut Vec<Item>, loaded: &mut std::collections::HashSet<String>) {
    if !loaded.insert(path.to_string()) { return; }
    let src = std::fs::read_to_string(path)
        .unwrap_or_else(|e| { eprintln!("Ошибка чтения {}: {}", path, e); std::process::exit(1); });
    let items = Parser::parse_file(&src)
        .unwrap_or_else(|e| { eprintln!("Ошибка парсинга {}: {}", path, e); std::process::exit(1); });
    // Сначала рекурсивно подгружаем импорты, потом добавляем содержимое текущего файла.
    let dir = std::path::Path::new(path).parent().unwrap_or(std::path::Path::new("."));
    for it in &items {
        if let Item::Import(name) = it {
            let dep = dir.join(format!("{}.zir", name));
            if dep.exists() {
                load_recursive(dep.to_str().unwrap(), all, loaded);
            }
            // Иначе — внешний модуль (bits, lookups, is_zero, po2 и т.п.), пропускаем.
        }
    }
    for it in items {
        all.push(it);
    }
}

fn cmd_parse(file: &str) {
    let items = load(file);
    println!("=== Парсинг {} ===\n", file);
    let mut n = 0;
    for item in &items {
        match item {
            Item::Import(name) => println!("  import {}", name),
            Item::Component(c) => {
                n += 1;
                let p: Vec<_> = c.params.iter().map(|(n,t)| format!("{}: {}", n, t)).collect();
                println!("  {:2}. component {}({}) — {} stmts [строка {}]",
                    n, c.name, p.join(", "), c.body.len(), c.source_line);
            }
            Item::Extern { name, return_type } =>
                println!("  extern {} : {}", name, return_type),
        }
    }
    println!("\n  Итого: {} компонентов | Парсинг: OK ✓", n);
}

fn cmd_list(file: &str) {
    let items = load(file);
    let db = ComponentDB::new(&items);
    println!("Компоненты в {}:", file);
    for name in db.names() { println!("  - {}", name); }
}

fn cmd_ir(file: &str, instr: &str) {
    let items = load(file);
    let db = ComponentDB::new(&items);
    match db.lower(instr) {
        Ok(spec) => {
            println!("=== IR: {} (строка {}) ===\n", spec.name, spec.source_line);
            println!("  Входы ({}):", spec.inputs.len());
            for v in &spec.inputs {
                let (mn, mx) = v.vtype.range();
                println!("    {} : {:?} [{}, {}]", v.name, v.vtype, mn, mx);
            }
            println!("  Выходы ({}):", spec.outputs.len());
            for v in &spec.outputs {
                let (mn, mx) = v.vtype.range();
                println!("    {} : {:?} [{}, {}]", v.name, v.vtype, mn, mx);
            }
            println!("  Промежуточные ({}):", spec.internals.len());
            for v in &spec.internals {
                let (mn, mx) = v.vtype.range();
                println!("    {} : {:?} [{}, {}]", v.name, v.vtype, mn, mx);
            }
            println!("  Ограничения ({}):", spec.constraints.len());
            for (i, c) in spec.constraints.iter().enumerate() {
                match c {
                    ir::IrConstraint::Eq { lhs, rhs, tag } =>
                        println!("    {}. {:?} = {:?}  [{}]", i+1, lhs, rhs, tag),
                    ir::IrConstraint::IsZero { result, expr } =>
                        println!("    {}. {} = IsZero({:?})", i+1, result, expr),
                    ir::IrConstraint::Call { component, args, outputs } => {
                        let outs: Vec<_> = outputs.iter().map(|(f, v)| format!("{}={}", f, v)).collect();
                        println!("    {}. UF[{}]({} args) → {}",
                            i+1, component, args.len(), outs.join(", "));
                    }
                }
            }
        }
        Err(e) => eprintln!("Ошибка: {}", e),
    }
}

fn cmd_verify(file: &str, instr: &str, use_int: bool, abstract_list: Vec<String>) {
    let items = load(file);
    let mut db = ComponentDB::new(&items);
    if !abstract_list.is_empty() {
        let refs: Vec<&str> = abstract_list.iter().map(String::as_str).collect();
        db.set_abstract(&refs);
    }

    // Дефолты для "all" зависят от файла — для u32.zir список одних, для mult.zir других.
    let targets: Vec<String> = if instr == "all" {
        if file.ends_with("mult.zir") {
            vec![
                "ExpandU32","SplitTotal","MultiplySettings",
                "MultiplyAccumulate","Expand32TestCase","MultiplyTestCase",
            ].into_iter().map(String::from).collect()
        } else if file.ends_with("div.zir") {
            vec!["DoDivU16", "DoDivU"].into_iter().map(String::from).collect()
        } else {
            vec![
                "AddU32","SubU32","NormalizeU32",
                "CmpEqual","CmpLessThanUnsigned","CmpLessThan",
                "GetSignU32",
                "BitwiseAnd","BitwiseOr","BitwiseXor",
                "AssertEqU32","CondDenormed","Denorm","Flat",
            ].into_iter().map(String::from).collect()
        }
    } else { vec![instr.to_string()] };

    println!("\n=== zkVM RISC Zero — Верификатор инструкций ===");
    println!("  Источник: {}", file);
    println!("  Метод: dual-instance determinism check");
    println!("  Теория: {}", if use_int { "QF_NIA (Int)" } else { "QF_BV (BitVec<32>)" });
    if !abstract_list.is_empty() {
        println!("  UF-абстракция: {}", abstract_list.join(", "));
    }
    println!("  Решатель: cvc5\n");
    println!("  {:<28} {:<6} {:<6} {:<28} {}", "Инструкция", "Пер.", "Огр.", "Результат", "Время");
    println!("  {}", "-".repeat(80));

    let mut total = 0;
    let mut det_count = 0;
    let mut nondet_count = 0;
    let mut skipped = 0;
    let mut errors = 0;

    for target in &targets {
        match db.lower(target) {
            Ok(spec) => {
                let r = if use_int {
                    verifier_int::verify_determinism(&spec)
                } else {
                    verifier::verify_determinism(&spec)
                };
                total += 1;
                let status = match r.deterministic {
                    Some(true)  => { det_count += 1; "✓ Детерминирован".to_string() }
                    Some(false) => { nondet_count += 1; "✗ НЕдетерминирован!".to_string() }
                    None => {
                        // Assertion-only компоненты без выходов — корректная ситуация
                        // (например, AssertEqU32 — нечего проверять на детерминизм).
                        let msg = r.error.as_deref().unwrap_or("?");
                        if msg.contains("No outputs") {
                            skipped += 1;
                            "— assertion-only (нечего проверять)".to_string()
                        } else {
                            errors += 1;
                            format!("⚠ {}", msg)
                        }
                    }
                };
                println!("  {:<28} {:<6} {:<6} {:<36} {}ms",
                    target, r.num_vars, r.num_constraints, status, r.time_ms);
            }
            Err(e) => {
                errors += 1;
                println!("  {:<28} {:<6} {:<6} {:<36}", target, "-", "-", format!("⚠ {}", e));
            }
        }
    }

    println!("  {}", "-".repeat(80));
    println!("\n  Итого: {} | Детерминированы: {} | Недетерм.: {} | Без выходов: {} | Ошибки: {}",
        total, det_count, nondet_count, skipped, errors);
    println!();
}
