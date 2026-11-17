//! A stream's entries pop in order: the same name hinted twice gets its first entry, then its
//! second, and a value the program asserts must be the entry's.

fn run(tree: &str, src: &str, witness: &[(String, Vec<Vec<stable_primitives::field::F128>>)]) -> Result<(), String> {
    let program = isa::Program::from(zkdsl_compiler::compile(&zkdsl_compiler::parse(src).unwrap()));
    let public = [
        stable_primitives::field::F128::new(11, 0),
        stable_primitives::field::F128::new(22, 0),
    ];
    match tree {
        "s" => stable_lean_vm_core::cpu::execute(&program, witness, public)
            .map(|_| ()).map_err(|e| e.to_string()),
        _ => unreachable!(),
    }
}

const SRC: &str = r#"
def main():
    a = StackBuf(1)
    hint_witness(a, "r")
    b = StackBuf(1)
    hint_witness(b, "r")
    assert a[0] == 11
    assert b[0] == 22
    p = GEN ** 0
    p[1] = a[0]
    p[GEN] = b[0]
    return
"#;

#[test]
fn second_entry_pops_second() {
    let witness = [("r".to_string(), vec![
        vec![stable_primitives::field::F128::new(11, 0)],
        vec![stable_primitives::field::F128::new(22, 0)],
    ])];
    assert_eq!(run("s", SRC, &witness), Ok(()));
}

#[test]
fn a_wrong_second_entry_is_refused() {
    let witness = [("r".to_string(), vec![
        vec![stable_primitives::field::F128::new(11, 0)],
        vec![stable_primitives::field::F128::new(23, 0)],
    ])];
    assert!(run("s", SRC, &witness).is_err());
}

#[test]
fn an_exhausted_stream_is_refused() {
    let witness = [("r".to_string(), vec![
        vec![stable_primitives::field::F128::new(11, 0)],
    ])];
    assert!(run("s", SRC, &witness).is_err());
}
