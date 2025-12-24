//! Integration test data exporter for Rust <-> OCaml comparison.
//!
//! Generates deterministic test cases that can be compared against OCaml extracted code.
//! Hash values are excluded since Rust uses Blake3 and OCaml uses stubs.

use alloy_primitives::B256;
use std::env;
use std::fs::File;
use std::io::Write;
use ubt::{Blake3Hasher, Stem, TreeKey, UnifiedBinaryTree};

#[derive(Debug)]
struct TestCase {
    name: String,
    operations: Vec<Operation>,
    queries: Vec<Query>,
}

#[derive(Debug, Clone)]
enum Operation {
    Insert {
        stem: Vec<u8>,
        subindex: u8,
        value: Vec<u8>,
    },
    Delete {
        stem: Vec<u8>,
        subindex: u8,
    },
}

#[derive(Debug)]
struct Query {
    stem: Vec<u8>,
    subindex: u8,
    expected: Option<Vec<u8>>,
}

fn bytes_to_stem(bytes: &[u8]) -> Stem {
    let mut arr = [0u8; 31];
    let len = bytes.len().min(31);
    arr[..len].copy_from_slice(&bytes[..len]);
    Stem::new(arr)
}

fn value_to_bytes(value: &B256) -> Vec<u8> {
    value.to_vec()
}

fn bytes_to_value(bytes: &[u8]) -> B256 {
    let mut arr = [0u8; 32];
    let len = bytes.len().min(32);
    arr[..len].copy_from_slice(&bytes[..len]);
    B256::from(arr)
}

fn pad32(v: Vec<u8>) -> Vec<u8> {
    let mut result = v;
    result.resize(32, 0);
    result
}

fn generate_test_cases() -> Vec<TestCase> {
    vec![
        TestCase {
            name: "empty_tree_get".to_string(),
            operations: vec![],
            queries: vec![Query {
                stem: vec![1, 2, 3],
                subindex: 5,
                expected: None,
            }],
        },
        TestCase {
            name: "single_insert_get".to_string(),
            operations: vec![Operation::Insert {
                stem: vec![1, 2, 3, 4, 5],
                subindex: 10,
                value: vec![42, 43, 44, 45],
            }],
            queries: vec![Query {
                stem: vec![1, 2, 3, 4, 5],
                subindex: 10,
                expected: Some(pad32(vec![42, 43, 44, 45])),
            }],
        },
        TestCase {
            name: "get_different_stem".to_string(),
            operations: vec![Operation::Insert {
                stem: vec![1, 2, 3],
                subindex: 10,
                value: vec![100, 101, 102],
            }],
            queries: vec![Query {
                stem: vec![4, 5, 6],
                subindex: 20,
                expected: None,
            }],
        },
        TestCase {
            name: "same_stem_different_subindex".to_string(),
            operations: vec![Operation::Insert {
                stem: vec![1, 2, 3],
                subindex: 10,
                value: vec![100, 101, 102],
            }],
            queries: vec![Query {
                stem: vec![1, 2, 3],
                subindex: 20,
                expected: None,
            }],
        },
        TestCase {
            name: "multiple_inserts_same_stem".to_string(),
            operations: vec![
                Operation::Insert {
                    stem: vec![1, 2, 3],
                    subindex: 10,
                    value: vec![100, 101, 102],
                },
                Operation::Insert {
                    stem: vec![1, 2, 3],
                    subindex: 20,
                    value: vec![200, 201, 202],
                },
            ],
            queries: vec![
                Query {
                    stem: vec![1, 2, 3],
                    subindex: 10,
                    expected: Some(pad32(vec![100, 101, 102])),
                },
                Query {
                    stem: vec![1, 2, 3],
                    subindex: 20,
                    expected: Some(pad32(vec![200, 201, 202])),
                },
            ],
        },
        TestCase {
            name: "delete_removes_value".to_string(),
            operations: vec![
                Operation::Insert {
                    stem: vec![1, 2, 3],
                    subindex: 10,
                    value: vec![42, 43, 44],
                },
                Operation::Delete {
                    stem: vec![1, 2, 3],
                    subindex: 10,
                },
            ],
            queries: vec![Query {
                stem: vec![1, 2, 3],
                subindex: 10,
                expected: None,
            }],
        },
        TestCase {
            name: "insert_preserves_others".to_string(),
            operations: vec![
                Operation::Insert {
                    stem: vec![10, 20, 30],
                    subindex: 1,
                    value: vec![111],
                },
                Operation::Insert {
                    stem: vec![40, 50, 60],
                    subindex: 2,
                    value: vec![222],
                },
                Operation::Insert {
                    stem: vec![70, 80, 90],
                    subindex: 3,
                    value: vec![255, 254, 253],
                },
            ],
            queries: vec![
                Query {
                    stem: vec![10, 20, 30],
                    subindex: 1,
                    expected: Some(pad32(vec![111])),
                },
                Query {
                    stem: vec![40, 50, 60],
                    subindex: 2,
                    expected: Some(pad32(vec![222])),
                },
                Query {
                    stem: vec![70, 80, 90],
                    subindex: 3,
                    expected: Some(pad32(vec![255, 254, 253])),
                },
            ],
        },
        TestCase {
            name: "overwrite_value".to_string(),
            operations: vec![
                Operation::Insert {
                    stem: vec![5, 5, 5],
                    subindex: 50,
                    value: vec![1, 1, 1],
                },
                Operation::Insert {
                    stem: vec![5, 5, 5],
                    subindex: 50,
                    value: vec![2, 2, 2],
                },
            ],
            queries: vec![Query {
                stem: vec![5, 5, 5],
                subindex: 50,
                expected: Some(pad32(vec![2, 2, 2])),
            }],
        },
        TestCase {
            name: "delete_nonexistent".to_string(),
            operations: vec![
                Operation::Insert {
                    stem: vec![1, 2, 3],
                    subindex: 10,
                    value: vec![42],
                },
                Operation::Delete {
                    stem: vec![9, 9, 9],
                    subindex: 99,
                },
            ],
            queries: vec![Query {
                stem: vec![1, 2, 3],
                subindex: 10,
                expected: Some(pad32(vec![42])),
            }],
        },
        TestCase {
            name: "large_values".to_string(),
            operations: vec![Operation::Insert {
                stem: vec![0xFF; 31],
                subindex: 255,
                value: vec![0xAB; 32],
            }],
            queries: vec![Query {
                stem: vec![0xFF; 31],
                subindex: 255,
                expected: Some(vec![0xAB; 32]),
            }],
        },
    ]
}

fn run_test_case(test: &TestCase) -> Vec<(String, Option<Vec<u8>>)> {
    let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();

    for op in &test.operations {
        match op {
            Operation::Insert {
                stem,
                subindex,
                value,
            } => {
                let s = bytes_to_stem(stem);
                let key = TreeKey::new(s, *subindex);
                let val = bytes_to_value(value);
                tree.insert(key, val);
            }
            Operation::Delete { stem, subindex } => {
                let s = bytes_to_stem(stem);
                let key = TreeKey::new(s, *subindex);
                tree.delete(&key);
            }
        }
    }

    let mut results = Vec::new();
    for query in &test.queries {
        let s = bytes_to_stem(&query.stem);
        let key = TreeKey::new(s, query.subindex);
        let result = tree.get(&key).map(|v| value_to_bytes(&v));
        let query_id = format!(
            "stem=[{}],subidx={}",
            query
                .stem
                .iter()
                .map(|b| b.to_string())
                .collect::<Vec<_>>()
                .join(","),
            query.subindex
        );
        results.push((query_id, result));
    }
    results
}

fn format_bytes(bytes: &[u8]) -> String {
    bytes
        .iter()
        .map(|b| b.to_string())
        .collect::<Vec<_>>()
        .join(",")
}

fn format_result(result: &Option<Vec<u8>>) -> String {
    match result {
        None => "None".to_string(),
        Some(bytes) => format!("Some([{}])", format_bytes(bytes)),
    }
}

fn export_test_data(path: &str) -> std::io::Result<()> {
    let mut file = File::create(path)?;
    let tests = generate_test_cases();

    writeln!(file, "# UBT Integration Test Data")?;
    writeln!(file, "# Format: TEST <name>")?;
    writeln!(
        file,
        "#         OP INSERT <stem_bytes> <subindex> <value_bytes>"
    )?;
    writeln!(file, "#         OP DELETE <stem_bytes> <subindex>")?;
    writeln!(file, "#         QUERY <stem_bytes> <subindex>")?;
    writeln!(file, "#         EXPECT <None|Some(bytes)>")?;
    writeln!(file)?;

    for test in &tests {
        writeln!(file, "TEST {}", test.name)?;
        for op in &test.operations {
            match op {
                Operation::Insert {
                    stem,
                    subindex,
                    value,
                } => {
                    writeln!(
                        file,
                        "OP INSERT [{}] {} [{}]",
                        format_bytes(stem),
                        subindex,
                        format_bytes(value)
                    )?;
                }
                Operation::Delete { stem, subindex } => {
                    writeln!(file, "OP DELETE [{}] {}", format_bytes(stem), subindex)?;
                }
            }
        }
        for query in &test.queries {
            writeln!(
                file,
                "QUERY [{}] {}",
                format_bytes(&query.stem),
                query.subindex
            )?;
            writeln!(file, "EXPECT {}", format_result(&query.expected))?;
        }
        writeln!(file)?;
    }

    Ok(())
}

fn run_and_export_results(path: &str) -> std::io::Result<()> {
    let mut file = File::create(path)?;
    let tests = generate_test_cases();

    writeln!(file, "# UBT Rust Test Results")?;
    writeln!(file)?;

    for test in &tests {
        writeln!(file, "TEST {}", test.name)?;
        let results = run_test_case(&test);
        for (query_id, result) in results {
            writeln!(file, "RESULT {} = {}", query_id, format_result(&result))?;
        }
        writeln!(file)?;
    }

    Ok(())
}

#[test]
fn test_export_integration_data() {
    let test_data_path =
        env::var("UBT_TEST_DATA_PATH").unwrap_or_else(|_| "target/test_data.txt".to_string());
    let results_path =
        env::var("UBT_RESULTS_PATH").unwrap_or_else(|_| "target/rust_results.txt".to_string());

    export_test_data(&test_data_path).expect("Failed to export test data");
    run_and_export_results(&results_path).expect("Failed to export results");

    println!("Test data exported to: {}", test_data_path);
    println!("Results exported to: {}", results_path);
}

#[test]
fn test_verify_expected_results() {
    let tests = generate_test_cases();
    let mut passed = 0;
    let mut failed = 0;

    for test in &tests {
        let results = run_test_case(&test);
        for (i, (query_id, result)) in results.iter().enumerate() {
            let expected = &test.queries[i].expected;
            if result == expected {
                println!(
                    "[PASS] {}: {} = {}",
                    test.name,
                    query_id,
                    format_result(result)
                );
                passed += 1;
            } else {
                println!(
                    "[FAIL] {}: {} = {} (expected {})",
                    test.name,
                    query_id,
                    format_result(result),
                    format_result(expected)
                );
                failed += 1;
            }
        }
    }

    println!("\n=== Results: {}/{} passed ===", passed, passed + failed);
    assert_eq!(failed, 0, "Some test cases failed");
}
