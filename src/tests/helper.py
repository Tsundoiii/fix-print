import subprocess

tests = [
    "test_1",
    "test_2",
    "test_3",
    "test_4",
    "test_5",
    "test_prefix_preservation",
    "test_trailing_comma_1",
    "test_trailing_comma_2",
    "test_trailing_comma_3",
    "test_tuple",
    "test_idempotency_1",
    "test_idempotency_2",
    "test_vargs_without_trailing_comma",
    "test_with_trailing_comma",
    "test_no_trailing_comma",
    "test_spaces_before_file",
]

for test in tests:
    with open(f"{test}.ml", "a") as testfile:
        testfile.write("\n" + "let () = print_string test")

for file in tests:
    subprocess.run(["ocamlopt", "-o", f"{file}.oc", f"{file}.mli", f"{file}.ml"])
