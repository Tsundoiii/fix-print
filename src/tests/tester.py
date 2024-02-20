import subprocess

datafile = open("data.csv", "w")
print(
    "Test | Python 2 Output | 2to3 Translation | 2to3 Output | 2to3 Output Matches Original Output | 2to3 Run Time 1 | 2to3 Run Time 2 | 2to3 Run Time 3 | 2to3 Run Time 4 | 2to3 Run Time 5 | fix_print Translation | fix_print Output | fix_print Output Matches Original Output | fix_print Run Time",
    file=datafile,
)

tests = [
    "test_1",
    "test_2",
    "test_3",
    "test_prefix_preservation",
    "test_trailing_comma_1",
    "test_trailing_comma_2",
    "test_trailing_comma_3",
    "test_tuple",
]

idempotency_tests = [
    "test_idempotency-1",
    "test_idempotency-2",
]

file_redirection_tests = [
    "test_vargs_without_trailing_comma",
    "test_with_trailing_comma",
    "test_no_trailing_comma",
    "test_spaces_before_file",
]

for test in tests:
    two_to_three_runtimes = []

    for j in range(5):
        python_two_output = subprocess.run(
            ["python2", test], capture_output=True
        ).stdout

        two_to_three_test = subprocess.run(
            f"time 2to3 {test}",
            shell=True,
            executable="/bin/bash",
            capture_output=True,
            encoding="utf-8",
        )

        for line in two_to_three_test.stdout.splitlines():
            if line.startswith("+"):
                two_to_three_translation = line.lstrip("+")

        for line in two_to_three_test.stderr.splitlines():
            if line.startswith("real"):
                two_to_three_runtimes.append(int(line[-4:-1]))

    two_to_three_average_runtime = sum(two_to_three_runtimes) / 5

    two_to_three_translation_output = subprocess.run(
        ["python", "-c", two_to_three_translation], capture_output=True
    ).stdout

    python_two_output_equals_two_to_three_output = (
        python_two_output == two_to_three_translation_output
    )

    print(
        f"{test} | {python_two_output} | {two_to_three_translation} | {two_to_three_translation_output} | {python_two_output_equals_two_to_three_output} | {two_to_three_runtimes[0]} | {two_to_three_runtimes[1]} | {two_to_three_runtimes[2]} | {two_to_three_runtimes[3]} | {two_to_three_runtimes[4]} | {two_to_three_average_runtime}",
        file=datafile,
    )

for test in idempotency_tests:
    two_to_three_runtimes = []

    for j in range(5):
        python_two_output = subprocess.run(
            ["python2", test], capture_output=True
        ).stdout

        two_to_three_test = subprocess.run(
            f"time 2to3 {test}",
            shell=True,
            executable="/bin/bash",
            capture_output=True,
            encoding="utf-8",
        )

        with open(test) as test_file:
            two_to_three_translation = test_file.read()

        for line in two_to_three_test.stderr.splitlines():
            if line.startswith("real"):
                two_to_three_runtimes.append(int(line[-4:-1]))

    two_to_three_average_runtime = sum(two_to_three_runtimes) / 5

    two_to_three_translation_output = subprocess.run(
        ["python", "-c", two_to_three_translation], capture_output=True
    ).stdout

    python_two_output_equals_two_to_three_output = (
        python_two_output == two_to_three_translation_output
    )

    print(
        f"{test} | {python_two_output} | {two_to_three_translation} | {two_to_three_translation_output} | {python_two_output_equals_two_to_three_output} | {two_to_three_runtimes[0]} | {two_to_three_runtimes[1]} | {two_to_three_runtimes[2]} | {two_to_three_runtimes[3]} | {two_to_three_runtimes[4]} | {two_to_three_average_runtime}",
        file=datafile,
    )

for test in file_redirection_tests:
    two_to_three_runtimes = []

    for j in range(5):
        python_two_output = subprocess.run(
            ["python2", test], capture_output=True
        ).stderr

        two_to_three_test = subprocess.run(
            f"time 2to3 {test}",
            shell=True,
            executable="/bin/bash",
            capture_output=True,
            encoding="utf-8",
        )

        for line in two_to_three_test.stdout.splitlines():
            if line.startswith("+"):
                two_to_three_translation = line.lstrip("+")

        for line in two_to_three_test.stderr.splitlines():
            if line.startswith("real"):
                two_to_three_runtimes.append(int(line[-4:-1]))

    two_to_three_average_runtime = sum(two_to_three_runtimes) / 5

    two_to_three_translation_output = subprocess.run(
        ["python", "-c", "import sys;" + two_to_three_translation],
        capture_output=True,
    ).stderr

    python_two_output_equals_two_to_three_output = (
        python_two_output == two_to_three_translation_output
    )

    print(
        f"{test} | {python_two_output} | {two_to_three_translation} | {two_to_three_translation_output} | {python_two_output_equals_two_to_three_output} | {two_to_three_runtimes[0]} | {two_to_three_runtimes[1]} | {two_to_three_runtimes[2]} | {two_to_three_runtimes[3]} | {two_to_three_runtimes[4]} | {two_to_three_average_runtime}",
        file=datafile,
    )
