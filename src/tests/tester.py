import subprocess

datafile = open("data.csv", "w")
print(
    "Test | Python 2 Output | 2to3 Translation | 2to3 Output | 2to3 Output Matches Original Output | 2to3 Run Time 1 | 2to3 Run Time 2 | 2to3 Run Time 3 | 2to3 Run Time 4 | 2to3 Run Time 5 | fix_print Translation | fix_print Output | fix_print Output Matches Original Output | fix_print Run Time",
    file=datafile,
)


for i in range(1, 12):
    two_to_three_runtimes = []

    for j in range(5):
        python_two_output = subprocess.run(
            ["python2", f"test{i}.py2"], capture_output=True
        ).stdout

        two_to_three_test = subprocess.run(
            f"time 2to3 test{i}.py2",
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
        f"{i} | {python_two_output} | {two_to_three_translation} | {two_to_three_translation_output} | {two_to_three_runtimes[0]} | {two_to_three_runtimes[1]} | {two_to_three_runtimes[2]} | {two_to_three_runtimes[3]} | {two_to_three_runtimes[4]} | {two_to_three_average_runtime} | {python_two_output_equals_two_to_three_output}",
        file=datafile,
    )


for i in range(1, 7):
    subprocess.run(["python2", f"filetest{i}.py2"])

    with open(f"filetest{i}.txt", "br") as two_output_file:
        python_two_output = two_output_file.read()

    two_to_three_runtimes = []

    for j in range(5):
        two_to_three_test = subprocess.run(
            f"time 2to3 filetest{i}.py2",
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

    subprocess.run(
        [
            "python",
            "-c",
            'x = open("filetest1.txt", "w")' + "\n" + two_to_three_translation,
        ],
        capture_output=True,
    )

    with open(f"filetest{i}.txt", "br") as two_output_file:
        two_to_three_translation_output = two_output_file.read()

    python_two_output_equals_two_to_three_output = (
        python_two_output == two_to_three_translation_output
    )

    print(
        f"Filetest {i} | {python_two_output} | {two_to_three_translation} | {two_to_three_translation_output} | {two_to_three_runtimes[0]} | {two_to_three_runtimes[1]} | {two_to_three_runtimes[2]} | {two_to_three_runtimes[3]} | {two_to_three_runtimes[4]} | {two_to_three_average_runtime} | {python_two_output_equals_two_to_three_output}",
        file=datafile,
    )
