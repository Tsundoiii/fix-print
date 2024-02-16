import subprocess
import csv

datafile = open("data.csv", "w")
print(
    "Test | Original Code Output | 2to3 Translation | 2to3 Output | 2to3 Output Matches Original Output | 2to3 Run Time | fix_print Translation | fix_print Output | fix_print Output Matches Original Output | fix_print Run Time",
    file=datafile,
)

for i in range(1, 4):
    two_to_three_test = subprocess.run(
        ["2to3", f"test{i}.py2"], capture_output=True, encoding="utf-8"
    )

    two_to_three_test_result = two_to_three_test.stdout.splitlines()
    for line in two_to_three_test_result:
        if line.startswith("+"):
            two_to_three_translation = line.lstrip("+")

    two_to_three_translation_output = subprocess.run(
        ["python", "-c", two_to_three_translation], capture_output=True
    ).stdout

    print(
        f"{i} | {two_to_three_translation} | {two_to_three_translation_output}",
        file=datafile,
    )
