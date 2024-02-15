import subprocess
import csv

"""
datafile = open("data.csv", "w")
print(
    "Test, Original Code Output, 2to3 Output, 2to3 Output Matches Original Output, 2to3 Run Time, fix_print Output, fix_print Output Matches Original Output, fix_print Run Time",
    file=datafile,
)
"""

for i in range(1, 4):
    two_to_three_test = subprocess.run(
        ["2to3", f"test{i}.py2"], capture_output=True, encoding="utf-8"
    )

    result = two_to_three_test.stdout.splitlines()
    for line in result:
        if line.startswith("+"):
            two_to_three_translation = line.lstrip("+")

    print(f"{two_to_three_translation=}")

    test2 = subprocess.run(
        ["python", "-c", f"'{two_to_three_translation}'"],
        capture_output=True,
        encoding="utf-8",
    )

    print(f"{test2.stdout=}")

    # print(f"{i},", file=datafile)
