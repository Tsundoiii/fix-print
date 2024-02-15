import subprocess
import csv

time = subprocess.run(["date"], capture_output=True, encoding="utf-8")
print(time.stdout)
