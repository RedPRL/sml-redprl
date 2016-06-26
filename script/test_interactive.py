import os
import subprocess
import filecmp

TESTS_PATH = 'testsuite/interactive/'

filenames = next(os.walk(TESTS_PATH))[2]
json_files = filter(lambda x: x.endswith('.json'), filenames)

for filename in json_files:
    test_name = filename.split('.')[0]
    myinput = open(TESTS_PATH + filename)
    myoutput = open(TESTS_PATH + test_name + '.out', 'w')
    p = subprocess.Popen(['bin/redprl', '--interactive'], stdin=myinput, stdout=myoutput)
    myoutput.flush()

    diff = filecmp.cmp(TESTS_PATH + test_name + '.out', TESTS_PATH + test_name + '.expected')

    if diff:
        print(test_name + ": fail")
    else:
        print(test_name + ": ok")
