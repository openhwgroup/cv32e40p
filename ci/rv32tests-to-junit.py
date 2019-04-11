#!/usr/bin/env python3
import sys, getopt
from junit_xml import *


def main(argv):
    inputfile = ''
    outputfile = ''

    try:
        opts, args = getopt.getopt(argv,"hi:o:",["ifile=","ofile="])
    except getopt.GetoptError:
        print ('rv32tests-to-junit.py -i <inputfile> -o <outputfile>')
        sys.exit(2)
    for opt, arg in opts:
        if opt == '-h':
            print ('rv32tests-to-junit.py -i <inputfile> -o <outputfile>')
            sys.exit()
        elif opt in ("-i", "--ifile"):
            inputfile = arg
        elif opt in ("-o", "--ofile"):
            outputfile = arg

    test_strings = defaultdict(list)
    current_testname = ''

    test_cases = []
    current_test_case = None

    with open(inputfile, 'r') as infile:
        for line in infile:
            if 'Test Begin' in line:
                current_testname = line.split('#')[1]
            if 'Test End' in line:
                current_testname = ""
            if current_testname != "":
                test_strings[current_testname].append(line)

    for k,v in test_strings.items():
        #test_cases.append(TestCase('Test1', stdout=''.join(v)))
        current_test_case = TestCase(k, stdout=''.join(v))
        error_msg = ""
        for line in v:
            if 'Assertion violation' in line:
                error_msg += line;

            if error_msg:
                current_test_case.add_error_info(error_msg)

        test_cases.append(current_test_case)

    ts = TestSuite("riscv-compliance", test_cases)
    # pretty printing is on by default but can be disabled using prettyprint=False
    with open(outputfile, 'w') as outfile:
        TestSuite.to_file(outfile, [ts])

if __name__ == "__main__":
    main(sys.argv[1:])
