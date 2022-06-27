#!/usr/bin/env python3
# Copyright 2020 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
import argparse
from git import Repo


def main():
    repo = Repo(search_parent_directories=True)

    parser = argparse.ArgumentParser(
        description='Check for changes in repository')
    parser.add_argument('--error-msg',
                        default='::error Files differ.',
                        required=False,
                        help='custom exit code string')
    args = parser.parse_args()

    diff_to_head = repo.head.commit.diff(None)

    # diff tree against working tree
    for diff in diff_to_head:
        print("::error file={}::Files differ ({})".format(
            diff.b_path, diff.change_type))
    if len(diff_to_head) > 0:
        print(args.error_msg)
        exit(1)


if __name__ == '__main__':
    main()