# Contributing
Contributors are encouraged to be a [member](https://www.openhwgroup.org/membership/) of the
OpenHW Group.  New members are always welcome.

## Getting Started
The [OpenHW Work Flow](https://github.com/openhwgroup/core-v-docs/blob/master/verif/Common/OpenHWGroup_WorkFlow.pdf) document
is required reading.  You will find information about the implementation and usage of the CORE-V verification environments
in the [Verification Strategy](https://github.com/openhwgroup/core-v-docs/blob/master/verif/Common/OpenHWGroup_CORE-V_Verif_Strategy.pdf).

## Updating Copyright
The files in this repository are open-source artifacts licensed under the terms of the Solderpad license, see [LICENSE](LICENSE).
If you modify a file, a new copyright _may_ be added, but the existing copyright and license header _must not_ be removed or modified.
If your contribution uses a newer version of the existing license, you are encouraged to declare that with a one-liner SPDX header.

In the example below, a new copyright and updated license are added to an existing copyright and license:
```
// Copyright 2024 OpenHW Group and <member-company>
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.
// ...remainder of original license header from ETHZ and UniBo.
```

## The Mechanics
1. From GitHub: [fork](https://help.github.com/articles/fork-a-repo/) the [cv32e40p](https://github.com/openhwgroup/cv32e40p) repository
2. Clone repository: `git clone https://github.com/[your_github_username]/cv32e40p`
3. Create your feature branch: `git checkout -b <my_branch>.`<br> Please uniquify your branch name.  See the [Git Cheats](https://github.com/openhwgroup/core-v-verif/blob/master/GitCheats.md)
for a useful nominclature.
4. Make your edits...
5. Commit your changes: `git commit -m 'Add some feature' -s`<br>...take note of that **-s**, it's important!
6. Push feature branch: `git push origin <my_branch>`
7. From GitHub: submit a pull request
