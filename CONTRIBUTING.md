# Contributing
Contributors are encouraged, but not required to be a [member](https://openhwfoundation.org/membership/become-a-member/) of the OpenHW Foundation.
New contributions are always welcome.
Start by having a look at the **README**, and review open [Issues](https://github.com/openhwgroup/cv32e40p/issues) with a "Good First Issue" label.
Please note that the CV32E40P is stable and well verified and in general we will not accept a PR that is
[not backward compatible](https://docs.openhwgroup.org/projects/cv32e40p-user-manual/en/cv32e40p_v1.8.3/core_versions.html#non-backward-compatibility) with earlier releases.

## Contributor Agreement
OpenHW is part of the [Eclipse Foundation](https://www.eclipse.org/) and all contributors must be covered by the terms of the
[Eclipse Contributor Agreement](https://www.eclipse.org/legal/ECA.php) (for individuals) **or** the
[Eclipse Member Committer and Contributor Agreement](https://www.eclipse.org/legal/committer_process/EclipseMemberCommitterAgreement.pdf) (for employees of Member companies).
The ECA/MCCA provides a legal framework for a Contributor's technical contributions to the OpenHW Foundation,
including provisions for grant of copyright license and a Developer Certificate of Origin on contributions merged into OpenHW Foundation repositories.

## Licensing
CV32E40P is an open source project, using permissive licensing.
Our preferred license is the [Solderpad](https://solderpad.org/licenses/) hardware license, and we accept most well known permissive licenses.
If you are submitting a new file that does not yet have a copyright header please add the following [SPDX](https://spdx.dev/) header:
```
// Copyright (c) <year> <organization>
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
```
In the above header, "organization" should either be your employer, your institution or yourself:
- If you are being paid to make a contribution on behalf of an employer, then the copyright will be held by your employer.
- If an educational institution is supporting your contribution (for example, by providing access to computer and/or tools), then the copyright should be assigned to your educational institution.
- Otherwise, you may assign the copyright to yourself.  You may use your full name or email address as you see fit.

## Updating Copyright
The files in this repository are open-source artifacts licensed under the terms of the Solderpad license, see [LICENSE](LICENSE).
If you modify a file, a new copyright _may_ be added, but the existing copyright and license header _must not_ be removed or modified.
If your contribution uses a newer version of the existing license, you are encouraged to declare that with a one-liner SPDX header.

In the example below, a new copyright and updated license are added to an existing copyright and license:
```
// Copyright (c) <year> <organization>
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
5. Commit your changes: `git commit -m 'Add some feature' -s`<br>Note: **-s**, is optional.
6. Push feature branch: `git push origin <my_branch>`
7. From GitHub: submit a pull request
