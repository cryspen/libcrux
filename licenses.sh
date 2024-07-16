# SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
#
# SPDX-License-Identifier: Apache-2.0

#!/usr/bin/env bash

reuse download Apache-2.0
reuse annotate -c "Cryspen Sarl <info@cryspen.com>" -l Apache-2.0 --skip-existing --skip-unrecognised -r * .gitignore
reuse lint
