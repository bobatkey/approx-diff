#!/bin/bash
set -xe
zip -r suppl.zip agda -x "agda/_build/*" -x "agda/src/unused/*" -x "agda/src/incomplete/*"
