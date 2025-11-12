#!/bin/bash
set -xe

NAME=arXiv

make

git archive --format=zip HEAD -o "$NAME.zip"
zip -d "$NAME.zip" *.pdf .git *.sh agda
