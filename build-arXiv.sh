#!/bin/bash
set -xe

NAME=arXiv.zip
ARCHIVE="./$NAME"

make

zip -r - . > $ARCHIVE
zip -d $ARCHIVE \*.{DS_Store,gitignore}
zip -d $ARCHIVE *.pdf .git *.sh
