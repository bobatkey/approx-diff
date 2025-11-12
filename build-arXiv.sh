#!/bin/bash
set -xe

NAME=arXiv

make

git archive --format=zip HEAD -o "$NAME.zip"
