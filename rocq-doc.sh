#!/bin/sh -e

mkdir -p html
coqdoc -Q src/main/coq com.io7m --toc --utf8 -d html src/main/coq/*.v
