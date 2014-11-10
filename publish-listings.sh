#!/bin/bash

cd /tmp
git clone git@github.com:pepijnkokke/thesis.git
cd thesis
git checkout gh-pages
git merge master -m "[auto] merge master into gh-pages"

./buildfile.hs listings

if [ "`git status --porcelain`" != "" ]; then
  echo "Updates:"
  git status --porcelain
  changed=`git status --porcelain | cut -c4-`
  git add --all -- $changed
  git commit -m "[auto] updated html listings"
  git push
else
  echo "No changes!"
fi

cd ..
rm -rf thesis
