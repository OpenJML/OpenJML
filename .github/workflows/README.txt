
As of this writing (12/2025) there are two workflows defined for OpenJML:

build -- builds an OpenJML release, running the release tests, and constructing a draft release (that draft release will need its release notes
added, after which the release can be published and be public). This workflow is executed when either the master-21 or dev-21 branch is pushed to github.

nightly -- checks out a development environment from github, builds openjlm, and runs all the various kinds of tests. This workflow runs when dev-21 is pushed to github.

The workflows can also be manually triggered.
These two workflows share code through some github 'composite' actions (defined in .github/actions).  The buil of their work is defined in Makefiles.

Some comments:

-- There is partial code for building a release on Windows WSL, but the configuration for this to succeed is not yet ironed out

-- The build workflow on dev-21 will fail if there already is draft release for the current version number. You can inspect the build details to see if the
build and test were actually successful, and it is just the prep for upload that fails.

-- In the nightly workflow, the build job is performed for a matrix of runners, and then the test job is performed for the same matrix of runners.
Each test job only 'needs' that the build job for its same runner has completed, but github requires all the first matrix of jobs complete successfully before
any of the second set of jobs will start.

-- FIXME: composite actions seem to require an explicit shell. Is there a way to define the default shell ? And what should the shell actually be?

-- FIXME: the output flag to say whether a release should be tested does not seem to work

