# lib/paths.sh: every path the tool uses inside a consumer repository, defined ONCE. Sourced, never run. Paths are relative to the consumer's root.
LAND_HOME=.land                          # the ONE folder that holds everything the tool owns in a consumer (the skills are the exception: an agent convention)
LAND_DIR=$LAND_HOME/tool                 # the vendored tool folder: replaced whole on every install, never edited
LAND_PIN=$LAND_HOME/PIN                  # version, commit and checksum of the vendored tool (OUTSIDE tool/, so replacing tool/ never removes it)
LAND_MANIFEST_FILE=$LAND_DIR/MANIFEST.sha256   # the per-file checksum list of the vendored tool
LAND_CONF_FILE=$LAND_HOME/land.conf      # the repository's own settings
LAND_HOOKS_DEFAULT=$LAND_HOME/land.d     # the repository's own hooks
LAND_SIGNERS_FILE=$LAND_HOME/land.signers   # who may sign releases
LAND_ENTRY=$LAND_HOME/land-direct        # the entry script an agent runs (it execs ./tool/bin/land-direct beside itself)
LAND_SKILLS_DIR=.agents/skills           # where the tool's agent skills are installed

# The OLD layout (before 0.8.0), where a consumer that has not been migrated yet keeps the same files. The migration in `install` MOVES them into $LAND_HOME and removes $LAND_LEGACY_DIR;
# land-update stages them, so their deletions are in the update commit; and install verifies a release against $LAND_LEGACY_SIGNERS_FILE too. Nothing else reads them, nothing writes here, and
# nothing of the consumer's own outside these paths is touched.
LAND_LEGACY_HOME=scripts                 # the folder the tool shared with the repository's own scripts
LAND_LEGACY_DIR=$LAND_LEGACY_HOME/land   # the vendored tool folder (with its own PIN and MANIFEST.sha256)
LAND_LEGACY_PIN=$LAND_LEGACY_DIR/PIN     # how the migration recognises an old-layout consumer
LAND_LEGACY_CONF_FILE=$LAND_LEGACY_HOME/land.conf
LAND_LEGACY_HOOKS_DEFAULT=$LAND_LEGACY_HOME/land.d
LAND_LEGACY_SIGNERS_FILE=$LAND_LEGACY_HOME/land.signers
LAND_LEGACY_ENTRY=$LAND_LEGACY_HOME/land-direct

# land_vpath PAYLOADPATH: where a path of the release payload lives in a consumer (a skill goes to .agents/skills/, everything else under $LAND_DIR).
land_vpath() { case "$1" in skills/*) echo ".agents/$1";; *) echo "$LAND_DIR/$1";; esac; }
