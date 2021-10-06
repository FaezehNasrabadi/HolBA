#!/usr/bin/env bash

# exit immediately if an error happens
set -e

OPT_DIR_PARAM=$1

# get setup directory path
SETUP_DIR=$(dirname "${BASH_SOURCE[0]}")
SETUP_DIR=$(readlink -f "${SETUP_DIR}")

# find the environment variables
set --
source "${SETUP_DIR}/env_config_gen.sh" "${OPT_DIR_PARAM}"

##################################################################


# make polyml binaries and libraries available
<<<<<<< HEAD
POLY_VERSION="v5.7.1"
=======
POLY_VERSION="v5.8.1"
>>>>>>> 24a6f6f2aba3708ecd62e9f1b7ba9b6ecc72edcc

# if poly version is specified in the environment, use this
if [[ ! -z "${HOLBA_POLYML_VERSION}" ]]; then
  POLY_VERSION=${HOLBA_POLYML_VERSION}
fi

POLY_DIR=${HOLBA_OPT_DIR}/polyml_${POLY_VERSION}
export PATH=${POLY_DIR}/bin:$PATH
export LD_LIBRARY_PATH=${POLY_DIR}/lib:$LD_LIBRARY_PATH

# HOL4 source and branch
GIT_URL=https://github.com/HOL-Theorem-Prover/HOL.git
<<<<<<< HEAD
GIT_BRANCH=kananaskis-13
GIT_IS_TAG=1

HOL4_DIR=${HOLBA_OPT_DIR}/hol_k13
=======
GIT_BRANCH=kananaskis-14
GIT_IS_TAG=1

HOL4_DIR=${HOLBA_OPT_DIR}/hol_k14
>>>>>>> 24a6f6f2aba3708ecd62e9f1b7ba9b6ecc72edcc


##################################################################


# if HOL does exist, check if it is up-to-date and remove it in case it is not
if [[ -d "${HOL4_DIR}" ]]; then
  if [[ ! -z "${GIT_IS_TAG}" ]]; then
    echo "the cached HOL4 version is based on a tag, keeping it"
  else
    cd "${HOL4_DIR}"
    git fetch origin

    # does the remote branch exist locally?
    if [[ ! `git branch --all --list origin/${GIT_BRANCH}` ]]; then
      echo "the cached HOL4 version seems to be on another branch, deleting it now"
      # delete the stale HOL4 build
      cd "${HOLBA_OPT_DIR}"
      rm -rf "${HOL4_DIR}"
    else
      # is there a difference between the current and the remote branch?
      GIT_DIFF=$(git diff)
      GIT_DIFF_REMOTE=$(git diff HEAD remotes/origin/${GIT_BRANCH})
      if [[ "${GIT_DIFF}${GIT_DIFF_REMOTE}" ]]; then
        echo "the cached HOL4 version has differences, deleting it now"
        # delete the stale HOL4 build
        cd "${HOLBA_OPT_DIR}"
        rm -rf "${HOL4_DIR}"
      else
        echo "the cached HOL4 version is correct, keeping it"
      fi
    fi
  fi
fi
cd "${HOLBA_OPT_DIR}"


# if HOL does not exist already, clone and build it
if [[ ! -d "${HOL4_DIR}" ]]; then
  # clone the specified HOL4 branch only
  git clone -b ${GIT_BRANCH} --single-branch ${GIT_URL} "${HOL4_DIR}"
  cd "${HOL4_DIR}"

  # compile HOL4
  poly < tools/smart-configure.sml
  bin/build --nograph
fi
cd "${HOLBA_OPT_DIR}"



# extra builds (e.g. some l3 models)
declare -a hol4_extrabuild=(
  "examples/l3-machine-code/common"
  "examples/l3-machine-code/arm8/model"
  "examples/l3-machine-code/arm8/step"
  "examples/l3-machine-code/m0/model"
  "examples/l3-machine-code/m0/step"
)

for dir in "${hol4_extrabuild[@]}"
do
  echo "Holmaking: ${dir}"
  cd "${HOL4_DIR}/${dir}"
  ${HOL4_DIR}/bin/Holmake
done

