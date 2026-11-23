#!/usr/bin/env bash

# rocqchk must refuse a library whose stored registration of a primitive
# inductive type (a Register_ind action) gives the inductive type that the
# library declares another canonical name. rocqchk checks the registration
# against the inductive type it finds by the user name, and
# Safe_typing.import then puts the registration in force for every later
# library as the file stores it, canonical name included. With B registered
# as bool under the canonical name of U := u1 | u2 (_ : False), a later
# primitive ltb : int -> int -> U computes u2 with no argument, and boom is
# a closed proof of False. The test proves that rocqchk refuses that
# registration, in any of the library's entries for B, with an error on the
# library that names it, and that it still accepts the honest
# registrations: one, the same one twice, and one through a module alias or
# an Include, whose user and canonical names can differ.
#
# The files. The sources are in misc/rocqchk-register-ind-canonical/, each
# compiled with $coqc -noinit -R <dir> RegInd in its own directory under
# the scratch directory, so that each library is RegInd.Lib (mode_args
# checks <root>.Lib). The scratch directories, which the test prints, for
# the names of BET-1505's plan (its C′, C″ and C‴ are spelled C', C'' and
# C''' here):
# - C: honest/Lib.vo, from Lib.v. It registers B as bool:
#   (RegInd.Lib.B, RegInd.Lib.B); its other action is the Register_type of
#   int;
# - control: control/Lib.vo, C with that entry written as the Dual name
#   (B, B), by forge.ml ind-canonical RegInd.Lib.B RegInd.Lib.B: it differs
#   from C' only in the canonical kernel name;
# - C': forged/Lib.vo, C with that entry (B, U), by forge.ml ind-canonical
#   RegInd.Lib.B RegInd.Lib.U;
# - C'': twice/Lib.vo, from twice/Lib.v, which registers B twice: (B, B),
#   then (B, B), as coqc stores them;
# - C''': repeated/Lib.vo, C with (B, U) just before its entry, by forge.ml
#   ind-repeat RegInd.Lib.B RegInd.Lib.U first: (B, U), then (B, B);
# - repeated-last: repeated-last/Lib.vo, C with (B, U) just after its
#   entry (ind-repeat ... last): (B, B), then (B, U);
# - operator-control: operator-control/Lib.vo, a copy of C;
# - A1: alias/Lib.vo and alias/Client.vo, from alias/: Module M := N, then
#   Register M.B; one entry with the user name RegInd.Lib.M.B;
# - A2: include/Lib.vo and include/Client.vo, from include/:
#   Module M. Include N. End M., then Register M.B; the same rule;
# - D_B: honest/ClientB.vo, from ClientB.v, compiled against C; its ltb
#   returns B. forge.ml client relinks it to control/, twice/ and
#   repeated-last/;
# - D_U: forged/ClientU.vo, from ClientU.v, compiled by coqc against C';
#   its ltb returns U and boom : False. forge.ml client relinks it to
#   repeated/ and operator-control/ (to C).
#
# The sets, in the order they run. Each runs as a grader runs rocqchk
# (mode grader) and with the default options (mode default), as mode_args
# builds them. forged, repeated and repeated-last run the library alone,
# then with the client: 12 runs per mode, 24 in all.
#   set               library        client              must be
#   honest            C              D_B                 accepted
#   control           control        D_B, relinked       accepted
#   honest-repeated   C''            D_B, relinked       accepted
#   honest-alias      A1             alias/Client.vo     accepted
#   honest-include    A2             include/Client.vo   accepted
#   forged            C'             D_U                 refused, D3, on C
#   repeated          C'''           D_U, relinked       refused, D3, on C
#   repeated-last     repeated-last  D_B, relinked       refused, D3, on C
#   operator-control  C              D_U, relinked       refused by
#                                                        check_primitive_operator,
#                                                        on the client
# D3 is the line rocqchk prints for the refusal of the stored canonical
# name, exactly as classify spells it. A refusal with the client is on C
# when the library alone, in the same mode, is refused with the same error
# line, and on the client when the library alone is accepted. C alone is
# not run again for operator-control: the honest set's run of the same mode
# checks C first, so its acceptance is C's.
#
# Before the runs of a set, the test prints forge.ml retro of its library,
# and "valid" when the print shows the entries above (for A1 and A2: one
# entry, index 0, prim bool, user RegInd.Lib.M.B, with "shape: user !=
# canonical" or a NOTE that the set does not test that shape), else VOID: a
# run on a VOID library counts as void. A refusal by check_module's
# "unknown inductive" or by Safe_typing.check_register_ind voids the run:
# those are the refusals of a badly built forgery. A coqc refusal of A1, A2
# or their clients drops that set, with coqc's error; any other compile or
# forge failure stops the test before its first verdict. The output names
# no scratch path and no time, so two runs print the same bytes. The test
# exits 0 only when every library is valid, every run that is not dropped
# is as the table says, and none is void. Without the check, rocqchk
# accepts forged, repeated and repeated-last, and the test exits 1 after
# printing every line.

set -e

. misc/rocqchk_forge_common.bash
. misc/rocqchk_summary_common.bash

: "${coqc:?the misc rule of test-suite/Makefile exports coqc}"

D=misc/rocqchk-register-ind-canonical
FORGE=misc/rocqchk-register-type/forge.ml
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT

# scrub: the standard input with the scratch directory written <scratch>.
scrub() { sed "s|$d|<scratch>|g"; }

# stop <message> [<log>]: print <message>, and <log> if it is given, then
# exit 1.
stop() {
  echo "stop: $1" | scrub
  if [ -n "${2-}" ]; then scrub < "$2"; fi
  exit 1
}

# coq <dir> <source>: copy $D/<source> into $d/<dir> and compile it there,
# bound to RegInd, with coqc's output in $d/step.log. It fails if coqc
# fails or writes no .vo file.
coq() {
  local v=$d/$1/${2##*/}
  mkdir -p "$d/$1"
  cp "$D/$2" "$v"
  # $coqc is a command line that the misc rule writes to be split.
  # shellcheck disable=SC2086
  $coqc -noinit -R "$d/$1" RegInd "$v" > "$d/step.log" 2>&1 && [ -s "${v%.v}.vo" ]
}

# build <dir> <source>: coq, or stop with coqc's output.
build() { coq "$1" "$2" || stop "coqc refused $2, compiled in $1/:" "$d/step.log"; }

# forge <argument>...: forge.ml <argument>..., with its output in
# $d/step.log, which is printed only if it fails; a failure stops the test.
forge() { ocaml "$FORGE" "$@" > "$d/step.log" 2>&1 || stop "forge.ml $* failed:" "$d/step.log"; }

# relink <client> <dir>: the client $d/<client>, recording $d/<dir>/Lib.vo
# as its dependency RegInd.Lib, written to $d/<dir>.
relink() { forge client "$d/$1" "$d/$2/Lib.vo" RegInd.Lib "$d/$2/${1##*/}"; }

# print_retro <set> <dir>: print forge.ml retro of $d/<dir>/Lib.vo, which
# the forge steps keep in retro_out[<dir>], each line after
# "retro <dir>/Lib.vo (<set>): ". Set inds and others to its Register_ind
# entries and its other actions, in stored order, each without its
# "<action> <k>/<n>: " head and joined by "; ", n_ind to the number of
# Register_ind entries, and retro_ok to 1 when the print is one line per
# action and then "actions: <n>".
print_retro() {
  local lib=$2/Lib.vo line total='' count=0
  inds='' others='' n_ind=0 retro_ok=1
  while IFS= read -r line; do
    echo "retro $lib ($1): $line"
    case $line in
      "Register_ind "*)
        inds+="${inds:+; }${line#*: }"
        n_ind=$((n_ind + 1))
        count=$((count + 1)) ;;
      "Register_type "*)
        others+="${others:+; }${line#*: }"
        count=$((count + 1)) ;;
      "actions: "*) total=${line#actions: } ;;
      *) retro_ok=0 ;;
    esac
  done <<< "${retro_out[$2]}"
  [ "$total" = "$count" ] || retro_ok=0
}

# The compile and forge steps.

build honest Lib.v
build honest ClientB.v
build twice twice/Lib.v
mkdir "$d/control" "$d/forged" "$d/repeated" "$d/repeated-last" "$d/operator-control"
forge ind-canonical "$d/honest/Lib.vo" "$d/control/Lib.vo" RegInd.Lib.B RegInd.Lib.B
forge ind-canonical "$d/honest/Lib.vo" "$d/forged/Lib.vo" RegInd.Lib.B RegInd.Lib.U
build forged ClientU.v
forge ind-repeat "$d/honest/Lib.vo" "$d/repeated/Lib.vo" RegInd.Lib.B RegInd.Lib.U first
forge ind-repeat "$d/honest/Lib.vo" "$d/repeated-last/Lib.vo" RegInd.Lib.B RegInd.Lib.U last
cp "$d/honest/Lib.vo" "$d/operator-control/"
relink honest/ClientB.vo control
relink honest/ClientB.vo twice
relink forged/ClientU.vo repeated
relink honest/ClientB.vo repeated-last
relink forged/ClientU.vo operator-control

# A1 and A2: a coqc refusal drops the set.
declare -A dropped_set
for dir in alias include; do
  for f in Lib.v Client.v; do
    if ! coq "$dir" "$dir/$f"; then
      echo "coqc refused $dir/$f; the set honest-$dir is dropped; coqc printed:"
      scrub < "$d/step.log"
      dropped_set[$dir]=1
      break
    fi
  done
done

# The stored actions of each library, printed before the runs of its set.
declare -A retro_out
for dir in honest control twice forged repeated repeated-last operator-control alias include; do
  if [ -z "${dropped_set[$dir]-}" ]; then
    retro_out[$dir]=$(ocaml "$FORGE" retro "$d/$dir/Lib.vo" 2> "$d/step.log") ||
      stop "forge.ml retro $dir/Lib.vo failed:" "$d/step.log"
  fi
done

# spec v3 R1: coqc stores both entries of the two Register commands of C''.
if [ "$(grep -c '^Register_ind ' <<< "${retro_out[twice]}")" = 1 ]; then
  print_retro honest-repeated twice
  stop "coqc stored one Register_ind entry for the two Register commands of twice/Lib.v, against spec v3 R1: tell the architect, with the print above"
fi

set +e

# classify <text>: the row of the classification table that <text> matches:
# the first line of a run's output that holds Error or Anomaly, or that
# line joined with the next by one space, for a BadConstant error, whose
# constant name can be on the line before its text. It prints one line,
# "<row>: <file>, <function>" for the check that refuses, where <row> is
# d3 (the refusal of the stored canonical name, exactly: the refusal the
# table expects of forged, repeated and repeated-last), d3-names (the same
# refusal of other names: not as the table says), operator (the refusal
# the table expects of operator-control), void (a refusal of a badly built
# forgery), recorded (a refusal by another check of the registrations, not
# as the table says), none (no error line) or unclassified.
classify() {
  local t=$1
  local d3='RegInd.Lib.B is registered as the primitive inductive type bool, but the registration gives it the canonical name RegInd.Lib.U, not RegInd.Lib.B.'
  local d3_names='is registered as the primitive inductive type [^ ,]+, but the registration gives it the canonical name [^ ,]+, not [^ ]+\.'
  local operator="is the primitive operator [^ ,]+, but its type is not the operator's"
  local unknown='Retroknowledge registration for unknown inductive'
  local register_ind='A universe monomorphic inductive type is expected|A non mutual inductive is expected|A non-private inductive type is expected|An inductive type with [0-9]+ parameters is expected|an inductive type with [0-9]+ constructors is expected|th constructor does not have the expected (name|type)|the constructor does not have the expected type'
  local inconsistent='Inconsistent primitive registration for inductive'
  if [ -z "$t" ]; then
    echo "none: none"
  elif [ "$t" = "Fatal Error: User error: $d3" ]; then
    echo "d3: checker/mod_checking.ml, check_structure_field"
  elif [[ $t =~ $d3_names ]]; then
    echo "d3-names: checker/mod_checking.ml, check_structure_field"
  elif [[ $t =~ $operator ]]; then
    echo "operator: checker/mod_checking.ml, check_primitive_operator"
  elif [[ $t =~ $unknown ]]; then
    echo "void: checker/mod_checking.ml, check_module"
  elif [[ $t =~ $register_ind ]]; then
    echo "void: kernel/safe_typing.ml, check_register_ind"
  elif [[ $t =~ $inconsistent ]]; then
    echo "recorded: checker/mod_checking.ml, get_retroknowlege"
  else
    echo "unclassified: unclassified"
  fi
}

# axioms_line <log>: the Axioms section of the rocqchk -o output in <log>,
# on one line: its names, sorted, or, when it lists none, what its title
# line says after "* Axioms:" (<none>).
axioms_line() {
  local s names title
  s=$(section Axioms "$1")
  if [ -z "$s" ]; then
    echo "no Axioms section"
    return
  fi
  names=$(printf '%s\n' "$s" | sed -n 's/^ \{1,\}//p' | LC_ALL=C sort | paste -sd ' ' -)
  title=${s%%$'\n'*}
  title=${title#"* Axioms:"}
  if [ -n "$names" ]; then printf '%s\n' "$names"; else printf '%s\n' "${title# }"; fi | scrub
}

all_valid=1

# verdict <set> <dir> <what differs>: print that $d/<dir>/Lib.vo is valid,
# or VOID, and set lib_ok.
verdict() {
  if [ -z "$3" ]; then
    echo "retro $2/Lib.vo ($1): valid"
    lib_ok=1
  else
    echo "VOID: $2/Lib.vo: $3"
    lib_ok=0
    all_valid=0
  fi
}

# valid <set> <dir> <entries> <others>: the print of print_retro must show
# the Register_ind entries <entries> and the other actions <others>.
valid() {
  local why=
  [ "$retro_ok" = 1 ] || why="the print is not one line per action and then their count"
  [ "$inds" = "$3" ] || why+="${why:+; }Register_ind entries [$inds], not [$3]"
  [ "$others" = "$4" ] || why+="${why:+; }other actions [$others], not [$4]"
  verdict "$1" "$2" "$why"
}

# valid_shape <set> <dir> <others>: the rule of A1 and A2: one
# Register_ind entry, index 0, prim bool, user RegInd.Lib.M.B, and the
# other actions <others>. Its canonical name is the one coqc writes; print
# whether it differs from the user name.
valid_shape() {
  local why='' user='' canonical='' index='' prim=''
  [ "$retro_ok" = 1 ] || why="the print is not one line per action and then their count"
  if [ "$n_ind" != 1 ]; then
    why+="${why:+; }$n_ind Register_ind entries, not one"
  else
    read -r user canonical index prim <<< "$inds"
    [ "$user" = user=RegInd.Lib.M.B ] || why+="${why:+; }the user name is ${user#user=}, not RegInd.Lib.M.B"
    [[ $canonical == canonical=?* ]] || why+="${why:+; }no canonical name"
    [ "$index" = index=0 ] || why+="${why:+; }the index is ${index#index=}, not 0"
    [ "$prim" = prim=bool ] || why+="${why:+; }the primitive is ${prim#prim=}, not bool"
  fi
  [ "$others" = "$3" ] || why+="${why:+; }other actions [$others], not [$3]"
  verdict "$1" "$2" "$why"
  if [ "$lib_ok" = 1 ]; then
    if [ "${canonical#canonical=}" != "${user#user=}" ]; then
      echo "retro $2/Lib.vo ($1): shape: user != canonical"
    else
      echo "NOTE: $1 stores user = canonical; it does not test this shape"
    fi
  fi
}

a=0 u=0 v=0 dropped=0
declare -A honest_rc honest_line

# run <set> <dir> <mode> <client or ""> <expected> <reference>: rocqchk on
# RegInd.Lib in $d/<dir>, and RegInd.<client> if it is given, in <mode>,
# within 300 s. Print its verdict, its error line and the refusing check,
# and, for a refusal with the client and a <reference> (alone: the library
# alone in this mode, from the previous run; honest: the honest set's run
# in this mode), where the refusal is. Count the run against <expected>:
# accepted, d3 (refused with the D3 line, and on C with the client) or
# operator (refused by check_primitive_operator, on the client). Set r_rc
# and r_line to the exit status and the error line.
run() {
  local set=$1 dir=$2 mode=$3 client=$4 expected=$5 reference=$6
  local kind="library alone" two line next class joined last where='' ref_rc ref_line ok='' want
  if [ -n "$client" ]; then kind="with client"; fi
  mode_args "$mode" "$d/$dir" RegInd "$client"
  r_rc=0
  timeout 300 "$BIN"rocqchk "${mode_argv[@]}" > "$d/run.log" 2>&1 || r_rc=$?
  r_line=
  class=accepted
  if [ "$r_rc" = 0 ]; then
    echo "set $set ($mode, $kind): accepted"
    if [ "$mode" = grader ]; then echo "  axioms: $(axioms_line "$d/run.log")"; fi
  else
    echo "set $set ($mode, $kind): refused"
    two=$(awk '/Error|Anomaly/ { print; if ((getline n) > 0) print n; exit }' "$d/run.log" | scrub)
    line=${two%%$'\n'*}
    line=${line%"${line##*[![:space:]]}"}
    next=
    if [[ $two == *$'\n'* ]]; then
      next=${two#*$'\n'}
      next=${next#"${next%%[![:space:]]*}"}
      next=${next%"${next##*[![:space:]]}"}
    fi
    class=$(classify "$line")
    if [ "${class%%:*}" = unclassified ] && [ -n "$next" ]; then
      joined=$(classify "$line $next")
      if [ "${joined%%:*}" != unclassified ]; then
        class=$joined
        line="$line $next"
      fi
    fi
    r_line=$line
    if [ "${class%%:*}" != none ]; then
      echo "  error: $line; check: ${class#*: }"
    else
      last=$(awk 'NF { l = $0 } END { print l }' "$d/run.log" | scrub)
      if [ "$r_rc" = 124 ]; then
        echo "  error: timeout, no error line (last line: $last); check: none"
      else
        echo "  error: none (exit status $r_rc; last line: $last); check: none"
      fi
    fi
    if [ -n "$client" ] && [ -n "$reference" ]; then
      case $reference in
        alone) ref_rc=$alone_rc ref_line=$alone_line ;;
        honest) ref_rc=${honest_rc[$mode]} ref_line=${honest_line[$mode]} ;;
      esac
      if [ "$ref_rc" != 0 ] && [ -n "$r_line" ] && [ "$ref_line" = "$r_line" ]; then
        where="on C"
      elif [ "$ref_rc" = 0 ]; then
        where="on the client"
      else
        where="neither: the library alone is refused with another line"
      fi
      echo "  where: $where"
    fi
  fi
  case $expected in
    accepted)
      want="accepted"
      if [ "$r_rc" = 0 ]; then ok=1; fi ;;
    d3)
      want="refused with the D3 line"
      if [ -n "$client" ]; then want+=", on C"; fi
      if [ "$r_rc" != 0 ] && [ "${class%%:*}" = d3 ] && { [ -z "$client" ] || [ "$where" = "on C" ]; }; then ok=1; fi ;;
    operator)
      want="refused by check_primitive_operator, on the client"
      if [ "$r_rc" != 0 ] && [ "${class%%:*}" = operator ] && [ "$where" = "on the client" ]; then ok=1; fi ;;
  esac
  if [ "$lib_ok" != 1 ]; then
    v=$((v + 1))
    echo "  result: void: the library is VOID"
  elif [ "${class%%:*}" = void ]; then
    v=$((v + 1))
    echo "  result: void: refused by a check that refuses a badly built forgery"
  elif [ -n "$ok" ]; then
    a=$((a + 1))
    echo "  result: as the table says"
  else
    u=$((u + 1))
    echo "  result: not as the table says, which is: $want"
  fi
}

# runs <set> <dir> <client> <expected> [alone|honest]: the runs of a set in
# both modes; with alone, the library alone runs first in each mode.
runs() {
  local mode
  for mode in grader default; do
    if [ "${5-}" = alone ]; then
      run "$1" "$2" "$mode" "" "$4" ""
      alone_rc=$r_rc alone_line=$r_line
    fi
    run "$1" "$2" "$mode" "$3" "$4" "${5-}"
    if [ "$1" = honest ]; then
      honest_rc[$mode]=$r_rc
      honest_line[$mode]=$r_line
    fi
  done
}

bb='user=RegInd.Lib.B canonical=RegInd.Lib.B index=0 prim=bool'
bu='user=RegInd.Lib.B canonical=RegInd.Lib.U index=0 prim=bool'
int_type='constant=RegInd.Lib.int prim=int63_type'

print_retro honest honest
valid honest honest "$bb" "$int_type"
c_others=$others
runs honest honest ClientB accepted

print_retro control control
valid control control "$bb" "$c_others"
runs control control ClientB accepted

print_retro honest-repeated twice
valid honest-repeated twice "$bb; $bb" "$c_others"
runs honest-repeated twice ClientB accepted

for dir in alias include; do
  if [ -n "${dropped_set[$dir]-}" ]; then
    echo "set honest-$dir: dropped (coqc refused a file of $dir/), 2 runs"
    dropped=$((dropped + 2))
  else
    print_retro "honest-$dir" "$dir"
    valid_shape "honest-$dir" "$dir" "$int_type"
    runs "honest-$dir" "$dir" Client accepted
  fi
done

print_retro forged forged
valid forged forged "$bu" "$c_others"
runs forged forged ClientU d3 alone

print_retro repeated repeated
valid repeated repeated "$bu; $bb" "$c_others"
runs repeated repeated ClientU d3 alone

print_retro repeated-last repeated-last
valid repeated-last repeated-last "$bb; $bu" "$c_others"
runs repeated-last repeated-last ClientB d3 alone

print_retro operator-control operator-control
valid operator-control operator-control "$bb" "$c_others"
runs operator-control operator-control ClientU operator honest

total=$((a + u + v + dropped))
if [ "$total" != 24 ]; then echo "the test counted $total runs, not 24"; fi
echo "ran $total runs: $a as the table says, $u not as the table says, $v void, $dropped dropped"
if [ "$total" = 24 ] && [ "$all_valid" = 1 ] && [ "$u" = 0 ] && [ "$v" = 0 ]; then exit 0; fi
exit 1
