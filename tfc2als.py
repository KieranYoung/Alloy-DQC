#!/usr/local/bin/python3

import sys
import os
import math
import re
import argparse
import csv
import subprocess
import time
import random
from enum        import Enum
from itertools   import combinations
from string      import Template
from collections import defaultdict
from collections import deque
import tempfile

SUPPORTED_FILE_EXTENSIONS = ['.tfc', '.real', '.qasm']
ENV_HOME = os.environ['HOME']
TMPDIR = ENV_HOME + "/tmp"
ALLOY_JAR_PATH = os.path.dirname(os.path.abspath(__file__)) + "/"
ALLOY_JAR_OPTIONS = ["-Djava.io.tmpdir="+TMPDIR]
tempfile.tempdir = TMPDIR
if True:
    ALLOY_JAR = "org.alloytools.alloy.dist.jar"
    ALLOY_JAR_LINK = "https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v6.0.0/" + ALLOY_JAR
else:
    ALLOY_JAR = "alloy4.2_2015-02-22.jar"
    ALLOY_JAR_LINK = "http://alloytools.org/download/" + ALLOY_JAR
JPYPE_INSTALL = "pip install --user JPype1"

Q_PREFIX = 'q_'
M_PREFIX = 'M_'

RECENT_HISTORY_SEARCH_Q_LEN = 10
#RECENT_HISTORY_LINEAR_RANGE = 4 # TODO broke

# TODO explanation of $VARs and general comments
ALLOY_TEMPLATE_BASIC = """
module teleport

open util/ordering[circGraph] as grph
open util/integer

abstract sig Qubit { }
one sig $V_LIST extends Qubit { }

abstract sig Machine { } 
one sig $M_LIST extends Machine { }

sig circGraph{
    edges: Qubit -> Qubit,
    location: Qubit -> Machine,
    numTele: Int
} {
    all q: Qubit | #q.location = 1 
}

/*
fact { all c:circGraph |
$M_CAP_LIST
}
*/
fact { all c:circGraph, m:Machine | #(c.location).m < $M_CAP }

fact CircuitGraph {
    let l_0 = grph/first | 
        l_0.numTele = 0 &&
        l_0.location =
$LOCATION$CIRCUIT
}

pred teleport[loc: Qubit -> Machine, r: Qubit -> Qubit, uloc: Qubit -> Machine, tele: Int, utele: Int] {
    all disj q0, q1: Qubit | (q0 -> q1 in r) implies q0.uloc = q1.uloc
    utele = plus[tele, #(uloc - loc)]
}

fact layerTransition {
    all l: circGraph, us: grph/next[l] { 
	teleport[l.location, us.edges, us.location, l.numTele, us.numTele] 
    }
}

pred finalLayer {  
    lte[grph/last.numTele, $TELE_MAX]
}

run finalLayer for $LAYERS circGraph, $INT_BITS Int
"""

ALLOY_TEMPLATE_LB = """
module teleport

open util/ordering[circGraph] as grph
open util/integer

abstract sig Qubit { }
one sig $V_LIST extends Qubit { }

abstract sig Machine { } 
one sig $M_LIST extends Machine { }

sig circGraph{
    edges: Qubit -> Qubit,
    location: Qubit -> Machine,
    numTele: Int,
    emptyMachines: Int
} {
    all q: Qubit | #q.location = 1 
}

/*
fact { all c:circGraph |
$M_CAP_LIST
}
*/
fact { all c:circGraph, m:Machine | #(c.location).m < $M_CAP }

fact CircuitGraph {
    let l_0 = grph/first | 
        l_0.numTele = 0 &&
        l_0.emptyMachines = 0 &&
        l_0.location =
$LOCATION$CIRCUIT
}

pred teleport[loc: Qubit -> Machine, r: Qubit -> Qubit, uloc: Qubit -> Machine, tele: Int, utele: Int, emptyMachines: Int, uEmptyMachines: Int] {
    all disj q0, q1: Qubit | (q0 -> q1 in r) implies q0.uloc = q1.uloc
    utele = plus[tele, #(uloc - loc)]
    uEmptyMachines = plus[emptyMachines, #(Machine - Qubit.uloc)]
}

fact layerTransition {
    all l: circGraph, us: grph/next[l] { 
	teleport[l.location, us.edges, us.location, l.numTele, us.numTele, l.emptyMachines, us.emptyMachines] 
    }
}

pred finalLayer {  
    lte[grph/last.numTele, $TELE_MAX]
    lte[grph/last.emptyMachines, $VAC_MAX]
}

run finalLayer for $LAYERS circGraph, $INT_BITS Int
"""

ALLOY_TEMPLATE_COST_LB = """
module teleport

open util/ordering[circGraph] as grph
open util/integer

abstract sig Qubit { }
one sig $V_LIST extends Qubit { }

abstract sig Machine {
    costTo: Machine -> Int
} 
one sig $M_LIST extends Machine { }

fact { costTo =
$COST_TO
}

sig circGraph {
    edges: Qubit -> Qubit,
    location: Qubit -> Machine,
    numTele: Int,
    emptyMachines: Int,
    teleCost: Int
} {
    all q: Qubit | #q.location = 1 
}

/*
fact { all c:circGraph |
$M_CAP_LIST
}
*/
fact { all c:circGraph, m:Machine | #(c.location).m < $M_CAP }

fact CircuitGraph {
    let l_0 = grph/first | 
        l_0.numTele = 0 &&
        l_0.emptyMachines = 0 &&
        l_0.teleCost = 0 &&
        l_0.location =
$LOCATION$CIRCUIT
}

pred teleport[loc: Qubit -> Machine, r: Qubit -> Qubit, uloc: Qubit -> Machine, tele: Int, utele: Int, emptyMachines: Int, uEmptyMachines: Int, totCost: Int, uTotCost: Int] {
    all disj q0, q1: Qubit | (q0 -> q1 in r) implies q0.uloc = q1.uloc
    utele = plus[tele, #(uloc - loc)]
    uEmptyMachines = plus[emptyMachines, #(Machine - Qubit.uloc)]
    uTotCost = plus[totCost, sum q: Qubit | ((q.loc).costTo)[q.uloc]]
}

fact layerTransition {
    all l: circGraph, us: grph/next[l] { 
	teleport[l.location, us.edges, us.location, l.numTele, us.numTele, l.emptyMachines, us.emptyMachines, l.teleCost, us.teleCost] 
    }
}

pred finalLayer {  
    lte[grph/last.numTele, $TELE_MAX]
    lte[grph/last.emptyMachines, $VAC_MAX]
    lte[grph/last.teleCost, $COST_MAX]
}

run finalLayer for $LAYERS circGraph, $INT_BITS Int
"""


class QubitAlloc(Enum):
    RANDOM   = 'random' 
    IN_ORDER = 'inorder'

class Exe(Enum):
    BINARY_SEARCH           = 'binary'
    ASCENDING_LINEAR_SEARCH = 'linear'
    RUN_ONCE                = 'once'
    AS_IS                   = 'asis'
    RECENT_HISTORY_SEARCH   = 'recent'

class Solver(Enum):
    MiniSatJNI       = 'MiniSatJNI'
    MiniSatProverJNI = 'MiniSatProverJNI'
    SAT4J            = 'SAT4J'


class Search:
    def __init__(self, lower_bound, upper_bound):
        self.lower_bound = lower_bound
        self.upper_bound = upper_bound
        self.valid_sat = False
        self.valid_unsat = False
    def get_result(self):
        return self.result
    def get_lower(self):
        return self.lower_bound
    def get_upper(self):
        return self.upper_bound
    def get_true_lower(self):
        return self.get_lower()
    def get_true_upper(self):
        return self.get_upper()
    def loop(self):
        pass
    def update(self, satisfiable):
        if satisfiable:
            self.valid_sat = True
        else:
            self.valid_unsat = True
    def _calc_result(self):
        pass

class BinarySearch(Search):
    def __init__(self, lower_bound, upper_bound):
        super().__init__(lower_bound, upper_bound + 1)
        self.result = self._calc_result()
    def get_upper(self):
        return self.upper_bound - 1
    def loop(self):
        return self.lower_bound < self.upper_bound
    def update(self, satisfiable):
        super().update(satisfiable)
        if satisfiable:
            self.upper_bound = self.result
        else:
            self.lower_bound = self.result + 1
        self.result = self._calc_result()
    def _calc_result(self):
        return (self.lower_bound + self.upper_bound) // 2

class AscendingLinearSearch(Search):
    def __init__(self, lower_bound, upper_bound):
        super().__init__(lower_bound, upper_bound)
        self.result = lower_bound
        self.satisfied = False
    def loop(self):
        if self.satisfied:
            return False
        return self.result <= self.upper_bound
    def update(self, satisfiable):
        super().update(satisfiable)
        self.satisfied = satisfiable
        self.result = self.lower_bound = self._calc_result()
    def _calc_result(self):
        return self.result + 1

class OnceSearch(AscendingLinearSearch):
    def __init__(self, lower_bound, upper_bound):
        super().__init__(lower_bound, lower_bound)

class AsIsSearch(AscendingLinearSearch):
    def __init__(self, lower_bound, upper_bound):
        super().__init__(lower_bound, lower_bound)

class RecentHistorySearch(Search): # TODO doesn't quit on unsatisfiable
    history = deque(maxlen=RECENT_HISTORY_SEARCH_Q_LEN)
    def __init__(self, lower_bound, upper_bound):
        super().__init__(lower_bound, upper_bound)

        self.sub_lower_bound, self.sub_upper_bound = (min(RecentHistorySearch.history) - 1, max(RecentHistorySearch.history) + 1) if len(RecentHistorySearch.history) > 0 else (lower_bound, upper_bound)
        self.sub_lower_bound = max(self.sub_lower_bound, 0)
        self.sub_upper_bound = max(self.sub_upper_bound, 0)

       #if (self.sub_upper_bound - self.sub_lower_bound) <= RECENT_HISTORY_LINEAR_RANGE:
       #    self.search = AscendingLinearSearch(self.sub_lower_bound, self.sub_upper_bound)
       #else:
        self.search = BinarySearch(self.sub_lower_bound, self.sub_upper_bound)
        self.loop_result = True
        self.recurse = 0
    def get_result(self):
        return self.search.get_result()
    def get_lower(self):
        return self.search.get_lower()
    def get_upper(self):
        return self.search.get_upper()
    def get_true_lower(self):
        if self.valid_unsat:
            return self.search.get_lower()
        else:
            return self.lower_bound
    def get_true_upper(self):
        if self.valid_sat:
            return self.search.get_upper()
        else:
            return self.upper_bound
    def loop(self):
        return self.loop_result
    def update(self, satisfiable):
        super().update(satisfiable)
        self.search.update(satisfiable)
        self.loop_result = self.search.loop()
        if not self.loop_result:
            if self.recurse == 0:
                if self.sub_lower_bound == self.search.get_lower() and self.lower_bound < self.sub_lower_bound:
                    self.search = BinarySearch(self.lower_bound, self.sub_lower_bound - 1)
                    self.loop_result = True
                    self.recurse += 1
                elif self.sub_upper_bound == self.search.get_upper() and self.sub_upper_bound < self.upper_bound:
                    self.search = BinarySearch(self.sub_upper_bound + 1, self.upper_bound)
                    self.loop_result = True
                    self.recurse += 1
    @classmethod
    def append_history(cls, rslt):
        cls.history.append(rslt)
    @classmethod
    def clear_history(cls):
        cls.history.clear()


SEARCHES = {
    Exe.BINARY_SEARCH:           BinarySearch,
    Exe.ASCENDING_LINEAR_SEARCH: AscendingLinearSearch,
    Exe.RUN_ONCE:                OnceSearch,
    Exe.AS_IS:                   AsIsSearch,
    Exe.RECENT_HISTORY_SEARCH:   RecentHistorySearch
}

flush_out = False

# NOTE HEURISTIC
def qnetwork(machines, capacity, qubits, largest_gate):
    def calc_cap():
        return math.ceil(qubits / machines) #+ 1 # NOTE
    def calc_mach():
        return math.ceil(qubits / capacity)

    m = machines <= 0
    c = capacity <= 0

    capacity = max(capacity, largest_gate)
    if m:
        machines = max(1, machines, calc_mach())
    if c:
        capacity = max(capacity, calc_cap())
    machines = min(machines, calc_mach())

    return machines, capacity

# NOTE HEURISTIC
def max_log2(*args):
   #return max(math.ceil(math.log2(tele + 1)) + 1, 4) # TODO
   #return math.ceil(math.log2(tele + 1))
    return max([(math.ceil(math.log2(arg + 1)) + 1) for arg in args])


def machine_locs(machines, cap):
    strings = []
    cap = str(cap)

    def append(i):
        strings.append("\t#(c.location).")
        strings.append(machines[i])
        strings.append(" < ")
        strings.append(cap)

    append(0)
    for i in range(1, len(machines)):
        strings.append(" &&\n")
        append(i)

    return "".join(strings) 


def qubits_to_machines(qubits, machines, start=0, end=None):
    if end is None:
        end = len(qubits)

    strings = []

    def append(i):
        strings.append("\t\t(")
        strings.append(qubits[i])
        strings.append(" -> ")
        strings.append(machines[i])
        strings.append(")")

    append(start)
    for i in range(start + 1, end, 1):
        strings.append(" + \n")
        append(i)

    return "".join(strings)


def qft_last_location(subp, qubits, machines, capacity):
    qubits_len = len(qubits)
    machine_len = len(machines)

    last_loc = [machines[machine_len - 1 - (q // capacity)] for q in range(subp)]
    return qubits_to_machines(qubits, last_loc)

#    last_loc = []
#    for q in range(subp, machine_len + subp):
#        last_loc += [machines[(q + ((subp + 0) % 2)) % machine_len] for c in range(capacity)]

   #last_loc = [machines[machine_len - 1 - (q // capacity)] for q in range(subp)]
   #last_loc = [machines[((q // capacity) + ((subp + 0) % 2)) % machine_len] for q in range(subp, qubits_len + subp)]
   #last_loc = [machines[((q // capacity) + ((subp) % 2)) % machine_len] for q in range(subp, qubits_len + subp)]
   #return qubits_to_machines(qubits, last_loc)

   #last_loc = [machines[machine_len - 1 - q // capacity] for q in range(subp)]
   #last_loc += [machines[q // capacity] for q in range(qubits_len - subp)]
   #return qubits_to_machines(qubits, last_loc)

   #last_loc = [machines[(q // capacity) % machine_len] for q in range(subp, subp + qubits_len)]
   #return qubits_to_machines(qubits, last_loc)

#   #last_loc = [machines[(q // capacity)] for q in range(qubits_len)]
#    last_loc = [machines[q // capacity] for q in range(min(subp, capacity))]
#   #last_loc += ["None" for q in range(qubits_len - min(subp, capacity))]
#    last_loc += [machines[(q // capacity)] for q in range(qubits_len, min(subp, capacity), -1)]
#    mq = capacity - subp
#    for q in range(subp, qubits_len, 1):
#        last_loc[q] = machines[(mq + q) // capacity]
#    return qubits_to_machines(qubits, last_loc) #, start=subp, end=qubits_len)

   #last_loc = [machines[(q + qubits_len - subp) // capacity] for q in range(subp)]

   #last_loc = [machines[machine_len - 1 - (q // capacity)] for q in range(subp)]
   #last_loc += [machines[q // capacity] for q in range(qubits_len - subp)]
   #return qubits_to_machines(qubits, last_loc, start=subp, end=qubits_len)

#    last_loc = ["None" for q in range(qubits_len)]
#    mq = capacity - subp
#    for q in range(subp, qubits_len, 1):
#        last_loc[q] = machines[(mq + q) // capacity]
#    return qubits_to_machines(qubits, last_loc, start=subp, end=qubits_len)


def cost_to_string(machines, cost):
    cost = str(cost)
    zero = str(0)
    strings = []
    combos = list(combinations(machines, 2))

    def append(m0, m1, cost):
        strings.append(m0)
        strings.append(" -> ")
        strings.append(m1)
        strings.append(" -> ")
        strings.append(cost)
        strings.append(")")

    strings.append("\t(")
    append(machines[0], machines[0], zero)
    for i in range(1, len(machines)):
        strings.append(" + (")
        append(machines[i], machines[i], zero)
    if len(machines) <= 1:
        return "".join(strings)
    strings.append(" + \n")

    m0, m1 = combos[0]
    strings.append("\t(")
    append(m0, m1, cost)
    strings.append(" + (")
    append(m1, m0, cost)
    for i in range(1, len(combos)):
        m0, m1 = combos[i]
        strings.append(" +\n\t(")
        append(m0, m1, cost)
        strings.append(" + (")
        append(m1, m0, cost)

    return "".join(strings)


def get_layer(qubits): 
    als_gates = []

    def append(i):
        als_gates.append("(")
        als_gates.append(Q_PREFIX)
        als_gates.append(qubits[i - 1])
        als_gates.append(" -> ")
        als_gates.append(Q_PREFIX)
        als_gates.append(qubits[i])
        als_gates.append(")")

    append(1)
    for i in range(2, len(qubits)):
        als_gates.append(" + ")
        append(i)

    return als_gates


def prefix_list(p, arr):
    strings = []
    for i in range(len(arr)):
        strings.append(p + arr[i])
    return strings


def list_to_string(arr):
    strings = [arr[0]]
    for i in range(1, len(arr)):
        strings.append(", ")
        strings.append(arr[i]) 
    return "".join(strings)


def open_read(path):
    try:
        with open(path, 'r') as r:
            return r.read()
    except FileNotFoundError:
        print(f"\tError: File '{path}' not found.", flush=flush_out)
    except Exception as e:
        print("\tError:", e, flush=flush_out)


def tfc_to_als(machines, qubit_alloc, capacity, cost, load, tfc_path, als_path, force=False, condense_layers=True, info=False, verbose=False):
    tfc = open_read(tfc_path)
    tfc = tfc.replace('^M', '')

    als_file = open(als_path, 'w')

    digits = int(math.log10(len(tfc)))
    SPACES_0 = 35 + digits * 3
    SPACES_1 = digits * 2
    SPACES_2 = digits

    circuit_strings = []
    circ_freq = defaultdict(lambda: defaultdict(int))

    layers_strings = []
    layers_qubits  = set()

    v_list = set();

    cur_layer = 1
    cur_layer_str = str(cur_layer)
    last_layer_str = "0"

    largest_gate = 1
    gate_count = 0
    single_gate_count = 0
    flip_condense_layers = True
    for line in tfc.splitlines():
        if line.isspace() or not line:
            continue

        qasm_gate = '[' in line and ']' in line
        if qasm_gate:
            line = re.sub(r"[\[\]]", "", line)
            line = re.sub(";", "", line)

        tag, *rem = line.split(maxsplit=1)
        tag = tag.lower()

        if tag == "#":
            continue
 
        if rem: 
            rem = re.split(r'\s|,\s*', rem[0])
        gate = tag[0]

        valid_gate = gate == 't' or gate == 'f'
        if valid_gate or qasm_gate:
            qubits = len(rem)

            if info:
                for q in rem:
                    circ_freq[qubits][q] += 1

            if qubits < 2:
                single_gate_count += 1
                continue

            if qubits > largest_gate:
                largest_gate = qubits

            gate_count += 1

            for q in rem:
                v_list.add(q) 
            layer = get_layer(rem)
            qubits_set = set(rem)

            if not bool(layers_qubits & qubits_set) and flip_condense_layers:
                if layers_strings:
                    layers_strings.append(" +\n   ")
                    layers_strings.append(" " * SPACES_0)
                layers_strings.extend(layer)

                layers_qubits |= qubits_set
                flip_condense_layers = condense_layers
                continue

            def circuit_strings_append():
                circuit_strings.append(" &&\n\tlet l_")
                circuit_strings.append(cur_layer_str)
                circuit_strings.append(" = l_")
                circuit_strings.append(last_layer_str)
                circuit_strings.append(".next ")
                circuit_strings.append(" " * (SPACES_1 - len(cur_layer_str) - len(last_layer_str)))
                circuit_strings.append("| l_")
                circuit_strings.append(cur_layer_str)
                circuit_strings.append(".edges ")
                circuit_strings.append(" " * (SPACES_2 - len(cur_layer_str)))
                circuit_strings.append("= ")
                circuit_strings.extend(layers_strings)

            circuit_strings_append()

            layers_strings = layer
            layers_qubits  = qubits_set

            last_layer_str = cur_layer_str
            cur_layer += 1
            cur_layer_str = str(cur_layer)

    if layers_strings:
        circuit_strings_append()

    v_list = list(v_list)
    qubits = len(v_list)

    if not force:
        machines, capacity = qnetwork(machines, capacity, qubits, largest_gate)
    v_list = prefix_list(Q_PREFIX, v_list) 
    m_list = prefix_list(M_PREFIX, [str(i) for i in range(machines)])
  
    capacity_list = machine_locs(m_list, capacity + 1)

    if qubit_alloc == QubitAlloc.RANDOM:
        qubit_alloc_list = random.sample(m_list * capacity, min(qubits, machines * capacity))
    elif qubit_alloc == QubitAlloc.IN_ORDER:
        qubit_alloc_list = [m_list[i // capacity] for i in range(qubits)]
    location = qubits_to_machines(v_list, qubit_alloc_list) # TODO heuristic

    tele_max = qubits * (cur_layer + 1)
   #int_bits = alloy_int_bits(tele_max)
    int_bits = max_log2(tele_max, capacity)

    cost_to = cost_to_string(m_list, cost) if cost else None

    if verbose:
        single_gate_perc = (single_gate_count / gate_count) * 100
        merges = max(gate_count - (cur_layer + 1), 0)
        merges_perc = (merges / gate_count) * 100
        reduc = single_gate_count + merges
        reduc_perc = single_gate_perc + merges_perc
        print(f"\tIgnored single-qubit gates reduced the layer count by {single_gate_count} ({single_gate_perc:.2f}%)")
        print(f"\tLayer merging reduced the layer count by {merges} ({merges_perc:.2f}%)")
        print(f"\tThere was a total layer reduction of {reduc} ({reduc_perc:.2f}%)")
        print(f"\tThe layer total is {cur_layer}")
        print(f"\tThe number of qubits is {qubits}")
        print(f"\tThe number of machines is {machines}")
        print(f"\tThe largest gate has arity {largest_gate}")
        print(f"\tThe machine capacity is {capacity}")
        print(f"\tThe qubit allocation policy is '{qubit_alloc}'", flush=flush_out)

    if cost and load:
        template = ALLOY_TEMPLATE_COST_LB
    elif load:
        template = ALLOY_TEMPLATE_LB
    else:
        template = ALLOY_TEMPLATE_BASIC

    als = Template(template).safe_substitute({
            'LOCATION': location,
            'CIRCUIT': "".join(circuit_strings),
            'LAYERS': cur_layer + 1,
            'INT_BITS': int_bits,
            'V_LIST': list_to_string(v_list),
            'M_CAP': capacity + 1,
            'M_CAP_LIST': capacity_list,
            'M_LIST': list_to_string(m_list),
            'TELE_MAX': tele_max // 8,          # NOTE heuristic
            'COST_TO': cost_to,
            'VAC_MAX': load,
            'COST_MAX': cost * tele_max // 5 if cost else 1  # NOTE heuristic
        })

    als_file.write(als)
    return als, circ_freq


def prepare_subproblem(als, layers):
    if layers is None:
        return als

    layer = layers[f"circGraph${len(layers) - 1}"]
    return re.sub(r'\$LOCATION', qubits_to_machines([q for m, q in layer], [m for m, q in layer]), als, count=1)


def split_list(a, layer_size):
    if layer_size[0] == 0:
        yield a
    else:
        la = len(a)
        if len(layer_size) == 1:
            n = math.ceil(la / layer_size[0])
        else:
            n = len(layer_size)
        avg = la // n
        rem = la % n
        start = 0
        for i in range(n):
            if len(layer_size) == 1:
                g_size = max(avg + (1 if i < rem else 0), 1)
            else:
                g_size = layer_size[i]
            end = start + g_size
            yield a[start:end]
            start = end


def als_subproblems(als, layer_size, als_extract, qft_last_loc, verbose=False):
    circuit = re.search(r'fact CircuitGraph \{([^}]*)\}', als).group(0)
    temp = re.sub(r'location =([^}]*)\}', 'location =\n$LOCATION &&\n$CIRCUIT\n}', circuit, count=1)
    temp = re.sub(r'fact CircuitGraph \{([^}]*)\}', temp, als, count=1)
    temp = re.sub(r'run finalLayer for (\d+)', 'run finalLayer for $LAYERS', temp, count=1)
   #temp = re.sub(r'circGraph, (\d+) Int', 'circGraph, $INT_BITS Int', temp, count=1)
    if qft_last_loc:
        def last_location_append(match):
            content = match.group(1)
            mod_content = content[:-1] + "$LAST_LOCATION" + content[-1]
            return f"pred finalLayer {{{mod_content}}}"
        temp = re.sub(r'pred finalLayer\s*{([\s\S]*)}', last_location_append, temp, count=1)
    template = Template(temp)

    if qft_last_loc:
        capacity, qubits, machines = als_extract

    init_loc = re.search(r'location =([^&&]*)&&', circuit).group(1) + ' &&'

    logical_lines = re.findall(r'\s*let.*?&&', circuit, flags=re.DOTALL)[1:]
    logical_lines.append(re.search(r'\s*let([^&&]*)\}', circuit).group(0)[:-1])

    subproblems = []
    upper_bounds = []
    groups = list(split_list(logical_lines, layer_size))

    if verbose:
        print(f'\tSplitting into {len(groups)} subproblems', flush=flush_out)

    for i, g in enumerate(groups):
        g[0] = re.sub(r'l_(\d+).next', 'l_0.next', g[0], count=1)
        g[-1] = re.sub(r'&&', '', g[-1], count=1)

        upper_bound = 0
        for l in g:
            upper_bound += l.count('(') * 2
        upper_bounds.append(upper_bound)

        if qft_last_loc > i:
            subproblems.append(template.safe_substitute({
                        'CIRCUIT': "".join(g),
                        'LAYERS': len(g) + 2,
                        'LAST_LOCATION': "\ngrph/last.location = " + qft_last_location(i + 1, qubits, machines, capacity)
                        })
                    )
        elif qft_last_loc:
            subproblems.append(template.safe_substitute({
                        'CIRCUIT': "".join(g),
                        'LAYERS': len(g) + 2,
                        'LAST_LOCATION': ""
                        })
                    )
        else:
            subproblems.append(template.safe_substitute({
                        'CIRCUIT': "".join(g),
                        'LAYERS': len(g) + 2
                        })
                    )
    subproblems[0] = re.sub(r'\$LOCATION &&', init_loc, subproblems[0], count=1)
    return subproblems, upper_bounds


def extract_params_break(string):
    return re.split(r'[,\s]+', string)[2:-2]


def extract_params(als):
    # fact { all c:circGraph, m:Machine | #(c.location).m < 11 }
   #capacities = []
    capacity = int(re.search(r'#\(c\.location\)\.m < (\d+)', als).group(1)) - 1
   #pat = re.compile(r'#\(c\.location\)\.' + M_PREFIX + r'(\d+) < (\d+)')
   #for match in pat.finditer(als):
   #    capacities.append(int(match.group(2)) - 1)
    qubits   = extract_params_break(re.search(r'one sig.*' + Q_PREFIX + r'([^\s]+).*extends Qubit', als).group(0))
    machines = extract_params_break(re.search(r'one sig.*' + M_PREFIX + r'([^\s]+).*extends Machine', als).group(0))
    return [capacity, len(qubits), len(machines)], [capacity, qubits, machines]


def template_tele_int(als):
    als = re.sub(r'lte\[grph/last\.(numTele|emptyMachines), (\d+)\]|\brun finalLayer for (\d+) circGraph, (\d+) Int',
        lambda match:
            r'lte[grph/last.numTele, $TELE_MAX]' if match.group(1) == 'numTele'
            else r'lte[grph/last.emptyMachines, $VAC_MAX]' if match.group(1) == 'emptyMachines'
            else f'run finalLayer for {match.group(3)} circGraph, $INT_BITS Int',
        als, count=2)
    return Template(als)


def start_alloy(solver, ram_gb):
    import jpype         as myjpype
    global jpype
    jpype = myjpype
    import jpype.imports

    try:
        jvm_options = []
        if ram_gb > 0:
            jvm_options.append(f"-Xmx{ram_gb}g")
            jvm_options.append(f"-Xss{ram_gb * 10}m")
        jpype.startJVM(jpype.getDefaultJVMPath(), *jvm_options, *ALLOY_JAR_OPTIONS, '-Djava.class.path=' + ALLOY_JAR_PATH + ALLOY_JAR)
    except Exception as e:
        print("Error:", e, flush=flush_out)
        exit(1)

    from edu.mit.csail.sdg.parser     import CompUtil               as myCompUtil
    from edu.mit.csail.sdg.alloy4     import A4Reporter             as myA4Reporter
    from edu.mit.csail.sdg.translator import A4Options              as myA4Options
    from edu.mit.csail.sdg.translator import TranslateAlloyToKodkod as myTranslateAlloyToKodkod

    global CompUtil, A4Reporter, A4Options, TranslateAlloyToKodkod
    CompUtil               = myCompUtil
    A4Reporter             = myA4Reporter
    A4Options              = myA4Options
    TranslateAlloyToKodkod = myTranslateAlloyToKodkod 

    def get_solver(solver): # TODO Abstract away
        if solver == Solver.MiniSatJNI:
            return A4Options.SatSolver.MiniSatJNI
        if solver == Solver.MiniSatProverJNI:
            return A4Options.SatSolver.MiniSatProverJNI
        if solver == Solver.SAT4J:
            return A4Options.SatSolver.SAT4J
        
    rep = A4Reporter()

    opt = A4Options()
    # Unsat core granularity, default is 0 (only top-level conjuncts are considered), 3 expands all quantifiers
   #opt.coreGranularity  = 
    # This option specifies the unsat core minimization strategy (0=GuaranteedLocalMinimum 1=FasterButLessAccurate 2=EvenFaster...)
   #opt.coreMinimization =
    # This option specifies whether the solver should report only solutions that don't cause any overflows.
    opt.noOverflow       = True
    # This option specifies the maximum skolem-function depth.
   #opt.skolemDepth      = sys.maxsize
    # This option specifies the SAT solver to use (SAT4J, MiniSatJNI, MiniSatProverJNI, ZChaffJNI...)
    opt.solver           = get_solver(solver)
    # This option specifies the amount of symmetry breaking to do (when symmetry breaking isn't explicitly disabled).
   #opt.symmetry         = 
    # This option constrols how deep we unroll loops and unroll recursive predicate/function/macros (negative means it's disallowed)
   #opt.unrolls          = sys.maxsize 

    return rep, opt


def stop_alloy():
    global jpype
    jpype.shutdownJVM()


def run_alloy(als, load, execute, moe, bounds, rep, opt, params, min_int_bits, verbose=False):
    global CompUtil, A4Reporter, A4Options, TranslateAlloyToKodkod

    if verbose:
        print("\t\tRunning Alloy", flush=flush_out)

    als_temp = template_tele_int(als)

    iteration = 0
    last_result = None

    lower_bound, upper_bound = bounds
    search = SEARCHES[execute](lower_bound, upper_bound)

    while search.loop():
        tele = search.get_result()

        if execute != Exe.AS_IS:
           #int_bits = alloy_int_bits(tele)
            int_bits = max(max_log2(tele, *params) + 1, min_int_bits)
            als = als_temp.safe_substitute({
                    'INT_BITS': int_bits,
                    'TELE_MAX': tele,
                    'VAC_MAX': load
                })
        else:
            int_bits = "?" # TODO for AS_IS search

        if verbose:
            print(f"\t\tIteration {iteration} with search {tele} in range [{search.get_lower()}, {search.get_upper()}] and {int_bits} Int", flush=flush_out)

        world = CompUtil.parseEverything_fromString(rep, als)

        commands = world.getAllCommands()
        cmd = commands.get(0)

        solution = TranslateAlloyToKodkod.execute_command(rep, world.getAllReachableSigs(), cmd, opt)
        satisfiable = solution.satisfiable()
        
        search.update(satisfiable)
        if satisfiable:
            last_result = (world, solution, tele)
            if verbose:
                print("\t\t\tSatisfiable", flush=flush_out)
        elif verbose:
                print("\t\t\tUnsatisfiable", flush=flush_out)
        iteration += 1

        if last_result:
            moe_search_upper = max(last_result[2], search.get_true_upper())
            moe_search_lower = min(last_result[2], search.get_true_lower())
            if moe > 0 and (moe_search_upper - moe_search_lower) <= moe:
                if verbose:
                    print(f"\t\tMoE caught range [{moe_search_lower}, {moe_search_upper}]", flush=flush_out)
                break

    if not last_result:
        print(f"\t\tNo solution in range [{lower_bound}, {upper_bound}]", flush=flush_out)
        return (None, None, None)
    elif verbose:
        print(f"\t\tSolution found is {last_result[2]}", flush=flush_out)

    if isinstance(search, RecentHistorySearch):
        search.append_history(last_result[-1])

    moe_range = [moe_search_lower, moe_search_upper]

    return last_result, moe_range


def generate_qft(N):
    lines = [".v 0"]
    for i in range(1, N):
        lines.append(",")
        lines.append(str(i))
    lines.append("\nBEGIN")
    for i in range(N):
        lines.append("\nT1 ")
        lines.append(str(i))
        for j in range(i + 1, N):
            lines.append("\nT2 ")
            lines.append(str(i))
            lines.append(",")
            lines.append(str(j))
    lines.append("\nEND")
    return "".join(lines)


def write_qft(path, N):
    with open(path, 'w') as file:
        file.write(generate_qft(N))


def process_solution(world, solution): 
    tcG = None
    for s in world.getAllReachableSigs():
        if "this/circGraph" == str(s.label):
            tcG = s
            break
    tcG_loc = None
    tcG_numTele = None
    for f in tcG.getFields():
        l = str(f.label)
        if "location" == l:
            tcG_loc = f
        elif "numTele" == l:
            tcG_numTele = f
        elif tcG_loc and tcG_numTele:
            break

    numTeles = {}
    for e in solution.eval(tcG_numTele):
        cG = str(e.atom(0))
        nT = int(str(e.atom(1)))
        numTeles[cG] = nT

    layers = defaultdict(list)
    for e in solution.eval(tcG_loc):
        cG = str(e.atom(0))
        q = str(e.atom(1))[:-2]
        m = str(e.atom(2))[:-2]
        layers[cG].append((m, q))

    return numTeles, layers


def output_info_csv(circ_freq, csv_path):
    csv_arr = [['Arity'] + list(circ_freq[next(iter(circ_freq))].keys()) + ['Total']]
    for freq, qubits in circ_freq.items():
        t = [freq]
        total = 0
        for q in qubits:
            r = qubits[q]
            total += r
            t.append(r)
        t.append(total)
        csv_arr.append(t)
    with open(csv_path, 'w') as csv_file:
        csv.writer(csv_file).writerows(csv_arr)


def detect_swaps(row1, row2):
    if len(row1) == 0 or len(row2) == 0:
        return 0

    pots = [row1[i] != row2[i] for i in range(len(row1))]
    swaps = 0
    for i in range(len(pots) - 1):
        if pots[i]:
            for j in range(i + 1, len(pots)):
                if pots[j] and row1[i] == row2[j] and row1[j] == row2[i]:
                    swaps += 1
                    pots[i] = pots[j] = False
                    break
    return swaps
                

def output_sol_csv(inst, numTeles, layers, start_row, csv_path):
    numTeles = list(numTeles.values())
    layers = list(layers.values())
    assert len(numTeles) == len(layers)

    csv_arr = []
    if inst == 0:
        header = ['Instance', 'Global Circuit layer', 'Local Circuit Layer', 'Number of Teleported Qubits', 'Total Number of Teleported Qubits', 'Number of Teleported Qubit Swaps', 'Total Number of Teleported Qubits Minus Swaps']
        q_list = [q for m, q in layers[0]]
        csv_arr.append(header + q_list)
        start_row = [0 for _ in range(len(header))]

    last_tele = 0
    last_layer = {}
    total_swaps = 0

    for i in range(len(numTeles)):
        layer = [m for m, q in layers[i]]

        swaps = detect_swaps(layer, last_layer)
        total_swaps += swaps

        row = [inst, start_row[1] + i, i, numTeles[i] - last_tele, numTeles[i] + start_row[4], swaps, numTeles[i] - total_swaps + start_row[6]]
        row.extend(layer)
        csv_arr.append(row)

        last_tele = numTeles[i]
        last_layer = layer

    with open(csv_path, 'w' if inst == 0 else 'a') as csv_file:
        csv.writer(csv_file).writerows(csv_arr)

    return row
  

def startup():
    if not os.path.exists(ALLOY_JAR_PATH + ALLOY_JAR):
        print(f"Installing the dependency '{ALLOY_JAR}' at '{ALLOY_JAR_PATH}'", flush=flush_out)
        result = subprocess.run("curl -LO " +  ALLOY_JAR_LINK, shell=True)
        if result.returncode:
            print(f"Error: Alloy could not be installed from '{ALLOY_JAR_LINK}'", flush=flush_out)
            exit(1)
        else:
            print(f"The dependency '{ALLOY_JAR}' has been installed", flush=flush_out)

    try:
        import jpype
        import jpype.imports
    except ModuleNotFoundError:
        print(f"Installing the dependency 'JPype1'", flush=flush_out)
        subprocess.run(JPYPE_INSTALL, shell=True)
        if result.returncode:
            print("Error: JPype1 could not be installed from '{JPYPE_INSTALL}'", flush=flush_out)
            exit(1)
        else:
            print(f"The dependency '{JPYPE_INSTALL}' has been installed", flush=flush_out)


def print_elapsed(start_time, tabs=0):
    elapsed = time.time() - start_time 
    hours, remainder = divmod(elapsed, 60**2)
    minutes, seconds = divmod(remainder, 60)
    t = '\t' * tabs
    print(f"\n{t}Time elapsed: {int(hours):02}:{int(minutes):02}:{seconds:05.2f}", flush=flush_out)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=
            "Convert a '.tfc' file into a '.als' file and execute to find the minimum number of teleportations required.")
    parser.add_argument('filename', type=str, nargs='+',
            help="The input '.tfc' or '.als' file(s). The '-a' flag is expected for '.tfc' and '-e' for '.als'.")
    parser.add_argument('-a', '--als', action='store_true', default=False,
            help="Generate the '.als' file from a '.tfc' file.")
    parser.add_argument('-m', '--machines', type=int, default=0,
            help="With '-a': The number of distributed machines.")
    parser.add_argument('-c', '--capacity', type=int, default=0,
            help="With '-a': The qubit capacity for each machine.")
    parser.add_argument('--force', action='store_true', default=False,
            help="With '-m' and '-c': Force the machine and capacity specified.")
    parser.add_argument('--qubit_alloc', choices=[qa.value for qa in QubitAlloc], default='inorder',
            help="With '-a': Specify how the qubits are allocated to the machines.")
    parser.add_argument('--cost', type=int, default=None,
            help="With '-a': Generate the '.als' with the cost and vacant machine Alloy model with the specified teleportation cost.")
    parser.add_argument('--load', type=int, default=None,
            help="With '-a': Generate the '.als' with the cost and vacant machine Alloy model with the specified teleportation cost.")
    parser.add_argument('-i', '--info', action='store_true', default=False,
            help="With '-a': Give information on the circuit contained within the '.tfc' file.")
    parser.add_argument('--uncond', action='store_true', default=False,
            help="With '-a': Leave the generated '.als' file layers uncondensed")
    parser.add_argument('-e', '--execute', choices=[exe.value for exe in Exe], default=None,
            help="Execute the generated or provided '.als' file with the specified search algorithm.")
    parser.add_argument('--marginoferror', type=int, default=0,
            help="With '-e': Stop the binary search once within range of the specified value.")
    parser.add_argument('-b', '--bounds', nargs=2, type=int, default=[0, None],
            help="With '-e': The lower and upper bound on the number of teleportations used with the search algorithm.")
    parser.add_argument('-l', '--layer', nargs='+', type=int, default=[0],
            help="With '-e': Execute as a number of subproblems with about the specified layer count (vertical execution).")
    parser.add_argument('--qft_last_loc', type=int, default=0,
            help="With '-l': Force the last location for each subproblem for QFT.")
    parser.add_argument('-w', '--write', action='store_true', default=False,
            help="With '-l': Write the subproblem '.als' files to disk.")
    parser.add_argument('-s', '--solver', choices=[solver.value for solver in Solver], default='MiniSatJNI',
            help="With '-e': The SAT solver.")
    parser.add_argument('-r', '--ram', type=int, default=0,
            help="With '-e': Set the amount of RAM in GB available to the Alloy JVM.")
    parser.add_argument('--int_bits', type=int, default=0,
            help="With '-e': Set the minimum value for Int.")
    parser.add_argument('--qft', type=int, default=0,
            help="Generate a '.tfc' for QFT of the supplied size.")
    parser.add_argument('-t', '--time', action='store_true', default=False,
            help="Show execution time.")
    parser.add_argument('-v', '--verbose', action='store_true', default=False,
            help="Show generation and execution information as well as execution time.")
    parser.add_argument('-o', '--output', action='store_true', default=False,
            help="Save any stdout or stderr to a '.out' file.")
    parser.add_argument('-f', '--flush', action='store_true', default=False,
            help="Write output '.out' (like '-o') while flushing every print.")
    parser.add_argument('--outname', type=str, default=None,
            help="Outfile path.")
    args = parser.parse_args()

    files           = args.filename
    gen_als         = args.als
    machines        = args.machines
    capacity        = args.capacity
    force_param     = args.force
    qubit_alloc     = QubitAlloc(args.qubit_alloc) if args.qubit_alloc is not None else None
    cost            = args.cost
    load            = args.load
    info            = args.info
    execute         = Exe(args.execute) if args.execute is not None else None
    marginoferror   = args.marginoferror
    bounds          = args.bounds
    bounds[0]       = max(bounds[0], 0) if args.bounds[0] is not None else 0
    bounds[1]       = bounds[1] if args.bounds[1] is not None and args.bounds[1] > 0 else None
    layer_size      = args.layer
    qft_last_loc    = args.qft_last_loc
    condense_layers = not args.uncond
    write_subs      = args.write
    solver          = Solver(args.solver)
    ram_gb          = args.ram
    min_int_bits    = args.int_bits
    gen_qft         = args.qft
    verbose         = args.verbose
    exe_time        = args.time or verbose
    flush_out       = args.flush
    save_out        = args.output
    outname         = args.outname

    if exe_time:
        global_start_time = time.time()

    if execute:
        startup()
        rep, opt = start_alloy(solver, ram_gb)

    args_info_string = f"""
    The search algorithm is '{args.execute}'
    The bounds are {bounds}
    The layer size is {layer_size}
    The SAT solver is '{args.solver}'
    The margin of error is {marginoferror}
    RAM allocation is set to {f"{ram_gb}GB" if ram_gb > 0 else "'default'"}
    """

    for filename in files:
        path, *post_fix = os.path.splitext(filename)
        if outname:
            path = outname

        if gen_qft > 0:
            write_qft(f"{path}.{gen_qft}.tfc", gen_qft)
            break

        if save_out:
            out_file = open(path + ".out", 'w')
            og_stdout = sys.stdout
            sys.stdout = out_file

        print(f"Processing file '{filename}'", flush=flush_out)
        if verbose:
            print(args_info_string, flush=flush_out)

        if exe_time:
            local_start_time = time.time()

        if ".als" in post_fix:
            gen_als = False
        elif post_fix[-1] in SUPPORTED_FILE_EXTENSIONS:
            gen_als = True
        else:
            print(f"\tNote: The given file {filename} is expected to be a {SUPPORTED_FILE_EXTENSIONS} or a '.als' file.", flush=flush_out)

        als = None
        if gen_als:
            als, circ_freq = tfc_to_als(machines, qubit_alloc, capacity, cost, load, filename, path + ".als", force_param, condense_layers, info, verbose)
            if info:
                output_info_csv(circ_freq, path + ".info.csv")

        if execute:
            if not als:
                als = open_read(filename)
                if not als:
                    continue

            RecentHistorySearch.clear_history()
            als_params, als_extract = extract_params(als)
            if load:
                als_params.append(load)

            layers = None
            last_row = None
            teles_total = 0
            working_moe_range = [0,0]
            for i, (sub_als, upper_bound) in enumerate(zip(*als_subproblems(als, layer_size, als_extract, qft_last_loc, verbose))):
                if verbose:
                    print(f"\n\tInstance {i}", flush=flush_out)
                    instance_start_time = time.time()

                sub_als = prepare_subproblem(sub_als, layers)
                
                if write_subs:
                    sub_path = path + f".sub.{i}.als"
                    if verbose:
                        print(f"\t\tWriting instance '{sub_path}'", flush=flush_out)
                    with open(sub_path, 'w') as subp_f:
                        subp_f.write(sub_als)

                sub_bounds = list(bounds)
                if sub_bounds[1] is None:
                    sub_bounds[1] = upper_bound

                ran_result, moe_range = run_alloy(sub_als, load, execute, marginoferror, sub_bounds, rep, opt, als_params + [layer_size[i] if qft_last_loc else layer_size[0]], min_int_bits, verbose)
                world, solution, tele = ran_result

                working_moe_range[0] += moe_range[0]
                working_moe_range[1] += moe_range[1]
                if verbose:
                    print_elapsed(instance_start_time, 2)
                if world is not None and solution is not None:
                    teles_total += tele
                    numTeles, layers = process_solution(world, solution) 
                    last_row = output_sol_csv(i, numTeles, layers, last_row, path + ".sol.csv")
                else:
                    break

            if verbose:
                teles_swaps = last_row[6]
                print(f"\n\tCumulative solution is {teles_total} ({teles_swaps} swaps)", flush=flush_out)
                if marginoferror > 0:
                    print(f"\t\t MoE solution range is [{working_moe_range[0]}, {working_moe_range[1]}]", flush=flush_out)

        if exe_time:
            print_elapsed(local_start_time, 1)

        if save_out:
            sys.stdout = og_stdout
            out_file.close()

    if execute:
        stop_alloy()

    if exe_time:
       print_elapsed(global_start_time) 
