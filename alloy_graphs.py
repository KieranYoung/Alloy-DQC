#!/bin/python

import os
import sys
import numpy as np
import pandas as pd
from collections import defaultdict
import statistics


def truncate_after_last_two_periods(s):
    # Count the number of periods in the string
    period_count = s.count('.')
    # If there are no periods, return the string as is
    if period_count == 0:
        return s
    # If there is one period, return everything before it
    elif period_count <= 2:
        return s.split('.')[0]
    # If there are two or more periods, split and join appropriately
    else:
        parts = s.rsplit('.', 2)
        return '.'.join(parts[:-2])


def str_to_range(stri):
    if (type(stri) != str):
        return (99999, -99999)
    stri = stri.split(',')
    for i in range(0, len(stri)):
        stri[i] = int(stri[i].strip())
    return stri

def get_unique(df):
    return df.dropna().unique().tolist()

def analysis2(df):
#   df = df[(df['Search Algorithm'] == search_algo)]
#   groups = df.groupby(['Search Algorithm', 'File', 'SAT Solver', 'Margin of Error'])

    search_algos = get_unique(df['Search Algorithm'])
    sat_solvers = get_unique(df['SAT Solver'])
    files = get_unique(df['File'])
    moes = get_unique(df['Margin of Error'])

    base_ss = sat_solvers[0]
    print(base_ss)


    for sa in search_algos:
        bad_files = set()
        time_ratios = defaultdict(list)
        for f in files:
            for moe in moes:
                for ss in sat_solvers:
                    if (f, moe) in bad_files:
                        continue
                    q = df[(df['Search Algorithm'] == sa) &
                           (df['File'] == f) &
                           (df['Margin of Error'] == moe) &
                           (df['SAT Solver'] == ss)];
                    b = df[(df['Search Algorithm'] == sa) &
                           (df['File'] == f) &
                           (df['Margin of Error'] == moe) &
                           (df['SAT Solver'] == base_ss)];
                    if q.shape[0] == 0 or b.shape[0] == 0:
                        bad_files.add((f, moe))
                        continue
                    assert(q.shape[0] == 1 and b.shape[0] == 1)
                    q = q.iloc[0]
                    b = b.iloc[0]

                    time = q['Time']
                    b_time = b['Time']
                    if np.isnan(time) or np.isnan(b_time):
                        bad_files.add((f, moe))
                        continue

                    time_ratio = time / b_time
                    time_ratios[(moe, ss)].append(time_ratio)
        for moe in moes:
            for ss in sat_solvers:
                print(sa, ",", moe, ",", ss, ",", statistics.mean(time_ratios[(moe, ss)]))

        total_mixes = len(files)*len(moes)
        print(sa, total_mixes - len(bad_files), "/", total_mixes)
        

def analysis(df, search_algo, axis=True):
    print(search_algo)

    PRiT_avg = defaultdict(list)
    PRiR_avg = defaultdict(list)
    PRiR_ir_avg = defaultdict(list)
    PRiR_mid_avg = defaultdict(list)

    if axis:
        groups = df.groupby(['Search Algorithm', 'File', 'SAT Solver', 'Margin of Error'])
        NE = ""
    else:
        groups = df.groupby(['SAT Solver', 'File', 'Search Algorithm', 'Margin of Error'])
        NE = "2"
    zero_moe_time = [("",""), 0, 0]
    bad_circs = set()
    good_circs = set()
    moe_keys = set()
    for (sa, f, ss, moe), g in groups:
        if (f, ss) in bad_circs or sa != search_algo:
            continue
        time = g.iloc[0]['Time']
        tele = g.iloc[0]['Cumulative Solution']
        if int(moe) == 0:
            zero_moe_time = [(f, ss), time, tele]
        if (f, ss) != zero_moe_time[0] or np.isnan(time) or np.isnan(tele):
            bad_circs.add((f, ss))
            continue

        rang = str_to_range(g.iloc[0]['MoE Range'])

        time_result = (zero_moe_time[1] - time) / zero_moe_time[1]
        tele_result = tele / zero_moe_time[2]

        if time_result < 0:
            bad_circs.add((f, ss))
            continue

        in_range = zero_moe_time[2] >= rang[0] and zero_moe_time[2] <= rang[1]
        mid_range = ((rang[1] + rang[0]) / 2)
        if in_range:
            mid_range = abs((mid_range - zero_moe_time[2]) / zero_moe_time[2])
        else:
            mid_range = 0

        good_circs.add((f, ss))
        moe_keys.add(moe)

        PRiT_avg[moe].append(time_result)
        PRiR_avg[moe].append(tele_result)
        PRiR_ir_avg[moe].append(int(in_range))
        if in_range:
            PRiR_mid_avg[moe].append(mid_range)

        df.loc[g.index, 'PRiR-in-range'+NE] = in_range
        df.loc[g.index, 'PRiR-mid'+NE] = mid_range
        df.loc[g.index, 'PRiT'+NE] = time_result
        df.loc[g.index, 'PRiR'+NE] = tele_result
#       print(f, ss, sa, moe, time, "\t", time_result, tele_result, in_range, mid_range)

    print(len(good_circs), "/", len(good_circs | bad_circs))
#   print(good_circs)
#   print(bad_circs)

    avgs = [PRiT_avg, PRiR_avg, PRiR_ir_avg, PRiR_mid_avg]
    print("avg time\n", "avg tele\n", "avg MoE 0 tele in range of MoE bounds\n", "avg MoE 0 tele mid of bounds")
    for moe in moe_keys:
        print(moe)
        for avg in avgs:
            if len(avg[moe]) == 0:
                mean = "N/A"
            else:
                mean = statistics.mean(avg[moe])
            print("\t", mean)

    f_df = df
    for f, ss in bad_circs:
        if axis:
            f_df = f_df[~(((f_df['File'] == f) & (f_df['SAT Solver'] == ss)) | (f_df['Search Algorithm'] != search_algo))]
        else:
            f_df = f_df[~(((f_df['File'] == f) & (f_df['Search Algorithm'] == ss)) | (f_df['SAT Solver'] != search_algo))]
    return f_df

if __name__ == '__main__':
    if len(sys.argv) != 2:
        print(sys.argv[0], " csv")
        exit(0)

    csv_filename = sys.argv[1]

    df = pd.read_csv(csv_filename, dtype={'MoE Range': str})
#   print(df.dtypes)

    df['File'] = df['File'].apply(truncate_after_last_two_periods)
    for ne in ["", "2"]:
        df['PRiT'+ne] = 0.0
        df['PRiR'+ne] = 0.0
        df['PRiR-in-range'+ne] = False
        df['PRiR-mid'+ne] = 0.0

    r_df = analysis(df, 'recent')
    b_df = analysis(df, 'binary')
    l_df = analysis(df, 'linear')

    analysis(df, 'SAT4J', False)
    analysis(df, 'MiniSatJNI', False)
    analysis(df, 'MiniSatProverJNI', False)

    analysis2(df)

    f_df = pd.concat([r_df, b_df, l_df], axis=0)

    base_csv_filename = os.path.splitext(csv_filename)[0]
    f_df.to_csv(base_csv_filename + ".filtered.csv", index=False)
    f_df[(f_df['Margin of Error'] == 0) & (f_df['Search Algorithm'] == 'recent') & (f_df['SAT Solver'] == 'MiniSatJNI')].to_csv(base_csv_filename + ".table.csv", index=False);
