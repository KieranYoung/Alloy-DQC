import sys
import os
import re
import csv

# Regular expression patterns for extracting data
patterns = {
    'Cumulative Solution': re.compile(r"Cumulative solution is (\d+)"),
    'Swaps': re.compile(r"Cumulative solution is \d+ \((\d+) swaps\)"),
    'MoE Range': re.compile(r"MoE solution range is \[([^\]]+)\]"),
    'Time': re.compile(r"Time elapsed: (\d{2}):(\d{2}):(\d{2})\.(\d{2})"),
    'Search Algorithm': re.compile(r"The search algorithm is '(\w+)'"),
    'Margin of Error': re.compile(r"The margin of error is (\d+)"),
    'Bounds': re.compile(r"The bounds are \[([^\]]+)\]"),
    'Layer Size': re.compile(r"The layer size is \[(\d+)\]"),
    'SAT Solver': re.compile(r"The SAT solver is '(\w+)'"),
    'RAM Allocation': re.compile(r"RAM allocation is set to (\d+)GB"),
    'Ignored Single-Qubit Gates Reduction': re.compile(r"Ignored single-qubit gates reduced the layer count by (\d+) \(([\d.]+%)\)"),
    'Layer Merging Reduction': re.compile(r"Layer merging reduced the layer count by (\d+) \(([\d.]+%)\)"),
    'Total Layer Reduction': re.compile(r"There was a total layer reduction of (\d+) \(([\d.]+%)\)"),
    'Layer Total': re.compile(r"The layer total is (\d+)"),
    'Number of Qubits': re.compile(r"The number of qubits is (\d+)"),
    'Number of Machines': re.compile(r"The number of machines is (\d+)"),
    'Largest Gate Arity': re.compile(r"The largest gate has arity (\d+)"),
    'Machine Capacity': re.compile(r"The machine capacity is (\d+)"),
    'Qubit Allocation Policy': re.compile(r"The qubit allocation policy is '([^']+)'"),
    'Splitting into Subproblems': re.compile(r"Splitting into (\d+) subproblems")
}

def convert_to_milliseconds(hours, mins, secs, mills):
    return (int(hours) * 3600 * 1000) + (int(mins) * 60 * 1000) + (int(secs) * 1000) + int(mills)

# Function to find .out files and extract data
def find_and_extract(directory):
    extracted_data = []
    
    # Walk through the directory and subdirectories
    for root, _, files in os.walk(directory):
        for file in files:
            if file.endswith(".out"):
                file_path = os.path.join(root, file)
                
                # Initialize a dictionary to store extracted values
                data = {
                    'Directory': os.path.basename(root),
                    'File': file,
                    'Cumulative Solution': '',
                    'Swaps': '',
                    'MoE Range': '',
                    'Time': '',
                    'Search Algorithm': '',
                    'Margin of Error': '',
                    'Bounds': '',
                    'Layer Size': '',
                    'SAT Solver': '',
                    'RAM Allocation (GB)': '',
                    'Ignored Single-Qubit Gates Reduction': '',
                    'Ignored Single-Qubit Gates Reduction (%)': '',
                    'Layer Merging Reduction': '',
                    'Layer Merging Reduction (%)': '',
                    'Total Layer Reduction': '',
                    'Total Layer Reduction (%)': '',
                    'Layer Total': '',
                    'Number of Qubits': '',
                    'Number of Machines': '',
                    'Largest Gate Arity': '',
                    'Machine Capacity': '',
                    'Qubit Allocation Policy': '',
                    'Splitting into Subproblems': ''
                }
                
                # Open and read the .out file
                try:
                    with open(file_path, 'r') as f:
                        content = f.read()
                except Exception as e:
                    print(f"Error reading {file_path}: {e}")
                    continue
                
                # Extract each pattern
                for key, pattern in patterns.items():
                    match = pattern.search(content)
                    if match:
                        if key in ['Ignored Single-Qubit Gates Reduction', 'Layer Merging Reduction', 'Total Layer Reduction']:
                            data[key] = match.group(1)
                            data[f"{key} (%)"] = match.group(2)
                        elif key in ['Time']:
                            data[key] = convert_to_milliseconds(*match.groups())
                        else:
                            data[key] = match.group(1)
                
                # Append the data dictionary to the list
                extracted_data.append(data)
    
    return extracted_data

# Function to write the extracted data to a CSV file
def write_to_csv(extracted_data, output_csv):
    if not extracted_data:
        print("No data extracted to write.")
        return
    
    # Get the header from the keys of the first dictionary
    header = extracted_data[0].keys()
    
    try:
        with open(output_csv, 'w', newline='') as csvfile:
            csvwriter = csv.DictWriter(csvfile, fieldnames=header)
            # Write header
            csvwriter.writeheader()
            # Write data rows
            csvwriter.writerows(extracted_data)
    except Exception as e:
        print(f"Error writing to CSV file {output_csv}: {e}")

if __name__ == "__main__":
    if (len(sys.argv) < 3):
        print(f'{sys.argv[0]} out.csv dir1 dir2 ...')
        exit(1)
    
    # Define the output CSV file name
    output_csv = sys.argv[1] #"output.csv"
    
    # Find and extract data
    extracted_data = []
    for i in range(2, len(sys.argv)):
        # Define the root directory where the search should begin
        root_dir = sys.argv[i]
        extracted_data += find_and_extract(root_dir)
    
    # Write the results to a CSV file
    write_to_csv(extracted_data, output_csv)

    print(f"Extraction complete. Data saved to {output_csv}.")
