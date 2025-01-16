import re
import sys
import os
from collections import defaultdict

output_log = []

def print_and_log(*args, sep=' ', end='\n'):
    """
    Prints the given args to stdout AND saves the same line in `output_log`.
    """
    message = sep.join(str(a) for a in args)
    # Print to console
    print(message, end=end)
    # Store in log list
    output_log.append(message)

def main():
    if len(sys.argv) < 2:
        print_and_log("Error: No file path provided. Please provide a valid file path as a command-line argument.")
        sys.exit(1)

    file_path = sys.argv[1]

    if not os.path.isfile(file_path):
        print_and_log(f"Error: File '{file_path}' does not exist or is not a valid file.")
        sys.exit(1)

    clauseNumber = 1
    clauses = []
    knowledge_dict = defaultdict(set)  # key = length, value = set of sorted-tuples

    try:
        with open(file_path, errors='ignore') as input_file:
            for i, line in enumerate(input_file):
                line = re.sub(r'\n', '', line)
                line = re.sub(r'[ \t]+$', '', line)
                cl = []
                for c in line.split(" "):
                    cl.append(c)
                clauses.append(cl)

        toProve = clauses[-1]
        del clauses[-1]

        # print clauses. This technically can be merged with building the knowledge_dict
        # But it's more "modular" this way. Looping through twice isn't that bad.
        for cl in clauses:
            print_and_log(f"{clauseNumber}. {' '.join(cl)} {{ }}")
            clauseNumber += 1

        # Build knowledge_dict from 'clauses'
        for cl in clauses:
            sorted_cl = sorted(cl)
            t_cl = tuple(sorted_cl)
            knowledge_dict[len(t_cl)].add(t_cl)

        # Create the contradictory statement
        for c in range(len(toProve)):
            if '~' in toProve[c]:
                toProve[c] = re.sub(r'~', '', toProve[c])
            else:
                toProve[c] = '~' + toProve[c]

        for c in toProve:
            clauses.append([c])
            print_and_log(f"{clauseNumber}. {c} {{ }}")
            clauseNumber += 1
            # Also add to knowledge_dict if needed
            sorted_cl = sorted([c])
            t_cl = tuple(sorted_cl)
            knowledge_dict[len(t_cl)].add(t_cl)

        # Using a two pointer method to compare and contrast clauses,
        # With cli being the left pointer
        # and clj being the right pointer
        cli = 1
        while cli < clauseNumber - 1:
            clj = 0
            while clj < cli:
                result = resolve(clauses[cli], clauses[clj], clauses, knowledge_dict)
                if result is False:
                    print_and_log(f"{clauseNumber}. Contradiction {{ {cli + 1}, {clj + 1} }}")
                    clauseNumber += 1
                    print_and_log("Valid")
                    write_output_to_file("output.txt")
                    sys.exit(0)
                elif result is True:
                    clj += 1
                    continue
                else:
                    print_and_log(f"{clauseNumber}. {' '.join(result)} {{ {cli + 1}, {clj + 1} }}")
                    clauseNumber += 1
                    clauses.append(result)
                    add_clause(result, clauses, knowledge_dict)
                clj += 1
            cli += 1
        print_and_log("Not Valid")
    
    except Exception as e:
        print_and_log(f"An error occurred while processing the file: {e}")        
        write_output_to_file("output.txt")
        sys.exit(1)

        # If we reach here normally, write final output to file
    write_output_to_file("output.txt")

def write_output_to_file(filename):
    """
    Writes all lines in `output_log` to the given filename.
    """
    with open(filename, 'w') as f:
        for line in output_log:
            f.write(line + '\n')


def add_clause(clause_list, clauses, knowledge_dict):
    sorted_clause = sorted(clause_list)
    t_clause = tuple(sorted_clause)
    length = len(sorted_clause)

    if t_clause in knowledge_dict[length]:
        return True  # Already in DB
    else:
        knowledge_dict[length].add(t_clause)
        clauses.append(sorted_clause)
        return False

def sort_by_list_size(list_of_lists):
    sorted_list = sorted(list_of_lists, key=len)
    return sorted_list

def sort_inner_lists(list_of_lists):
    sorted_lists = [sorted(inner_list) for inner_list in list_of_lists]
    return sorted_lists

def full_sort(list_of_lists):
    return sort_inner_lists(sort_by_list_size(list_of_lists))


# This helps us only do logic on clauses with who are subsets of other clauses
def have_equivalent_literals(list1, list2):
    # Function to remove '~' from the beginning of a literal, if present
    def clean_literal(literal):
        return literal[1:] if literal.startswith('~') else literal

    # Create sets of cleaned literals for each list
    cleaned_set1 = set(map(clean_literal, list1))
    cleaned_set2 = set(map(clean_literal, list2))

    # Check if there's any intersection between the sets
    return bool(cleaned_set1.intersection(cleaned_set2))

def resolve(c1, c2, clauses, knowledge_dict):
    if not have_equivalent_literals(c1, c2):
        return True

    resolved2 = c1 + c2
    resolved = None
    hashmap = {}
    for r1 in resolved2:
        if r1 not in hashmap.keys():
            hashmap[r1] = 0

    resolved = list(hashmap.keys())
    ors = list(hashmap.keys())
    for l1 in c1:
        for l2 in c2:
            if neg(l1, l2):

                resolved.remove(l1)
                resolved.remove(l2)
                if len(resolved)==0:  # We have found a contradiction. Exit the program
                    return False
                elif impTrue(resolved): # You can reduce this proposition further as there are two of the same literals
                    return True
                else:
                    sorted_resolved = sorted(resolved)
                    t_res = tuple(sorted_resolved)
                    if t_res in knowledge_dict[len(t_res)]:
                        # We already have it
                        return True
                    else:
                        # It's new; let's add it
                        add_clause(sorted_resolved, clauses, knowledge_dict)
                        return sorted_resolved

    if resolved == ors:
        return True

# Finding the first instance of a target length in an array? This returns the position of the target length value so position not value 
def first_instance_index(list_array, target): 
    low, high = 0, len(list_array) - 1
    result = -1

    while low <= high:
        mid = (low + high) // 2
        current_number = len(list_array[mid])

        if current_number == target:
            result = mid  # Store the current index as a potential result
            high = mid - 1  # Continue searching to the left
        elif current_number < target:
            low = mid + 1
        else:
            high = mid - 1

    return result

def last_instance_index(list_array, target):
    low, high = 0, len(list_array) - 1
    result = -1

    while low <= high:
        mid = (low + high) // 2
        current_number = len(list_array[mid])

        if current_number == target:
            result = mid  # Store the current index as a potential result
            low = mid + 1  # Continue searching to the right
        elif current_number < target:
            low = mid + 1
        else:
            high = mid - 1

    return result

def neg(l1, l2):
    if l1 == ('~' + l2) or l2 == ('~' + l1):
        return True
    else:
        return False


# Check to see if there are two instances of the same literal in the clause
def impTrue(clause):
    def clean_literal(literal):
        return literal[1:] if literal.startswith('~') else literal

    literal_count = {}

    for literal in clause:
        cleaned_literal = clean_literal(literal)

        if cleaned_literal not in literal_count:
            literal_count[cleaned_literal] = 0
        literal_count[cleaned_literal] += 1
        if (literal_count[cleaned_literal] > 1):
            return True
    return False


def Diff(li1, li2):
    li_dif = [i for i in li1 + li2 if i not in li1 or i not in li2]
    return li_dif

if __name__ == "__main__":
    main()

