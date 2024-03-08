import re
import sys


def main():
    clauseNumber = 1
    clauses = []
    with open(sys.argv[1], errors='ignore') as input_file:
        for i, line in enumerate(input_file):
            line = re.sub(r'\n', '', line)
            line = re.sub(r'[ \t]+$', '', line)
            cl = []
            for c in line.split(" "):
                cl.append(c)
            clauses.append(cl)

    toProve = clauses[-1]
    del clauses[-1]

    for cl in clauses:
        print(clauseNumber, ". ", ' '.join(cl), " { }", sep='')
        clauseNumber += 1

    for c in range(len(toProve)):
        if '~' in toProve[c]:
            toProve[c] = re.sub(r'~', '', toProve[c])
        else:
            toProve[c] = '~' + toProve[c]

    for c in toProve:
        clauses.append([c])
        print(clauseNumber, ". ", ' '.join([c]), " { }", sep='')
        clauseNumber += 1
    #sort so its easier to retrieve and do resolution
    clauses = sort_inner_lists(sort_by_list_size(clauses))
    cli = 1
    while cli < clauseNumber - 1:
        clj = 0
        while clj < cli:
            #print("testing",cli, clj)
            result = resolve(clauses[cli], clauses[clj], clauses)
            if result is False:
                print(clauseNumber, ". ","Contradiction", ' {', cli + 1, ", ", clj + 1, '}', sep='')
                clauseNumber += 1
                print("Valid")
                sys.exit(0)
            elif result is True:
                clj += 1
                continue
            else:
                print(clauseNumber, ". ",' '.join(result), ' {', cli + 1, ", ", clj + 1, '}', sep='')
                clauseNumber += 1
                clauses.append(result)
                clauses = (sort_by_list_size(clauses))

            clj += 1
        cli += 1
    print('Not Valid')

def sort_by_list_size(list_of_lists):
    sorted_list = sorted(list_of_lists, key=len)
    return sorted_list

def sort_inner_lists(list_of_lists):
    sorted_lists = [sorted(inner_list) for inner_list in list_of_lists]
    return sorted_lists

def have_equivalent_literals(list1, list2):
    # Function to remove '~' from the beginning of a literal, if present
    def clean_literal(literal):
        return literal[1:] if literal.startswith('~') else literal

    # Create sets of cleaned literals for each list
    cleaned_set1 = set(map(clean_literal, list1))
    cleaned_set2 = set(map(clean_literal, list2))

    # Check if there's any intersection between the sets
    return bool(cleaned_set1.intersection(cleaned_set2))

def resolve(c1, c2, clauses):
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
                if len(resolved)==0:
                    return False
                elif impTrue(resolved):
                    return True
                else:
                    sorted_resolved = sorted(resolved)
                    #do a binary search to find the subset of clauses we want to check
                    first_instance = first_instance_index(clauses, len(sorted_resolved))
                    if first_instance == -1: #there are no clauses of equal length
                        return sorted_resolved #so we return this new clause
                    last_instance = last_instance_index(clauses, len(sorted_resolved))
                    sub_list = clauses[first_instance:last_instance+1]


                    for cl in sub_list:
                        if sorted_resolved == cl:
                            return True
                    return sorted_resolved

    if resolved == ors:
        return True

def first_instance_index(list_array, target): #first instance index
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

