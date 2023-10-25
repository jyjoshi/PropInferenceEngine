import copy


def read():
    file = open("Samples/test_case_1/input.txt", "r")
    query = file.readline().replace('\n', '')
    sentences = []
    for _ in range(int(file.readline())):
        sentences.append(file.readline().replace("\n", ""))
    file.close()
    return query, sentences


def output(data):
    file = open("output.txt", "w")
    data = "TRUE" if data else "FALSE"
    file.write(data)
    file.close()




def parseSentence(sentence):
    sentence = sentence.split()
    if len(sentence) >= 3 and sentence[-2] == '=>':
        sentence = " ".join(sentence)
        cnf = convert_implication_to_cnf(sentence)
    else:
        predicates = []
        connectives = []
        for elem in sentence:
            if elem == '&' or elem == '|':
                connectives.append(elem)
            elif elem == '=>':
                # # print("Implication found")
                for i in range(len(connectives)):
                    connectives[i] = flip_connective(connectives[i])
                for i in range(len(predicates)):
                    predicates[i] = flip_predicate(predicates[i])
                connectives.append('|')
            else:
                predicates.append(elem)
        cnf = convert_to_cnf(predicates, connectives)
    return cnf


def convert_to_cnf(predicates, connectives):
    or_encountered = False
    cnf = [predicates[0]]
    # # print("Start cnf is", cnf)
    i = 0
    while i < len(connectives):
        connective = connectives[i]
        if connective == '&' and not or_encountered:
            cnf.append(predicates[i + 1])
        else:
            and_list = [predicates[i + 1]]
            or_encountered = True
            while (i + 1) != len(connectives) and connectives[i + 1] != "|":
                and_list.append(predicates[i + 2])
                i += 1
            # # print("And list is", and_list)

            temp_cnf = []

            for x in range(len(cnf)):
                for y in range(len(and_list)):
                    temp_cnf.append(cnf[x] + " V " + and_list[y])
            cnf = temp_cnf
            # # print(temp_cnf)
            # # print(len(temp_cnf))
        i += 1
    # # print("End cnf is ", cnf)
    # # print("Length of cnf is", len(cnf))
    return cnf


def convert_implication_to_cnf(sentence):
    left_side, last_predicate = sentence.split(' => ')
    first_split = left_side.split(" | ")
    # # print(first_split)
    res_list = []
    for i in range(len(first_split)):
        x = first_split[i].split(" & ")
        # # print(x)
        for i in range(len(x)):
            x[i] = flip_predicate(x[i])
        x = " V ".join(x)
        # # print(x)
        res_list.append(x)
    for i in range(len(res_list)):
        res_list[i] = res_list[i] + " V " + last_predicate
    # # print(res_list)
    return res_list


def flip_connective(connective):
    if connective == '&':
        return '|'
    elif connective == '|':
        return '&'


def flip_predicate(predicate):
    if predicate[0] == '~':
        return predicate[1:]
    else:
        return "~" + predicate


def get_predicate_name(predicate):
    open_bracket_index = predicate.index("(")
    predicate_name = predicate[:open_bracket_index]
    return predicate_name, open_bracket_index


def get_predicate_args(args_string):
    args_list = args_string.split(",")
    return args_list


def get_predicate_info(predicate):
    predicate_name, open_bracket_index = get_predicate_name(predicate)
    args_string = predicate[open_bracket_index + 1: len(predicate) - 1]
    predicate_args = get_predicate_args(args_string)
    return predicate_name, predicate_args


def make_kb(sentences):
    kb = []
    for i in range(len(sentences)):
        cnf = parseSentence(sentences[i])
        for x in cnf:
            predicate_list = x.split(" V ")
            kb.append(predicate_list)
    return kb


def make_predicate_dictionary(kb):
    predicate_dict = dict()
    for i in range(len(kb)):
        clause = kb[i]
        clause_length = len(clause)
        for j in range(clause_length):
            term = clause[j]
            bracket_open_index = term.index("(")
            term_name = term[:bracket_open_index]
            if term_name in predicate_dict.keys():
                predicate_dict[term_name].append((clause_length, i, j))
            else:
                predicate_dict[term_name] = [(clause_length, i, j)]

    for key in predicate_dict.keys():
        values = predicate_dict[key]
        sorted_values = sorted(values)
        predicate_dict[key] = sorted_values

    return predicate_dict


def is_unifiable(query_args, chosen_args):
    c_args_map_dict = dict()
    q_args_map_dict = dict()
    # print("Query predicate args are", query_args)
    # print("Chosen predicate args are", chosen_args)
    for i in range(len(query_args)):
        qarg = query_args[i]
        carg = chosen_args[i]
        q = ord(qarg[0])
        c = ord(carg[0])

        # variable and variable
        if 97 <= q <= 122 and 97 <= c <= 122:
            val = c_args_map_dict.get(carg, None)
            if val and val != qarg:
                return False, [], []
            else:
                c_args_map_dict[carg] = qarg

        # constant and variable
        elif q <= 90 and 97 <= c <= 122:
            val = c_args_map_dict.get(carg, None)
            if val and val != qarg:
                return False, [], []
            else:
                c_args_map_dict[carg] = qarg

        # variable and constant
        elif 97 <= q <= 122 and c <= 90:
            val = q_args_map_dict.get(qarg, None)
            if val and val != carg:
                return False, [], []
            else:
                q_args_map_dict[qarg] = carg

        # constant == constant
        else:
            if not qarg == carg:
                return False, [], []

    return True, q_args_map_dict, c_args_map_dict

    # constant != constant


def get_variables_from_clause(clause):
    variables_list = []
    for predicate in clause:
        variables_list += get_variables_from_predicate(predicate)
    variables_list = list(set(variables_list))
    return variables_list


def get_variables_from_predicate(predicate):
    p_name, p_args = get_predicate_info(predicate)
    variables = []
    for arg in p_args:
        if 97 <= ord(arg[0]) <= 122:
            variables.append(arg)
    return variables




def unify(query_clause, chosen_clause, q_args_map, c_args_map, chosen_query_predicate_index, j):
    q_clause = copy.deepcopy(query_clause)
    c_clause = copy.deepcopy(chosen_clause)

    rename_q_dict = dict()
    rename_c_dict = dict()
    q_clause_variables = get_variables_from_clause(q_clause)
    c_clause_variables = get_variables_from_clause(c_clause)

    # print("Q clause variables are ", q_clause_variables)
    # print("C clause variables are ", c_clause_variables)

    q_variable_initials = ""
    c_variable_initials = ""

    if len(q_clause_variables) == 0:
        q_variable_initials = "usp"
        c_variable_initials = "glo"

    elif q_clause_variables[0].startswith("usp"):
        q_variable_initials = "xer"
        c_variable_initials = "ytl"
    else:
        q_variable_initials = "usp"
        c_variable_initials = "glo"

    num = 0

    for var in q_clause_variables:
        val = q_variable_initials + str(num)
        rename_q_dict[var] = val
        num += 1
        # print("Val is ", val)

    num = 0
    for var in c_clause_variables:
        val = c_variable_initials + str(num)
        rename_c_dict[var] = val
        num += 1
        # print("Clause val is ", val)

    # print("Rename Q Dict is ", rename_q_dict)
    # print("Rename C Dict is ", rename_c_dict)

    new_clause = []
    q_predicates_names = []
    del q_clause[chosen_query_predicate_index]
    del c_clause[j]
    for i in range(len(q_clause)):
        predicate = q_clause[i]
        p_name, p_args = get_predicate_info(predicate)
        q_predicates_names.append(p_name)
        for j in range(len(p_args)):
            if p_args[j] in q_args_map.keys():
                p_args[j] = q_args_map[p_args[j]]
            else:
                ascii_val = ord(p_args[j][0])
                if 97 <= ascii_val <= 122:
                    p_args[j] = rename_q_dict[p_args[j]]

        new_args = ",".join(p_args)
        new_predicate = p_name + "(" + new_args + ")"
        new_clause.append(new_predicate)

    for i in range(len(c_clause)):
        predicate = c_clause[i]
        p_name, p_args = get_predicate_info(predicate)

        if p_name not in q_predicates_names:
            for j in range(len(p_args)):
                if p_args[j] in c_args_map.keys():
                    val = c_args_map[p_args[j]]
                    ascii_val = ord(val[0])
                    if 97 <= ascii_val <= 122:
                        # Variable
                        p_args[j] = rename_q_dict[val]
                    else:
                        # Constant
                        p_args[j] = val
                else:
                    ascii_val = ord(p_args[j][0])
                    if 97 <= ascii_val <= 122:
                        p_args[j] = rename_c_dict[p_args[j]]

            new_args = ",".join(p_args)
            new_predicate = p_name + "(" + new_args + ")"
            new_clause.append(new_predicate)

    return new_clause


def resolve(query_clause):
    # print("Inside Resolve")
    if len(query_clause) == 0:
        return True

    query = tuple(query_clause)
    var = visited.get(query, None)
    if var:
        # print("In here")
        return False
    else:
        visited[query] = 1

    # Code to select which query_predicate should be unified first needs to be written.
    chosen_query_predicate_index = 0
    chosen_query_predicate = copy.deepcopy(query_clause[chosen_query_predicate_index])
    # print("Chosen Query Predicate is ", chosen_query_predicate)
    query_predicate = flip_predicate(chosen_query_predicate)
    query_predicate_name, query_predicate_args = get_predicate_info(query_predicate)
    # print("Negation of chosen query predicate provides", query_predicate_name, query_predicate_args)
    if query_predicate_name not in predicate_dict.keys():
        # print("Predicate not found")
        # print(len(query_predicate_name))
        # print(query_predicate_name)
        return False
    for index in predicate_dict[query_predicate_name]:
        # print("Index is ", index)
        _, i, j = index
        chosen_clause = copy.deepcopy(kb[i])
        # print("Chosen clause is ", chosen_clause)
        chosen_predicate = chosen_clause[j]
        # print("Chosen predicate is ", chosen_predicate)
        chosen_predicate_name, chosen_predicate_args = get_predicate_info(chosen_predicate)
        unifiable, q_args_map, c_args_map = is_unifiable(query_predicate_args, chosen_predicate_args)
        if unifiable:
            # print("Found unifiable")
            new_query = unify(query_clause, chosen_clause, q_args_map, c_args_map, chosen_query_predicate_index, j)
            result = resolve(new_query)
            if result:
                return True
    return False


# Code entry point
query, sentences = read()
kb = make_kb(sentences)
predicate_dict = make_predicate_dictionary(kb)
query = flip_predicate(query)
visited = dict()
result = resolve([query])
output(result)
