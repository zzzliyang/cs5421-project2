########################################################################################
## project2.py - Code template for Project 2 - Functional Dependencies and Normalization 
########################################################################################

## If you need to import library put it below


## Determine the closure of set of attribute S given the schema R and functional dependency F
def closure(R, F, S):
    # make copy of F, S so that they can be called by other functions safely
    new_f = F.copy()
    result = S.copy()
    # flag to stop iteration when no more functional dependency can be drawn from F
    to_stop = False
    while len(new_f) > 0 and not to_stop:
        # in each loop, initialize to_stop to True
        to_stop = True
        # loop through all new_f to find dependency that has its condition in result set
        temp = new_f.copy()
        new_f = []
        for dependency in temp:
            # if found, remove this dependency from new_f
            # add the element to the result set if it's not there yet
            # also set to_stop to Fasle because we have new item in result set
            if is_subset(result, dependency[0]):
                for item in dependency[1]:
                    if item not in result:
                        result.append(item)
                        to_stop = False
            # if not found, may need to check in future runs
            else:
                new_f.append(dependency)
    return result

## Determine the all the attribute closure excluding superkeys that are not candidate keys given the schema R and functional dependency F
def all_closures(R, F):
    all_result = []
    # call the recursive worker function with initialized values
    # result will be added to result by the workers
    super_key_list = []
    for i in range(len(R)):
        all_set = []
        get_all_set_rec(R, i + 1, [], all_set, super_key_list)
        for subset in all_set:
            closure_result = closure(R, F, subset)
            if is_subset(closure_result, R):
                super_key_list.append(subset)
            result = [subset, closure_result]
            all_result.append(result)
    return all_result
    
## Return a minimal cover of the functional dependencies of a given schema R and functional dependencies F.
def min_cover_step1(R, FD):
    new_fd = []
    # simplify right hand side
    for dependency in FD:
        left = dependency[0]
        right = dependency[1]
        for item in right:
            new_fd.append([left, [item]])
    closures = all_closures(R, FD)
    new_fd = [item for item in new_fd if not is_subset(item[0], item[1])]
    for fd_item in new_fd:
        fd_left = fd_item[0]
        for closure in closures:
            closure_left = closure[0]
            if len(closure_left) >= len(fd_left):
                break
            if is_subset(closure[1], fd_item[1]) and is_subset(fd_left, closure_left):
                fd_item[0] = closure_left
                break
    return new_fd

def min_cover_step2(R, new_fd):
    to_continue = True
    while to_continue:
        to_continue = False
        for i in range(len(new_fd)):
            left = new_fd[i][0]
            right = new_fd[i][1]
            new_closures = all_closures(R, new_fd[:i] + new_fd[i + 1:])
            for new_closure in new_closures:
                if set_equals(new_closure[0], left):
                    if is_subset(new_closure[1], right):
                        new_fd.pop(i)
                        to_continue = True
                    break
                # this rule is not found in all closures,
                # meaning it is a super key hence redundant
                if len(new_closure[0]) > len(left):
                    new_fd.pop(i)
                    to_continue = True
                    break
            if to_continue:
                break
    return new_fd

def min_cover(R, FD):
    new_fd = min_cover_step1(R, FD)
    return min_cover_step2(R, new_fd)

## Return all minimal covers reachable from the functional dependencies of a given schema R and functional dependencies F.
def min_covers_step1(R, FD):
    new_fd = []
    # simplify right hand side
    for dependency in FD:
        left = dependency[0]
        right = dependency[1]
        for item in right:
            new_fd.append([left, [item]])
    closures = all_closures(R, FD)
    new_fd = [item for item in new_fd if not is_subset(item[0], item[1])]
    choices = []
    static_items = []
    for fd_item in new_fd:
        choice = []
        fd_left = fd_item[0]
        for closure in closures:
            closure_left = closure[0]
            if len(closure_left) >= len(fd_item[0]):
                break
            if is_subset(closure[1], fd_item[1]) and is_subset(fd_item[0], closure_left):
                fd_left = closure_left
                to_add_choice = True
                for existing_choice in choice:
                    if is_subset(closure_left, existing_choice[0]):
                        to_add_choice = False
                        break
                if to_add_choice:
                    choice.append([closure_left, fd_item[1]])
        if len(choice) > 1:
            is_new_choice = True
            for choice_item in choices:
                if set_equals(choice_item, choice):
                    is_new_choice = False
                    break
            if is_new_choice:
                choices.append(choice)
        else:
            static_items.append([fd_left, fd_item[1]])
    all_combi = []
    get_all_combi([], choices, all_combi)
    result = []
    for combi in all_combi:
        temp_fd = remove_fd_dup(combi + static_items)
        is_new = True
        for existing in result:
            if fd_equals(temp_fd, existing):
                is_new = False
                break
        if is_new:
            result.append(temp_fd)
    return result

def remove_fd_dup(fd):
    result = []
    for i in range(len(fd)):
        found = False
        for j in range(i + 1, len(fd)):
            if fd_equals([fd[i]], [fd[j]]):
                found = True
                break
        # only keep the fd if it's not found in the later part of this list
        if not found:
            result.append(fd[i])
    return result

def get_all_combi(current_list, remain_list, result):
    if len(remain_list) == 0:
        result.append(current_list)
        return
    for i in range(len(remain_list[0])):
        get_all_combi(current_list + [remain_list[0][i]], remain_list[1:], result)

def min_covers(R, FD):
    '''
    Explain the rationale of the algorithm here.
    '''
    results = []
    new_fds = min_covers_step1(R, FD)
    full_closures = all_closures(R, FD)
    for new_fd in new_fds:
        fd_to_keep = []
        fd_redundant = []
        for i in range(len(new_fd)):
            redundant = False
            left = new_fd[i][0]
            right = new_fd[i][1]
            new_closures = all_closures(R, new_fd[:i] + new_fd[i+1:])
            for new_closure in new_closures:
                if set_equals(new_closure[0], left):
                    if is_subset(new_closure[1], right):
                        redundant = True
                    break
                # this rule is not found in all closures,
                # meaning it is a super key hence redundant
                if len(new_closure[0]) > len(left):
                    redundant = True
                    break
            if redundant:
                fd_redundant.append(new_fd[i])
            else:
                fd_to_keep.append(new_fd[i])
        fd_redundant_sub = []
        get_all_subset([], fd_redundant, fd_redundant_sub)
        for sub in fd_redundant_sub:
            temp_result = sub + fd_to_keep
            is_minimal = True
            for i in range(len(temp_result)):
                left = temp_result[i][0]
                right = temp_result[i][1]
                new_closures = all_closures(R, temp_result[:i] + temp_result[i + 1:])
                for new_closure in new_closures:
                    if set_equals(new_closure[0], left):
                        if is_subset(new_closure[1], right):
                            is_minimal = False
                        break
                    # this rule is not found in all closures,
                    # meaning it is a super key hence redundant
                    if len(new_closure[0]) > len(left):
                        is_minimal = False
                        break
            if is_minimal:
                closures_to_check = all_closures(R, temp_result)
                if fd_equals(closures_to_check, full_closures):
                    results.append(temp_result)
    return results

def get_all_subset(current_list, remain_list, result):
    if len(remain_list) == 0:
        result.append(current_list)
        return
    get_all_subset(current_list + [remain_list[0]], remain_list[1:], result)
    get_all_subset(current_list.copy(), remain_list[1:], result)

def min_covers_bak(R, FD):
    '''
    Explain the rationale of the algorithm here.
    '''
    results = []
    new_fds = min_covers_step1(R, FD)
    for new_fd in new_fds:
        fd_to_keep = []
        fd_redundant = []
        for i in range(len(new_fd)):
            redundant = False
            left = new_fd[i][0]
            right = new_fd[i][1]
            new_closures = all_closures(R, new_fd[:i] + new_fd[i+1:])
            for new_closure in new_closures:
                if set_equals(new_closure[0], left):
                    if is_subset(new_closure[1], right):
                        redundant = True
                    break
                # this rule is not found in all closures,
                # meaning it is a super key hence redundant
                if len(new_closure[0]) > len(left):
                    redundant = True
                    break
            if redundant:
                fd_redundant.append(new_fd[i])
            else:
                fd_to_keep.append(new_fd[i])
        fd_redundant_perm = []
        get_all_perm([], fd_redundant, fd_redundant_perm)
        count = 1
        for perm in fd_redundant_perm:
            print(count)
            count += 1
            temp_result = min_cover_step2(R, perm + fd_to_keep)
            is_new = True
            for result in results:
                if fd_equals(result, temp_result):
                    is_new = False
                    break
            if is_new:
                results.append(temp_result)
    return results

def fd_equals(fd1_list, fd2_list):
    if len(fd1_list) != len(fd2_list):
        return False
    for fd1 in fd1_list:
        found = False
        left1 = fd1[0]
        right1 = fd1[1]
        for fd2 in fd2_list:
            left2 = fd2[0]
            right2 = fd2[1]
            if set_equals(left1, left2) and set_equals(right1, right2):
                found = True
        if not found:
            return False
    return True

def get_all_perm(current_list, remain_list, result):
    if len(remain_list) == 0:
        result.append(current_list)
        return
    for i in range(len(remain_list)):
        get_all_perm(current_list + [remain_list[i]], remain_list[:i] + remain_list[i+1:], result)

## Return all minimal covers of a given schema R and functional dependencies F.
def all_min_covers(R, FD):
    '''
    Explain the rationale of the algorithm here.
    '''
    closures = all_closures(R, FD)
    return min_covers(R, closures)

## You can add additional functions below
def set_equals(set1, set2):
    return len(set1) == len(set2) and is_subset(set1, set2)

def is_subset(big, small):
    for item in small:
        if item not in big:
            return False
    return True

def get_all_set_rec(remaining_list, length, current_list, result_list, super_key_list):
    if len(super_key_list) > 0:
        for super_key in super_key_list:
            if is_subset(current_list, super_key):
                return
    if len(current_list) == length:
        result_list.append(current_list)
        return
    if len(remaining_list) == 0:
        return
    item = remaining_list[0]
    current_list_copy = current_list.copy()
    current_list_copy.append(item)
    remaining_list_copy = remaining_list.copy()
    remaining_list_copy.remove(item)
    get_all_set_rec(remaining_list_copy, length, current_list_copy, result_list, super_key_list)
    get_all_set_rec(remaining_list_copy, length, current_list.copy(), result_list, super_key_list)

## Main functions
def main():
    ### Test case from the project
    R = ['A', 'B', 'C', 'D']
    FD = [[['A', 'B'], ['C']], [['C'], ['D']]]
    # FD2 = [[['C', 'D'], ['A']], [['A'], ['B']]]

    # print(closure(R, FD, ['A']))
    # print(closure(R, FD, ['A', 'B']))
    # print(all_closures(R, FD))
    # print(all_closures(R, FD2))

    R = ['A', 'B', 'C', 'D', 'E', 'F']
    FD = [[['A'], ['B', 'C']],[['B'], ['C','D']], [['D'], ['B']],[['A','B','E'], ['F']]]
    R2 = ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H']
    FD2 = [[['A'], ['B']],[['A', 'B', 'C','D'], ['E']], [['E', 'F'], ['G', 'H']],[['A', 'C', 'D','F'], ['E', 'G']]]
    # print(min_cover(R, FD))
    # print(min_cover(R2, FD2))

    R = ['A', 'B', 'C']
    FD = [[['A', 'B'], ['C']],[['A'], ['B']], [['B'], ['A']]] 
    # print(min_covers(R, FD))
    # print(all_min_covers(R, FD))

    ### Add your own additional test cases if necessary

    ## Tutorial questions
    R = ['A', 'B', 'C', 'D', 'E']
    FD = [[['A', 'B'],['C']], [['D'],['D', 'B']], [['B'],['E']], [['E'],['D']], [['A', 'B', 'D'],['A', 'B', 'C', 'D']]]
    R2 = ['A', 'B', 'C']
    FD2 = [[['A'], ['B']], [['B'], ['C']], [['C'], ['A']]]

    print(min_cover(R, FD))
    print(min_covers(R, FD))
    print(all_min_covers(R, FD))
    # print(all_min_covers(R2, FD2))

if __name__ == '__main__':
    main()



