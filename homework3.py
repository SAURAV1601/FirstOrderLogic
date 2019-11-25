from itertools import count
import copy

import time
var_tracker = count()


def get_standardized_var():
    global var_tracker
    return 'x' + str(next(var_tracker))


class Sentence:
    def __init__(self, sentence=None):
        self.input_s = sentence
        self.predicates_obj = []
        self.premises_obj = []
        self.conclusion_obj = []
        self.implication = False
        self.seen_variables = {}
        if not sentence:
            return

        # Add premises and conclusions for implication
        if '=>' in sentence:
            self.implication = True
            temp_list = sentence.split("=>")
            for i, idx in enumerate(temp_list):
                if i == 0 and '&' in idx:
                    temp_idx = idx.split('&')
                    for t_idx in temp_idx:
                        self.premises_obj.append(Predicate(t_idx, self.implication))
                elif i == 0:

                    self.premises_obj.append(Predicate(idx, self.implication))
                else:

                    self.conclusion_obj.append(Predicate(idx, self.implication))
                self.predicates_obj = self.premises_obj + self.conclusion_obj

        # Add predicates if it's not implication
        else:
            self.predicates_obj.append(Predicate(sentence, self.implication))

        # Eliminate implication
        if self.implication:
            for premise in self.premises_obj:
                premise.negation = not premise.negation

        # standardize var
        for predicate in self.predicates_obj:
            for i, argument in enumerate(predicate.constant_arguments):
                if argument.isalpha() and argument.islower() and len(argument) == 1:
                    if argument in self.seen_variables:
                        predicate.constant_arguments[i] = self.seen_variables[argument]
                    else:
                        st_argument = get_standardized_var()
                        self.seen_variables[predicate.constant_arguments[i]] = st_argument
                        predicate.constant_arguments[i] = st_argument

    def __eq__(self, other):

        if len(self.predicates_obj) != len(other.predicates_obj):
            return False
        f = 0
        for i in self.predicates_obj:
            for j in other.predicates_obj:
                if i != j:
                    continue
                else:
                    f += 1

        return f == len(self.predicates_obj)  # == len(other.predicates_obj)

    def __ne__(self, other):
        return not self.__eq__(other)

    def __contains__(self, item):

        for pred in self.predicates_obj:
            if pred != item:
                continue
            else:
                return True
        return False

    def dump_sentences(self):

        for pred in self.predicates_obj:
            pred.dump_predicate()

class Predicate:
    def __init__(self, sentence, implication):
        self.t_predicate = sentence.strip().split('(')[0].strip()
        self.implication = implication
        self.negation = False
        if self.t_predicate.strip()[0] == '~':
            self.predicate = self.t_predicate.strip()[1:]
            self.negation = True
        else:
            self.predicate = self.t_predicate.strip()
        self.constant_arguments = sentence.split('(')[1].replace(')', '').strip().split(',')

        for i, arg in enumerate(self.constant_arguments):
            self.constant_arguments[i] = arg.strip()

    def __ne__(self, other):
        if self.predicate != other.predicate:
            return True
        if self.constant_arguments != other.constant_arguments:
            return True
        return False

    def __eq__(self, other):
        return not self.__ne__(other)

    def dump_predicate(self):
        print(f"\nPredicate : {self.predicate}")
        print(f"is_neg : {self.negation}")
        print(f"args : {self.constant_arguments}")


def predicate_copy(predicate, predicate_list):
    """
    if not isinstance(predicate, Predicate):
        return []

    new_pred = copy.deepcopy(predicate_list)
    l_1 = []
    for x in new_pred:
        if x != predicate:
            l_1.append(x)
    return l_1
    """
    if isinstance(predicate, Predicate):
        new_predicate_list = copy.deepcopy(predicate_list)
        print(f"New predicate list : {new_predicate_list}")
        return [x for x in new_predicate_list if x != predicate]

def var_substitution(all_predicates, var_map):
    """
    for predicate in all_predicates:
        for i in range(len(predicate.constant_arguments)):
            if not predicate.constant_arguments[i] in var_map:
                continue
            predicate.constant_arguments[i] = var_map[predicate.constant_arguments[i]]
    """
    for predicate in all_predicates:
        for i in range(len(predicate.constant_arguments)):
            if predicate.constant_arguments[i] in var_map:
                predicate.constant_arguments[i] = var_map[predicate.constant_arguments[i]]

class KB:
    def __init__(self, sentences, queries):
        self.input_sentences = sentences
        self.queries = queries
        self.sentences_obj = []
        self.hash_map = {}
        self.queries_obj = []
        self.add_to_kb = []

        for query in self.queries:
            self.queries_obj.append(Sentence(query))

        # Add to KB
        for sentence in self.input_sentences:
            temp_obj = Sentence(sentence)
            self.sentences_obj.append(temp_obj)

            for premise in temp_obj.predicates_obj:

                if premise.t_predicate in self.hash_map and temp_obj not in self.hash_map[premise.t_predicate]:
                    self.hash_map[premise.t_predicate].append(temp_obj)
                elif premise.t_predicate not in self.hash_map:
                    self.hash_map[premise.t_predicate] = [temp_obj]
        print(f"Hash map{self.hash_map}")
        #print(f" RESULT : {self.ask()}!!!")
        self.result = self.ask()

    def variable_unification(self, var, x, theta):

        if var in theta:
            return self.unification(theta[var], x, theta)
        elif x in theta:
            return self.unification(var, theta[x], theta)
        else:
            if not (isinstance(x, str) and x[0].isalpha() and x[0].islower()):
                theta[var] = x
            return theta

    def unification(self, x, y, theta):

        if 'fail' in theta:
            return theta

        if x == y:
            return theta
        elif isinstance(x, str) and x[0].isalpha() and x[0].islower():
            return self.variable_unification(x, y, theta)
        elif isinstance(y, str) and y[0].isalpha() and y[0].islower():
            return self.variable_unification(y, x, theta)
        elif isinstance(x, Predicate) and isinstance(y, Predicate):
            return self.unification(x.constant_arguments, y.constant_arguments,
                                    self.unification(x.predicate, y.predicate, theta))
        elif isinstance(x, list) and isinstance(y, list):
            return self.unification(x[1:], y[1:], self.unification(x[0], y[0], theta))
        else:
            theta['fail'] = 1
            return theta

    def resolution(self, y, x):
        temp_s = []
        for i in x.predicates_obj:
            for j in y.predicates_obj:
                if (i.predicate == j.predicate) and (not (i.negation == j.negation)):
                    theta = {}
                    self.unification(i, j, theta)
                    if 'fail' not in theta:
                        temp_1 = predicate_copy(i, x.predicates_obj[:])
                        var_substitution(temp_1, theta)
                        temp_2 = predicate_copy(j, y.predicates_obj[:])
                        var_substitution(temp_2, theta)

                        # create sentence
                        temp_obj = Sentence()
                        for pred in temp_1:
                            if pred and not (pred in temp_obj):
                                temp_obj.predicates_obj.append(pred)
                        for pred in temp_2:
                            if pred and not(pred in temp_obj):
                                temp_obj.predicates_obj.append(pred)

                        temp_s.append(temp_obj)
        return temp_s

    def loop_detection(self, path, p_len):
        if p_len > 0:
            for i in range(p_len - 1):
                if path[p_len - 1] == path[i] or path[p_len - 1] == self.add_to_kb[0]:
                    return False
        return True

    def query_resolution(self, query, t_count, parent):
        sentences_list = []
        result = False

        if time.time() - time1 > 50:
            print(f"TIMED OUT!!")
            return False

        if not query or not query.predicates_obj:
            return True
        if t_count > 0:
            p_len = len(parent[:t_count - 1])
            if not self.loop_detection(parent, p_len):
                print(f"Yo loop")
                return False

        for pred in query.predicates_obj:
            if pred.negation:
                search_string = pred.predicate
            else:
                search_string = '~' + pred.predicate

            if search_string in self.hash_map:
                sentences_list += self.hash_map[search_string]

        sentences_list += self.add_to_kb[:t_count]


        for sent in sentences_list:

            resolved_sent = self.resolution(sent, query)

            if not resolved_sent:
                continue

            print(f"\nResolved Sentences\n")
            print("=================================================")
            print(f"{resolved_sent[0].dump_sentences()}")
            print("=================================================\n")

            if len(self.add_to_kb) >= t_count + 1:
                self.add_to_kb[t_count] = resolved_sent[0]
            else:
                self.add_to_kb.append(resolved_sent[0])

            if len(parent) > t_count:
                parent[t_count] = resolved_sent[0]
            else:
                parent.append(resolved_sent[0])

            result = self.query_resolution(resolved_sent[0], t_count + 1, parent)
            if result:
                return True

        if not result:
            return result

    def ask(self):
        result = []
        for query in self.queries_obj:
            query.predicates_obj[0].negation = not query.predicates_obj[0].negation
            self.add_to_kb.append(query)
            result.append(self.query_resolution(query, 1, []))

        return result


if __name__ == '__main__':

    with open('input.txt', 'r') as fp:
        query_count = int(fp.readline().strip())
        queries = []
        for i in range(query_count):
            queries.append(fp.readline().strip())

        sentence_count = int(fp.readline().strip())
        sentences = []
        for i in range(sentence_count):
            sentences.append(fp.readline().strip())

        time1 = time.time()
        obj = KB(sentences, queries)

    fp.close()

    with open('output.txt', 'w+') as fp:
        for i, s in enumerate(obj.result):
            if i == 0:
                fp.write(str(s).upper())
            else:
                fp.write('\n' + str(s).upper())
    fp.close()
