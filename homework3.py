from itertools import count
import copy

var_tracker = count()


def get_standardized_var():
    global var_tracker
    return 'x' + str(next(var_tracker))


class Sentence:
    # each sentence ge list of predicates, store operator
    def __init__(self, sentence = None):
        self.input_s = sentence
        self.predicates_obj = []
        self.premises_obj = []
        self.conclusion_obj = []
        self.is_implication = False

        if not sentence:
            return
        # Add predicates
        if '=>' in sentence:
            self.is_implication = True
            temp_list = sentence.split("=>")
            for i, idx in enumerate(temp_list):
                if i == 0 and '&' in idx:
                    temp_idx = idx.split('&')
                    for t_idx in temp_idx:
                        self.premises_obj.append(Predicate(t_idx, self.is_implication))
                elif i == 0:

                    self.premises_obj.append(Predicate(idx, self.is_implication))
                else:

                    self.conclusion_obj.append(Predicate(idx, self.is_implication))
                self.predicates_obj = self.premises_obj+self.conclusion_obj
        else:
            self.predicates_obj.append(Predicate(sentence, self.is_implication))
        # Add predicates - end

        # Eliminate implication
        if self.is_implication:
            for premise in self.premises_obj:
                premise.is_negation = not premise.is_negation

        # standardize var
        self.seen_variables = {}
        for predicate in self.predicates_obj:
            for i, argument in enumerate(predicate.constant_arguments):
                if argument.isalpha() and argument.islower() and len(argument) == 1:
                    if argument in self.seen_variables:
                        predicate.constant_arguments[i] = self.seen_variables[argument]
                    else:
                        st_argument = get_standardized_var()
                        self.seen_variables[predicate.constant_arguments[i]] = st_argument
                        predicate.constant_arguments[i] = st_argument

        self.dump_sentences()

    def dump_sentences(self):

        for pred in (self.predicates_obj + self.premises_obj + self.conclusion_obj):
            pred.dump_predicate()


class Predicate:
    def __init__(self, sentence, is_implication):
        self.t_predicate = sentence.strip().split('(')[0]
        self.is_implication = is_implication
        self.is_negation = False
        if self.t_predicate.strip()[0] == '~':
            self.predicate = self.t_predicate.strip()[1:]
            self.is_negation = True
        else:
            self.predicate = self.t_predicate.strip()
        self.constant_arguments = sentence.split('(')[1].replace(')', '').strip().split(',')

        for i, arg in enumerate(self.constant_arguments):
            self.constant_arguments[i] = arg.strip()

        # print(f"Predicate:{self.predicate}, Negation:{self.is_negation}, Implication:{self.is_implication}")
        # print(f"Arguments:{self.constant_arguments}")
    def __ne__(self, other):
        if self.predicate != other.predicate:
            return True
        if self.constant_arguments != other.constant_arguments:
            return True
        return False

    def dump_predicate(self):
        print(f"\nPredicate : {self.predicate}")
        print(f"is_neg : {self.is_negation}")
        print(f"args : {self.constant_arguments}")




class KB:
    def __init__(self, sentences, queries):
        self.input_sentences = sentences
        self.queries = queries
        self.sentences_obj = []
        self.kb_hashmap = {}
        self.queries_obj = []
        self.add_to_kb = []

        for query in self.queries:
            self.queries_obj.append(Sentence(query))

        # Tell
        for sentence in self.input_sentences:
            temp_obj = Sentence(sentence)
            self.sentences_obj.append(temp_obj)


            for premise in temp_obj.predicates_obj:

                if premise.t_predicate in self.kb_hashmap and temp_obj not in self.kb_hashmap[premise.t_predicate]:
                    self.kb_hashmap[premise.t_predicate].append(temp_obj)
                elif premise.t_predicate not in self.kb_hashmap:
                    self.kb_hashmap[premise.t_predicate] = [temp_obj]
        # Tell - end

        print(f"Hashmap:{self.kb_hashmap}")
        result = self.ask()
        print(f"Result:{result}")

        # print(f"Queries:{self.queries}")

    def variable_unification(self, var, x, theta):

        if var in theta:
            return self.unification(theta[var], x, theta)
        elif x in theta:
            return self.unification(var, theta[x], theta)
        else:
            theta[var] = x
            return theta

    def unification(self, x, y, theta):

        if 'fail' in theta:
            return theta

        if x == y:
            return theta
        elif isinstance(x, str) and x[0].isalpha() and x[0].islower():
            return self.variable_unification(x, y, theta)
        elif isinstance(y ,str) and y[0].isalpha() and y[0].islower():
            return self.variable_unification(y, x, theta)
        elif isinstance(x, Predicate) and isinstance(y, Predicate):
            return self.unification(x.constant_arguments, y.constant_arguments,
                                    self.unification(x.predicate, y.predicate, theta))
        elif isinstance(x, list) and isinstance(y, list):
            return self.unification(x[1:], y[1:], self.unification(x[0], y[0], theta))
        else:
            theta['fail'] = 1
            return theta

    def duplicate_predicate(self, predicate, predicate_list):
        if isinstance(predicate, Predicate):
            new_predicate_list = copy.deepcopy(predicate_list)
            print(f"New predicate list : {new_predicate_list}")
            return [x for x in new_predicate_list if x != predicate]

    def substitute(self, predicate_list, theta):

        for predicate in predicate_list:
            for i in range(len(predicate.constant_arguments)):
                if predicate.constant_arguments[i] in theta:
                    predicate.constant_arguments[i] = theta[predicate.constant_arguments[i]]

    def resolution(self, y, x):
        temp_s = []
        for i in x.predicates_obj:
            for j in y.predicates_obj:
                if (i.predicate == j.predicate) and (not (i.is_negation == j.is_negation)):
                    theta = {}
                    self.unification(i, j, theta)
                    if 'fail' not in theta:
                        print(f"Theta : {theta}")
                        new_pred_i = self.duplicate_predicate(i, x.predicates_obj[:])
                        print(f"S1 : New predicates : {[x.dump_predicate() for x in new_pred_i]}")
                        new_pred_j = self.duplicate_predicate(j, y.predicates_obj[:])
                        print(f"S2 : New predicates : {[x.dump_predicate() for x in new_pred_j]}")
                        self.substitute(new_pred_i, theta)
                        self.substitute(new_pred_j, theta)

                        # create sentence
                        temp_obj = Sentence()
                        for pred in new_pred_i:
                            if pred:
                                temp_obj.predicates_obj.append(pred)
                        for pred in new_pred_j:
                            if pred:
                                temp_obj.predicates_obj.append(pred)

                        temp_obj.dump_sentences()
                        temp_s.append(temp_obj)
        return temp_s

    def query_resolution(self, query, count):
        sentences_list = []
        result = False

        if not query or not query.predicates_obj:
            return True

        for pred in query.predicates_obj:
            if pred.is_negation:
                search_string = pred.predicate
            else:
                search_string = '~' + pred.predicate

            if search_string in self.kb_hashmap:
                sentences_list += self.kb_hashmap[search_string]

            sentences_list += self.add_to_kb[:count]
            print(f"\nResolution sentences : {sentences_list}")
            for sent in sentences_list:
                resolved_sent = self.resolution(sent, query)

                if not resolved_sent:
                    print(f"Not resolved")
                    continue

                print(f"\nResolved Sentences\n")
                print("=================================================")
                print(f"{resolved_sent[0].dump_sentences()}")
                print("=================================================\n")
                if len(self.add_to_kb) >= count+1:
                    self.add_to_kb[count] = resolved_sent[0]
                else:
                    self.add_to_kb.append(resolved_sent[0])
                result = self.query_resolution(resolved_sent[0], count + 1)
                if result:
                    return True
        return result

    def ask(self):
        result = []
        for query in self.queries_obj:
            query.predicates_obj[0].is_negation = not query.predicates_obj[0].is_negation
            self.add_to_kb.append(query)
            result.append(self.query_resolution(query, 1))
        print(f"Query result : {result}")
        return result


if __name__ == '__main__':

    with open('input2.txt', 'r') as fp:
        query_count = int(fp.readline().strip())
        queries = []
        for i in range(query_count):
            queries.append(fp.readline().strip())

        sentence_count = int(fp.readline().strip())
        sentences = []
        for i in range(sentence_count):
            sentences.append(fp.readline().strip())

        KB(sentences, queries)
