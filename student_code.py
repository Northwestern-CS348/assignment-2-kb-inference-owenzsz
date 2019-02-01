import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        ####################################################
        # Student code goes here
        if isinstance(fact_or_rule, Fact) and fact_or_rule in self.facts:
            real_fact = self._get_fact(fact_or_rule)
            self.remove_helper(real_fact)
        

    def remove_helper(self, fact_or_rule):
        #check supported_by first, ask can we remove this?
        #if it has things in support, check if asserted, set it to false, after the if loop return
        #check if this a fact and if it's in facts
        #chekc first if there are things in supports_facts
            #for each fact in sup_facts, look at fact_rule pairs, if the fact in the supported by is the fact we are removing, remove the supported fact
            #now if that dependent has empty supported_by and not asserted, call remove

        if len(fact_or_rule.supported_by) != 0:
            if fact_or_rule.asserted:
                fact_or_rule.asserted = False
            return
        # remove that fact from self.facts
        if isinstance(fact_or_rule, Fact) and fact_or_rule in self.facts:
            if len(fact_or_rule.supported_by) != 0:
                for sup_pairs in fact_or_rule.supported_by:
                    sup_pairs[0].supports_facts.remove(fact_or_rule)
                    sup_pairs[1].supports_facts.remove(fact_or_rule)
            if len(fact_or_rule.supports_facts)!=0:
                for supported_fact in fact_or_rule.supports_facts:
                    for pairs in supported_fact.supported_by:
                        # pairs[0] -> fact
                        if pairs[0] == fact_or_rule:
                            supported_fact.supported_by.remove(pairs)
                    if len(supported_fact.supported_by) == 0 and not supported_fact.asserted:
                        self.remove_helper(supported_fact)
            if len(fact_or_rule.supports_rules) != 0:
                for supported_rule in fact_or_rule.supports_rules:
                    for pairs in supported_rule.supported_by:
                        if pairs[0] == fact_or_rule:
                            supported_rule.supported_by.remove(pairs)
                    if len(supported_rule.supported_by)==0 and not supported_rule.asserted:
                        self.remove_helper(supported_rule)
            self.facts.remove(fact_or_rule)
        # do the same thing for rules
        elif isinstance(fact_or_rule, Rule) and fact_or_rule in self.rules:
            if len(fact_or_rule.supported_by) != 0:
                for sup_pairs in fact_or_rule.supported_by:
                    sup_pairs[0].supports_rules.remove(fact_or_rule)
                    sup_pairs[1].supports_rules.remove(fact_or_rule)
            if len(fact_or_rule.supports_facts)!=0:
                for supported_fact in fact_or_rule.supports_facts:
                    for pairs in supported_fact.supported_by:
                        if pairs[1] == fact_or_rule:
                            supported_fact.supported_by.remove(pairs)
                    if len(supported_fact.supported_by)==0 and not supported_fact.asserted:
                        self.remove_helper(supported_fact)
            if len(fact_or_rule.supports_rules)!=0:
                for supported_rule in fact_or_rule.supports_rules:
                    for pairs in supported_rule.supported_by:
                        if pairs[1] == fact_or_rule:
                            supported_rule.supported_by.remove(pairs)
                    if len(supported_rule.supported_by)==0 and not supported_rule.asserted:
                        self.remove_helper(supported_rule)
            self.rules.remove(fact_or_rule)



class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here
        # if there is only one thing on lhs, create a new fact from the bindings created from lhs and fact

        if match(fact.statement, rule.lhs[0]):
            fact_bindings = match(fact.statement, rule.lhs[0])
            if len(rule.lhs) == 1:
                f_statement = instantiate(rule.rhs, fact_bindings)
                new_fact = Fact(f_statement, supported_by=[[fact, rule]])
                #add the fact to the support list of fact and rule
                fact.supports_facts.append(new_fact)
                rule.supports_facts.append(new_fact)
                #add the new fact to the database
                kb.kb_add(new_fact)
        # if there are multiple things on lhs, iterate through the list and create rules out of that
            else:
                left_statements = []
                for left in rule.lhs[1:]:
                    lhs_statement = instantiate(left, fact_bindings)
                    left_statements.append(lhs_statement)
                new_rule = Rule([left_statements, instantiate(rule.rhs, fact_bindings)], supported_by = [[fact, rule]])
                fact.supports_rules.append(new_rule)
                rule.supports_rules.append(new_rule)
                kb.kb_add(new_rule)

