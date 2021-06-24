package org.semanticweb.rulewerk.reasoner.vlog;

/*-
 * #%L
 * Rulewerk VLog Reasoner Support
 * %%
 * Copyright (C) 2018 - 2020 Rulewerk Developers
 * %%
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 * #L%
 */

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Formatter;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.semanticweb.rulewerk.core.exceptions.RulewerkRuntimeException;
import org.semanticweb.rulewerk.core.model.api.DataSource;
import org.semanticweb.rulewerk.core.model.api.DataSourceDeclaration;
import org.semanticweb.rulewerk.core.model.api.Fact;
import org.semanticweb.rulewerk.core.model.api.Literal;
import org.semanticweb.rulewerk.core.model.api.PositiveLiteral;
import org.semanticweb.rulewerk.core.model.api.Predicate;
import org.semanticweb.rulewerk.core.model.api.Rule;
import org.semanticweb.rulewerk.core.model.api.Statement;
import org.semanticweb.rulewerk.core.model.api.StatementVisitor;
import org.semanticweb.rulewerk.core.model.api.Term;
import org.semanticweb.rulewerk.core.model.implementation.ConjunctionImpl;
import org.semanticweb.rulewerk.core.model.implementation.PositiveLiteralImpl;
import org.semanticweb.rulewerk.core.model.implementation.PredicateImpl;
import org.semanticweb.rulewerk.core.model.implementation.RuleImpl;
import org.semanticweb.rulewerk.core.model.implementation.UniversalVariableImpl;
import org.semanticweb.rulewerk.core.reasoner.KnowledgeBase;
import org.semanticweb.rulewerk.core.reasoner.implementation.ReasonerDataSource;

/**
 * Class for organizing a Knowledge Base using vLog-specific data structures.
 *
 * @author Irina Dragoste
 *
 */
public class VLogKnowledgeBase {

	private final Map<Predicate, DataSourceDeclaration> edbPredicates = new HashMap<>();
	private final Map<DataSourceDeclaration, Predicate> aliasesForEdbPredicates = new HashMap<>();

	private final Set<Predicate> aliasedEdbPredicates = new HashSet<>();

	private final Set<Predicate> idbPredicates = new HashSet<>();

	private final Map<Predicate, List<Fact>> directEdbFacts = new HashMap<>();

	private final List<Rule> rules = new ArrayList<>();

	/**
	 * Package-protected constructor, that organizes given {@code knowledgeBase} in
	 * vLog-specific data structures.
	 *
	 * @param knowledgeBase
	 */
	VLogKnowledgeBase(final KnowledgeBase knowledgeBase) {
		final LoadKbVisitor visitor = this.new LoadKbVisitor();
		visitor.clearIndexes();
		for (final Statement statement : knowledgeBase) {
			statement.accept(visitor);
		}
	}

	boolean hasData() {
		return !this.edbPredicates.isEmpty() || !this.aliasedEdbPredicates.isEmpty();
	}

	public boolean hasRules() {
		return !this.rules.isEmpty();
	}

	Predicate getAlias(final Predicate predicate) {
		if (this.edbPredicates.containsKey(predicate)) {
			return predicate;
		} else {
			return this.aliasesForEdbPredicates.get(new LocalFactsDataSourceDeclaration(predicate));
		}
	}

	String getVLogDataSourcesConfigurationString() {
		final StringBuilder configStringBuilder = new StringBuilder();
		final Formatter formatter = new Formatter(configStringBuilder);
		int dataSourceIndex = 0;

		for (final Entry<Predicate, DataSourceDeclaration> e : this.edbPredicates.entrySet()) {
			dataSourceIndex = addDataSourceConfigurationString(e.getValue().getDataSource(), e.getKey(),
					dataSourceIndex, formatter);
		}

		for (final Entry<DataSourceDeclaration, Predicate> e : this.aliasesForEdbPredicates.entrySet()) {
			dataSourceIndex = addDataSourceConfigurationString(e.getKey().getDataSource(), e.getValue(),
					dataSourceIndex, formatter);
		}

		formatter.close();
		return configStringBuilder.toString();
	}

	int addDataSourceConfigurationString(final DataSource dataSource, final Predicate predicate,
			final int dataSourceIndex, final Formatter formatter) {
		int newDataSourceIndex = dataSourceIndex;

		if (dataSource != null) {
			if (dataSource instanceof ReasonerDataSource) {
				final ReasonerDataSource reasonerDataSource = (ReasonerDataSource) dataSource;
				final VLogDataSourceConfigurationVisitor visitor = new VLogDataSourceConfigurationVisitor();
				try {
					reasonerDataSource.accept(visitor);
				} catch (IOException e) {
					throw new RulewerkRuntimeException("Error while building VLog data source configuration", e);
				}
				final String configString = visitor.getConfigString();
				if (configString != null) {
					formatter.format(configString, dataSourceIndex, ModelToVLogConverter.toVLogPredicate(predicate));
					newDataSourceIndex++;
				}
			}
		}

		return newDataSourceIndex;
	}

	Map<Predicate, DataSourceDeclaration> getEdbPredicates() {
		return this.edbPredicates;
	}

	Map<DataSourceDeclaration, Predicate> getAliasesForEdbPredicates() {
		return this.aliasesForEdbPredicates;
	}

	Map<Predicate, List<Fact>> getDirectEdbFacts() {
		return this.directEdbFacts;
	}

	List<Rule> getRules() {
		return this.rules;
	}

	/**
	 * Local visitor implementation for processing statements upon loading. Internal
	 * index structures are updated based on the statements that are detected.
	 *
	 * @author Markus Kroetzsch
	 */

	class LoadKbVisitor implements StatementVisitor<Void> {

		public void clearIndexes() {
			VLogKnowledgeBase.this.edbPredicates.clear();
			VLogKnowledgeBase.this.idbPredicates.clear();
			VLogKnowledgeBase.this.aliasedEdbPredicates.clear();
			VLogKnowledgeBase.this.aliasesForEdbPredicates.clear();
			VLogKnowledgeBase.this.directEdbFacts.clear();
			VLogKnowledgeBase.this.rules.clear();
		}

		@Override
		public Void visit(final Fact fact) {
			final Predicate predicate = fact.getPredicate();
			registerEdbDeclaration(new LocalFactsDataSourceDeclaration(predicate));
			if (!VLogKnowledgeBase.this.directEdbFacts.containsKey(predicate)) {
				final List<Fact> facts = new ArrayList<>();
				facts.add(fact);
				VLogKnowledgeBase.this.directEdbFacts.put(predicate, facts);
			} else {
				VLogKnowledgeBase.this.directEdbFacts.get(predicate).add(fact);
			}
			return null;
		}

		@Override
		public Void visit(final Rule statement) {
			VLogKnowledgeBase.this.rules.add(statement);
			for (final PositiveLiteral positiveLiteral : statement.getHead()) {
				final Predicate predicate = positiveLiteral.getPredicate();
				if (!VLogKnowledgeBase.this.idbPredicates.contains(predicate)) {
					if (VLogKnowledgeBase.this.edbPredicates.containsKey(predicate)) {
						addEdbAlias(VLogKnowledgeBase.this.edbPredicates.get(predicate));
						VLogKnowledgeBase.this.edbPredicates.remove(predicate);
					}
					VLogKnowledgeBase.this.idbPredicates.add(predicate);
				}
			}
			return null;
		}

		@Override
		public Void visit(final DataSourceDeclaration statement) {
			registerEdbDeclaration(statement);
			return null;
		}

		void registerEdbDeclaration(final DataSourceDeclaration dataSourceDeclaration) {
			final Predicate predicate = dataSourceDeclaration.getPredicate();
			if (VLogKnowledgeBase.this.idbPredicates.contains(predicate)
					|| VLogKnowledgeBase.this.aliasedEdbPredicates.contains(predicate)) {
				if (!VLogKnowledgeBase.this.aliasesForEdbPredicates.containsKey(dataSourceDeclaration)) {
					addEdbAlias(dataSourceDeclaration);
				}
			} else {
				final DataSourceDeclaration currentMainDeclaration = VLogKnowledgeBase.this.edbPredicates
						.get(predicate);
				if (currentMainDeclaration == null) {
					VLogKnowledgeBase.this.edbPredicates.put(predicate, dataSourceDeclaration);
				} else if (!currentMainDeclaration.equals(dataSourceDeclaration)) {
					addEdbAlias(currentMainDeclaration);
					addEdbAlias(dataSourceDeclaration);
					VLogKnowledgeBase.this.edbPredicates.remove(predicate);
				} // else: predicate already known to have local facts (only)
			}
		}

		void addEdbAlias(final DataSourceDeclaration dataSourceDeclaration) {
			final Predicate predicate = dataSourceDeclaration.getPredicate();
			Predicate aliasPredicate;
			if (dataSourceDeclaration instanceof LocalFactsDataSourceDeclaration) {
				aliasPredicate = new PredicateImpl(predicate.getName() + "##FACT", predicate.getArity());
			} else {
				aliasPredicate = new PredicateImpl(predicate.getName() + "##" + dataSourceDeclaration.hashCode(),
						predicate.getArity());
			}
			VLogKnowledgeBase.this.aliasesForEdbPredicates.put(dataSourceDeclaration, aliasPredicate);
			VLogKnowledgeBase.this.aliasedEdbPredicates.add(predicate);

			final List<Term> terms = new ArrayList<>();
			for (int i = 1; i <= predicate.getArity(); i++) {
				terms.add(new UniversalVariableImpl("X" + i));
			}
			final Literal body = new PositiveLiteralImpl(aliasPredicate, terms);
			final PositiveLiteral head = new PositiveLiteralImpl(predicate, terms);
			final Rule rule = new RuleImpl(new ConjunctionImpl<>(Arrays.asList(head)),
					new ConjunctionImpl<>(Arrays.asList(body)));
			VLogKnowledgeBase.this.rules.add(rule);
		}

	}

	/**
	 * Dummy data source declaration for predicates for which we have explicit local
	 * facts in the input.
	 *
	 * @author Markus Kroetzsch
	 *
	 */
	class LocalFactsDataSourceDeclaration implements DataSourceDeclaration {

		final Predicate predicate;

		public LocalFactsDataSourceDeclaration(Predicate predicate) {
			this.predicate = predicate;
		}

		@Override
		public <T> T accept(StatementVisitor<T> statementVisitor) {
			return statementVisitor.visit(this);
		}

		@Override
		public Predicate getPredicate() {
			return this.predicate;
		}

		@Override
		public DataSource getDataSource() {
			return null;
		}

		@Override
		public int hashCode() {
			return this.predicate.hashCode();
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			final LocalFactsDataSourceDeclaration other = (LocalFactsDataSourceDeclaration) obj;
			return this.predicate.equals(other.predicate);
		}
	}
}
