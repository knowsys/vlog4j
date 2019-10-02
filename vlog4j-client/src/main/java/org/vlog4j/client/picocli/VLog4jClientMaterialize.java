package org.vlog4j.client.picocli;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.semanticweb.vlog4j.core.model.api.PositiveLiteral;
import org.semanticweb.vlog4j.core.reasoner.Algorithm;
import org.semanticweb.vlog4j.core.reasoner.KnowledgeBase;
import org.semanticweb.vlog4j.core.reasoner.LogLevel;
import org.semanticweb.vlog4j.core.reasoner.Reasoner;
import org.semanticweb.vlog4j.core.reasoner.implementation.VLogReasoner;
import org.semanticweb.vlog4j.examples.ExamplesUtils;
import org.semanticweb.vlog4j.parser.ParsingException;
import org.semanticweb.vlog4j.parser.RuleParser;

import picocli.CommandLine.ArgGroup;
import picocli.CommandLine.Command;
import picocli.CommandLine.Option;

@Command(name = "materialize", description = "Execute the chase and store the literal's extensions")
public class VLog4jClientMaterialize implements Runnable {

	// TODO add link to rls syntax
	@Option(names = "--rule-file", description = "Rule file(s) in rls syntax", required = true)
	private List<String> ruleFiles = new ArrayList<>();

//  TODO
//	Support graal rule files
//	@Option(names = "--graal-rule-file", description = "Rule file(s) in graal syntax", required = true)
//	private List<String> graalRuleFiles = new ArrayList<>();

	@Option(names = "--log-level", description = "Log level of VLog (c++ library). One of: DEBUG, INFO, WARNING (default), ERROR.", required = false)
	private LogLevel logLevel = LogLevel.WARNING;

	@Option(names = "--log-file", description = "Log file of VLog (c++ library). VLog will log to the default system output by default", required = false)
	private String logFile;

	@Option(names = "--chase-algorithm", description = "Chase algorithm. RESTRICTED_CHASE (default) or SKOLEM_CHASE.", required = false)
	private Algorithm chaseAlgorithm = Algorithm.RESTRICTED_CHASE;

	@Option(names = "--timeout", description = "Timeout in seconds. Infinite by default", required = false)
	private int timeout = 0;

	@Option(names = "--query", description = "Positive not-ground Literals to query after materialization in rls syntax. Vlog4jClient will print the size of its extension", required = true)
	private List<String> queryStrings = new ArrayList<>();

	@ArgGroup(exclusive = false)
	private PrintQueryResults printQueryResults = new PrintQueryResults();

	@ArgGroup(exclusive = false)
	private SaveQueryResults saveQueryResults = new SaveQueryResults();

	// TODO save model
	// @ArgGroup(exclusive = false)
	// private SaveModel saveModel = new SaveModel();

	@Override
	public void run() {
		ExamplesUtils.configureLogging();

		if (!printQueryResults.isConfigOk()) {
			printQueryResults.printErrorAndExit();
		}

		if (!saveQueryResults.isConfigOk()) {
			saveQueryResults.printErrorAndExit();
		}

		// TODO
		// if (!saveModel.isConfigOk()) {
		// saveModel.printErrorAndExit();
		// }

		System.out.println("Configuration:");

		/* Configure rules */
		final KnowledgeBase kb = new KnowledgeBase();
		for (String ruleFile : ruleFiles) {
			try {
				RuleParser.parseInto(kb, new FileInputStream(ruleFile));
				System.out.println("  --rule-file: " + ruleFile);
			} catch (FileNotFoundException e) {
				System.out.println("File not found: " + ruleFile + ". " + e.getMessage());
				System.exit(1);
			} catch (ParsingException e) {
				System.out.println("Failed to parse rule file: " + ruleFile + ". " + e.getMessage());
				System.exit(1);
			}
		}

		/* Configure queries (We throw parsing query errors before materialization) */
		List<PositiveLiteral> queries = new ArrayList<>();
		for (String queryString : queryStrings) {
			try {
				queries.add(RuleParser.parsePositiveLiteral(queryString));
				System.out.println("  --query: " + queries.get(queries.size() - 1));
			} catch (ParsingException e) {
				System.out.println("Failed to parse query: " + queryString + ". " + e.getMessage());
				System.exit(1);
			}
		}

		/* Print configuration */
		System.out.println("  --log-file: " + logFile);
		System.out.println("  --log-level: " + logLevel);
		System.out.println("  --chase-algorithm: " + chaseAlgorithm);
		System.out.println("  --timeout: " + ((timeout > 0) ? Integer.toString(timeout) : "none"));

		/* Print what to do with the result */

		printQueryResults.printConfiguration();
		saveQueryResults.printConfiguration();
		// saveModel.printConfiguration();

		try (Reasoner reasoner = new VLogReasoner(kb)) {
			// logFile
			reasoner.setLogFile(logFile);
			// logLevel
			reasoner.setLogLevel(logLevel);
			// chaseAlgorithm
			reasoner.setAlgorithm(chaseAlgorithm);
			// timeout
			if (timeout > 0) {
				reasoner.setReasoningTimeout(timeout);
			}

			try {
				System.out.println("Executing the chase ...");
				reasoner.reason();
			} catch (IOException e) {
				System.out.println("Something went wrong. Please check the log file.");
				System.exit(1);
			}

			// TODO save the model
			// if (saveModel.saveModel) {
			// System.out.println("Saving model ...");
			// }

			String outputPath;
			if (queries.size() > 0) {
				System.out.println("Answering queries ...");
				for (PositiveLiteral query : queries) {
					if (saveQueryResults.saveResults) {
						try {
							outputPath = saveQueryResults.outputQueryResultDirectory + "/" + query + ".csv";
							reasoner.exportQueryAnswersToCsv(query, outputPath, true);
						} catch (IOException e) {
							System.out.println("Can't save query " + query);
							System.exit(1);
						}
					}
					if (printQueryResults.sizeOnly) {
						System.out.println(
								"Elements in " + query + ": " + ExamplesUtils.getQueryAnswerCount(query, reasoner));
					} else if (printQueryResults.complete) {
						ExamplesUtils.printOutQueryAnswers(query, reasoner);
					}
				}
			}
		}
		System.out.println("Process completed.");
	}
}
