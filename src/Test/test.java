package Test;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.deri.iris.Configuration;
import org.deri.iris.KnowledgeBaseFactory;
import org.deri.iris.api.IKnowledgeBase;
import org.deri.iris.api.basics.IPredicate;
import org.deri.iris.api.basics.IQuery;
import org.deri.iris.api.basics.IRule;
import org.deri.iris.api.basics.ITuple;
import org.deri.iris.api.terms.IVariable;
import org.deri.iris.compiler.Parser;
import org.deri.iris.compiler.ParserException;
import org.deri.iris.storage.IRelation;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;

//man('homer').
//isMale(?x) :- man(?x). from  right to left
public class test {

	/** The new line separator to use when formatting output. */
	public static final String NEW_LINE = System.getProperty("line.separator");

	/** Output helper. */
	public static final String BAR = "----------------------------------";

	/** Flag for how to format the output. */
	public static final boolean SHOW_VARIABLE_BINDINGS = true;

	/** Flag for how to format the output. */
	public static final boolean SHOW_QUERY_TIME = true;

	/** Flag for how to format the output. */
	public static final boolean SHOW_ROW_COUNT = true;

	public static final String default_rules1 = "inst(?x,?x) :- nom(?x). \n";
	public static final String default_rules2 = "self(?x,?v) :- nom(?x),triple(?x,?v,?x). \n";
	public static final String default_rules3 = "inst(?x,?z) :- top(?z),inst(?x,?z). \n";
	public static final String default_rules4 = "inst(?x,?y) :- bot(?z),inst(?u,?z),inst(?x,?r),cls(?y). \n";
	public static final String default_rules5 = "inst(?x,?z) :- subClass(?y,?z),inst(?x,?y). \n";
	public static final String default_rules6 = "inst(?x,?z) :- subConj(?y1,?y2,?z),inst(?x,?y1),inst(?x,?y2). \n";
	public static final String default_rules7 = "inst(?x,?z) :- subEx(?v,?y,?z),self(?x,?v),inst(?x,?y). \n";
	public static final String default_rules8 = "inst(?x,?z) :- subEx(?v,?y,?z),triple(?x,?v,?x2),inst(?x2,?y). \n";
	public static final String default_rules9 = "inst(?x2,?z) :- supEx(?y,?v,?z,?x2), inst(?x,?y). \n";
	public static final String default_rules10 = "triple(?x,?v,?x2) :- supEx(?y,?v,?z,?x2), inst(?x,?y). \n";
	public static final String default_rules11 = "inst(?x,?z) :- subSelf(?v,?z),self(?x,?v). \n";
	public static final String default_rules12 = "self(?x,?v) :- supSelf(?y,?v),inst(?x,?y). \n";
	public static final String default_rules13 = "triple(?x,?w,?x2) :- subRole(?v,?w),triple(?x,?v,?x2). \n";
	public static final String default_rules14 = "self(?x,?w) :- subRole(?v,?w),self(?x,?v). \n";
	public static final String default_rules15 = "triple(?x,?w,?x2) :- subRChain(?u,?v,?w),triple(?x,?u,?x1),triple(?x1,?v,?x2).\n";
	public static final String default_rules16 = "triple(?x,?w,?x1) :- subRChain(?u,?v,?w),self(?x,?u),triple(?x,?v,?x1).\n";
	public static final String default_rules17 = "triple(?x,?w,?x1) :- subRChain(?u,?v,?w),triple(?x,?u,?x1),self(?x1,?v).  \n";
	public static final String default_rules18 = "triple(?x,?w,?x) :- subRChain(?u,?v,?w),self(?x,?u),self(?x,?v).\n";
	public static final String default_rules19 = "triple(?x,?w,?x1) :- subRConj(?v1,?v2,?w),triple(?x,?v1,?x1),triple(?x,?v2, ?x1).\n";
	public static final String default_rules20 = "self(?x,?w) :- subRConj(?v1,?v2,?w),self(?x,?v1),self(?x,?v2).\n";
	public static final String default_rules21 = "triple(?x,?w,?x1) :- subProd(?y1,?y2,?w),inst(?x,?y1),inst(?x1,?y2).\n";
	public static final String default_rules22 = "self(?x,?w) :- subProd(?y1,?y2,?w),inst(?x,?y1),inst(?x,?y2).\n";
	public static final String default_rules23 = "inst(?x,?z1) :- supProd(?v,?z1,?z2),triple(?x,?v,?x2).\n";
	public static final String default_rules24 = "inst(?x,?z1) :-  supProd(?v,?z1,?z2),self(?x,?v).\n";
	public static final String default_rules25 = "inst(?x1,?z2) :- supProd(?v,?z1,?z2),triple(?x,?v,?x1).\n";
	public static final String default_rules26 = "inst(?x,?z2) :- supProd(?v,?z1,?z2),self(?x, ?v).\n";
	public static final String default_rules27 = "inst(?y,?z) :- inst(?x,?y),nom(?y),inst(?x,?z).\n";
	public static final String default_rules28 = "inst(?x,?z) :- inst(?x,?y),nom(?y),inst(?y,?z).\n";
	public static final String default_rules29 = "triple(?z,?u,?y) :- inst(?x,?y),nom(?y),triple(?z,?u,?x).\n";
	public static final String default_rules30 = "triple(?x,?y,?x) :- self(?x,?y).\n";

	public static final String query_triple = "?-triple(?x,?y,?z) .";
	public static final String query_inst = "?-inst(?x,?y) .";
	public static final String query_nom = "?-nom(?x) .";

	// \exists prop1.{v1} \sqcap \exists prop2.{v1} \sqcap \exists prop3.{v2}
	// \sqcap \exists prop4.{v2} \sqsubseteq Class1
	public static final String ns_rules_1 = " inst(?x,'test_concept') :- nom(?v1), triple(?x,'<start_stage>',?v1).";
	public static final String ns_rules_2 = " inst(?x,'test_concept') :- nom(?v1), triple(?x,'<start_stage>',?v1),nom(?v2),triple(?x,'<end_stage>',?v2).";
	public static final String ns_rules_3 = " inst(?x,'test_concept') :- nom(?v1), triple(?x,'<start_stage>',?v1),nom(?v2),triple(?x,'<end_stage>',?v2),nom(?v3),triple(?x,'<preceded_by>',?v3).";
	public static final String ns_rules_4 = " inst(?x,'test_concept') :- nom(?v1), triple(?x,'<start_stage>',?v1),nom(?v2),triple(?x,'<end_stage>',?v2),nom(?v3),triple(?x,'<preceded_by>',?v3),nom(?v4),triple(?x,'<develops_from>',?v4).";
	public static final String ns_rules_5 = " inst(?x,'test_concept') :- nom(?v1), triple(?x,'<start_stage>',?v1),nom(?v2),triple(?x,'<end_stage>',?v2),nom(?v3),triple(?x,'<preceded_by>',?v3),nom(?v4),triple(?x,'<develops_from>',?v4),nom(?v5),triple(?x,'<part_of>',?v5).";

	/**
	 * public static final String ns_rules_1 =
	 * " inst(?x,'test_concept') :- nom(?v1), triple(?x,'<has_axis>',?v1).";
	 * public static final String ns_rules_2 =
	 * " inst(?x,'test_concept') :- nom(?v1), triple(?x,'<has_axis>',?v1),nom(?v2),triple(?x,'<opposite_to>',?v2)."
	 * ; public static final String ns_rules_3 =
	 * " inst(?x,'test_concept') :- nom(?v1), triple(?x,'<has_axis>',?v1),nom(?v2),triple(?x,'<opposite_to>',?v2),nom(?v3),triple(?x,'<BSPO_0000103>',?v3)."
	 * ; public static final String ns_rules_4 =
	 * " inst(?x,'test_concept') :- nom(?v1), triple(?x,'<has_axis>',?v1),nom(?v2),triple(?x,'<opposite_to>',?v2),nom(?v3),triple(?x,'<BSPO_0000103>',?v3),nom(?v4),triple(?x,'<BSPO_0000097>',?v4)."
	 * ; public static final String ns_rules_5 =
	 * " inst(?x,'test_concept') :- nom(?v1), triple(?x,'<has_axis>',?v1),nom(?v2),triple(?x,'<opposite_to>',?v2),nom(?v3),triple(?x,'<BSPO_0000103>',?v3),nom(?v4),triple(?x,'<BSPO_0000097>',?v4),nom(?v5),triple(?x,'<BSPO_0000098>',?v5)."
	 * ;
	 */

	public static final String query = query_inst + query_triple + query_nom;

	public static final String default_rules_ns = default_rules1
			+ default_rules2 + default_rules3 + default_rules4 + default_rules5
			+ default_rules6 + default_rules7 + default_rules8 + default_rules9
			+ default_rules10 + default_rules11 + default_rules12
			+ default_rules13 + default_rules14 + default_rules15
			+ default_rules16 + default_rules17 + default_rules18
			+ default_rules19 + default_rules20 + default_rules21
			+ default_rules22 + default_rules23 + default_rules24
			+ default_rules25 + default_rules26 + default_rules27
			+ default_rules28 + default_rules29 + default_rules30 + query
			+ ns_rules_5;

	public static final String default_rules = default_rules1 + default_rules2
			+ default_rules3 + default_rules4 + default_rules5 + default_rules6
			+ default_rules7 + default_rules8 + default_rules9
			+ default_rules10 + default_rules11 + default_rules12
			+ default_rules13 + default_rules14 + default_rules15
			+ default_rules16 + default_rules17 + default_rules18
			+ default_rules19 + default_rules20 + default_rules21
			+ default_rules22 + default_rules23 + default_rules24
			+ default_rules25 + default_rules26 + default_rules27
			+ default_rules28 + default_rules29 + default_rules30 + query;

	public static String rules;

	protected final OWLOntology m_rootOntology;
	protected final OWLAxioms m_axioms;
	protected final OWLDataFactory factory;

	public long time;

	public void FullGrounding1(String ns_rule) {
		String newrule = "";
		for (OWLIndividual e : m_axioms.m_namedIndividuals) {
			newrule = ns_rule.replace("?v1", "'"+e.toString()+"'");
			m_axioms.m_datalog_rules.add(newrule);
			//System.out.println(newrule);
		}
	}

	public void FullGrounding2(String ns_rule) {
		String newrule = "";
		for (OWLIndividual e1 : m_axioms.m_namedIndividuals) {
			newrule = ns_rule.replace("?v1", "'"+e1.toString()+"'");
			for (OWLIndividual e2 : m_axioms.m_namedIndividuals) {
				newrule = ns_rule.replace("?v2", "'"+e2.toString()+"'");
				m_axioms.m_datalog_rules.add(newrule);
			}
		}
	}

	public void FullGrounding3(String ns_rule) {
		String newrule = "";
		for (OWLIndividual e1 : m_axioms.m_namedIndividuals) {
			newrule = ns_rule.replace("?v1", "'"+e1.toString()+"'");
			for (OWLIndividual e2 : m_axioms.m_namedIndividuals) {
				newrule = ns_rule.replace("?v2", "'"+e2.toString()+"'");
				for (OWLIndividual e3 : m_axioms.m_namedIndividuals) {
					newrule = ns_rule.replace("?v3", "'"+e3.toString()+"'");
					m_axioms.m_datalog_rules.add(newrule);
				}
			}
		}
	}

	public void FullGrounding4(String ns_rule) {
		String newrule = "";
		for (OWLIndividual e1 : m_axioms.m_namedIndividuals) {
			newrule = ns_rule.replace("?v1", "'"+e1.toString()+"'");
			for (OWLIndividual e2 : m_axioms.m_namedIndividuals) {
				newrule = ns_rule.replace("?v2", "'"+e2.toString()+"'");
				for (OWLIndividual e3 : m_axioms.m_namedIndividuals) {
					newrule = ns_rule.replace("?v3", "'"+e3.toString()+"'");
					for (OWLIndividual e4 : m_axioms.m_namedIndividuals) {
						newrule = ns_rule.replace("?v4", "'"+e4.toString()+"'");
						m_axioms.m_datalog_rules.add(newrule);
					}
				}
			}
		}
	}

	public void FullGrounding5(String ns_rule) {
		String newrule = "";
		for (OWLIndividual e1 : m_axioms.m_namedIndividuals) {
			newrule = ns_rule.replace("?v1", "'"+e1.toString()+"'");
			for (OWLIndividual e2 : m_axioms.m_namedIndividuals) {
				newrule = ns_rule.replace("?v2", "'"+e2.toString()+"'");
				for (OWLIndividual e3 : m_axioms.m_namedIndividuals) {
					newrule = ns_rule.replace("?v3", "'"+e3.toString()+"'");
					for (OWLIndividual e4 : m_axioms.m_namedIndividuals) {
						newrule = ns_rule.replace("?v4", "'"+e4.toString()+"'");
						for (OWLIndividual e5 : m_axioms.m_namedIndividuals) {
							newrule = ns_rule.replace("?v5", "'"+e5.toString()+"'");
							m_axioms.m_datalog_rules.add(newrule);
						}
					}
				}
			}
		}
	}

	public test(OWLOntology rootOntology, String namespace, int size, int size2)
			throws Exception {
		rules = getRules();
		m_rootOntology = rootOntology;
		m_axioms = new OWLAxioms();
		factory = m_rootOntology.getOWLOntologyManager().getOWLDataFactory();
		Normalization normalization = new Normalization(factory, m_axioms);
		normalization.randomAssignIndividuals(m_rootOntology, size, size2);
		normalization.processOntology(m_rootOntology);
		Translator trans = new Translator(factory, m_axioms);
		trans.translateKB();
		String KB_rules = "";
		
		//FullGrounding();
		for (String s : m_axioms.m_datalog_rules) {
			KB_rules += s.replace(namespace, "") + "\n";
		}
		//System.out.println(m_axioms.m_datalog_rules.size());
		// System.out.println(KB_rules);

		this.ProgramExecutor(default_rules + KB_rules);
	}
	
	public test(OWLOntology rootOntology, String namespace, int size, int size2, boolean b1, boolean b2)
			throws Exception {
		rules = getRules();
		m_rootOntology = rootOntology;
		m_axioms = new OWLAxioms();
		factory = m_rootOntology.getOWLOntologyManager().getOWLDataFactory();
		Normalization normalization = new Normalization(factory, m_axioms);
		normalization.randomAssignIndividuals(m_rootOntology, size, size2);
		normalization.processOntology(m_rootOntology);
		Translator trans = new Translator(factory, m_axioms);
		trans.translateKB();
		String KB_rules = "";
		
		FullGrounding2(ns_rules_2);
		for (String s : m_axioms.m_datalog_rules) {
			KB_rules += s.replace(namespace, "") + "\n";
		}
		System.out.println(m_axioms.m_datalog_rules.size());
		this.ProgramExecutor(default_rules + KB_rules);
	}

	public String getRules() {
		rules += this.default_rules + this.query;
		return rules;
	}

	public test(OWLOntology rootOntology, String namespace, int size,
			int size2, boolean b) throws Exception {
		m_rootOntology = rootOntology;
		m_axioms = new OWLAxioms();
		factory = m_rootOntology.getOWLOntologyManager().getOWLDataFactory();
		Normalization normalization = new Normalization(factory, m_axioms);
		normalization.randomAssignIndividuals(m_rootOntology, size, size2);
		normalization.processOntology(m_rootOntology);
		Translator trans = new Translator(factory, m_axioms);
		trans.translateKB();
		String KB_rules = "";
		for (String s : m_axioms.m_datalog_rules) {
			KB_rules += s.replace(namespace, "") + "\n";
		}
		System.out.println(m_axioms.m_datalog_rules.size());
		// System.out.println(KB_rules);

		this.ProgramExecutor(default_rules_ns + KB_rules);
	}

	public String getDefaultRules() {
		String KB_rules = "";
		for (String s : m_axioms.m_datalog_rules) {
			System.out.println(s);
			KB_rules += s + "\n";
		}
		return KB_rules + "\n" + default_rules;
	}

	public void ProgramExecutor(String program) throws Exception {

		Parser parser = new Parser();

		parser.parse(program);

		Map<IPredicate, IRelation> facts = parser.getFacts();
		List<IRule> rules = parser.getRules();
		Configuration config = KnowledgeBaseFactory.getDefaultConfiguration();

		StringBuilder output = new StringBuilder();

		long duration = -System.currentTimeMillis();
		IKnowledgeBase knowledgeBase = KnowledgeBaseFactory
				.createKnowledgeBase(facts, rules, config);
		duration += System.currentTimeMillis();

		output.append("Init time: ").append(duration).append("ms")
				.append(System.getProperty("line.separator"));

		List<IVariable> variableBindings = new ArrayList<IVariable>();

		for (IQuery query : parser.getQueries()) {
			// Execute the query
			duration = -System.currentTimeMillis();
			IRelation results = knowledgeBase.execute(query, variableBindings);
			duration += System.currentTimeMillis();

			output.append(BAR).append(NEW_LINE);
			output.append("Query:      ").append(query);
			if (SHOW_ROW_COUNT) {
				output.append(" ==>> ").append(results.size());
				if (results.size() == 1)
					output.append(" row");
				else
					output.append(" rows");
			}
			if (SHOW_QUERY_TIME)
				output.append(" in ").append(duration).append("ms");

			output.append(NEW_LINE);

			if (SHOW_VARIABLE_BINDINGS) {
				output.append("Variables:  ");
				boolean first = true;
				for (IVariable variable : variableBindings) {
					if (first)
						first = false;
					else
						output.append(", ");
					output.append(variable);
				}
				output.append(NEW_LINE);
			}

			formatResults(output, results);
		}

		time = duration;
		mOutput = output.toString();

	}

	public String getOutput() {
		return mOutput;
	}

	/**
	 * Format the actual query results (tuples).
	 * 
	 * @param builder
	 * @param m
	 */
	private void formatResults(StringBuilder builder, IRelation m) {
		for (int t = 0; t < m.size(); ++t) {
			ITuple tuple = m.get(t);
			builder.append(tuple.toString()).append(NEW_LINE);
		}
	}

	/** The output (or error) from the program execution. */
	private String mOutput;

	public static void main(String[] args) throws Exception {
		/**
		 * String pathFile = new String("TEST_ONTOLOGIES/"); File dir = new
		 * File(pathFile); String[] ontologyNames = dir.list(); int size =
		 * 10000; int size2 = 10000; for (int i = 0; i < ontologyNames.length;
		 * i++) { File file = new File(pathFile + ontologyNames[i]);
		 * OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		 * OWLOntology m_rootOntology = manager
		 * .loadOntologyFromOntologyDocument(file); String namespace =
		 * "http://www.geneontology.org/go#"; test r = new test(m_rootOntology,
		 * namespace, size, size2/2); //test r = new
		 * test(m_rootOntology,namespace,size,size2,true);
		 * //System.out.println(r.getOutput()); OutputStream fos = new
		 * FileOutputStream(new File(ontologyNames[i] + "_" + size +
		 * "_output.txt")); fos.write(r.getOutput().getBytes()); }
		 */

		File file = new File("TEST_ONTOLOGIES/xenopus_anatomy.owl");
		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		OWLOntology m_rootOntology = manager
				.loadOntologyFromOntologyDocument(file);
		String namespace = "http://www.geneontology.org/go#";
		int size = 100;
		int size2 = 100;
		test r = new test(m_rootOntology, namespace, size, size2 / 2, true,true);

		//System.out.println(r.getOutput());
		OutputStream fos = new FileOutputStream(new File("fullgrounding_ns2_xenopus_anatomy_100_output.txt"));
		fos.write(r.getOutput().getBytes());

	}
}
