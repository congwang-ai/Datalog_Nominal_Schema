package Test;

import java.util.*;

import org.semanticweb.owlapi.model.*;

import Test.OWLAxioms.ComplexObjectPropertyInclusion;

public class Translator {

	protected final OWLAxioms m_axioms;
	protected final OWLDataFactory m_factory;

	public Translator(OWLDataFactory factory, OWLAxioms axioms) {
		m_axioms = axioms;
		m_factory = factory;

	}

	public void translateKB() {
		TranslateELAxioms();
		TranslateABox();
		TranslateSignature();
		TranslateRBOX();
		TranslatorNSAxioms();
	}

	public void TranslateELAxioms() {
		ArrayList<OWLClassExpression[]> inclusions = m_axioms.m_conceptInclusions_normalized;
		for (int i = 0; i < inclusions.size(); i++) {
			OWLClassExpression[] current = inclusions.get(i);
			if (current.length == 2) { // subsumption
				if (current[0] instanceof OWLClass
						&& current[1] instanceof OWLClass)
					rewriteType1(current[0], current[1]);
				if (current[0] instanceof OWLObjectSomeValuesFrom
						&& current[1] instanceof OWLClass)
					rewriteType3(current[0], current[1]);
				if (current[0] instanceof OWLClass
						&& current[1] instanceof OWLObjectSomeValuesFrom)
					rewriteType4(current[0], current[1]);
				if (current[0] instanceof OWLObjectHasSelf
						&& current[1] instanceof OWLClass)
					rewriteType5(current[0], current[1]);
				if (current[0] instanceof OWLClass
						&& current[1] instanceof OWLObjectHasSelf)
					rewriteType6(current[0], current[1]);
				if (current[0].isOWLThing() && current[1] instanceof OWLClass)
					rewriteType7(current[1]);
				if (current[0] instanceof OWLClass && current[1].isOWLNothing())
					rewriteType8(current[0]);
			}
			if (current.length == 3) { // disjointness
				if (current[0] instanceof OWLObjectIntersectionOf
						&& current[1] instanceof OWLClass)
					rewriteType2(current[0], current[1]);
			}

		}
	}

	public void TranslateABox() {
		// Class Assertions, C(a)
		for (int i = 0; i < m_axioms.m_class_assertions.size(); i++) {
			OWLClassAssertionAxiom current = m_axioms.m_class_assertions.get(i);
			String expression = current.getClassExpression().toString();
			String individual = current.getIndividual().toString();
			m_axioms.m_datalog_rules.add("subClass('" + individual + "','"
					+ expression + "').");
		}

		// Property Assertions, R(a,b)
		for (int i = 0; i < m_axioms.m_property_assertions.size(); i++) {
			OWLObjectPropertyAssertionAxiom current = m_axioms.m_property_assertions
					.get(i);
			String subject = current.getSubject().toString();
			String object = current.getObject().toString();
			String property = current.getProperty().toString();
			//System.out.println("subEx('" + subject + "','" + property
				//	+ "','" + object + "','" + object + "').");
			m_axioms.m_datalog_rules.add("supEx('" + subject + "','" + property
					+ "','" + object + "','" + object + "').");
		//	m_axioms.m_datalog_rules.add("triple('" + subject + "','" + property
			//		+ "','" + object + "').");
		}
	}

	public void TranslateSignature() {
		// translate individual a to nom(a)
		for (OWLIndividual e : m_axioms.m_namedIndividuals) {
			m_axioms.m_datalog_rules.add("nom('" + e.toString() + "').");
			
		}
		// translate role s to rol(s)
		for (OWLObjectProperty e : m_axioms.m_objectProperties) {
			m_axioms.m_datalog_rules.add("rol('" + e.toString() + "').");
			
		}
		// translate concept c to cls(c)
		for (OWLClass e : m_axioms.m_classes) {
			
			m_axioms.m_datalog_rules.add("cls('" + e.toString() + "').");
		}
		System.out.println("Property size:"+m_axioms.m_objectProperties.size());
		System.out.println("Class size:"+m_axioms.m_classes.size());
	}

	public void TranslateRBOX() {
		// translate simple role inclusion
		for (OWLObjectPropertyExpression[] current : m_axioms.m_simpleObjectPropertyInclusions) {
			m_axioms.m_datalog_rules.add("subRole('" + current[0].toString()
					+ "','" + current[1].toString() + "').");
		}
		// translate role chain
		for (ComplexObjectPropertyInclusion current : m_axioms.m_complexObjectPropertyInclusions) {
			OWLObjectPropertyExpression[] subObjectPropertyExpressions = current.m_subObjectProperties;
			OWLObjectPropertyExpression superObjectPropertyExpression = current.m_superObjectProperty;
			m_axioms.m_datalog_rules.add("subRole('"
					+ subObjectPropertyExpressions[0].toString() + "','"
					+ subObjectPropertyExpressions[1].toString() + "','"
					+ superObjectPropertyExpression.toString() + "').");
		}

	}

	// A \subclass B
	private void rewriteType1(OWLClassExpression ex1, OWLClassExpression ex2) {
		m_axioms.m_datalog_rules.add("subClass('" + ex1.toString() + "','"
				+ ex2.toString() + "').");
	}

	// A \conjunct B \subclass C
	private void rewriteType2(OWLClassExpression ex1, OWLClassExpression ex2) {
		List<OWLClassExpression> conjuncts = ((OWLObjectIntersectionOf) ex1)
				.getOperandsAsList();
		m_axioms.m_datalog_rules.add("subConj('" + conjuncts.get(0).toString()
				+ "','" + conjuncts.get(1).toString() + "'," + "'"
				+ ex2.toString() + "').");
	}

	// \exists R.A \subclass C
	private void rewriteType3(OWLClassExpression ex1, OWLClassExpression ex2) {
		String concept = ((OWLObjectSomeValuesFrom) ex1).getFiller()
				.toString();
		String relation = ((OWLObjectSomeValuesFrom) ex1).getProperty()
				.toString();
		m_axioms.m_datalog_rules.add("subEx('" + relation + "','" + concept
				+ "'," + "'" + ex2.toString() + "').");
	}

	// A \subclass \exists R.C
	private void rewriteType4(OWLClassExpression ex1, OWLClassExpression ex2) {
		String concept = ((OWLObjectSomeValuesFrom) ex2).getFiller()
				.toString();
		String relation = ((OWLObjectSomeValuesFrom) ex2).getProperty()
				.toString();
		String freshname = "FN"
				+ (ex1.toString() + relation + concept).hashCode();
		m_axioms.m_datalog_rules.add("supEx('" + ex1.toString() + "','"
				+ relation + "'," + "'" + concept + "','" + freshname + "').");
	}

	// \exists R.Self \subclass A
	private void rewriteType5(OWLClassExpression ex1, OWLClassExpression ex2) {
		String relation = ((OWLObjectHasSelf) ex1).getProperty().toString();
		m_axioms.m_datalog_rules.add("subSelf('" + relation + "','"
				+ ex2.toString() + "').");
	}

	// A \subclass \exists R.Self
	private void rewriteType6(OWLClassExpression ex1, OWLClassExpression ex2) {
		String relation = ((OWLObjectHasSelf) ex2).getProperty().toString();
		m_axioms.m_datalog_rules.add("supSelf('" + ex1.toString() + "','"
				+ relation + "').");
	}

	// Top \subclass A
	private void rewriteType7(OWLClassExpression ex) {
		m_axioms.m_datalog_rules.add("top('" + ex.toString() + "').");
	}

	// A \subclass BOT
	private void rewriteType8(OWLClassExpression ex) {
		m_axioms.m_datalog_rules.add("bot('" + ex.toString() + "').");
	}

	//only for test
	private void TranslatorNSAxioms() {
		
	}
}
