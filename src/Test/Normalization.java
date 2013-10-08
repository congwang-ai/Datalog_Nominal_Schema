package Test;

import java.util.*;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;

public class Normalization {

	protected final OWLAxioms m_axioms;
	protected final OWLDataFactory m_factory;
	protected int fresh_role_name_index = 1;

	public Normalization(OWLDataFactory factory, OWLAxioms axioms) {
		m_axioms = axioms;
		m_factory = factory;

	}

	public void processOntology(OWLOntology ontology) {
		m_axioms.m_classes.addAll(ontology.getClassesInSignature(true));
		m_axioms.m_objectProperties.addAll(ontology
				.getObjectPropertiesInSignature(true));
		m_axioms.m_dataProperties.addAll(ontology
				.getDataPropertiesInSignature(true));
		m_axioms.m_namedIndividuals.addAll(ontology
				.getIndividualsInSignature(true));

		processAxioms(ontology.getLogicalAxioms());
	}

	// only for test
	public void addIndividuals(OWLOntology ontology) {
		int counter = 1;
		Set<OWLClass> concepts = ontology.getClassesInSignature();
		for (OWLClass c : concepts) {
			OWLIndividual individual = m_factory.getOWLNamedIndividual(IRI
					.create("test_individual" + counter++));
			// System.out.println(c.toString());
			m_axioms.m_namedIndividuals.add((OWLNamedIndividual) individual);
			m_axioms.m_class_assertions.add(m_factory
					.getOWLClassAssertionAxiom(c, individual));
		}
	}

	// only for test
	public void addRoleAssertion(OWLOntology ontology) {
		int counter = 1;
		Set<OWLObjectProperty> properties = ontology
				.getObjectPropertiesInSignature();
		for (OWLObjectProperty c : properties) {
			OWLIndividual individual1 = m_factory.getOWLNamedIndividual(IRI
					.create("test_role_assertion_individual" + counter++));
			OWLIndividual individual2 = m_factory.getOWLNamedIndividual(IRI
					.create("test_role_assertion_individual" + counter++));
			// System.out.println(c.toString());
			m_axioms.m_namedIndividuals.add((OWLNamedIndividual) individual1);
			m_axioms.m_namedIndividuals.add((OWLNamedIndividual) individual2);
			m_axioms.m_property_assertions.add(m_factory
					.getOWLObjectPropertyAssertionAxiom(c, individual1,
							individual2));
		}
	}

	// only for test
	public void randomAssignIndividuals(OWLOntology ontology, int size,
			int size2) {
		int counter = 1;
		Set<OWLClass> concepts = ontology.getClassesInSignature();
		ArrayList<OWLClass> cl = new ArrayList<OWLClass>(concepts);
		int concepts_size = concepts.size();
		

		for (int i = 0; i < size; i++) {
			OWLIndividual individual = m_factory.getOWLNamedIndividual(IRI
					.create("test_individual" + counter++));
			m_axioms.m_namedIndividuals.add((OWLNamedIndividual) individual);
			Random r = new Random();
			int ri = r.nextInt(concepts_size);
			m_axioms.m_class_assertions.add(m_factory
					.getOWLClassAssertionAxiom(cl.get(ri), individual));
			//System.out.println(individual.toString());
		}

		counter = 0;
		Set<OWLObjectProperty> properties = ontology
				.getObjectPropertiesInSignature();
		ArrayList<OWLObjectProperty> pl = new ArrayList<OWLObjectProperty>(
				properties);
		int properties_size = properties.size();
		
		for (int i = 0; i < size2; i++) {
			OWLIndividual individual1 = m_factory.getOWLNamedIndividual(IRI
					.create("test_role_assertion_individual" + counter++));
			OWLIndividual individual2 = m_factory.getOWLNamedIndividual(IRI
					.create("test_role_assertion_individual" + counter++));
			// System.out.println(c.toString());
			m_axioms.m_namedIndividuals.add((OWLNamedIndividual) individual1);
			m_axioms.m_namedIndividuals.add((OWLNamedIndividual) individual2);
			Random r = new Random();
			int ri = r.nextInt(properties_size);
			m_axioms.m_property_assertions.add(m_factory
					.getOWLObjectPropertyAssertionAxiom(pl.get(ri),
							individual1, individual2));
		}
	}

	public void processAxioms(Collection<? extends OWLAxiom> axioms) {
		AxiomVisitor axiomVisitor = new AxiomVisitor();
		for (OWLAxiom axiom : axioms) {
			axiom.accept(axiomVisitor);
		}

		normalizeInclusions(axiomVisitor.m_classExpressionInclusions);
	}

	public void normalizeInclusions(List<OWLClassExpression[]> inclusions) {
		// TODO Auto-generated method stub
		int m_firstReplacementIndex = 1;
		while (!inclusions.isEmpty()) {
			OWLClassExpression[] current = inclusions
					.remove(inclusions.size() - 1);
			if (current.length == 2) { // subsumption situation
				if (isObjectExpressionSimple(current[0], current[1])) { // it's
																		// a
																		// normalized
																		// axiom
					m_axioms.m_conceptInclusions_normalized
							.add(new OWLClassExpression[] { current[0],
									current[1] });
					if (current[0] instanceof OWLClass)
						m_axioms.m_classesOccurringInOWLAxioms
								.add((OWLClass) current[0]);
					if (current[1] instanceof OWLClass)
						m_axioms.m_classesOccurringInOWLAxioms
								.add((OWLClass) current[1]);
					continue;
				}
				if (!isLeftSimple(current[0])) {
					if (current[0] instanceof OWLObjectIntersectionOf) {
						List<OWLClassExpression> conjuncts = ((OWLObjectIntersectionOf) current[0])
								.getOperandsAsList();
						if (conjuncts.size() != 2) { // when conjunctions are
														// more than 2
							OWLObjectIntersectionOf newConjunct = m_factory
									.getOWLObjectIntersectionOf(
											conjuncts.get(0), conjuncts.get(1));
							OWLClass freshname = m_factory.getOWLClass(IRI
									.create("internal:def#"
											+ m_firstReplacementIndex++));
							inclusions.add(new OWLClassExpression[] {
									newConjunct, freshname });
							Set<OWLClassExpression> newconjuncts = new HashSet<OWLClassExpression>();
							conjuncts.remove(0);
							conjuncts.remove(1);
							conjuncts.add(freshname);
							newconjuncts.addAll(conjuncts);
							OWLObjectIntersectionOf newConjunctEx = m_factory
									.getOWLObjectIntersectionOf(newconjuncts);
							inclusions.add(new OWLClassExpression[] {
									newConjunctEx, current[1] });
						} else { // when conjunctions are 2
							if (!(conjuncts.get(0) instanceof OWLClass)) {
								OWLClass freshname = m_factory.getOWLClass(IRI
										.create("internal:def#"
												+ m_firstReplacementIndex++));
								inclusions.add(new OWLClassExpression[] {
										conjuncts.get(0), freshname });
								OWLObjectIntersectionOf newConjunctEx = m_factory
										.getOWLObjectIntersectionOf(freshname,
												conjuncts.get(1));
								inclusions.add(new OWLClassExpression[] {
										newConjunctEx, current[1] });
							} else if (!(conjuncts.get(1) instanceof OWLClass)) {
								OWLClass freshname = m_factory.getOWLClass(IRI
										.create("internal:def#"
												+ m_firstReplacementIndex++));
								inclusions.add(new OWLClassExpression[] {
										conjuncts.get(1), freshname });
								OWLObjectIntersectionOf newConjunctEx = m_factory
										.getOWLObjectIntersectionOf(
												conjuncts.get(0), freshname);
								inclusions.add(new OWLClassExpression[] {
										newConjunctEx, current[1] });
							}
						}
					} else if (current[0] instanceof OWLObjectSomeValuesFrom) { // normalization
																				// somevaluesfrom
																				// at
																				// left
																				// head
						if (!isObjectSomeValuesFromSimple(current[0])) {
							OWLClassExpression original = ((OWLObjectSomeValuesFrom) current[0])
									.getFiller();
							OWLClass freshname = m_factory.getOWLClass(IRI
									.create("internal:def#"
											+ m_firstReplacementIndex++));
							OWLObjectPropertyExpression theProperty = ((OWLObjectSomeValuesFrom) current[0])
									.getProperty();
							OWLObjectSomeValuesFrom newExpression = m_factory
									.getOWLObjectSomeValuesFrom(theProperty,
											freshname);
							inclusions.add(new OWLClassExpression[] {
									newExpression, current[1] });
							inclusions.add(new OWLClassExpression[] { original,
									freshname });
						} else {

						}
					}
				} else if (!isRightSimple(current[1])) {
					if (current[1] instanceof OWLObjectSomeValuesFrom) { // normalization
																			// somevaluesfrom
																			// at
																			// right
																			// head
						OWLClassExpression original = ((OWLObjectSomeValuesFrom) current[1])
								.getFiller();
						OWLClass freshname = m_factory.getOWLClass(IRI
								.create("internal:def#"
										+ m_firstReplacementIndex++));
						OWLObjectPropertyExpression theProperty = ((OWLObjectSomeValuesFrom) current[1])
								.getProperty();
						OWLObjectSomeValuesFrom newExpression = m_factory
								.getOWLObjectSomeValuesFrom(theProperty,
										freshname);
						inclusions.add(new OWLClassExpression[] { current[0],
								newExpression });
						inclusions.add(new OWLClassExpression[] { freshname,
								original });
					} else if (current[1] instanceof OWLObjectIntersectionOf) { // break
																				// conjunction
																				// at
																				// right
																				// head
						List<OWLClassExpression> conjuncts = ((OWLObjectIntersectionOf) current[1])
								.getOperandsAsList();
						for (int i = 0; i < conjuncts.size(); i++) {
							inclusions.add(new OWLClassExpression[] {
									current[0], conjuncts.get(0) });
						}
					}
				}

			}
			if (current.length == 3) { // which is concept disjointness
										// situation
				if (current[2].isOWLNothing()) {
					if (!(current[0] instanceof OWLClass)) {
						OWLClass freshname = m_factory.getOWLClass(IRI
								.create("internal:def#"
										+ m_firstReplacementIndex++));
						inclusions.add(new OWLClassExpression[] { current[0],
								freshname });
						inclusions.add(new OWLClassExpression[] { freshname,
								current[1], current[2] });
					} else if (!(current[1] instanceof OWLClass)) {
						OWLClass freshname = m_factory.getOWLClass(IRI
								.create("internal:def#"
										+ m_firstReplacementIndex++));
						inclusions.add(new OWLClassExpression[] { current[1],
								freshname });
						inclusions.add(new OWLClassExpression[] { current[0],
								freshname, current[2] });
					}
				}
			}
		}
	}

	public boolean isObjectSomeValuesFromSimple(OWLClassExpression ex) {
		if (ex instanceof OWLObjectSomeValuesFrom) {
			if (((OWLObjectSomeValuesFrom) ex).getFiller() instanceof OWLClass) {
				return true;
			}

		}
		return false;
	}

	public boolean isObjectExpressionSimple(OWLClassExpression left,
			OWLClassExpression right) {
		if (left instanceof OWLClass) {
			if (right instanceof OWLClass)
				return true;
			else if (right instanceof OWLObjectSomeValuesFrom) {
				if (((OWLObjectSomeValuesFrom) right).getFiller() instanceof OWLClass)
					return true;

				else
					return false;
			} else if (right.isOWLThing())
				return true;
			else if (right instanceof OWLObjectHasSelf)
				return true;
			else
				return false;
		} else if (left instanceof OWLObjectIntersectionOf) {
			if (!(right instanceof OWLClass))
				return false;
			List<OWLClassExpression> conjuncts = ((OWLObjectIntersectionOf) left)
					.getOperandsAsList();
			if (conjuncts.size() != 2)
				return false;
			for (int i = 0; i < 2; i++) {
				if (!(conjuncts.get(i) instanceof OWLClass)) {
					return false;
				}
			}
			return true;
		} else if (left instanceof OWLObjectSomeValuesFrom) {
			if (((OWLObjectSomeValuesFrom) left).getFiller() instanceof OWLClass) {
				if (right instanceof OWLClass)
					return true;
			}
			return false;
		} else if (left.isOWLThing() && right instanceof OWLClass)
			return true;
		else if (left instanceof OWLObjectHasSelf && right instanceof OWLClass)
			return true;
		else
			return false;
	}

	public boolean isLeftSimple(OWLClassExpression left) {
		if (left instanceof OWLClass || left.isOWLThing()) {
			return true;
		} else if (left instanceof OWLObjectIntersectionOf) {
			List<OWLClassExpression> conjuncts = ((OWLObjectIntersectionOf) left)
					.getOperandsAsList();
			if (conjuncts.size() != 2)
				return false;
			for (int i = 0; i < 2; i++) {
				if (!(conjuncts.get(i) instanceof OWLClass)) {
					return false;
				}
			}
			return true;
		} else if (left instanceof OWLObjectSomeValuesFrom) {
			if (((OWLObjectSomeValuesFrom) left).getFiller() instanceof OWLClass) {
				return true;
			} else
				return false;
		} else if (left instanceof OWLObjectHasSelf)
			return true;
		else
			return false;
	}

	public boolean isRightSimple(OWLClassExpression right) {
		if (right instanceof OWLClass || right.isOWLNothing()) {
			return true;
		} else if (right instanceof OWLObjectSomeValuesFrom) {
			if (((OWLObjectSomeValuesFrom) right).getFiller() instanceof OWLClass) {
				return true;
			} else
				return false;
		} else if (right instanceof OWLObjectHasSelf)
			return true;
		else
			return false;
	}

	protected void addInclusion(
			OWLObjectPropertyExpression subObjectPropertyExpression,
			OWLObjectPropertyExpression superObjectPropertyExpression) {
		m_axioms.m_simpleObjectPropertyInclusions
				.add(new OWLObjectPropertyExpression[] {
						subObjectPropertyExpression.getSimplified(),
						superObjectPropertyExpression.getSimplified() });
	}

	protected void addInclusion(
			OWLObjectPropertyExpression[] subObjectPropertyExpressions,
			OWLObjectPropertyExpression superObjectPropertyExpression) {
		for (int index = subObjectPropertyExpressions.length - 1; index >= 0; --index)
			subObjectPropertyExpressions[index] = subObjectPropertyExpressions[index]
					.getSimplified();
		m_axioms.m_complexObjectPropertyInclusions
				.add(new OWLAxioms.ComplexObjectPropertyInclusion(
						subObjectPropertyExpressions,
						superObjectPropertyExpression.getSimplified()));
	}

	protected void addFact(OWLIndividualAxiom axiom) {
		m_axioms.m_facts.add(axiom);
	}
	
	protected void fullGrounding(OWLOntology ontology, int number){
		Set<OWLObjectProperty> p_set = ontology.getObjectPropertiesInSignature();
		for(OWLObjectProperty p : p_set){
			for(OWLIndividual i : m_axioms.m_individuals){
				OWLObjectSomeValuesFrom ex = m_factory.getOWLObjectSomeValuesFrom(p, (OWLClassExpression)i);
			}
		}
	}

	class AxiomVisitor implements OWLAxiomVisitor {
		protected final List<OWLClassExpression[]> m_classExpressionInclusions;

		public AxiomVisitor() {
			m_classExpressionInclusions = new ArrayList<OWLClassExpression[]>();
		}

		// Semantics-less axioms

		public void visit(OWLImportsDeclaration axiom) {
		}

		public void visit(OWLDeclarationAxiom axiom) {
		}

		public void visit(OWLAnnotationAssertionAxiom axiom) {
		}

		public void visit(OWLSubAnnotationPropertyOfAxiom axiom) {
		}

		public void visit(OWLAnnotationPropertyDomainAxiom axiom) {
		}

		public void visit(OWLAnnotationPropertyRangeAxiom axiom) {
		}

		// TBOX
		@Override
		public void visit(OWLSubClassOfAxiom axiom) {
			m_classExpressionInclusions.add(new OWLClassExpression[] {
					axiom.getSubClass(), axiom.getSuperClass() });

		}

		public void visit(OWLEquivalentClassesAxiom axiom) {
			if (axiom.getClassExpressions().size() > 1) {
				Iterator<OWLClassExpression> iterator = axiom
						.getClassExpressions().iterator();
				OWLClassExpression first = iterator.next();
				OWLClassExpression last = first;
				while (iterator.hasNext()) {
					OWLClassExpression next = iterator.next();
					m_classExpressionInclusions.add(new OWLClassExpression[] {
							last, next });
					last = next;
				}
				m_classExpressionInclusions.add(new OWLClassExpression[] {
						last, first });
			}
		}

		public void visit(OWLDisjointClassesAxiom axiom) {
			if (axiom.getClassExpressions().size() <= 1) {
				throw new IllegalArgumentException(
						"Error: Parsed "
								+ axiom.toString()
								+ ". A DisjointClasses axiom in OWL 2 DL must have at least two classes as parameters. ");
			}
			OWLClassExpression[] descriptions = new OWLClassExpression[axiom
					.getClassExpressions().size()];
			axiom.getClassExpressions().toArray(descriptions);
			OWLClass botClass = m_factory.getOWLNothing();
			for (int i = 0; i < descriptions.length; i++)
				for (int j = i + 1; j < descriptions.length; j++)
					m_classExpressionInclusions.add(new OWLClassExpression[] {
							descriptions[i], descriptions[j], botClass });
		}

		// RBOX

		public void visit(OWLSubObjectPropertyOfAxiom axiom) {
			if (!axiom.getSubProperty().isOWLBottomObjectProperty()
					&& !axiom.getSuperProperty().isOWLTopObjectProperty())
				m_axioms.m_simpleObjectPropertyInclusions
						.add(new OWLObjectPropertyExpression[] {
								axiom.getSubProperty(),
								axiom.getSuperProperty() });
			m_axioms.m_objectPropertiesOccurringInOWLAxioms.add(axiom
					.getSubProperty().getNamedProperty());
			m_axioms.m_objectPropertiesOccurringInOWLAxioms.add(axiom
					.getSuperProperty().getNamedProperty());
		}

		public void visit(OWLSubPropertyChainOfAxiom axiom) {
			List<OWLObjectPropertyExpression> subPropertyChain = axiom
					.getPropertyChain();
			OWLObjectPropertyExpression superObjectPropertyExpression = axiom
					.getSuperProperty();

			if (subPropertyChain.size() == 1)
				addInclusion(subPropertyChain.get(0),
						superObjectPropertyExpression);
			else if (subPropertyChain.size() == 2) {
				OWLObjectPropertyExpression[] subObjectProperties = new OWLObjectPropertyExpression[subPropertyChain
						.size()];
				subPropertyChain.toArray(subObjectProperties);
				addInclusion(subObjectProperties, superObjectPropertyExpression);
			} else { // Normalization of Role Chain
				OWLObjectPropertyExpression[] subObjectProperties = new OWLObjectPropertyExpression[2];
				subObjectProperties[0] = subPropertyChain.get(0);
				subObjectProperties[1] = subPropertyChain.get(1);
				IRI ontologyIRI = IRI.create("fresh_role_name");
				OWLObjectProperty newProperty = m_factory
						.getOWLObjectProperty(IRI.create(ontologyIRI + ""
								+ fresh_role_name_index++));
				addInclusion(subObjectProperties, newProperty);
				for (int i = 2; i < subPropertyChain.size() - 1; i++) {
					subObjectProperties[0] = newProperty;
					subObjectProperties[1] = subPropertyChain.get(i);
					newProperty = m_factory
							.getOWLObjectProperty(IRI.create(ontologyIRI + ""
									+ fresh_role_name_index++));
					addInclusion(subObjectProperties, newProperty);
				}
				subObjectProperties[0] = newProperty;
				subObjectProperties[1] = subPropertyChain.get(subPropertyChain
						.size() - 1);
				addInclusion(subObjectProperties, superObjectPropertyExpression);
			}

			for (OWLObjectPropertyExpression objectPropertyExpression : subPropertyChain)
				m_axioms.m_objectPropertiesOccurringInOWLAxioms
						.add(objectPropertyExpression.getNamedProperty());
			m_axioms.m_objectPropertiesOccurringInOWLAxioms.add(axiom
					.getSuperProperty().getNamedProperty());

		}

		public void visit(OWLEquivalentObjectPropertiesAxiom axiom) {
			Set<OWLObjectPropertyExpression> objectPropertyExpressions = axiom
					.getProperties();
			if (objectPropertyExpressions.size() > 1) {
				Iterator<OWLObjectPropertyExpression> iterator = objectPropertyExpressions
						.iterator();
				OWLObjectPropertyExpression first = iterator.next();
				OWLObjectPropertyExpression last = first;
				while (iterator.hasNext()) {
					OWLObjectPropertyExpression next = iterator.next();
					addInclusion(last, next);
					last = next;
				}
				addInclusion(last, first);
			}
			for (OWLObjectPropertyExpression objectPropertyExpression : objectPropertyExpressions)
				m_axioms.m_objectPropertiesOccurringInOWLAxioms
						.add(objectPropertyExpression.getNamedProperty());
		}

		// Assertions

		public void visit(OWLSameIndividualAxiom axiom) {
			if (axiom.containsAnonymousIndividuals())
				throw new IllegalArgumentException(
						"The axiom "
								+ axiom
								+ " contains anonymous individuals, which is not allowed in OWL 2. ");
			for (OWLIndividual e : axiom.getIndividuals()) {
				m_axioms.m_individuals.add(e);
			}
			addFact(axiom);
		}

		public void visit(OWLDifferentIndividualsAxiom axiom) {
			if (axiom.containsAnonymousIndividuals())
				throw new IllegalArgumentException(
						"The axiom "
								+ axiom
								+ " contains anonymous individuals, which is not allowed in OWL 2. ");
			for (OWLIndividual e : axiom.getIndividuals()) {
				m_axioms.m_individuals.add(e);
			}
			addFact(axiom);
		}

		public void visit(OWLClassAssertionAxiom axiom) {
			OWLClassExpression classExpression = axiom.getClassExpression();
			addFact(m_factory.getOWLClassAssertionAxiom(classExpression,
					axiom.getIndividual()));
			m_axioms.m_class_assertions.add(axiom);
			m_axioms.m_individuals.add(axiom.getIndividual());
			if (axiom instanceof OWLClass)
				m_axioms.m_classesOccurringInOWLAxioms.add((OWLClass) axiom);
		}

		public void visit(OWLObjectPropertyAssertionAxiom axiom) {
			addFact(m_factory.getOWLObjectPropertyAssertionAxiom(axiom
					.getProperty().getSimplified(), axiom.getSubject(), axiom
					.getObject()));
			m_axioms.m_property_assertions.add(axiom);
			m_axioms.m_objectPropertiesOccurringInOWLAxioms.add(axiom
					.getProperty().getNamedProperty());
			m_axioms.m_individuals.add(axiom.getObject());
			m_axioms.m_individuals.add(axiom.getSubject());
		}

		public void visit(OWLNegativeObjectPropertyAssertionAxiom axiom) {
			if (axiom.containsAnonymousIndividuals())
				throw new IllegalArgumentException(
						"The axiom "
								+ axiom
								+ " contains anonymous individuals, which is not allowed in OWL 2 DL. ");
			addFact(m_factory.getOWLNegativeObjectPropertyAssertionAxiom(axiom
					.getProperty().getSimplified(), axiom.getSubject(), axiom
					.getObject()));
			m_axioms.m_objectPropertiesOccurringInOWLAxioms.add(axiom
					.getProperty().getNamedProperty());
			m_axioms.m_negative_property_assertions.add(axiom);
			m_axioms.m_individuals.add(axiom.getObject());
			m_axioms.m_individuals.add(axiom.getSubject());

		}

		@Override
		public void visit(OWLAsymmetricObjectPropertyAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLReflexiveObjectPropertyAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLDataPropertyDomainAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLObjectPropertyDomainAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLNegativeDataPropertyAssertionAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLDisjointDataPropertiesAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLDisjointObjectPropertiesAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLObjectPropertyRangeAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLFunctionalObjectPropertyAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLDisjointUnionAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLSymmetricObjectPropertyAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLDataPropertyRangeAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLFunctionalDataPropertyAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLEquivalentDataPropertiesAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLDataPropertyAssertionAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLTransitiveObjectPropertyAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLIrreflexiveObjectPropertyAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLSubDataPropertyOfAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLInverseFunctionalObjectPropertyAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLInverseObjectPropertiesAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLHasKeyAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLDatatypeDefinitionAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(SWRLRule axiom) {
			// TODO Auto-generated method stub

		}

	}
}
