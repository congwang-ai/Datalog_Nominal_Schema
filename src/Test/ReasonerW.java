package Test;

import java.awt.BorderLayout;
import java.awt.Font;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.io.File;

import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JComboBox;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.JTextArea;
import javax.swing.SwingUtilities;
import javax.swing.UIManager;

import org.deri.iris.Configuration;
import org.deri.iris.KnowledgeBaseFactory;
import org.deri.iris.evaluation.stratifiedbottomup.StratifiedBottomUpEvaluationStrategyFactory;
import org.deri.iris.evaluation.stratifiedbottomup.naive.NaiveEvaluatorFactory;
import org.deri.iris.evaluation.stratifiedbottomup.seminaive.SemiNaiveEvaluatorFactory;
import org.deri.iris.evaluation.wellfounded.WellFoundedEvaluationStrategyFactory;
import org.deri.iris.optimisations.magicsets.MagicSets;
import org.deri.iris.optimisations.rulefilter.RuleFilter;
import org.deri.iris.rules.safety.AugmentingRuleSafetyProcessor;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;

/**
 * A GUI version of the Demo application.
 */

public class ReasonerW {

	public static final int FONT_SIZE = 12;
	public static final String NEW_LINE = System.getProperty("line.separator");

	public static void main(String[] args) {
		// Set up the native look and feel
		try {
			UIManager.setLookAndFeel(UIManager.getSystemLookAndFeelClassName());
		} catch (Exception e) {
		}

		// Create the main window and show it.
		MainFrame mainFrame = new MainFrame();
		mainFrame.setSize(1000, 1000);
		mainFrame.setVisible(true);
	}

	/**
	 * The main application window
	 */
	public static class MainFrame extends JFrame implements ActionListener {
		/** The serialisation ID. */
		private static final long serialVersionUID = 1L;

		private final JTextArea mProgram = new JTextArea();
		private final JTextArea mRules = new JTextArea();
		private final JTextArea mOutput = new JTextArea();

		private final JButton mRun = new JButton("Evaluate");
		private final JButton mAbort = new JButton("Abort");
		private final JButton open = new JButton("Open a File (owl)...");
		private final JFileChooser fc = new JFileChooser();
		private File f = null;

		private final JComboBox mOptimise = new JComboBox(new String[] {
				"none", "Magic Sets" });

		Thread mExecutionThread;

		public MainFrame() {
			super("Datalog for Nominal Schema - Demo");

			setup();
		}

		private void setup() {
			// TODO Auto-generated method stub
			setLayout(new BorderLayout());

			mRun.addActionListener(this);
			open.addActionListener(this);
			mAbort.addActionListener(this);
			mAbort.setEnabled(false);

			JScrollPane programScroller = new JScrollPane(mProgram);
			// JScrollPane rulesScroller = new JScrollPane(mRules);
			JScrollPane outputScroller = new JScrollPane(mOutput);

			Font f = new Font("courier", Font.PLAIN, FONT_SIZE);
			mProgram.setFont(f);
			mOutput.setFont(f);
			mRules.setFont(f);

			JSplitPane mainSplitter = new JSplitPane(JSplitPane.VERTICAL_SPLIT,
					true, programScroller, outputScroller);
			// JSplitPane secondSplitter = new
			// JSplitPane(JSplitPane.HORIZONTAL_SPLIT);

			getContentPane().add(mainSplitter, BorderLayout.CENTER);
			// getContentPane().add(secondSplitter, BorderLayout.CENTER);

			JPanel panel = new JPanel();
			panel.add(mOptimise);
			panel.add(mRun);
			panel.add(mAbort);
			panel.add(open);

			getContentPane().add(panel, BorderLayout.SOUTH);

			mainSplitter.setOneTouchExpandable(true);
			mainSplitter.setDividerLocation(400);

			// secondSplitter.setOneTouchExpandable(true);
			// secondSplitter.setDividerLocation(700);

			addWindowListener(new WindowAdapter() {
				public void windowClosing(WindowEvent e) {
					System.exit(0);
				}
			});
		}

		@Override
		public void actionPerformed(ActionEvent e) {
			if (e.getSource() == mRun) {
				run();
			} else if (e.getSource() == mAbort) {
				abort();
			} else if (e.getSource() == open) {
				int returnVal = fc.showOpenDialog(this);

				if (returnVal == JFileChooser.APPROVE_OPTION) {
					f = fc.getSelectedFile();
					// This is where a real application would open the file.
					OWLOntologyManager manager = OWLManager
							.createOWLOntologyManager();
					OWLOntology m_rootOntology;
					try {
						m_rootOntology = manager
								.loadOntologyFromOntologyDocument(f);

						//Reasoner r = new Reasoner(m_rootOntology);
						//mProgram.setText(r.getDefaultRules());
					} catch (Exception e1) {
						// TODO Auto-generated catch block
						e1.printStackTrace();
					}
				}
			}
		}

		class NotifyOutput implements Runnable {
			NotifyOutput(String output) {
				mOutput = output;
			}

			public void run() {
				setOutput(mOutput);
			}

			final String mOutput;
		}

		synchronized void setOutput(String output) {
			mRun.setEnabled(true);
			mAbort.setEnabled(false);

			mOutput.setText(output);
		}

		synchronized void run() {
			mOutput.setText("");

			mRun.setEnabled(false);
			mAbort.setEnabled(true);
			open.setEnabled(true);

			String program = mProgram.getText();

			Configuration config = KnowledgeBaseFactory
					.getDefaultConfiguration();

			switch (mOptimise.getSelectedIndex()) {
			case 0:
				break;

			case 1:
				config.programOptmimisers.add(new RuleFilter());
				config.programOptmimisers.add(new MagicSets());
				break;
			}

			mExecutionThread = new Thread(new ExecutionTask(program),
					"Evaluation task");

			mExecutionThread.setPriority(Thread.MIN_PRIORITY);
			mExecutionThread.start();
		}

		synchronized void abort() {
			mRun.setEnabled(true);
			mAbort.setEnabled(false);
			open.setEnabled(true);
			// Not very nice, but hey, that's life.
			mExecutionThread.stop();
		}

		class ExecutionTask implements Runnable {
			ExecutionTask(String program) {
				this.program = program;
			}

			// @Override
			public void run() {
				if (f != null) {
					try {
						OWLOntologyManager manager = OWLManager
								.createOWLOntologyManager();
						OWLOntology m_rootOntology = manager
								.loadOntologyFromOntologyDocument(f);
						//Reasoner r = new Reasoner(m_rootOntology);
						// mProgram.setText(r.getDefaultRules());
						//SwingUtilities.invokeLater(new NotifyOutput(r.getOutput()));
					} catch (Exception e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
				}
			}

			private final String program;
		}

	}

}
