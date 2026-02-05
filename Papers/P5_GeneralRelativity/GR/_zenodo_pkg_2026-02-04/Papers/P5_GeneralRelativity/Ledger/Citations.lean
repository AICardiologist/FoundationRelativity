/-
Paper 5: General Relativity AxCal Analysis - Citation Ledger
Structured bibliography handles for certificates
-/

namespace Papers.P5_GeneralRelativity

-- Citation structure for certificate references
structure Citation where
  key : String        -- citation key
  title : String      -- paper/book title  
  authors : String    -- author names
  venue : String      -- journal/publisher
  year : Nat          -- publication year
  pages : String      -- page numbers (optional)

-- Citation constructor helper
def cite (key : String) : Citation :=
  ⟨key, "", "", "", 0, ""⟩  -- minimal citation (full details in LaTeX)

-- Standard GR references used in certificates
def cite_wald_appendixB4 : Citation :=
  ⟨"Wald1984", "General Relativity", "R. M. Wald", "University of Chicago Press", 1984, "§B.4"⟩

def cite_wald_thm10_1_2 : Citation :=
  ⟨"Wald1984", "General Relativity", "R. M. Wald", "University of Chicago Press", 1984, "Thm. 10.1.2"⟩

def cite_wald_ch10_1 : Citation := 
  ⟨"Wald1984", "General Relativity", "R. M. Wald", "University of Chicago Press", 1984, "§10.1"⟩

def cite_wald_ch14 : Citation :=
  ⟨"Wald1984", "General Relativity", "R. M. Wald", "University of Chicago Press", 1984, "§14"⟩

def cite_hawking_ellis_ch8 : Citation :=
  ⟨"HawkingEllis1973", "The Large Scale Structure of Space-Time", 
   "S. W. Hawking and G. F. R. Ellis", "Cambridge University Press", 1973, "§8"⟩

def cite_choquet_bruhat_2009 : Citation :=
  ⟨"ChoquetBruhat2009", "General Relativity and the Einstein Equations",
   "Y. Choquet-Bruhat", "Oxford University Press", 2009, ""⟩

def cite_pour_el_richards_1989 : Citation :=
  ⟨"PourElRichards1989", "Computability in Analysis and Physics",
   "M. B. Pour-El and J. I. Richards", "Springer", 1989, ""⟩

def cite_eps_1972 : Citation :=
  ⟨"EPS1972", "The geometry of free fall and light propagation",
   "J. Ehlers, F. A. E. Pirani, and A. Schild", 
   "General Relativity: Papers in Honour of J. L. Synge", 1972, ""⟩

def cite_robb_1914 : Citation :=
  ⟨"Robb1914", "A Theory of Time and Space", "A. A. Robb", 
   "Cambridge University Press", 1914, ""⟩

def cite_reichenbach_1969 : Citation :=
  ⟨"Reichenbach1969", "Axiomatization of the Theory of Relativity",
   "H. Reichenbach", "University of California Press", 1969, ""⟩

def cite_bishop_bridges_1985 : Citation :=
  ⟨"BishopBridges1985", "Constructive Analysis", "E. Bishop and D. S. Bridges",
   "Springer", 1985, ""⟩

def cite_hellman_1998 : Citation :=
  ⟨"Hellman1998", "Mathematical constructivism in spacetime physics",
   "G. Hellman", "Brit. J. Phil. Sci.", 1998, "49(3):425-450"⟩

def cite_bridges_reply_1995 : Citation :=
  ⟨"BridgesReply1995", "Constructive mathematics and unbounded operators: a reply to Hellman",
   "D. S. Bridges", "J. Philosophical Logic", 1995, "24(5):549-561"⟩

-- AxCal-specific citations
def cite_axcal_dc_eliminator : Citation :=
  ⟨"AxCalDC", "AxCal DCω eliminator", "AxCal Framework", "Papers 3A/4", 2025, ""⟩

def cite_paper3a : Citation :=
  ⟨"Paper3A", "Axiom Calibration for Constructive Mathematics (Paper 3A)",
   "P. C.-K. Lee", "FoundationRelativity", 2025, ""⟩

def cite_paper4 : Citation :=
  ⟨"Paper4", "AxCal Framework and Spectral Geometry (Paper 4)",
   "P. C.-K. Lee", "FoundationRelativity", 2025, ""⟩

-- Citation list for easy enumeration
def all_citations : List Citation := [
  cite_wald_appendixB4, cite_wald_thm10_1_2, cite_wald_ch10_1, cite_wald_ch14,
  cite_hawking_ellis_ch8, cite_choquet_bruhat_2009, cite_pour_el_richards_1989,
  cite_eps_1972, cite_robb_1914, cite_reichenbach_1969,
  cite_bishop_bridges_1985, cite_hellman_1998, cite_bridges_reply_1995,
  cite_axcal_dc_eliminator, cite_paper3a, cite_paper4
]

end Papers.P5_GeneralRelativity