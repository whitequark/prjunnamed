searchState.loadedDescShard("prjunnamed_netlist", 0, "This crate defines the IR of Project Unnamed.\n<code>a + b + ci</code> — add with carry.\n<code>a &amp; b</code>.\nIf <code>enable</code> is asserted, output is <code>value</code> where …\nA unit of logic.\nA constant is a (possibly empty) sequence of <code>Trit</code>s.\nA control net is a <code>Net</code> that can be negated.\nTentatively attaches a name to a given value.\nSea of <code>Cell</code>s.\nA flip-flop cell.\nIdentifier within source code.\nScope identified by an index. A top-level named scope …\nDesign input of a given width.\nIf <code>enable</code> is asserted, output is one-hot priority match of …\nAn all-in-one random-access memory cell.\nA structure describing a synchronous read port’s control …\nA memory read port, either synchronous or asynchronous.\nA synchronous memory write port.\nMetadata item.\n<code>a ? b : c</code>.\nAttaches a name to a given value for debugging.\nScope identified by a name. A top-level named scope could …\nA net is a driver in the design; either a constant (a <code>Trit</code>…\nAbsence of a metadata item. The purpose of this variant is …\n<code>a | b</code>.\nDesign output. Attaches a name to a given value.\nWhen the same memory bit is written by the given write …\n<code>a &gt;&gt; (b * c)</code>. The top bits are filled with copies of the …\nMultiple metadata items. The purpose of this variant is to …\n<code>a &lt;&lt; (b * c)</code>. The bottom bits are filled with zeros.\nSource location.\nWhen the same memory bit is written by the given write …\nAn extended binary value.\n<code>a &gt;&gt; (b * c)</code>. The top bits are filled with zeros.\nWhen the same memory bit is written by the given write …\nA value is a (possibly empty) sequence of <code>Net</code>s.\n<code>a &gt;&gt; (b * c)</code>. The top bits are filled with <code>X</code>.\nThe write address, selecting which row(s) to write.  The …\nThe read address, selecting which row(s) to read.  Follows …\nAsynchronous reset.\nMust have the same width as <code>data</code>.\nThe clock.  The active edge is rising if it is a …\nThe write data.  The width must be a power-of-two multiple …\nThe width of the read data.  Must be a power-of-two …\nThe number of rows in the memory.\nClock enable.\nConvert target cells into generic instances.\nA flip-flop-like structure describing the synchronous read …\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nConvert generic instances into target cells.\nMust have the same width as <code>data</code>.\nInitial value for the memory, with all the rows …\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nThe write mask.  Must have the same width as <code>data</code>.  On …\nGet target name. The name of the target can be used to …\nCreates an empty constant.\nCreates an empty value.\nCreates a constant of given width that has a <code>1</code> at position …\nCreates an all-<code>1</code> constant of given width.\nCreates an all-<code>1</code> value of given width.\nGet target options. Target options define the exact …\nEach pattern is a list of alternatives.\nGet prototypes of target cells. Prototypes in conjunction …\nExpands the constant by a single position with the given …\nThe behavior of this read port during a simultaneous write …\nSynchronous reset.\nIf true, <code>reset</code> has priority over <code>enable</code>.  Otherwise, <code>enable</code>…\nMust have the same width as <code>data</code>.\nIf possible, return a cell that computes only a slice of …\nRun the complete synthesis flow.\nCreates an all-<code>X</code> constant of given width.\nCreates an all-<code>X</code> value of given width.\nValidate target-specific constraints. Conformance with the …\nThe width of single memory row.\nCreates an all-<code>0</code> constant of given width.\nCreates an all-<code>0</code> value of given width.\nEnd of the range (exclusive).\nFilename.  Must not be empty.\nName.  Must not be empty.\nName.  Must not be empty.\nName.  Must not be empty.\nParent scope.  Must reference <code>MetaItem::None</code>, …\nParent scope.  Must reference <code>MetaItem::None</code>, …\nContaining scope. Must reference a <code>MetaItem::NamedScope</code>, …\nSource location.  Must reference <code>MetaItem::None</code> or …\nSource location.  Must reference <code>MetaItem::None</code> or …\nStart of the range (inclusive).\nValue.")