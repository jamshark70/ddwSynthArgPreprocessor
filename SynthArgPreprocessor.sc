// TODO: i-rate controls

SynthArgPreprocessor {
	classvar closeBrackets;
	classvar <>enabled = false;
	classvar notInstalled = true;

	*initClass {
		closeBrackets = IdentityDictionary[
			$( -> $),
			$[ -> $],
			${ -> $}
		]
	}

	*install {
		if(notInstalled) {
			if(thisProcess.interpreter.preProcessor.isNil) {
				thisProcess.interpreter.preProcessor = this
			} {
				thisProcess.interpreter.preProcessor =
				thisProcess.interpreter.preProcessor <> this;
			};
			notInstalled = false;
		};
		enabled = true;
	}

	// top level: skip over irrelevant syntactic units
	// dispatch for brackets, comments, quotes, and functions
	// parser sub-methods should leave 'stream' such that 'next' is the char after that unit
	*value { |str|
		var stream = CollStream(str);
		var out = CollStream.new;
		var ch;

		if(enabled) {
			while {
				ch = stream.next;
				ch.notNil
			} {
				out << this.parseElement(stream, ch);
			};
			^out.collection
		} { ^str }
	}

	*parseElement { |stream, ch, whileCondition(true)|
		var out = CollStream(String.with(ch));

		while {
			ch.notNil and: { whileCondition.value(ch) }
		} {
			case
			{ stream.collection.findRegexpAt("SynthDef", stream.pos - 1).notNil } {
				out << this.parseSynthDef(stream);
			}
			{ ch == ${ } {
				out << this.parseFunction(stream);
			}
			{ closeBrackets[ch].notNil } {
				out << this.parseBrackets(stream, ch);
			}
			{ "\"'".includes(ch) } {
				out << this.parseString(stream, ch);
			}
			{ ch == $/ } {
				// / might not be a comment, so it may return valid content
				out << this.skipComment(stream);
			}
			{ out << ch };
			ch = stream.next;
		};
		^out.collection
	}

	*parseSpaces { |stream|
		var out = String.new;
		var ch;
		while {
			ch = stream.next;
			ch.notNil and: { ch.isSpace }
		} {
			out = out ++ ch;
		};
		stream.rewind(1);
		^out
	}

	*parseIdentifier { |stream, ch|
		var out = String.new;
		if(ch.notNil) { out = out.add(ch) };
		while {
			ch = stream.next;
			ch.notNil and: { ch.isAlphaNum or: { ch == $_ } }
		} {
			out = out ++ ch;
		};
		stream.rewind(1);
		^out
	}

	// SynthDef(\name, {...}, rates, prependArgs, variants, metadata)
	// 'S' has been consumed
	*parseSynthDef { |stream|
		// parseFunction will put an array of arg details into the Ref
		// use this to write metadata at the end
		// if there's an existing metadata string, use .putAll
		var argSpecs = Ref.new;
		var name, func, isClosedFunc = false;
		var paramStream = Pseq(["rates", "prependArgs", "variants", "metadata"], 1).asStream;
		var param, paramString, params;
		var ch;
		var out;

		params = IdentityDictionary.new;

		7.do { stream.next };  // findRegexpAt already validated
		this.parseSpaces(stream);
		if(stream.next != $() {
			Error("SynthDef parse failed").throw;
		};

		this.parseSpaces(stream);
		name = this.parseElement(stream, stream.next, { |ch| ch != $, });
		this.parseSpaces(stream);

		if(stream.next == $#) {
			isClosedFunc = true;
			this.parseSpaces(stream);
		} {
			stream.rewind(1);
		};
		if(stream.next == ${) {
			func = this.parseFunction(stream, argSpecs);
		};

		// fairly sure confusion ensues if you use ## controls with 'rates' and 'lags'
		// but preserve them anyway
		while {
			this.parseSpaces(stream);
			ch = stream.next;
			ch.notNil and: { ch != $) }
		} {
			// keyword arg?
			if(stream.collection.findRegexpAt("[A-Za-z0-9_]+:")) {
				param = this.parseIdentifier(stream, stream.next);
				stream.next;  // ":" already validated
			} {
				param = paramStream.next;
			};
			this.parseSpaces(stream);
			paramString = this.parseElement(stream, stream.next,
				{ |ch| ",)".includes(ch).not }
			);
			if(param.notNil and: { paramString.every(_.isSpace).not }) {
				params.put(param, paramString);
			};
		};

		out = CollStream.new;
		out << "SynthDef(" << name << ", "
		<< func;
		paramStream.reset.do { |param|
			var str = params[param];
			if(str.size > 0) {
				out << ", " << param << ": " << str;
			};
			if(param == "metadata") {
				str = "";
				argSpecs.dereference.keysValuesDo { |argName, ctl|
					if(ctl[\spec].size > 0) {
						if(str.size > 0) { str = str ++ ", " };
						str = str ++ ctl[\name] ++ ": " ++ ctl[\spec] ++ ".asSpec";
					};
				};
				if(str.notEmpty) {
					if(params[param].size > 0) {  // there's user metadata
						// here's a problem: merging user specs with auto-specs
						out << ".put(\\specs, (" << str << "))"
					} {
						out << ", metadata: (specs: (" << str << "))";
					};
				};
			};
		};
		out << ")";
		^out.collection
	}

	// assume open-brace is already consumed
	*parseFunction { |stream, argSpecRef|
		// - plain text
		// - arg block
		// - '##' arg spec
		var units;
		var preSpace, argBlock;
		var controlDict = IdentityDictionary.new;  // to track ctl --> lag dependencies

		var ch, unit, out;
		var firstNonVar, i, ordinal;

		// skip spaces: open brace is consumed so 'next' should be the first space or other
		preSpace = this.parseSpaces(stream);
		if(stream.peek.isNil) { ^"{" ++ preSpace };  // probably syntax error later

		// see if there's an arg block
		// for now treating as plain text
		// but I really should read names and default values for each
		ch = stream.next;
		case
		{ ch == $| } {
			argBlock = "|"
			++ this.parseElement(stream, stream.next, { |ch| ch != $| })
			++ "|"
		}
		{ stream.collection.findRegexpAt("arg", stream.pos - 1).notNil } {
			argBlock = "a"  // only consumed the 'a' -- parseElement will get "rg"
			++ this.parseElement(stream, stream.next, { |ch| ch != $; })
			++ ";"
		}
		{ stream.rewind(1) };  // didn't find arg block: back up one

		// main loop: either ## spec or free text
		unit = CollStream.new;
		while {
			ch = stream.next;
			ch.notNil and: { ch != $} }
		} {
			case
			{ ch == $# } {
				ch = stream.next;
				if(ch == $#) {
					if(unit.collection.size > 0) {
						units = units.add(unit.collection);
					};
					unit = this.parseControl(stream, controlDict);
					units = units.add(unit);
					controlDict.put(unit[\name], unit);
					unit = CollStream.new;
				} {
					unit << $# << ch;
				};
			}
			{ unit << ch };
		};
		if(unit.collection.size > 0) {
			units = units.add(unit.collection);
		};

		if(units.size == 0) {
			^"{" ++ preSpace ++ argBlock ++ "}"
		};

		units = units.select { |unit|
			unit.isString.not or: { unit.every(_.isSpace).not }
		};
		units.do { |unit, i|
			if(unit.isString and: { unit.last == $\n }) {
				units[i] = unit.drop(-1);
			};
		};

		// control units should all come before non-var blocks
		firstNonVar = units.detectIndex { |unit|
			unit.isString and: {
				unit.every(_.isSpace).not and: {
					unit.contains("var").not
				}
			}
		};
		if(firstNonVar.notNil) {
			i = firstNonVar;
			// clean this up later
			while { i < units.size } {
				if(units[i].isKindOf(IdentityDictionary)) {
					unit = units.removeAt(i);
					units = units.insert(firstNonVar, unit);
					firstNonVar = firstNonVar + 1;
				};
				i = i + 1;
			};
		};

		// output will be '{' ++ arg block ++ argspec var block ++ plain text ++ '}'

		ordinal = Ref(0);
		out = CollStream.new;
		out << "{" << preSpace;
		if(argBlock.size > 0) { out << argBlock };
		units.separate { |a, b|
			a.isKindOf(IdentityDictionary) xor: b.isKindOf(IdentityDictionary)
		}.do { |group|
			if(group[0].isString) {
				group.do { |str| out << str }
			} {
				this.renderControls(out, group, ordinal);
			}
		};

		if(argSpecRef.notNil) { argSpecRef.value = controlDict };

		^out.collection ++ "}"
	}

	// ## name = default: rate(1 char) (lag) [spec];
	// assumes '##' has been eaten but nothing else
	*parseControl { |stream, controlDict|
		var ctl = IdentityDictionary.new;
		var ch, refs;
		this.parseSpaces(stream);

		ctl[\level] = 1;
		ctl[\ordinal] = controlDict.size;
		ctl[\rate] = $k;
		ctl[\default] = 0;
		ctl[\name] = this.parseIdentifier(stream);
		this.parseSpaces(stream);

		ch = stream.next;
		if(ch == $=) {
			this.parseSpaces(stream);
			ctl[\default] = this.parseElement(stream, stream.next,
				{ |ch| ":;".includes(ch).not }
			);
			stream.rewind(1);
		} {
			stream.rewind(1);
			this.parseSpaces(stream);
		};
		if(stream.peek == $;) {
			stream.next;
			^ctl  // # name = value; -- no lag, no spec
		};

		stream.next;
		this.parseSpaces(stream);
		ch = stream.next;
		if("ktai".includes(ch)) {
			ctl[\rate] = ch;
		} {
			stream.rewind(1);
		};
		this.parseSpaces(stream);
		if(stream.peek == $;) {
			stream.next;
			^ctl  // ## name = value: k; -- no lag, no spec
		};

		this.parseSpaces(stream);
		if(stream.peek == $,) {
			stream.next;
			this.parseSpaces(stream);
		};
		ch = stream.next;
		if(ch != $[) {  // not supporting array lag
			ctl[\lag] = this.parseElement(stream, ch, { |ch| ",;".includes(ch).not });
			// check for ctl references
			refs = controlDict.select { |value, key|
				ctl[\lag].contains(key.asString)
			};
			if(refs.size > 0) {
				ctl[\level] = 1 + refs.maxValue { |item| item[\level] }
			};
		};
		stream.rewind(1);
		if(stream.peek == $;) {
			stream.next;
			^ctl
		};

		stream.next;
		this.parseSpaces(stream);
		if(stream.peek == $,) {
			stream.next;
			this.parseSpaces(stream);
			stream.next;
		};
		// looks weird but I'd like to support name = value: \spec
		stream.rewind(1);
		if(stream.peek != $;) {
			ctl[\spec] = this.parseElement(stream, stream.next, { |ch| ch != $; });
			stream.rewind(1);
		};
		if(stream.peek != $;) {
			Error("## synth control '%' failed parsing".format(ctl[\name])).throw;
		};

		stream.next;
		^ctl
	}

	*renderControls { |out, group, ordinal|
		var container, groupContainer;
		group.sort { |a, b|
			if(a[\level] == b[\level]) {
				a[\ordinal] < b[\ordinal]
			} {
				a[\level] < b[\level]
			};
		};
		group = group.separate { |a, b| a[\level] != b[\level] };
		container = "ctl" ++ group.hash.asHexString(8);
		group.do { |gr|
			ordinal.value = ordinal.dereference + 1;
			groupContainer = container ++ "_" ++ ordinal.dereference;
			out << "\n\tvar " << groupContainer << " = [";
			gr.do { |ctl, i|
				if(i > 0) { out << ", " };
				out << "[" << ctl[\name] << ": "
				<< ctl[\default] << ", \\"
				<< ctl[\rate] << "r, "
				<< ctl[\lag] << ", ";
				if(ctl[\spec].size > 0) {
					out << ctl[\spec] << ".asSpec"
				} {
					out << "nil"
				};
				out << "]";
			};
			out << "].synthArgPPMakeControls;\n";
			gr.do { |ctl, i|
				out << "\tvar " << ctl[\name]
				<< " = " << groupContainer << "[" << i << "];\n"
			};
		};
	}

	*parseBrackets { |stream, openBracket|
		var closeBracket = closeBrackets[openBracket];
		var ch, out = String.with(openBracket);

		if(closeBracket.isNil) {
			Error("Incorrectly entered parseBrackets with '%'".format(openBracket))
			.throw;
		};
		^openBracket
		++ this.parseElement(stream, stream.next, { |ch| ch != closeBracket })
		++ closeBracket;
	}

	*parseString { |stream, delimiter|
		var out = String.with(delimiter);
		var ch;
		while {
			ch = stream.next;
			ch.notNil and: { ch != delimiter }
		} {
			if(ch == $\\) {
				out = out ++ stream.next;
			} {
				out = out ++ ch;
			}
		};
		if(ch.notNil) {
			^out ++ ch
		} {
			Error("Unclosed " ++ if(delimiter = $') { "symbol" } { "string" }).throw;
		}
	}

	*skipComment { |stream|
		var ch = stream.next, continue;
		var out;
		^switch(ch)
		{ $* } {
			continue = true;
			while {
				ch = stream.next;
				ch.notNil and: { continue }
			} {
				switch(ch)
				{ $* } {
					ch = stream.next;
					if(ch.isNil or: { ch == $/ }) {
						continue = false;
					}
				}
				{ $/ } {
					if(stream.peek == $*) { this.skipComment(stream) };
				}
			};
			stream.rewind(1);
			""  // no need to pass comments through
		}
		{ $/ } {
			while {
				ch = stream.next;
				ch.notNil and: { ch != $\n }
			};
			stream.rewind(1);
			""
		}
		{
			"/" ++ ch
		}
	}
}

+ SequenceableCollection {
	synthArgPPMakeControls {
		var audio, ac;
		var control, cc;
		var lagcontrol, lc;
		var trigcontrol, tc;
		var defaults;
		var which = Array(this.size);
		var arrays, indices;
		var out;

		this.do { |ctl, i|
			switch(ctl[2])
			{ \kr } {
				if(ctl[3].isNumber and: { ctl[3] != 0 }) {
					// fixed numeric lag: can use LagControl
					lagcontrol = lagcontrol.add(ctl);
					which = which.add(2);
				} {
					control = control.add(ctl);
					which = which.add(1);
				};
			}
			{ \ar } {
				audio = audio.add(ctl);
				which = which.add(0);
			}
			{ \tr } {
				trigcontrol = trigcontrol.add(ctl);
				which = which.add(3);
			}
		};

		if(audio.notNil) {
			defaults = audio.synthArgPPDefaults;
			ac = AudioControl.names(audio.synthArgPPNames)
			.ar(defaults.flat)
			.asArray.reshapeLike(defaults);  // needed?
		};
		if(control.notNil) {
			defaults = control.synthArgPPDefaults;
			cc = Control.names(control.synthArgPPNames)
			.kr(defaults.flat)
			.asArray.reshapeLike(defaults);
			control.do { |ctl, i|
				if(ctl[3].notNil) {
					cc[i] = Lag.kr(cc[i], ctl[3]);
				};
			};
		};
		if(lagcontrol.notNil) {
			defaults = lagcontrol.synthArgPPDefaults;
			lc = LagControl.names(lagcontrol.synthArgPPNames)
			.kr(defaults.flat, lagcontrol.synthArgPPDefaults(3).flat)
			.asArray.reshapeLike(defaults);
		};
		if(trigcontrol.notNil) {
			defaults = trigcontrol.synthArgPPDefaults;
			lc = LagControl.names(trigcontrol.synthArgPPNames)
			.kr(defaults.flat)
			.asArray.reshapeLike(defaults);
		};

		arrays = [ac, cc, lc, tc];
		indices = Array.fill(4, 0);
		^this.collect { |ctl, i|
			var one = arrays[which[i]] .at( indices[which[i]] );
			indices[which[i]] = indices[which[i]] + 1;
			one
		};
	}

	synthArgPPNames {
		^this.collect { |ctl|
			if(ctl[1].size > 1) {
				Array.fill(ctl[1].size, '?').put(0, ctl[0])
			} {
				ctl[0]
			}
		}.flat
	}

	synthArgPPDefaults { |index = 1|
		^this.collect { |ctl|
			if(ctl[index].size != ctl[1].size) {
				ctl[index].wrapExtend(ctl[1].size)
			} {
				ctl[index]
			}
		}
	}
}
