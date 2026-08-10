//Creates Swift runtime data types (value witness tables, type metadata, context
//descriptors, reflection records) in the /Swift category and optionally applies
//them to the program's Swift reflection sections, mangled symbols, and to
//heuristically located value witness tables.
//@author swift-re
//@category Swift
//@keybinding
//@menupath Analysis.Swift.Add Swift Type Metadata
//@toolbar

import java.util.ArrayList;
import java.util.List;

import ghidra.app.script.GhidraScript;
import ghidra.program.model.address.Address;
import ghidra.program.model.address.AddressSet;
import ghidra.program.model.address.AddressSetView;
import ghidra.program.model.data.ArrayDataType;
import ghidra.program.model.data.CategoryPath;
import ghidra.program.model.data.CharDataType;
import ghidra.program.model.data.DWordDataType;
import ghidra.program.model.data.DataType;
import ghidra.program.model.data.DataTypeConflictHandler;
import ghidra.program.model.data.DataTypeManager;
import ghidra.program.model.data.EnumDataType;
import ghidra.program.model.data.FunctionDefinitionDataType;
import ghidra.program.model.data.ParameterDefinition;
import ghidra.program.model.data.ParameterDefinitionImpl;
import ghidra.program.model.data.PointerType;
import ghidra.program.model.data.PointerTypedef;
import ghidra.program.model.data.StructureDataType;
import ghidra.program.model.data.TerminatedStringDataType;
import ghidra.program.model.data.QWordDataType;
import ghidra.program.model.data.WordDataType;
import ghidra.program.model.data.VoidDataType;
import ghidra.program.model.listing.Data;
import ghidra.program.model.listing.Function;
import ghidra.program.model.listing.Listing;
import ghidra.program.model.mem.Memory;
import ghidra.program.model.mem.MemoryBlock;
import ghidra.program.model.symbol.SourceType;
import ghidra.program.model.symbol.Symbol;
import ghidra.program.model.symbol.SymbolIterator;

/**
 * Teaches Ghidra about the Swift runtime's on-disk data structures.
 *
 * <p>Phase 1 always runs: it builds the data types (sized for the program's
 * pointer size) under the /Swift category. Phase 2 applies them:
 * <ul>
 * <li>walks the __swift5_* / .sw5* reflection sections and lays down context
 * descriptors, field descriptors, associated type / builtin / capture records,
 * and reflection strings, labelling each with the name Swift stored for it;</li>
 * <li>uses mangled symbol suffixes (WV, Mn, MF, Mc, Mp, N) to type value
 * witness tables, nominal type descriptors and type metadata;</li>
 * <li>optionally scans read-only data for value witness table shaped records,
 * which is how you find them in a stripped binary.</li>
 * </ul>
 *
 * Layouts follow swift/ABI/Metadata.h, MetadataValues.h and
 * swift/RemoteInspection/Records.h (Swift 5 stable ABI).
 */
public class SwiftTypeMetadata extends GhidraScript {

	// ---------------------------------------------------------------- config

	private static final String[] SEC_TYPES =
		{ "swift5_types", "swift5_type_metadata", "sw5tymd" };
	private static final String[] SEC_PROTOS =
		{ "swift5_protos", "swift5_protocols", "sw5prt" };
	private static final String[] SEC_PROTO_CONF =
		{ "swift5_proto", "swift5_protocol_conformances", "sw5prtc" };
	private static final String[] SEC_FIELDMD =
		{ "swift5_fieldmd", "sw5flmd" };
	private static final String[] SEC_ASSOCTY =
		{ "swift5_assocty", "sw5asty" };
	private static final String[] SEC_BUILTIN =
		{ "swift5_builtin", "sw5bltn" };
	private static final String[] SEC_CAPTURE =
		{ "swift5_capture", "sw5cptr" };
	private static final String[] SEC_REFLSTR =
		{ "swift5_reflstr", "sw5rfst" };

	/** ContextDescriptorKind, low 5 bits of a context descriptor's flags. */
	private static final int CTX_MODULE = 0;
	private static final int CTX_EXTENSION = 1;
	private static final int CTX_ANONYMOUS = 2;
	private static final int CTX_PROTOCOL = 3;
	private static final int CTX_OPAQUE_TYPE = 4;
	private static final int CTX_CLASS = 16;
	private static final int CTX_STRUCT = 17;
	private static final int CTX_ENUM = 18;

	/** ValueWitnessFlags::HasEnumWitnesses -- table is an EnumValueWitnessTable. */
	private static final int VWT_HAS_ENUM_WITNESSES = 0x00200000;

	// ------------------------------------------------------------------ state

	private DataTypeManager dtm;
	private Listing listing;
	private Memory memory;
	private int ptrSize;

	private CategoryPath CAT_RT;      // /Swift/Runtime
	private CategoryPath CAT_MD;      // /Swift/Metadata
	private CategoryPath CAT_CTX;     // /Swift/Descriptors
	private CategoryPath CAT_REFL;    // /Swift/Reflection

	// primitives
	private DataType U16, U32, U64, SIZE_T, VOIDP, CHARP;

	// runtime
	private DataType MetadataKindEnum, ValueWitnessFlagsEnum;
	private DataType Metadata;
	private DataType ValueWitnessTable, ValueWitnessTableP, EnumValueWitnessTable;

	// "full" metadata records, which start at the value witness table, paired with
	// the offset-pointer typedefs that address them the way Swift code does: at the
	// metadata address point, some way into the record.
	private DataType FullMetadata, FullStructMetadata, FullEnumMetadata, FullClassMetadata;
	private DataType MetadataRef, StructMetadataRef, EnumMetadataRef, ClassMetadataRef;

	// descriptors
	private DataType ContextDescriptor;
	private DataType TypeContextDescriptor, StructDescriptor, EnumDescriptor,
			ClassDescriptor, ProtocolDescriptor, ProtocolConformanceDescriptor,
			ModuleDescriptor, ExtensionDescriptor, AnonymousDescriptor,
			OpaqueTypeDescriptor;

	// reflection
	private DataType FieldDescriptor, FieldRecord, AssociatedTypeDescriptor,
			AssociatedTypeRecord, BuiltinTypeDescriptor, CaptureDescriptor,
			CaptureTypeRecord, MetadataSourceRecord;

	// relative pointers
	private DataType RelVoid, RelChar, RelCtx, RelTypeCtx, RelFieldDesc, RelProtoDesc;

	// counters
	private int nTypes, nFields, nVwt, nConformances, nStrings, nOther, nAccessors;
	private final java.util.Set<Address> seenFieldDescriptors = new java.util.HashSet<>();

	// ------------------------------------------------------------------- main

	@Override
	public void run() throws Exception {
		if (currentProgram == null) {
			printerr("SwiftTypeMetadata: no program is open.");
			return;
		}
		dtm = currentProgram.getDataTypeManager();
		listing = currentProgram.getListing();
		memory = currentProgram.getMemory();
		ptrSize = currentProgram.getDefaultPointerSize();

		// Args: "types-only" | "apply" | "apply+scan". With no args an interactive
		// run asks; a headless one applies without the heuristic scan.
		boolean apply = true;
		boolean heuristic = false;
		String[] args = getScriptArgs();
		if (args != null && args.length > 0) {
			String mode = args[0].trim().toLowerCase();
			apply = !mode.equals("types-only");
			heuristic = mode.equals("apply+scan");
		}
		else if (!isRunningHeadless()) {
			apply = askYesNo("Swift Type Metadata",
				"Types will be added under /Swift.\n\n" +
					"Also apply them to the reflection sections and Swift symbols?");
			if (apply) {
				heuristic = askYesNo("Swift Type Metadata",
					"Also scan read-only data for value witness tables?\n\n" +
						"Useful for stripped binaries; slower, and can produce\n" +
						"the occasional false positive.");
			}
		}

		buildTypes();
		println("SwiftTypeMetadata: created Swift data types under /Swift (pointer size " +
			ptrSize + ").");

		if (apply) {
			applyReflectionSections();
			applyMangledSymbols();
			if (heuristic) {
				scanForValueWitnessTables();
			}
			println("SwiftTypeMetadata: " + nTypes + " type descriptors, " + nFields +
				" field descriptors, " + nConformances + " protocol conformances, " + nVwt +
				" value witness tables, " + nStrings + " reflection strings, " + nOther +
				" metadata records, " + nAccessors + " metadata accessors typed.");
		}
	}

	// ====================================================================
	// Phase 1 -- data type construction
	// ====================================================================

	private void buildTypes() throws Exception {
		CAT_RT = new CategoryPath("/Swift/Runtime");
		CAT_MD = new CategoryPath("/Swift/Metadata");
		CAT_CTX = new CategoryPath("/Swift/Descriptors");
		CAT_REFL = new CategoryPath("/Swift/Reflection");

		// word/dword/qword are Ghidra's fixed-size unsigned integers; the
		// 'int'/'long' types follow the language's data organization instead.
		U16 = WordDataType.dataType;
		U32 = DWordDataType.dataType;
		U64 = QWordDataType.dataType;
		SIZE_T = (ptrSize == 8) ? U64 : U32;
		VOIDP = dtm.getPointer(VoidDataType.dataType);
		CHARP = dtm.getPointer(CharDataType.dataType);

		buildEnums();
		buildValueWitnessTables();
		buildMetadata();
		buildContextDescriptors();
		buildReflectionRecords();
		buildStdlibTypes();
	}

	private void buildEnums() {
		// MetadataKind is a stored-pointer-sized field at offset 0 of every
		// metadata record. For classes it is instead the ObjC isa pointer.
		EnumDataType k = new EnumDataType(CAT_RT, "SwiftMetadataKind", ptrSize, dtm);
		k.add("Class", 0);
		k.add("Struct", 0x200);
		k.add("Enum", 0x201);
		k.add("Optional", 0x202);
		k.add("ForeignClass", 0x203);
		k.add("ForeignReferenceType", 0x204);
		k.add("Opaque", 0x300);
		k.add("Tuple", 0x301);
		k.add("Function", 0x302);
		k.add("Existential", 0x303);
		k.add("Metatype", 0x304);
		k.add("ObjCClassWrapper", 0x305);
		k.add("ExistentialMetatype", 0x306);
		k.add("ExtendedExistential", 0x307);
		k.add("HeapLocalVariable", 0x400);
		k.add("HeapGenericLocalVariable", 0x500);
		k.add("ErrorObject", 0x501);
		k.add("Task", 0x502);
		k.add("Job", 0x503);
		k.setDescription("swift::MetadataKind. 0x200 = non-heap, 0x400 = non-type, " +
			"0x100 = runtime private.");
		MetadataKindEnum = commit(k);

		EnumDataType f = new EnumDataType(CAT_RT, "SwiftValueWitnessFlags", 4, dtm);
		f.add("AlignmentMask", 0x000000FF);
		f.add("IsNonPOD", 0x00010000);
		f.add("IsNonInline", 0x00020000);
		f.add("HasExtraInhabitants_pre5", 0x00040000);
		f.add("HasSpareBits", 0x00080000);
		f.add("IsNonBitwiseTakable", 0x00100000);
		f.add("HasEnumWitnesses", 0x00200000);
		f.add("Incomplete", 0x00400000);
		f.add("IsNonCopyable", 0x00800000);
		f.add("IsNonBitwiseBorrowable", 0x01000000);
		f.add("IsAddressableForDependencies", 0x02000000);
		f.setDescription("swift::TargetValueWitnessFlags. Low byte is (alignment - 1). " +
			"IsNonInline means values are boxed rather than stored in the 3-word buffer.");
		ValueWitnessFlagsEnum = commit(f);

		EnumDataType c = new EnumDataType(CAT_CTX, "SwiftContextDescriptorKind", 1, dtm);
		c.add("Module", CTX_MODULE);
		c.add("Extension", CTX_EXTENSION);
		c.add("Anonymous", CTX_ANONYMOUS);
		c.add("Protocol", CTX_PROTOCOL);
		c.add("OpaqueType", CTX_OPAQUE_TYPE);
		c.add("Class", CTX_CLASS);
		c.add("Struct", CTX_STRUCT);
		c.add("Enum", CTX_ENUM);
		c.setDescription("Low 5 bits of ContextDescriptorFlags.");
		commit(c);

		EnumDataType fd = new EnumDataType(CAT_REFL, "SwiftFieldDescriptorKind", 2, dtm);
		fd.add("Struct", 0);
		fd.add("Class", 1);
		fd.add("Enum", 2);
		fd.add("MultiPayloadEnum", 3);
		fd.add("Protocol", 4);
		fd.add("ClassProtocol", 5);
		fd.add("ObjCProtocol", 6);
		fd.add("ObjCClass", 7);
		commit(fd);

		EnumDataType fr = new EnumDataType(CAT_REFL, "SwiftFieldRecordFlags", 4, dtm);
		fr.add("IsIndirectCase", 0x1);
		fr.add("IsVar", 0x2);
		fr.add("IsArtificial", 0x4);
		commit(fr);

		EnumDataType cf = new EnumDataType(CAT_MD, "SwiftClassFlags", 4, dtm);
		cf.add("IsSwiftPreStableABI", 0x1);
		cf.add("UsesSwiftRefcounting", 0x2);
		cf.add("HasCustomObjCName", 0x4);
		cf.add("IsStaticSpecialization", 0x8);
		cf.add("IsCanonicalStaticSpecialization", 0x10);
		commit(cf);

		EnumDataType tr = new EnumDataType(CAT_CTX, "SwiftTypeReferenceKind", 1, dtm);
		tr.add("DirectTypeDescriptor", 0);
		tr.add("IndirectTypeDescriptor", 1);
		tr.add("DirectObjCClassName", 2);
		tr.add("IndirectObjCClass", 3);
		tr.setDescription("Bits 3-5 of ProtocolConformanceDescriptor.flags.");
		commit(tr);
	}

	private void buildValueWitnessTables() {
		// swift::TargetMetadata -- just the kind word; everything else depends on it.
		StructureDataType md = newStruct(CAT_MD, "SwiftMetadata",
			"Base of every Swift type metadata record. The address of a metadata " +
				"record is its 'address point'; the value witness table pointer lives " +
				"one word *before* it.");
		md.add(MetadataKindEnum, "kind", "MetadataKind, or the ObjC isa pointer for classes");
		Metadata = commit(md);

		// Chicken and egg: the witness signatures want a metadata *reference*, which
		// is an offset pointer into a full metadata record, which starts with a
		// pointer to the witness table. Commit an empty witness table first and fill
		// it in below; REPLACE_HANDLER updates everything already pointing at it.
		DataType vwtShell = commit(newStruct(CAT_RT, "SwiftValueWitnessTable", null));
		ValueWitnessTableP = dtm.getPointer(vwtShell);

		StructureDataType fullMd = newStruct(CAT_MD, "SwiftFullMetadata",
			"swift::FullMetadata -- a metadata record including the header that " +
				"precedes its address point. Type it here, and address it through " +
				"SwiftMetadataRef.");
		fullMd.add(ValueWitnessTableP, "valueWitnesses", null);
		fullMd.add(Metadata, "metadata", "the address point");
		FullMetadata = commit(fullMd);
		MetadataRef = offsetPtr("SwiftMetadataRef", FullMetadata, ptrSize, CAT_MD);

		ParameterDefinition selfP = param("self", MetadataRef);

		DataType initBuf = fnPtr("swift_vw_initializeBufferWithCopyOfBuffer", VOIDP,
			param("dest", VOIDP), param("src", VOIDP), selfP);
		DataType destroy = fnPtr("swift_vw_destroy", VoidDataType.dataType,
			param("object", VOIDP), selfP);
		DataType initCopy = fnPtr("swift_vw_initializeWithCopy", VOIDP,
			param("dest", VOIDP), param("src", VOIDP), selfP);
		DataType assignCopy = fnPtr("swift_vw_assignWithCopy", VOIDP,
			param("dest", VOIDP), param("src", VOIDP), selfP);
		DataType initTake = fnPtr("swift_vw_initializeWithTake", VOIDP,
			param("dest", VOIDP), param("src", VOIDP), selfP);
		DataType assignTake = fnPtr("swift_vw_assignWithTake", VOIDP,
			param("dest", VOIDP), param("src", VOIDP), selfP);
		DataType getSingle = fnPtr("swift_vw_getEnumTagSinglePayload", U32,
			param("instance", VOIDP), param("numEmptyCases", U32), selfP);
		DataType storeSingle = fnPtr("swift_vw_storeEnumTagSinglePayload",
			VoidDataType.dataType, param("instance", VOIDP), param("whichCase", U32),
			param("numEmptyCases", U32), selfP);

		StructureDataType vwt = newStruct(CAT_RT, "SwiftValueWitnessTable",
			"swift::ValueWitnessTable. Referenced from metadata[-1]. Describes how to " +
				"copy, move and destroy values of the type, plus its size/stride/alignment. " +
				"Every struct, enum and class metadata record points at one.");
		vwt.add(initBuf, "initializeBufferWithCopyOfBuffer", null);
		vwt.add(destroy, "destroy", null);
		vwt.add(initCopy, "initializeWithCopy", null);
		vwt.add(assignCopy, "assignWithCopy", null);
		vwt.add(initTake, "initializeWithTake", null);
		vwt.add(assignTake, "assignWithTake", null);
		vwt.add(getSingle, "getEnumTagSinglePayload", null);
		vwt.add(storeSingle, "storeEnumTagSinglePayload", null);
		vwt.add(SIZE_T, "size", "bytes actually used by a value");
		vwt.add(SIZE_T, "stride", "size rounded up to alignment; 1 for empty types");
		vwt.add(ValueWitnessFlagsEnum, "flags", "low byte is (alignment - 1)");
		vwt.add(U32, "extraInhabitantCount", "spare bit patterns usable by enums");
		ValueWitnessTable = commit(vwt);
		ValueWitnessTableP = dtm.getPointer(ValueWitnessTable);

		DataType getTag = fnPtr("swift_vw_getEnumTag", U32, param("instance", VOIDP), selfP);
		DataType project = fnPtr("swift_vw_destructiveProjectEnumData",
			VoidDataType.dataType, param("instance", VOIDP), selfP);
		DataType inject = fnPtr("swift_vw_destructiveInjectEnumTag", VoidDataType.dataType,
			param("instance", VOIDP), param("tag", U32), selfP);

		StructureDataType evwt = newStruct(CAT_RT, "SwiftEnumValueWitnessTable",
			"swift::EnumValueWitnessTable: a value witness table with the three extra " +
				"enum witnesses appended. Used when flags & HasEnumWitnesses (0x200000).");
		evwt.add(ValueWitnessTable, "base", null);
		evwt.add(getTag, "getEnumTag", null);
		evwt.add(project, "destructiveProjectEnumData", null);
		evwt.add(inject, "destructiveInjectEnumTag", null);
		EnumValueWitnessTable = commit(evwt);

		StructureDataType buf = newStruct(CAT_RT, "SwiftValueBuffer",
			"Three-word inline buffer used by existential containers.");
		buf.add(new ArrayDataType(VOIDP, 3, ptrSize), "storage", null);
		commit(buf);

		StructureDataType resp = newStruct(CAT_MD, "SwiftMetadataResponse",
			"swift::MetadataResponse, returned by a generic type metadata accessor in " +
				"the first two return registers.");
		resp.add(MetadataRef, "value", null);
		resp.add(SIZE_T, "state", "MetadataState: 0 = complete, 0x3f = abstract");
		commit(resp);
	}

	private void buildMetadata() {
		// Forward-declare the descriptors as empty structs so metadata can point at
		// them; buildContextDescriptors() fills them in afterwards (REPLACE_HANDLER
		// updates these instances in place).
		StructDescriptor = commit(newStruct(CAT_CTX, "SwiftStructDescriptor", null));
		EnumDescriptor = commit(newStruct(CAT_CTX, "SwiftEnumDescriptor", null));
		ClassDescriptor = commit(newStruct(CAT_CTX, "SwiftClassDescriptor", null));

		StructureDataType sm = newStruct(CAT_MD, "SwiftStructMetadata",
			"swift::StructMetadata. Followed by the field offset vector " +
				"(uint32[numFields]) and, for generic types, the generic arguments.");
		sm.add(MetadataKindEnum, "kind", "MetadataKind.Struct (0x200)");
		sm.add(dtm.getPointer(StructDescriptor), "description", null);
		DataType structMd = commit(sm);

		StructureDataType em = newStruct(CAT_MD, "SwiftEnumMetadata",
			"swift::EnumMetadata. Followed by generic arguments if the enum is generic.");
		em.add(MetadataKindEnum, "kind", "MetadataKind.Enum (0x201) or .Optional (0x202)");
		em.add(dtm.getPointer(EnumDescriptor), "description", null);
		DataType enumMd = commit(em);

		FullStructMetadata = fullMetadata("SwiftFullStructMetadata", structMd, false,
			"Address it through SwiftStructMetadataRef, which is what a struct's type " +
				"metadata accessor returns.");
		StructMetadataRef =
			offsetPtr("SwiftStructMetadataRef", FullStructMetadata, ptrSize, CAT_MD);

		FullEnumMetadata = fullMetadata("SwiftFullEnumMetadata", enumMd, false,
			"Address it through SwiftEnumMetadataRef. An enum's witness table is " +
				"usually a SwiftEnumValueWitnessTable.");
		EnumMetadataRef =
			offsetPtr("SwiftEnumMetadataRef", FullEnumMetadata, ptrSize, CAT_MD);

		StructureDataType cm = newStruct(CAT_MD, "SwiftClassMetadata",
			"swift::ClassMetadata (ObjC-interop layout). Followed by the field offset " +
				"vector, generic arguments and the vtable of immediate members.");
		cm.add(VOIDP, "isa", "ObjC isa; also the metadata kind slot");
		cm.add(VOIDP, "superclass", "SwiftClassMetadata *");
		cm.add(new ArrayDataType(VOIDP, 2, ptrSize), "cacheData", "ObjC method cache");
		cm.add(SIZE_T, "data", "class_ro_t/rw_t pointer; low bit set marks a Swift class");
		cm.add(U32, "flags", "SwiftClassFlags");
		cm.add(U32, "instanceAddressPoint", null);
		cm.add(U32, "instanceSize", null);
		cm.add(U16, "instanceAlignMask", null);
		cm.add(U16, "reserved", null);
		cm.add(U32, "classSize", null);
		cm.add(U32, "classAddressPoint", null);
		cm.add(dtm.getPointer(ClassDescriptor), "description", null);
		cm.add(VOIDP, "ivarDestroyer", null);
		DataType classMd = commit(cm);

		// A class's address point has two words in front of it, not one: the heap
		// object destructor, then the value witness table.
		FullClassMetadata = fullMetadata("SwiftFullClassMetadata", classMd, true,
			"Address it through SwiftClassMetadataRef, which is also the isa of " +
				"every instance of the class.");
		ClassMetadataRef =
			offsetPtr("SwiftClassMetadataRef", FullClassMetadata, 2 * ptrSize, CAT_MD);

		StructureDataType tm = newStruct(CAT_MD, "SwiftTupleMetadata",
			"swift::TupleTypeMetadata, followed by numElements x SwiftTupleElement.");
		tm.add(MetadataKindEnum, "kind", "MetadataKind.Tuple (0x301)");
		tm.add(SIZE_T, "numElements", null);
		tm.add(CHARP, "labels", "space separated label list, or null");
		commit(tm);

		StructureDataType te = newStruct(CAT_MD, "SwiftTupleElement", null);
		te.add(MetadataRef, "type", null);
		te.add(SIZE_T, "offset", null);
		commit(te);

		StructureDataType fm = newStruct(CAT_MD, "SwiftFunctionTypeMetadata",
			"swift::FunctionTypeMetadata; parameter types follow.");
		fm.add(MetadataKindEnum, "kind", "MetadataKind.Function (0x302)");
		fm.add(SIZE_T, "flags", "low 16 bits: parameter count; bits 16-23: convention");
		fm.add(MetadataRef, "resultType", null);
		commit(fm);

		StructureDataType mm = newStruct(CAT_MD, "SwiftMetatypeMetadata", null);
		mm.add(MetadataKindEnum, "kind", "MetadataKind.Metatype (0x304)");
		mm.add(MetadataRef, "instanceType", null);
		commit(mm);

		StructureDataType xm = newStruct(CAT_MD, "SwiftExistentialTypeMetadata",
			"swift::ExistentialTypeMetadata; protocol descriptors follow.");
		xm.add(MetadataKindEnum, "kind", "MetadataKind.Existential (0x303)");
		xm.add(U32, "flags", "numWitnessTables, special protocol, class constraint");
		xm.add(U32, "numProtocols", null);
		commit(xm);

		StructureDataType ow = newStruct(CAT_MD, "SwiftObjCClassWrapperMetadata", null);
		ow.add(MetadataKindEnum, "kind", "MetadataKind.ObjCClassWrapper (0x305)");
		ow.add(VOIDP, "objcClass", null);
		commit(ow);

		StructureDataType fc = newStruct(CAT_MD, "SwiftForeignClassMetadata", null);
		fc.add(MetadataKindEnum, "kind", "MetadataKind.ForeignClass (0x203)");
		fc.add(VOIDP, "description", null);
		fc.add(VOIDP, "superclass", null);
		fc.add(new ArrayDataType(VOIDP, 3, ptrSize), "reserved", null);
		commit(fc);
	}

	private void buildContextDescriptors() {
		// Self-referential: create the empty shell, build the relative pointer to it,
		// then re-commit the full definition.
		DataType ctxShell = commit(newStruct(CAT_CTX, "SwiftContextDescriptor", null));

		RelVoid = relPtr("SwiftRelativeDirectPointer", VoidDataType.dataType, CAT_CTX);
		RelChar = relPtr("SwiftRelativeStringPointer", CharDataType.dataType, CAT_CTX);
		RelCtx = relPtr("SwiftRelativeContextPointer", ctxShell, CAT_CTX);

		StructureDataType ctx = newStruct(CAT_CTX, "SwiftContextDescriptor",
			"swift::TargetContextDescriptor. Base of every context descriptor. " +
				"'parent' is a relative *indirectable* pointer: if its low bit is set, " +
				"the target is a pointer to the descriptor rather than the descriptor.");
		ctx.add(U32, "flags", "low 5 bits: SwiftContextDescriptorKind; bit 7: generic; " +
			"bit 6: unique; bits 8-15: version; bits 16-31: kind specific flags");
		ctx.add(RelCtx, "parent", null);
		ContextDescriptor = commit(ctx);

		// Forward shell for field descriptors (defined for real in buildReflectionRecords).
		DataType fdShell = commit(newStruct(CAT_REFL, "SwiftFieldDescriptor", null));
		RelFieldDesc = relPtr("SwiftRelativeFieldDescriptorPointer", fdShell, CAT_CTX);

		StructureDataType tcd = newStruct(CAT_CTX, "SwiftTypeContextDescriptor",
			"swift::TargetTypeContextDescriptor -- common prefix of the struct, enum " +
				"and class descriptors.");
		addTypeContextPrefix(tcd);
		TypeContextDescriptor = commit(tcd);
		RelTypeCtx = relPtr("SwiftRelativeTypeDescriptorPointer", TypeContextDescriptor, CAT_CTX);

		StructureDataType sd = newStruct(CAT_CTX, "SwiftStructDescriptor",
			"swift::TargetStructDescriptor (context kind 17). Trailing objects: " +
				"generic context, foreign metadata initialization, singleton metadata " +
				"initialization.");
		addTypeContextPrefix(sd);
		sd.add(U32, "numFields", null);
		sd.add(U32, "fieldOffsetVectorOffset", "in words, from the metadata address point");
		StructDescriptor = commit(sd);

		StructureDataType ed = newStruct(CAT_CTX, "SwiftEnumDescriptor",
			"swift::TargetEnumDescriptor (context kind 18).");
		addTypeContextPrefix(ed);
		ed.add(U32, "numPayloadCasesAndPayloadSizeOffset",
			"low 24 bits: payload case count; high 8 bits: payload size offset in words");
		ed.add(U32, "numEmptyCases", null);
		EnumDescriptor = commit(ed);

		StructureDataType cd = newStruct(CAT_CTX, "SwiftClassDescriptor",
			"swift::TargetClassDescriptor (context kind 16). Followed by the generic " +
				"context, resilient superclass, vtable descriptor and method descriptors.");
		addTypeContextPrefix(cd);
		cd.add(RelChar, "superclassType", "mangled name of the superclass, or 0");
		cd.add(U32, "metadataNegativeSizeInWords",
			"or a relative pointer to the resilient metadata bounds");
		cd.add(U32, "metadataPositiveSizeInWords", "or extra class flags when resilient");
		cd.add(U32, "numImmediateMembers", "in words");
		cd.add(U32, "numFields", null);
		cd.add(U32, "fieldOffsetVectorOffset", "in words, from the metadata address point");
		ClassDescriptor = commit(cd);

		StructureDataType mod = newStruct(CAT_CTX, "SwiftModuleDescriptor",
			"swift::TargetModuleContextDescriptor (context kind 0).");
		mod.add(U32, "flags", null);
		mod.add(RelCtx, "parent", null);
		mod.add(RelChar, "name", null);
		ModuleDescriptor = commit(mod);

		StructureDataType ext = newStruct(CAT_CTX, "SwiftExtensionDescriptor",
			"swift::TargetExtensionContextDescriptor (context kind 1).");
		ext.add(U32, "flags", null);
		ext.add(RelCtx, "parent", null);
		ext.add(RelChar, "extendedContext", "mangled name of the extended type");
		ExtensionDescriptor = commit(ext);

		StructureDataType anon = newStruct(CAT_CTX, "SwiftAnonymousContextDescriptor",
			"swift::TargetAnonymousContextDescriptor (context kind 2).");
		anon.add(U32, "flags", null);
		anon.add(RelCtx, "parent", null);
		AnonymousDescriptor = commit(anon);

		StructureDataType pd = newStruct(CAT_CTX, "SwiftProtocolDescriptor",
			"swift::TargetProtocolDescriptor (context kind 3). Followed by the " +
				"requirement signature and the requirement list.");
		pd.add(U32, "flags", null);
		pd.add(RelCtx, "parent", null);
		pd.add(RelChar, "name", null);
		pd.add(U32, "numRequirementsInSignature", null);
		pd.add(U32, "numRequirements", null);
		pd.add(RelChar, "associatedTypeNames", "space separated list, or 0");
		ProtocolDescriptor = commit(pd);
		RelProtoDesc = relPtr("SwiftRelativeProtocolPointer", ProtocolDescriptor, CAT_CTX);

		StructureDataType otd = newStruct(CAT_CTX, "SwiftOpaqueTypeDescriptor",
			"swift::TargetOpaqueTypeDescriptor (context kind 4), e.g. 'some P'.");
		otd.add(U32, "flags", null);
		otd.add(RelCtx, "parent", null);
		OpaqueTypeDescriptor = commit(otd);

		StructureDataType pcd = newStruct(CAT_CTX, "SwiftProtocolConformanceDescriptor",
			"swift::TargetProtocolConformanceDescriptor -- one entry per conformance in " +
				"__swift5_proto. Trailing: retroactive context, conditional requirements, " +
				"resilient witnesses, generic witness table.");
		pcd.add(RelProtoDesc, "protocolDescriptor", "relative indirectable");
		pcd.add(RelVoid, "typeRef",
			"kind given by flags bits 3-5 (SwiftTypeReferenceKind)");
		pcd.add(RelVoid, "witnessTablePattern", null);
		pcd.add(U32, "flags", "bits 3-5: type reference kind; bit 6: retroactive; " +
			"bits 8-15: conditional requirement count");
		ProtocolConformanceDescriptor = commit(pcd);

		StructureDataType mdsc = newStruct(CAT_CTX, "SwiftMethodDescriptor",
			"swift::TargetMethodDescriptor -- one vtable slot of a class descriptor.");
		mdsc.add(U32, "flags", "low 4 bits: method kind; 0x10: instantiated from method");
		mdsc.add(RelVoid, "impl", null);
		commit(mdsc);

		StructureDataType mo = newStruct(CAT_CTX, "SwiftMethodOverrideDescriptor", null);
		mo.add(RelCtx, "cls", null);
		mo.add(RelVoid, "method", null);
		mo.add(RelVoid, "impl", null);
		commit(mo);

		StructureDataType gh = newStruct(CAT_CTX, "SwiftGenericContextDescriptorHeader",
			"Present when the descriptor's flags bit 7 (generic) is set.");
		gh.add(U32, "numParams_numRequirements", "uint16 numParams; uint16 numRequirements");
		gh.add(U16, "numKeyArguments", null);
		gh.add(U16, "numExtra", null);
		commit(gh);

		StructureDataType gr = newStruct(CAT_CTX, "SwiftGenericRequirementDescriptor", null);
		gr.add(U32, "flags", null);
		gr.add(RelChar, "param", "mangled name of the constrained parameter");
		gr.add(RelVoid, "typeOrProtocolOrConformanceOrLayout", null);
		commit(gr);
	}

	/** flags, parent, name, accessFunction, fields -- shared by all type contexts. */
	private void addTypeContextPrefix(StructureDataType s) {
		s.add(U32, "flags", "low 5 bits: SwiftContextDescriptorKind");
		s.add(RelCtx, "parent", "relative indirectable pointer to the enclosing context");
		s.add(RelChar, "name", null);
		s.add(RelVoid, "accessFunction", "metadata accessor, or 0");
		s.add(RelFieldDesc, "fields", "field descriptor in __swift5_fieldmd, or 0");
	}

	private void buildReflectionRecords() {
		StructureDataType fd = newStruct(CAT_REFL, "SwiftFieldDescriptor",
			"swift::reflection::FieldDescriptor from __swift5_fieldmd. Immediately " +
				"followed by numFields x SwiftFieldRecord.");
		fd.add(RelChar, "mangledTypeName", null);
		fd.add(RelChar, "superclass", null);
		fd.add(dtm.getDataType(CAT_REFL, "SwiftFieldDescriptorKind"), "kind", null);
		fd.add(U16, "fieldRecordSize", "always 12");
		fd.add(U32, "numFields", null);
		FieldDescriptor = commit(fd);

		StructureDataType fr = newStruct(CAT_REFL, "SwiftFieldRecord",
			"One stored property, or one enum case.");
		fr.add(dtm.getDataType(CAT_REFL, "SwiftFieldRecordFlags"), "flags", null);
		fr.add(RelChar, "mangledTypeName", "empty for a payload-less enum case");
		fr.add(RelChar, "fieldName", null);
		FieldRecord = commit(fr);

		StructureDataType at = newStruct(CAT_REFL, "SwiftAssociatedTypeDescriptor",
			"From __swift5_assocty; followed by numAssociatedTypes records.");
		at.add(RelChar, "conformingTypeName", null);
		at.add(RelChar, "protocolTypeName", null);
		at.add(U32, "numAssociatedTypes", null);
		at.add(U32, "associatedTypeRecordSize", "always 8");
		AssociatedTypeDescriptor = commit(at);

		StructureDataType ar = newStruct(CAT_REFL, "SwiftAssociatedTypeRecord", null);
		ar.add(RelChar, "name", null);
		ar.add(RelChar, "substitutedTypeName", null);
		AssociatedTypeRecord = commit(ar);

		StructureDataType bt = newStruct(CAT_REFL, "SwiftBuiltinTypeDescriptor",
			"From __swift5_builtin: layout of a primitive/opaque type.");
		bt.add(RelChar, "typeName", null);
		bt.add(U32, "size", null);
		bt.add(U32, "alignmentAndFlags", "bit 31: bitwise takable; low 16 bits: alignment");
		bt.add(U32, "stride", null);
		bt.add(U32, "numExtraInhabitants", null);
		BuiltinTypeDescriptor = commit(bt);

		StructureDataType cap = newStruct(CAT_REFL, "SwiftCaptureDescriptor",
			"From __swift5_capture: the box layout of a closure context. Followed by " +
				"capture type records, then metadata source records.");
		cap.add(U32, "numCaptureTypes", null);
		cap.add(U32, "numMetadataSources", null);
		cap.add(U32, "numBindings", null);
		CaptureDescriptor = commit(cap);

		StructureDataType ctr = newStruct(CAT_REFL, "SwiftCaptureTypeRecord", null);
		ctr.add(RelChar, "mangledTypeName", null);
		CaptureTypeRecord = commit(ctr);

		StructureDataType msr = newStruct(CAT_REFL, "SwiftMetadataSourceRecord", null);
		msr.add(RelChar, "mangledTypeName", null);
		msr.add(RelChar, "mangledMetadataSource", null);
		MetadataSourceRecord = commit(msr);

		StructureDataType mpe = newStruct(CAT_REFL, "SwiftMultiPayloadEnumDescriptor",
			"From __swift5_mpenum; a spare-bit mask follows the header.");
		mpe.add(RelChar, "typeName", null);
		mpe.add(U32, "contentsSizeInWords", null);
		commit(mpe);
	}

	/** A few standard library layouts that make decompiled Swift far more readable. */
	private void buildStdlibTypes() {
		StructureDataType ho = newStruct(CAT_RT, "SwiftHeapObject",
			"swift::HeapObject -- the header of every Swift class instance and box.");
		ho.add(ClassMetadataRef, "metadata",
			"an instance's isa points at the class metadata address point");
		ho.add(SIZE_T, "refCounts", "InlineRefCounts: strong/unowned counts plus flags");
		DataType heapObject = commit(ho);

		StructureDataType str = newStruct(CAT_RT, "SwiftString",
			"Swift.String (64-bit _StringObject). Small strings store up to 15 bytes " +
				"inline; otherwise _object points at a string storage class or literal.");
		str.add(U64, "_countAndFlagsBits", null);
		str.add(VOIDP, "_object", null);
		commit(str);

		StructureDataType arrStorage = newStruct(CAT_RT, "SwiftArrayStorage",
			"_ContiguousArrayStorage header; elements follow, aligned to the element type.");
		arrStorage.add(heapObject, "header", null);
		arrStorage.add(SIZE_T, "count", null);
		arrStorage.add(SIZE_T, "capacityAndFlags", "capacity << 1 | isImmutable");
		DataType storage = commit(arrStorage);

		StructureDataType arr = newStruct(CAT_RT, "SwiftArray",
			"Swift.Array / ContiguousArray -- a single pointer to the array buffer.");
		arr.add(dtm.getPointer(storage), "_buffer", null);
		commit(arr);

		StructureDataType any = newStruct(CAT_RT, "SwiftExistentialContainer",
			"Layout of Any / a protocol-typed value. Witness table pointers follow.");
		any.add(new ArrayDataType(VOIDP, 3, ptrSize), "buffer", null);
		any.add(MetadataRef, "type", null);
		commit(any);

		StructureDataType err = newStruct(CAT_RT, "SwiftError",
			"swift::SwiftError box (native, non-ObjC layout).");
		err.add(heapObject, "header", null);
		err.add(MetadataRef, "type", null);
		err.add(VOIDP, "witnessTable", "Error protocol witness table");
		commit(err);
	}

	// ====================================================================
	// Phase 2 -- applying types to the program
	// ====================================================================

	private void applyReflectionSections() {
		// Each walker is fenced off: a truncated or hand-mangled section should cost
		// us that one section, not the whole run.
		walkSections(SEC_TYPES, b -> walkRelativePointerTable(b, RelTypeCtx, true));
		walkSections(SEC_PROTO_CONF, b -> walkRelativePointerTable(b, RelVoid, false));
		walkSections(SEC_PROTOS, this::walkProtocolTable);
		walkSections(SEC_FIELDMD, this::walkFieldDescriptorSection);
		walkSections(SEC_ASSOCTY, this::walkAssociatedTypeSection);
		walkSections(SEC_BUILTIN, b -> walkFixedRecordSection(b, BuiltinTypeDescriptor));
		walkSections(SEC_CAPTURE, this::walkCaptureSection);
		walkSections(SEC_REFLSTR, this::walkStringSection);
	}

	private interface BlockWalker {
		void walk(MemoryBlock b);
	}

	private void walkSections(String[] names, BlockWalker walker) {
		for (MemoryBlock b : matchingBlocks(names)) {
			monitor.setMessage("Swift: " + b.getName());
			try {
				walker.walk(b);
			}
			catch (Exception e) {
				printerr("SwiftTypeMetadata: stopped walking " + b.getName() + ": " + e);
			}
		}
	}

	/** __swift5_types / __swift5_proto: arrays of int32 relative pointers. */
	private void walkRelativePointerTable(MemoryBlock b, DataType relType,
			boolean typeDescriptors) {
		long count = b.getSize() / 4;
		for (long i = 0; i < count && !monitor.isCancelled(); i++) {
			Address a = b.getStart().add(i * 4);
			applyData(a, relType);
			Address target = relativeTarget(a);
			if (target == null) {
				continue;
			}
			if (typeDescriptors) {
				applyTypeDescriptor(target);
			}
			else {
				applyConformanceDescriptor(target);
			}
		}
	}

	/** __swift5_protos: relative pointers to protocol descriptors. */
	private void walkProtocolTable(MemoryBlock b) {
		long count = b.getSize() / 4;
		for (long i = 0; i < count && !monitor.isCancelled(); i++) {
			Address a = b.getStart().add(i * 4);
			applyData(a, RelProtoDesc);
			Address target = relativeTarget(a);
			if (target == null) {
				continue;
			}
			if (applyData(target, ProtocolDescriptor) != null) {
				nOther++;
				String name = relativeString(target.add(8));
				if (name != null) {
					label(target, qualifiedName(target, name) + ".protocolDescriptor");
				}
			}
		}
	}

	private void applyTypeDescriptor(Address d) {
		int flags;
		try {
			flags = getInt(d);
		}
		catch (Exception e) {
			return;
		}
		int kind = flags & 0x1F;
		DataType dt;
		String suffix;
		switch (kind) {
			case CTX_CLASS:
				dt = ClassDescriptor;
				suffix = ".classDescriptor";
				break;
			case CTX_STRUCT:
				dt = StructDescriptor;
				suffix = ".structDescriptor";
				break;
			case CTX_ENUM:
				dt = EnumDescriptor;
				suffix = ".enumDescriptor";
				break;
			case CTX_PROTOCOL:
				dt = ProtocolDescriptor;
				suffix = ".protocolDescriptor";
				break;
			case CTX_MODULE:
				dt = ModuleDescriptor;
				suffix = ".moduleDescriptor";
				break;
			case CTX_EXTENSION:
				dt = ExtensionDescriptor;
				suffix = ".extensionDescriptor";
				break;
			case CTX_ANONYMOUS:
				dt = AnonymousDescriptor;
				suffix = ".anonymousContext";
				break;
			case CTX_OPAQUE_TYPE:
				dt = OpaqueTypeDescriptor;
				suffix = ".opaqueTypeDescriptor";
				break;
			default:
				return;
		}
		if (applyData(d, dt) == null) {
			return;
		}
		nTypes++;

		String name = null;
		if (kind != CTX_ANONYMOUS && kind != CTX_EXTENSION && kind != CTX_OPAQUE_TYPE) {
			name = relativeString(d.add(8));
		}
		String qualified = (name == null) ? null : qualifiedName(d, name);
		if (qualified != null) {
			label(d, qualified + suffix);
			setPlateComment(d, "Swift " + kindName(kind) + ": " + qualified);
		}

		// Nominal types point at their field descriptor at offset 16.
		if (kind == CTX_CLASS || kind == CTX_STRUCT || kind == CTX_ENUM) {
			Address fields = relativeTarget(d.add(16));
			if (fields != null) {
				applyFieldDescriptor(fields, qualified);
			}
		}
	}

	private void applyConformanceDescriptor(Address c) {
		if (applyData(c, ProtocolConformanceDescriptor) == null) {
			return;
		}
		nConformances++;

		String proto = null;
		Address pd = indirectableTarget(c);
		if (pd != null && isValid(pd)) {
			proto = relativeString(pd.add(8));
		}

		String type = null;
		try {
			int flags = getInt(c.add(12));
			int refKind = (flags >> 3) & 0x7;
			if (refKind == 0 || refKind == 1) {
				Address td = relativeTarget(c.add(4));
				if (refKind == 1 && td != null) {
					td = readPointer(td);
				}
				if (td != null && isValid(td)) {
					String n = relativeString(td.add(8));
					if (n != null) {
						type = qualifiedName(td, n);
					}
				}
			}
			else {
				Address nameAddr = relativeTarget(c.add(4));
				if (refKind == 2 && nameAddr != null) {
					type = readCString(nameAddr);
				}
			}
		}
		catch (Exception e) {
			// leave the conformance unnamed
		}

		if (type != null || proto != null) {
			String n = (type == null ? "unknown" : type) +
				(proto == null ? "" : "." + proto.replace('.', '_')) + ".conformance";
			label(c, n);
			setPlateComment(c, "Swift conformance: " + (type == null ? "?" : type) +
				" : " + (proto == null ? "?" : proto));
		}
	}

	private void applyFieldDescriptor(Address f, String owner) {
		int numFields;
		int recordSize;
		try {
			recordSize = getShort(f.add(10)) & 0xFFFF;
			numFields = getInt(f.add(12));
		}
		catch (Exception e) {
			return;
		}
		if (recordSize != 12 || numFields < 0 || numFields > 0xFFFF) {
			return;
		}
		if (applyData(f, FieldDescriptor) == null) {
			return;
		}
		if (owner != null) {
			label(f, owner + ".fieldDescriptor");
		}
		// __swift5_types reaches most field descriptors, and the __swift5_fieldmd walk
		// reaches all of them, so only count and annotate each one once.
		if (!seenFieldDescriptors.add(f)) {
			return;
		}
		nFields++;
		if (numFields == 0) {
			return;
		}

		Address recs = f.add(16);
		applyData(recs, new ArrayDataType(FieldRecord, numFields, 12));
		for (int i = 0; i < numFields; i++) {
			Address r = recs.add(i * 12L);
			String fieldName = relativeString(r.add(8));
			String typeName = readMangledName(r.add(4));
			if (fieldName != null) {
				String comment = fieldName;
				if (typeName != null && !typeName.isEmpty()) {
					comment += " : " + typeName;
				}
				setEOLComment(r, comment);
			}
		}
	}

	/** __swift5_fieldmd holds variable length records; walk them in order. */
	private void walkFieldDescriptorSection(MemoryBlock b) {
		Address a = b.getStart();
		Address end = b.getEnd();
		while (a.compareTo(end) < 0 && !monitor.isCancelled()) {
			int numFields;
			int recordSize;
			try {
				recordSize = getShort(a.add(10)) & 0xFFFF;
				numFields = getInt(a.add(12));
			}
			catch (Exception e) {
				return;
			}
			if (recordSize != 12 || numFields < 0 || numFields > 0xFFFF) {
				return; // out of sync; the descriptors reached from __swift5_types stand
			}
			// Only fall back to the mangled type name when __swift5_types has not
			// already given this descriptor a demangled label.
			String owner = null;
			if (currentProgram.getSymbolTable().getSymbols(a).length == 0) {
				String mangled = readMangledName(a);
				if (mangled != null && !mangled.isEmpty()) {
					owner = "swift_" + sanitize(mangled);
				}
			}
			applyFieldDescriptor(a, owner);
			a = a.add(16L + 12L * numFields);
		}
	}

	private void walkAssociatedTypeSection(MemoryBlock b) {
		Address a = b.getStart();
		Address end = b.getEnd();
		while (a.compareTo(end) < 0 && !monitor.isCancelled()) {
			int num;
			int recSize;
			try {
				num = getInt(a.add(8));
				recSize = getInt(a.add(12));
			}
			catch (Exception e) {
				return;
			}
			if (recSize != 8 || num < 0 || num > 0xFFFF) {
				return;
			}
			if (applyData(a, AssociatedTypeDescriptor) == null) {
				return;
			}
			nOther++;
			if (num > 0) {
				applyData(a.add(16), new ArrayDataType(AssociatedTypeRecord, num, 8));
				for (int i = 0; i < num; i++) {
					Address r = a.add(16L + 8L * i);
					String n = readMangledName(r);
					String sub = readMangledName(r.add(4));
					if (n != null) {
						setEOLComment(r, n + (sub == null ? "" : " = " + sub));
					}
				}
			}
			a = a.add(16L + 8L * num);
		}
	}

	private void walkCaptureSection(MemoryBlock b) {
		Address a = b.getStart();
		Address end = b.getEnd();
		while (a.compareTo(end) < 0 && !monitor.isCancelled()) {
			int nCapture;
			int nSources;
			int nBindings;
			try {
				nCapture = getInt(a);
				nSources = getInt(a.add(4));
				nBindings = getInt(a.add(8));
			}
			catch (Exception e) {
				return;
			}
			if (nCapture < 0 || nCapture > 0xFFFF || nSources < 0 || nSources > 0xFFFF ||
				nBindings < 0 || nBindings > 0xFFFF) {
				return;
			}
			if (applyData(a, CaptureDescriptor) == null) {
				return;
			}
			nOther++;
			Address p = a.add(12);
			if (nCapture > 0) {
				applyData(p, new ArrayDataType(CaptureTypeRecord, nCapture, 4));
				p = p.add(4L * nCapture);
			}
			if (nSources > 0) {
				applyData(p, new ArrayDataType(MetadataSourceRecord, nSources, 8));
				p = p.add(8L * nSources);
			}
			a = p;
		}
	}

	private void walkFixedRecordSection(MemoryBlock b, DataType record) {
		int len = record.getLength();
		if (len <= 0) {
			return;
		}
		long count = b.getSize() / len;
		for (long i = 0; i < count && !monitor.isCancelled(); i++) {
			Address a = b.getStart().add(i * len);
			if (applyData(a, record) != null) {
				nOther++;
				String n = readMangledName(a);
				if (n != null && !n.isEmpty()) {
					setEOLComment(a, n);
				}
			}
		}
	}

	private void walkStringSection(MemoryBlock b) {
		Address a = b.getStart();
		Address end = b.getEnd();
		while (a.compareTo(end) <= 0 && !monitor.isCancelled()) {
			String s = readCString(a);
			if (s == null) {
				return;
			}
			if (s.isEmpty()) {
				a = a.add(1);
				continue;
			}
			if (applyString(a, s) != null) {
				nStrings++;
			}
			a = a.add(s.length() + 1L);
		}
	}

	// ---------------------------------------------------------- symbol driven

	/**
	 * Uses Swift name mangling suffixes to find the runtime records:
	 * WV = value witness table, N = type metadata, Mn = nominal type descriptor,
	 * Mp = protocol descriptor, Mc = conformance descriptor, MF = field descriptor.
	 */
	private void applyMangledSymbols() {
		SymbolIterator it = currentProgram.getSymbolTable().getDefinedSymbols();
		while (it.hasNext() && !monitor.isCancelled()) {
			Symbol s = it.next();
			String name = s.getName();
			if (name == null || name.length() < 4) {
				continue;
			}
			int dollar = name.indexOf("$s");
			if (dollar < 0) {
				dollar = name.indexOf("$S");
			}
			if (dollar < 0 || dollar > 1) {
				continue; // not a Swift 4.2+/5 mangled symbol
			}
			Address a = s.getAddress();
			if (!isValid(a)) {
				continue;
			}
			try {
				applyMangledSymbol(a, name.substring(dollar));
			}
			catch (Exception e) {
				printerr("SwiftTypeMetadata: " + name + " at " + a + ": " + e);
			}
		}
	}

	private void applyMangledSymbol(Address a, String base) {
		if (base.endsWith("WV")) {
			applyValueWitnessTable(a, trimMangled(base, 2));
		}
		else if (base.endsWith("Mn")) {
			applyTypeDescriptor(a);
		}
		else if (base.endsWith("Mp")) {
			if (applyData(a, ProtocolDescriptor) != null) {
				nOther++;
			}
		}
		else if (base.endsWith("Mc")) {
			applyConformanceDescriptor(a);
		}
		else if (base.endsWith("MF")) {
			applyFieldDescriptor(a, null);
		}
		else if (base.endsWith("Ma")) {
			typeMetadataAccessor(a, base);
		}
		else if (base.endsWith("N") && base.length() >= 2) {
			// A metadata symbol points at the record's address point, so the full
			// record starts one word earlier (two, for a class).
			char nominal = base.charAt(base.length() - 2);
			DataType full = fullMetadataFor(nominal);
			if (full == null) {
				return;
			}
			int headerSize = (nominal == 'C') ? 2 * ptrSize : ptrSize;
			Address start = a.subtract(headerSize);
			if (!isValid(start) || applyData(start, full) == null) {
				return;
			}
			nOther++;
			Address vwt = readPointer(a.subtract(ptrSize));
			if (vwt != null && isValid(vwt)) {
				applyValueWitnessTable(vwt, trimMangled(base, 1));
			}
		}
	}

	private DataType fullMetadataFor(char nominal) {
		switch (nominal) {
			case 'V':
				return FullStructMetadata;
			case 'O':
				return FullEnumMetadata;
			case 'C':
				return FullClassMetadata;
			default:
				return null;
		}
	}

	private DataType metadataRefFor(char nominal) {
		switch (nominal) {
			case 'V':
				return StructMetadataRef;
			case 'O':
				return EnumMetadataRef;
			case 'C':
				return ClassMetadataRef;
			default:
				return MetadataRef;
		}
	}

	/**
	 * Gives a type metadata accessor ("...Ma") a return type of the matching
	 * metadata reference, so every caller that stashes the result decompiles with
	 * the witness table reachable at [-1].
	 *
	 * <p>Generic accessors really return a two-word MetadataResponse in the first
	 * two return registers; the metadata pointer is the first of those, and typing
	 * the return as that pointer is what makes call sites readable.
	 */
	private void typeMetadataAccessor(Address a, String base) {
		Function fn = getFunctionAt(a);
		if (fn == null) {
			// A "...Ma" symbol is always a function. Ghidra's analysis normally has
			// one here already; make it if the program has not been analysed yet.
			MemoryBlock block = memory.getBlock(a);
			if (block == null || !block.isExecute()) {
				return;
			}
			try {
				if (listing.getInstructionAt(a) == null) {
					disassemble(a);
				}
				fn = createFunction(a, null);
			}
			catch (Exception e) {
				return;
			}
			if (fn == null) {
				return;
			}
		}
		DataType ref = metadataRefFor(
			base.length() >= 3 ? base.charAt(base.length() - 3) : '?');
		try {
			fn.setReturnType(ref, SourceType.ANALYSIS);
			nAccessors++;
		}
		catch (Exception e) {
			// leave the accessor alone if its signature is locked
		}
	}

	/** Applies the plain or enum-flavoured witness table and names its witnesses. */
	private void applyValueWitnessTable(Address a, String prefix) {
		int flags;
		try {
			flags = getInt(a.add(10L * ptrSize));
		}
		catch (Exception e) {
			return;
		}
		DataType dt = ((flags & VWT_HAS_ENUM_WITNESSES) != 0) ? EnumValueWitnessTable
				: ValueWitnessTable;
		if (applyData(a, dt) == null) {
			return;
		}
		nVwt++;
		if (prefix != null) {
			label(a, prefix + ".valueWitnessTable");
			setPlateComment(a, "Swift value witness table" +
				((flags & VWT_HAS_ENUM_WITNESSES) != 0 ? " (with enum witnesses)" : ""));
			nameWitnessFunctions(a, prefix, (flags & VWT_HAS_ENUM_WITNESSES) != 0);
		}
	}

	private static final String[] WITNESS_NAMES = { "initializeBufferWithCopyOfBuffer",
		"destroy", "initializeWithCopy", "assignWithCopy", "initializeWithTake",
		"assignWithTake", "getEnumTagSinglePayload", "storeEnumTagSinglePayload" };

	private static final String[] ENUM_WITNESS_NAMES =
		{ "getEnumTag", "destructiveProjectEnumData", "destructiveInjectEnumTag" };

	private void nameWitnessFunctions(Address vwt, String prefix, boolean isEnum) {
		int total = WITNESS_NAMES.length + (isEnum ? ENUM_WITNESS_NAMES.length : 0);
		for (int i = 0; i < total; i++) {
			// The eight function witnesses come first; the enum witnesses are appended
			// after size, stride, flags and extraInhabitantCount.
			long off = (i < WITNESS_NAMES.length) ? (long) i * ptrSize
					: 10L * ptrSize + 8L + (long) (i - WITNESS_NAMES.length) * ptrSize;
			String witness = (i < WITNESS_NAMES.length) ? WITNESS_NAMES[i]
					: ENUM_WITNESS_NAMES[i - WITNESS_NAMES.length];
			Address slot = vwt.add(off);
			Address target = readPointer(slot);
			if (target == null || !isValid(target)) {
				continue;
			}
			Function fn = getFunctionAt(target);
			if (fn == null) {
				continue;
			}
			if (fn.getSymbol() != null && fn.getSymbol().getSource() == SourceType.DEFAULT) {
				try {
					fn.setName(prefix + "." + witness, SourceType.ANALYSIS);
				}
				catch (Exception e) {
					// name clash; the plate comment below still identifies it
				}
			}
			String plate = getPlateComment(target);
			String note = "Swift value witness '" + witness + "' for " + prefix;
			if (plate == null) {
				setPlateComment(target, note);
			}
			else if (!plate.contains(note)) {
				setPlateComment(target, plate + "\n" + note);
			}
		}
	}

	// ------------------------------------------------------------- heuristics

	/**
	 * Finds value witness tables that have no symbol, which is the usual case in a
	 * stripped binary: eight code pointers followed by a self-consistent
	 * size / stride / alignment triple. stride must equal size rounded up to the
	 * alignment, which keeps false positives rare.
	 *
	 * <p>Data blocks are read in bulk and screened with plain integer arithmetic;
	 * only a candidate that survives that costs an Address allocation or a memory
	 * manager call. Scanning a 60MB binary a word at a time the naive way does not
	 * finish in reasonable time or memory.
	 */
	private void scanForValueWitnessTables() {
		AddressSetView exec = memory.getExecuteSet();
		int vwtLen = ValueWitnessTable.getLength();
		boolean bigEndian = currentProgram.getLanguage().isBigEndian();
		int chunkSize = 1 << 20;
		byte[] buf = new byte[chunkSize + vwtLen];

		for (MemoryBlock b : memory.getBlocks()) {
			if (!b.isInitialized() || b.isExecute() || b.getSize() < vwtLen) {
				continue;
			}
			monitor.setMessage("Swift: scanning " + b.getName() + " for value witness tables");
			long blockSize = b.getSize();
			for (long base = 0; base + vwtLen <= blockSize && !monitor.isCancelled();
					base += chunkSize) {
				int want = (int) Math.min(buf.length, blockSize - base);
				int got;
				try {
					got = memory.getBytes(b.getStart().add(base), buf, 0, want);
				}
				catch (Exception e) {
					break;
				}
				for (int off = 0; off + vwtLen <= got; off += ptrSize) {
					if (!layoutLooksLikeValueWitnessTable(buf, off, bigEndian)) {
						continue;
					}
					Address a = b.getStart().add(base + off);
					if (!witnessesPointAtCode(buf, off, bigEndian, exec)) {
						continue;
					}
					if (listing.getDefinedData(new AddressSet(a, a.add(vwtLen - 1)), true)
							.hasNext()) {
						continue; // already typed, e.g. by the symbol pass
					}
					applyValueWitnessTable(a, null);
					label(a, "swift_valueWitnessTable_" + a);
					off += vwtLen - ptrSize;
				}
			}
		}
	}

	/** The cheap screen: size, stride, alignment and flags must agree. */
	private boolean layoutLooksLikeValueWitnessTable(byte[] buf, int off, boolean bigEndian) {
		long size = word(buf, off + 8 * ptrSize, bigEndian);
		long stride = word(buf, off + 9 * ptrSize, bigEndian);
		if (size < 0 || size > 0x1000000 || stride <= 0 || stride > 0x1000000) {
			return false;
		}
		int flags = (int) dword(buf, off + 10 * ptrSize, bigEndian);
		if ((flags & 0xFC000000) != 0) {
			return false;
		}
		long align = flags & 0xFF;
		if (((align + 1) & align) != 0) {
			return false; // the alignment mask has to be 2^n - 1
		}
		long expected = (size + align) & ~align;
		if (expected == 0) {
			expected = 1; // an empty type still has stride 1
		}
		if (stride != expected) {
			return false;
		}
		long extraInhabitants = dword(buf, off + 10 * ptrSize + 4, bigEndian);
		return extraInhabitants <= 0x7FFFFFFFL;
	}

	/** The expensive confirmation: all eight witnesses must land in executable memory. */
	private boolean witnessesPointAtCode(byte[] buf, int off, boolean bigEndian,
			AddressSetView exec) {
		for (int i = 0; i < 8; i++) {
			long v = word(buf, off + i * ptrSize, bigEndian);
			if (v == 0) {
				return false;
			}
			try {
				if (!exec.contains(toAddr(v))) {
					return false;
				}
			}
			catch (Exception e) {
				return false;
			}
		}
		return true;
	}

	private long word(byte[] buf, int off, boolean bigEndian) {
		return (ptrSize == 8) ? qword(buf, off, bigEndian) : dword(buf, off, bigEndian);
	}

	private long dword(byte[] buf, int off, boolean bigEndian) {
		long v = 0;
		if (bigEndian) {
			for (int i = 0; i < 4; i++) {
				v = (v << 8) | (buf[off + i] & 0xFFL);
			}
		}
		else {
			for (int i = 3; i >= 0; i--) {
				v = (v << 8) | (buf[off + i] & 0xFFL);
			}
		}
		return v;
	}

	private long qword(byte[] buf, int off, boolean bigEndian) {
		long v = 0;
		if (bigEndian) {
			for (int i = 0; i < 8; i++) {
				v = (v << 8) | (buf[off + i] & 0xFFL);
			}
		}
		else {
			for (int i = 7; i >= 0; i--) {
				v = (v << 8) | (buf[off + i] & 0xFFL);
			}
		}
		return v;
	}

	// ====================================================================
	// helpers
	// ====================================================================

	private StructureDataType newStruct(CategoryPath cp, String name, String description) {
		StructureDataType s = new StructureDataType(cp, name, 0, dtm);
		if (description != null) {
			s.setDescription(description);
		}
		return s;
	}

	private DataType commit(DataType dt) {
		return dtm.addDataType(dt, DataTypeConflictHandler.REPLACE_HANDLER);
	}

	private ParameterDefinition param(String name, DataType dt) {
		return new ParameterDefinitionImpl(name, dt, null);
	}

	private DataType fnPtr(String name, DataType ret, ParameterDefinition... params) {
		FunctionDefinitionDataType f = new FunctionDefinitionDataType(CAT_RT, name, dtm);
		f.setReturnType(ret);
		f.setArguments(params);
		return dtm.getPointer(commit(f));
	}

	/**
	 * Builds a "full" metadata record: the header that precedes the address point,
	 * followed by the metadata proper. Heap (class) metadata carries an extra
	 * destructor word ahead of the value witness table.
	 */
	private DataType fullMetadata(String name, DataType metadata, boolean heap,
			String extraDoc) {
		StructureDataType s = newStruct(CAT_MD, name,
			"A complete " + metadata.getName() + " record, starting at the header " +
				"rather than at the address point. Swift code addresses this through " +
				"an offset pointer, so the value witness table shows up as a negative " +
				"offset from the metadata pointer. " + extraDoc);
		if (heap) {
			s.add(VOIDP, "destroy", "heap object destructor, at metadata[-2]");
		}
		s.add(ValueWitnessTableP, "valueWitnesses", "at metadata[-1]");
		s.add(metadata, "metadata", "the address point");
		return commit(s);
	}

	/**
	 * An offset pointer: a pointer whose value lands {@code componentOffset} bytes
	 * into {@code base} rather than at its start. The decompiler resolves accesses
	 * on both sides of that point, which is what turns the load at
	 * {@code metadata[-1]} into a named valueWitnesses field.
	 */
	private DataType offsetPtr(String name, DataType base, long componentOffset,
			CategoryPath cp) {
		// A PointerTypedef takes its description from the type it points at, and
		// throws if you try to set one, so the explanation lives on that struct.
		PointerTypedef td = new PointerTypedef(name, base, ptrSize, dtm, componentOffset);
		try {
			td.setCategoryPath(cp);
		}
		catch (Exception e) {
			// keep the default category
		}
		return commit(td);
	}

	/**
	 * A Swift relative direct pointer: a 32 bit offset from the field's own address.
	 * Ghidra's RELATIVE pointer typedef models exactly this, so the listing resolves
	 * and cross references the target for free.
	 */
	private DataType relPtr(String name, DataType target, CategoryPath cp) {
		PointerTypedef td = new PointerTypedef(name, target, 4, dtm, PointerType.RELATIVE);
		try {
			td.setCategoryPath(cp);
		}
		catch (Exception e) {
			// keep the default category
		}
		return commit(td);
	}

	private List<MemoryBlock> matchingBlocks(String[] names) {
		List<MemoryBlock> out = new ArrayList<>();
		for (MemoryBlock b : memory.getBlocks()) {
			if (!b.isInitialized()) {
				continue;
			}
			String n = b.getName().toLowerCase();
			for (String want : names) {
				if (n.contains(want)) {
					out.add(b);
					break;
				}
			}
		}
		return out;
	}

	private boolean isValid(Address a) {
		if (a == null) {
			return false;
		}
		MemoryBlock b = memory.getBlock(a);
		return b != null && b.isInitialized();
	}

	/** Resolves a relative direct pointer stored at {@code at}. */
	private Address relativeTarget(Address at) {
		try {
			int off = getInt(at);
			if (off == 0) {
				return null;
			}
			Address t = at.add(off);
			return isValid(t) ? t : null;
		}
		catch (Exception e) {
			return null;
		}
	}

	/** Resolves a relative *indirectable* pointer: low bit set means one more hop. */
	private Address indirectableTarget(Address at) {
		try {
			int off = getInt(at);
			if (off == 0) {
				return null;
			}
			boolean indirect = (off & 1) != 0;
			Address t = at.add(off & ~1);
			if (!isValid(t)) {
				return null;
			}
			return indirect ? readPointer(t) : t;
		}
		catch (Exception e) {
			return null;
		}
	}

	private String relativeString(Address at) {
		Address t = relativeTarget(at);
		return (t == null) ? null : readCString(t);
	}

	/**
	 * Mangled type names in __swift5_typeref may embed symbolic references: a byte
	 * in 0x01-0x1F followed by a relative pointer to the referenced descriptor,
	 * instead of spelling the type out. Those bytes are not text, so report the name
	 * as unavailable rather than pasting binary into a comment.
	 */
	private String readMangledName(Address at) {
		String s = relativeString(at);
		if (s == null) {
			return null;
		}
		for (int i = 0; i < s.length(); i++) {
			if (s.charAt(i) < 0x20) {
				return null;
			}
		}
		return s;
	}

	private Address readPointer(Address at) {
		try {
			long v = (ptrSize == 8) ? getLong(at) : (getInt(at) & 0xFFFFFFFFL);
			if (v == 0) {
				return null;
			}
			return toAddr(v);
		}
		catch (Exception e) {
			return null;
		}
	}

	private String readCString(Address a) {
		if (!isValid(a)) {
			return null;
		}
		StringBuilder sb = new StringBuilder();
		try {
			for (int i = 0; i < 1024; i++) {
				byte b = memory.getByte(a.add(i));
				if (b == 0) {
					return sb.toString();
				}
				sb.append((char) (b & 0xFF));
			}
		}
		catch (Exception e) {
			return null;
		}
		return sb.toString();
	}

	/** Walks the parent chain to build Module.Type.Nested style names. */
	private String qualifiedName(Address descriptor, String leaf) {
		StringBuilder sb = new StringBuilder(leaf);
		Address ctx = descriptor;
		for (int depth = 0; depth < 8; depth++) {
			Address parent = indirectableTarget(ctx.add(4));
			if (parent == null || !isValid(parent)) {
				break;
			}
			int flags;
			try {
				flags = getInt(parent);
			}
			catch (Exception e) {
				break;
			}
			int kind = flags & 0x1F;
			if (kind == CTX_ANONYMOUS || kind == CTX_EXTENSION) {
				break;
			}
			String pname = relativeString(parent.add(8));
			if (pname == null || pname.isEmpty()) {
				break;
			}
			sb.insert(0, pname + ".");
			if (kind == CTX_MODULE) {
				break;
			}
			ctx = parent;
		}
		return sanitize(sb.toString());
	}

	private String kindName(int kind) {
		switch (kind) {
			case CTX_CLASS:
				return "class";
			case CTX_STRUCT:
				return "struct";
			case CTX_ENUM:
				return "enum";
			case CTX_PROTOCOL:
				return "protocol";
			case CTX_MODULE:
				return "module";
			case CTX_EXTENSION:
				return "extension";
			case CTX_OPAQUE_TYPE:
				return "opaque type";
			default:
				return "context";
		}
	}

	/** Drops a mangling suffix and the leading '$s' so labels stay readable. */
	private String trimMangled(String mangled, int suffixLen) {
		String s = mangled.substring(0, mangled.length() - suffixLen);
		if (s.startsWith("$s") || s.startsWith("$S")) {
			s = s.substring(2);
		}
		return "swift_" + sanitize(s);
	}

	private String sanitize(String s) {
		StringBuilder sb = new StringBuilder(s.length());
		for (int i = 0; i < s.length(); i++) {
			char c = s.charAt(i);
			sb.append((Character.isLetterOrDigit(c) || c == '_' || c == '.' || c == '$') ? c
					: '_');
		}
		return sb.toString();
	}

	private Data applyData(Address addr, DataType dt) {
		if (addr == null || dt == null || !isValid(addr)) {
			return null;
		}
		int len = dt.getLength();
		if (len <= 0) {
			return null;
		}
		try {
			Address end = addr.add(len - 1);
			if (!isValid(end)) {
				return null;
			}
			Data existing = listing.getDataAt(addr);
			if (existing != null && existing.isDefined() &&
				existing.getDataType().isEquivalent(dt)) {
				return existing;
			}
			AddressSet range = new AddressSet(addr, end);
			if (listing.getInstructions(range, true).hasNext()) {
				return null; // never clobber code
			}
			listing.clearCodeUnits(addr, end, false);
			return listing.createData(addr, dt);
		}
		catch (Exception e) {
			return null;
		}
	}

	private Data applyString(Address addr, String s) {
		try {
			Address end = addr.add(s.length());
			if (!isValid(end)) {
				return null;
			}
			Data existing = listing.getDataAt(addr);
			if (existing != null && existing.isDefined() &&
				existing.getDataType() instanceof TerminatedStringDataType) {
				return existing;
			}
			AddressSet range = new AddressSet(addr, end);
			if (listing.getInstructions(range, true).hasNext()) {
				return null;
			}
			listing.clearCodeUnits(addr, end, false);
			return listing.createData(addr, TerminatedStringDataType.dataType);
		}
		catch (Exception e) {
			return null;
		}
	}

	private void label(Address a, String name) {
		if (a == null || name == null || name.isEmpty()) {
			return;
		}
		String clean = sanitize(name);
		for (Symbol s : currentProgram.getSymbolTable().getSymbols(a)) {
			if (s.getName().equals(clean)) {
				return;
			}
		}
		try {
			createLabel(a, clean, false, SourceType.ANALYSIS);
		}
		catch (Exception e) {
			// duplicate or invalid name; not worth failing the run over
		}
	}
}
