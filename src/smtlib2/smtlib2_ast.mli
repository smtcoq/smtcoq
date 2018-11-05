type loc = Lexing.position * Lexing.position
type specconstant =
    SpecConstsDec of loc * string
  | SpecConstNum of loc * string
  | SpecConstString of loc * string
  | SpecConstsHex of loc * string
  | SpecConstsBinary of loc * string
type symbol = Symbol of loc * string | SymbolWithOr of loc * string
type sexpr =
    SexprSpecConst of loc * specconstant
  | SexprSymbol of loc * symbol
  | SexprKeyword of loc * string
  | SexprInParen of loc * (loc * sexpr list)
type attributevalue =
    AttributeValSpecConst of loc * specconstant
  | AttributeValSymbol of loc * symbol
  | AttributeValSexpr of loc * (loc * sexpr list)
type attribute =
    AttributeKeyword of loc * string
  | AttributeKeywordValue of loc * string * attributevalue
type an_option = AnOptionAttribute of loc * attribute
type infoflag = InfoFlagKeyword of loc * string
type identifier =
    IdSymbol of loc * symbol
  | IdUnderscoreSymNum of loc * symbol * (loc * string list)
type sort =
    SortIdentifier of loc * identifier
  | SortIdSortMulti of loc * identifier * (loc * sort list)
type qualidentifier =
    QualIdentifierId of loc * identifier
  | QualIdentifierAs of loc * identifier * sort
type sortedvar = SortedVarSymSort of loc * symbol * sort
type varbinding = VarBindingSymTerm of loc * symbol * term
and term =
    TermSpecConst of loc * specconstant
  | TermQualIdentifier of loc * qualidentifier
  | TermQualIdTerm of loc * qualidentifier * (loc * term list)
  | TermLetTerm of loc * (loc * varbinding list) * term
  | TermForAllTerm of loc * (loc * sortedvar list) * term
  | TermExistsTerm of loc * (loc * sortedvar list) * term
  | TermExclimationPt of loc * term * (loc * attribute list)
type command =
    CSetLogic of loc * symbol
  | CSetOption of loc * an_option
  | CSetInfo of loc * attribute
  | CDeclareSort of loc * symbol * string
  | CDefineSort of loc * symbol * (loc * symbol list) * sort
  | CDeclareFun of loc * symbol * (loc * sort list) * sort
  | CDefineFun of loc * symbol * (loc * sortedvar list) * sort * term
  | CPush of loc * string
  | CPop of loc * string
  | CAssert of loc * term
  | CCheckSat of loc
  | CGetAssert of loc
  | CGetProof of loc
  | CGetUnsatCore of loc
  | CGetValue of loc * (loc * term list)
  | CGetAssign of loc
  | CGetOption of loc * string
  | CGetInfo of loc * infoflag
  | CExit of loc
type commands = Commands of loc * (loc * command list)
val loc_an_option : an_option -> loc
val loc_attribute : attribute -> loc
val loc_attributevalue : attributevalue -> loc
val loc_command : command -> loc
val loc_commands : commands -> loc
val loc_identifier : identifier -> loc
val loc_infoflag : infoflag -> loc
val loc_qualidentifier : qualidentifier -> loc
val loc_sexpr : sexpr -> loc
val loc_sort : sort -> loc
val loc_sortedvar : sortedvar -> loc
val loc_specconstant : specconstant -> loc
val loc_symbol : symbol -> loc
val loc_term : term -> loc
val loc_varbinding : varbinding -> loc
val loc_couple : 'a * 'b -> 'a
val loc_of : commands -> loc
