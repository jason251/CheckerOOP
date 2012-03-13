//---------------------------------------------------------------------------


#pragma hdrstop

#include "uProver.h"

//---------------------------------------------------------------------------

#pragma package(smart_init)


unit uProver;

interface

uses
   uTermsAndFormulasStructures, uHashingTablesArray, Classes, Dialogs;

const
  byCTablesCount       = 5; // количество таблиц
  byCVariablesTable    = 1; // таблица имен переменных
  byCIntegersTable     = 2; // таблица целых в строковом представлении
  byCRealsTable        = 3; // таблица вещественных в строковом представлении
  byCStringsTable      = 4; // таблица строк
  byCPredicatesTable   = 5; // таблица имен предикатов

type
  // Типовый квантор
  //----------------------------------------------------------//
  TadrQuantifier = ^TQuantifier;
  TQuantifier = record
				   boolFUnQuan: Boolean; // Знак квантора
				   arFVariables: TArrayOfadrVariable;
				   arFTypeCondition: TArrayOfadrAtom;

				   adrFSon, adrFBrother: TadrQuantifier;
				end;
  //----------------------------------------------------------//





  // Вопрос
  TadrQuestion = ^TQuestion;
  TQuestion = record
				 adrFQuan: TadrQuantifier; // ссылка на подформулу,
										   // adrFQuan - квантор-вопрос
				 objFAnswersTable: TAnswersTable;
			  end;


  // База
  TadrBase = ^TBase;
  TBase = record
			 arFVariables: TArrayOfadrVariable;
			 objFAtomsTable: TAtomsTable;
			 arFQuestions: array of TadrQuestion;

			 adrFNextBase: TadrBase;
		  end;


  // Блок хранения
  TStorageBlock = record
					 htaFTermsPredicates: THashingTablesArray;
					 adrFFirstBase: TadrBase;
					 adrFFirstQuestQuan, adrFLastQuestQuan: TadrQuantifier;
				  end;

  TStackOfBases = class

  end;


  TProver = class
  private
	 FStorageBlock: TStorageBlock;

	 // ссылка на поле вывода
	 stgsFOutput: TStrings;

	 // поля для сбора статистической информации
	 intFRuleOfInferenceCount: Integer;
	 intFBaseIndex: Integer;
	 intFBasesCount: Integer;

	 cardFTimeEnd: Cardinal; // Время завершения доказательства
	 cardFTimeCurrent: Cardinal;

	 boolFDWS_DTQVis: Boolean;
	 boolFRuleOfInferenceVis: Boolean;
	 boolFRefutVis: Boolean;
	 boolFDisplayBasesOnly: Boolean;
	 boolFkRefutationStrategy: Boolean;

	 //----------------------------------//
	 boolFEnableDisjunctiveBranching: Boolean;
	 boolFAnswered: Boolean;
	 boolFkRefutationInProcess: Boolean;
	 intFRejectedBranchings: Integer;
	 //----------------------------------//

	 procedure Init(adrAFormulaRoot: TadrQuantifier);

	 function RefuteBase(adrABase: TadrBase;
						 intAStepsMax: Integer): Boolean;

	 function Strategy(adrABase: TadrBase;
					   var intAQuestionIndex: Integer): Boolean;

	 function AddNewAnswers(adrABase: TadrBase;
							intAQuestionIndex: Integer): Boolean;
	 function ApplyRuleOfInference(adrABase: TadrBase;
								   intAQuestionIndex: Integer): Boolean;
	 function DuplicateWithSpecification(adrABase: TadrBase;
										 intAQuestionIndex: Integer): Integer;
	 function DeleteTrivialQuestion(adrABase: TadrBase;
									intATrivQuestIndex: Integer;
									boolADeleteTrivQuestion,
									boolAQuestInStorageBlock: Boolean): Boolean;
	 function QuestionHasAnswers(adrABase: TadrBase;
								 intAQuestionIndex: Integer): Boolean;
	 function CopyBase(adrASourceBase: TadrBase): TadrBase;
	 function CopyFormula(adrARoot: TadrQuantifier): TadrQuantifier;
	 function CopyAnswerQueue(const AAnswerQueue: TAnswerQueue): TAnswerQueue;
	 function CopyTypeCondition(const arATypeCondition: TArrayOfadrAtom): TArrayOfadrAtom;
	 function DereferencingVariable(adrAVariable: TadrVariable): TadrVariable;
	 function SearchTermInVariablesOfQuantifier(const ATerm: TTerm;
												adrAQuantifier: TadrQuantifier): Integer;
	 function RepeatedAnswer(const arAAnswerSubstitution: TArrayOfTerm;
							 adrAQuestion: TadrQuestion): Boolean;
	 procedure InitAnswerQueue(var AAnswerQueue: TAnswerQueue);
	 procedure AnswerToQueue(const arAAnswerSubstitution: TArrayOfTerm;
							 var AAnswerQueue: TAnswerQueue;
							 boolAToEnd: Boolean);

	 function TermsIsConstants(const arATerms: TArrayOfTerm): Boolean;
	 function CalculatePredicate(adrAAtom: TadrAtom;
								 const arASubstitutionConstants: TArrayOfTerm): Boolean;

	 function VariablesAsString(const arAVariables: TArrayOfadrVariable): AnsiString;
	 function SimpleTermAsString(const ATerm: TTerm): AnsiString;
	 function TermVariantsAsString(adrATermVariants: TadrTermVariants): AnsiString;
	 function TermAsString(const ATerm: TTerm): AnsiString;
	 function AtomAsString(const AAtom: TAtom): AnsiString;
	 function TypeConditionAsString(const arAAtoms: TArrayOfadrAtom): AnsiString;
	 function QuantifierAsString(adrAQuantifier: TadrQuantifier): AnsiString;
	 function SubstitutionAsString(adrAQuestion: TadrQuestion): AnsiString;
	 function BaseAsString(adrABase: TadrBase): AnsiString;

	 procedure DisposeFormula(adrARoot: TadrQuantifier);
	 procedure DisposeQuantifier(adrAQuantifier: TadrQuantifier);
	 procedure ExcludeQuanFormulaFromStorageBlock(adrAQuantifier: TadrQuantifier);
	 procedure DisposeAnswerQueue(var AAnswerQueue: TAnswerQueue);
	 procedure DisposeQuestion(adrAQuestion: TadrQuestion);
	 procedure DisposeStructuresOfBase(adrABase: TadrBase);
	 procedure SetBaseRefuted(adrABase: TadrBase);

	 function TimeIsOver: Boolean;

	 //--------------------------------//
	 // FStorageBlock
	 procedure DisposeBase(adrABase: TadrBase);
	 procedure DisposeAllBases;
	 procedure DisposeQuestQuantifiers;
	 procedure DisposeTermsPredicates;
	 //--------------------------------//

	 procedure DisplayFormulaByBase(adrABase: TadrBase;
									boolAShowNextBases: Boolean);

  public

	 constructor Create;
	 destructor Destroy; override;

	 function LoadFormula(stgsAIncomingText, stgsAMessagesField: TStrings;
						  var cardAErrorRow, cardAErrorCol: Cardinal): Boolean;

	 function Prove: Boolean;

	 property stgsPOutput: TStrings
		write stgsFOutput;
	 property cardPTimeForProof: Cardinal
		write cardFTimeEnd;
	 property boolPDWS_DTQVis: Boolean
		write boolFDWS_DTQVis;
	 property boolPRuleOfInferenceVis: Boolean
		write boolFRuleOfInferenceVis;
	 property boolPRefutVis: Boolean
		write boolFRefutVis;
	 property boolPDisplayBasesOnly: Boolean
		write boolFDisplayBasesOnly;
	 property boolPkRefutationStrategy: Boolean
		write boolFkRefutationStrategy;
  end;

implementation

uses uSyntaxAnalyzer, uStack, uTranslatorDeclarations, SysUtils,
	 uCourseOfProof, uCalculatedPredicates, Windows;

{ TProver }

constructor TProver.Create;
begin
  inherited Create;

  // Инициализация блока хранения
  with FStorageBlock do
  begin
	 htaFTermsPredicates := nil;
	 adrFFirstBase := nil;
	 adrFFirstQuestQuan := nil;
	 adrFLastQuestQuan := nil;
  end;

  stgsFOutput := nil;

  cardFTimeEnd := 4233600000 {49 суток} - 432000000 {5 суток};
  cardFTimeCurrent := 0;
  boolFDWS_DTQVis := False;
  boolFRuleOfInferenceVis := False;
  boolFRefutVis := False;
  boolFDisplayBasesOnly := False;
  boolFkRefutationStrategy := True;
  boolFkRefutationInProcess := False;
  intFRejectedBranchings := 0;
  boolFEnableDisjunctiveBranching := True;
  intFRuleOfInferenceCount := -1;
  intFBaseIndex := -1;
  intFBasesCount := -1;
end;

destructor TProver.Destroy;
begin
  DisposeTermsPredicates;
  DisposeAllBases;
  DisposeQuestQuantifiers;
  inherited Destroy;
end;

function TProver.LoadFormula(stgsAIncomingText,
							 stgsAMessagesField: TStrings;
							 var cardAErrorRow,
								 cardAErrorCol: Cardinal): Boolean;
var
  objVSyntaxAnalyzer: TSyntaxAnalyzer;
  adrVFormulaRoot: TadrQuantifier;
begin
  Result := True;

  FStorageBlock.htaFTermsPredicates := THashingTablesArray.Create(byCTablesCount);

  objVSyntaxAnalyzer := TSyntaxAnalyzer.Create;
  with objVSyntaxAnalyzer do
  begin
	 stgsPMessages := stgsAMessagesField;
	 htaPTermsPredicates := FStorageBlock.htaFTermsPredicates;
	 if AnalyseAndTranslate(stgsAIncomingText, adrVFormulaRoot)
	 then begin
			 Init(adrVFormulaRoot);
			 DisposeQuantifier(adrVFormulaRoot);
		  end
	 else begin
			 Result := False;
			 cardAErrorRow := intPErrorRow;
			 cardAErrorCol := intPErrorCol;

			 DisposeFormula(adrVFormulaRoot);
			 DisposeTermsPredicates;
		  end;
  end;
  objVSyntaxAnalyzer.Destroy;
end;

procedure TProver.Init(adrAFormulaRoot: TadrQuantifier);
// Трансформирует дерево по-формулы в вид, используемый при доказательстве:
//    1) создание баз и подчиненных им вопросов
//    2) инициализация ответных очередей вопросов
//    3) перенос V-подформул в блок хранения
var
  adrVBaseQuan, adrVQuestQuan, adrVWrkQuan: TadrQuantifier;
  adrVWrkBase, adrVTempBase: TadrBase;
  i, intVTemp: Integer;
begin
  adrVBaseQuan := adrAFormulaRoot^.adrFSon;
  New(adrVWrkBase);
  FStorageBlock.adrFFirstBase := adrVWrkBase;
  FStorageBlock.adrFFirstQuestQuan := nil;
  adrVWrkQuan := nil;

  intFBasesCount := 0;

  repeat
	 Inc(intFBasesCount);

	 with adrVWrkBase^ do
	 begin
		arFVariables := Copy(adrVBaseQuan^.arFVariables);

		objFAtomsTable := TAtomsTable.Create;

		for i := 0 to High(adrVBaseQuan^.arFTypeCondition) do
		   objFAtomsTable.AddAtom(adrVBaseQuan^.arFTypeCondition[i]);

		adrVQuestQuan := adrVBaseQuan^.adrFSon;
		while adrVQuestQuan <> nil do
		begin
		   if FStorageBlock.adrFFirstQuestQuan = nil then
			  FStorageBlock.adrFFirstQuestQuan := adrVQuestQuan
		   else
			  adrVWrkQuan^.adrFBrother := adrVQuestQuan;

		   adrVWrkQuan := adrVQuestQuan;

		   intVTemp := Length(arFQuestions);
		   SetLength(arFQuestions, intVTemp + 1);
		   New(arFQuestions[intVTemp]);
		   with arFQuestions[intVTemp]^ do
		   begin
			  adrFQuan := adrVQuestQuan;
			  objFAnswersTable := TAnswersTable.Create;
		   end;

		   adrVQuestQuan := adrVQuestQuan^.adrFBrother;
		end;
	 end;

	 adrVQuestQuan := adrVBaseQuan^.adrFBrother; // adrVQuestQuan используется для обмена значениями
	 DisposeQuantifier(adrVBaseQuan);
	 adrVBaseQuan := adrVQuestQuan;
	 if adrVBaseQuan <> nil
	 then begin
			 adrVTempBase := adrVWrkBase;
			 New(adrVWrkBase);
			 adrVTempBase^.adrFNextBase := adrVWrkBase;
		  end
	 else
		adrVWrkBase^.adrFNextBase := nil;

  until adrVBaseQuan = nil;

  FStorageBlock.adrFLastQuestQuan := adrVWrkQuan;
end;

procedure TProver.InitAnswerQueue(var AAnswerQueue: TAnswerQueue);
begin
  with AAnswerQueue do
  begin
     adrFFirstLink := nil;
     adrFLastLink := nil;
    // adrFCurrentLink := nil;
  end;
end;

procedure TProver.DisplayFormulaByBase(adrABase: TadrBase;
                                       boolAShowNextBases: Boolean);
// Вывод формулы, имеющей представление, используемое при доказательстве,
// в поле stgsFOutput
var
  VStack: TStack;
  adrVCurrentBase: TadrBase;
  adrVCurrentQuan: TadrQuantifier;
  i, j, intVTemp: Integer;
  strVTemp: AnsiString;
  wrdVShift, wrdVTemp1, wrdVTemp2: Word;
  boolVPopped: Boolean;
begin
  frmCourseOfProof.FStatusBar.SimpleText := 'Вывод формулы...';

  strVTemp := chrCUnQuan + ':' + strCTrue + ' ';

  {----}
  if (adrABase^.adrFNextBase <> nil) and boolAShowNextBases then
     strVTemp := strVTemp + '(';
  {----}

  adrVCurrentBase := adrABase;
  VStack := nil;

  wrdVTemp1 := Length(strVTemp);
  repeat
     strVTemp := strVTemp + BaseAsString(adrVCurrentBase);

     if not boolFDisplayBasesOnly
     then begin
             intVTemp := Length(adrVCurrentBase^.arFQuestions);
             if intVTemp > 1 then
                strVTemp := strVTemp + ' ('
             else if intVTemp = 1 then
                     strVTemp := strVTemp + ' ';

             wrdVTemp2 := Length(strVTemp);
             for i := 0 to intVTemp - 1 do
             begin
                adrVCurrentQuan := adrVCurrentBase^.arFQuestions[i]^.adrFQuan;
                repeat

                   repeat
                      if (adrVCurrentQuan^.adrFBrother <> nil) and
                         (adrVCurrentQuan <> adrVCurrentBase^.arFQuestions[i]^.adrFQuan)
                      then
                         Push(VStack, adrVCurrentQuan^.adrFBrother, Length(strVTemp));

                      strVTemp := strVTemp + QuantifierAsString(adrVCurrentQuan);

                      if adrVCurrentQuan^.adrFSon <> nil then
                         if adrVCurrentQuan^.adrFSon^.adrFBrother <> nil
                         then begin
                                 strVTemp := strVTemp + ' (';
                                 Push(VStack, nil);
                              end
                         else
                            strVTemp := strVTemp + ' ';

                      adrVCurrentQuan := adrVCurrentQuan^.adrFSon;
                   until adrVCurrentQuan = nil;

                   boolVPopped := Pop(VStack, adrVCurrentQuan, wrdVShift);

                   if boolVPopped
                   then begin
                           while (adrVCurrentQuan = nil) and boolVPopped do
                           begin
                              strVTemp := strVTemp + ')';
                              boolVPopped := Pop(VStack, adrVCurrentQuan, wrdVShift);
                           end;

                           if boolVPopped then
                              strVTemp := strVTemp + ',';
                        end;

                   //----------------------------//
                   if boolVPopped
                   then begin
                           stgsFOutput.Append(strVTemp);
                           strVTemp := '';
                           for j := 1 to wrdVShift do
                              strVTemp := strVTemp + ' ';
                        end;
                   //----------------------------//
                until not boolVPopped;


                if intVTemp > 1 then
                if i < intVTemp - 1
                then begin
                        strVTemp := strVTemp + ',';
                        stgsFOutput.Append(strVTemp);
                        strVTemp := '';
                        for j := 1 to wrdVTemp2 do
                           strVTemp := strVTemp + ' ';
                     end;
             end;

             if intVTemp > 1 then
                strVTemp := strVTemp + ')';
          end;

     if boolAShowNextBases
     then begin
             adrVCurrentBase := adrVCurrentBase^.adrFNextBase;
             if adrVCurrentBase <> nil
             then begin
                     strVTemp := strVTemp + ',';
                     stgsFOutput.Append(strVTemp);
                     strVTemp := '';
                     for j := 1 to wrdVTemp1 do
                        strVTemp := strVTemp + ' ';
                  end;
          end
     else
        adrVCurrentBase := nil;

     if TimeIsOver then
        if adrVCurrentBase <> nil
        then begin
                adrVCurrentBase := nil;
                if boolAShowNextBases then
                   strVTemp := strVTemp + ' ... ';
             end;
  until adrVCurrentBase = nil;

  {----}
  if (adrABase^.adrFNextBase <> nil) and boolAShowNextBases then
     strVTemp := strVTemp + ')';
  {----}
  stgsFOutput.Append(strVTemp);
end;

procedure TProver.DisposeAnswerQueue(var AAnswerQueue: TAnswerQueue);
var
  adrVTempLink: TadrAnswerQueueLink;
begin
  {with AAnswerQueue do
  begin
     while adrFFirstLink <> nil do
     begin
        Finalize(adrFFirstLink^.arFAnswerSubstitution);
        adrVTempLink := adrFFirstLink^.adrFNextLink;
        Dispose(adrFFirstLink);
        adrFFirstLink := adrVTempLink;
     end;
     adrFLastLink := nil;
     adrFCurrentLink := nil;
  end;}
end;

procedure TProver.DisposeStructuresOfBase(adrABase: TadrBase);
var
  i: Integer;
begin
  with adrABase^ do
  begin
     Finalize(arFVariables);

     objFAtomsTable.Free;
     objFAtomsTable := nil;

     for i := 0 to High(arFQuestions) do
        DisposeQuestion(arFQuestions[i]);
     Finalize(arFQuestions);
  end;
end;

procedure TProver.SetBaseRefuted(adrABase: TadrBase);
begin
  DisposeStructuresOfBase(adrABase);
end;

procedure TProver.DisposeBase(adrABase: TadrBase);
begin
  DisposeStructuresOfBase(adrABase);
  Dispose(adrABase);
end;

procedure TProver.DisposeAllBases;
var
  adrVCurrentBase, adrVTempBase: TadrBase;
begin
  adrVCurrentBase := FStorageBlock.adrFFirstBase;

  while adrVCurrentBase <> nil do
  begin
     adrVTempBase := adrVCurrentBase^.adrFNextBase;
     DisposeBase(adrVCurrentBase);
     adrVCurrentBase := adrVTempBase;
  end;

  FStorageBlock.adrFFirstBase := nil;
end;

procedure TProver.ExcludeQuanFormulaFromStorageBlock(
                                               adrAQuantifier: TadrQuantifier);
// Удаление из блока хранения ссылки на V-подформулу
var
  adrVWrkQuan: TadrQuantifier;
begin
  if FStorageBlock.adrFFirstQuestQuan <> nil then
     if FStorageBlock.adrFFirstQuestQuan = adrAQuantifier
     then begin
             if FStorageBlock.adrFLastQuestQuan = adrAQuantifier then
                FStorageBlock.adrFLastQuestQuan := nil;
             FStorageBlock.adrFFirstQuestQuan := FStorageBlock.adrFFirstQuestQuan^.adrFBrother
          end
     else begin
             adrVWrkQuan := FStorageBlock.adrFFirstQuestQuan;
             while (adrVWrkQuan^.adrFBrother <> adrAQuantifier) and (adrVWrkQuan^.adrFBrother <> nil) do
                adrVWrkQuan := adrVWrkQuan^.adrFBrother;
             if adrVWrkQuan^.adrFBrother = adrAQuantifier
             then begin
                     if FStorageBlock.adrFLastQuestQuan = adrAQuantifier then
                        FStorageBlock.adrFLastQuestQuan := adrVWrkQuan;

                     adrVWrkQuan^.adrFBrother := adrAQuantifier^.adrFBrother;
                  end;
          end;
end;

procedure TProver.DisposeQuestion(adrAQuestion: TadrQuestion);
begin
  adrAQuestion^.objFAnswersTable.Destroy;
  Dispose(adrAQuestion);
end;

procedure TProver.DisposeQuestQuantifiers;
begin
  with FStorageBlock do
     if adrFFirstQuestQuan <> nil
     then begin
             DisposeFormula(adrFFirstQuestQuan);
             adrFFirstQuestQuan := nil;
             adrFLastQuestQuan := nil;
          end;
end;

procedure TProver.DisposeQuantifier(adrAQuantifier: TadrQuantifier);
var
  i: Integer;
begin
  with adrAQuantifier^ do
  begin
     Finalize(arFVariables);
     for i := 0 to High(arFTypeCondition) do
        ExcludeReferenceToAtom(arFTypeCondition[i]);
     Finalize(arFTypeCondition);
  end;
  Dispose(adrAQuantifier);
end;

procedure TProver.DisposeFormula(adrARoot: TadrQuantifier);
var
  VStack: TStack;
  adrVCurrentQuan: TadrQuantifier;
begin
  if adrARoot <> nil
  then begin
          VStack := nil;
          adrVCurrentQuan := adrARoot;
          repeat
             with adrVCurrentQuan^ do
             begin
                if adrFBrother <> nil then
                   Push(VStack, adrFBrother);
                if adrFSon <> nil then
                   Push(VStack, adrFSon);
             end;
             DisposeQuantifier(adrVCurrentQuan);
          until not Pop(VStack, adrVCurrentQuan);
       end;
end;

procedure TProver.DisposeTermsPredicates;
var
  i, j: Integer;
  slstVLexicalUnits: TStringList;
  cardVLexicalCode: Cardinal;
begin
  if FStorageBlock.htaFTermsPredicates <> nil
  then begin
          slstVLexicalUnits := TStringList.Create;
          for i := 1 to byCTablesCount do
             with FStorageBlock.htaFTermsPredicates do
             begin
                GetLexicalUnitsList(i, slstVLexicalUnits);
                for j := 0 to slstVLexicalUnits.Count - 1 do
                begin
                   SearchLexicalUnit(slstVLexicalUnits.Strings[j], i,
                                     cardVLexicalCode);
                   case i of
                      byCVariablesTable : Dispose(TadrVariable(
                                                  Pointers[cardVLexicalCode]));
                      byCPredicatesTable: if Pointers[cardVLexicalCode] <> nil then
                                             ExcludeReferenceToAtom(TadrAtom(Pointers[cardVLexicalCode]));
                      byCIntegersTable: Dispose(TadrIntegerConstant(
                                                  Pointers[cardVLexicalCode]));
                      byCStringsTable: Dispose(TadrStringConstant(
                                                  Pointers[cardVLexicalCode]));
                end;
             end;
             slstVLexicalUnits.Clear;
          end;
          slstVLexicalUnits.Destroy;

          FStorageBlock.htaFTermsPredicates.Destroy;
          FStorageBlock.htaFTermsPredicates := nil;
       end;
end;

function TProver.VariablesAsString(const arAVariables: TArrayOfadrVariable): AnsiString;
var
  i, intVTemp: Integer;
begin
  Result := '';
  intVTemp := High(arAVariables);
  for i := 0 to intVTemp do
  begin
     Result := Result + FStorageBlock.htaFTermsPredicates.LexicalUnits[arAVariables[i]^.cardFLexicalCode];
     if i < intVTemp then
        Result := Result + ',';
  end;
end;

function TProver.SimpleTermAsString(const ATerm: TTerm): AnsiString;
begin
  with ATerm, FStorageBlock.htaFTermsPredicates do
     case Tag of
        byCVariableTag: Result := LexicalUnits[TadrVariable(ptrFReference)^.cardFLexicalCode];
        byCIntegerConstantTag: Result := LexicalUnits[TadrIntegerConstant(ptrFReference)^.cardFLexicalCode];
        byCRealConstantTag: Result := LexicalUnits[TadrRealConstant(ptrFReference)^.cardFLexicalCode];
        byCStringConstantTag: Result := '''' + LexicalUnits[TadrStringConstant(ptrFReference)^.cardFLexicalCode] + '''';
     else
        Result := '';
     end;
end;

function TProver.TermVariantsAsString(adrATermVariants: TadrTermVariants): AnsiString;
var
  i, intVTemp: Integer;
begin
  Result := '';
  intVTemp := High(adrATermVariants^.arFTerms);
  for i := 0 to intVTemp do
  begin
     Result := Result + SimpleTermAsString(adrATermVariants^.arFTerms[i]);
     if i < intVTemp then
        Result := Result + ',';
  end;
end;

function TProver.TermAsString(const ATerm: TTerm): AnsiString;
begin
  if ATerm.Tag = byCTermVariantsTag then
     Result := '{' + TermVariantsAsString(ATerm.ptrFReference) + '}'
  else
     Result := SimpleTermAsString(ATerm);
end;

function TProver.AtomAsString(const AAtom: uTermsAndFormulasStructures.TAtom): AnsiString;
var
  i, intVTemp: Integer;
begin
  case AAtom.Tag of
     byCSimplePredicateTag,
     byCCalculatedPredicateTag,
     byCTrueTag,
     byCFalseTag: begin
                     Result := FStorageBlock.htaFTermsPredicates.LexicalUnits[AAtom.cardFName];

                     intVTemp := High(AAtom.arFTerms);
                     if intVTemp >= 0
                     then begin
                             Result := Result + '(';
                             for i := 0 to intVTemp do
                             begin
                                Result := Result + TermAsString(AAtom.arFTerms[i]);
                                if i < intVTemp then
                                   Result := Result + ',';
                             end;
                             Result := Result + ')';
                          end;
                  end;

     byCEqualTag,
     byCLessGreaterTag,
     byCLessTag,
     byCLessEqualTag,
     byCGreaterTag,
     byCGreaterEqualTag: begin
                            Result := TermAsString(AAtom.arFTerms[0]);
                            Result := Result + FStorageBlock.htaFTermsPredicates.LexicalUnits[AAtom.cardFName];
                            Result := Result + TermAsString(AAtom.arFTerms[1]);
                         end;
  else
     Result := 'Неизвестный тип атома';
  end;
end;

function TProver.TypeConditionAsString(const arAAtoms: TArrayOfadrAtom): AnsiString;
var
  i, intVTemp: Integer;
begin
  intVTemp := Length(arAAtoms);
  if intVTemp > 0
  then begin
          Result := '';
          Dec(intVTemp);
          for i := 0 to intVTemp do
          begin
             Result := Result + AtomAsString(arAAtoms[i]^);
             if i < intVTemp then
                Result := Result + ',';
          end
       end
  else
     Result := strCTrue;
end;

function TProver.QuantifierAsString(adrAQuantifier: TadrQuantifier): AnsiString;
begin
  with adrAQuantifier^ do
  begin
     if boolFUnQuan then
        Result := chrCUnQuan
     else
        Result := chrCExQuan;

     Result := Result + VariablesAsString(arFVariables) + ':' + TypeConditionAsString(arFTypeCondition);
  end;
end;

function TProver.SubstitutionAsString(adrAQuestion: TadrQuestion): AnsiString;
  // В качестве параметра приходит вопрос, а не TArrayOfTerm, т.к.
  // подстановка определяется с помощью кванторных переменных вопроса
var
  i, intVTemp: Integer;
begin
  Result := '';
  intVTemp := High(adrAQuestion^.objFAnswersTable.arPCurrentAnswer);
  with FStorageBlock.htaFTermsPredicates, adrAQuestion^.objFAnswersTable do
     for i := 0 to intVTemp do
     begin
        Result := Result + LexicalUnits[adrAQuestion^.adrFQuan^.arFVariables[i]^.cardFLexicalCode] + '->';
        case arPCurrentAnswer[i].Tag of
           byCIntegerConstantTag: Result := Result + LexicalUnits[TadrIntegerConstant(arPCurrentAnswer[i].ptrFReference)^.cardFLexicalCode];
           byCRealConstantTag: Result := Result + LexicalUnits[TadrRealConstant(arPCurrentAnswer[i].ptrFReference)^.cardFLexicalCode];
           byCStringConstantTag: Result := Result + '''' + LexicalUnits[TadrStringConstant(arPCurrentAnswer[i].ptrFReference)^.cardFLexicalCode] + '''';
           byCVariableTag: Result := Result + LexicalUnits[TadrVariable(arPCurrentAnswer[i].ptrFReference)^.cardFLexicalCode];
        end;

        if i <> intVTemp then
           Result := Result + ', ';
     end;
end;

function TProver.BaseAsString(adrABase: TadrBase): AnsiString;
begin
  Result := chrCExQuan + VariablesAsString(adrABase^.arFVariables) + ':';

  if adrABase^.objFAtomsTable <> nil then
     Result := Result + TypeConditionAsString(adrABase^.objFAtomsTable.GetAllAtoms)
  else
     Result := Result + strCFalse;
end;

function TProver.SearchTermInVariablesOfQuantifier(
                                      const ATerm: TTerm;
                                      adrAQuantifier: TadrQuantifier): Integer;
  // Ф-я вернет индекс переменной (терма ATerm) в массиве переменных квантора.
  // Ф-я вернет -1, если терм - не переменная квантора.
begin
  if ATerm.Tag = byCVariableTag
  then begin
          Result := SearchVariable(TadrVariable(ATerm.ptrFReference), adrAQuantifier^.arFVariables);
          if Result < -1 then
             Result := -1;
       end
  else
     Result := -1;
end;

function TProver.CopyAnswerQueue(const AAnswerQueue: TAnswerQueue): TAnswerQueue;
var
  adrVSourceLink, adrVDestLink, adrVTempLink: TadrAnswerQueueLink;
begin
  {adrVSourceLink := AAnswerQueue.adrFFirstLink;
  if adrVSourceLink <> nil
  then begin
          New(adrVDestLink);
          Result.adrFFirstLink := adrVDestLink;
          Result.adrFCurrentLink := nil; // На случай, если все ответы использовались

          repeat
             adrVDestLink^.arFAnswerSubstitution := Copy(adrVSourceLink^.arFAnswerSubstitution);

             if adrVSourceLink = AAnswerQueue.adrFCurrentLink then
                Result.adrFCurrentLink := adrVDestLink;

             adrVSourceLink := adrVSourceLink^.adrFNextLink;
             if adrVSourceLink <> nil
             then begin
                     adrVTempLink := adrVDestLink;
                     New(adrVDestLink);
                     adrVTempLink^.adrFNextLink := adrVDestLink;
                  end
             else begin
                     adrVDestLink^.adrFNextLink := nil;
                     Result.adrFLastLink := adrVDestLink;
                  end;
          until adrVSourceLink = nil;
       end
  else
     InitAnswerQueue(Result);  }
end;

function TProver.CopyTypeCondition(
                     const arATypeCondition: TArrayOfadrAtom): TArrayOfadrAtom;
var
  i, intVTemp: Integer;
begin
  intVTemp := Length(arATypeCondition);
  SetLength(Result, intVTemp);
  for i := 0 to intVTemp - 1 do
     Result[i] := CopyReferenceToAtom(arATypeCondition[i])
end;

function TProver.CopyFormula(adrARoot: TadrQuantifier): TadrQuantifier;
var
  VStack: TStack;
  adrVSourceQuan, adrVDestQuan: TadrQuantifier;
begin
  VStack := nil;
  New(Result);
  adrVDestQuan := Result;
  adrVSourceQuan := adrARoot;

  repeat
     with adrVDestQuan^ do
     begin
        boolFUnQuan := adrVSourceQuan^.boolFUnQuan;
        arFVariables := Copy(adrVSourceQuan^.arFVariables);
        arFTypeCondition := CopyTypeCondition(adrVSourceQuan^.arFTypeCondition);

        if adrVSourceQuan^.adrFSon <> nil
        then begin
                New(adrFSon);
                Push(VStack, adrVSourceQuan^.adrFSon, adrFSon);
             end
        else
           adrFSon := nil;

        if (adrVSourceQuan^.adrFBrother <> nil) and (adrVSourceQuan <> adrARoot)
        then begin
                New(adrFBrother);
                Push(VStack, adrVSourceQuan^.adrFBrother, adrFBrother);
             end
        else
           adrFBrother := nil;
     end;
  until not Pop(VStack, adrVSourceQuan, adrVDestQuan);
end;

function TProver.CopyBase(adrASourceBase: TadrBase): TadrBase;
// Функция вернет ссылку на копию adrASourceBase
var
  i, intVTemp: Integer;
  arVAtomsOfSourceBase: TArrayOfadrAtom;
begin
  New(Result);
  Result^.adrFNextBase := nil;

  with Result^ do
  begin
     arFVariables := Copy(adrASourceBase^.arFVariables);

     arVAtomsOfSourceBase := adrASourceBase^.objFAtomsTable.GetAllAtoms;
     objFAtomsTable := TAtomsTable.Create(adrASourceBase^.objFAtomsTable.cardPHashSize);
     for i := 0 to High(arVAtomsOfSourceBase) do
        objFAtomsTable.AddAtom(arVAtomsOfSourceBase[i]);
     Finalize(arVAtomsOfSourceBase);
  end;

  intVTemp := Length(adrASourceBase^.arFQuestions);
  SetLength(Result^.arFQuestions, intVTemp);
  for i := 0 to intVTemp - 1 do
  begin
     New(Result^.arFQuestions[i]);
     Result^.arFQuestions[i]^.adrFQuan := adrASourceBase^.arFQuestions[i]^.adrFQuan;

     Result^.arFQuestions[i]^.objFAnswersTable := TAnswersTable.CopyAnswersTable(adrASourceBase^.arFQuestions[i].objFAnswersTable);
     //Result^.arFQuestions[i]^.FAnswerQueue := CopyAnswerQueue(adrASourceBase^.arFQuestions[i]^.FAnswerQueue);
  end;
end;

function TProver.RepeatedAnswer(const arAAnswerSubstitution: TArrayOfTerm;
                                adrAQuestion: TadrQuestion): Boolean;
var
  adrVCurrentLink: TadrAnswerQueueLink;
  i, intVHigh: Integer;
begin
  {Result := False;
  if adrAQuestion^.FAnswerQueue.adrFFirstLink <> nil
  then begin
          adrVCurrentLink := adrAQuestion^.FAnswerQueue.adrFFirstLink;
          intVHigh := High(adrVCurrentLink^.arFAnswerSubstitution);

          repeat
             i := 0;
             while i <= intVHigh do
                if arAAnswerSubstitution[i].ptrFReference =
                   adrVCurrentLink^.arFAnswerSubstitution[i].ptrFReference then
                   Inc(i)
                else
                   i := intVHigh + 10;

             if i = (intVHigh + 1) then
                Result := True;

             adrVCurrentLink := adrVCurrentLink^.adrFNextLink;
          until (adrVCurrentLink = nil) or Result;
       end; }
end;

function TProver.DereferencingVariable(adrAVariable: TadrVariable): TadrVariable;
// Разыменование переменной
// Новая переменная заносится в FStorageBlock.htaFTermsFormulas
var
  strVVariable: AnsiString;
  intVAddition: Integer;
  cardVLexCode: Cardinal;
begin
  with FStorageBlock.htaFTermsPredicates do
  begin
     strVVariable := LexicalUnits[adrAVariable^.cardFLexicalCode];
     intVAddition := 1;
     while AddLexicalUnit(strVVariable + '_' + IntToStr(intVAddition), byCVariablesTable, cardVLexCode) do
        Inc(intVAddition);
     New(Result);
     Result^.cardFLexicalCode := cardVLexCode;
     Pointers[cardVLexCode] := Pointer(Result);
  end;
end;

procedure TProver.AnswerToQueue(const arAAnswerSubstitution: TArrayOfTerm;
                                var AAnswerQueue: TAnswerQueue;
                                boolAToEnd: Boolean);
// Добавление ответной подстановки
//    1) в конец очереди (AAnswerQueue.adrFLastLink), если boolAToEnd = True
//    2) в начало очереди (AAnswerQueue.adrFCurrentLink), иначе
var
  adrVNewLink: TadrAnswerQueueLink;
  arVTemp: TArrayOfTerm;
begin
  {New(adrVNewLink);
  adrVNewLink^.arFAnswerSubstitution := Copy(arAAnswerSubstitution);

  with AAnswerQueue do
     if adrFCurrentLink = nil
     then begin
             adrVNewLink^.adrFNextLink := nil;

             if adrFFirstLink = nil
             then begin
                     adrFFirstLink := adrVNewLink;
                     adrFLastLink := adrVNewLink;
                     adrFCurrentLink := adrVNewLink;
                  end
             else begin
                     adrFLastLink^.adrFNextLink := adrVNewLink;
                     adrFLastLink := adrVNewLink;
                     adrFCurrentLink := adrFLastLink;
                  end;
          end
     else
        if boolAToEnd
        then begin
                adrVNewLink^.adrFNextLink := nil;

                adrFLastLink^.adrFNextLink := adrVNewLink;
                adrFLastLink := adrVNewLink;
             end
        else begin
                adrVNewLink^.adrFNextLink := adrFCurrentLink^.adrFNextLink;
                adrFCurrentLink^.adrFNextLink := adrVNewLink;

                arVTemp := adrVNewLink^.arFAnswerSubstitution;
                adrVNewLink^.arFAnswerSubstitution := adrFCurrentLink^.arFAnswerSubstitution;
                adrFCurrentLink^.arFAnswerSubstitution := arVTemp;
             end; }
end;

function TProver.TermsIsConstants(const arATerms: TArrayOfTerm): Boolean;
var
  i, intVTemp: Integer;
begin
  intVTemp := High(arATerms);
  i := 0;

  while i <= intVTemp do
     if arATerms[i].Tag = byCVariableTag then
        i := intVTemp + 10
     else
        Inc(i);

  Result := i = intVTemp + 1;
end;

function TProver.CalculatePredicate(adrAAtom: TadrAtom;
                                    const arASubstitutionConstants: TArrayOfTerm): Boolean;
begin
  Result := False;
  if adrAAtom^.Tag = byCCalculatedPredicateTag
  then begin
          // запрос в dll на вычисление предиката
       end
  else begin
          case arASubstitutionConstants[0].Tag of
             byCIntegerConstantTag: Result := BinaryRelation(adrAAtom^.Tag, TadrIntegerConstant(arASubstitutionConstants[0].ptrFReference)^.intFValue, TadrIntegerConstant(arASubstitutionConstants[1].ptrFReference)^.intFValue);
             byCRealConstantTag: Result := BinaryRelation(adrAAtom^.Tag, TadrRealConstant(arASubstitutionConstants[0].ptrFReference)^.extFValue, TadrRealConstant(arASubstitutionConstants[1].ptrFReference)^.extFValue);
             byCStringConstantTag: Result := BinaryRelation(adrAAtom^.Tag, FStorageBlock.htaFTermsPredicates.LexicalUnits[TadrStringConstant(arASubstitutionConstants[0].ptrFReference)^.cardFLexicalCode], FStorageBlock.htaFTermsPredicates.LexicalUnits[TadrStringConstant(arASubstitutionConstants[1].ptrFReference)^.cardFLexicalCode]);
          end;
       end;
end;

function TProver.AddNewAnswers(adrABase: TadrBase;
                               intAQuestionIndex: Integer): Boolean;

     function Bit(var cardANumber: Cardinal;
                  byABitIndex: Byte;
                  boolASetBit1: Boolean): Boolean; assembler;
       // Возвращает True, если в cardANumber бит с индексом byABitIndex равен 1.
       // Устанавливает бит с индексом byABitIndex в 1, если boolASetBit1 = True.
     asm
       // [eax] = cardANumber, dl = byABitIndex, cl = boolASetBit1, al = Result
       mov ch,cl
       mov cl,dl
       xor edx,edx
       inc edx
       shl edx,cl
       xor cl,cl
       test [eax],edx
       jz @L
          inc cl
          jmp @M
       @L:
       shr ch,1
       jnc @M
          or [eax],edx
       @M:
       mov al,cl
     end;

var
  VStack: TStack;
  i, j, intVAtomIndex, intVTypeCondHigh, intVVariablesHigh,
  intVVariableIndex, intVTermsHigh: Integer;
  arVAnswerSubstitution: TArrayOfTerm;
  arVSimplePredicates, arVCalculatedPredicates, arVAtomsOfBase: TArrayOfadrAtom;
  cardVUsed_Mask, cardVTemp: Cardinal;
  boolVAllVariants, boolVAtomMatch: Boolean;
  adrVQuestion: TadrQuestion;
  VTermOfAtomInBase: TTerm;

     function SubstTermsIsConstants(const arATerms: TArrayOfTerm;
                                    var arASubstitutionConstants: TArrayOfTerm): Boolean;
     var
        i, j, intVTemp: Integer;
     begin
        intVTemp := High(arATerms);
        SetLength(arASubstitutionConstants, intVTemp + 1);
        i := 0;

        while i <= intVTemp do
        begin
           if arATerms[i].Tag <> byCVariableTag then
              arASubstitutionConstants[i] := arATerms[i]
           else begin
                   j := SearchTermInVariablesOfQuantifier(arATerms[i], adrVQuestion^.adrFQuan);
                   if j >= 0
                   then begin
                           if not Bit(cardVUsed_Mask, j, False) then
                              i := intVTemp + 10
                           else
                              if arVAnswerSubstitution[j].Tag = byCVariableTag then
                                 i := intVTemp + 10
                              else
                                 arASubstitutionConstants[i] := arVAnswerSubstitution[j];
                        end
                   else
                      i := intVTemp + 10;
                end;

           Inc(i);
        end;

        if i = intVTemp + 1 then
           Result := True
        else begin
                Result := False;
                Finalize(arASubstitutionConstants);
             end;
     end;

     function CalculatedPredicatesTrue: Boolean;
     var
       i, intVTemp: Integer;
       arVConstants: TArrayOfTerm;
     begin
       intVTemp := High(arVCalculatedPredicates);
       i := 0;
       while i <= intVTemp do
          if SubstTermsIsConstants(arVCalculatedPredicates[i]^.arFTerms, arVConstants)
          then begin
                  if CalculatePredicate(arVCalculatedPredicates[i], arVConstants) = True then
                     Inc(i)
                  else
                     i := intVTemp + 10;
               end
          else
             i := intVTemp + 10;

       Result := i = intVTemp + 1;
     end;

begin
  adrVQuestion := adrABase^.arFQuestions[intAQuestionIndex];

  intVTypeCondHigh := -1;
  j := -1;
  for i := 0 to High(adrVQuestion^.adrFQuan^.arFTypeCondition) do
     if adrVQuestion^.adrFQuan^.arFTypeCondition[i]^.Tag = byCSimplePredicateTag
     then begin
             Inc(intVTypeCondHigh);
             SetLength(arVSimplePredicates, intVTypeCondHigh + 1);
             arVSimplePredicates[intVTypeCondHigh] := adrVQuestion^.adrFQuan^.arFTypeCondition[i];
          end
     else begin
             Inc(j);
             SetLength(arVCalculatedPredicates, j + 1);
             arVCalculatedPredicates[j] := adrVQuestion^.adrFQuan^.arFTypeCondition[i];
          end;

  if intVTypeCondHigh <> -1
  then begin
          Result := False;
          intVVariablesHigh := High(adrVQuestion^.adrFQuan^.arFVariables);
          SetLength(arVAnswerSubstitution, intVVariablesHigh + 1);

          VStack := nil;
          cardVUsed_Mask := 0;
          intVAtomIndex := 0;
          i := 0;
          boolVAllVariants := False;

          repeat
             if adrABase^.objFAtomsTable.SearchAtoms(arVSimplePredicates[i]^.cardFName, arVAtomsOfBase)
             then begin
                     cardVTemp := cardVUsed_Mask;
                     intVTermsHigh := High(arVSimplePredicates[i]^.arFTerms);
                     boolVAtomMatch := False;

                     repeat
                        j := 0;
                        while j <= intVTermsHigh do
                        begin
                           VTermOfAtomInBase := arVAtomsOfBase[intVAtomIndex]^.arFTerms[j];

                           intVVariableIndex := SearchTermInVariablesOfQuantifier(arVSimplePredicates[i]^.arFTerms[j], adrVQuestion^.adrFQuan);
                           if intVVariableIndex >= 0
                           then begin { терм атома вопроса - кванторная переменная вопроса }
                                   if Bit(cardVUsed_Mask, intVVariableIndex, True)
                                   then begin
                                           if arVAnswerSubstitution[intVVariableIndex].ptrFReference <> VTermOfAtomInBase.ptrFReference
                                           then j := intVTermsHigh + 9
                                        end
                                   else
                                      arVAnswerSubstitution[intVVariableIndex] := VTermOfAtomInBase;
                                end
                           else begin{ терм атома вопроса - кванторная переменная базы или число, строка и т.п. }
                                   if arVSimplePredicates[i]^.arFTerms[j].ptrFReference <> VTermOfAtomInBase.ptrFReference
                                   then j := intVTermsHigh + 9;
                                end;
                           Inc(j);
                        end;

                        if j <> intVTermsHigh + 10
                        then begin
                                if i < intVTypeCondHigh
                                then begin
                                        if intVAtomIndex < High(arVAtomsOfBase) then
                                           Push(VStack, intVAtomIndex + 1, cardVTemp)
                                        else
                                           Push(VStack, -1, 0);

                                        Inc(i);
                                        intVAtomIndex := 0;
                                        boolVAtomMatch := True;
                                     end
                                else
                                   if intVVariablesHigh >= 0
                                   then begin { Подстановка - ответная }
                                           if CalculatedPredicatesTrue then
                                              if adrVQuestion.objFAnswersTable.AddAnswer(arVAnswerSubstitution, False) then
                                                 Result := True;
                                              {if not RepeatedAnswer(arVAnswerSubstitution, adrVQuestion)
                                              then begin
                                                      AnswerToQueue(arVAnswerSubstitution, adrVQuestion^.FAnswerQueue, False);
                                                      Result := True;
                                                   end;}
                                        end
                                   else begin{ Вопрос - тривиальный }
                                           if CalculatedPredicatesTrue then
                                              Result := True;
                                           boolVAllVariants := True;
                                           boolVAtomMatch := True;
                                        end;
                             end;

                        if not boolVAtomMatch
                        then begin
                                if intVAtomIndex = High(arVAtomsOfBase)
                                then begin
                                        boolVAtomMatch := True;
                                        repeat
                                           Dec(i);
                                           if i >= 0 then
                                              Pop(VStack, intVAtomIndex, cardVUsed_Mask)
                                           else
                                              boolVAllVariants := True;
                                        until (intVAtomIndex <> -1) or boolVAllVariants;
                                     end
                                else begin
                                        Inc(intVAtomIndex);
                                        cardVUsed_Mask := cardVTemp;
                                     end;
                             end;
                     until boolVAtomMatch;
                  end
             else
                boolVAllVariants := True;

          until boolVAllVariants;

          DisposeStack(VStack);
          Finalize(arVAnswerSubstitution);
       end
  else
     Result := CalculatedPredicatesTrue;
end;

function TProver.DuplicateWithSpecification(adrABase: TadrBase;
                                            intAQuestionIndex: Integer): Integer;
var
  VStack: TStack;
  adrVQuestion: TadrQuestion;
  adrVSourceQuan, adrVDestQuan: TadrQuantifier;
  htaFDereferencingVariables: THashingTablesArray;
  cardVLexCode: Cardinal;
  i, intVVarHigh: Integer;

   procedure DWS_TypeCondition;
   var
     i, j, intVHighAtomIndex, intVHighTermIndex, intVVariableIndex: Integer;
   begin
      intVHighAtomIndex := High(adrVSourceQuan^.arFTypeCondition);
      SetLength(adrVDestQuan^.arFTypeCondition, intVHighAtomIndex + 1);
      for i := 0 to intVHighAtomIndex do
      begin
         intVHighTermIndex := High(adrVSourceQuan^.arFTypeCondition[i]^.arFTerms);

         if intVHighTermIndex = -1 then
            adrVDestQuan^.arFTypeCondition[i] := CopyReferenceToAtom(adrVSourceQuan^.arFTypeCondition[i])
         else begin
                 adrVDestQuan^.arFTypeCondition[i] := NewAtom;

                 with adrVDestQuan^.arFTypeCondition[i]^ do
                 begin
                    Tag := adrVSourceQuan^.arFTypeCondition[i]^.Tag;
                    cardFName := adrVSourceQuan^.arFTypeCondition[i]^.cardFName;

                    SetLength(arFTerms, intVHighTermIndex + 1);

                    for j := 0 to intVHighTermIndex do
                       if adrVSourceQuan^.arFTypeCondition[i]^.arFTerms[j].Tag = byCVariableTag then
                          if htaFDereferencingVariables.SearchLexicalUnit(IntToStr(Integer(adrVSourceQuan^.arFTypeCondition[i]^.arFTerms[j].ptrFReference)), 1, cardVLexCode)
                          then begin
                                  arFTerms[j].Tag := byCVariableTag;
                                  arFTerms[j].ptrFReference := htaFDereferencingVariables.Pointers[cardVLexCode];
                               end
                          else begin
                                  intVVariableIndex := SearchTermInVariablesOfQuantifier(adrVSourceQuan^.arFTypeCondition[i]^.arFTerms[j], adrVQuestion^.adrFQuan);
                                  if intVVariableIndex >= 0 then
                                     arFTerms[j] := adrVQuestion^.objFAnswersTable.arPCurrentAnswer[intVVariableIndex]
                                     //arFTerms[j] := adrVQuestion^.FAnswerQueue.adrFCurrentLink^.arFAnswerSubstitution[intVVariableIndex]
                                  else
                                     arFTerms[j] := adrVSourceQuan^.arFTypeCondition[i]^.arFTerms[j];
                               end
                       else
                          arFTerms[j] := adrVSourceQuan^.arFTypeCondition[i]^.arFTerms[j];
                 end;
         end;
      end;
   end;

begin
  adrVQuestion := adrABase^.arFQuestions[intAQuestionIndex];

  htaFDereferencingVariables := THashingTablesArray.Create(1);
  htaFDereferencingVariables.SetPointTable(1);

  adrVSourceQuan := adrVQuestion^.adrFQuan;
  New(adrVDestQuan);
  with adrVDestQuan^ do begin
     boolFUnQuan := True;
     DWS_TypeCondition;
     adrVDestQuan^.adrFBrother := nil;
  end;

  with adrABase^ do
  begin
     Result := Length(arFQuestions);
     SetLength(arFQuestions, Result + 1);
     New(arFQuestions[Result]);
     arFQuestions[Result]^.adrFQuan := adrVDestQuan;
     arFQuestions[Result]^.objFAnswersTable := TAnswersTable.Create;
     //InitAnswerQueue(arFQuestions[Result]^.FAnswerQueue);
  end;

  adrVSourceQuan := adrVQuestion^.adrFQuan^.adrFSon;
  New(adrVDestQuan^.adrFSon);
  adrVDestQuan := adrVDestQuan^.adrFSon;
  VStack := nil;

  repeat
     with adrVDestQuan^ do
     begin
        boolFUnQuan := adrVSourceQuan^.boolFUnQuan;
        intVVarHigh := High(adrVSourceQuan^.arFVariables);
        SetLength(arFVariables, intVVarHigh + 1);
        for i := 0 to intVVarHigh do
        begin
           arFVariables[i] := DereferencingVariable(adrVSourceQuan^.arFVariables[i]);
           htaFDereferencingVariables.AddLexicalUnit(IntToStr(Integer(adrVSourceQuan^.arFVariables[i])), 1, cardVLexCode);
           htaFDereferencingVariables.Pointers[cardVLexCode] := Pointer(arFVariables[i]);
        end;
        SortVariables(arFVariables);

        DWS_TypeCondition;

        if adrVSourceQuan^.adrFSon <> nil
        then begin
                New(adrFSon);
                Push(VStack, adrVSourceQuan^.adrFSon, adrFSon)
             end
        else
           adrFSon := nil;

        if adrVSourceQuan^.adrFBrother <> nil
        then begin
                New(adrFBrother);
                Push(VStack, adrVSourceQuan^.adrFBrother, adrFBrother)
             end
        else
           adrFBrother := nil;
     end;
  until not Pop(VStack, adrVSourceQuan, adrVDestQuan);

  htaFDereferencingVariables.Destroy;
end;

function TProver.DeleteTrivialQuestion(adrABase: TadrBase;
                                       intATrivQuestIndex: Integer;
                                       boolADeleteTrivQuestion,
                                       boolAQuestInStorageBlock: Boolean): Boolean;
// boolADeleteTrivQuestion - можно удалить квантор с тривиальным вопросом.
// boolAQuestInStorageBlock - если квантор с тривиальным вопросом находится в блоке хранения,
//                            то исключить квантор из блока хранения.
var
  adrVCurrentBase, adrVInitialBase: TadrBase;
  adrVExQuan, adrVTempQuan, adrVWrkQuan: TadrQuantifier;
  i, intVTemp1, intVTemp2: Integer;
  boolVBaseRefuted, boolVTruePredicate: Boolean;
begin
  Result := False;

  with adrABase^.arFQuestions[intATrivQuestIndex]^ do
     if boolADeleteTrivQuestion
     then begin
             adrVExQuan := adrFQuan^.adrFSon;

             if boolAQuestInStorageBlock then
                ExcludeQuanFormulaFromStorageBlock(adrFQuan);
             DisposeQuantifier(adrFQuan);
             DisposeQuestion(adrABase^.arFQuestions[intATrivQuestIndex]);
          end
     else begin
             // Создание копии (E.. ,E.. , ...)
             //------------------------------------------------------//
             adrVExQuan := CopyFormula(adrFQuan^.adrFSon);

             adrVTempQuan := adrVExQuan;
             adrVWrkQuan := adrFQuan^.adrFSon^.adrFBrother;
             while adrVWrkQuan <> nil do
             begin
                adrVTempQuan^.adrFBrother := CopyFormula(adrVWrkQuan);
                adrVTempQuan := adrVTempQuan^.adrFBrother;

                adrVWrkQuan := adrVWrkQuan^.adrFBrother;
             end;
             //------------------------------------------------------//
          end;

  // Удаление ссылки на тривиальный вопрос из базы
  with adrABase^ do
  begin
     intVTemp1 := Length(arFQuestions);
     for i := intATrivQuestIndex to intVTemp1 - 2 do
        arFQuestions[i] := arFQuestions[i + 1];
     SetLength(arFQuestions, intVTemp1 - 1);
  end;


  adrVInitialBase := adrABase;

  repeat
     adrVCurrentBase := adrVInitialBase;

     if adrVExQuan^.adrFBrother <> nil // Подформула с дизъюнктивным ветвлением
     then begin
             adrVInitialBase := CopyBase(adrVInitialBase);

             adrVInitialBase^.adrFNextBase := adrVCurrentBase^.adrFNextBase;
             adrVCurrentBase^.adrFNextBase := adrVInitialBase;

             Inc(intFBasesCount);
          end;

     with adrVCurrentBase^ do
     begin
        // добавление в базу кванторных переменных
        //------------------------------------------------------------//
        intVTemp1 := Length(arFVariables);
        intVTemp2 := Length(adrVExQuan^.arFVariables);
        SetLength(arFVariables, intVTemp1 + intVTemp2);
        for i := 0 to intVTemp2 - 1 do
           arFVariables[intVTemp1 + i] := adrVExQuan^.arFVariables[i];
        //------------------------------------------------------------//

        // добавление атомов в типовое условие базы
        //--------------------------------------------------------------------//
        boolVBaseRefuted := False;

        intVTemp2 := Length(adrVExQuan^.arFTypeCondition);
        i := 0;
        while i <= intVTemp2 - 1 do
        begin
           boolVTruePredicate := False;

           if adrVExQuan^.arFTypeCondition[i]^.Tag = byCFalseTag then
              boolVBaseRefuted := True
           else
              if adrVExQuan^.arFTypeCondition[i]^.Tag <> byCSimplePredicateTag then
                 if TermsIsConstants(adrVExQuan^.arFTypeCondition[i]^.arFTerms) then
                    if CalculatePredicate(adrVExQuan^.arFTypeCondition[i], adrVExQuan^.arFTypeCondition[i]^.arFTerms) = True then
                       boolVTruePredicate := True
                    else
                       boolVBaseRefuted := True;

           if boolVBaseRefuted
           then begin
                   SetBaseRefuted(adrVCurrentBase);

                   if adrVCurrentBase = adrABase then
                      Result := True;

                   i := intVTemp2 + 10;
                end
           else
              if not boolVTruePredicate
              then begin
                      objFAtomsTable.AddAtom(adrVExQuan^.arFTypeCondition[i])
                   end;

           Inc(i);
        end;
        //--------------------------------------------------------------------//

        // добавление новых вопросов к базе
        //-----------------------------------------------------------------//
        adrVTempQuan := adrVExQuan^.adrFSon;
        if (adrVTempQuan <> nil) and (not boolVBaseRefuted)
        then begin
                if FStorageBlock.adrFLastQuestQuan = nil
                then begin
                        FStorageBlock.adrFFirstQuestQuan := adrVTempQuan;
                        FStorageBlock.adrFLastQuestQuan := adrVTempQuan;
                     end
                else begin
                        FStorageBlock.adrFLastQuestQuan^.adrFBrother := adrVTempQuan;
                        FStorageBlock.adrFLastQuestQuan := adrVTempQuan;
                     end;

                repeat
                   intVTemp1 := Length(arFQuestions);
                   SetLength(arFQuestions, intVTemp1 + 1);
                   New(arFQuestions[intVTemp1]);
                   with arFQuestions[intVTemp1]^ do
                   begin
                      adrFQuan := adrVTempQuan;
                      objFAnswersTable := TAnswersTable.Create;
                      //InitAnswerQueue(FAnswerQueue);
                   end;
                   adrVTempQuan := adrVTempQuan^.adrFBrother;
                until adrVTempQuan = nil;
             end;
        //-----------------------------------------------------------------//
     end;

     adrVTempQuan := adrVExQuan^.adrFBrother;
     DisposeQuantifier(adrVExQuan);
     adrVExQuan := adrVTempQuan;
  until adrVExQuan = nil;
end;

function TProver.ApplyRuleOfInference(adrABase: TadrBase;
                                      intAQuestionIndex: Integer): Boolean;
var
  intVTrivQuestIndex: Integer;
  boolVDelTrQuest, boolVQuestInStorageBlock: Boolean;
begin
  if boolFRuleOfInferenceVis and (not boolFkRefutationInProcess)
  then begin
          stgsFOutput.Append('');
          if adrABase^.arFQuestions[intAQuestionIndex]^.objFAnswersTable.arPCurrentAnswer <> nil then
             stgsFOutput.Append('w' + IntToStr(intFRuleOfInferenceCount) + ' : ' + IntToStr(intAQuestionIndex + 1) + '   Подстановка: ' + SubstitutionAsString(adrABase^.arFQuestions[intAQuestionIndex]))
          else
             stgsFOutput.Append('w' + IntToStr(intFRuleOfInferenceCount) + ' : ' + IntToStr(intAQuestionIndex + 1));
       end
  else
     if boolFDWS_DTQVis and (not boolFkRefutationInProcess)
     then begin
             stgsFOutput.Append('');
             stgsFOutput.Append('{--- w' + IntToStr(intFRuleOfInferenceCount) + ' ---}');
          end;

  if adrABase^.arFQuestions[intAQuestionIndex]^.objFAnswersTable.arPCurrentAnswer = nil
     // У тривиального вопроса всегда пустая ответная очередь
  then begin
          intVTrivQuestIndex := intAQuestionIndex;
          boolVDelTrQuest := intFBasesCount = 1;
          boolVQuestInStorageBlock := boolVDelTrQuest;
       end
  else begin
          if boolFDWS_DTQVis then
             stgsFOutput.Append('Дублирование с уточнением: ' + IntToStr(intAQuestionIndex + 1) + '   Подстановка: ' + SubstitutionAsString(adrABase^.arFQuestions[intAQuestionIndex]));

          intVTrivQuestIndex := DuplicateWithSpecification(adrABase, intAQuestionIndex);
          adrABase^.arFQuestions[intAQuestionIndex]^.objFAnswersTable.MoveAnswerQueue;
         // adrABase^.arFQuestions[intAQuestionIndex]^.FAnswerQueue.adrFCurrentLink := adrABase^.arFQuestions[intAQuestionIndex]^.FAnswerQueue.adrFCurrentLink^.adrFNextLink;

          if boolFDWS_DTQVis then
             if not boolFkRefutationInProcess then
                DisplayFormulaByBase(FStorageBlock.adrFFirstBase, True)
             else
                DisplayFormulaByBase(adrABase, True);

          boolVDelTrQuest := True;
          boolVQuestInStorageBlock := False;
       end;

  if boolFDWS_DTQVis then
     stgsFOutput.Append('Удаление тривиального вопроса: ' + IntToStr(intVTrivQuestIndex + 1));
  Result := DeleteTrivialQuestion(adrABase,
                                  intVTrivQuestIndex,
                                  boolVDelTrQuest,
                                  boolVQuestInStorageBlock);

  if boolFRuleOfInferenceVis or boolFDWS_DTQVis then
     if not boolFkRefutationInProcess then
        DisplayFormulaByBase(FStorageBlock.adrFFirstBase, True)
     else
        DisplayFormulaByBase(adrABase, True);
end;

function TProver.QuestionHasAnswers(adrABase: TadrBase;
                                    intAQuestionIndex: Integer): Boolean;
begin
  if adrABase^.arFQuestions[intAQuestionIndex]^.objFAnswersTable.arPCurrentAnswer <> nil
  then begin
          Result := True;
          AddNewAnswers(adrABase, intAQuestionIndex);
       end
  else
     Result := AddNewAnswers(adrABase, intAQuestionIndex);

  {if Result
  then begin
          CombineResemblingAnswers(adrABase^.arFQuestions[intAQuestionIndex]^.FAnswerQueue);
       end;}
end;

function TProver.Strategy(adrABase: TadrBase;
                          var intAQuestionIndex: Integer): Boolean;
// Процедура определяет последовательность применения правила вывода.
// intFQuestionIndex станет равным -1, если больше ни один вопрос не имеет ответов.
// Функция вернет True, если стратегия k-опровержения опровергнула одну из двух расщепляющихся баз
// (текущая база adrABase заменится опровергнутой базой).
var
  intVk: Integer;

  function kRefutation: Boolean;
  var
    adrVWrkBase, adrVTempBase: TadrBase;
    intVTemp1, intVTemp2: Integer;
    boolVTemp1, boolVTemp2, boolVAllAnswers: Boolean;
    ptrVTemp: Pointer;
    boolVFirstBase: Boolean;
  begin
    boolFkRefutationInProcess := True;

    // Сохранение состояния решателя
    //--------------------------------------------------------//
    intVTemp1 := intFRuleOfInferenceCount;
    intVTemp2 := intFRejectedBranchings;
    boolVTemp1 := boolFDWS_DTQVis;
    boolVTemp2 := boolFRefutVis;
    //--------------------------------------------------------//
    //boolFStepVis := False;
    boolFRefutVis := False;

    if boolFDWS_DTQVis then
       stgsFOutput.Append('');

    Result := False;
    boolVAllAnswers := False;
    ptrVTemp := nil;

    repeat

       if boolFRuleOfInferenceVis or boolFDWS_DTQVis then
          stgsFOutput.Append('Создание копии текущей базы');

       adrVWrkBase := CopyBase(adrABase);

       if boolFRuleOfInferenceVis or boolFDWS_DTQVis then
          DisplayFormulaByBase(adrVWrkBase, True);

       ApplyRuleOfInference(adrVWrkBase, intAQuestionIndex);

       if RefuteBase(adrVWrkBase, intVk)
       then begin
               Result := True;
               boolVFirstBase := True;
            end
       else begin
               if boolFRuleOfInferenceVis or boolFDWS_DTQVis
               then begin
                       stgsFOutput.Append('Опровержение за k = ' + IntToStr(intVk) + ' шагов не получено, переход ко второй базе');
                       stgsFOutput.Append('');
                    end;

               if RefuteBase(adrVWrkBase^.adrFNextBase, intVk)
               then begin
                       Result := True;
                       boolVFirstBase := False;
                    end
               else
                  if boolFRuleOfInferenceVis or boolFDWS_DTQVis then
                     stgsFOutput.Append('Опровержение за k = ' + IntToStr(intVk) + ' шагов не получено');
            end;

       if Result
       then begin
               if boolVFirstBase
               then begin
                       adrVWrkBase^.adrFNextBase^.adrFNextBase := adrABase^.adrFNextBase;
                       adrABase^.adrFNextBase := adrVWrkBase^.adrFNextBase;
                    end
               else begin
                       adrVTempBase := adrVWrkBase^.adrFNextBase;
                       adrVWrkBase^.adrFNextBase := adrABase^.adrFNextBase;
                       adrABase^.adrFNextBase := adrVWrkBase;
                       adrVWrkBase := adrVTempBase;
                    end;

               DisposeBase(adrVWrkBase);

               SetBaseRefuted(adrABase);

               Inc(intFRuleOfInferenceCount);
               intFRejectedBranchings := intVTemp2;

               if boolFRuleOfInferenceVis or boolFDWS_DTQVis then
                  stgsFOutput.Append('Замена текущей базы на опровергнутую');
            end
       else begin
               // использовать новый ответ
               boolVAllAnswers := adrABase^.arFQuestions[intAQuestionIndex]^.objFAnswersTable.SelectNextAnswer(ptrVTemp) = False;

               DisposeBase(adrVWrkBase^.adrFNextBase);
               DisposeBase(adrVWrkBase);

               Dec(intFBasesCount);
               intFRuleOfInferenceCount := intVTemp1;
               Inc(intVTemp2);
            end;

    until Result or boolVAllAnswers;

    if boolFRuleOfInferenceVis or boolFDWS_DTQVis then
       stgsFOutput.Append('');

    //--------------------------------------------------------//
    boolFDWS_DTQVis := boolVTemp1;
    boolFRefutVis := boolVTemp2;
    //--------------------------------------------------------//
    if not Result
    then begin
            boolFAnswered := False;
            boolFEnableDisjunctiveBranching := True;
         end;
    boolFkRefutationInProcess := False;
  end;

const
  intCkMax: Integer = 10;
var
  boolVSelected: Boolean;
begin
  Result := False;
  boolVSelected := False;
  intVk := 1;
  repeat
     Inc(intAQuestionIndex);

     if intAQuestionIndex > High(adrABase^.arFQuestions) then
        if Length(adrABase^.arFQuestions) > 0
        then begin
                intAQuestionIndex := 0;

                if boolFAnswered
                then begin
                        boolFAnswered := False;
                        //boolFEnableDisjunctiveBranching := False;
                     end
                else
                   if boolFkRefutationInProcess then
                      intAQuestionIndex := -1
                   else
                      if boolFEnableDisjunctiveBranching
                      then begin
                              if (intVk > intCkMax) or (not boolFkRefutationStrategy) then
                                 intAQuestionIndex := -1
                              else
                                 Inc(intVk);
                           end
                      else
                         boolFEnableDisjunctiveBranching := True;
             end
        else
           intAQuestionIndex := -1;

     if intAQuestionIndex <> -1
     then begin
             if adrABase^.arFQuestions[intAQuestionIndex]^.adrFQuan^.adrFSon^.adrFBrother = nil then
                boolVSelected := QuestionHasAnswers(adrABase, intAQuestionIndex)
             else
                if boolFEnableDisjunctiveBranching and (not boolFkRefutationInProcess) then // Дизъюнктивное ветвление во время k-опровержения запрещено
                   if QuestionHasAnswers(adrABase, intAQuestionIndex) then
                      if (adrABase^.arFQuestions[intAQuestionIndex]^.adrFQuan^.adrFSon^.adrFBrother^.adrFBrother = nil) and // V.. (E.. , E..)
                         (adrABase^.arFQuestions[intAQuestionIndex]^.objFAnswersTable.arPCurrentAnswer <> nil) // Вопрос с дизъюнктивным ветвлением не тривиальный
                      then begin
                              if (intVk <= intCkMax) and boolFkRefutationStrategy then
                                 Result := kRefutation
                              else
                                 boolVSelected := True;
                           end
                      else
                         boolVSelected := True;
          end
     else
        boolVSelected := True;
  until boolVSelected or Result;
end;

function TProver.RefuteBase(adrABase: TadrBase;
                            intAStepsMax: Integer): Boolean;
var
  boolVModelConjunct: Boolean;
  intVQuestionIndex: Integer;
begin
  Result := adrABase^.objFAtomsTable = nil;
  boolVModelConjunct := False;

  //boolFEnableDisjunctiveBranching := False;
  boolFAnswered := False;
  intVQuestionIndex := -1;

  while (not Result) and (not boolVModelConjunct) do
  begin
     if Strategy(adrABase, intVQuestionIndex) then
        Result := True
     else
        if intVQuestionIndex <> - 1
        then begin
                Inc(intFRuleOfInferenceCount);
                Result := ApplyRuleOfInference(adrABase, intVQuestionIndex);
                boolFAnswered := True;
                if intAStepsMax <> -1
                then begin
                        Dec(intAStepsMax);
                        if intAStepsMax = 0 then
                           boolVModelConjunct := True;
                     end;
             end
        else
           boolVModelConjunct := True;

     if TimeIsOver then
        boolVModelConjunct := True;

     if not boolFkRefutationInProcess then
        if boolFkRefutationStrategy then
           frmCourseOfProof.FStatusBar.SimpleText := 'Опровергнуто баз: ' + IntToStr(intFBaseIndex - 1) + ' / ' + IntToStr(intFBasesCount) + '    Шагов поиска: ' + IntToStr(intFRuleOfInferenceCount) + '    Отвергнуто попыток ветвления: ' + IntToStr(intFRejectedBranchings)
        else
           frmCourseOfProof.FStatusBar.SimpleText := 'Опровергнуто баз: ' + IntToStr(intFBaseIndex - 1) + ' / ' + IntToStr(intFBasesCount) + '    Шагов поиска: ' + IntToStr(intFRuleOfInferenceCount);
  end;
end;

function TProver.TimeIsOver: Boolean;
begin
  cardFTimeCurrent := GetTickCount;
  Result := cardFTimeCurrent > cardFTimeEnd;
end;

function TProver.Prove: Boolean;
var
  adrVBase: TadrBase;
  boolVTemp: Boolean;
begin
  Result := True;
  intFRuleOfInferenceCount := 0;
  intFBaseIndex := 1;
  cardFTimeEnd := cardFTimeEnd + GetTickCount;

  boolVTemp := boolFDisplayBasesOnly;
  boolFDisplayBasesOnly := False;
  DisplayFormulaByBase(FStorageBlock.adrFFirstBase, True);
  boolFDisplayBasesOnly := boolVTemp;


  adrVBase := FStorageBlock.adrFFirstBase;

  while (adrVBase <> nil) {and Result} do
  begin
     if boolFRuleOfInferenceVis or boolFDWS_DTQVis
     then begin
             stgsFOutput.Append('');
             stgsFOutput.Append('***База № ' + IntToStr(intFBaseIndex) + '***');
          end;

     if Result then
        Result := RefuteBase(adrVBase, -1)
     else
        RefuteBase(adrVBase, -1);

     if boolFRefutVis and Result
     then begin
             stgsFOutput.Append('');
             DisplayFormulaByBase(FStorageBlock.adrFFirstBase, True);
          end;

     adrVBase := adrVBase^.adrFNextBase;
     Inc(intFBaseIndex);
     if TimeIsOver and (adrVBase <> nil) then
        Result := False;
  end;




  if (not boolFRuleOfInferenceVis) and (not boolFDWS_DTQVis) and (not boolFRefutVis)
  then begin
          stgsFOutput.Append('');
          DisplayFormulaByBase(FStorageBlock.adrFFirstBase, True);
       end;
  stgsFOutput.Append('');

  if Result then
     stgsFOutput.Append('Теорема доказана')
  else if TimeIsOver then
          stgsFOutput.Append('Закончилось время, отведенное для доказательства')
       else
          stgsFOutput.Append('Получены модельные конъюнкты');

  stgsFOutput.Append('Шагов поиска: ' + IntToStr(intFRuleOfInferenceCount));
  if boolFkRefutationStrategy then
     stgsFOutput.Append('Отвергнуто попыток ветвления: ' + IntToStr(intFRejectedBranchings));

  frmCourseOfProof.FStatusBar.SimpleText := 'Процесс доказательства завершен';

  DisposeTermsPredicates;
  DisposeAllBases;
  DisposeQuestQuantifiers;
end;

end.