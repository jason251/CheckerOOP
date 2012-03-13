//---------------------------------------------------------------------------


#pragma hdrstop

#include "uTermsAndFormulasStructures.h"

//---------------------------------------------------------------------------

#pragma package(smart_init)

unit uTermsAndFormulasStructures;

interface

const
  byCIntegerConstantTag     = 1;
  byCRealConstantTag        = 2;
  byCStringConstantTag      = 3;
  { ... }
  byCVariableTag            = 13;
  { ... }
  byCTermVariantsTag        = 24;

  byCSimplePredicateTag     = 38;
  byCCalculatedPredicateTag = 39;
  byCTrueTag                = 40;
  byCFalseTag               = 41;
  { ... }
  byCEqualTag               = 46;
  byCLessGreaterTag         = 47;
  byCLessTag                = 48;
  byCLessEqualTag           = 49;
  byCGreaterTag             = 50;
  byCGreaterEqualTag        = 51;


type
                            { СТРУКТУРЫ ТЕРМОВ }
  {--------------------------------------------------------------------------}
  {--------------------------------------------------------------------------}
  TTerm = record
             Tag: Byte;
             ptrFReference: Pointer;
          end;

  TArrayOfTerm = array of TTerm;




  TIntegerConstant = record { Tag = 1 }
                        cardFLexicalCode: Cardinal;
                        intFValue: Integer;
                     end;
  TadrIntegerConstant = ^TIntegerConstant;

  TRealConstant = record { Tag = 2 }
                     cardFLexicalCode: Cardinal;
                     extFValue: Extended;
                  end;
  TadrRealConstant = ^TRealConstant;

  TStringConstant = record { Tag = 3 }
                       cardFLexicalCode: Cardinal;
                    end;
  TadrStringConstant = ^TStringConstant;

  { Диапазон целых }
  {-----------------------------------------------------}
  TIntegerRange_00 = record { Tag = 4 }         { (A-B) }
                         A: TIntegerConstant;
                         B: TIntegerConstant;
                      end;
  TIntegerRange_10 = record { Tag = 5 }         { [A-B) }
                         A: TIntegerConstant;
                         B: TIntegerConstant;
                      end;
  TIntegerRange_01 = record { Tag = 6 }         { (A-B] }
                         A: TIntegerConstant;
                         B: TIntegerConstant;
                      end;
  TIntegerRange_11 = record { Tag = 7 }         { [A-B] }
                         A: TIntegerConstant;
                         B: TIntegerConstant;
                      end;
  {-----------------------------------------------------}


  { Диапазон вещественных }
  {--------------------------------------------------}
  TRealRange_00 = record { Tag = 8 }         { (A-B) }
                     A: TRealConstant;
                     B: TRealConstant;
                  end;
  TRealRange_10 = record { Tag = 9 }         { [A-B) }
                     A: TRealConstant;
                     B: TRealConstant;
                  end;
  TRealRange_01 = record { Tag = 10 }        { (A-B] }
                     A: TRealConstant;
                     B: TRealConstant;
                  end;
  TRealRange_11 = record { Tag = 11 }        { [A-B] }
                     A: TRealConstant;
                     B: TRealConstant;
                  end;
  {--------------------------------------------------}


  TVariable = record { Tag = 13 }
                 cardFLexicalCode: Cardinal;
              end;
  TadrVariable = ^TVariable;
  TArrayOfadrVariable = array of TadrVariable; // Бинарный поиск => элементы должны быть упорядочены


  TTermVariants = record { Tag = 39 }
                     arFTerms: TArrayOfTerm;
                     intFCurrentIndex: Integer;
                  end;
  TadrTermVariants = ^TTermVariants;
  {--------------------------------------------------------------------------}
  {--------------------------------------------------------------------------}




                             { СТРУКТУРЫ ФОРМУЛ }
  {--------------------------------------------------------------------------}
  {--------------------------------------------------------------------------}
  { True    Tag = 40
    False   Tag = 41
    =       Tag = 46
    <>      Tag = 47
    <       Tag = 48
    <=      Tag = 49
    >       Tag = 50
    >=      Tag = 51 }

  TAtom = record
             Tag: Byte;
             cardFName: Cardinal; // лексический код имени предиката
             arFTerms: TArrayOfTerm; // список параметров
             intFReferencesCount: Integer; // поле для подсчета количества ссылок на эту область памяти
          end;
  TadrAtom = ^TAtom;
  TArrayOfadrAtom = array of TadrAtom; // Конъюнкт (множество атомов)
  {--------------------------------------------------------------------------}
  {--------------------------------------------------------------------------}




  TArrayOfInteger = array of Integer;

  TCustomTable = class
  private
     arFHashingElements: TArrayOfInteger;
     cardFQuantityUsedElements: Cardinal;

     function AddElement(ptrAElement: Pointer;
                         var intAIndexInTable: Integer): Boolean;
     function SearchElement(ptrAElement: Pointer;
                            var intAIndexInTable: Integer): Boolean;
     function HashFunction(ptrAElement: Pointer): Cardinal;

     procedure Expansion;
     procedure ReHashingTable(cardANewSize: Cardinal);
     function TakeNextPrimeNumber(cardAOldPrimeNumber: Cardinal): Cardinal;

     function GetHashSize: Cardinal;

     function HashCode(ptrAElement: Pointer): Cardinal; dynamic; abstract;
     function Equal(ptrAElement: Pointer;
                    intAIndexOfElementInTable: Integer): Boolean; dynamic; abstract;
     procedure IncreaseTable(cardACountOfNewElements: Cardinal); dynamic; abstract;
     function PointerToElement(intAElementIndex: Integer): Pointer; dynamic; abstract;
  public
     constructor Create; overload;
     constructor Create(cardAHashSize: Cardinal); overload;
     destructor Destroy; override;

     property cardPHashSize: Cardinal
        read GetHashSize;
  end;





  TAtomsTable = class(TCustomTable)
  private
     arFTable: array of TArrayOfadrAtom;

     function HashCode(ptrAElement: Pointer): Cardinal; override;
     function Equal(ptrAElement: Pointer;
                    intAIndexOfElementInTable: Integer): Boolean; override;
     procedure IncreaseTable(cardACountOfNewElements: Cardinal); override;
     function PointerToElement(intAElementIndex: Integer): Pointer; override;
  public
     procedure AddAtom(adrAAtom: TadrAtom);
     function SearchAtoms(cardAGeneralName: Cardinal;
                          var arVAtoms: TArrayOfadrAtom): Boolean;
     function GetAllAtoms: TArrayOfadrAtom;

     destructor Destroy; override;
  end;





  // Ответная очередь
  //-------------------------------------------------------------//
  TadrAnswerQueueLink = ^TAnswerQueueLink;
  TAnswerQueueLink = record
                        intFIndexInTable: Integer;
                        adrFNextLink: TadrAnswerQueueLink;
                     end;
  TAnswerQueue = record
                    adrFFirstLink: TadrAnswerQueueLink;
                    adrFLastLink: TadrAnswerQueueLink;
                 end;
  //-------------------------------------------------------------//

  TAnswersTable = class(TCustomTable)
  private
     arFTable: array of TArrayOfTerm;

     FAnswerQueue: TAnswerQueue; // ответная очередь (еще не использованные ответные подстановки)

     procedure AnswerToQueue(intAIndexInTable: Integer; boolAToEnd: Boolean);
     procedure DisposeAnswerQueue;

     function GetCurrentAnswer: TArrayOfTerm;

     function HashCode(ptrAElement: Pointer): Cardinal; override;
     function Equal(ptrAElement: Pointer;
                    intAIndexOfElementInTable: Integer): Boolean; override;
     procedure IncreaseTable(cardACountOfNewElements: Cardinal); override;
     function PointerToElement(intAElementIndex: Integer): Pointer; override;
  public
     function AddAnswer(const arAAnswerSubstitution: TArrayOfTerm;
                        boolAToEndOfQueue: Boolean): Boolean;
     procedure MoveAnswerQueue;
     function SelectNextAnswer(var ptrATemp: Pointer): Boolean;
     procedure CopyUnusedAnswersFromTable(const objASourceTable: TAnswersTable);

     class function CopyAnswersTable(const objASourceTable: TAnswersTable): TAnswersTable;

     constructor Create; overload;
     constructor Create(cardAHashSize: Cardinal); overload;
     destructor Destroy; override;

     property arPCurrentAnswer: TArrayOfTerm
        read GetCurrentAnswer;
  end;



  function NewAtom: TadrAtom;
  function CopyReferenceToAtom(adrAAtom: TadrAtom): TadrAtom;
  procedure ExcludeReferenceToAtom(adrAAtom: TadrAtom);

  procedure SortVariables(var arAVariables: TArrayOfadrVariable);
  function SearchVariable(adrAVariable: TadrVariable;
                          const arAVariables: TArrayOfadrVariable): Integer;

implementation

{ TCustomTable }

constructor TCustomTable.Create;
begin
  inherited Create;
  SetLength(arFHashingElements, 7);
  cardFQuantityUsedElements := 0;
end;

constructor TCustomTable.Create(cardAHashSize: Cardinal);
begin
  inherited Create;
  SetLength(arFHashingElements, cardAHashSize);
  cardFQuantityUsedElements := 0;
end;

destructor TCustomTable.Destroy;
begin
  Finalize(arFHashingElements);
  inherited Destroy;
end;

function TCustomTable.AddElement(ptrAElement: Pointer;
                                 var intAIndexInTable: Integer): Boolean;
var
  cardVHashIndex: Cardinal;
begin
  cardVHashIndex := HashFunction(ptrAElement);

  if arFHashingElements[cardVHashIndex] = 0
  then begin
          Result := False;

          if (cardFQuantityUsedElements + 2) > (Length(arFHashingElements) * 0.9)
          then begin
                  Expansion;
                  cardVHashIndex := HashFunction(ptrAElement);
               end;

          Inc(cardFQuantityUsedElements);
          IncreaseTable(1);
          arFHashingElements[cardVHashIndex] := cardFQuantityUsedElements;
       end
  else
     Result := True;

  intAIndexInTable := arFHashingElements[cardVHashIndex] - 1;
end;

function TCustomTable.SearchElement(ptrAElement: Pointer;
                                    var intAIndexInTable: Integer): Boolean;
var
  cardVHashIndex: Cardinal;
begin
  cardVHashIndex := HashFunction(ptrAElement);
  if arFHashingElements[cardVHashIndex] = 0
  then begin
          Result := False;
          intAIndexInTable := -1;
       end
  else begin
          Result := True;
          intAIndexInTable := arFHashingElements[cardVHashIndex] - 1;
       end;
end;

procedure TCustomTable.Expansion;
begin
  ReHashingTable( TakeNextPrimeNumber(Length(arFHashingElements)) );
end;

function TCustomTable.TakeNextPrimeNumber(cardAOldPrimeNumber: Cardinal): Cardinal;
  // вычисляет следующее за cardAOldPrimeNumber простое число,
  // отстоящее не менее, чем на 10 процентов
var
  i, j: Cardinal;
  boolVIsPrimeNumber: Boolean;
begin
  // увеличиваем на 10 процентов
  Result := cardAOldPrimeNumber + cardAOldPrimeNumber div 10 + 1;
  // рассматриваем только нечетные числа, т.к. простые среди них
  if (Result mod 2) = 0 then
     Inc(Result);

  repeat
     boolVIsPrimeNumber := True;
     Result := Result + 2;
     i := 3;
     j := Result div 3 + 1; // диапазон делителей
     while boolVIsPrimeNumber and (i < j) do
        if (Result mod i) = 0 then
           boolVIsPrimeNumber := False
        else i := i + 2;
  until boolVIsPrimeNumber;
end;

function TCustomTable.HashFunction(ptrAElement: Pointer): Cardinal;
var
  cardVSize, cardVTemp, i: Cardinal;
  boolVFinded: Boolean;
begin
  cardVSize := Length(arFHashingElements);

  Result := HashCode(ptrAElement) mod cardVSize;

  if Result = 0 then
     cardVTemp := 1
  else
     cardVTemp := Result;
  i := 1;
  boolVFinded := False;

  repeat
     if arFHashingElements[Result] = 0 then
        boolVFinded := True
     else
        if Equal(ptrAElement, arFHashingElements[Result] - 1) then
           boolVFinded := True
        else begin
                Inc(i);
                Result := cardVTemp * i mod cardVSize;
             end;
  until boolVFinded;
end;

procedure TCustomTable.ReHashingTable(cardANewSize: Cardinal);
var
  arVOld: TArrayOfInteger;
  i: Integer;
begin
  arVOld := arFHashingElements;
  arFHashingElements := nil;
  SetLength(arFHashingElements, cardANewSize);

  for i := 0 to High(arVOld) do
     if arVOld[i] <> 0 then
        arFHashingElements[ HashFunction(PointerToElement(arVOld[i] - 1)) ] := arVOld[i];

  Finalize(arVOld);
end;

function TCustomTable.GetHashSize: Cardinal;
begin
  Result := Length(arFHashingElements);
end;




{ TAtomsTable }

procedure TAtomsTable.AddAtom(adrAAtom: TadrAtom);
var
  intAIndex, intVTemp: Integer;
begin
  AddElement(@adrAAtom^.cardFName, intAIndex);

  intVTemp := Length(arFTable[intAIndex]);
  SetLength(arFTable[intAIndex], intVTemp + 1);
  arFTable[intAIndex][intVTemp] := CopyReferenceToAtom(adrAAtom);
end;

function TAtomsTable.SearchAtoms(cardAGeneralName: Cardinal;
                                 var arVAtoms: TArrayOfadrAtom): Boolean;
var
  intAIndex: Integer;
begin
  Result := SearchElement(@cardAGeneralName, intAIndex);
  if Result then
     arVAtoms := arFTable[intAIndex]
  else
     arVAtoms := nil;
end;

function TAtomsTable.GetAllAtoms: TArrayOfadrAtom;
var
  i, j, intVTemp1, intVTemp2: Integer;
begin
  Result := nil;
  intVTemp1 := 0;

  for i := 0 to High(arFTable) do
  begin
     intVTemp2 := Length(arFTable[i]);
     SetLength(Result, intVTemp1 + intVTemp2);

     for j := 0 to intVTemp2 - 1 do
        Result[intVTemp1 + j] := arFTable[i][j];

     intVTemp1 := intVTemp1 + intVTemp2
  end;
end;

function TAtomsTable.HashCode(ptrAElement: Pointer): Cardinal;
begin
  Result := Cardinal(ptrAElement^);
end;

function TAtomsTable.Equal(ptrAElement: Pointer;
                           intAIndexOfElementInTable: Integer): Boolean;
begin
  Result := Cardinal(ptrAElement^) = arFTable[intAIndexOfElementInTable][0].cardFName;
end;

procedure TAtomsTable.IncreaseTable(cardACountOfNewElements: Cardinal);
begin
  SetLength(arFTable, Length(arFTable) + cardACountOfNewElements);
end;

function TAtomsTable.PointerToElement(intAElementIndex: Integer): Pointer;
begin
  Result := @arFTable[intAElementIndex][0].cardFName;
end;

destructor TAtomsTable.Destroy;
var
  i, j: Integer;
begin
  for i := 0 to High(arFTable) do
  begin
     for j := 0 to High(arFTable[i]) do
        ExcludeReferenceToAtom(arFTable[i][j]);
     Finalize(arFTable[i]);
  end;
  Finalize(arFTable);

  inherited Destroy;
end;















{ TAnswersTable }

constructor TAnswersTable.Create;
begin
  inherited Create(3);

  FAnswerQueue.adrFFirstLink := nil;
  FAnswerQueue.adrFLastLink := nil;
end;

constructor TAnswersTable.Create(cardAHashSize: Cardinal);
begin
  inherited Create(cardAHashSize);

  FAnswerQueue.adrFFirstLink := nil;
  FAnswerQueue.adrFLastLink := nil;
end;

destructor TAnswersTable.Destroy;
var
  i: Integer;
begin
  for i := 0 to High(arFTable) do
     Finalize(arFTable[i]);
  Finalize(arFTable);

  DisposeAnswerQueue;

  inherited Destroy;
end;

procedure TAnswersTable.DisposeAnswerQueue;
var
  adrVTempLink: TadrAnswerQueueLink;
begin
  with FAnswerQueue do
  begin
     while adrFFirstLink <> nil do
     begin
        adrVTempLink := adrFFirstLink^.adrFNextLink;
        Dispose(adrFFirstLink);
        adrFFirstLink := adrVTempLink;
     end;
     adrFLastLink := nil;
  end;
end;

function TAnswersTable.AddAnswer(const arAAnswerSubstitution: TArrayOfTerm;
                                 boolAToEndOfQueue: Boolean): Boolean;
var
  intAIndex: Integer;
begin
  if not AddElement(arAAnswerSubstitution, intAIndex)
  then begin
          Result := True;
          arFTable[intAIndex] := Copy(arAAnswerSubstitution);
          AnswerToQueue(intAIndex, boolAToEndOfQueue);
       end
  else
     Result := False;
end;

function TAnswersTable.GetCurrentAnswer: TArrayOfTerm;
begin
  if FAnswerQueue.adrFFirstLink <> nil then
     Result := arFTable[FAnswerQueue.adrFFirstLink^.intFIndexInTable]
  else
     Result := nil;
end;

procedure TAnswersTable.MoveAnswerQueue;
begin
  with FAnswerQueue do
     if adrFFirstLink <> nil then
        adrFFirstLink := adrFFirstLink^.adrFNextLink;
end;

function TAnswersTable.SelectNextAnswer(var ptrATemp: Pointer): Boolean;

   procedure Exchange(adrAFirst, adrASecond: TadrAnswerQueueLink);
   var
     intVTemp: Integer;
   begin
     intVTemp := adrAFirst^.intFIndexInTable;
     adrAFirst^.intFIndexInTable := adrASecond^.intFIndexInTable;
     adrASecond^.intFIndexInTable := intVTemp;
   end;

begin
  Result := False;
  with FAnswerQueue do
     if adrFFirstLink <> nil then
        if ptrATemp = nil
        then begin
                if adrFFirstLink^.adrFNextLink <> nil
                then begin
                        Result := True;
                        Exchange(adrFFirstLink, adrFFirstLink^.adrFNextLink);
                        ptrATemp := adrFFirstLink^.adrFNextLink;
                     end;
             end
        else begin
                Exchange(adrFFirstLink, TadrAnswerQueueLink(ptrATemp));
                ptrATemp := TadrAnswerQueueLink(ptrATemp)^.adrFNextLink;
                if ptrATemp <> nil
                then begin
                        Result := True;
                        Exchange(adrFFirstLink, TadrAnswerQueueLink(ptrATemp));
                     end;
             end;
end;

procedure TAnswersTable.CopyUnusedAnswersFromTable(const objASourceTable: TAnswersTable);
var
  adrVTempLink: TadrAnswerQueueLink;
begin
  adrVTempLink := objASourceTable.FAnswerQueue.adrFFirstLink;

  while adrVTempLink <> nil do
  begin
     Self.AddAnswer( objASourceTable.arFTable[adrVTempLink^.intFIndexInTable], True );
     adrVTempLink := adrVTempLink^.adrFNextLink;
  end;
end;

class function TAnswersTable.CopyAnswersTable(const objASourceTable: TAnswersTable): TAnswersTable;
var
  i: Integer;
  adrVSourceLink, adrVDestLink, adrVTempLink: TadrAnswerQueueLink;
begin
  Result := TAnswersTable.Create(objASourceTable.cardPHashSize);
  Result.arFHashingElements := Copy(objASourceTable.arFHashingElements);

  SetLength(Result.arFTable, Length(objASourceTable.arFTable));
  for i := 0 to High(objASourceTable.arFTable) do
     Result.arFTable[i] := Copy(objASourceTable.arFTable[i]);

  Result.cardFQuantityUsedElements := objASourceTable.cardFQuantityUsedElements;

  adrVSourceLink := objASourceTable.FAnswerQueue.adrFFirstLink;
  if adrVSourceLink <> nil
  then begin
          New(adrVDestLink);
          Result.FAnswerQueue.adrFFirstLink := adrVDestLink;

          repeat
             adrVDestLink^.intFIndexInTable := adrVSourceLink^.intFIndexInTable;

             adrVSourceLink := adrVSourceLink^.adrFNextLink;
             if adrVSourceLink <> nil
             then begin
                     adrVTempLink := adrVDestLink;
                     New(adrVDestLink);
                     adrVTempLink^.adrFNextLink := adrVDestLink;
                  end
             else begin
                     adrVDestLink^.adrFNextLink := nil;
                     Result.FAnswerQueue.adrFLastLink := adrVDestLink;
                  end;
          until adrVSourceLink = nil;
       end;
end;

procedure TAnswersTable.AnswerToQueue(intAIndexInTable: Integer;
                                      boolAToEnd: Boolean);
var
  adrVNewLink: TadrAnswerQueueLink;
begin
  New(adrVNewLink);
  adrVNewLink^.intFIndexInTable := intAIndexInTable;

  with FAnswerQueue do
     if adrFFirstLink = nil
     then begin
             adrVNewLink^.adrFNextLink := nil;
             adrFFirstLink := adrVNewLink;
             adrFLastLink := adrVNewLink;
          end
     else
        if boolAToEnd
        then begin
                adrVNewLink^.adrFNextLink := nil;

                adrFLastLink^.adrFNextLink := adrVNewLink;
                adrFLastLink := adrVNewLink;
             end
        else begin
                adrVNewLink^.adrFNextLink := adrFFirstLink;
                adrFFirstLink := adrVNewLink;
             end;
end;

function TAnswersTable.HashCode(ptrAElement: Pointer): Cardinal;
var
  i: Integer;
  arVAnswerSubstitution: TArrayOfTerm;
begin
  Result := 0;

  arVAnswerSubstitution := TArrayOfTerm(ptrAElement);

  for i := 0 to High(arVAnswerSubstitution) do
     Result := Result + Cardinal(arVAnswerSubstitution[i].ptrFReference);
end;

function TAnswersTable.Equal(ptrAElement: Pointer;
                             intAIndexOfElementInTable: Integer): Boolean;
var
  i, intVHigh: Integer;
  arVAnswerSubstitution: TArrayOfTerm;
begin
  Result := False;

  arVAnswerSubstitution := TArrayOfTerm(ptrAElement);
  intVHigh := High(arVAnswerSubstitution);

  if intVHigh = High(arFTable[intAIndexOfElementInTable])
  then begin
          i := 0;
          while i <= intVHigh do
             if arVAnswerSubstitution[i].ptrFReference = arFTable[intAIndexOfElementInTable][i].ptrFReference then
                Inc(i)
             else
                i := intVHigh + 10;

          if i = (intVHigh + 1) then
             Result := True;
       end;
end;

procedure TAnswersTable.IncreaseTable(cardACountOfNewElements: Cardinal);
begin
  SetLength(arFTable, Length(arFTable) + cardACountOfNewElements);
end;

function TAnswersTable.PointerToElement(intAElementIndex: Integer): Pointer;
begin
  Result := arFTable[intAElementIndex];
end;










function NewAtom: TadrAtom;
begin
  New(Result);
  Result^.intFReferencesCount := 1;
end;

function CopyReferenceToAtom(adrAAtom: TadrAtom): TadrAtom;
begin
  Inc(adrAAtom^.intFReferencesCount);
  Result := adrAAtom;
end;

procedure ExcludeReferenceToAtom(adrAAtom: TadrAtom);
begin
  with adrAAtom^ do
     if intFReferencesCount = 1
     then begin
             Finalize(arFTerms);
             Dispose(adrAAtom);
          end
     else
        Dec(intFReferencesCount);
end;






procedure SortVariables(var arAVariables: TArrayOfadrVariable);
var
  i, intVLength: Integer;
  adrVTemp: TadrVariable;
  boolVSorted: Boolean;
begin
  intVLength := Length(arAVariables);
  if intVLength > 0
  then begin
          // 1) упорядочивание адресов - работает быстрее, но всегда разный вывод на экран
          //----------------------------------------------------------------//
          {repeat
             Dec(intVLength);
             boolVSorted := True;
             for i := 0 to intVLength - 1 do
                if Cardinal(arAVariables[i]) > Cardinal(arAVariables[i + 1])
                then begin
                        adrVTemp := arAVariables[i];
                        arAVariables[i] := arAVariables[i + 1];
                        arAVariables[i + 1] := adrVTemp;
                        boolVSorted := False;
                     end;
          until boolVSorted;}
          //----------------------------------------------------------------//

          // 2) упорядочивание лексических кодов
          //--------------------------------------------------------------------------------//
          repeat
             Dec(intVLength);
             boolVSorted := True;
             for i := 0 to intVLength - 1 do
                if arAVariables[i]^.cardFLexicalCode > arAVariables[i + 1]^.cardFLexicalCode
                then begin
                        adrVTemp := arAVariables[i];
                        arAVariables[i] := arAVariables[i + 1];
                        arAVariables[i + 1] := adrVTemp;
                        boolVSorted := False;
                     end;
          until boolVSorted;
          //--------------------------------------------------------------------------------//
       end;
end;

function SearchVariable(adrAVariable: TadrVariable;
                        const arAVariables: TArrayOfadrVariable): Integer;
  // Используется бинарный поиск.
  // Ф-я вернет индекс переменной в массиве переменных.
  // Ф-я вернет отрицательное число, если переменная в массиве не найдена
  //  (при этом Abs(Result)-1 будет обозначать индекс в массиве переменных,
  //   на который нужно вставить эту переменную для сохранения упорядоченного состояния).
var
  intVLow, intVHigh, intVMiddle: Integer;
begin
  intVHigh := High(arAVariables);
  if intVHigh <> -1
  then begin
          intVLow := 0;
          intVMiddle := (intVLow + intVHigh) div 2;

          // 1) бинарный поиск относительно адресов
          //-----------------------------------------------------------------------//
          {while (Cardinal(adrAVariable) <> Cardinal(arAVariables[intVMiddle])) and
                (intVLow <= intVHigh) do
          begin
             if Cardinal(adrAVariable) < Cardinal(arAVariables[intVMiddle]) then
                intVHigh := intVMiddle - 1
             else
                intVLow := intVMiddle + 1;

             intVMiddle := (intVLow + intVHigh) div 2;
          end;}
          //-----------------------------------------------------------------------//

          // 2) бинарный поиск относительно лексических кодов
          //--------------------------------------------------------------------------------------//
          while (adrAVariable^.cardFLexicalCode <> arAVariables[intVMiddle]^.cardFLexicalCode) and
                (intVLow <= intVHigh) do
          begin
             if adrAVariable^.cardFLexicalCode < arAVariables[intVMiddle]^.cardFLexicalCode then
                intVHigh := intVMiddle - 1
             else
                intVLow := intVMiddle + 1;

             intVMiddle := (intVLow + intVHigh) div 2;
          end;
          //--------------------------------------------------------------------------------------//

          if intVLow <= intVHigh then
             Result := intVMiddle
          else
             Result := -intVLow - 1;
       end
  else
     Result := -1;
end;

end.