//---------------------------------------------------------------------------


#pragma hdrstop

#include "uCalculatedPredicates.h"

//---------------------------------------------------------------------------

#pragma package(smart_init)

unit uCalculatedPredicates;

interface

uses uTermsAndFormulasStructures;

  function BinaryRelation(byARelationTag: Byte;
						  intALeftArg, intARightArg: Integer): Boolean; overload;

  function BinaryRelation(byARelationTag: Byte;
						  extALeftArg, extARightArg: Extended): Boolean; overload;

  function BinaryRelation(byARelationTag: Byte;
						  const strALeftArg, strARightArg: AnsiString): Boolean; overload;

implementation

uses Dialogs;

function BinaryRelation(byARelationTag: Byte;
                        intALeftArg, intARightArg: Integer): Boolean;
begin
  case byARelationTag of
     byCEqualTag: Result := intALeftArg = intARightArg;
     byCLessGreaterTag: Result := intALeftArg <> intARightArg;
     byCLessTag: Result := intALeftArg < intARightArg;
     byCLessEqualTag: Result := intALeftArg <= intARightArg;
     byCGreaterTag: Result := intALeftArg > intARightArg;
     byCGreaterEqualTag: Result := intALeftArg >= intARightArg;
  else
     ShowMessage('Ошибка в func BinaryRelation: неправильный Tag');
     Result := False;
  end;
end;

function BinaryRelation(byARelationTag: Byte;
                        extALeftArg, extARightArg: Extended): Boolean;
begin
  case byARelationTag of
     byCEqualTag: Result := extALeftArg = extARightArg;
     byCLessGreaterTag: Result := extALeftArg <> extARightArg;
     byCLessTag: Result := extALeftArg < extARightArg;
     byCLessEqualTag: Result := extALeftArg <= extARightArg;
     byCGreaterTag: Result := extALeftArg > extARightArg;
     byCGreaterEqualTag: Result := extALeftArg >= extARightArg;
  else
     ShowMessage('Ошибка в func BinaryRelation: неправильный Tag');
     Result := False;
  end;
end;

function BinaryRelation(byARelationTag: Byte;
                        const strALeftArg, strARightArg: AnsiString): Boolean;
begin
  case byARelationTag of
    byCEqualTag: Result := strALeftArg = strARightArg;
    byCLessGreaterTag: Result := strALeftArg <> strARightArg;
    byCLessTag: Result := strALeftArg < strARightArg;
    byCLessEqualTag: Result := strALeftArg <= strARightArg;
    byCGreaterTag: Result := strALeftArg > strARightArg;
    byCGreaterEqualTag: Result := strALeftArg >= strARightArg;
  else
     ShowMessage('Ошибка в func BinaryRelation: неправильный Tag');
     Result := False;
  end;
end;

end.