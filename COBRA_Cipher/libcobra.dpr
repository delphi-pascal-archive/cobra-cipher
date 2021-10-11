library libcobra;

{
        COBRA Cipher by Chris Schneider
        Delphi implementation by Alexander Myasnikow
        Web: www.darksoftware.narod.ru
}


uses
  SysUtils;

const
  MAXDATA = 65536 - 16;

type
  ULONG = longword;     { unsigned 32bit }
  UINT  = word;         { unsigned 16bit }
  UCHAR = byte;         { unsigned 8bit }
  P_UCHAR_Buffer = ^T_UCHAR_Buffer;
  T_UCHAR_Buffer = array[0..MAXDATA - 1] of UCHAR;
  P_ULONG_Buffer = ^T_ULONG_Buffer;
  T_ULONG_Buffer = array[0..(MAXDATA div 4) - 1] of ULONG;

  { public constants }
const
  COBRA_MAXKEYSIZE = 32;


var
  pbox:  array[0..15] of ULONG;
  sbox1: array[0..255] of ULONG;
  sbox2: array[0..255] of ULONG;
  sbox3: array[0..255] of ULONG;
  sbox4: array[0..255] of ULONG;
  wbox:  array[0..3] of ULONG;


{$I cobratabs.inc}

{
        F - the cobra function
        <-> 32bit data element
}
  function F (ulX: ULONG; unRound: UINT): ULONG;
    var
      unA: UINT;
      unB: UINT;
      unC: UINT;
      unD: UINT;
      ulY: ULONG;
    begin
      ulX := ulX xor pbox[unRound];

      unD := (ulX and $00ff);
      ulX := ulX shr 8;
      unC := (ulX and $00ff);
      ulX := ulX shr 8;
      unB := (ulX and $00ff);
      ulX := ulX shr 8;
      unA := (ulX and $00ff);
      { ignore overflows }
{$Q-}
      ulY := ((sbox1[unA] + sbox2[unB]) xor sbox3[unC]) + sbox4[unD];
{$Q+}
      Result := ulY;
    end;


{
        COBRA_ENCIPHER - encryption routine
        <-> 64bit data element
}
  procedure cobra_encipher (var ulXleft, ulXright: ULONG);
    var
      ulXl: ULONG;
      ulXr: ULONG;
      ulXlt: ULONG;
      ulXrt: ULONG;
      unI: UINT;
    begin
      ulXl := ulXleft;
      ulXr := ulXright;

      ulXl := ulXl xor wbox[0];
      ulXr := ulXr xor wbox[1];

      for unI := 0 to 15 do
        begin
        ulXlt := ulXr;
        ulXrt := ulXl xor F(ulXr, unI);
        ulXrt := (ulXrt shr 1) or (ulXrt shl 31);

        ulXl := ulXlt;
        ulXr := ulXrt;
        end;

      ulXl := ulXl xor wbox[2];
      ulXr := ulXr xor wbox[3];

      ulXleft  := ulXl;
      ulXright := ulXr;
    end;


{
        COBRA_DECIPHER - decryption routine
        <-> 64bit data element
}
  procedure cobra_decipher (var ulXleft, ulXright: ULONG);
    var
      ulXl: ULONG;
      ulXr: ULONG;
      ulXlt: ULONG;
      ulXrt: ULONG;
      unI: UINT;
    begin
      ulXl := ulXleft;
      ulXr := ulXright;

      ulXl := ulXl xor wbox[2];
      ulXr := ulXr xor wbox[3];

      for unI := 15 downto 0 do
        begin
        ulXrt := ulXl;
        ulXlt := (ulXr shl 1) or (ulXr shr 31);
        ulXlt := ulXlt xor F(ulXrt, unI);

        ulXl := ulXlt;
        ulXr := ulXrt;
        end;

      ulXl := ulXl xor wbox[0];
      ulXr := ulXr xor wbox[1];

      ulXleft  := ulXl;
      ulXright := ulXr;
    end;

  procedure crypt (pBuffer: P_ULONG_Buffer); stdcall; export;
    begin
      cobra_encipher(pBuffer^[0], pBuffer^[1]);
    end;

  procedure decrypt (pBuffer: P_ULONG_Buffer); stdcall; export;
    begin
      cobra_decipher(pBuffer^[0], pBuffer^[1]);
    end;

  procedure setup (pKey: P_ULong_Buffer); stdcall; export;
    type
      { for better encryption handling define a 64bit data element }
      TData64 = record
        ulDataL: ULONG;
        ulDataR: ULONG;
        end;
    var
      unI: UINT;
      unPos: UINT;
      block: TData64;
      aulKey: array[0..7] of ULONG;
    begin

      for unI := 0 to 255 do
        begin
        sbox1[unI] := sbox1mat[unI];
        sbox2[unI] := sbox2mat[unI];
        sbox3[unI] := sbox3mat[unI];
        sbox4[unI] := sbox4mat[unI];
        end;

      for unI := 0 to 15 do
        begin
        pbox[unI] := pboxmat[unI];
        end;

      for unI := 0 to 3 do
        begin
        wbox[unI] := wboxmat[unI];
        end;

      { build a temporary 256bit key by looping the password, if necessary }

      for unI := 0 to 7 do
        begin
        aulKey[unI] := pKey^[unI];
        end;

      { xor the p-boxes with the key }
      unPos := 0;
      for unI := 0 to 15 do
        begin
        pbox[unI] := pbox[uni] xor aulKey[unPos];
        Inc(unPos);
        if (unPos > 7) then
          unPos := 0;
        end;

      { encrypt the p-boxes starting with a zero string }
      block.ulDataL := $00000000;
      block.ulDataR := $00000000;
      unI := 0;
      while (unI < 1) do
        begin
        cobra_encipher(block.ulDataL, block.ulDataR);
        pbox[unI] := block.ulDataL;
        pbox[unI + 1] := block.ulDataR;
        Inc(unI, 2);
        end;

      { circular shift all 32bit entries of the key right by one }
      for unI := 0 to 7 do
        begin
        aulKey[unI] := (aulKey[unI] shr 1) or (aulKey[unI] shl 31);
        end;

      { xor the p-boxes with the key again }
      unPos := 0;
      for unI := 0 to 15 do
        begin
        pbox[unI] := pbox[unI] xor aulKey[unPos];
        Inc(unPos);
        if (unPos > 7) then
          unPos := 0;
        end;

      { encrypt the p-boxes starting again with a zero string }
      block.ulDataL := $00000000;
      block.ulDataR := $00000000;
      unI := 0;
      while (unI < 15) do
        begin
        cobra_encipher(block.ulDataL, block.ulDataR);
        pbox[unI] := block.ulDataL;
        pbox[unI + 1] := block.ulDataR;
        Inc(unI, 2);
        end;

      { encrypt all other boxes... }
      unI := 0;
      while (unI < 255) do
        begin
        cobra_encipher(block.ulDataL, block.ulDataR);
        sbox1[unI] := block.ulDataL;
        sbox1[unI + 1] := block.ulDataR;
        Inc(unI, 2);
        end;
      unI := 0;
      while (unI < 255) do
        begin
        cobra_encipher(block.ulDataL, block.ulDataR);
        sbox2[unI] := block.ulDataL;
        sbox2[unI + 1] := block.ulDataR;
        Inc(unI, 2);
        end;
      unI := 0;
      while (unI < 255) do
        begin
        cobra_encipher(block.ulDataL, block.ulDataR);
        sbox3[unI] := block.ulDataL;
        sbox3[unI + 1] := block.ulDataR;
        Inc(unI, 2);
        end;
      unI := 0;
      while (unI < 255) do
        begin
        cobra_encipher(block.ulDataL, block.ulDataR);
        sbox4[unI] := block.ulDataL;
        sbox4[unI + 1] := block.ulDataR;
        Inc(unI, 2);
        end;
      unI := 0;
      while (unI < 3) do
        begin
        cobra_encipher(block.ulDataL, block.ulDataR);
        wbox[unI] := block.ulDataL;
        wbox[unI + 1] := block.ulDataR;
        Inc(unI, 2);
        end;

      { clear the temporary key }
      for unI := 0 to (COBRA_MAXKEYSIZE div 4) - 1 do
        aulKey[unI] := $00000000;

    end;


  function getblocksize (): longword; stdcall; export;
    begin
      Result := 64;
    end;

  function getkeysize (): longword; stdcall; export;
    begin
      Result := 256;
    end;


  procedure getciphername (p: PChar); stdcall; export;
    begin
      StrPCopy(p, 'Cobra-64-256');
    end;


exports

  setup,
  crypt,
  decrypt,
  getblocksize,
  getkeysize,
  getciphername;

end.
