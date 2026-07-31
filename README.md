# cil2koat

.NETアセンブリ内のCILを解析し、[KoAT](https://github.com/aprove-developers/KoAT2-Releases)向けの整数遷移系（`.koat`）へ変換するF#製の試作プログラムです。

現在は、1つのメソッド内にある整数値と、文字列・F#リスト・C# `List<T>`の長さを中心に、CILの制御フロー、代入、分岐条件を整数遷移系へ変換します。安全に変換できない入力は近似せず、可能な限り命令位置と理由を示して処理を中止します。

## 処理フロー
```
.NETアセンブリ（DLL／EXE）
  ↓ Mono.Cecil
CIL命令列
  ↓ Cfg.fs
基本ブロックと制御フロー
  ↓ StackSim.fs + Analysis.fs
代入・分岐条件・評価スタック
  ↓ GuardNormalization.fs + TransitionIr.fs
型付き整数遷移系
  ↓ Koat.fs
KoAT入力ファイル
```

変換時には、生のIL命令列、基本ブロック、分岐先、復元した代入、ガード条件も標準出力へ表示します。

## 必要な環境

- .NET 10 SDK
- 初回ビルド時にNuGetパッケージを取得できる環境
- 生成したファイルを解析する場合は、別途KoAT

## ビルド

```powershell
dotnet build
```

## 使い方

```powershell
dotnet run -- <assembly.dllまたはassembly.exeのpath> <method-specifier> [output.koat]
```

出力先を省略すると解析内容の表示だけを行います。出力先を指定すると、表示に加えてKoATファイルを書き出します。

メソッド名がアセンブリ全体で一意なら、名前だけで指定することが可能です。

```powershell
dotnet run -- Target.dll sampleFunc output.koat
```

同名メソッドやオーバーロードがある場合は、型と引数型を含む厳密指定を使用してください。

```text
Namespace.Type::Method(System.Int32)
static:Namespace.Type::Method(System.Int32)
instance:Namespace.Type::Method(System.Int32)
```

```powershell
dotnet run -- Target.dll "static:Example.Program::sampleFunc(System.Int32)" output.koat
```

単純名が曖昧な場合は1件を暗黙に選ばず、利用可能な厳密指定を表示して終了します。ネスト型内のメソッドも検索対象です。

## 生成されるKoAT

概念的に次の処理を変換すると、

```csharp
while (x > 0)
{
    x = x - 1;
}
```

CILの基本ブロックに対応する規則が生成されます。

```text
(GOAL COMPLEXITY)
(STARTTERM (FUNCTIONSYMBOLS block_0000))
(VAR x)
(RULES
  block_0000(x) -> block_000A(x)
  block_000A(x) -> block_0003(x) [x > 0]
  block_000A(x) -> block_0012(x) [x <= 0]
  block_0003(x) -> block_000A(x - 1)
)
```

ラベルや規則の分割は、入力アセンブリのCILやビルド構成によって変わります。本体は基本ブロックを縮約せず、CILに対応する非縮約の遷移系を出力します。

## 現在の対応範囲

### 型

| .NET型 | 遷移系での扱い |
|---|---|
| `sbyte`、`byte`、`short`、`ushort` | KoATの整数変数 |
| `int`、`uint`、`long`、`ulong` | KoATの整数変数 |
| `bool` | 比較結果や分岐ガード。一般の整数変数としては扱わない |
| `string` | `<変数名>_length`という文字列長 |
| F# `'T list` | `<変数名>_length`というリスト長 |
| C# `List<T>` | `<変数名>_length`という要素数 |
| `List<T>.Enumerator` | `<ローカル名>_remaining`という未走査要素数 |
| 1次元配列 `T[]` | `<変数名>_length`という要素数 |

整数型のビット幅や符号は、現在のKoAT遷移系には保持されません。

### 操作と制御フロー

- CIL命令列からの基本ブロックとCFGの構築
- 整数引数・整数ローカルの追跡
- `string`を`<変数名>_length`という整数変数へ抽象化
- F#の`list`を`<変数名>_length`という整数変数へ抽象化
- `string.Length`、`String.IsNullOrEmpty`
- C# `List<T>`を`<変数名>_length`、その`foreach`列挙子を残り要素数として抽象化
- `List<T>.Count`、`GetEnumerator`、`MoveNext`、要素値に依存しない`foreach`
- 1次元配列の生成、代入、`Length`、要素値に依存しない`for`／`foreach`
- 配列用の`newarr`、`ldlen`、`ldelem.*`と、典型的な`conv.i4`
- F#リストの`Length`、`IsEmpty`、`Tail`、コンパイラ内部の`TailOrNull`、`List.length`
- 評価スタックを介した整数式と代入の復元
- CFG合流点における整数スタック値の受け渡し
- 加算・減算・乗算による多項式更新
- 条件分岐、直接比較分岐、`switch`
- ガードの局所的な否定除去と簡約
- `!=`や論理和の複数KoAT規則への展開
- 型名、引数型、static／instanceを含むメソッド選択
- 到達不能ブロックの識別
- 遷移IRの整合性検証

### C# `List<T>`の`foreach`

要素値に依存しないループ本体を、列挙子の残り要素数が1ずつ減る遷移として扱えます。

```csharp
public static int CountItems(List<int> xs)
{
    int count = 0;
    foreach (int item in xs)
    {
        count++;
    }
    return count;
}
```

標準的な`foreach`が生成する`GetEnumerator`、`MoveNext`、`Current`、`Dispose`、`try/finally`に付随する限定的なCIL命令を認識します。一方、`sum += item`や`if (item > 0)`のように要素値を計算や分岐へ使用する処理は拒否します。

### 配列の`for`／`foreach`

1次元配列も長さだけを追跡し、C#コンパイラが配列の`foreach`を展開した添字ループを変換できます。

```csharp
public static int CountArray(int[] xs)
{
    int count = 0;
    foreach (int item in xs)
    {
        count++;
    }
    return count;
}
```

`ldelem.*`で読み出した要素は未知要素として扱います。読み捨てることはできますが、要素値を算術や分岐に使用する処理は拒否します。`stelem.*`による要素の書き込みも未対応です。多次元配列、非ゼロ始点の配列、配列要素間の関係は扱いません。

## 主な制限

- 解析単位は単一メソッドです。
- `float`（`System.Single`）、`double`（`System.Double`）、`decimal`（`System.Decimal`）は未対応です。浮動小数点定数・演算・比較、IEEE 754の`NaN`、無限大、丸め、`-0.0`は表現しません。`decimal`の演算として生成される`System.Decimal`のメソッド呼び出しにも対応していません。
- `char`の文字値、enum固有の意味、nullable型、任意精度整数や有理数も未対応です。
- 文字列とリストは長さだけを追跡し、文字・要素の値は追跡しません。
- `call`／`callvirt`は上記の文字列・リスト操作だけに対応します。一般のメソッド呼び出し、直接・相互再帰、フィールド、一般の例外フロー、高階関数は未対応です。
- F#リストではランタイム表現に合わせてnullを空リストとして扱います。文字列ではnullと空文字列を同一視せず、長さだけでは安全に表現できないnull代入や参照値のnull分岐を拒否します。
- CILの有限幅整数とKoATの数学的整数の意味の差は未解決です。オーバーフローし得るプログラムでは、変換結果が元プログラムの意味を完全には保存しない可能性があります。
- 一般の符号なし比較は、符号付き整数比較へ誤変換せず拒否します。ただし、C#コンパイラが`x != 0`に使用する特定の`cgt.un`パターンは正規化します。
- 除算や剰余などはスタック上の式として扱えますが、KoATの多項式更新としては出力できません。
- 異なるBoolean値が評価スタック上で合流するケースは未対応です。
- 基本ブロックの縮約を行わないため、ソースコードを直接モデル化したKoAT入力より規則数や解析コストが増える場合があります。
- 生成後のKoAT実行、停止性証明、非停止証明は本体の範囲外です。

## 本体のファイル構成

| ファイル | 役割 |
|---|---|
| `CilFrontend.fsproj` | .NETプロジェクト定義とF#ソースのコンパイル順 |
| `Cfg.fs` | CIL命令列の基本ブロック分割と終端分類 |
| `StackSim.fs` | CIL評価スタックのシミュレーションと式の復元 |
| `Analysis.fs` | CFG全体のワークリスト解析とスタック値の伝播 |
| `GuardNormalization.fs` | Booleanガードの局所的な正規化 |
| `TransitionIr.fs` | 出力形式に依存しない型付き遷移IRの構築と検証 |
| `Koat.fs` | 遷移IRのKoAT形式への変換 |
| `MethodSelection.fs` | メソッド指定の解析と曖昧性の検出 |
| `Program.fs` | CLIエントリーポイントと解析結果の表示 |
