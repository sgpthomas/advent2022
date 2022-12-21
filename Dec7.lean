import Utils

namespace Dec7

inductive Fs where
  | entry (name : String) (size : Nat) (files : List Fs)
deriving BEq

def Fs.root : Fs := Fs.entry "" 0 []

instance : Inhabited Fs where
  default := Fs.root

mutual
  def Fs.toString : Fs -> Nat -> String
    | Fs.entry name 0 [], _ => s!"{name}/"
    | Fs.entry name 0 files, d =>
      s!"{name}/\n" ++ (String.intercalate "\n"
        (List.map
          (λ x => (String.pushn "" ' ' d) ++ s!"{x}")
          (dirString files d)))
    | Fs.entry name size _, _ => s!"{name} - {size}"
   
  def dirString : List Fs -> Nat -> List String
    | [], _ => []
    | h :: tl, d => h.toString (d + 1) :: dirString tl d
end

def Fs.name : Fs -> String
  | entry name _ _ => name

def Fs.size : Fs -> Nat
  | entry _ size _ => size

def Fs.files : Fs -> List Fs
  | entry _ _ files => files

instance : ToString Fs where
  toString := (Fs.toString · 1)

mutual
  def Fs.mkOver (name : String) : (Fs -> Fs) -> Fs -> Fs
    | f, Fs.entry oldName size l => Fs.entry oldName size (mkOverDirs name f l)

  def mkOverDirs (name : String) (f : Fs -> Fs) : List Fs -> List Fs
    | [] => []
    | hd :: tl =>
      if name == hd.name then
        f hd :: tl
      else
        hd :: (mkOverDirs name f tl)
end

def Fs.pathOver : List String -> (Fs -> Fs) -> Fs -> Fs
  | hd :: tl, f, fs => Fs.mkOver hd (Fs.pathOver tl f) fs
  | [], f, fs => f fs
  
def Fs.pathView : List String -> Fs -> Fs
  | hd :: tl, Fs.entry name size files =>
    match files.find? (·.name = hd) with
    | some fs => Fs.pathView tl fs
    | none => Fs.entry name size files
  | [], fs => fs
  
def Fs.mkdir (name : String) : Fs -> Fs
  | Fs.entry oldName size l =>
    Fs.entry oldName size (l ++ [Fs.entry name 0 []])

def Fs.touch (name : String) (size : Nat) : Fs -> Fs
  | Fs.entry oldName oldSize l =>
    Fs.entry oldName oldSize (l ++ [Fs.entry name size []])

-- #eval Fs.entry "" 0 []
--   |> Fs.pathOver [] (Fs.mkdir "a")
--   |> Fs.pathOver [] (Fs.touch "b.txt" 14848514)
--   |> Fs.pathOver [] (Fs.touch "c.dat" 85)
--   |> Fs.pathOver [] (Fs.mkdir "d")
--   |> Fs.pathOver ["a"] (Fs.mkdir "e")
--   |> Fs.pathOver ["a"] (Fs.touch "f" 29)
--   |> Fs.pathOver ["a"] (Fs.touch "g" 25)
--   |> Fs.pathOver ["a"] (Fs.touch "h.lst" 62)
--   |> Fs.pathOver ["a"] (Fs.touch "h.lst" 62)
--   |> Fs.pathOver ["a", "e"] (Fs.touch "i" 584)
--   |> Fs.pathOver ["d"] (Fs.touch "j" 40)
--   |> Fs.pathOver ["d"] (Fs.touch "d.log" 40)
--   |> Fs.pathOver ["d"] (Fs.touch "d.ext" 40)
--   |> Fs.pathOver ["d"] (Fs.touch "k" 40)

inductive Command where
| cd (path : String)
| ls
deriving BEq, Repr

instance : Inhabited Command where
  default := Command.ls

inductive Output where
| dir (path : String)
| file (size : Nat) (path : String)
deriving BEq, Repr

instance : Inhabited Output where
  default := Output.dir "/"

instance : ToString Command where
  toString c := match c with
                | Command.cd path => s!"cd {path}"
                | Command.ls => "ls"

instance : ToString Output where
  toString o := match o with
                | Output.dir path => s!"dir {path}"
                | Output.file size path => s!"{size} {path}"

def parseString : List String -> Option (Command ⊕ Output)
  | ["$", "cd", path] => some (Sum.inl $ Command.cd path)
  | ["$", "ls"] => some (Sum.inl $ Command.ls)
  | ["dir", path] => some (Sum.inr $ Output.dir path)
  | [num, path] => ((String.toNat? num).map (λ n => Sum.inr $ Output.file n path))
  | _ => none
  
def gather : List (Command ⊕ Output) -> List (Command × List Output)
  | [] => []
  | Sum.inr _ :: _ => []
  | Sum.inl cmd :: tl =>
    let (finCmd, finOut, acc) := tl.foldl
      (λ (wipCmd, wipOut, acc) el =>
        match el with
        | Sum.inr out => (wipCmd, out :: wipOut, acc)
        | Sum.inl cmd => (cmd, [], (wipCmd, wipOut.reverse) :: acc))
      (cmd, [], [])
    ((finCmd, finOut.reverse) :: acc).reverse
    
/-- Calculates the actual paths at every command. -/
def pwd : List (Command × List Output) -> List (List String × List Output) :=
  h []
where h (acc : List String)
  : List (Command × List Output) -> List (List String × List Output)
  | [] => []
  | (Command.cd "/", lo)  :: tl => ([], lo)            :: h [] tl
  | (Command.cd "..", lo) :: tl => (acc.dropLast, lo)  :: h acc.dropLast tl
  | (Command.cd path, lo) :: tl => (acc ++ [path], lo) :: h (acc ++ [path]) tl
  | (Command.ls, lo)      :: tl => (acc, lo)           :: h acc tl
  
def flatten : List (List String × List Output) -> List (List String × Output)
  | [] => []
  | (path, lo) :: tl => lo.map (λ out => (path, out)) ++ flatten tl
  
def Fs.apply (path : List String) : Output -> Fs -> Fs
  | Output.dir name => Fs.pathOver path (Fs.mkdir name)
  | Output.file size name => Fs.pathOver path (Fs.touch name size)
  
def Fs.dirSize : Fs -> Nat
  | Fs.entry _ size [] => size
  | Fs.entry name 0 (hd :: tl) => hd.dirSize + (Fs.dirSize (Fs.entry name 0 tl))
  | _ => 0
  
def Fs.allDirs : Fs -> List (List String) :=
  (List.map (List.filter (· ≠ ""))) ∘ h
where h : Fs -> List (List String)
  | Fs.entry name 0 [] => [[name]]
  | Fs.entry name 0 (hd :: tl) => ((h hd).map (name :: ·)) ++ (h (Fs.entry name 0 tl))
  | _ => []
  
def data : String := "data/dec7.txt"

def run : IO Unit := do

  let lines <- Utils.lines data
  let parsed := lines
    |> List.map (λ l => l.split (· = ' ') |> parseString)
    |> Utils.allGood?
    
  let (part1, part2) := match parsed with
  | some parsed => 
    let fs := parsed
      |> gather
      |> pwd
      |> flatten
      |> List.foldl (λ fs (path, output) => Fs.apply path output fs) Fs.root
      
    let sizes := fs
      |> Fs.allDirs
      |> List.map (λ path => Fs.pathView path fs)
      |> List.map Fs.dirSize
      
    let part1 := sizes
      |> List.filter (· <= 100000)
      |> List.foldl (· + ·) 0

    let totalSize := 70000000
    let updSize := 30000000
    let needed := updSize - (totalSize - Fs.dirSize fs) 
    let part2 := sizes |> List.find? (· >= needed)
    (part1, part2)
  | none => default
  
  let stdout <- IO.getStdout
  stdout.putStrLn s!"Part1: {part1}"
  stdout.putStrLn s!"Part2: {part2}"

  pure ()
  
#eval run

end Dec7
