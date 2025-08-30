%{
  open Cegarbox
%}

%token SEMICOLON
%token LPAR RPAR
%token Diamond Boxe
%token TRUE FALSE
%token EOF
%token Conj
%token Dij
%token Impl
%token Equiv
%token Not
%token BEGIN END
%token <int> Prop

%right Conj
%right Dij
%right Impl
%right Equiv
%nonassoc Boxe Diamond Not

%start file
%type <Fml.t> file

%%

file :
| BEGIN; f = formulas ;END; EOF {f}

formulas:
| f1 = formula; SEMICOLON; f2 = formulas {Fml.And (f1, f2)}
| f = formula {f}

formula:
| TRUE {Fml.Or (Fml.Var 0, Fml.Neg (Fml.Var 0))}
| FALSE {Fml.And (Fml.Var 0, Fml.Neg (Fml.Var 0))}
| f = atom {f}
| Not; f = formula {Fml.Neg f}
| f1 = formula; Conj; f2 = formula {Fml.And (f1,f2)}
| f1 = formula; Dij; f2 = formula {Fml.Or (f1,f2)}
| f1 = formula; Impl; f2 = formula {Fml.Impl (f1,f2)}
| f1 = formula; Equiv; f2 = formula {Fml.And (Fml.Impl (f1,f2), Fml.Impl (f2,f1))}
| Boxe; f = formula {Fml.Box f}
| Diamond; f = formula {Fml.Dia f}

atom:
| LPAR; f = formula; RPAR {f}
| i = Prop; {Fml.Var i}
