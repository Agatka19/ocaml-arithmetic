(* AUTOR: Agata Chrzanowska 417771 *)
(* REVIEWER: Julia Podrażka 418374 *)

(* TYPY *)
type wartosc = 
  Przedzial of float * float (*wartość w przedziale od x do y, gdzie x <= y *)
  | Dopelnienie of float * float (* wartość poza przedziałem zdefiniowanym wyżej *)

(* KONSTRUKTORY *)
let wartosc_dokladnosc x p = (* wartość początkowa: p > 0 *)
  let procent = (p /. 100.0 *. x) in
  if procent > 0.0 then Przedzial (x -. procent, x +. procent)
  else Przedzial (x +. procent, x -. procent)

let wartosc_od_do x y = 
  Przedzial (x, y)

let wartosc_dokladna x = 
  Przedzial (x, x)

(* SELEKTORY *)
let in_wartosc x y = match x with
  | Przedzial (i, j) -> i <= y && y <= j
  | Dopelnienie (i, j) -> i >= y || y >= j

let min_wartosc x = match x with
  | Przedzial (i, _) -> i
  | Dopelnienie (_, _) -> neg_infinity

let max_wartosc x = match x with
  | Przedzial (_, j) -> j
  | Dopelnienie (_, _) -> infinity

let sr_wartosc x = match x with
  | Przedzial (i, j) -> 
    if(i = neg_infinity && j = infinity) then nan
    else (i +. j) /. 2.0
  | Dopelnienie (_, _) -> nan

(* FUNKCJE POMOCNICZE *)
let jest_nan x = compare x nan = 0

(* wywołujemy tę funkcję jeśli (i > j) i zamieniamy tak, żeby było i <= j *)
let odwroc x = match x with
  | Przedzial (i, j) -> Przedzial (j, i)
  | Dopelnienie (i, j) -> Dopelnienie (j, i)

(* zmieniamy znaki przedziału *)
let ujemna x = match x with
  | Przedzial (i, j) -> Przedzial (-.i, -.j)
  | Dopelnienie (i, j) -> Dopelnienie (-.i, -.j)

(* znajdujemy odwrotność przedziału - w liczbach naturalnych miałoby to odzwierciedlenie 1/n *)
let odwrotnosc x = match x with
  | Przedzial (i, j) ->
    if (i > j || (i = 0.0 && j = 0.0)) then Przedzial (nan, nan)
    else if (i = 0.0) then Przedzial ((1.0 /. j), infinity)
    else if (j = 0.0) then Przedzial (neg_infinity, 1.0 /. i)
    else if (i < 0.0 && j > 0.0) then Dopelnienie (min (1.0 /. j) (1.0 /. i), max (1.0 /. j) (1.0 /. i))
    else Przedzial (min (1.0 /. i) (1.0 /. j), max (1.0 /. i) (1.0 /. j))
  | Dopelnienie (i, j) ->
    if (i > j || (i = 0.0 && j = 0.0)) then Przedzial (nan, nan)
    else if (i < 0.0 && j > 0.0) then Przedzial (min (1.0 /. i) (1.0 /. j), max (1.0 /. i) (1.0 /. j))
    else Dopelnienie (min (1.0 /. i) (1.0 /. j), max (1.0 /. i) (1.0 /. j))

(* tworzy Dopełnienie (x, y) w zależności od tego jakie nam wyszły wartości l i r lub zwraca nieskończony przedział jeżeli chcemy Dopełnienie Przedziału (nan, nan) *)
let stworz_dopelnienie l r ia ja ib jb = 
  if ((compare l nan = 0 && compare r nan = 0) || (l = 0.0 && r = 0.0)) then Przedzial (neg_infinity, infinity)
  else if (l = infinity && r <> neg_infinity) then Dopelnienie (r, min (ia *. jb) (ia *. ib))
  else if (r = neg_infinity && l <> infinity) then Dopelnienie (max (ja *. jb) (ja *. ib), l)
  else
    if l < r then Dopelnienie (l, r) else Dopelnienie(r, l)

(* razy (Przedzial (ia, ja)) (Przedzial (ib, jb)) *)
let mnoz_dwa_przedzialy ia ja ib jb = 
  if((jest_nan ia && jest_nan ja) || (jest_nan ib && jest_nan jb)) then Przedzial (nan, nan)
  else if ((ia = 0.0 && ja = 0.0) || (ib = 0.0 && jb = 0.0)) then Przedzial (0.0, 0.0)
  else 
    let ograniczenia = List.filter (fun x -> x = x) (* sprawdzamy czy x nie jest nan, bo nan nie spełnia równości nan = nan *)
    [ia *. ib; ia *. jb; ja *. ib; ja *. jb] in 
    (* liczymy minimalne i maksymalne miejsce *) 
    let l  = List.fold_left (min) infinity ograniczenia
    and r = List.fold_left (max) neg_infinity ograniczenia in
    Przedzial (l, r)

(* razy (Dopelnienie (ia, ja)) (Przedzial (ib, jb)) *)
let mnoz_dop_przedz ia ja ib jb = 
  let x = Przedzial (ib, jb) in
  if (jest_nan ib || jest_nan jb) then Przedzial (nan, nan) (* nie trzeba sprawdzać ia i ja bo nie ma Dopełnienia od nan *)
  else  if (ib = 0.0 && jb = 0.0) then Przedzial (0.0, 0.0)
  (* jeżeli argument nie jest zerem, ale oscyluje wokół zera, to może osiągnąć każdą wartość *)
  else if (ib <> 0.0 && jb <> 0.0 && in_wartosc x 0.0) then Przedzial (neg_infinity, infinity)
  else if (ib < 0.0 && jb > 0.0) then Przedzial (neg_infinity, infinity)
  else if ib >= 0.0 then
    let l = max (ia *. jb) (ia *. ib)
    and r = min (ja *. jb) (ja *. ib) in
    stworz_dopelnienie l r ia ja ib jb
  else 
    let l = min (ia *. jb) (ia *. ib)
    and r = max (ja *. jb) (ja *. ib) in
    stworz_dopelnienie l r ia ja ib jb

(* razy (Dopelnienie (ia, ja)) (Dopelnienie (ib, jb)) *)
let mnoz_dwa_dopelnienia ia ja ib jb = 
  let l = max (ib *. ja) (jb *. ia)
  and r = min (jb *. ja) (ib *. ia) in
  if l >= r then Przedzial (neg_infinity, infinity)
  else Dopelnienie (l, r)

(* MODYFIKATORY *)
let rec plus a b = match a, b with 
  | Przedzial (ia, ja), Przedzial (ib, jb) -> Przedzial ((ia +. ib), (ja +. jb))
  | Przedzial (ia, ja), Dopelnienie (ib, jb) -> 
      let iab = ia +. jb
      and jab = ja +. ib in
      if jab >= iab then Przedzial (neg_infinity, infinity)
      else if (jest_nan iab || jest_nan jab) then Przedzial (nan, nan)
      else Dopelnienie (jab, iab)
  | Dopelnienie (_, _), Przedzial (_, _) -> plus b a
  | Dopelnienie (_, _), Dopelnienie (_, _) -> Przedzial (neg_infinity, infinity);;

(* Wiemy, że a - b = a + (-b) *)
let minus a b = 
  plus a (odwroc(ujemna b));;

let rec razy a b = match a, b with
  | Przedzial (ia, ja),   Przedzial (ib, jb) -> mnoz_dwa_przedzialy ia ja ib jb
  | Dopelnienie (ia, ja), Przedzial (ib, jb) -> mnoz_dop_przedz ia ja ib jb
  (* Z symetrii mnożenia wiemy, że ab = ba, więc wystarczy, że dla Przedzial(ia, ja), Dopelnienie (ib, jb) wywołamy się zamieniając argumenty *)
  | Przedzial (_, _), Dopelnienie (_, _) -> razy b a
  | Dopelnienie (ia, ja), Dopelnienie (ib, jb) -> 
      if in_wartosc a 0.0 then Przedzial (neg_infinity, infinity)
      else mnoz_dwa_dopelnienia ia ja ib jb;;

(* Wiemy, że a / b = a * (1/b) *)
let podzielic a b = 
  let bb = odwrotnosc b in match bb with
  | Przedzial (i, j) -> 
      if ((jest_nan i || i = 0.0) && (jest_nan j || j = 0.0)) then Przedzial (nan, nan)
      else razy a bb
  | Dopelnienie (i, j) -> 
      if (jest_nan i && jest_nan j) then Przedzial (nan, nan)
      else razy a bb;; (*nie sprawdzamy 0, bo Dopełnienie (-inf, inf) to Przedział (0, 0) *)