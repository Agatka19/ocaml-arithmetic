Tam gdzie dokonujemy pomiarów wielkości fizycznych, wyniki są obarczone pewnym błędem, np. 5m ± 10%. Każdą taką przybliżoną wartość traktujemy jak zbiór możliwych wartości. Zaimplementuj pakiet operacji arytmetycznych na takich przybliżonych wartościach zawierający:

konstruktory:
        
         wartosc_dokladnosc x p = x ± p% (dla p > 0),
         wartosc_od_do x y = (x+y)/2 ± (y-x)/2 (dla x < y),
         wartosc_dokladna x = x ± 0
selektory:

         in_wartosc x y ⇔ wartość x może być równa y,
         min_wartosc x = kres dolny możliwych wartości x (lub -∞ jeśli możliwe wartości x nie są ograniczone od dołu),
         max_wartosc x = kres górny możliwych wartości x (lub ∞ jeśli możliwe wartości x nie są ograniczone od góry),
         sr_wartosc x = średnia (arytmetyczna) wartości min_wartosc x i max_wartosc x (lub nan jeśli min_wartosc x i max_wartosc x nie są skończone),
         
modyfikatory:

         plus a b = { x + y : in_wartosc a x ∧ in_wartosc b y },
         minus a b = { x - y : in_wartosc a x ∧ in_wartosc b y },
         razy a b = { x · y : in_wartosc a x ∧ in_wartosc b y },
         podzielic a b = {x / y:  in_wartosc a x ∧ in_wartosc b y }.

Zakładamy przy tym implicite, że wszystkie argumenty typu float są liczbami rzeczywistymi (tzn. są różne od infinity, neg_infinity i nan.
Natomiast w przypadku, gdy wynik nie jest liczbą rzeczywistą, powinien być odpowiednią z wartości: infinity, neg_infinity lub nan.

Rozwiązując to zadanie możesz przyjąć następujące zasady ułatwiające rozumowanie:

Przyjmij, że modyfikatory domykają wynikowe zbiory wartości – to znaczy, jeżeli wynikiem jest przedział otwarty, to przyjmij, że zostaje on zamieniony na przedział domknięty. 
Operacje na wartościach przybliżonych są monotoniczne ze względu na zawieranie się zbiorów możliwych wartości.
To znaczy, jeżeli wartości przybliżone x, y i z spełniają, jako zbiory możliwych wartości, x ⊆ y, to:

    plus x z ⊆ plus y z,
    plus z x ⊆ plus z y,
    
i podobie dla innych operacji arytmetycznych.

Kilka przykładów opartych o powyższą zasadę:

    let jeden = wartosc_dokladna 1.0;;
    let zero = wartosc_dokladna 0.0;;
    in_wartosc (razy jeden zero) 0.0;;
    - : bool = true
    in_wartosc (razy zero (wartosc_od_do 1.0 10.0)) 0.0;;
    - : bool = true
    in_wartosc (razy zero (wartosc_od_do 0.0 1.0)) 0.0;;
    - : bool = true
    let duzo = podzielic jeden (wartosc_od_do 0.0 1.0);;

    sr_wartosc duzo;;
    - : float = infinity
    in_wartosc (razy zero duzo) 0.0;;
    - : bool = true
