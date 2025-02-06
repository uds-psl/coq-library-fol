Notation "'existsT' x .. y , p" := (sig (fun x => .. (sig (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'existsT'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope. 

Notation "'existsT2' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'existsT2'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.