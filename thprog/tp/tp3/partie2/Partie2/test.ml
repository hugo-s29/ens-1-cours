let rev (l: 'a list): 'a list =
  List.fold_left (fun acc x -> x :: acc) [] l

let length (l: 'a list): int =
  List.fold_left (fun x _ -> x + 1) 0 l

let fold_right (f: 'a -> 'acc -> 'acc) (l: 'a list) (a: 'acc): 'acc =
  List.fold_left (fun acc z -> f z acc) a (rev l)
