method Main(){
  var a := new int[6];
  a[0], a[1], a[2], a[3], a[4], a[5] := 0,2,5,10,20,30;
  var value := 20;
  var index := jumpSearch(a, value);
  print "The value ",value, " was found at index ",index,"\n";
}

predicate sorted(arr: array<int>)
   reads arr
{
   forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
}

method squareRoot(n: int) returns (r : int)
  requires n >= 0;
  ensures 0 <= r*r && r*r <= n && n < (r+1)*(r+1);
{
  r := 0 ;
  while ((r+1) * (r+1) <= n)
    invariant r*r <= n ;
  {
    r := r+1 ;
  }
}


method min(a: int, b: int) returns (d: int){
  if(a<b){
    return a;
  }
  else{
   return b;
  }
}

method jumpSearch (a: array<int>, value: int) returns (index: int)
  requires a.Length >= 0 && sorted(a)
  ensures 0 <= index ==> index < a.Length && a[index] == value
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value
{
  var length := a.Length;
  var jump := squareRoot(length);
  var left := 0;
  var right := 0;

  while (left < right && a[left] <=value)
    invariant 0 <= left <= right <= length
    invariant forall i ::
       0 <= i < left ==> a[i] <= value
  {
    right := min(length-1, left + jump);

    if (a[left] <= value && a[right] >= value){
      break;
    }
    left := left + jump;
  }

  if (left >= length || a[left] > value){
    return -1;
  }

  right := min(length-1, right);

  var i:= left;
  while(i <= right && a[i] <= value)
    invariant i <= right
  {
    if(a[i] == value){
      return i;
    }
    i := i + 1;
  }
  return -1;
}
