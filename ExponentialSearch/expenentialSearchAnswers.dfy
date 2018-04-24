method Main(){
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 0,2,5,10,20;
  var value := 20;
  var n := a.Length;
  var index := ExponentialSearch(a, n, value);
  print "The value ",value, " was found at index ",index,"\n";
}

method min(a: int, b: int) returns (d: int){
  if(a<b){
    return a;
  }
  else{
   return b;
  }
}

method ExponentialSearch(arr: array<int>, n: int, val: int) returns (index: int)
  requires arr.Length >= 0 && sorted(arr)
  ensures 0 <= index ==> index < arr.Length && arr[index] == val
  ensures index < 0 ==> forall k :: 0 <= k < arr.Length ==> arr[k] != val
{
  var temp := 0;
  if(arr[temp] == val){
    return 0;
  }

  var i := 1;
  while(1 < n && arr[i] <= val)
    invariant i <= arr.Length;
    invariant forall i :: 1 <= i < n && arr[i] <= val
    decreases n - i*2
  {
    i := i*2;
  }
  var minimum := min(i,n);
  var output := BinarySearch(arr, val, i/2, minimum);
  return output;
}

predicate sorted(a: array<int>)
   reads a
{
   forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}
method BinarySearch(a: array<int>, value: int, x: int, y: int) returns (index: int)
   requires a.Length >= 0 && sorted(a)
   requires 0 <= x <= y <= a.Length
   requires forall i :: 0 <= i < a.Length && !(x <= i < y) ==> a[i] != value
   ensures 0 <= index ==> index < a.Length && a[index] == value
   ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value
{
  var low, high := x, y;
   while low < high
      invariant 0 <= low <= high <= a.Length
      invariant forall i ::
         0 <= i < a.Length && !(low <= i < high) ==> a[i] != value
   {
      var mid := (high + low) / 2;
      if a[mid] < value
      {
         low := mid + 1;
      }
      else if value < a[mid]
      {
         high := mid;
      }
      else
      {
         return mid;
      }
   }
   return -1;
}
