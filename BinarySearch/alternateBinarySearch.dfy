method Main(){
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 0,2,5,10,20;
  var value := 20;
  var length := a.Length;
  var index := BinarySearch(a, value,0, length);
  print "The value ",value, " was found at index ",index,"\n";
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
