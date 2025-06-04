module API {
  extern method FetchData(url: string) returns (response: string);
}


// call external API
module C {
  import API;

  method UseData(url: string) returns (len: int)
    requires url != ""
    ensures len >= 0
  {
    var body := API.FetchData(url);
    len := body.Length;   // purely logical use of the fetched string
  }

  // Example usage
  method Main()
  {
    var url := "http://example.com/data";
    var length := UseData(url);
    print "Length of data: ", length;
  }
}