<?

# tree :: treeName
# ---------------------------------------------------------------------------------------------------------
   class treeName
   {
   # self :: meta : aspects
   # ------------------------------------------------------------------------------------------------------
      public static $meta;
   # ------------------------------------------------------------------------------------------------------



   # func :: auto : call
   # ------------------------------------------------------------------------------------------------------
      public static function __callStatic($func,$args)
      {
         return call(__CLASS__.'::'.$func,$args);
      }
   # ------------------------------------------------------------------------------------------------------
   }
# ---------------------------------------------------------------------------------------------------------

?>
