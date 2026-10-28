import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7064 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7064 = true := by
  decide +kernel

theorem tot7064 : totK PA10K2 A10K2.t7064 = [0, 0, 387430578264, 1654180929897, 2071835865707, 746659785553, 45613493098, 0, 0, 0] := by
  decide +kernel

theorem rows7065 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7065 = true := by
  decide +kernel

theorem tot7065 : totK PA10K2 A10K2.t7065 = [0, 0, 612143352615, 1998098587104, 1852606377913, 509458114940, 29367733220, 0, 0, 0] := by
  decide +kernel

theorem rows7066 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7066 = true := by
  decide +kernel

theorem tot7066 : totK PA10K2 A10K2.t7066 = [0, 0, 0, 824968281255, 2304148520049, 1655255621522, 263194420950, 6279851884, 0, 0] := by
  decide +kernel

theorem rows7067 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7067 = true := by
  decide +kernel

theorem tot7067 : totK PA10K2 A10K2.t7067 = [0, 0, 0, 426539909774, 1728069991422, 2144826726332, 737811562556, 56084282801, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
