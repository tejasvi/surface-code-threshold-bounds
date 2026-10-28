import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4292 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4292 = true := by
  decide +kernel

theorem tot4292 : totK PA10K2 A10K2.t4292 = [0, 31409270183, 833826266997, 2179317090250, 1644623554431, 293479514545, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows4293 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4293 = true := by
  decide +kernel

theorem tot4293 : totK PA10K2 A10K2.t4293 = [0, 0, 518978502116, 1779110828896, 1910413864667, 635480710054, 40545095891, 0, 0, 0] := by
  decide +kernel

theorem rows4294 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4294 = true := by
  decide +kernel

theorem tot4294 : totK PA10K2 A10K2.t4294 = [0, 0, 461423799267, 1844993903735, 1931012094263, 453701246579, 25667075836, 0, 0, 0] := by
  decide +kernel

theorem rows4295 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4295 = true := by
  decide +kernel

theorem tot4295 : totK PA10K2 A10K2.t4295 = [0, 0, 285617419803, 1361715147983, 2133039455537, 1029008021801, 104071152193, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
