import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2216 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2216 = true := by
  decide +kernel

theorem tot2216 : totK PA10K2 A10K2.t2216 = [0, 577534374215, 1921363423890, 1959198840787, 612432560549, 57952395209, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2217 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2217 = true := by
  decide +kernel

theorem tot2217 : totK PA10K2 A10K2.t2217 = [0, 215095608158, 1251715800439, 2144324341804, 1227340260233, 205414890876, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows2218 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2218 = true := by
  decide +kernel

theorem tot2218 : totK PA10K2 A10K2.t2218 = [0, 0, 534814909727, 1988836846106, 2129288438189, 501687428037, 12268875723, 0, 0, 0] := by
  decide +kernel

theorem rows2219 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2219 = true := by
  decide +kernel

theorem tot2219 : totK PA10K2 A10K2.t2219 = [0, 0, 590308256730, 1812548276814, 1852906811332, 670550606982, 68804449356, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
