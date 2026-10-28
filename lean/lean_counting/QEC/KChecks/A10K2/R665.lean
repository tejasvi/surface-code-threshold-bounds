import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2660 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2660 = true := by
  decide +kernel

theorem tot2660 : totK PA10K2 A10K2.t2660 = [0, 58470587612, 730009166011, 2088839113796, 1540223340308, 253928448144, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows2661 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2661 = true := by
  decide +kernel

theorem tot2661 : totK PA10K2 A10K2.t2661 = [0, 636652483932, 2099143214417, 1919982177050, 480849014338, 26374032118, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2662 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2662 = true := by
  decide +kernel

theorem tot2662 : totK PA10K2 A10K2.t2662 = [0, 0, 775093968986, 2314616480264, 1750462171554, 321282023178, 6962742351, 0, 0, 0] := by
  decide +kernel

theorem rows2663 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2663 = true := by
  decide +kernel

theorem tot2663 : totK PA10K2 A10K2.t2663 = [0, 0, 611821954803, 1991275886364, 1876091532721, 545385070183, 35117149505, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
