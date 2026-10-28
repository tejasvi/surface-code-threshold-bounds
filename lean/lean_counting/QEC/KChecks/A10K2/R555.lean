import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2220 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2220 = true := by
  decide +kernel

theorem tot2220 : totK PA10K2 A10K2.t2220 = [0, 0, 0, 915581734617, 2286898582870, 1481423670248, 257906266254, 7007974415, 0, 0] := by
  decide +kernel

theorem rows2221 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2221 = true := by
  decide +kernel

theorem tot2221 : totK PA10K2 A10K2.t2221 = [0, 0, 474865294577, 1856431252434, 2087617510468, 633431579662, 41242688036, 0, 0, 0] := by
  decide +kernel

theorem rows2222 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2222 = true := by
  decide +kernel

theorem tot2222 : totK PA10K2 A10K2.t2222 = [0, 316661823121, 1079783406308, 1548197089122, 1452418451119, 574387100275, 50425690648, 0, 0, 0] := by
  decide +kernel

theorem rows2223 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2223 = true := by
  decide +kernel

theorem tot2223 : totK PA10K2 A10K2.t2223 = [0, 446069928637, 1789343791317, 2000188449786, 552353836159, 32207422962, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
