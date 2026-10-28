import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3092 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3092 = true := by
  decide +kernel

theorem tot3092 : totK PA10K2 A10K2.t3092 = [0, 304638153981, 1002782565961, 1050577625441, 867083289516, 1080951808729, 506914864948, 49137922124, 0, 0] := by
  decide +kernel

theorem rows3093 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3093 = true := by
  decide +kernel

theorem tot3093 : totK PA10K2 A10K2.t3093 = [0, 473271288100, 1841739920495, 2084580666067, 647290532879, 24891698380, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3094 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3094 = true := by
  decide +kernel

theorem tot3094 : totK PA10K2 A10K2.t3094 = [0, 0, 494336561174, 1813525357017, 1833998189666, 497296408312, 30831673886, 0, 0, 0] := by
  decide +kernel

theorem rows3095 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3095 = true := by
  decide +kernel

theorem tot3095 : totK PA10K2 A10K2.t3095 = [0, 265289717592, 1384961362423, 2168182464244, 1032202780968, 106500842687, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
