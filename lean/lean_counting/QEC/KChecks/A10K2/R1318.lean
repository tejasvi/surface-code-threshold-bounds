import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5272 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5272 = true := by
  decide +kernel

theorem tot5272 : totK PA10K2 A10K2.t5272 = [0, 0, 728236139843, 2206685670504, 1555937276717, 258412225865, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows5273 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5273 = true := by
  decide +kernel

theorem tot5273 : totK PA10K2 A10K2.t5273 = [0, 0, 453590476629, 1832762725113, 1954405230028, 482548402024, 26479096260, 0, 0, 0] := by
  decide +kernel

theorem rows5274 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5274 = true := by
  decide +kernel

theorem tot5274 : totK PA10K2 A10K2.t5274 = [0, 0, 189143449987, 1053362707112, 1969797047996, 1347026604246, 298519597310, 25565504801, 0, 0] := by
  decide +kernel

theorem rows5275 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5275 = true := by
  decide +kernel

theorem tot5275 : totK PA10K2 A10K2.t5275 = [0, 0, 246316869382, 1172432573306, 2000547908066, 1149454335946, 176228502697, 5517381808, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
