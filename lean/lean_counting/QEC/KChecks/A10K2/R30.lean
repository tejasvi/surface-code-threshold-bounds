import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows120 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t120 = true := by
  decide +kernel

theorem tot120 : totK PA10K2 A10K2.t120 = [0, 471204071551, 1717120975256, 1822158329571, 597933774663, 51464731716, 0, 0, 0, 0] := by
  decide +kernel

theorem rows121 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t121 = true := by
  decide +kernel

theorem tot121 : totK PA10K2 A10K2.t121 = [0, 0, 911603597321, 2377081288819, 1259397204552, 112680555227, 0, 0, 0, 0] := by
  decide +kernel

theorem rows122 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t122 = true := by
  decide +kernel

theorem tot122 : totK PA10K2 A10K2.t122 = [0, 511453697279, 1601315224904, 1721939582168, 882488681928, 187413838633, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows123 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t123 = true := by
  decide +kernel

theorem tot123 : totK PA10K2 A10K2.t123 = [0, 78784909528, 941941245254, 2188553868218, 1527772892713, 262843379146, 6853348008, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
