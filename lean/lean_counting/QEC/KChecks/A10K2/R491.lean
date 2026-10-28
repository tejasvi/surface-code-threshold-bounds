import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1964 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1964 = true := by
  decide +kernel

theorem tot1964 : totK PA10K2 A10K2.t1964 = [0, 270838076424, 1328479878901, 2098727425122, 1249639962160, 229111880173, 6851704726, 0, 0, 0] := by
  decide +kernel

theorem rows1965 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1965 = true := by
  decide +kernel

theorem tot1965 : totK PA10K2 A10K2.t1965 = [0, 0, 608974484474, 2103648026080, 1963716807995, 387956651684, 6962742351, 0, 0, 0] := by
  decide +kernel

theorem rows1966 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1966 = true := by
  decide +kernel

theorem tot1966 : totK PA10K2 A10K2.t1966 = [0, 0, 409535206189, 1555964421845, 1969730494749, 814355862500, 75643137603, 0, 0, 0] := by
  decide +kernel

theorem rows1967 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1967 = true := by
  decide +kernel

theorem tot1967 : totK PA10K2 A10K2.t1967 = [0, 0, 370513210790, 1641306058834, 2131937695225, 798896928653, 61866981726, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
