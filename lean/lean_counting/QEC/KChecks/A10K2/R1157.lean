import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4628 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4628 = true := by
  decide +kernel

theorem tot4628 : totK PA10K2 A10K2.t4628 = [0, 310172558276, 1573800126132, 2120987995759, 745301846678, 53529463056, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4629 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4629 = true := by
  decide +kernel

theorem tot4629 : totK PA10K2 A10K2.t4629 = [0, 191761985142, 1133569849942, 2094573975493, 1254192718530, 192983494206, 6239673734, 0, 0, 0] := by
  decide +kernel

theorem rows4630 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4630 = true := by
  decide +kernel

theorem tot4630 : totK PA10K2 A10K2.t4630 = [0, 612240640940, 2023756022947, 1876416944252, 478989474451, 25944972470, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4631 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4631 = true := by
  decide +kernel

theorem tot4631 : totK PA10K2 A10K2.t4631 = [0, 0, 712728605100, 2279198891529, 1816601141657, 320768387686, 6279851884, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
