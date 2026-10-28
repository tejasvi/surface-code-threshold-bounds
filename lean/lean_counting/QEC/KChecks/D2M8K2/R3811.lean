import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15244 = true := by
  decide +kernel

theorem tot15244 : totK PD2M8K2 D2M8K2.t15244 = [0, 0, 178344286931, 456048431984, 254650519694, 18387281282, 0, 0] := by
  decide +kernel

theorem rows15245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15245 = true := by
  decide +kernel

theorem tot15245 : totK PD2M8K2 D2M8K2.t15245 = [0, 0, 154416783043, 444636985572, 285968286598, 21775997421, 0, 0] := by
  decide +kernel

theorem rows15246 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15246 = true := by
  decide +kernel

theorem tot15246 : totK PD2M8K2 D2M8K2.t15246 = [0, 0, 0, 218055270457, 502588802710, 149787886297, 4928554699, 0] := by
  decide +kernel

theorem rows15247 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15247 = true := by
  decide +kernel

theorem tot15247 : totK PD2M8K2 D2M8K2.t15247 = [0, 0, 0, 194964602253, 460803288618, 196289892572, 16843409175, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
