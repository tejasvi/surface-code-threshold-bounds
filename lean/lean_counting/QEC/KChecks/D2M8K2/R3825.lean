import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15300 = true := by
  decide +kernel

theorem tot15300 : totK PD2M8K2 D2M8K2.t15300 = [0, 0, 164640597464, 471400643012, 240551397889, 13630046840, 0, 0] := by
  decide +kernel

theorem rows15301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15301 = true := by
  decide +kernel

theorem tot15301 : totK PD2M8K2 D2M8K2.t15301 = [0, 0, 0, 294476610725, 503244658666, 82673044511, 1164319620, 0] := by
  decide +kernel

theorem rows15302 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15302 = true := by
  decide +kernel

theorem tot15302 : totK PD2M8K2 D2M8K2.t15302 = [0, 0, 142020996997, 434158854507, 293786257092, 24026319056, 0, 0] := by
  decide +kernel

theorem rows15303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15303 = true := by
  decide +kernel

theorem tot15303 : totK PD2M8K2 D2M8K2.t15303 = [0, 0, 185214699773, 460152974624, 250860610876, 17213049621, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
