import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14628 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14628 = true := by
  decide +kernel

theorem tot14628 : totK PD2M8K2 D2M8K2.t14628 = [0, 173928958965, 450695388444, 276103350797, 28475720695, 0, 0, 0] := by
  decide +kernel

theorem rows14629 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14629 = true := by
  decide +kernel

theorem tot14629 : totK PD2M8K2 D2M8K2.t14629 = [0, 191967858886, 483496640308, 219745723402, 11179141883, 0, 0, 0] := by
  decide +kernel

theorem rows14630 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14630 = true := by
  decide +kernel

theorem tot14630 : totK PD2M8K2 D2M8K2.t14630 = [0, 19474609260, 268117746720, 423153728432, 188984796946, 21400436502, 0, 0] := by
  decide +kernel

theorem rows14631 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14631 = true := by
  decide +kernel

theorem tot14631 : totK PD2M8K2 D2M8K2.t14631 = [0, 0, 205536128640, 478376704308, 199263826013, 7928598406, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
