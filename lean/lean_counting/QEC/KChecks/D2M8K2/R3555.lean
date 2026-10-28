import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14220 = true := by
  decide +kernel

theorem tot14220 : totK PD2M8K2 D2M8K2.t14220 = [0, 88579576547, 364468842342, 355534677960, 67523614321, 1162935789, 0, 0] := by
  decide +kernel

theorem rows14221 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14221 = true := by
  decide +kernel

theorem tot14221 : totK PD2M8K2 D2M8K2.t14221 = [0, 0, 261025148231, 471628076513, 142124768530, 8416438934, 0, 0] := by
  decide +kernel

theorem rows14222 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14222 = true := by
  decide +kernel

theorem tot14222 : totK PD2M8K2 D2M8K2.t14222 = [0, 135358512438, 371932715273, 275746111053, 71165278393, 3436822651, 0, 0] := by
  decide +kernel

theorem rows14223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14223 = true := by
  decide +kernel

theorem tot14223 : totK PD2M8K2 D2M8K2.t14223 = [0, 172473481689, 465178734052, 245413520967, 18252358503, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
