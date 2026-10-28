import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t164 = true := by
  decide +kernel

theorem tot164 : totK PD2M8K2 D2M8K2.t164 = [0, 155794207477, 444652505758, 272138290225, 21670518515, 0, 0, 0] := by
  decide +kernel

theorem rows165 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t165 = true := by
  decide +kernel

theorem tot165 : totK PD2M8K2 D2M8K2.t165 = [0, 0, 248448202582, 483583886421, 127602959986, 4879840392, 0, 0] := by
  decide +kernel

theorem rows166 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t166 = true := by
  decide +kernel

theorem tot166 : totK PD2M8K2 D2M8K2.t166 = [0, 114077852496, 402850694644, 326075575494, 39176005166, 0, 0, 0] := by
  decide +kernel

theorem rows167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t167 = true := by
  decide +kernel

theorem tot167 : totK PD2M8K2 D2M8K2.t167 = [0, 171807044681, 440137409842, 265355439249, 27723706782, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
