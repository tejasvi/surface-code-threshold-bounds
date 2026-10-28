import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8620 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8620 = true := by
  decide +kernel

theorem tot8620 : totK PD2M8K2 D2M8K2.t8620 = [0, 165428393621, 464263192941, 259027082438, 17167551880, 0, 0, 0] := by
  decide +kernel

theorem rows8621 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8621 = true := by
  decide +kernel

theorem tot8621 : totK PD2M8K2 D2M8K2.t8621 = [0, 213585793981, 478393984657, 207500924242, 11051716772, 0, 0, 0] := by
  decide +kernel

theorem rows8622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8622 = true := by
  decide +kernel

theorem tot8622 : totK PD2M8K2 D2M8K2.t8622 = [0, 162542719202, 473298433817, 238086738944, 12370590376, 0, 0, 0] := by
  decide +kernel

theorem rows8623 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8623 = true := by
  decide +kernel

theorem tot8623 : totK PD2M8K2 D2M8K2.t8623 = [0, 183449280587, 470167064108, 233935593736, 13616632443, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
