import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8640 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8640 = true := by
  decide +kernel

theorem tot8640 : totK PD2M8K2 D2M8K2.t8640 = [78591702769, 319462212174, 368747569709, 115837687119, 8388657623, 0, 0, 0] := by
  decide +kernel

theorem rows8641 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8641 = true := by
  decide +kernel

theorem tot8641 : totK PD2M8K2 D2M8K2.t8641 = [180399678129, 454629442801, 265383644556, 27917257514, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8642 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8642 = true := by
  decide +kernel

theorem tot8642 : totK PD2M8K2 D2M8K2.t8642 = [157971732341, 456213612712, 275325101094, 21337181412, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8643 = true := by
  decide +kernel

theorem tot8643 : totK PD2M8K2 D2M8K2.t8643 = [0, 239393801801, 505642217306, 150546472107, 2348440009, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
