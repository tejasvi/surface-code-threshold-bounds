import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11168 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11168 = true := by
  decide +kernel

theorem tot11168 : totK PD2M8K2 D2M8K2.t11168 = [0, 161889094836, 458633098334, 262232426669, 16781734060, 0, 0, 0] := by
  decide +kernel

theorem rows11169 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11169 = true := by
  decide +kernel

theorem tot11169 : totK PD2M8K2 D2M8K2.t11169 = [0, 0, 236875939840, 510762795737, 146577461711, 2329117419, 0, 0] := by
  decide +kernel

theorem rows11170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11170 = true := by
  decide +kernel

theorem tot11170 : totK PD2M8K2 D2M8K2.t11170 = [0, 66628313411, 260967803724, 388932934981, 143056967633, 10841558499, 0, 0] := by
  decide +kernel

theorem rows11171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11171 = true := by
  decide +kernel

theorem tot11171 : totK PD2M8K2 D2M8K2.t11171 = [0, 161608367514, 461392251224, 258476445992, 22210949632, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
