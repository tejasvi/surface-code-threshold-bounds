import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11080 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11080 = true := by
  decide +kernel

theorem tot11080 : totK PD2M8K2 D2M8K2.t11080 = [0, 319454184730, 514442507817, 72417504577, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11081 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11081 = true := by
  decide +kernel

theorem tot11081 : totK PD2M8K2 D2M8K2.t11081 = [190366795483, 447360114877, 243847741113, 27479320354, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11082 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11082 = true := by
  decide +kernel

theorem tot11082 : totK PD2M8K2 D2M8K2.t11082 = [199075123833, 469308364015, 214289224079, 12356293777, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11083 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11083 = true := by
  decide +kernel

theorem tot11083 : totK PD2M8K2 D2M8K2.t11083 = [7930757961, 302105160271, 483444429233, 100690870130, 1164319620, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
