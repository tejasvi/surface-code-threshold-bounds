import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16372 = true := by
  decide +kernel

theorem tot16372 : totK PD2M8K2 D2M8K2.t16372 = [0, 0, 0, 181676448264, 476305735286, 226494083562, 14207203644, 0] := by
  decide +kernel

theorem rows16373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16373 = true := by
  decide +kernel

theorem tot16373 : totK PD2M8K2 D2M8K2.t16373 = [0, 0, 0, 173558142410, 455794456709, 222015322994, 11831259726, 0] := by
  decide +kernel

theorem rows16374 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16374 = true := by
  decide +kernel

theorem tot16374 : totK PD2M8K2 D2M8K2.t16374 = [0, 0, 0, 71815494694, 346471114068, 388700480620, 67117698892, 1054738420] := by
  decide +kernel

theorem rows16375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16375 = true := by
  decide +kernel

theorem tot16375 : totK PD2M8K2 D2M8K2.t16375 = [0, 0, 0, 31785185157, 298503540611, 415231490321, 99737695152, 3732315745] := by
  decide +kernel

end QECKChecks.D2M8K2
