import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16040 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16040 = true := by
  decide +kernel

theorem tot16040 : totK PD2M8K2 D2M8K2.t16040 = [0, 0, 134690097165, 440906029203, 288060234635, 24583296246, 0, 0] := by
  decide +kernel

theorem rows16041 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16041 = true := by
  decide +kernel

theorem tot16041 : totK PD2M8K2 D2M8K2.t16041 = [0, 0, 0, 276887575754, 508764320046, 96311310966, 1369150432, 0] := by
  decide +kernel

theorem rows16042 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16042 = true := by
  decide +kernel

theorem tot16042 : totK PD2M8K2 D2M8K2.t16042 = [0, 0, 172273633986, 429053053392, 293326100083, 35741163638, 0, 0] := by
  decide +kernel

theorem rows16043 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16043 = true := by
  decide +kernel

theorem tot16043 : totK PD2M8K2 D2M8K2.t16043 = [0, 0, 205844567484, 492095823284, 217461715140, 8687655683, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
