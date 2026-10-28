import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16100 = true := by
  decide +kernel

theorem tot16100 : totK PD2M8K2 D2M8K2.t16100 = [0, 19374756099, 316673937406, 474541234332, 98279802321, 1197396724, 0, 0] := by
  decide +kernel

theorem rows16101 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16101 = true := by
  decide +kernel

theorem tot16101 : totK PD2M8K2 D2M8K2.t16101 = [0, 0, 200929843374, 477052137781, 187805864990, 10580318081, 0, 0] := by
  decide +kernel

theorem rows16102 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16102 = true := by
  decide +kernel

theorem tot16102 : totK PD2M8K2 D2M8K2.t16102 = [0, 172217339405, 435959042789, 286703711313, 36500648008, 0, 0, 0] := by
  decide +kernel

theorem rows16103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16103 = true := by
  decide +kernel

theorem tot16103 : totK PD2M8K2 D2M8K2.t16103 = [0, 155333559663, 462539549994, 276299079527, 24297862525, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
