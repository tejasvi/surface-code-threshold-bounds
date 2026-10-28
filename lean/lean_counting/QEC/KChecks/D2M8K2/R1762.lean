import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7048 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7048 = true := by
  decide +kernel

theorem tot7048 : totK PD2M8K2 D2M8K2.t7048 = [0, 0, 0, 256779637723, 483281796975, 130113915377, 3569676519, 0] := by
  decide +kernel

theorem rows7049 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7049 = true := by
  decide +kernel

theorem tot7049 : totK PD2M8K2 D2M8K2.t7049 = [0, 92342479873, 161177781494, 127164903489, 299880833235, 185773535021, 16939352947, 0] := by
  decide +kernel

theorem rows7050 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7050 = true := by
  decide +kernel

theorem tot7050 : totK PD2M8K2 D2M8K2.t7050 = [0, 174576905601, 483052443586, 233314691791, 10870740798, 0, 0, 0] := by
  decide +kernel

theorem rows7051 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7051 = true := by
  decide +kernel

theorem tot7051 : totK PD2M8K2 D2M8K2.t7051 = [0, 175505707022, 465001257835, 248679078898, 15130212454, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
