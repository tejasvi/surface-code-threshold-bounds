import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6480 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6480 = true := by
  decide +kernel

theorem tot6480 : totK PD2M8K2 D2M8K2.t6480 = [181643737189, 473623559324, 231020990809, 12491870267, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6481 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6481 = true := by
  decide +kernel

theorem tot6481 : totK PD2M8K2 D2M8K2.t6481 = [44456655414, 336268511558, 431475523785, 94722434292, 1197396724, 0, 0, 0] := by
  decide +kernel

theorem rows6482 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6482 = true := by
  decide +kernel

theorem tot6482 : totK PD2M8K2 D2M8K2.t6482 = [0, 187150718622, 474763679890, 195788249005, 12040273252, 0, 0, 0] := by
  decide +kernel

theorem rows6483 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6483 = true := by
  decide +kernel

theorem tot6483 : totK PD2M8K2 D2M8K2.t6483 = [194873206748, 458606947849, 240986895694, 26188383011, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
