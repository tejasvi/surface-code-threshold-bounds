import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4140 = true := by
  decide +kernel

theorem tot4140 : totK PD2M8K2 D2M8K2.t4140 = [0, 153125176227, 456061046655, 277630801522, 19806708611, 0, 0, 0] := by
  decide +kernel

theorem rows4141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4141 = true := by
  decide +kernel

theorem tot4141 : totK PD2M8K2 D2M8K2.t4141 = [0, 0, 206519258112, 484582704406, 185264306041, 9668735432, 0, 0] := by
  decide +kernel

theorem rows4142 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4142 = true := by
  decide +kernel

theorem tot4142 : totK PD2M8K2 D2M8K2.t4142 = [0, 80883928075, 317872598957, 378844584707, 100708003985, 3581949829, 0, 0] := by
  decide +kernel

theorem rows4143 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4143 = true := by
  decide +kernel

theorem tot4143 : totK PD2M8K2 D2M8K2.t4143 = [0, 176990743926, 451964513523, 267543269044, 27881952543, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
