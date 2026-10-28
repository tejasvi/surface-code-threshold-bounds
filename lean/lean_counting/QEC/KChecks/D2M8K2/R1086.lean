import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4344 = true := by
  decide +kernel

theorem tot4344 : totK PD2M8K2 D2M8K2.t4344 = [0, 0, 164800286972, 453627107833, 274519286634, 32386210880, 0, 0] := by
  decide +kernel

theorem rows4345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4345 = true := by
  decide +kernel

theorem tot4345 : totK PD2M8K2 D2M8K2.t4345 = [0, 0, 195699025273, 472389214926, 223423478426, 15374826919, 0, 0] := by
  decide +kernel

theorem rows4346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4346 = true := by
  decide +kernel

theorem tot4346 : totK PD2M8K2 D2M8K2.t4346 = [0, 0, 53287976846, 343767406113, 442214739809, 72445398079, 0, 0] := by
  decide +kernel

theorem rows4347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4347 = true := by
  decide +kernel

theorem tot4347 : totK PD2M8K2 D2M8K2.t4347 = [0, 0, 0, 216017018436, 482132942608, 176384515258, 6654590951, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
