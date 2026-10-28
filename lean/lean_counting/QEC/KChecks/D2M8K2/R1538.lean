import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6152 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6152 = true := by
  decide +kernel

theorem tot6152 : totK PD2M8K2 D2M8K2.t6152 = [0, 196942837705, 484752494893, 209789282120, 7807117139, 0, 0, 0] := by
  decide +kernel

theorem rows6153 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6153 = true := by
  decide +kernel

theorem tot6153 : totK PD2M8K2 D2M8K2.t6153 = [0, 195885252143, 468155224135, 218783934322, 10760992776, 0, 0, 0] := by
  decide +kernel

theorem rows6154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6154 = true := by
  decide +kernel

theorem tot6154 : totK PD2M8K2 D2M8K2.t6154 = [75343266900, 227111501636, 369319595844, 219993259289, 17433533548, 0, 0, 0] := by
  decide +kernel

theorem rows6155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6155 = true := by
  decide +kernel

theorem tot6155 : totK PD2M8K2 D2M8K2.t6155 = [173795989759, 439308098247, 284233449200, 30379478485, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
