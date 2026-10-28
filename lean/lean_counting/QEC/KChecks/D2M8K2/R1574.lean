import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6296 = true := by
  decide +kernel

theorem tot6296 : totK PD2M8K2 D2M8K2.t6296 = [0, 144801674033, 450006463813, 294815757761, 23266604953, 0, 0, 0] := by
  decide +kernel

theorem rows6297 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6297 = true := by
  decide +kernel

theorem tot6297 : totK PD2M8K2 D2M8K2.t6297 = [0, 0, 243587608821, 478589886843, 141181533787, 4931404646, 0, 0] := by
  decide +kernel

theorem rows6298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6298 = true := by
  decide +kernel

theorem tot6298 : totK PD2M8K2 D2M8K2.t6298 = [0, 175439753920, 454993898134, 253497834794, 27024206121, 0, 0, 0] := by
  decide +kernel

theorem rows6299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6299 = true := by
  decide +kernel

theorem tot6299 : totK PD2M8K2 D2M8K2.t6299 = [0, 171257418686, 457561586239, 252970918778, 16829263881, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
