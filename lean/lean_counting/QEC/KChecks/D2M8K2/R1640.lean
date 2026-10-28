import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6560 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6560 = true := by
  decide +kernel

theorem tot6560 : totK PD2M8K2 D2M8K2.t6560 = [0, 279367814896, 515561467031, 104773128400, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows6561 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6561 = true := by
  decide +kernel

theorem tot6561 : totK PD2M8K2 D2M8K2.t6561 = [0, 211483978473, 492148045011, 177259640967, 5253830308, 0, 0, 0] := by
  decide +kernel

theorem rows6562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6562 = true := by
  decide +kernel

theorem tot6562 : totK PD2M8K2 D2M8K2.t6562 = [0, 200824696240, 471359644040, 194231016654, 9713690252, 0, 0, 0] := by
  decide +kernel

theorem rows6563 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6563 = true := by
  decide +kernel

theorem tot6563 : totK PD2M8K2 D2M8K2.t6563 = [0, 86005329647, 371829887695, 338834260673, 56394390424, 1239866073, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
