import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14616 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14616 = true := by
  decide +kernel

theorem tot14616 : totK PD2M8K2 D2M8K2.t14616 = [0, 0, 204612866205, 476333808437, 194740741244, 12482056447, 0, 0] := by
  decide +kernel

theorem rows14617 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14617 = true := by
  decide +kernel

theorem tot14617 : totK PD2M8K2 D2M8K2.t14617 = [0, 0, 185333289250, 496202602814, 187384699081, 3708492342, 0, 0] := by
  decide +kernel

theorem rows14618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14618 = true := by
  decide +kernel

theorem tot14618 : totK PD2M8K2 D2M8K2.t14618 = [0, 0, 169334178784, 457540321137, 214080236328, 13251578578, 0, 0] := by
  decide +kernel

theorem rows14619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14619 = true := by
  decide +kernel

theorem tot14619 : totK PD2M8K2 D2M8K2.t14619 = [0, 0, 0, 298401316888, 451160878722, 83314480194, 1310517177, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
