import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6588 = true := by
  decide +kernel

theorem tot6588 : totK PD2M8K2 D2M8K2.t6588 = [177743929200, 441830016834, 265088857122, 28721894169, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6589 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6589 = true := by
  decide +kernel

theorem tot6589 : totK PD2M8K2 D2M8K2.t6589 = [140247328733, 442362943262, 291646310053, 18021231730, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6590 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6590 = true := by
  decide +kernel

theorem tot6590 : totK PD2M8K2 D2M8K2.t6590 = [0, 197790239687, 468052268731, 190314342387, 9668735432, 0, 0, 0] := by
  decide +kernel

theorem rows6591 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6591 = true := by
  decide +kernel

theorem tot6591 : totK PD2M8K2 D2M8K2.t6591 = [86527685341, 333612997822, 365261502707, 95003721065, 3581949829, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
