import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4360 = true := by
  decide +kernel

theorem tot4360 : totK PD2M8K2 D2M8K2.t4360 = [0, 0, 0, 223799763398, 475251427326, 192762604422, 6713026827, 0] := by
  decide +kernel

theorem rows4361 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4361 = true := by
  decide +kernel

theorem tot4361 : totK PD2M8K2 D2M8K2.t4361 = [0, 0, 0, 0, 331876059477, 468484692717, 75156098322, 1332468113] := by
  decide +kernel

theorem rows4362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4362 = true := by
  decide +kernel

theorem tot4362 : totK PD2M8K2 D2M8K2.t4362 = [0, 0, 0, 166157372645, 457692989557, 247022973693, 22712551131, 0] := by
  decide +kernel

theorem rows4363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4363 = true := by
  decide +kernel

theorem tot4363 : totK PD2M8K2 D2M8K2.t4363 = [0, 0, 0, 170473899286, 435901217184, 266370940728, 22362866037, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
