import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14396 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14396 = true := by
  decide +kernel

theorem tot14396 : totK PD2M8K2 D2M8K2.t14396 = [0, 0, 49060121697, 361013689865, 364844508161, 56112315629, 1103454931, 0] := by
  decide +kernel

theorem rows14397 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14397 = true := by
  decide +kernel

theorem tot14397 : totK PD2M8K2 D2M8K2.t14397 = [0, 0, 124190121657, 429845891320, 300378866801, 23436331386, 0, 0] := by
  decide +kernel

theorem rows14398 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14398 = true := by
  decide +kernel

theorem tot14398 : totK PD2M8K2 D2M8K2.t14398 = [0, 0, 209177201236, 491339943287, 193400326382, 5014594880, 0, 0] := by
  decide +kernel

theorem rows14399 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14399 = true := by
  decide +kernel

theorem tot14399 : totK PD2M8K2 D2M8K2.t14399 = [0, 0, 238081021861, 475023687542, 166747275722, 9535105402, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
