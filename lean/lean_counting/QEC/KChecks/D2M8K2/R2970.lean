import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11880 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11880 = true := by
  decide +kernel

theorem tot11880 : totK PD2M8K2 D2M8K2.t11880 = [19692840307, 306852478959, 462480132525, 105431630410, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows11881 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11881 = true := by
  decide +kernel

theorem tot11881 : totK PD2M8K2 D2M8K2.t11881 = [0, 208282897004, 474341714913, 179632763946, 7442000727, 0, 0, 0] := by
  decide +kernel

theorem rows11882 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11882 = true := by
  decide +kernel

theorem tot11882 : totK PD2M8K2 D2M8K2.t11882 = [0, 172969524593, 467914599630, 227492159746, 15860424110, 0, 0, 0] := by
  decide +kernel

theorem rows11883 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11883 = true := by
  decide +kernel

theorem tot11883 : totK PD2M8K2 D2M8K2.t11883 = [0, 173511103334, 449961799865, 225309890843, 16561712910, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
