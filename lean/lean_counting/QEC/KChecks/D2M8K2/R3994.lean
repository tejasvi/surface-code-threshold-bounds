import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15976 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15976 = true := by
  decide +kernel

theorem tot15976 : totK PD2M8K2 D2M8K2.t15976 = [0, 0, 0, 216157527051, 473529319306, 170231826581, 9799017416, 0] := by
  decide +kernel

theorem rows15977 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15977 = true := by
  decide +kernel

theorem tot15977 : totK PD2M8K2 D2M8K2.t15977 = [0, 0, 0, 237202695378, 490656858562, 142657102673, 2551524611, 0] := by
  decide +kernel

theorem rows15978 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15978 = true := by
  decide +kernel

theorem tot15978 : totK PD2M8K2 D2M8K2.t15978 = [0, 0, 0, 223520786142, 502534764865, 147923096302, 2448800629, 0] := by
  decide +kernel

theorem rows15979 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15979 = true := by
  decide +kernel

theorem tot15979 : totK PD2M8K2 D2M8K2.t15979 = [0, 0, 0, 268261155967, 484955736211, 139980264462, 3946843644, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
