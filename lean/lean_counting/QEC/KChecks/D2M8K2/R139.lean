import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows556 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t556 = true := by
  decide +kernel

theorem tot556 : totK PD2M8K2 D2M8K2.t556 = [0, 0, 212297437688, 477139912555, 168213602560, 9464357663, 0, 0] := by
  decide +kernel

theorem rows557 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t557 = true := by
  decide +kernel

theorem tot557 : totK PD2M8K2 D2M8K2.t557 = [0, 0, 102714041118, 401205643337, 290074313847, 42204048962, 1103454931, 0] := by
  decide +kernel

theorem rows558 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t558 = true := by
  decide +kernel

theorem tot558 : totK PD2M8K2 D2M8K2.t558 = [0, 0, 69535932396, 397955113518, 357213317218, 31333671848, 0, 0] := by
  decide +kernel

theorem rows559 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t559 = true := by
  decide +kernel

theorem tot559 : totK PD2M8K2 D2M8K2.t559 = [0, 0, 201537653713, 466114364776, 216415458204, 14862756435, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
