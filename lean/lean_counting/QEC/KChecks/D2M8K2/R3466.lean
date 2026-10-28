import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13864 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13864 = true := by
  decide +kernel

theorem tot13864 : totK PD2M8K2 D2M8K2.t13864 = [151715084213, 434393776480, 290989989199, 41989693486, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13865 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13865 = true := by
  decide +kernel

theorem tot13865 : totK PD2M8K2 D2M8K2.t13865 = [183343833154, 446695548966, 254738201407, 21467168788, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13866 = true := by
  decide +kernel

theorem tot13866 : totK PD2M8K2 D2M8K2.t13866 = [43287432853, 349242474717, 419993800041, 78786406861, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows13867 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13867 = true := by
  decide +kernel

theorem tot13867 : totK PD2M8K2 D2M8K2.t13867 = [67154020223, 289470308482, 412043979107, 114206948166, 3884009855, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
