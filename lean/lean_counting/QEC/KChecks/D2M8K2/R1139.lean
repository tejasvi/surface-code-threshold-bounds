import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4556 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4556 = true := by
  decide +kernel

theorem tot4556 : totK PD2M8K2 D2M8K2.t4556 = [0, 0, 182755172275, 462079410197, 264848804536, 26568896397, 0, 0] := by
  decide +kernel

theorem rows4557 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4557 = true := by
  decide +kernel

theorem tot4557 : totK PD2M8K2 D2M8K2.t4557 = [0, 0, 172968728466, 460682378429, 242261935303, 13483641365, 0, 0] := by
  decide +kernel

theorem rows4558 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4558 = true := by
  decide +kernel

theorem tot4558 : totK PD2M8K2 D2M8K2.t4558 = [0, 0, 0, 265724859639, 490090033454, 144177539126, 6821150176, 0] := by
  decide +kernel

theorem rows4559 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4559 = true := by
  decide +kernel

theorem tot4559 : totK PD2M8K2 D2M8K2.t4559 = [0, 0, 90400450959, 324958212700, 392881393423, 99048868362, 2266161007, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
