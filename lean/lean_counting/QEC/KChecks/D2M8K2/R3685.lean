import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14740 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14740 = true := by
  decide +kernel

theorem tot14740 : totK PD2M8K2 D2M8K2.t14740 = [122982374721, 426491162301, 317504069685, 27821048014, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14741 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14741 = true := by
  decide +kernel

theorem tot14741 : totK PD2M8K2 D2M8K2.t14741 = [0, 204635031386, 482110311074, 188888978893, 9668735432, 0, 0, 0] := by
  decide +kernel

theorem rows14742 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14742 = true := by
  decide +kernel

theorem tot14742 : totK PD2M8K2 D2M8K2.t14742 = [86448444628, 323854303358, 358277077721, 101982099397, 3581949829, 0, 0, 0] := by
  decide +kernel

theorem rows14743 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14743 = true := by
  decide +kernel

theorem tot14743 : totK PD2M8K2 D2M8K2.t14743 = [177886690194, 452173079698, 241086722358, 17104814242, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
