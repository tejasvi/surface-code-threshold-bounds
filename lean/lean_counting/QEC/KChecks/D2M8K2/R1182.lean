import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4728 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4728 = true := by
  decide +kernel

theorem tot4728 : totK PD2M8K2 D2M8K2.t4728 = [0, 0, 198564876290, 497241497526, 191993139897, 9668735432, 0, 0] := by
  decide +kernel

theorem rows4729 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4729 = true := by
  decide +kernel

theorem tot4729 : totK PD2M8K2 D2M8K2.t4729 = [0, 82383434728, 315932164537, 378325923694, 103497459925, 3581949829, 0, 0] := by
  decide +kernel

theorem rows4730 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4730 = true := by
  decide +kernel

theorem tot4730 : totK PD2M8K2 D2M8K2.t4730 = [0, 153158986055, 446574773175, 270297553322, 26583472999, 0, 0, 0] := by
  decide +kernel

theorem rows4731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4731 = true := by
  decide +kernel

theorem tot4731 : totK PD2M8K2 D2M8K2.t4731 = [0, 180567783026, 475016705523, 240065783843, 14985674079, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
