import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13516 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13516 = true := by
  decide +kernel

theorem tot13516 : totK PD2M8K2 D2M8K2.t13516 = [185540208842, 448512807374, 230927879817, 17104814242, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13517 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13517 = true := by
  decide +kernel

theorem tot13517 : totK PD2M8K2 D2M8K2.t13517 = [55761343512, 344475222707, 408445437749, 69969056101, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows13518 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13518 = true := by
  decide +kernel

theorem tot13518 : totK PD2M8K2 D2M8K2.t13518 = [29445328733, 273085821029, 456064229284, 122980537846, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows13519 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13519 = true := by
  decide +kernel

theorem tot13519 : totK PD2M8K2 D2M8K2.t13519 = [192591788741, 469866605920, 231198755883, 20232616314, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
