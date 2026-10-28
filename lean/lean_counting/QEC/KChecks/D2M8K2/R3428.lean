import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13712 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13712 = true := by
  decide +kernel

theorem tot13712 : totK PD2M8K2 D2M8K2.t13712 = [0, 52068623752, 328082297099, 434643536683, 85126219681, 1164319620, 0, 0] := by
  decide +kernel

theorem rows13713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13713 = true := by
  decide +kernel

theorem tot13713 : totK PD2M8K2 D2M8K2.t13713 = [0, 0, 197175693850, 468324191160, 188575469978, 11885407614, 0, 0] := by
  decide +kernel

theorem rows13714 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13714 = true := by
  decide +kernel

theorem tot13714 : totK PD2M8K2 D2M8K2.t13714 = [0, 150443794684, 436314855688, 290768449743, 32822159651, 0, 0, 0] := by
  decide +kernel

theorem rows13715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13715 = true := by
  decide +kernel

theorem tot13715 : totK PD2M8K2 D2M8K2.t13715 = [0, 174575961514, 435808761951, 255777064491, 22470554710, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
