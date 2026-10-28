import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13800 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13800 = true := by
  decide +kernel

theorem tot13800 : totK PD2M8K2 D2M8K2.t13800 = [0, 0, 174546362632, 457786571740, 246153137849, 16460032206, 0, 0] := by
  decide +kernel

theorem rows13801 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13801 = true := by
  decide +kernel

theorem tot13801 : totK PD2M8K2 D2M8K2.t13801 = [0, 10283532795, 177913166861, 464269872723, 216929108191, 10017192441, 0, 0] := by
  decide +kernel

theorem rows13802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13802 = true := by
  decide +kernel

theorem tot13802 : totK PD2M8K2 D2M8K2.t13802 = [0, 196432865685, 458738366888, 237819860904, 23099921452, 0, 0, 0] := by
  decide +kernel

theorem rows13803 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13803 = true := by
  decide +kernel

theorem tot13803 : totK PD2M8K2 D2M8K2.t13803 = [0, 180287915531, 471167570512, 220107424839, 12146590560, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
