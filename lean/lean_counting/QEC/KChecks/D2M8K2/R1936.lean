import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7744 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7744 = true := by
  decide +kernel

theorem tot7744 : totK PD2M8K2 D2M8K2.t7744 = [0, 0, 186235177522, 495918866565, 210347286826, 7483396811, 0, 0] := by
  decide +kernel

theorem rows7745 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7745 = true := by
  decide +kernel

theorem tot7745 : totK PD2M8K2 D2M8K2.t7745 = [0, 0, 87592756475, 368749053528, 351637884812, 52621301640, 1104198603, 0] := by
  decide +kernel

theorem rows7746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7746 = true := by
  decide +kernel

theorem tot7746 : totK PD2M8K2 D2M8K2.t7746 = [0, 0, 85383260213, 351888322848, 358278220663, 70832775405, 3581949829, 0] := by
  decide +kernel

theorem rows7747 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7747 = true := by
  decide +kernel

theorem tot7747 : totK PD2M8K2 D2M8K2.t7747 = [0, 0, 176450019734, 465778986691, 255811025834, 17186216661, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
