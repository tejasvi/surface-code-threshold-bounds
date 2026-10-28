import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13384 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13384 = true := by
  decide +kernel

theorem tot13384 : totK PD2M8K2 D2M8K2.t13384 = [0, 0, 179821548492, 479508982822, 239253549463, 12227244834, 0, 0] := by
  decide +kernel

theorem rows13385 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13385 = true := by
  decide +kernel

theorem tot13385 : totK PD2M8K2 D2M8K2.t13385 = [0, 0, 174154374474, 454208523484, 241673275173, 15076589585, 0, 0] := by
  decide +kernel

theorem rows13386 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13386 = true := by
  decide +kernel

theorem tot13386 : totK PD2M8K2 D2M8K2.t13386 = [0, 0, 192164662434, 476746582062, 218799673243, 15844255384, 0, 0] := by
  decide +kernel

theorem rows13387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13387 = true := by
  decide +kernel

theorem tot13387 : totK PD2M8K2 D2M8K2.t13387 = [0, 0, 179463675600, 460770224977, 229546034236, 16702988424, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
