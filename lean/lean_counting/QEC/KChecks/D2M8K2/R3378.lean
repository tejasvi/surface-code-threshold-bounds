import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13512 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13512 = true := by
  decide +kernel

theorem tot13512 : totK PD2M8K2 D2M8K2.t13512 = [188439665601, 461517915483, 224064376288, 12523541424, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13513 = true := by
  decide +kernel

theorem tot13513 : totK PD2M8K2 D2M8K2.t13513 = [37939107553, 310741784358, 448242443307, 98459121221, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows13514 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13514 = true := by
  decide +kernel

theorem tot13514 : totK PD2M8K2 D2M8K2.t13514 = [0, 197533452321, 461801099523, 190389008958, 12052611869, 0, 0, 0] := by
  decide +kernel

theorem rows13515 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13515 = true := by
  decide +kernel

theorem tot13515 : totK PD2M8K2 D2M8K2.t13515 = [156361785850, 428707711898, 276621210412, 32744592004, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
