import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10964 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10964 = true := by
  decide +kernel

theorem tot10964 : totK PD2M8K2 D2M8K2.t10964 = [0, 0, 302602377121, 457860722041, 100416726895, 1369150432, 0, 0] := by
  decide +kernel

theorem rows10965 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10965 = true := by
  decide +kernel

theorem tot10965 : totK PD2M8K2 D2M8K2.t10965 = [0, 179803319846, 460026646963, 235655781061, 16755837386, 0, 0, 0] := by
  decide +kernel

theorem rows10966 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10966 = true := by
  decide +kernel

theorem tot10966 : totK PD2M8K2 D2M8K2.t10966 = [0, 184340548559, 461681093786, 215909689165, 12243442891, 0, 0, 0] := by
  decide +kernel

theorem rows10967 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10967 = true := by
  decide +kernel

theorem tot10967 : totK PD2M8K2 D2M8K2.t10967 = [0, 201392879390, 475860503454, 208578152886, 10177609099, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
