import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10916 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10916 = true := by
  decide +kernel

theorem tot10916 : totK PD2M8K2 D2M8K2.t10916 = [0, 123351558152, 438424124035, 321036240140, 27741077662, 0, 0, 0] := by
  decide +kernel

theorem rows10917 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10917 = true := by
  decide +kernel

theorem tot10917 : totK PD2M8K2 D2M8K2.t10917 = [0, 0, 195054752381, 488210714519, 190680960497, 9652233629, 0, 0] := by
  decide +kernel

theorem rows10918 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10918 = true := by
  decide +kernel

theorem tot10918 : totK PD2M8K2 D2M8K2.t10918 = [0, 87123270202, 353834866021, 363509425443, 92597441150, 3564119920, 0, 0] := by
  decide +kernel

theorem rows10919 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10919 = true := by
  decide +kernel

theorem tot10919 : totK PD2M8K2 D2M8K2.t10919 = [0, 177997545107, 444049644315, 274140414206, 28643289390, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
