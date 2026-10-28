import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8820 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8820 = true := by
  decide +kernel

theorem tot8820 : totK PD2M8K2 D2M8K2.t8820 = [0, 0, 191347507135, 459718790471, 213375957225, 17041558502, 0, 0] := by
  decide +kernel

theorem rows8821 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8821 = true := by
  decide +kernel

theorem tot8821 : totK PD2M8K2 D2M8K2.t8821 = [0, 0, 277239829478, 511960142647, 126493475355, 1369820453, 0, 0] := by
  decide +kernel

theorem rows8822 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8822 = true := by
  decide +kernel

theorem tot8822 : totK PD2M8K2 D2M8K2.t8822 = [0, 0, 168094073185, 436785849645, 267654489918, 27027668444, 0, 0] := by
  decide +kernel

theorem rows8823 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8823 = true := by
  decide +kernel

theorem tot8823 : totK PD2M8K2 D2M8K2.t8823 = [0, 0, 214457313255, 484208529134, 202377440937, 6553345076, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
