import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15344 = true := by
  decide +kernel

theorem tot15344 : totK PD2M8K2 D2M8K2.t15344 = [0, 0, 326976103314, 505156971093, 76233445747, 0, 0, 0] := by
  decide +kernel

theorem rows15345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15345 = true := by
  decide +kernel

theorem tot15345 : totK PD2M8K2 D2M8K2.t15345 = [0, 88130666923, 337333751092, 374916771887, 98688546057, 2585032425, 0, 0] := by
  decide +kernel

theorem rows15346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15346 = true := by
  decide +kernel

theorem tot15346 : totK PD2M8K2 D2M8K2.t15346 = [0, 173872417280, 440073790711, 274416206042, 30191107111, 0, 0, 0] := by
  decide +kernel

theorem rows15347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15347 = true := by
  decide +kernel

theorem tot15347 : totK PD2M8K2 D2M8K2.t15347 = [0, 163930573481, 460139235510, 268176025725, 21883372984, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
