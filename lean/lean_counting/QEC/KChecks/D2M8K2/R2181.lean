import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8724 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8724 = true := by
  decide +kernel

theorem tot8724 : totK PD2M8K2 D2M8K2.t8724 = [0, 0, 163518337462, 428625349447, 288305724779, 33507069526, 0, 0] := by
  decide +kernel

theorem rows8725 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8725 = true := by
  decide +kernel

theorem tot8725 : totK PD2M8K2 D2M8K2.t8725 = [0, 0, 173396785304, 484264109967, 226103653573, 10625029159, 0, 0] := by
  decide +kernel

theorem rows8726 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8726 = true := by
  decide +kernel

theorem tot8726 : totK PD2M8K2 D2M8K2.t8726 = [0, 0, 177037516370, 458848110411, 237456705622, 13265697193, 0, 0] := by
  decide +kernel

theorem rows8727 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8727 = true := by
  decide +kernel

theorem tot8727 : totK PD2M8K2 D2M8K2.t8727 = [0, 0, 178058404940, 450597908720, 260416449694, 23282239808, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
