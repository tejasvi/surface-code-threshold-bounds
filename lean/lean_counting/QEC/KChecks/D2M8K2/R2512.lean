import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10048 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10048 = true := by
  decide +kernel

theorem tot10048 : totK PD2M8K2 D2M8K2.t10048 = [0, 0, 71249301310, 339452150048, 396009582383, 76847613649, 1149959346, 0] := by
  decide +kernel

theorem rows10049 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10049 = true := by
  decide +kernel

theorem tot10049 : totK PD2M8K2 D2M8K2.t10049 = [0, 0, 174257081095, 446675166521, 278321338659, 28919984260, 0, 0] := by
  decide +kernel

theorem rows10050 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10050 = true := by
  decide +kernel

theorem tot10050 : totK PD2M8K2 D2M8K2.t10050 = [0, 0, 172446104734, 464611904887, 245835286418, 15415215284, 0, 0] := by
  decide +kernel

theorem rows10051 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10051 = true := by
  decide +kernel

theorem tot10051 : totK PD2M8K2 D2M8K2.t10051 = [0, 0, 0, 278993705245, 480572940654, 128124988891, 4031931762, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
