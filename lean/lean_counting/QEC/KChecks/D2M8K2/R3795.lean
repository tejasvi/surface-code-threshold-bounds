import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15180 = true := by
  decide +kernel

theorem tot15180 : totK PD2M8K2 D2M8K2.t15180 = [0, 0, 303088174292, 509470982450, 91583802392, 1069412848, 0, 0] := by
  decide +kernel

theorem rows15181 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15181 = true := by
  decide +kernel

theorem tot15181 : totK PD2M8K2 D2M8K2.t15181 = [0, 0, 175439649984, 480951737221, 209956910454, 11083827978, 0, 0] := by
  decide +kernel

theorem rows15182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15182 = true := by
  decide +kernel

theorem tot15182 : totK PD2M8K2 D2M8K2.t15182 = [0, 0, 183308582787, 456704783254, 211204866045, 13892812787, 0, 0] := by
  decide +kernel

theorem rows15183 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15183 = true := by
  decide +kernel

theorem tot15183 : totK PD2M8K2 D2M8K2.t15183 = [0, 0, 57413408558, 357665076329, 366605629656, 65020973887, 1138244013, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
