import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6228 = true := by
  decide +kernel

theorem tot6228 : totK PD2M8K2 D2M8K2.t6228 = [0, 0, 308498845963, 470237333357, 74776838001, 1021600638, 0, 0] := by
  decide +kernel

theorem rows6229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6229 = true := by
  decide +kernel

theorem tot6229 : totK PD2M8K2 D2M8K2.t6229 = [0, 124671354637, 361041791848, 297855322913, 73628380942, 3552795014, 0, 0] := by
  decide +kernel

theorem rows6230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6230 = true := by
  decide +kernel

theorem tot6230 : totK PD2M8K2 D2M8K2.t6230 = [0, 178728659629, 448096652512, 260554715452, 25454134109, 0, 0, 0] := by
  decide +kernel

theorem rows6231 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6231 = true := by
  decide +kernel

theorem tot6231 : totK PD2M8K2 D2M8K2.t6231 = [76372199855, 231413996183, 366428924585, 215629390190, 17293032901, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
