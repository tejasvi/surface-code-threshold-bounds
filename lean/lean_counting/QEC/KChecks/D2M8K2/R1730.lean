import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6920 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6920 = true := by
  decide +kernel

theorem tot6920 : totK PD2M8K2 D2M8K2.t6920 = [0, 0, 165126680728, 463305339690, 206512203686, 9079956249, 0, 0] := by
  decide +kernel

theorem rows6921 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6921 = true := by
  decide +kernel

theorem tot6921 : totK PD2M8K2 D2M8K2.t6921 = [0, 0, 88265605660, 347136859342, 351502121966, 76606062842, 1369150432, 0] := by
  decide +kernel

theorem rows6922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6922 = true := by
  decide +kernel

theorem tot6922 : totK PD2M8K2 D2M8K2.t6922 = [0, 0, 37180689048, 364409145776, 405367713627, 39092012543, 0, 0] := by
  decide +kernel

theorem rows6923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6923 = true := by
  decide +kernel

theorem tot6923 : totK PD2M8K2 D2M8K2.t6923 = [0, 0, 210900261272, 505909308098, 176702361001, 2750377411, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
