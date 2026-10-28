import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows836 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t836 = true := by
  decide +kernel

theorem tot836 : totK PD2M8K2 D2M8K2.t836 = [0, 0, 167552931810, 420556765093, 235246763514, 47070079084, 2490301335, 0] := by
  decide +kernel

theorem rows837 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t837 = true := by
  decide +kernel

theorem tot837 : totK PD2M8K2 D2M8K2.t837 = [0, 0, 152108753724, 450236496424, 246444238481, 19128485265, 0, 0] := by
  decide +kernel

theorem rows838 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t838 = true := by
  decide +kernel

theorem tot838 : totK PD2M8K2 D2M8K2.t838 = [0, 0, 90551747220, 361792496106, 332873955152, 56185796091, 1032241984, 0] := by
  decide +kernel

theorem rows839 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t839 = true := by
  decide +kernel

theorem tot839 : totK PD2M8K2 D2M8K2.t839 = [0, 0, 18424404154, 281477933025, 432411425126, 97307154442, 3598673838, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
