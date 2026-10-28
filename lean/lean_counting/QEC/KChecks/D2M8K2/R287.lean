import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1148 = true := by
  decide +kernel

theorem tot1148 : totK PD2M8K2 D2M8K2.t1148 = [0, 92009307245, 385381525871, 394179096509, 38182550434, 0, 0, 0] := by
  decide +kernel

theorem rows1149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1149 = true := by
  decide +kernel

theorem tot1149 : totK PD2M8K2 D2M8K2.t1149 = [0, 170612279127, 424624394405, 267035274140, 30304740390, 0, 0, 0] := by
  decide +kernel

theorem rows1150 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1150 = true := by
  decide +kernel

theorem tot1150 : totK PD2M8K2 D2M8K2.t1150 = [0, 141541834761, 467507297571, 280462860629, 15528878924, 0, 0, 0] := by
  decide +kernel

theorem rows1151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1151 = true := by
  decide +kernel

theorem tot1151 : totK PD2M8K2 D2M8K2.t1151 = [0, 0, 181499783352, 454035320451, 226246341932, 18317572719, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
