import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8112 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8112 = true := by
  decide +kernel

theorem tot8112 : totK PD2M8K2 D2M8K2.t8112 = [0, 0, 195948154857, 459211011072, 235941979901, 31427768910, 1415142070, 0] := by
  decide +kernel

theorem rows8113 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8113 = true := by
  decide +kernel

theorem tot8113 : totK PD2M8K2 D2M8K2.t8113 = [0, 0, 191701414054, 464910567193, 230726822799, 11906191703, 0, 0] := by
  decide +kernel

theorem rows8114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8114 = true := by
  decide +kernel

theorem tot8114 : totK PD2M8K2 D2M8K2.t8114 = [0, 0, 38096821493, 391525438484, 422975985649, 57544418726, 0, 0] := by
  decide +kernel

theorem rows8115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8115 = true := by
  decide +kernel

theorem tot8115 : totK PD2M8K2 D2M8K2.t8115 = [0, 0, 0, 187479170864, 499903067406, 179450742057, 3622693787, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
