import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5860 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5860 = true := by
  decide +kernel

theorem tot5860 : totK PD2M8K2 D2M8K2.t5860 = [166657218090, 447444095534, 285005411259, 30437197709, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5861 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5861 = true := by
  decide +kernel

theorem tot5861 : totK PD2M8K2 D2M8K2.t5861 = [166436754966, 459606871366, 251827079624, 18513797132, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5862 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5862 = true := by
  decide +kernel

theorem tot5862 : totK PD2M8K2 D2M8K2.t5862 = [0, 234287456284, 498372113426, 164412921808, 7233348802, 0, 0, 0] := by
  decide +kernel

theorem rows5863 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5863 = true := by
  decide +kernel

theorem tot5863 : totK PD2M8K2 D2M8K2.t5863 = [66525107661, 277485962374, 394662515617, 131008527027, 6017336459, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
