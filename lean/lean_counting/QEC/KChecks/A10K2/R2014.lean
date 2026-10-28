import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8056 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8056 = true := by
  decide +kernel

theorem tot8056 : totK PA10K2 A10K2.t8056 = [0, 0, 0, 459008515546, 1674894831864, 1942782653612, 758720154614, 69728412988, 0, 0] := by
  decide +kernel

theorem rows8057 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8057 = true := by
  decide +kernel

theorem tot8057 : totK PA10K2 A10K2.t8057 = [0, 0, 0, 386836717687, 1692080512314, 2088025220571, 657935108125, 40588570868, 0, 0] := by
  decide +kernel

theorem rows8058 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8058 = true := by
  decide +kernel

theorem tot8058 : totK PA10K2 A10K2.t8058 = [0, 0, 0, 0, 601154460960, 1992740164755, 1705096606393, 372642325910, 13576218110, 0] := by
  decide +kernel

theorem rows8059 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8059 = true := by
  decide +kernel

theorem tot8059 : totK PA10K2 A10K2.t8059 = [0, 0, 0, 507603773640, 1706933918529, 1872035573818, 717050166759, 65527055973, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
