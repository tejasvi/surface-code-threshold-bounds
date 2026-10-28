import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6192 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6192 = true := by
  decide +kernel

theorem tot6192 : totK PA10K2 A10K2.t6192 = [0, 0, 227687032730, 1075609973154, 1929648836553, 1216580658331, 206831905036, 5410721913, 0, 0] := by
  decide +kernel

theorem rows6193 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6193 = true := by
  decide +kernel

theorem tot6193 : totK PA10K2 A10K2.t6193 = [0, 0, 520090643496, 1826337437723, 1823634793800, 512309257788, 31608797364, 0, 0, 0] := by
  decide +kernel

theorem rows6194 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6194 = true := by
  decide +kernel

theorem tot6194 : totK PA10K2 A10K2.t6194 = [0, 0, 0, 1050362405084, 2445896576759, 1082859228154, 71239518531, 0, 0, 0] := by
  decide +kernel

theorem rows6195 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6195 = true := by
  decide +kernel

theorem tot6195 : totK PA10K2 A10K2.t6195 = [0, 0, 590619959281, 1756669761894, 1695484990103, 734517407665, 141538455291, 5546304973, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
