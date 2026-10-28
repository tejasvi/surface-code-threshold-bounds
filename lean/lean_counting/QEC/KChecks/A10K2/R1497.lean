import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5988 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5988 = true := by
  decide +kernel

theorem tot5988 : totK PA10K2 A10K2.t5988 = [0, 459935659359, 1671504704120, 1937623733000, 710675000964, 58003447868, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5989 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5989 = true := by
  decide +kernel

theorem tot5989 : totK PA10K2 A10K2.t5989 = [0, 288453439043, 1525591355730, 2136182530358, 689319178807, 38769339849, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5990 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5990 = true := by
  decide +kernel

theorem tot5990 : totK PA10K2 A10K2.t5990 = [0, 295157913241, 1239803859967, 1903225665858, 1060514803398, 166212260397, 5546304973, 0, 0, 0] := by
  decide +kernel

theorem rows5991 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5991 = true := by
  decide +kernel

theorem tot5991 : totK PA10K2 A10K2.t5991 = [152930188526, 649446177302, 1557773689770, 1919003041948, 760038219254, 70524874826, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
