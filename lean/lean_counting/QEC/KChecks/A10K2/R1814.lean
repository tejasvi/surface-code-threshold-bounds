import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7256 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7256 = true := by
  decide +kernel

theorem tot7256 : totK PA10K2 A10K2.t7256 = [0, 0, 295901161011, 1474559751694, 2180933763506, 899867581975, 76573704244, 0, 0, 0] := by
  decide +kernel

theorem rows7257 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7257 = true := by
  decide +kernel

theorem tot7257 : totK PA10K2 A10K2.t7257 = [0, 0, 0, 509592406874, 1782202376664, 1800505706850, 486211571152, 30780440178, 0, 0] := by
  decide +kernel

theorem rows7258 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7258 = true := by
  decide +kernel

theorem tot7258 : totK PA10K2 A10K2.t7258 = [0, 0, 520503246358, 1694229234154, 1830156346389, 712706896081, 70503053467, 0, 0, 0] := by
  decide +kernel

theorem rows7259 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7259 = true := by
  decide +kernel

theorem tot7259 : totK PA10K2 A10K2.t7259 = [0, 0, 42105865362, 862022511225, 2144539036495, 1265114122603, 193488419059, 5705019915, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
