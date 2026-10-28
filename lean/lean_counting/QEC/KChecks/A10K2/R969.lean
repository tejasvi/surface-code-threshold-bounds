import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3876 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3876 = true := by
  decide +kernel

theorem tot3876 : totK PA10K2 A10K2.t3876 = [0, 166463907846, 1286092010517, 2247675407267, 954422876458, 71926030646, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3877 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3877 = true := by
  decide +kernel

theorem tot3877 : totK PA10K2 A10K2.t3877 = [0, 486648432359, 1639162125467, 1809557516252, 854504903332, 150996265910, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows3878 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3878 = true := by
  decide +kernel

theorem tot3878 : totK PA10K2 A10K2.t3878 = [0, 314008318368, 1488926180550, 2194220124319, 941411457794, 84220238048, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3879 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3879 = true := by
  decide +kernel

theorem tot3879 : totK PA10K2 A10K2.t3879 = [0, 0, 614383265447, 2069177226622, 1983004267681, 447816112618, 13803657628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
