import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4148 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4148 = true := by
  decide +kernel

theorem tot4148 : totK PA10K2 A10K2.t4148 = [0, 0, 640942056703, 2002702749220, 1793644296772, 383354582796, 12918102615, 0, 0, 0] := by
  decide +kernel

theorem rows4149 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4149 = true := by
  decide +kernel

theorem tot4149 : totK PA10K2 A10K2.t4149 = [0, 0, 504265071917, 1827344146018, 1837761364804, 467922168726, 30973630058, 0, 0, 0] := by
  decide +kernel

theorem rows4150 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4150 = true := by
  decide +kernel

theorem tot4150 : totK PA10K2 A10K2.t4150 = [0, 0, 316474870400, 1607882981247, 2014094156691, 583963139732, 31772334738, 0, 0, 0] := by
  decide +kernel

theorem rows4151 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4151 = true := by
  decide +kernel

theorem tot4151 : totK PA10K2 A10K2.t4151 = [0, 308867641608, 727363409707, 912236165499, 1521475987178, 962294216821, 166421390822, 5676195732, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
