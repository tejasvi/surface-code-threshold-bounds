import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5068 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5068 = true := by
  decide +kernel

theorem tot5068 : totK PA10K2 A10K2.t5068 = [0, 0, 529697789564, 1832713513713, 1960532957931, 639089398917, 49180423016, 0, 0, 0] := by
  decide +kernel

theorem rows5069 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5069 = true := by
  decide +kernel

theorem tot5069 : totK PA10K2 A10K2.t5069 = [0, 0, 528967769960, 1927670322455, 1910412203391, 507442737739, 31080743953, 0, 0, 0] := by
  decide +kernel

theorem rows5070 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5070 = true := by
  decide +kernel

theorem tot5070 : totK PA10K2 A10K2.t5070 = [0, 0, 0, 833977427318, 2281319871005, 1493529875063, 252890991993, 6904928264, 0, 0] := by
  decide +kernel

theorem rows5071 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5071 = true := by
  decide +kernel

theorem tot5071 : totK PA10K2 A10K2.t5071 = [0, 0, 471468432376, 1759547547742, 2016025576300, 716947035397, 49931350110, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
