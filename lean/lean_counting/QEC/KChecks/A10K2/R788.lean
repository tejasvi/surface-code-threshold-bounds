import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3152 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3152 = true := by
  decide +kernel

theorem tot3152 : totK PA10K2 A10K2.t3152 = [0, 0, 612143352615, 2038905219504, 1894116615403, 461684974021, 17787053285, 0, 0, 0] := by
  decide +kernel

theorem rows3153 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3153 = true := by
  decide +kernel

theorem tot3153 : totK PA10K2 A10K2.t3153 = [0, 0, 0, 746874696302, 2284364166540, 1750341534196, 275739675010, 6279851884, 0, 0] := by
  decide +kernel

theorem rows3154 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3154 = true := by
  decide +kernel

theorem tot3154 : totK PA10K2 A10K2.t3154 = [0, 0, 0, 436018404544, 1725282874571, 2099872794252, 740730367174, 56084282801, 0, 0] := by
  decide +kernel

theorem rows3155 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3155 = true := by
  decide +kernel

theorem tot3155 : totK PA10K2 A10K2.t3155 = [0, 0, 0, 581349832860, 1975176266755, 1872208547389, 409262565759, 12719058911, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
