import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows208 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t208 = true := by
  decide +kernel

theorem tot208 : totK PA10K2 A10K2.t208 = [0, 372742425205, 1698397356354, 2220771427038, 755383201818, 39253065429, 0, 0, 0, 0] := by
  decide +kernel

theorem rows209 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t209 = true := by
  decide +kernel

theorem tot209 : totK PA10K2 A10K2.t209 = [0, 55593335868, 695165238469, 2064774030192, 1820709428561, 393714626946, 12219140272, 0, 0, 0] := by
  decide +kernel

theorem rows210 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t210 = true := by
  decide +kernel

theorem tot210 : totK PA10K2 A10K2.t210 = [0, 486683067761, 1798630906501, 1928201993184, 558973590089, 32263146721, 0, 0, 0, 0] := by
  decide +kernel

theorem rows211 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t211 = true := by
  decide +kernel

theorem tot211 : totK PA10K2 A10K2.t211 = [0, 330354438850, 1564152939801, 2166968185494, 893259302006, 68214171399, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
