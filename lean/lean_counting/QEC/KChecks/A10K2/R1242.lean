import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4968 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4968 = true := by
  decide +kernel

theorem tot4968 : totK PA10K2 A10K2.t4968 = [477697633225, 1734679484316, 1900332097961, 643064441451, 52230035883, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4969 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4969 = true := by
  decide +kernel

theorem tot4969 : totK PA10K2 A10K2.t4969 = [196642455102, 1360145922581, 2266928649399, 922700131762, 60972737519, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4970 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4970 = true := by
  decide +kernel

theorem tot4970 : totK PA10K2 A10K2.t4970 = [274889264427, 1178506638437, 1857253714955, 1186231167759, 234737231800, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4971 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4971 = true := by
  decide +kernel

theorem tot4971 : totK PA10K2 A10K2.t4971 = [183631161869, 1071043452830, 2058610177663, 1346063221778, 238348130385, 6853348008, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
