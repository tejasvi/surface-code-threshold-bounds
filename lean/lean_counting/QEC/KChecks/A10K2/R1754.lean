import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7016 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7016 = true := by
  decide +kernel

theorem tot7016 : totK PA10K2 A10K2.t7016 = [0, 49414089556, 508886385393, 1722974175464, 2122627413643, 760104964135, 57551169768, 0, 0, 0] := by
  decide +kernel

theorem rows7017 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7017 = true := by
  decide +kernel

theorem tot7017 : totK PA10K2 A10K2.t7017 = [0, 463846356530, 1796968579454, 1874037011929, 484001208385, 26273936808, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7018 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7018 = true := by
  decide +kernel

theorem tot7018 : totK PA10K2 A10K2.t7018 = [0, 297779599935, 1409970571783, 2210884291554, 1067635388848, 90843342500, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7019 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7019 = true := by
  decide +kernel

theorem tot7019 : totK PA10K2 A10K2.t7019 = [0, 0, 497583934763, 1810740432707, 1838980401340, 502458163285, 31543789865, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
