import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4364 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4364 = true := by
  decide +kernel

theorem tot4364 : totK PA10K2 A10K2.t4364 = [0, 293349203532, 1117451200117, 1820411561587, 1230727476231, 235068694400, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows4365 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4365 = true := by
  decide +kernel

theorem tot4365 : totK PA10K2 A10K2.t4365 = [0, 258963577619, 1476929442117, 2247833916088, 913635156399, 75702874438, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4366 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4366 = true := by
  decide +kernel

theorem tot4366 : totK PA10K2 A10K2.t4366 = [0, 0, 525671985971, 1834074921082, 1980020798500, 587805646333, 35503361870, 0, 0, 0] := by
  decide +kernel

theorem rows4367 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4367 = true := by
  decide +kernel

theorem tot4367 : totK PA10K2 A10K2.t4367 = [0, 0, 463456653039, 1908460504658, 1920587124307, 444520062617, 25667075836, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
