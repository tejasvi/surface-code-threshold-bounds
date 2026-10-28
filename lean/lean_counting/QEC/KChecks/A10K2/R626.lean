import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2504 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2504 = true := by
  decide +kernel

theorem tot2504 : totK PA10K2 A10K2.t2504 = [66454976102, 826008847166, 2033563200739, 1615216947957, 392541200210, 25734533292, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2505 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2505 = true := by
  decide +kernel

theorem tot2505 : totK PA10K2 A10K2.t2505 = [226848922415, 1075276864795, 1887464230068, 1299342449570, 223522557936, 6034215561, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2506 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2506 = true := by
  decide +kernel

theorem tot2506 : totK PA10K2 A10K2.t2506 = [520626115933, 1727584903796, 1838697124015, 636295038869, 52232171148, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2507 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2507 = true := by
  decide +kernel

theorem tot2507 : totK PA10K2 A10K2.t2507 = [49226751914, 1121978737251, 2292577324584, 1100819309813, 93627914531, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
