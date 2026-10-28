import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7812 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7812 = true := by
  decide +kernel

theorem tot7812 : totK PA10K2 A10K2.t7812 = [0, 0, 0, 575416913994, 1907832052479, 1696913056791, 459693944928, 41822933480, 0, 0] := by
  decide +kernel

theorem rows7813 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7813 = true := by
  decide +kernel

theorem tot7813 : totK PA10K2 A10K2.t7813 = [0, 0, 0, 295411761641, 1419967728101, 2061366008286, 796244492943, 65232036096, 0, 0] := by
  decide +kernel

theorem rows7814 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7814 = true := by
  decide +kernel

theorem tot7814 : totK PA10K2 A10K2.t7814 = [0, 0, 0, 502045099659, 1950239713257, 2123341114814, 534622742758, 27545930069, 0, 0] := by
  decide +kernel

theorem rows7815 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7815 = true := by
  decide +kernel

theorem tot7815 : totK PA10K2 A10K2.t7815 = [0, 0, 539669932579, 1881157378351, 1792992503672, 498582086190, 97190614510, 16365519116, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
