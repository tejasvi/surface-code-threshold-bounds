import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2516 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2516 = true := by
  decide +kernel

theorem tot2516 : totK PA10K2 A10K2.t2516 = [234310089757, 1134910635753, 2115841270946, 1406988951050, 237189114531, 6032141194, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2517 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2517 = true := by
  decide +kernel

theorem tot2517 : totK PA10K2 A10K2.t2517 = [564140227026, 1956258259847, 1955195603340, 553170875686, 32780473262, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2518 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2518 = true := by
  decide +kernel

theorem tot2518 : totK PA10K2 A10K2.t2518 = [0, 690605281713, 2189715391922, 1868709401321, 412780349286, 13816090359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2519 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2519 = true := by
  decide +kernel

theorem tot2519 : totK PA10K2 A10K2.t2519 = [0, 517870819818, 1863422518698, 1958721054926, 627848557189, 49180423016, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
