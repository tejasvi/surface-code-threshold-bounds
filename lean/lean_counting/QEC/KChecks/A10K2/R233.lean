import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows932 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t932 = true := by
  decide +kernel

theorem tot932 : totK PA10K2 A10K2.t932 = [0, 0, 499327501531, 1762111754460, 1886920214953, 623047932324, 50978082554, 0, 0, 0] := by
  decide +kernel

theorem rows933 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t933 = true := by
  decide +kernel

theorem tot933 : totK PA10K2 A10K2.t933 = [0, 0, 226393887035, 1239660868375, 2121895797896, 1201713178878, 171946831677, 6439430839, 0, 0] := by
  decide +kernel

theorem rows934 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t934 = true := by
  decide +kernel

theorem tot934 : totK PA10K2 A10K2.t934 = [0, 0, 278436382637, 1370714475827, 2062123603018, 1042332521599, 116151178047, 0, 0, 0] := by
  decide +kernel

theorem rows935 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t935 = true := by
  decide +kernel

theorem tot935 : totK PA10K2 A10K2.t935 = [0, 0, 605698359635, 2053777692773, 1890794549143, 404217009348, 11163036971, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
