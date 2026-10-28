import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1212 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1212 = true := by
  decide +kernel

theorem tot1212 : totK PA10K2 A10K2.t1212 = [0, 0, 0, 0, 870643413484, 2279347415167, 1151917420838, 116968246317, 0, 0] := by
  decide +kernel

theorem rows1213 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1213 = true := by
  decide +kernel

theorem tot1213 : totK PA10K2 A10K2.t1213 = [0, 0, 509695482927, 1852428605178, 1793203117607, 470310658900, 166221397912, 75321663333, 5676195732, 0] := by
  decide +kernel

theorem rows1214 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1214 = true := by
  decide +kernel

theorem tot1214 : totK PA10K2 A10K2.t1214 = [0, 0, 301744193252, 1419433888347, 2180087467309, 979512080708, 80098206426, 0, 0, 0] := by
  decide +kernel

theorem rows1215 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1215 = true := by
  decide +kernel

theorem tot1215 : totK PA10K2 A10K2.t1215 = [0, 0, 187999926649, 931198146315, 1874531501340, 1540344328682, 384324952740, 25313348169, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
